//! Streaming parsing and translation of incoming UTF-8 bytes into [`u8char`].

use crate::{error::Utf8Error, u8char};
use core::iter::FusedIterator;

/// A lossy, streaming UTF-8 sequence parser that produces [`u8char`] values.
///
/// A [`U8CharStream`] translates incoming byte slices containing chunks
/// of a byte stream into a series of UTF-8 sequences, using a small internal
/// buffer to track partial sequences for completion once the next chunk is
/// available.
///
/// Each time a new chunk arrives, pass it to [`Self::more`] to get an iterator
/// over as many whole UTF-8 characters can be extracted from the unconverted
/// input so far. Sequences that aren't valid UTF-8 are lossily represented
/// as [`u8char::REPLACEMENT_CHAR`].
///
/// If you reach the end of the stream, call [`Self::end`] to consume any bytes
/// left in the internal buffer. This will produce one more
/// [`u8char::REPLACEMENT_CHAR`] to represent any incomplete prefix left in
/// the internal buffer.
pub struct U8CharStream {
    partial: Option<PartialU8Char>,
}

impl U8CharStream {
    pub fn new() -> Self {
        Self { partial: None }
    }

    /// Feed more input into the stream and read back as many new [`u8char`]
    /// values as possible based on the new bytes.
    ///
    /// Sequences that aren't valid UTF-8 are lossily represented
    /// as [`u8char::REPLACEMENT_CHAR`].
    pub fn more<'a>(
        &'a mut self,
        buf: &'a [u8],
    ) -> impl Iterator<Item = u8char> + FusedIterator + 'a {
        StreamIter {
            remain: buf,
            stream: self,
        }
    }

    /// Handle the end of the stream, at which point any remaining incomplete
    /// sequence in the internal buffer is produced as
    /// [`u8char::REPLACEMENT_CHAR`].
    ///
    /// It's valid to continue using the stream after calling this function.
    /// The next byte given to [`Self::more`] would be treated as the beginning
    /// of a new sequence.
    pub fn end(&mut self) -> impl Iterator<Item = u8char> + FusedIterator + '_ {
        (if self.partial.is_some() {
            // Since we know there's no more input coming, any partial
            // sequence we have must be invalid due to being truncated,
            // so we'll mark that with one more replacement character
            // at the end of our output.
            self.partial = None;
            Some(u8char::REPLACEMENT_CHAR)
        } else {
            None
        })
        .into_iter()
    }
}

struct StreamIter<'a> {
    remain: &'a [u8],
    stream: &'a mut U8CharStream,
}

impl<'a> Iterator for StreamIter<'a> {
    type Item = u8char;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(partial) = self.stream.partial.as_mut() {
            // We have some leftover bytes from a partial sequence at
            // the end of the previous chunk, so we'll try to complete
            // that before we start looking for new sequences.
            let (ret, rest) = partial.continue_with(self.remain);
            self.remain = rest;
            if ret.is_some() {
                // the prefix is now finished, either by reaching a valid
                // conclusion or by there not being enough completion
                // characters to complete it.
                self.stream.partial = None;
            }
            ret
        } else {
            // Since we _don't_ have a previous uncompleted sequence in
            // our partial buffer, we'll try to begin the next sequence.
            let (r, rest) = u8char::from_bytes_prefix(self.remain);
            self.remain = rest;
            match r {
                Ok(ret) => ret,
                Err(e) => {
                    if let Some(prefix) = e.incomplete_prefix() {
                        // We'll need to remember this partial prefix in our
                        // buffer so we can try to complete it when the next
                        // chunk arrives.
                        self.stream.partial = Some(unsafe {
                            // Safety: Utf8Error::incomplete_prefix, by definition,
                            // returns between one and three bytes that could
                            // potentially become a valid UTF-8 sequence from only
                            // adding more continuation bytes to the end.
                            PartialU8Char::new(prefix)
                        });
                        None
                    } else {
                        // We've found one or more bytes that cannot possibly
                        // become a valid UTF-8 sequence, and so we'll just
                        // discard them and use the replacement character
                        // instead.
                        Some(u8char::REPLACEMENT_CHAR)
                    }
                }
            }
        }
    }
}

impl<'a> FusedIterator for StreamIter<'a> {}

#[derive(Debug)]
struct PartialU8Char {
    buf: [u8; 4],
    len: u8,
}

impl PartialU8Char {
    //
    // # Safety
    //
    // The prefix must be between 1 and 3 bytes in length, and must contain
    // a sequence of bytes that could potentially become a valid UTF-8
    // scalar value only from contatenating more continuation bytes.
    pub unsafe fn new(prefix: &[u8]) -> Self {
        let mut ret = Self {
            buf: [0; 4],
            len: prefix.len() as u8,
        };
        unsafe {
            core::ptr::copy_nonoverlapping(prefix.as_ptr(), ret.buf.as_mut_ptr(), prefix.len())
        };
        ret
    }

    pub fn len(&self) -> usize {
        self.len as usize
    }

    pub fn want_len(&self) -> usize {
        // We assume that the initial byte is valid because `U8CharsFromBytes`
        // should only be using its `PartialU8Char` if it found a valid
        // prefix of a UTF-8 sequence, and an invalid starting byte would
        // immediately render it _not_ a valid prefix.
        crate::util::length_by_initial_byte_valid(self.buf[0])
    }

    pub fn need_more(&self) -> bool {
        return self.want_len() != self.len();
    }

    pub fn as_slice(&self) -> &[u8] {
        &self.buf[..self.len()]
    }

    pub fn continue_with<'buf>(&mut self, from: &'buf [u8]) -> (Option<u8char>, &'buf [u8]) {
        let mut remain = from;
        while self.need_more() && !remain.is_empty() {
            if (remain[0] & 0b11000000) != 0b10000000 {
                // not a UTF-8 continuation character, so we're done
                break;
            }
            let (first, rest) = remain.split_at(1);
            self.buf[self.len()] = first[0];
            self.len += 1;
            remain = rest;
        }
        let ret = match self.as_u8char() {
            Ok(c) => Some(c),
            Err(e) => {
                if e.is_valid() && remain.is_empty() {
                    // We still don't have enough bytes to complete the
                    // sequence, but it remains a valid prefix.
                    None
                } else {
                    // If either the buffer is now completely invalid or
                    // it remains incomplete when the next character is not
                    // a continuation byte then this prefix can never become
                    // valid and so we'll just discard it in favor of the
                    // replacement character.
                    Some(u8char::REPLACEMENT_CHAR)
                }
            }
        };
        (ret, remain)
    }

    pub fn as_u8char(&self) -> Result<u8char, Utf8Error<'_>> {
        let (r, _) = u8char::from_bytes_prefix(self.as_slice());
        match r {
            Ok(Some(r)) => Ok(r),
            Err(e) => Err(e),
            Ok(None) => unsafe {
                // Safety: the safety requirements of `Self::new`
                // require that we always have at least one byte of prefix,
                // so u8char::from_bytes_prefix must either successfully
                // return Some or return an error.
                core::hint::unreachable_unchecked()
            },
        }
    }
}

#[test]
fn test_u8charstream() {
    let mut s = U8CharStream::new();

    let ascii_only: Vec<_> = collect(s.more(b"Hello!"));
    assert_eq!(ascii_only, ['H', 'e', 'l', 'l', 'o', '!']);

    let longer_seq: Vec<_> = collect(s.more(b"a\xe2\x9d\x9ec"));
    assert_eq!(longer_seq, ['a', '❞', 'c']);

    let invalid: Vec<_> = collect(s.more(b"a\xff\xfec"));
    assert_eq!(invalid, ['a', '\u{FFFD}', '\u{FFFD}', 'c']);

    let split: Vec<_> = collect(s.more(b"a\xe2"));
    assert_eq!(split, ['a']);
    let split: Vec<_> = collect(s.more(b"\x9d"));
    assert_eq!(split, []);
    let split: Vec<_> = collect(s.more(b"\x9ec"));
    assert_eq!(split, ['❞', 'c']);
    let split: Vec<_> = collect(s.more(b"a\xe2\x9d"));
    assert_eq!(split, ['a']);
    let split: Vec<_> = collect(s.more(b"\x9e"));
    assert_eq!(split, ['❞']);

    let invalid_split: Vec<_> = collect(s.more(b"\xe2"));
    assert_eq!(invalid_split, []);
    let invalid_split: Vec<_> = collect(s.more(b"c")); // while expecting a continuation byte
    assert_eq!(invalid_split, ['\u{FFFD}', 'c']);

    let zero_len: Vec<_> = collect(s.more(b""));
    assert_eq!(zero_len, []);

    let end_valid: Vec<_> = collect(s.end());
    assert_eq!(end_valid, []);
    let end_incomplete: Vec<_> = collect(s.more(b"\xe2"));
    assert_eq!(end_incomplete, []);
    let end_incomplete: Vec<_> = collect(s.end()); // while expecting a continuation byte
    assert_eq!(end_incomplete, ['\u{FFFD}']);
    let end_again: Vec<_> = collect(s.end());
    assert_eq!(end_again, []);

    fn collect(it: impl Iterator<Item = u8char>) -> Vec<char> {
        it.map(|c| c.to_char()).collect()
    }
}
