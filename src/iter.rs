//! Implementations of the [`AsU8Chars`] extension trait.

use super::AsU8Chars;
use super::u8char;

impl<'a> AsU8Chars for &'a str {
    type Iter = U8CharsFromStr<'a>;

    fn u8chars(self) -> U8CharsFromStr<'a> {
        U8CharsFromStr { remain: self }
    }
}

/// Iterator type returned by the [`AsU8Chars`] implementation for
/// references to `str`.
pub struct U8CharsFromStr<'a> {
    remain: &'a str,
}

impl<'a> Iterator for U8CharsFromStr<'a> {
    type Item = u8char;

    fn next(&mut self) -> Option<u8char> {
        let (ret, rest) = u8char::from_string_prefix(self.remain);
        self.remain = rest;
        ret
    }
}

impl<'a> core::iter::FusedIterator for U8CharsFromStr<'a> {}

impl<'a> AsU8Chars for &'a [u8] {
    type Iter = U8CharsFromBytes<'a>;

    /// Performs a **lossy** extraction of [`u8char`]-represented characters
    /// from UTF-8 sequences in the byte array.
    ///
    /// Specifically, any invalid sequences will be replaced by
    /// [`u8char::REPLACEMENT_CHAR`].
    fn u8chars(self) -> U8CharsFromBytes<'a> {
        U8CharsFromBytes { remain: self }
    }
}

/// Iterator type returned by the [`AsU8Chars`] implementation for
/// references to `[u8]`.
#[derive(Debug)]
pub struct U8CharsFromBytes<'a> {
    remain: &'a [u8],
}

impl<'a> Iterator for U8CharsFromBytes<'a> {
    type Item = u8char;

    fn next(&mut self) -> Option<u8char> {
        let (ret, rest) = u8char::from_bytes_prefix(self.remain);
        self.remain = rest;
        match ret {
            Ok(c) => c,
            Err(_) => Some(u8char::REPLACEMENT_CHAR),
        }
    }
}

impl<'a> core::iter::FusedIterator for U8CharsFromBytes<'a> {}

#[test]
fn test_from_str() {
    use AsU8Chars;

    let input = "\0\n\u{00A4}\u{275D}\u{275E}\u{FFFD}\u{1FBC6}";
    let got: Vec<_> = input.u8chars().map(|c| c.to_char()).collect();
    let want = &['\0', '\n', '¤', '❝', '❞', '\u{FFFD}', '🯆'];
    assert_eq!(got, want);
}

#[test]
fn test_from_bytes() {
    use AsU8Chars;

    let input = b"hello\xff\xe2\x9d\x9eworld\xe2\x9d";
    let got: Vec<_> = input.u8chars().map(|c| c.to_char()).collect();
    let want = &[
        'h', 'e', 'l', 'l', 'o', '\u{FFFD}', '❞', 'w', 'o', 'r', 'l', 'd', '\u{FFFD}',
    ];
    assert_eq!(got, want);
}
