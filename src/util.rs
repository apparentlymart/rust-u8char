//! Additional helper functions that are used in the implementation of
//! [`crate::u8char`] and exported in case they are useful for "off-menu"
//! uses of that type, such as when using unsafe code.

use crate::error::Utf8Error;

/// Determines the expected encoded length of a unicode value, in bytes,
/// based on its initial byte.
///
/// Returns `Err` if the given byte is not valid to start an UTF-8 encoded
/// sequence, such as if it is a continuation byte.
pub const fn length_by_initial_byte(b0: u8) -> Result<usize, ()> {
    if matches!(b0, 0xc0 | 0xc1 | 0xf5..=0xff) {
        // These bytes never appear in valid UTF-8, in any position,
        // so we'll rule them out early.
        return Err(());
    }
    Ok(match b0.leading_ones() {
        0 => 1,
        1 => return Err(()), // continuation byte cannot appear at start
        2 => 2,
        3 => 3,
        4 => 4,
        _ => return Err(()),
    })
}

/// A faster alternative to [`length_by_initial_byte`] that assumes that
/// the given byte is a valid starting byte, such as when taking the first
/// byte from a [`str`] where valid UTF-8 is guaranteed.
///
/// Results are unspecified if the given byte is not a valid UTF-8 starting
/// byte.
pub const fn length_by_initial_byte_valid(b0: u8) -> usize {
    // The four most significant bits are enough to make our decision
    // here, and so we'll use a 16-element lookup table instead of
    // calculation.
    const TABLE: [u8; 16] = {
        let mut table = [0_u8; 16];
        let mut i = 0;
        while i < 16 {
            let example = (i as u8) << 4;
            let len = example.leading_ones().saturating_sub(1) + 1; // treat zero as one
            table[i] = len as u8;
            i += 1;
        }
        table
    };
    TABLE[(b0 >> 4) as usize] as usize
}

/// Splits the given string at the end of its first UTF-8 character.
///
/// If the string is empty then this returns two empty strings.
pub const fn split_str_at_first_char(s: &str) -> (&str, &str) {
    if s.is_empty() {
        return (s, s);
    }
    // Safety: we can assume that len represents a valid UTF-8 boundary
    // because str is guaranteed to always be correctly encoded.
    unsafe {
        let bytes = s.as_bytes();
        let len = length_by_initial_byte_valid(bytes[0]);
        let (a, b) = bytes.split_at_unchecked(len);
        (str::from_utf8_unchecked(a), str::from_utf8_unchecked(b))
    }
}

/// Attempts to split the given byte slice into a `str` prefix containing one
/// valid UTF-8 sequence and the remainder of the given slice.
///
/// If the slice does not begin with a valid UTF-8 sequence then the first
/// result is a [`Utf8Error`] which represents that the slice begins either
/// with a valid prefix of an incomplete sequence or with a byte that cannot
/// possibly begin a sequence.
///
/// If the given slice is empty then this succeeds with an empty string
/// and an empty slice.
pub const fn split_bytes_at_first_char(buf: &[u8]) -> (Result<&str, Utf8Error<'_>>, &[u8]) {
    extern crate std;
    if buf.is_empty() {
        return (Ok(""), buf);
    }
    if buf[0] < 0x80 {
        // Easy case for ASCII character
        let (a, b) = unsafe { buf.split_at_unchecked(1) };
        return (Ok(unsafe { str::from_utf8_unchecked(a) }), b);
    }
    let Ok(expected_len) = length_by_initial_byte(buf[0]) else {
        let (a, b) = unsafe { buf.split_at_unchecked(1) };
        return (Err(Utf8Error::new_invalid(a)), b);
    };

    let eff_len = if expected_len < buf.len() {
        expected_len
    } else {
        buf.len()
    };
    let candidate = unsafe {
        // Using unsafe here only because we can't currently slice in a const
        // function.
        // Safety: we checked above that this is in bounds.
        core::slice::from_raw_parts(buf.as_ptr(), eff_len)
    };
    // We'll just borrow the standard library's UTF-8 validation here, because
    // it's well-optimized and well-tested. Our work above was just to make
    // sure that we're only validating at most one UTF-8 sequence's worth
    // of bytes at a time.
    if let Err(e) = str::from_utf8(candidate) {
        let valid_prefix = e.valid_up_to();
        debug_assert!(valid_prefix == 0); // should always be zero because we only provided one character
        if let Some(errlen) = e.error_len() {
            let (a, b) = unsafe { buf.split_at_unchecked(errlen) };
            return (Err(Utf8Error::new_invalid(a)), b);
        } else {
            return (Err(Utf8Error::new_incomplete(buf)), b"");
        }
    }
    // If str::from_utf8 considered the candidate valid then that's
    // what we'll return as a successful result.
    let (a, b) = unsafe { buf.split_at_unchecked(candidate.len()) };
    (Ok(unsafe { str::from_utf8_unchecked(a) }), b)
}

/// Describes the role of some `u8` value in UTF-8.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Utf8ByteRole {
    /// The beginning of a sequence of the given length.
    Begin(u8),
    /// A valid continuation byte.
    Continuation,
    /// A byte value that cannot appear anywhere in a valid UTF-8 sequence.
    Invalid,
}

impl Utf8ByteRole {
    /// Determines the [`Utf8ByteRole`] of the given byte.
    ///
    /// This function is not well-optimized, since it's here primarily for
    /// error handling and debugging, such as with the return value from
    /// [`crate::error::Utf8Error::invalid_byte`].
    pub fn for_byte(b: u8) -> Self {
        if matches!(b, 0xc0 | 0xc1 | 0xf5..=0xff) {
            // These bytes never appear in valid UTF-8, in any position,
            // so we'll rule them out early.
            return Self::Invalid;
        }
        if b < 0x80 {
            return Self::Begin(1);
        }
        match b.leading_ones() {
            0 => Self::Begin(1),
            1 => Self::Continuation,
            2 => Self::Begin(2),
            3 => Self::Begin(3),
            4 => Self::Begin(4),
            _ => Self::Invalid,
        }
    }
}
