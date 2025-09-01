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
