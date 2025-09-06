//! UTF-8 parse errors.

/// Describes a series of one or more bytes that don't form a valid UTF-8
/// sequence, either due to being totally invalid or being a truncation
/// of a valid UTF-8 sequence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Utf8Error<'a> {
    bytes: &'a [u8],
    valid: bool,
}

impl<'a> Utf8Error<'a> {
    /// Creates a [`Utf8Error`] for an invalid sequence.
    ///
    /// The given byte slice is zero or more invalid bytes followed by
    /// an invalid byte.
    pub(crate) const fn new_invalid(bad: &'a [u8]) -> Self {
        debug_assert!(!bad.is_empty());
        Self {
            bytes: bad,
            valid: false,
        }
    }

    /// Creates a [`Utf8Error`] for a prefix of an incomplete sequence.
    /// The given slice must therefore have length between one and three
    /// and must be completable only by adding one or more continuation
    /// bytes.
    pub(crate) const fn new_incomplete(prefix: &'a [u8]) -> Self {
        debug_assert!(!prefix.is_empty());
        debug_assert!(prefix.len() < 4);
        Self {
            bytes: prefix,
            valid: true,
        }
    }

    /// Returns true if the consumed bytes were valid and just incomplete,
    /// or false if the consumed bytes cannot possibly be valid.
    pub const fn is_valid(&self) -> bool {
        self.valid
    }

    /// Returns the incomplete prefix (up to three bytes) if the input
    /// contained only a valid-but-incomplete UTF-8 sequence.
    ///
    /// Returns `None` if the input began with bytes that cannot possibly
    /// represent a valid UTF-8 sequence. In that case, a lossy parser should
    /// use U+FFFD REPLACEMENT CHARACTER instead of the represented bytes
    /// and then expect a new UTF-8 sequence to begin at the following byte.
    pub const fn incomplete_prefix(&self) -> Option<&[u8]> {
        if !self.valid {
            return None;
        }
        Some(self.bytes)
    }

    /// If the input began with a byte that cannot possibly represent the start
    /// of a valid UTF-8 sequence even if continued, returns zero or more
    /// valid prefix bytes followed by one or more errored bytes.
    ///
    /// A lossy parser should typically replace the entire invalid sequence
    /// with U+FFFD REPLACEMENT CHARACTER and then expect a new UTF-8 sequence
    /// to begin at the following byte.
    ///
    /// Returns `None` if the input consisted only of a valid prefix of an
    /// incomplete UTF-8 sequence.
    pub const fn invalid_bytes(&self) -> Option<&[u8]> {
        if self.valid {
            return None;
        }
        Some(self.bytes)
    }
}
