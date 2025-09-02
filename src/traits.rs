use super::u8char;

/// Convenience trait for obtaining an iterator over the characters of a
/// `str` as [`u8char`].
pub trait AsU8Chars {
    fn u8chars(&self) -> U8Chars<'_>;
}

impl AsU8Chars for str {
    fn u8chars(&self) -> U8Chars<'_> {
        U8Chars { remain: self }
    }
}

pub struct U8Chars<'a> {
    remain: &'a str,
}

impl<'a> Iterator for U8Chars<'a> {
    type Item = u8char;

    fn next(&mut self) -> Option<Self::Item> {
        let (ret, rest) = u8char::from_string_prefix(self.remain);
        self.remain = rest;
        ret
    }
}

impl<'a> core::iter::FusedIterator for U8Chars<'a> {}
