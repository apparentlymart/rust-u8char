//! `u8char` provides the type [`u8char`], which is similar to [`char`] but
//! represented internally as UTF-8 to allow lower-cost usage in conjunction
//! with [`str`] and [`String`].
//!
//! # Features
//!
//! This package currently supports the feature `unstable_niches`, which is
//! disabled by default. This can be enabled only on nightly builds of Rust
//! and uses some perma-unstable features to try to make `Option<u8char>` have
//! the same size as `u8char`. Without this feature `Option<u8char>` will be
//! larger than `u8char`, whereas the Rust compiler knows that built-in `char`
//! only stores valid Unicode scalar values and `Option<char>` has the same
//! size as `char`.
#![cfg_attr(
    feature = "unstable_niches",
    allow(internal_features),
    feature(rustc_attrs)
)]
#![cfg_attr(not(any(test, doc)), no_std)]

pub mod error;
pub mod iter;
pub mod stream;
pub mod util;

use crate::error::Utf8Error;

/// A representation of a Unicode scalar value that has the same representation
/// as if the same scalar value were used as part of a [`str`].
///
/// This type can represent all of the same values that [`char`] can represent,
/// but does so using one to four UTF-8 bytes instead of directly as a [`u32`].
///
/// This type has the same size and alignment as `char`, but it does not have
/// the same representation.
#[repr(transparent)]
#[cfg_attr(
    feature = "unstable_niches",
    rustc_layout_scalar_valid_range_start(0x00000000)
)]
#[cfg_attr(
    all(feature = "unstable_niches", target_endian = "little"),
    rustc_layout_scalar_valid_range_end(0xbfbf90f0)
)]
#[cfg_attr(
    all(feature = "unstable_niches", target_endian = "big"),
    rustc_layout_scalar_valid_range_end(0xf090bfbf)
)]
#[allow(non_camel_case_types)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct u8char(u32);

impl u8char {
    /// The `u8char` value representing U+0000 NULL.
    #[allow(unused_unsafe)]
    pub const NULL: Self = unsafe { u8char(0) };

    /// The `u8char` value representing U+FFFD REPLACEMENT CHARACTER.
    pub const REPLACEMENT_CHAR: Self = u8char::from_char('\u{FFFD}');

    pub const fn from_char(c: char) -> Self {
        let c = c as u32;
        let mut ret = Self::NULL;
        {
            // Safety: we're going to leave this in a valid repr before we
            // return it as a `u8char`.
            let bs: &mut [u8; 4] = unsafe { core::mem::transmute(&mut ret) };
            if c <= 0x007F {
                bs[0] = c as u8;
            } else if c <= 0x07FF {
                bs[0] = 0b11000000 | (c >> 6) as u8;
                bs[1] = 0b10000000 | (c & 0b111111) as u8;
            } else if c <= 0xFFFF {
                bs[0] = 0b11100000 | (c >> 12) as u8;
                bs[1] = 0b10000000 | ((c >> 6) & 0b111111) as u8;
                bs[2] = 0b10000000 | (c & 0b111111) as u8;
            } else if c <= 0x10FFFF {
                bs[0] = 0b11110000 | (c >> 18) as u8;
                bs[1] = 0b10000000 | ((c >> 12) & 0b111111) as u8;
                bs[2] = 0b10000000 | ((c >> 6) & 0b111111) as u8;
                bs[3] = 0b10000000 | (c & 0b111111) as u8;
            }
            // bs MUST contain a valid UTF-8 sequence by the time we get here.
        }
        ret
    }

    /// Returns a representation of the first character of the given string,
    /// and a slice covering the remainder of the string from the same
    /// underlying buffer.
    ///
    /// If the given string is empty then returns `(None, s)`.
    ///
    /// This function relies on the guarantee that `str` always contains
    /// only valid UTF-8 encoding.
    pub const fn from_string_prefix(s: &str) -> (Option<Self>, &str) {
        let (a, b) = util::split_str_at_first_char(s);
        if a.is_empty() {
            return (None, b);
        }
        let ret = unsafe {
            // Safety: We can now assume that the byte representation of `a` is
            // at most four bytes long and is a valid UTF-8 sequence, and so is
            // ready to copy directly as a bit pattern for `Self`.
            let mut ret = Self::NULL;
            let dst: &mut [u8; 4] = core::mem::transmute(&mut ret);
            core::ptr::copy_nonoverlapping(a.as_ptr(), dst.as_mut_ptr(), a.len());
            ret
        };
        (Some(ret), b)
    }

    /// Returns a [`u8char`] representation of the valid UTF-8 sequence at the
    /// beginning of `buf`, or a [`Utf8Error`] value if there is not a valid
    /// and complete sequence at the start.
    ///
    /// Unless it successfully returns `None` to indicate an empty buffer this
    /// function always consumes at least one byte from `buf`, possibly
    /// classifying what it consumed as an error. The error type distinguishes
    /// between definitely-invald sequences (which could not become valid even
    /// if more bytes were added) and incomplete prefixes (which could
    /// potentially become valid if more bytes were added).
    ///
    /// A streaming parser should typically handle the `Utf8Error` cases as
    /// follows:
    /// - If [`Utf8Error::incomplete_prefix`] returns `Some` then save what
    ///   was returned in a four-byte "leverovers" buffer and then try to
    ///   complete parsing from that buffer once more bytes are available.
    /// - Otherwise, discard the bytes that were consumed and use
    ///   [`Self::REPLACEMENT_CHAR`] in their place, and then try to restart
    ///   parsing at the first unconsumed byte.
    ///
    /// The second return value is the remainder of the given buffer after
    /// consuming what was returned in the first value.
    pub fn from_bytes_prefix(buf: &[u8]) -> (Result<Option<Self>, Utf8Error<'_>>, &[u8]) {
        let (result, remain) = util::split_bytes_at_first_char(buf);
        let result = result.map(|s| {
            if s.is_empty() {
                return None;
            }
            unsafe {
                // Safety: If split_bytes_at_first_char is correct then we can
                // assume that the byte representation of `a` is at most four
                // bytes long and is a valid UTF-8 sequence, and so is
                // ready to copy directly as a bit pattern for `Self`.
                let mut ret = Self::NULL;
                let dst: &mut [u8; 4] = core::mem::transmute(&mut ret);
                core::ptr::copy_nonoverlapping(s.as_ptr(), dst.as_mut_ptr(), s.len());
                Some(ret)
            }
        });
        (result, remain)
    }

    /// Returns the length of the UTF-8 encoding of the character in bytes.
    #[inline(always)]
    pub const fn len(self) -> usize {
        util::length_by_initial_byte_valid(self.first_byte())
    }

    /// Returns true if the character is in the ASCII range, or false otherwise.
    #[inline(always)]
    pub const fn is_ascii(self) -> bool {
        self.first_byte() < 0x80
    }

    /// Returns the first byte of the UTF-8 encoding of the character.
    #[inline(always)]
    pub const fn first_byte(self) -> u8 {
        self.to_byte_array()[0]
    }

    /// Returns a byte slice covering the UTF-8 encoding of the character.
    #[inline]
    pub const fn as_bytes(&self) -> &[u8] {
        let len = self.len();
        unsafe {
            let bs: &[u8; 4] = core::mem::transmute(self);
            core::slice::from_raw_parts(bs.as_ptr(), len)
        }
    }

    /// Returns a reference to a `str` representation of the character.
    #[inline(always)]
    pub const fn as_str(&self) -> &str {
        unsafe { core::str::from_utf8_unchecked(&self.as_bytes()) }
    }

    /// Returns a mutable reference to a `str` representation of the character.
    #[inline(always)]
    pub const fn as_mut_str(&mut self) -> &mut str {
        let len = self.len();
        let bs = unsafe {
            let bs: &mut [u8; 4] = core::mem::transmute(self);
            core::slice::from_raw_parts_mut(bs.as_mut_ptr(), len)
        };
        unsafe { core::str::from_utf8_unchecked_mut(bs) }
    }

    /// Returns a pointer to the first byte of the character's UTF-8
    /// representation. The pointer is valid only as long as the reference
    /// it was created from remains valid.
    #[inline(always)]
    #[allow(dangling_pointers_from_locals)]
    pub fn as_ptr(&self) -> *const u8 {
        &self as *const _ as *const u8
    }

    /// Converts to the primitive type [`char`].
    ///
    /// The built-in `char` type uses a different representation, so this
    /// operation requires conversion. Staying in the world of UTF-8 -- using
    /// `str` in combination with `u8char` -- avoids these conversions.
    pub const fn to_char(self) -> char {
        let bs = self.to_byte_array();
        let b0 = bs[0];
        if b0 < 0x80 {
            return b0 as char; // fast path for ASCII
        }

        // The rest of this is based on standard library's
        // `core/src/str/validations.rs`, and particularly `fn next_code_point`.

        // Mask of the data portion of a continuation byte.
        const CONT_MASK: u8 = 0b0011_1111;
        const fn do_first_byte(byte: u8, width: u32) -> u32 {
            (byte & (0x7F >> width)) as u32
        }
        const fn do_cont_byte(ch: u32, byte: u8) -> u32 {
            (ch << 6) | (byte & CONT_MASK) as u32
        }

        let init = do_first_byte(b0, 2);
        let b1 = bs[1];
        let mut cv = do_cont_byte(init, b1);
        if b0 >= 0xe0 {
            let b2 = bs[2];
            let next = do_cont_byte((b1 & CONT_MASK) as u32, b2);
            cv = (init << 12) | next;
            if b0 >= 0xf0 {
                let b3 = bs[3];
                cv = ((init & 7) << 18) | do_cont_byte(next, b3);
            }
        }
        debug_assert!(char::from_u32(cv).is_some());
        // Safety: u8char always has valid UTF-8 in 0..len.
        unsafe { char::from_u32_unchecked(cv) }
    }

    /// Interprets the value as an array of four bytes. Bytes beyond the
    /// reported length of the value are zero.
    #[inline(always)]
    pub(crate) const fn to_byte_array(self) -> [u8; 4] {
        unsafe { core::mem::transmute(self) }
    }
}

impl AsRef<str> for u8char {
    /// Equivalent to [`Self::as_str`].
    #[inline(always)]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl core::borrow::Borrow<str> for u8char {
    /// Equivalent to [`Self::as_str`].
    #[inline(always)]
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<[u8]> for u8char {
    /// Equivalent to [`Self::as_bytes`].
    #[inline(always)]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

/// Equivalent to [`Self::from_char`].
impl From<char> for u8char {
    #[inline(always)]
    fn from(value: char) -> u8char {
        u8char::from_char(value)
    }
}

/// Equivalent to [`Self::to_char`].
impl Into<char> for u8char {
    #[inline(always)]
    fn into(self) -> char {
        self.to_char()
    }
}

impl core::cmp::PartialEq<str> for u8char {
    #[inline(always)]
    fn eq(&self, other: &str) -> bool {
        self.as_str().eq(other)
    }
}

/// The ordering of [`u8char`] values is the same as the corresponding [`str`].
impl core::cmp::PartialOrd for u8char {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.as_str().partial_cmp(other.as_str())
    }

    #[inline(always)]
    fn lt(&self, other: &Self) -> bool {
        self.as_str().lt(other.as_str())
    }

    #[inline(always)]
    fn le(&self, other: &Self) -> bool {
        self.as_str().le(other.as_str())
    }

    #[inline(always)]
    fn gt(&self, other: &Self) -> bool {
        self.as_str().gt(other.as_str())
    }

    #[inline(always)]
    fn ge(&self, other: &Self) -> bool {
        self.as_str().ge(other.as_str())
    }
}

impl core::cmp::PartialOrd<str> for u8char {
    #[inline(always)]
    fn partial_cmp(&self, other: &str) -> Option<core::cmp::Ordering> {
        self.as_str().partial_cmp(other)
    }

    #[inline(always)]
    fn lt(&self, other: &str) -> bool {
        self.as_str().lt(other)
    }

    #[inline(always)]
    fn le(&self, other: &str) -> bool {
        self.as_str().le(other)
    }

    #[inline(always)]
    fn gt(&self, other: &str) -> bool {
        self.as_str().gt(other)
    }

    #[inline(always)]
    fn ge(&self, other: &str) -> bool {
        self.as_str().ge(other)
    }
}

impl core::cmp::Ord for u8char {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl core::hash::Hash for u8char {
    /// Hashing for [`u8char`] is delegated to the [`core::hash::Hash`]
    /// implementation of [`str`].
    #[inline(always)]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl core::ops::Deref for u8char {
    type Target = str;

    /// Equivalent to [`Self::as_str`], giving access to all of the methods
    /// supported for shared references to [`str`].
    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl core::ops::DerefMut for u8char {
    /// Equivalent to [`Self::as_mut_str`], giving access to all of the methods
    /// supported for mutable references to [`str`].
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_str()
    }
}

impl core::fmt::Display for u8char {
    #[inline(always)]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.to_char().fmt(f)
    }
}

impl core::fmt::Debug for u8char {
    #[inline(always)]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.to_char().fmt(f)
    }
}

#[cfg(feature = "unstable_niches")]
const _: () = {
    // This is here so that any caller that is trying to rely on the
    // unstable_niches feature will get a compile error if it stops allowing
    // a same-sized Option<u8char> in a future version of Rust, since this
    // is currently relying on a perma-unstable feature that could go away
    // or change behavior in future versions.
    if core::mem::size_of::<u8char>() != core::mem::size_of::<Option<u8char>>() {
        panic!("unstable_niches unable to make u8char same size as Option<u8char>")
    }
};

/// Convenience trait for obtaining an iterator over the characters of a
/// `str` as [`u8char`].
pub trait AsU8Chars {
    type Iter: Iterator<Item = u8char>;

    /// Returns an iterator over the UTF-8 characters in the value.
    fn u8chars(self) -> Self::Iter;
}

#[cfg(test)]
mod tests;
