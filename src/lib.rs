#![cfg_attr(
    feature = "unstable_niches",
    allow(internal_features),
    feature(rustc_attrs)
)]
#![cfg_attr(not(test), no_std)]

pub mod util;

/// Similar to `char` in that it represents a Unicode scalar value, but uses
/// valid, canonical UTF-8 as the in-memory representation, and so it can be
/// converted more cheaply from the prefix of a `str` and can be interpreted
/// as a single-character `str` without re-encoding.
///
/// Has the same size and alignment as `char`, but _does not_ have the same
/// representation.
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

    #[inline(always)]
    pub const fn len(self) -> usize {
        let bs = self.to_byte_array();
        util::length_by_initial_byte_valid(bs[0])
    }

    #[inline]
    pub const fn as_bytes(&self) -> &[u8] {
        let len = self.len();
        unsafe {
            let bs: &[u8; 4] = core::mem::transmute(self);
            core::slice::from_raw_parts(bs.as_ptr(), len)
        }
    }

    #[inline(always)]
    pub const fn as_str(&self) -> &str {
        unsafe { core::str::from_utf8_unchecked(&self.as_bytes()) }
    }

    /// Returns a pointer to the first byte of the character's UTF-8
    /// representation. The pointer is valid only as long as the reference
    /// it was created from remains valid.
    #[inline(always)]
    #[allow(dangling_pointers_from_locals)]
    pub fn as_ptr(&self) -> *const u8 {
        &self as *const _ as *const u8
    }

    /// Interprets the value as an array of four bytes. Bytes beyond the
    /// reported length of the value are zero.
    pub(crate) const fn to_byte_array(self) -> [u8; 4] {
        unsafe { core::mem::transmute(self) }
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

#[cfg(test)]
mod tests;
