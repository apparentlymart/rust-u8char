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
        util::length_by_initial_byte_valid(self.first_byte())
    }

    #[inline(always)]
    pub const fn is_ascii(self) -> bool {
        self.first_byte() < 0x80
    }

    #[inline(always)]
    pub const fn first_byte(self) -> u8 {
        self.to_byte_array()[0]
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
    #[inline(always)]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl core::borrow::Borrow<str> for u8char {
    #[inline(always)]
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<[u8]> for u8char {
    #[inline(always)]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl From<char> for u8char {
    #[inline(always)]
    fn from(value: char) -> u8char {
        u8char::from_char(value)
    }
}

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
    #[inline(always)]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl core::ops::Deref for u8char {
    type Target = str;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        self.as_str()
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

#[cfg(test)]
mod tests;
