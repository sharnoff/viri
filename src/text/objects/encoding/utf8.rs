//! Implementation of the UTF-8 encoding
//!
//! Why aren't we using the standard library's utilities? We want to be able to go through,
//! character-by-character and isolate invaid byte sequences -- the standard library's
//! all-or-nothing approach would be much more inefficient here.

use super::{ByteSlice, DecodedStr, Encoding, Range};
// @def "utf8 intrinsics::{likely, unlikely}" v0
use std::intrinsics::{likely, unlikely};

/// Dummy type with an implementation of [`Encoding`] compliant with the UTF-8 spec
pub struct Utf8;

impl Encoding for Utf8 {
    fn decode_chunk<'a>(
        &self,
        chunk: &'a [u8],
        bof: bool,
        eof: bool,
    ) -> (DecodedStr<'a>, Range<usize>) {
        // Checking whether a slice is ascii is *very* quick. Most things are going to be entirely
        // ascii, so it's well worth doing this optimistic check first.
        if likely(chunk.is_ascii()) {
            // SAFETY: All valid 7-bit ascii is valid utf-8
            let s = unsafe { std::str::from_utf8_unchecked(chunk).into() };
            return (DecodedStr::Success(s), 0..chunk.len());
        }

        // If it's not simple ascii, we need to actually check. We need to go through the bytes to
        // determine if there's anything that's not valid utf-8. There's a couple cases to consider
        // here.
        //
        // If `chunk` starts with invalid utf-8, but the rest of the string is ok, we want to
        // return the part that's ok with a range that doesn't contain the start. But if `bof` is
        // true, we should return the part at the start as invalid -- we aren't required to, but it
        // makes things easier. (If `bof` isn't true, those might not even be invalid!)
        //
        // If `chunk` has invalid utf-8 but there's valid parts before it, we should return those
        // valid parts first -- even if `eof` is true.
        //
        // Otherwise, if there's no invalid parts, we should just return.

        // Part 1: check the very start of `chunk` for invalid bytes.
        let first_valid = match first_valid_char_idx(chunk) {
            // If we don't have enough information, we should return an empty range to get more.
            None if !eof => return (DecodedStr::Invalid, 0..0),
            None /*  eof */ => chunk.len(),
            Some(idx) => idx,
        };

        // If the start of the string is *definitely* invalid, then there's two cases:
        //  (1) if `bof` is true, then there isn't anything before it; we should just return the
        //      values
        //  (2) if `bof` is false AND `first_valid` is contained within the slice, then we'll
        //      return the part of the slice that is valid.
        if first_valid != 0 && (bof || first_valid == chunk.len()) {
            if bof {
                return (DecodedStr::Invalid, 0..0);
            }

            return (DecodedStr::Invalid, 0..first_valid);
        }

        // We now know that some portion of the slice is valid. We'll find out how big that is and
        // return it.
        let first_invalid = first_invalid_char_idx(&chunk[first_valid..]).unwrap_or(chunk.len());
        assert!(first_invalid != first_valid);

        let range = first_valid..first_invalid;
        // SAFETY: The bytes within the range are required to be valid utf-8. This is guaranteed by
        // the implemenation of `first_valid_char_idx` and `first_invalid_char_idx`.
        let s = unsafe { std::str::from_utf8_unchecked(&chunk[range.clone()]) };
        (DecodedStr::Success(s.into()), range)
    }

    fn encode(&self, string: &str) -> ByteSlice {
        ByteSlice::new(string.as_bytes())
    }

    fn char_size(&self, chunk: &[u8], eof: bool) -> Option<usize> {
        match next_char_size(chunk) {
            Ok(Some(n)) => Some(n),
            // According to the specification of this function, invalid characters must return
            // Some(1)
            Err(()) => Some(1),
            // If we needed more input, but that's the end, this is also invalid
            Ok(None) if eof => Some(1),
            // But if there's more input available, we'll ask for it
            Ok(None) => None,
        }
    }
}

// Returns whether the byte is a "tail" byte, as defined in the ABNF in RFC 3629. Essentially:
// whether the byte matches 0b10xx_xxxx
fn is_utf8_tail(b: u8) -> bool {
    b & 0b1100_0000 == 0b1000_0000
}

// Returns the encoded length of a character starting with this byte, if such a character can exist
// in valid utf-8
fn encoded_len(b: u8) -> Result<usize, ()> {
    // To copy a table directly from the relevant RFC:
    //
    //   Char. number range  |        UTF-8 octet sequence
    //      (hexadecimal)    |              (binary)
    //   --------------------+------------------------------------
    //   0000 0000-0000 007F | 0xxxxxxx
    //   0000 0080-0000 07FF | 110xxxxx 10xxxxxx
    //   0000 0800-0000 FFFF | 1110xxxx 10xxxxxx 10xxxxxx
    //   0001 0000-0010 FFFF | 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
    //
    // Testing this is therefore fairly straightforward. The implementation in the rust standard
    // library uses a table, but that's probably overkill for our purposes, given that it's harder
    // to verify it's correct.

    if likely(b & 0b1000_0000 == 0) {
        Ok(1)
    } else if b & 0b1110_0000 == 0b1100_0000 {
        Ok(2)
    } else if b & 0b1111_0000 == 0b1110_0000 {
        Ok(3)
    } else if b & 0b1111_1000 == 0b1111_0000 {
        Ok(4)
    } else {
        Err(())
    }
}

// Returns the size of the character encoded at the start of `chunk`, if it's a valid encoding.
// Returns Err(()) if the character is invalid, or Ok(None) if there isnt' enough to tell
// Otherwise returns Err(())
//
// Assumes that chunk.len() > 0
fn next_char_size(chunk: &[u8]) -> Result<Option<usize>, ()> {
    let expected_len = encoded_len(chunk[0])?;

    // If we're expecting more bytes to make up the character than we have available, we might
    // not be able to return anything.
    //
    // We *can* look at the bytes that are already there, though:
    if unlikely(expected_len > chunk.len()) {
        // If this would be invalid anyways with more bytes, don't bother asking for more.
        //
        // This isn't 100% accurate -- in some cases, we might say that something's *possibly*
        // valid, even though we already have the information to know that that's not the case.
        // It's honestly just not worth the effort to write a perfect implementation.
        if chunk[1..].iter().any(|&b| !is_utf8_tail(b)) {
            return Err(());
        }

        // Otherwise, there actually isn't enough
        return Ok(None);
    }

    // We now know that `chunk.len() <= expected_len`.
    let is_valid = match expected_len {
        1 => likely(true),

        // There's a table from the RFC that we'll reference ehre:
        //
        //   Char. number range  |        UTF-8 octet sequence
        //      (hexadecimal)    |              (binary)
        //   --------------------+------------------------------------
        //   0000 0000-0000 007F | 0xxxxxxx
        //   0000 0080-0000 07FF | 110xxxxx 10xxxxxx
        //   0000 0800-0000 FFFF | 1110xxxx 10xxxxxx 10xxxxxx
        //   0001 0000-0010 FFFF | 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
        //
        // Below this, it says:
        //
        //   It is important to note that the rows of the table are mutually exclusive, i.e.,
        //   there is only one valid way to encode a given character.
        //
        // What this means for us is that we can't just check that the bytes match a valid
        // pattern; we have to also check that the produced character number is inside the
        // range specified above.
        //
        // We *can* do it without explicitly producing the character number, though. Take the
        // second row as an example: because we know it should not have values in the range of
        // the first, at least one of the first 4 bits must be non-zero. (2nd row has 11 bits,
        // first row has 7). The total number of bits each row gets to encode with is:
        //   1: 7
        //   2: 11
        //   3: 16
        //   4: 21
        // So for row (n), we need one of the first #bits(n) - #bits(n-1) bits to be non-zero.
        // 4-byte encodings also have a maximum value, so we have to account for that as well.
        2 => is_utf8_tail(chunk[1]) && chunk[0] & !0b0001_1110 != 0,
        3 => {
            is_utf8_tail(chunk[2])
                && is_utf8_tail(chunk[1])
                && (chunk[0] & !0b0000_1111 | chunk[1] & 0b1000_0000 != 0)
        }
        4 => {
            is_utf8_tail(chunk[3])
                && is_utf8_tail(chunk[2])
                && is_utf8_tail(chunk[1])
                // 4-byte encodings are capped at 0x0010_FFFF, which is one less than
                // 0x0011_0000. The bits of that number are:
                //   0b0000_0000_0001_0001_0000_0000_0000_0000
                // There's 16 trailing zeroes, so the first five bits must be less than
                //   0b1_0001
                // We also need a lower-bound check that at least one of the first five bits is
                // non-zero. We can accomplish both of these by checking that EITHER (i) the
                // first bit is zero, or (ii) one of the others is, but NOT BOTH.
                && (chunk[0] & 0b0000_0100 == 0) !=
                    (chunk[0] & !0b0000_0011 | chunk[1] & 0b1100_0000 != 0)
        }
        // SAFETY: Have a look at the `encoded_len` function -- it won't return anything other
        // than 1, 2, 3, or 4.
        _ => unsafe { std::hint::unreachable_unchecked() },
    };

    if is_valid {
        Ok(Some(expected_len))
    } else {
        Err(())
    }
}

// Returns starting index of the first valid utf8-encoded character in the slice, if one exists
//
// This function makes no assumptions about the input.
fn first_valid_char_idx(slice: &[u8]) -> Option<usize> {
    for idx in 0..slice.len() {
        if let Ok(Some(n)) = next_char_size(&slice[idx..]) {
            return Some(n);
        }
    }

    None
}

// Returns the byte index of the first invalid byte, if one exists in the slice
//
// This function assumes that the slice starts with a valid utf8-encoded character. If the input
// ends too son, we assume that the encoded character is invalid.
fn first_invalid_char_idx(slice: &[u8]) -> Option<usize> {
    let mut idx = encoded_len(slice[0]).unwrap();
    while idx < slice.len() {
        match next_char_size(&slice[idx..]) {
            Ok(Some(n)) => idx += n,
            Err(()) | Ok(None) => return Some(idx),
        }
    }

    None
}
