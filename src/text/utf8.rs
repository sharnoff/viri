//! Tools for decoding UTF-8 encoded text
//!
//! Why aren't we using the standard library's set? We want to go through character-by-character
//! and display a specific values for invalid byte sequences, instead of the typical
//! "all-or-nothing" approach.
// Much of this module originally appeared in: github.com/mk-lang/mk, but we've since abandoned
// that project.

/// The default newline separator
///
/// This may be replaced by a per-file config in the future.
pub const DEFAULT_NEWLINE: &'static [u8] = b"\n";

/// Encodes a string as a `Vec<u8>`
pub fn into_bytes(s: &str) -> Vec<u8> {
    s.into()
}

/// Tries to get the next utf8 encoded character from the sequence of bytes.
///
/// On success, this function returns the produced character in addition to the number of bytes
/// consumed to produce it. For error cases, the first byte is returned.
///
/// Failure can happen from (a) invalid utf-8 sequences, or (b) the resulting u32 being outside of
/// the range of possible unicode scalar values.
///
/// The sequence of bytes should be non-empty. This function will panic (with a debug assertion) if
/// that is not the case.
pub fn try_next_utf8(bytes: &[u8]) -> Result<(char, usize), u8> {
    // For this function, refer to section three of the utf-8 definition:
    //
    //     Decoding a UTF-8 character proceeds as follows:
    //
    //     1.  Initialize a binary number with all bits set to 0. Up to 21
    //         bits may be needed.
    //
    //     2.  Determine which bits encode the character number from the
    //         number of octets in the sequence and the second column of the
    //         table above (the bits marked x).
    //
    //     3.  Distribute the bits from the sequence to the binary number,
    //         first the lower-order bits from the last octet of the sequence
    //         and proceeding to the left until no x bits are left. The
    //         binary number is now equal to the character number.
    //
    // The referenced table is:
    //
    //     Char. number range  |        UTF-8 octet sequence
    //        (hexadecimal)    |              (binary)
    //     --------------------+--------------------------------------------
    //     0000 0000-0000 007F | 0xxxxxxx
    //     0000 0080-0000 07FF | 110xxxxx 10xxxxxx
    //     0000 0800-0000 FFFF | 1110xxxx 10xxxxxx 10xxxxxx
    //     0001 0000-0010 FFFF | 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
    //
    // The following code should then be fairly self-explanatory.

    debug_assert!(!bytes.is_empty());

    let buf = {
        let mut buf = [0_u8; 4];
        let n = bytes.len().min(4);
        buf[0..n].copy_from_slice(&bytes[0..n]);
        buf
    };

    // Get the number of bytes we're expecting, given the first character.
    let n_bytes = match expected_utf8_size(buf[0]) {
        Some(n) => n,
        None => {
            // We have a single invalid byte, so we'll return that.
            return Err(buf[0]);
        }
    };

    if n_bytes > bytes.len() {
        return Err(buf[0]);
    }

    // All the bytes should be there. We now just have to ensure that the
    // rest of the bytes are continuation bytes.
    for &b in buf[1..n_bytes].iter() {
        if !is_continuation_byte(b) {
            return Err(buf[0]);
        }
    }

    // Now that we know all of the bytes are valid, we can construct the u32
    // corresponding to the utf-8 value
    let unicode_value = match n_bytes {
        1 => buf[0] as u32,
        2 => ((buf[1] & !CONT_MASK) as u32) + (((buf[0] & !0b1100_0000) as u32) << 6),
        3 => {
            ((buf[2] & !CONT_MASK) as u32)
                + (((buf[1] & !CONT_MASK) as u32) << 6)
                + (((buf[0] & !0b1110_0000) as u32) << 12)
        }
        4 => {
            ((buf[3] & !CONT_MASK) as u32)
                + (((buf[2] & !CONT_MASK) as u32) << 6)
                + (((buf[1] & !CONT_MASK) as u32) << 12)
                + (((buf[0] & !0b1111_0000) as u32) << 18)
        }
        // We should never get a value for `n` greater than
        _ => unreachable!(),
    };

    let c = match std::char::from_u32(unicode_value) {
        None => {
            return Err(buf[0]);
        }
        Some(c) => c,
    };

    Ok((c, n_bytes))
}

/// Detects the character sequence being used to denote a line break
///
/// ### Semantics
///
/// If the slice does not contain any newline characters, this function will return `None`.
/// Otherwise, it will return either `"\n"` or `"\r\n"`, where the latter is only ever returned if
/// all newline characters are immediately preceeded by a carriage return.
pub fn detect_newline(bytes: &[u8]) -> Option<&'static [u8]> {
    if bytes.is_empty() {
        // If no bytes, we can't tell what the line breaks are. We'll leave it up to the caller
        return None;
    } else if bytes[0] == b'\n' {
        // In this case, there can't be a preceeding '\r' because this is the first index
        return Some(b"\n");
    }

    // The set of all characters that preceed a newline
    let mut preceeding_chars = bytes
        .iter()
        .zip(bytes[1..].iter())
        .filter(|(_, c)| **c == b'\n')
        .map(|(c, _)| c);

    let next = preceeding_chars.next();

    // If there's no newlines, we still can't tell what the line breaks are, so we'll return
    // `None`.
    if next.is_none() {
        return None;
    }

    // Per the comment at the top, we'll only return "\r\n" if all of the preceeding characters are
    // exactly '\r'
    if *next.unwrap() == b'\r' && preceeding_chars.all(|&c| c == b'\r') {
        Some(b"\r\n")
    } else {
        Some(b"\n")
    }
}

fn expected_utf8_size(b: u8) -> Option<usize> {
    const INVALID: u8 = 5;
    const CONT: u8 = 0;

    match UTF8_CHAR_WIDTH[b as usize] {
        INVALID | CONT => None,
        w => Some(w as usize),
    }
}

// Internal helper function
fn is_continuation_byte(b: u8) -> bool {
    // continuation bytes start '10'
    b & 0b1100_0000 == 0b1000_0000
}

// Slightly modified version of a similar array in the rust source, at
//   src/core/str/mod.rs, line 1621
// at time of writing (Feb. 01, 2020)
//
// Where the the file above gives both continuation bytes and invalid bytes a
// value of 0, we're instead giving invalid bytes an expected length of 5,
// which is not possible in utf-8. We're basing this on a chart from wikipedia:
//   https://en.wikipedia.org/wiki/UTF-8#Codepage_layout
//
// We make it static (not const) because it makes no difference in the runtime:
// they both will require the same pointer arithmetic. The only difference is
// in the size of the compiled binary, which will be larger if it is declared
// as `const`.
static UTF8_CHAR_WIDTH: [u8; 256] = [
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    5, 5, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
];

const CONT_MASK: u8 = 0b1100_0000;
