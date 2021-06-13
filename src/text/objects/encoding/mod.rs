//! Wrapper module for the [`Encoding`] trait

use super::ByteSlice;
use std::borrow::Cow;
use std::ops::Range;

mod utf8;

/// A particular byte encoding, used to decode the bytes of a text object into strings, and vice
/// versa
///
/// While implementors of this trait are typically file encodings, like UTF-8, it's also possible
/// to "abuse" the implementation to provide non-trivial functionality. One such example is the
/// byte-wise view into a file, which expands each byte into a pair of hex digits. Use cases like
/// that are why we generally don't require that encodings are their own inverse -- i.e. that
/// going from bytes to a string and back produces the same bytes.
///
/// Generic usage over mutliple encodings is not used outside of a couple particular cases, so it's
/// generally not provided for. The [`FileEncoding`] type captures a few stateless file encodings
/// -- essentially the "normal" ones that you might already know.
pub trait Encoding {
    /// Decodes a chunk of bytes, also returning the range of the original used
    ///
    /// The arguments `bof` and `eof` indicate whether the given chunk is at the beginning or end
    /// of the "file", respectively. It is possible for these to both be true. If `bof` is true,
    /// the returned range *must* start with the beginning of the chunk. Likewise, if `eof` is
    /// true, the returned range *must* end with the end of the chunk.
    ///
    /// If returned range is empty, the string should be as well. An empty range will cause this
    /// function to be called again with a larger chunk. As specified above, the returned range
    /// should never be empty if either of `bof` or `eof` are true.
    ///
    /// If the returned string is invalid *and* either `bof` or `eof` is true, then callers can
    /// assume that it's *because* the chunk is at the beginning or end of the text.
    fn decode_chunk<'a>(
        &self,
        chunk: &'a [u8],
        bof: bool,
        eof: bool,
    ) -> (DecodedStr<'a>, Range<usize>);

    /// Encodes the string as a slice of bytes
    ///
    /// This method is pretty straightforward. It cannot be assumed that all modifications to the
    /// underlying text object will pass through this function; direct operations on the bytes may
    /// be supported outside of the encoding.
    ///
    /// Note that it's assumed by callers that the returned bytes will be valid in any position in
    /// the text. This may mean that some encodings cannot provide an implementation of this trait.
    fn encode(&self, string: &str) -> ByteSlice;

    /// Returns the size of the character, in bytes, at the start of `chunk`
    ///
    /// The returned size *must* be less than or equal to `chunk.len()`; if the slice isn't big
    /// enough, returning `None` will prompt this function to be called again with a larger chunk.
    /// The size must also not be equal to zero.
    ///
    /// If `eof` is true, there aren't any more bytes that could be supplied, so the returned size
    /// cannot be `None`.
    ///
    /// When provided unambiguously invalid bytes, this function should always return `Some(1)`.
    fn char_size(&self, chunk: &[u8], eof: bool) -> Option<usize>;
}

/// The output of a decoded chunk -- either a successful string, or an indication that the range of
/// bytes was invalid
///
/// If the range of bytes is invalid, the caller is responsible for determining an appropriate
/// rendering of the bytes that indicates as such.
pub enum DecodedStr<'a> {
    /// The bytes were able to be decoded, and doing so produced this string
    ///
    /// We use a `Cow<str>` because -- more often than not -- files are going to be encoded with
    /// UTF-8, which we can just directly convert to a string without reallocating.
    Success(Cow<'a, str>),
    /// The entire range of bytes is invalid, and should be displayed in way that indicates as
    /// such.
    Invalid,
}

/// The encoding of a particular file
///
/// Currently, we only support UTF-8. More encodings are planned, but not immediately necessary.
// @def "only utf8 supported but plans for more" v0
pub enum FileEncoding {
    Utf8,
}

impl Encoding for FileEncoding {
    fn decode_chunk<'a>(
        &self,
        chunk: &'a [u8],
        bof: bool,
        eof: bool,
    ) -> (DecodedStr<'a>, Range<usize>) {
        match self {
            Self::Utf8 => utf8::Utf8.decode_chunk(chunk, bof, eof),
        }
    }

    fn encode(&self, string: &str) -> ByteSlice {
        match self {
            Self::Utf8 => utf8::Utf8.encode(string),
        }
    }

    fn char_size(&self, chunk: &[u8], eof: bool) -> Option<usize> {
        match self {
            Self::Utf8 => utf8::Utf8.char_size(chunk, eof),
        }
    }
}
