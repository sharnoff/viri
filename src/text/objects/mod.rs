//! Concrete types for representing dynamic text objects
//!
//! There's a wide variety of types here, provided at different levels of abstraction. At the very
//! bottom, we have the [`ByteTree`], which is composed entirely of [`ByteSlice`s]. For shared text
//! objects, this serves as a ground truth for the full content of the text object.
//!
//! [`ByteSlice`s]: ByteSlice
//!
//! Providing shared access to a `ByteTree` is done with the [`SharedByteTree`] type, which
//! individually tracks changes so that each "user" of a `ByteTree` can process the changes
//! separately.
//!
//! Above these, we have [`TextTree`], which is generic over the encoding of the file and stores
//! additional information about how individual characters are displayed. This is the type used as
//! the implementor of [`Text`] in most ways of viewing a file.
//!
//! [`Text`]: super::Text
//!
//! Having multiple ways of viewing the same file allows us to do interesting things -- like
//! viewing the raw bytes of a file, as we're editing it.

mod byte_tree;
pub mod encoding;
mod shared;
mod slice;
mod text_tree;

#[doc(inline)]
pub use byte_tree::ByteTree;
#[doc(inline)]
pub use encoding::{Encoding, FileEncoding};
#[doc(inline)]
pub use shared::{Change, SharedByteTree};
#[doc(inline)]
pub use slice::ByteSlice;
#[doc(inline)]
pub use text_tree::TextTree;

/// (*Internal*) The maximum allowed size of an inlined [`ByteSlice`]
const INLINE_SIZE: usize = 16;
