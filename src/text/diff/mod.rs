//! Byte-wise text differences; wrapper module for [`Diff`] and companion types

use std::fmt::{self, Debug, Formatter};
use std::ops::{Deref, Range};

// TODO-FEATURE: `Collect` is valuable, but currently not needed.
// mod collect;
// pub use collect::Collect;

/// A marker trait for various types of containers that can be used to reference byte slices
///
/// This is what's used for the bound on the generic parameter for [`Diff`]s. This trait is
/// implemented on all types that *can* satisfy the bound.
pub trait BytesRef: Clone + Deref<Target = [u8]> {}

impl<T> BytesRef for T where T: Clone + Deref<Target = [u8]> {}

/// A single change to a source set of bytes
///
/// This is inspired by Google's [diff-match-patch] library and its specification of a format
/// similar to [Unidiff]: it includes the bytes being replaced, their location, but not the context
/// on either side. The reason we don't include any context is because it becomes prohibitively
/// difficult to maintain within the [`HistoryCore`] system, and would simply be an additional
/// source of bugs.
///
/// Typical construction of a `Diff` is done directly through the fields. This is because they
/// typically operate on data structures that are complex enough that a generic solution would be
/// just as cumbersome as manual initialization.
///
/// The generic type parameter serves as a way to generalize over byte slices, allowing advanced
/// methods of preventing expensive cloning.
///
/// [diff-match-patch]: https://github.com/google/diff-match-patch/wiki/Unidiff
/// [Unidiff]: https://en.wikipedia.org/wiki/Diff#Unified_format
/// [`HistoryCore`]: super::history_core::HistoryCore
/// [`apply`]: Self::apply
#[derive(Clone)]
pub struct Diff<R> {
    /// The index in the set of bytes to make the change
    pub diff_idx: usize,

    /// The original values being replaced
    ///
    /// This is provided both as context and so that diffs can be reversed
    pub old: R,

    /// The new values replacing `old` at `diff_idx`.
    pub new: R,
}

impl<R: BytesRef> Debug for Diff<R> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("Diff")
            .field("diff_idx", &self.diff_idx)
            .field("old", &&self.old[..])
            .field("new", &&self.new[..])
            .finish()
    }
}

impl<R: Deref<Target = [u8]>> Diff<R> {
    /// Returns the byte range being replaced
    ///
    /// Equivalent to
    /// ```ignore
    /// self.diff_idx .. self.diff_idx + self.old.len()
    /// ```
    pub fn old_range(&self) -> Range<usize> {
        self.diff_idx..self.diff_idx + self.old.len()
    }

    /// Analagous to [`old_range`], but for `self.new`
    ///
    /// This method returns the range that -- after applying the diff -- would correspond to the
    /// values set by `new`.
    ///
    /// Equivalent to
    /// ```ignore
    /// self.diff_idx .. self.diff_idx + self.new.len()
    /// ```
    ///
    /// [`old_range`]: Self::old_range
    pub fn new_range(&self) -> Range<usize> {
        self.diff_idx..self.diff_idx + self.new.len()
    }

    /// Applies the `Diff` to an object that supports it, panicking if it is incompatible with the
    /// state of the object
    pub fn apply<B: ByteReplace>(&self, obj: &mut B) {
        // @def "Diff::apply internals" v0
        //
        // TODO-ERROR: We shouldn't use plain assertions here; the panic messages should be a
        // *little* nicer.
        let end_idx = self.diff_idx + self.old.len();

        // Check that the object has the required length:
        assert!(end_idx <= obj.length());
        // Check that the old values match:
        assert!(obj.is_eq(self.diff_idx, &self.old));

        // Once the checks have passed, we perform the actual replacement:
        obj.replace(self.diff_idx..end_idx, &self.new);
    }

    /// Applies the inverse of the diff; equivalent to `diff.invert.apply(obj)`, but doesn't
    /// require ownership.
    pub fn apply_inverted<B: ByteReplace>(&self, obj: &mut B) {
        // This function is exactly the same as `apply`, except with `self.old` and `self.new`
        // swapped
        //
        // @req "Diff::apply internals" v0
        let end_idx = self.diff_idx + self.new.len();
        assert!(obj.length() < end_idx);
        assert!(obj.is_eq(self.diff_idx, &self.new));
        obj.replace(self.diff_idx..end_idx, &self.old);
    }

    /// Produces the inverse of the `Diff` - i.e. the diff that can be applied to undo the
    /// original's replacement
    pub fn invert(self) -> Self {
        Diff {
            // Just swap the order of 'old' and 'new'
            old: self.new,
            new: self.old,
            // ... everything else stays the same
            diff_idx: self.diff_idx,
        }
    }
}

/// A trait for types that can be modified by a [`Diff`]
///
/// Implementations are provided for `Vec<u8>` and `{Box,Arc,Rc}<[u8]>`. Typically however, the
/// best type to use will usually be [`ByteTree`], due to its performance characteristics.
///
/// [`ByteTree`]: crate::text::objects::ByteTree
pub trait ByteReplace {
    /// Returns the length in bytes of the object
    ///
    /// This is named `length` instead of `len` to avoid naming conflicts
    fn length(&self) -> usize;

    /// Returns whether the bytes at the given index are equal to what's expected
    ///
    /// This function may assume that `self.length()` is less than `start_idx + bytes.len()`,
    /// panicking if not. This function *cannot* perform unsafe code under this assumption.
    ///
    /// We use an `&mut self` because certain data structures (namely: `ByteTree`) require a
    /// mutable reference to extract ranges.
    fn is_eq(&mut self, start_idx: usize, bytes: &[u8]) -> bool;

    /// Replaces the byte range with the given values
    fn replace(&mut self, replace: Range<usize>, with: &[u8]);
}

macro_rules! impl_byte_replace_container {
    ($container:ty) => {
        impl ByteReplace for $container {
            fn length(&self) -> usize {
                self.len()
            }

            fn is_eq(&mut self, start_idx: usize, bytes: &[u8]) -> bool {
                &self[start_idx..start_idx + bytes.len()] == bytes
            }

            fn replace(&mut self, replace: Range<usize>, with: &[u8]) {
                // Create a new backing allocation; we always use a box here
                let new_len = self.len() + with.len() - replace.len();
                let mut new = vec![0_u8; new_len].into_boxed_slice();

                // And then copy the three pieces into it
                new[..replace.start].copy_from_slice(&self[..replace.start]);

                let with_end = replace.start + with.len();
                new[replace.start..with_end].copy_from_slice(with);
                new[with_end..].copy_from_slice(&self[replace.end..]);

                *self = new.into();
            }
        }
    };
}

// TODO-ALG: the `Vec` implementation can possibly be sped up significantly
impl_byte_replace_container!(Vec<u8>);
impl_byte_replace_container!(Box<[u8]>);
impl_byte_replace_container!(std::sync::Arc<[u8]>);
impl_byte_replace_container!(std::rc::Rc<[u8]>);
