//! Utilities for a `Cow`-like wrapper around `Arc` and `Vec`
//!
//! This is a wrapper module for the [`Raw`] type
//!
//! [`Raw`]: enum.Raw.html

use std::ops::{Deref, Range};
use std::sync::Arc;

/// A slice of memory - either a `Vec<T>` or a range of an `Arc<Vec<T>>`
///
/// This is provided to allow minimal reallocation when changes are made to large files. It can be
/// constructed with the [`from_range`] method on an existing `Arc<Vec<T>>` or directly via
/// conversion from `Vec<T>` with the `From` trait.
///
/// [`from_range`]: #method.from_range
#[derive(Debug, Clone)]
pub struct Raw<T> {
    inner: RawInner<T>,
}

/// The *actual* `Raw` type
///
/// This is made private to avoid exposing the internals of the type; we don't want people
/// constructing `Ref` themselves.
#[derive(Debug, Clone)]
enum RawInner<T> {
    Ref(Arc<Vec<T>>, Range<usize>),
    Owned(Vec<T>),
}

impl<T> Raw<T> {
    // Checks the bounds on the range as well
    pub fn from_range(arc: Arc<Vec<T>>, range: Range<usize>) -> Self {
        if range.start > arc.len() {
            panic!(
                "Index out of bounds: range start {} is greater than len {}",
                range.start,
                arc.len()
            );
        } else if range.end > arc.len() {
            panic!(
                "Index out of bounds: range end {} is greater than len {}",
                range.end,
                arc.len()
            );
        }

        Raw {
            inner: RawInner::Ref(arc, range),
        }
    }
}

impl<T> From<Vec<T>> for Raw<T> {
    fn from(owned: Vec<T>) -> Self {
        Raw {
            inner: RawInner::Owned(owned),
        }
    }
}

impl<T> Deref for Raw<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        match &self.inner {
            RawInner::Ref(a, range) => &a[range.clone()],
            RawInner::Owned(v) => v.as_ref(),
        }
    }
}
