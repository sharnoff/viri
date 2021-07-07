//! Utility wrapper module for [`MaxVec`]

use std::fmt::{self, Debug, Formatter};
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::ops::{Deref, DerefMut};
use std::ptr::copy_nonoverlapping;

/// A `Vec`-like container stored entirely on the stack
///
/// The constant parameter serves both as the maximum length of the vector and as an approximation
/// of the size of this struct. This is intentionally more limited than the standard library's
/// `Vec`, primarily because it doesn't need to be more complex; it's only really used inside
/// [`Diff`](crate::text::Diff)s
pub struct MaxVec<T, const CAP: usize> {
    len: usize,
    // SAFETY: the values[..len] are guaranteed to be initialized
    values: [MaybeUninit<T>; CAP],
}

impl<T, const CAP: usize> Drop for MaxVec<T, CAP> {
    fn drop(&mut self) {
        let len = self.len();
        for v in &mut self.values[..len] {
            // @req #![feature(maybe_uninit_extra)] v0
            unsafe { MaybeUninit::assume_init_drop(v) }
        }
    }
}

impl<T, const CAP: usize> MaxVec<T, CAP> {
    /// Creates a new [`MaxVec`], with no elements
    pub const fn new() -> Self {
        MaxVec {
            len: 0,
            // @req #![feature(maybe_uninit_uninit_array)] v0
            values: MaybeUninit::uninit_array(),
        }
    }

    /// Returns the capacity of the vector
    pub const fn capacity(&self) -> usize {
        CAP
    }

    /// Returns the number of elements in the vector
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the vector contains no elements
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns `true` if the vector cannot contain more elements
    pub const fn is_full(&self) -> bool {
        self.len == CAP
    }

    /// Appends the element onto the end of the vector, panicking if the length is equal to the
    /// capacity
    pub fn push(&mut self, elem: T) {
        if self.len() >= self.capacity() {
            panic!("length equal to capacity {}", self.capacity());
        }

        // @req #![feature(maybe_uninit_extra)] v0
        self.values[self.len].write(elem);
        self.len += 1;
    }

    /// Produces an iterator over references to the values in the `MaxVec`
    pub fn iter<'a>(&'a self) -> Iter<'a, T> {
        Iter {
            len: self.len,
            // @req #![feature(maybe_uninit_slice)] v0
            values: MaybeUninit::slice_as_ptr(&self.values),
            marker: PhantomData,
        }
    }

    /// Creates the vector from at most `CAP` elements of the iterator
    pub fn from_iter(iter: impl IntoIterator<Item = T>) -> Self {
        // This is fairly simple; we just continuously push to the vector until it's full or we run
        // out of space

        let mut this = Self::new();
        if this.capacity() == 0 {
            return this;
        }

        let mut iter = iter.into_iter();

        while let Some(item) = iter.next() {
            this.push(item);
            if this.is_full() {
                break;
            }
        }

        this
    }

    /// A version of [`from_iter`](Self::from_iter) that populates the vector from back-to-front
    ///
    /// It should be noted that this method does not reverse the *iterator*, but the placement of
    /// the elements from it. If there are fewer elements in the iterator than the capacity of this
    /// vector, the vector will be shifted so that the final element produced by the iterator is at
    /// index zero.
    ///
    /// ## Panics
    ///
    /// If the capacity of the vector is *equal* to `usize::MAX`, this function will always panic.
    /// They are not supported. This should hopefully not be an issue.
    pub fn from_iter_reversed(iter: impl IntoIterator<Item = T>) -> Self {
        // Our general strategy here is to construct the vector backwards, leaving space at the
        // start, until either the vector is full (in which case we're done), or the iterator runs
        // out of items (in which case we need to shift everything backwards)
        //
        // There's also some special care we need to take to ensure that the values are dropped
        // correctly if the iterator panics, so we have a wrapper type for handling that.

        // If we can't take any items, we don't bother. We need to have this guard here because the
        // later code assumes that the capacity is non-zero.
        if CAP == 0 {
            return Self::new();
        }

        // This assertion is required later down; see the comment inside the loop. Because `CAP` is
        // a generic parameter, this should hopefully force the function to be compiled as a
        #[rustfmt::skip]
        assert_ne!(CAP, usize::MAX, "vectors with capacity `usize::MAX` are not supported");

        // A reversed `MaxVec` so that we can
        struct RevMaxVec<T, const CAP: usize> {
            next_idx: usize,
            values: [MaybeUninit<T>; CAP],
        }

        impl<T, const CAP: usize> Drop for RevMaxVec<T, CAP> {
            fn drop(&mut self) {
                for idx in self.next_idx + 1..CAP {
                    unsafe {
                        // @req #![feature(maybe_uninit_extra)] v0
                        self.values[idx].assume_init_drop();
                    }
                }
            }
        }

        let mut iter = iter.into_iter();

        let mut rev: RevMaxVec<_, CAP> = RevMaxVec {
            next_idx: CAP - 1,
            // @req #![feature(maybe_uninit_uninit_array)] v0
            values: MaybeUninit::uninit_array(),
        };

        let mut len = 0;
        while let Some(item) = iter.next() {
            len += 1;

            // @req #![feature(maybe_uninit_extra)] v0
            rev.values[rev.next_idx].write(item);
            rev.next_idx = rev.next_idx.wrapping_sub(1);
            if rev.next_idx == usize::MAX {
                // If the index we just filled is zero, it'll underflow to usize::MAX;
                // we don't have any more values to add. This does mean that this function will
                // fail on arrays with length usize::MAX, but that's realistically not an issue.
                //
                // That's why we have the assertion at the top of this function.
                break;
            }
        }

        // If we got here, we ran out of items early; we need to shift everything back so that we
        // start at zero, instead of `next_idx + 1`

        // @req #![feature(maybe_uninit_uninit_array)] v0
        let mut new_values: [_; CAP] = MaybeUninit::uninit_array();
        let values_start = rev.next_idx.wrapping_add(1);

        // SAFETY: We know that the range provided here is valid and copying here is okay because
        // we're ensuring we don't drop the values first. From the rust reference, we have that not
        // running destructors is always safe, so we need to forget first. See:
        //   https://doc.rust-lang.org/reference/destructors.html#not-running-destructors
        let rev = std::mem::ManuallyDrop::new(rev);
        unsafe {
            copy_nonoverlapping(
                rev.values[values_start..].as_ptr(),
                new_values.as_mut_ptr(),
                len,
            );
        }

        MaxVec {
            len,
            values: new_values,
        }
    }
}

impl<T: Copy, const CAP: usize> MaxVec<T, CAP> {
    /// Constructs the vector from the given slice, panicking if it is too big
    ///
    /// Like [`from_slice_prefix`] and [`from_slice_suffix`], this method is very cheap.
    /// (Internally, it uses one of them.)
    ///
    /// [`from_slice_prefix`]: Self::from_slice_prefix
    /// [`from_slice_suffix`]: Self::from_slice_suffix
    ///
    /// ## Panics
    ///
    /// Panics if `slice.len() > CAP`.
    pub fn from_slice(slice: &[T]) -> Self {
        if slice.len() > CAP {
            panic!("slice len {} too long for capacity {}", slice.len(), CAP);
        }

        Self::from_slice_prefix(slice)
    }

    /// Constructs the vector - up to capacity - from as long a prefix of the slice as possible
    ///
    /// This uses `std::ptr::copy_nonoverlapping` internally, and so is typically very cheap,
    /// operating entirely on the stack.
    pub fn from_slice_prefix(slice: &[T]) -> Self {
        // @req #![feature(maybe_uninit_uninit_array)] v0
        let mut values: [MaybeUninit<T>; CAP] = MaybeUninit::uninit_array();

        let len = slice.len().min(CAP);
        // @req #![feature(maybe_uninit_slice)] v0
        let values_ptr = MaybeUninit::slice_as_mut_ptr(&mut values);
        unsafe { copy_nonoverlapping(slice.as_ptr(), values_ptr, len) };

        MaxVec { len, values }
    }

    /// Constructs the vector - up to capacity - from as long a suffix of the slice as possible
    ///
    /// This uses `std::ptr::copy_nonoverlapping` internally, and so is typically very cheap,
    /// operating entirely on the stack.
    pub fn from_slice_suffix(slice: &[T]) -> Self {
        // @req #![feature(maybe_uninit_uninit_array)] v0
        let mut values: [MaybeUninit<T>; CAP] = MaybeUninit::uninit_array();

        let len = slice.len().min(CAP);
        // @req #![feature(maybe_uninit_slice)] v0
        let values_ptr = MaybeUninit::slice_as_mut_ptr(&mut values);

        // Extract the suffix of the slice. We know this won't panic here because
        // `len <= slice.len()`
        let slice_ptr = slice[slice.len() - len..].as_ptr();
        unsafe { copy_nonoverlapping(slice_ptr, values_ptr, len) };

        MaxVec { len, values }
    }

    /// Analagous to [`Vec::extend_from_slice`], panics if the addition of the slice would fill up
    /// the capacity of the vector
    ///
    /// ## Panics
    ///
    /// Panics if `self.len() + slice.len() > CAP`.
    pub fn extend_from_slice(&mut self, slice: &[T]) {
        if self.len() + slice.len() > CAP {
            panic!(
                "extended len {} would be greater than capacity {}",
                self.len() + slice.len(),
                CAP
            )
        }

        // @req #![feature(maybe_uninit_slice)] v0
        let values_ptr = MaybeUninit::slice_as_mut_ptr(&mut self.values);
        let values_end_ptr = unsafe { values_ptr.add(self.len) };

        // SAFETY: We already know that `self.len() + slice.len() <= CAP`, and `values_end_ptr`
        // just points to the value at index `self.len()`, so this won't overrun the array.
        //
        // The slice and `self` cannot safely overlap because we have a mutable reference to
        // `self`.
        unsafe { copy_nonoverlapping(slice.as_ptr(), values_end_ptr, slice.len()) };

        self.len += slice.len();
    }
}

impl<T, const CAP: usize> Deref for MaxVec<T, CAP> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        // SAFETY: We know that the values 0..self.len() are initialized,
        // so it's safe to convert here.
        let len = self.len();
        // @req #![feature(maybe_uninit_slice)] v0
        unsafe { MaybeUninit::slice_assume_init_ref(&self.values[..len]) }
    }
}

impl<T, const CAP: usize> DerefMut for MaxVec<T, CAP> {
    fn deref_mut(&mut self) -> &mut [T] {
        // SAFETY: We know that the values 0..self.len() are initialized,
        // so it's safe to convert here.
        let len = self.len();
        // @req #![feature(maybe_uninit_slice)] v0
        unsafe { MaybeUninit::slice_assume_init_mut(&mut self.values[..len]) }
    }
}

impl<T, const CAP: usize> Default for MaxVec<T, CAP> {
    fn default() -> Self {
        Self::new()
    }
}

// This could use a clone bound on T, but then it wouldn't be a bitwise copy
impl<T: Copy, const CAP: usize> Clone for MaxVec<T, CAP> {
    fn clone(&self) -> Self {
        MaxVec {
            len: self.len,
            values: self.values,
        }
    }
}

impl<T: Debug, const CAP: usize> Debug for MaxVec<T, CAP> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(&**self, f)
    }
}

// this is pretty similar to what's used in the standard library to implement on `Vec`
macro_rules! impl_partial_eq {
    ( [$($vars:tt)*] $lhs:ty, $rhs:ty ) => {
        impl<A, B, $($vars)*> PartialEq<$rhs> for $lhs
        where
            A: PartialEq<B>,
        {
            fn eq(&self, other: &$rhs) -> bool {
                self[..] == other[..]
            }

            fn ne(&self, other: &$rhs) -> bool {
                self[..] != other[..]
            }
        }
    };
}

impl_partial_eq! { [const N: usize] Vec<A>, MaxVec<B, N> }
impl_partial_eq! { [const N: usize] MaxVec<A, N>, Vec<B> }
impl_partial_eq! { [const N: usize, const M: usize] MaxVec<A, N>, MaxVec<B, M> }
impl_partial_eq! { [const N: usize] MaxVec<A, N>, &[B] }
impl_partial_eq! { [const N: usize] MaxVec<A, N>, &mut [B] }
impl_partial_eq! { [const N: usize] &[A], MaxVec<B, N> }
impl_partial_eq! { [const N: usize] &mut [A], MaxVec<B, N> }
impl_partial_eq! { [const N: usize, const M: usize] MaxVec<A, N>, [B; M] }
impl_partial_eq! { [const N: usize, const M: usize] [A; N], MaxVec<B, M> }

impl<const CAP: usize, T> Eq for MaxVec<T, CAP> where T: Eq {}

/// An iterator over references to the values in a `MaxVec`
pub struct Iter<'a, T> {
    len: usize,
    values: *const T,
    marker: PhantomData<&'a ()>,
}

impl<'a, T: 'a> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        if self.len == 0 {
            return None;
        }

        let v = unsafe { &*self.values };
        self.values = unsafe { self.values.add(1) };
        self.len -= 1;
        Some(v)
    }
}

#[cfg(test)]
mod tests {
    use super::MaxVec;
    use std::sync::Arc;

    #[test]
    fn new_is_empty() {
        let this: MaxVec<(), 4> = MaxVec::new();

        assert!(this.is_empty());
        assert_eq!(this, []);
    }

    #[test]
    fn sample_len() {
        let mut this: MaxVec<(), 2> = MaxVec::new();
        this.push(());

        assert_eq!(this.len(), 1);
    }

    #[test]
    #[should_panic]
    fn overflow_panic() {
        let mut this: MaxVec<i32, 2> = MaxVec::new();
        this.push(1);
        this.push(2);
        this.push(3);
    }

    #[test]
    fn successful_drop() {
        use std::sync::Arc;

        // We use the strong count of an arc to check that the dropping actually happens
        let v: Arc<i32> = Arc::new(5);

        let mut this: MaxVec<Arc<i32>, 4> = MaxVec::new();
        this.push(v.clone());
        this.push(v.clone());

        assert_eq!(Arc::strong_count(&v), 3);

        drop(this);

        assert_eq!(Arc::strong_count(&v), 1);
    }

    #[test]
    fn slice_eq() {
        let mut this: MaxVec<i32, 4> = MaxVec::new();
        this.push(1);
        this.push(2);
        this.push(3);
        assert_eq!(this, [1, 2, 3]);
    }

    #[test]
    fn full_prefix() {
        let vec = vec![1_i32, 2, 3, 4, 5, 6, 7, 8];
        let this: MaxVec<i32, 4> = MaxVec::from_slice_prefix(&vec);

        assert_eq!(this, [1, 2, 3, 4]);
        assert_eq!(this.len(), this.capacity());
    }

    #[test]
    fn partial_prefix() {
        let vec = vec![1_i32, 2];
        let this: MaxVec<i32, 4> = MaxVec::from_slice_prefix(&vec);

        assert_eq!(this, [1, 2]);
        assert_eq!(this.len(), 2);
    }

    #[test]
    fn full_suffix() {
        let vec = vec![1_i32, 2, 3, 4, 5, 6];
        let this: MaxVec<i32, 4> = MaxVec::from_slice_suffix(&vec);

        assert_eq!(this, [3, 4, 5, 6]);
        assert_eq!(this.len(), this.capacity());
    }

    #[test]
    fn partial_suffix() {
        let vec = vec![1_i32, 2];
        let this: MaxVec<i32, 4> = MaxVec::from_slice_suffix(&vec);

        assert_eq!(this, [1, 2]);
        assert_eq!(this.len(), 2);
    }

    // `from_iter` that isn't the full length
    #[test]
    fn from_iter_partial() {
        let vec = vec![1_i32, 2];
        let this: MaxVec<i32, 4> = MaxVec::from_iter(vec);

        assert_eq!(this, [1, 2]);
    }

    // `from_iter` that's >= the full length
    #[test]
    fn from_iter_full() {
        let vec = vec![1_i32, 2, 3, 4, 5, 6];
        let this: MaxVec<i32, 4> = MaxVec::from_iter(vec);

        assert_eq!(this, [1, 2, 3, 4]);
    }

    #[test]
    fn from_iter_reversed_partial() {
        let vec = vec![1_i32, 2];
        let this: MaxVec<i32, 4> = MaxVec::from_iter_reversed(vec);

        assert_eq!(this, [2, 1]);
    }

    #[test]
    fn from_iter_reversed_full() {
        let vec = vec![1_i32, 2, 3, 4, 5, 6];
        let this: MaxVec<i32, 4> = MaxVec::from_iter_reversed(vec);

        assert_eq!(this, [4, 3, 2, 1]);
    }

    #[test]
    fn empty_iter() {
        let vec = vec![];
        let this: MaxVec<i32, 4> = MaxVec::from_iter(vec.clone());
        assert_eq!(this.iter().cloned().collect::<Vec<_>>(), vec);
    }

    #[test]
    fn midfull_iter() {
        let vec = vec![1, 2];
        let this: MaxVec<i32, 4> = MaxVec::from_iter(vec.clone());
        assert_eq!(this.iter().cloned().collect::<Vec<_>>(), vec);
    }

    #[test]
    fn full() {
        let vec = vec![1, 2, 2, 4];
        let this: MaxVec<i32, 4> = MaxVec::from_iter(vec.clone());
        assert_eq!(this.iter().cloned().collect::<Vec<_>>(), vec);
    }

    struct PanicIter<T> {
        iter: <Vec<T> as IntoIterator>::IntoIter,
    }

    impl<T> Iterator for PanicIter<T> {
        type Item = T;

        fn next(&mut self) -> Option<T> {
            match self.iter.next() {
                Some(it) => Some(it),
                None => panic!("out of items!"),
            }
        }
    }

    // Checks that a panicking iterator will still have previous items dropped
    #[test]
    fn from_iter_panics() {
        let arc = Arc::new(2_i32);
        let items = PanicIter {
            iter: vec![arc.clone(), arc.clone()].into_iter(),
        };

        let res = std::panic::catch_unwind(move || {
            let _: MaxVec<_, 4> = MaxVec::from_iter(items);
        });

        let err = res.unwrap_err();
        let err_msg = *err.downcast_ref::<&'static str>().unwrap();
        assert_eq!(err_msg, "out of items!");

        // Check that the values were dropped
        assert_eq!(Arc::strong_count(&arc), 1);
    }

    #[test]
    fn from_iter_reversed_panics() {
        let arc = Arc::new(2_i32);
        let items = PanicIter {
            iter: vec![arc.clone(), arc.clone()].into_iter(),
        };

        let res = std::panic::catch_unwind(move || {
            let _: MaxVec<_, 4> = MaxVec::from_iter_reversed(items);
        });

        let err = res.unwrap_err();
        let err_msg = *err.downcast_ref::<&'static str>().unwrap();
        assert_eq!(err_msg, "out of items!");

        // Check that the values were dropped
        assert_eq!(Arc::strong_count(&arc), 1);
    }
}
