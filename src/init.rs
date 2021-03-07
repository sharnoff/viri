//! Wrapper module for a few different initialization tools
//!
//! The primary tool for module initialization is the [`init`] macro, which allows blocks
//! initializing code to run at a time of your choosing - while also guaranteeing (as much as
//! possible) that they run exactly once. For more information on this, see the
//! [macros module documentation](crate::macros).
//!
//! Outside of that, the [`LazyInit`] type is also provided, which allows the value of a `static`
//! item to be specified exactly once, typically within an initializing block for a module.
//!
//! [`init`](crate::macros::init)

use std::cell::UnsafeCell;
use std::mem::MaybeUninit;
use std::ops::Deref;
use std::ptr;
use std::sync::atomic::{AtomicU8, Ordering};

// Marker values for the `is_init` field
const UNINIT: u8 = 0;
const INIT_IN_PROGRESS: u8 = 1;
const INIT: u8 = 2;

/// Values that can be initialized exactly once
///
/// A `LazyInit` is created with `LazyInit::new()` and initalized with the `initialize_with`
/// method. After initialization, access is provided with the implementation of [`Deref`]. Note
/// that attempting to dereference to a value that has not been initialized will result in a
/// panic.
///
/// Typical usage of this type is within `static`s, set by the [`init!`] macro.
pub struct LazyInit<T> {
    /// Marker for whether `val` has been set
    state: AtomicU8,
    val: UnsafeCell<MaybeUninit<T>>,
}

unsafe impl<T: Sync> Sync for LazyInit<T> {}

impl<T> LazyInit<T> {
    /// Creates a new, uninitalized `LazyInit`
    pub const fn new() -> Self {
        LazyInit {
            state: AtomicU8::new(UNINIT),
            val: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    /// Initializes the value, panicking if this has already been called
    ///
    /// Calling `initialize_with` is required before dereferencing the value; it will panic if the
    /// value has not been set.
    ///
    /// ## Panics
    ///
    /// This method will panic if it has already been called on this value - in any other thread.
    //
    // TODO-API: Generally, types impementing `Deref` don't provide methods, due to possible
    // ambiguity. There's unfortunately unavoidable ambiguity - whether we make this an associated
    // function *OR* a method - because `&lazy` can implicitly dereference, so this isn't as clear
    // cut as it might seem.
    //   Q: Do we change this to an associated function?
    pub fn initialize_with(&self, val: T) {
        match self.state.swap(INIT_IN_PROGRESS, Ordering::AcqRel) {
            UNINIT => (),
            INIT_IN_PROGRESS | INIT => panic!("attempted to double-initialize `LazyInit`"),
            _ => panic!("unexpected initialization marker"),
        }

        // SAFETY: We know that the previous value of `self.state` was `UNINIT` -- i.e. `self.val`
        // has not been initialized. If anything attempts to read `self.state` after we've
        // performed the swap, with an at-least-Acquire ordering, they'll read it as
        // `INIT_IN_PROGRESS` and cannot run this section.
        //
        // So exactly one thread can run this block, and only exactly once.
        unsafe {
            *self.val.get() = MaybeUninit::new(val);
        }

        self.state.store(INIT, Ordering::Release);
    }
}

impl<T> Deref for LazyInit<T> {
    type Target = T;

    fn deref(&self) -> &T {
        match self.state.load(Ordering::Release) {
            UNINIT | INIT_IN_PROGRESS => panic!("`LazyInit` is not fully initialized"),
            INIT => unsafe { (&*self.val.get()).assume_init_ref() },
            _ => panic!("unexpected initialization marker in `LazyInit`"),
        }
    }
}

// We should implement `Drop` so that the contents of `self.val` are dropped - but only if they've
// already been set
impl<T> Drop for LazyInit<T> {
    fn drop(&mut self) {
        if self.state.load(Ordering::Acquire) == INIT {
            // SAFETY: the value is initialized, so we're free to drop it
            unsafe { ptr::drop_in_place(self.val.get_mut().as_mut_ptr()) }
        }
    }
}
