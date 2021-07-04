//! Wrapper module for [`OwnedCell`] and related types
//
// TODO-CORRECTNESS (MEM): There's a few cases in here where we have interior mutability that
// doesn't boil down to an `UnsafeCell`. `Weak::clone`, for example, increments the count behind
// the pointer. So: do we need to include this in the `PhanomData`?
//
// TODO-API: It might be better to allow `try_borrow` to return an error if `is_valid` is false,
// instead of simply panicking. We'd have to make `BorrowError` internally use an enum for this to
// be the case.

use std::fmt::{self, Debug, Display, Formatter};
use std::marker::PhantomData;
use std::mem::{self, MaybeUninit};
use std::num::NonZeroUsize;
use std::ops::{Deref, DerefMut};
use std::ptr::{drop_in_place, NonNull};
use std::thread;

/// A custom pointer type similar to `Rc<RefCell<T>>`
///
/// This type provides two key properties, both crucial to implementing stable node references in
/// [`Ranged`]:
///
///  1. There is only ever a single owner of the reference, which corresponds to having mutable
///     access *and* being a strong pointer.
///  2. We support an operation to promote *all* weak pointers to keep the allocation alive without
///     any gaining mutation rights.
///
/// Both of these are ideal for implementing node references. In general, we want redirected nodes
/// to stay alive with other references to them, but without the second operation we'd have to do
/// some convoluted tracking to keep a single strong reference alive.
///
/// In addition, restricting mutable access to a single owner means that we can safely go from a
/// `&OwnedCell<T>` to `&T`, without hiding it behind a guard -- another win.
///
/// Weak pointers are represented with the [`Weak`] type.
///
/// ## Usage
///
/// Usage of this type should feel fairly familiar - kind of a cross between a `Box<T>` and an
/// `Rc<RefCell<T>>`.
///
/// New `OwnedCell`s are created with the [`new`] method. Creating weak references is done with the
/// [`weak`] method; producing a `&T` is done with the implementation of [`AsRef`]; and mutable
/// guards are acquired with the [`borrow_mut`] method.
///
/// The [`drop_and_promote_weaks`] method is provided to allow you to keep the value alive, even
/// after the owner has been dropped.
///
/// ## Quirks
///
/// This type comes with a couple quirks that it may help to be aware of. Because of the dynamics
/// around single ownership *and* allowing shared references that exist within this type, it's
/// possible that dropping the `OwnedCell` for a value may not immediately call its destructor.
/// The inner value itself will be kept alive until all existing borrows have been dropped. If
/// there aren't any, then it will be dropped immediately, but if some borrow on the node is stored
/// elsewhere, it won't.
///
/// If your usage of this type relies on destructors being run, it's worth checking that you don't
/// can't accidentally hold a borrow on the data when you want this destructor to be run.
///
/// Aside from a *delayed* destructor, this value should act normally.
///
/// [`Ranged`]: super::Ranged
/// [`new`]: Self::new
/// [`weak`]: Self::weak
/// [`borrow_mut`]: Self::borrow_mut
pub struct OwnedCell<T> {
    ptr: NonNull<Inner<T>>,
    marker: PhantomData<T>,
}

/// The weak counterpart to [`OwnedCell`]
///
/// This type provides immutable access to the value behind an `OwnedCell`, and only through guards
/// created by the [`borrow`] method. If the owner of the value is dropped, any `Weak`s pointing to
/// it will (usually) also lose access. As such, you can think of this type as *similar* to an
/// `rc::Weak<RefCell<T>>`, but without mutable access.
///
/// Pointers of this type cannot be promoted to a proper [`OwnedCell`]; they must always go through
/// the [`borrow`] method to obtain a read guard. This is because [`OwnedCell`] is guaranteed to be
/// the unique owner for its value.
///
/// ## Usage
///
/// This type essentially provides two things to use. The [`borrow`] method, to produce a read
/// guard, and the implementation of [`Clone`]. Both should be pretty simple. Whether a borrow will
/// succeed can also be checked by two methods: [`is_valid`] and [`try_borrow`].
///
/// Attempting to access without panicking is done in two steps:
///
// @def "ranged::rc::Weak main doctests" v0
/// ```
/// // A sample function that attempts to extract a borrow on the inner value
/// fn try_get(weak: &Weak<i32>) -> Option<Borrow<'_, i32>> {
///     // First, check if the inner value has been dropped:
///     if !weak.is_valid() {
///         return None;
///     }
///
///     // If the inner value is still alive, we still might fail if it's
///     // currently mutably borrowed:
///     match weak.try_borrow() {
///         Ok(b) => Some(b),
///         Err(e) => {
///             println!("failed to borrow: {}", e);
///             None
///         }
///     }
/// }
/// ```
///
/// [`borrow`]: Self::borrow
pub struct Weak<T> {
    ptr: NonNull<Inner<T>>,
    marker: PhantomData<T>,
}

// The value pointed to by an `OwnedCell` or `Weak`
struct Inner<T> {
    val: MaybeUninit<T>,
    state: State,
    weak_count: usize,
    borrow: Option<Borrowed>,
}

// The state of the inner value. Used to determine what weak pointers should do: when borrows are
// dropped, when attempting to borrow, and when the weak pointers themselves are dropped
#[derive(Copy, Clone, PartialEq)]
enum State {
    // The strong pointer (OwnedCell) to the value is still alive.
    HasStrong,
    // The strong pointer has been dropped, but some number of borrows from weak pointers are
    // keeping the allocation alive. `Inner.borrow` is always `Some(Immutable { .. })` if this is
    // true.
    ShouldDrop,
    // The weak references have been promoted to keep the value alive, even though there isn't a
    // strong pointer any more.
    WeaksAreStrong,
    // The inner value `Inner.val` has been dropped.
    Dropped,
}

#[derive(Copy, Clone)]
enum Borrowed {
    Immutable { count: NonZeroUsize },
    Mutable,
}

impl<T> OwnedCell<T> {
    /// Constructs a new `OwnedCell` from the provided value
    pub fn new(val: T) -> Self {
        let boxed = Box::new(Inner {
            val: MaybeUninit::new(val),
            state: State::HasStrong,
            weak_count: 0,
            borrow: None,
        });

        OwnedCell {
            // SAFETY: The pointer provided by a `Box` is always non-null
            ptr: unsafe { NonNull::new_unchecked(Box::into_raw(boxed)) },
            marker: PhantomData,
        }
    }

    /// Produces a pointer-formattable value that can be used to debug addresses
    pub fn fmt_ptr(&self) -> impl fmt::Pointer {
        Inner::val_ptr(self.ptr.as_ptr()) as *const T
    }

    /// Creates a new weak, immutable pointer to the value behind the `OwnedCell`
    ///
    /// The [`Weak`] pointer will have immutable access to the value so long as the `OwnedCell`
    /// stays alive.
    pub fn weak(&self) -> Weak<T> {
        let ptr = self.ptr.as_ptr();

        // SAFETY: We know that we have unique mutable access to the field because references
        // to `weak_count` are only ever created temporarily, and we have single-threaded
        // accesshere.
        unsafe { *Inner::weak_count_ptr(ptr) += 1 };

        Weak {
            ptr: self.ptr,
            marker: PhantomData,
        }
    }

    /// Creates a mutable borrow to the inner value
    ///
    /// ## Panics
    ///
    /// This method panics if there are currently any immutable borrows on the inner value as well.
    ///
    /// ## Examples
    ///
    // @def "ranged::rc::OwnedCell::borrow_mut doctests" v0
    /// ```
    /// let mut x = OwnedCell::new(4_i32);
    /// let weak = x.weak();
    ///
    /// // Borrowing normally works as it should:
    /// let mut borrow = x.borrow_mut();
    /// *borrow = 3;
    ///
    /// // Attempting to borrow from a weak reference will fail while we hold
    /// // a mutable reference:
    /// assert!(weak.try_borrow().is_err());
    ///
    /// // But it's ok once the mutable borrow is gone:
    /// drop(borrow);
    /// assert_eq!(*weak.borrow(), 3);
    /// ```
    #[track_caller]
    pub fn borrow_mut<'r>(&'r mut self) -> BorrowMut<'r, T> {
        let ptr = self.ptr.as_ptr();

        // SAFETY: We know the pointer itself is valid, because `self` still exists and the
        // offset given by `Inner::borrow_ptr` points to the field we want.
        //
        // We're guaranteed to have unique mutable access here because the `borrow` field is only
        // ever referenced temporarily -- we could only possibly have aliasing as a result of
        // multiple threads accessing pointers to the same allocation, which is prevented by the
        // lack of an implementation of `Send` and `Sync` for these types.
        let b = unsafe { &mut *Inner::borrow_ptr(ptr) };

        match b {
            None => *b = Some(Borrowed::Mutable),
            Some(Borrowed::Immutable { .. }) => panic!("already immutably borrowed"),
            Some(Borrowed::Mutable) => {
                panic!("internal invariant violated: double mutable borrow. this is a bug");
            }
        }

        BorrowMut {
            base_ptr: self.ptr,
            marker: PhantomData,
        }
    }

    /// Sets the value behind `self`, returning what was previously there
    ///
    /// ## Panics
    ///
    /// This method panics if there are any existing immutable borrows on the inner value.
    ///
    /// ## Examples
    ///
    // @def "ranged::rc::OwnedCell::replace.0 doctests" v0
    /// ```
    /// let mut x: OwnedCell<Option<i32>> = OwnedCell::new(None);
    /// assert_eq!(x.replace(Some(5)), None);
    /// ```
    ///
    // @def "ranged::rc::OwnedCell::replace.1 doctests" v0
    /// ```should_panic
    /// let mut y: OwnedCell<Option<i32>> = OwnedCell::new(None);
    ///
    /// let weak = y.weak();
    /// // Holding a borrow will cause `replace` to panic.
    /// let borrow = weak.borrow();
    /// assert_eq!(*borrow, None);
    ///
    /// // Panics!
    /// y.replace(Some(5));
    /// ```
    #[track_caller]
    pub fn replace(&mut self, val: T) -> T {
        mem::replace(&mut *self.borrow_mut(), val)
    }

    /// Drops the `OwnedCell` and keeps the inner value alive until all weak references have been
    /// dropped
    ///
    /// ## Examples
    ///
    // @def "ranged::rc::OwnedCell::drop_and_promote_weaks doctests" v0
    /// ```
    /// let x = OwnedCell::new(5);
    /// let y = x.weak();
    /// x.drop_and_promote_weaks();
    ///
    /// // After dropping, the weak pointer is still good to use!
    /// assert!(y.is_valid());
    /// assert_eq!(*y.borrow(), 5);
    ///
    /// // And any clones are good to use as well!
    /// let z = y.clone();
    /// assert_eq!(*z.borrow(), 5);
    /// ```
    pub fn drop_and_promote_weaks(self) {
        // This function is pretty similar to the implementation of `Drop` for `OwnedCell`. It may
        // be worth looking there as well.
        //
        // The general safety note at the top of that function applies here as well.

        let ptr = self.ptr.as_ptr();

        // The only component of `self` that we actually need is the pointer, so we can just
        // `forget()` it immediately:
        mem::forget(self);

        // SAFETY: Because we were handed `self`, we know that the pointer is valid. Any pointer to
        // `state` is temporary, so it's safe to mutate it in a single-threaded context.
        unsafe { *Inner::state_ptr(ptr) = State::WeaksAreStrong };

        // If there are any weak references, we're essentially done here. Otherwise, this is the
        // last reference to the value, so we should deallocate.
        //
        // SAFETY: Another value that's only accessed temporarily. `ptr` is still valid, because
        // `self` was given to us.
        if unsafe { *Inner::weak_count_ptr(ptr) == 0 } {
            // As described in `OwnedCell::drop`, it's easiest to just convert the pointer to a
            // `Box` to deallocate.
            //
            // SAFETY: A weak count of zero means there can't be any more pointers to the
            // allocation. We won't leave anything dangling.
            drop(unsafe { <Box<Inner<T>>>::from_raw(ptr) });
        }
    }
}

impl<T> AsRef<T> for OwnedCell<T> {
    fn as_ref(&self) -> &T {
        // SAFETY: The pointer is guaranteed to be valid by virtue of the existence of this type;
        // it cannot have been deallocated yet. Also, because we have a strong pointer, we know
        // that the value hasn't been dropped yet.
        unsafe { &*(Inner::val_ptr(self.ptr.as_ptr()) as *const T) }
    }
}

impl<T> Drop for OwnedCell<T> {
    fn drop(&mut self) {
        // General safety note: Because this type is still alive, we know that `ptr` is valid. For
        // every field except `val`, we only ever construct temporary references, so we can safely
        // produce those references as either mutable *or* immutable, without worrying about
        // whatever else might happen.
        //
        // Note: "temporary" in this context means that the references aren't held when any other
        // function that may attempt to construct such a reference is called. This always means
        // that references aren't held across function calls, but it ALSO means that we drop
        // references before making certain calls as well.
        let ptr = self.ptr.as_ptr();

        // We'll store a handle on the state for now, so that we can access it later. We need to be
        // careful to drop this reference before deallocating, if we end up doing that.
        //
        // SAFETY: See above note.
        let state = unsafe { &mut *Inner::state_ptr(ptr) };

        // SAFETY: Like `state`, references are only constructed temporarily.
        let borrow = unsafe { *Inner::borrow_ptr(ptr) };

        match borrow {
            Some(Borrowed::Immutable { .. }) => {
                // If there are current immutable borrows, we WANT to drop the value, but doing so
                // would invalidate those active references.
                //
                // So instead, we mark that - once there aren't borrows left - it *should* be
                // dropped.
                //
                // SAFETY: References are only ever constructed temporarily; we're good here.
                *state = State::ShouldDrop;

                // And then we're done here - we'll have to let the destructors for existing
                // borrows run.
            }
            None | Some(Borrowed::Mutable) => {
                // Above, we match on `Some(Borrowed::Mutable)`. This case should never occur in
                // practice, but it *is* possible -- even in safe rust. For example:
                //
                //   let x = OwnedCell::new("foobar");
                //   let b = x.borrow_mut();
                //   mem::forget(b);
                //
                //   drop(x); // <- dropped while we think it's borrowed
                //
                // In this case, it's actually unsound for the borrow returned from `borrow_mut` to
                // still be alive when the destructor from `x` is called. This is because
                // `borrow_mut` mutably borrows `x` for its entire duration.
                //
                // So we can *still* drop the value (and possibly deallocate it), assuming that
                // usage of this type was sound. If the usage wasn't sound, then proceeding to
                // deallocate this would be more likely to produce some other kind of behavior that
                // we can detect.
                //
                // Just to be nice, though: we'll only do something silently as a last resort. If
                // the thread isn't already panicking, we'll start that now in order to send a
                // message that something unexpected happened. We *really* want to avoid
                // double-panics, because they tend to make the runtime very unhappy.
                if let Some(Borrowed::Mutable) = borrow {
                    if !thread::panicking() {
                        panic!("dropped `OwnedCell` while mutably borrowed")
                    }
                }

                // Drop the value itself:
                //
                // We actually need to be careful here: it's possible for the value to contain a
                // cycle, having a weak reference pointing back to this allocation. As such, we
                // can't hold any mutable references across calling the destructor.
                //
                // We also need to indicate *before* dropping the value that it's been dropped, in
                // order to prevent weak references accessing it *during its own destructor*.
                *state = State::Dropped;
                drop(state);

                // SAFETY: At this point, we know we have unique mutable access to the value --
                // there aren't any immutable references, and there can't (soundly) be any other
                // mutable references, and so we're free to do as we please. If calling the
                // destructor happens to result in the destructor for a `Weak` reference to this
                // allocation being dropped, we know it won't access `state` because we've already
                // set the flag to indicate it's been dropped.
                unsafe { drop_in_place(Inner::val_ptr(ptr)) };

                // And, if there's no other references, deallocate:
                //
                // SAFETY: Same as above; only temporary references.
                if unsafe { *Inner::weak_count_ptr(ptr) == 0 } {
                    // The easiest way for us to deallocate (without using the various
                    // currently-unstable APIs that *are* available) is to just convert back into a
                    // Box. We actually originally use a box for all `OwnedCell`s in the
                    // implementation of `OwnedCell::new`.
                    //
                    // SAFETY: A weak count of zero means there cannot be any other weak references
                    // (unless a destructor has been called twice, which is unsound). So we have
                    // unique access to the contents behind ptr.
                    drop(unsafe { <Box<Inner<T>>>::from_raw(ptr) });
                }
            }
        }
    }
}

impl<T: Clone> Clone for OwnedCell<T> {
    fn clone(&self) -> Self {
        OwnedCell::new(self.as_ref().clone())
    }
}

impl<T: Debug> Debug for OwnedCell<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.as_ref().fmt(f)
    }
}

impl<T: Display> Display for OwnedCell<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.as_ref().fmt(f)
    }
}

impl<T> Weak<T> {
    /// Creates a new, always-invalid `Weak` pointer
    ///
    /// Note that this method *does* create a new allocation for the pointer. This may be changed
    /// in the future, but - for now - do not assume this method has no cost.
    ///
    /// ## Examples
    ///
    // @def "ranged::rc::Weak::new doctests" v0
    /// ```
    /// // The immediate `Weak` is, of course, invalid.
    /// let w: Weak<i32> = Weak::new();
    /// assert!(!w.is_valid());
    ///
    /// // And while we *can* clone it, those pointers will also be invalid.
    /// assert!(!w.clone().is_valid());
    /// ```
    ///
    /// This functionality can be particularly useful when you want to encode the fallibility of an
    /// `Option<OwnedCell<T>>` into a single `Weak`. For example:
    /// ```
    /// fn extract_weak<T>(this: Option<OwnedCell<T>>) -> Weak<T> {
    ///     this.as_ref().map(OwnedCell::weak).unwrap_or_else(Weak::new)
    /// }
    /// ```
    pub fn new() -> Self {
        // Currently, we allocate. We essentially just set the state to pretend as if the strong
        // reference has already been dropped, which produces the behavior we want.
        let boxed = Box::new(Inner {
            val: <MaybeUninit<T>>::uninit(),
            state: State::Dropped,
            // A single weak count, for this reference
            weak_count: 1,
            borrow: None,
        });

        Weak {
            // SAFETY: The pointer provided by a `Box` is always non-null
            ptr: unsafe { NonNull::new_unchecked(Box::into_raw(boxed)) },
            marker: PhantomData,
        }
    }

    /// Produces a pointer-formattable value that can be used to debug addresses
    pub fn fmt_ptr(&self) -> impl fmt::Pointer {
        Inner::val_ptr(self.ptr.as_ptr()) as *const T
    }

    /// Returns whether the value behind the weak pointer can still be accessed
    ///
    /// In general, this method indicates whether the value behind the pointer has been dropped.
    /// That being said, there *are* certain cases where the this method may return `false`, even
    /// though the value is currently being accessed.
    ///
    /// Note that if this method returns true, borrowing may still fail if a mutable borrow is
    /// currently held. See also: [`try_borrow`].
    ///
    /// [`try_borrow`]: Self::try_borrow
    pub fn is_valid(&self) -> bool {
        let ptr = self.ptr.as_ptr();

        // The pointer is valid only if the value hasn't been dropped
        //
        // SAFETY: The `Inner` itself is only deallocated once all weak references are gone.
        // Because we're accessing through a weak reference, it must still be alive. Also, all
        // references to `Inner.state` are only constructed in a temporary fashion, so there's no
        // possibilities of aliased pointers.
        match unsafe { *Inner::state_ptr(ptr) } {
            State::HasStrong | State::WeaksAreStrong => true,
            State::ShouldDrop | State::Dropped => false,
        }
    }

    /// Borrows the data behind the `Weak`, panicking on failure
    ///
    /// This method actually has a copule interesting things about it. Normally, we'd expect that a
    /// `Weak` pointer completely loses access once the strong pointer (the [`OwnedCell`]) is
    /// dropped. But if we happen to have a borrow on the value, that borrow will continue to be
    /// valid until it has been dropped, even if we can no longer create another borrow from the
    /// same `Weak` pointer.
    ///
    /// For a (partially) fallible version of this method, see [`try_borrow`].
    ///
    /// ## Panics
    ///
    /// This method panics if the pointer is invalid (i.e. the value has been dropped), or if the
    ///
    /// ## Examples
    ///
    // @def "ranged::rc::Weak::borrow.0 doctests" v0
    /// ```
    /// let x = OwnedCell::new(3);
    /// let weak = x.weak();
    ///
    /// // We can make multiple borrows from the same weak reference, if we want:
    /// let borrows: Vec<_> = (0..10).map(|_| weak.borrow()).collect();
    ///
    /// for b in borrows {
    ///     assert_eq!(*b, 3);
    /// }
    ///
    /// # // Just another check: we can still mutably borrow afterwards
    /// # let mut x = x; x.borrow_mut();
    /// ```
    ///
    /// Attempting to borrow while a mutable one is held will result in a panic:
    ///
    // @def "ranged::rc::Weak::borrow.1 doctests" v0
    /// ```should_panic
    /// let mut x = OwnedCell::new(3);
    /// let weak = x.weak();
    ///
    /// let mut b = x.borrow_mut();
    /// *b = 5;
    ///
    /// // Panics!
    /// let _ = weak.borrow();
    /// ```
    ///
    /// And borrows are still valid after the `OwnedCell` is dropped, even though we can't create a new
    /// borrow:
    ///
    // @def "ranged::rc::Weak::borrow.2 doctests" v0
    /// ```
    /// let x = OwnedCell::new(3);
    ///
    /// let weak = x.weak();
    /// let borrow = weak.borrow();
    ///
    /// // Even though we drop the `OwnedCell` here, the borrow is still alive.
    /// drop(x);
    ///
    /// // So we can't create a new borrow...
    /// assert!(!weak.is_valid());
    /// // ... but the existing one still works!
    /// assert_eq!(*borrow, 3);
    /// ```
    ///
    /// [`try_borrow`]: Self::try_borrow
    #[track_caller]
    pub fn borrow<'r>(&'r self) -> Borrow<'r, T> {
        match self.try_borrow() {
            Ok(b) => b,
            Err(e) => panic!("{}", e),
        }
    }

    /// Attempts to borrow the data behind a valid `Weak`, returning an error if mutably borrowed
    ///
    /// For a version of this method that simply panics on failure, see [`borrow`].
    ///
    /// ## Panics
    ///
    /// This method panics if the `Weak` pointer is invalid (i.e. [`is_valid`] returns false).
    /// Refer to the type-level documentation for an example of how to attempt to borrow the value
    /// without the possibility of panicking.
    ///
    /// [`borrow`]: Self::borrow
    /// [`is_valid`]: Self::is_valid
    pub fn try_borrow<'r>(&'r self) -> Result<Borrow<'r, T>, BorrowError> {
        if !self.is_valid() {
            panic!("cannot borrow from invalid pointer");
        }

        // Because is_valid returned true, we know that the state is either `HasStrong` or
        // `WeaksAreStrong`. We can therefore just check the `borrow` field because we know that
        // `val` will be valid and able for us to take.
        let ptr = self.ptr.as_ptr();

        // SAFETY: We're safe to construct a mutable reference to `borrow` here because all
        // references to `borrow` exist only temporarily -- i.e. they exist within these functions,
        // and are always dropped before calling any external code.
        let borrow = unsafe { &mut *Inner::borrow_ptr(ptr) };
        match borrow {
            None => {
                // SAFETY: Trivailly safe; 1 != 0.
                let count = unsafe { NonZeroUsize::new_unchecked(1) };
                *borrow = Some(Borrowed::Immutable { count });
            }
            Some(Borrowed::Immutable { count }) => {
                // We use `checked_add` here because integer arithmetic will not panic in release
                // mode. We *really* don't want to end up with a zero here.
                let new_count = match count.get().checked_add(1) {
                    Some(c) => c,
                    None => panic!(
                        "integer overflow on borrow count: cannot add 1 to {}",
                        count.get()
                    ),
                };

                // SAFETY: Incrementing cannot produce a value of zero without overflow, and we've
                // already checked for that above.
                *count = unsafe { NonZeroUsize::new_unchecked(new_count) };
            }
            Some(Borrowed::Mutable) => return Err(BorrowError { _private: () }),
        }

        Ok(Borrow {
            base_ptr: self.ptr,
            marker: PhantomData,
        })
    }
}

impl<T> Clone for Weak<T> {
    fn clone(&self) -> Self {
        // Cloning a weak pointer is relatively simple; we just increment the weak count.
        //
        // SAFETY: By virtue of the original weak pointer being passed in, we know that the
        // backing allocation is still there -- it's still safe to read from (and write to) fields
        // of the `Inner`.
        unsafe { *Inner::weak_count_ptr(self.ptr.as_ptr()) += 1 };

        // We've incremented the weak count, so we're now free to construct a new pointer:
        Weak {
            ptr: self.ptr,
            marker: PhantomData,
        }
    }
}

impl<T> Drop for Weak<T> {
    fn drop(&mut self) {
        // When dropping a weak pointer, there's a couple things that could happen.
        //
        // If this is the last weak pointer, we may need to deallocate. It might *also* be the case
        // that the weak pointers were assigned shared ownership of the value, meaning that we'll
        // have to drop the value before deallocating as well.
        let ptr = self.ptr.as_ptr();

        let weak_count = unsafe { &mut *Inner::weak_count_ptr(ptr) };

        // We expect that `weak_count` is not zero. In debug builds, we'll handle this gracefully
        // and panic if possible. But in actuality, a value of zero can ONLY occur if the
        // destructor for a `Weak` was called twice; we can assume in an unsafe manner that this
        // will not occur.
        if *weak_count == 0 {
            #[cfg(debug_assertions)]
            if !thread::panicking() {
                panic!("dropped `Weak` with weak count of zero");
            } else {
                return;
            }

            #[cfg(not(debug_assertions))]
            // SAFETY: See reasons above.
            unsafe {
                std::hint::unreachable_unchecked()
            };
        }

        // If this isn't the last `Weak` pointer, decrement the weak count and exit - there isn't
        // anything more to do.
        //
        // If it *is* the last, then we continue to check for deallocation and dropping.
        *weak_count -= 1;
        if *weak_count != 0 {
            return;
        }
        drop(weak_count);

        let state = unsafe { *Inner::state_ptr(ptr) };

        // If this is the last pointer to the value *and* it hasn't been dropped yet, we should do
        // that now.
        if state == State::WeaksAreStrong {
            // SAFETY: todo
            unsafe { drop_in_place(Inner::val_ptr(ptr)) };
        }

        if state == State::WeaksAreStrong || state == State::Dropped {
            // The way we handle deallocation is to just convert the `*mut Inner` to a box and drop
            // that.
            //
            // SAFETY: Because there isn't a strong pointer, and this is the last weak pointer, we
            // know that nothing else can possibly access the value after we free it here. But we
            // also know that it hasn't been deallocated yet, because `self` WAS an existing weak
            // pointer to it.
            drop(unsafe { <Box<Inner<T>>>::from_raw(ptr) });
        }
    }
}

/// An immutable borrow, constructed by [`Weak::borrow`]
///
/// Immutable borrows can be cloned, in addition to mapped by the associated [`map`] function.
///
/// [`map`]: Self::map
pub struct Borrow<'r, T> {
    // The layout here is used similarly to `BorrowMut`; we're pretending that we actually have
    // some field `val: &'r T`. The primary difference here is that we don't allow constructing a
    // mutable reference to `val` through `base_ptr`, where `BorrowMut` does.
    base_ptr: NonNull<Inner<T>>,

    // So our marker actually needs to contain more than just `&'r T`. Because dropping this type
    // can ALSO drop the inner `T` under certain circumstances, we need to indicate this fact to
    // dropck by indicating that we logically own a `T`.
    marker: PhantomData<(&'r T, T)>,
}

/// A mutable borrow, constructed by [`OwnedCell::borrow_mut`]
///
/// Mutable borrows can be mapped via the associated [`map`] function, or downgraded to an
/// immutable borrow with [`downgrade`] to allow new immutable borrows to be made.
///
/// [`downgrade`]: Self::downgrade
/// [`map`]: Self::map
pub struct BorrowMut<'r, T> {
    // We use the fields in `base_ptr` and the marker alongside it to pretend like we actually
    // store a field `val: &'r mut T`. We need to store a pointer to the containing `Inner`
    // anyways, so it's more memory efficient to just store a single pointer and produce the other
    // one as needed.
    base_ptr: NonNull<Inner<T>>,
    marker: PhantomData<&'r mut T>,
}

impl<'r, T> Drop for Borrow<'r, T> {
    fn drop(&mut self) {
        // Dropping an immtuable borrow is sometimes tricky. In general, we're guaranteed that
        // `self.val` is a valid reference, and `self.base_ptr` hasn't been deallocated -- so
        // `base_ptr.state` is anything *except* `State::Dropped`.
        //
        // But other than that, there's a couple things we need to do. We need to decrement the
        // number of immutable borrows (setting `base_ptr.borrow = None` if that would be zero),
        // and if the state is `ShouldDrop`, then we also need to actually drop the value if this
        // was the last borrow.

        let ptr = self.base_ptr.as_ptr();

        // SAFETY: we know the `Inner` hasn't been deallocated because the lifetime attached to
        // this `Borrow` ensures that there's at least one `Weak` pointer alive. Constructing a
        // mutable reference is safe here because -- like all other references to `Inner.borrow` --
        // it's only used temporarily.
        let borrow = unsafe { &mut *Inner::borrow_ptr(ptr) };

        let new_count = match *borrow {
            Some(Borrowed::Immutable { count }) => count.get() - 1,

            // When the destructor is called, it would actually be *unsound* for the value of
            // `borrow` to be anything other than `Immutable { .. }`, because we would have had to
            // have a destructor run twice.
            //
            // If we're running in a debug build, we'll do the nice thing and panic (assuming we
            // aren't already) if this isn't the case -- just so that we can catch an error in
            // tests if it's there. But this really shouldn't happen AT ALL, so we'll use
            // `unreachable()` if we aren't in a debug build.
            #[cfg(debug_assertions)]
            None => {
                if !thread::panicking() {
                    panic!("dropped `Borrow` while not borrowed");
                }

                return;
            }
            #[cfg(debug_assertions)]
            Some(Borrowed::Mutable) => {
                if !thread::panicking() {
                    panic!("dropped `Borrow` while mutably borrowed");
                }

                return;
            }
            #[cfg(not(debug_assertions))]
            None | Some(Borrowed::Mutable) => unsafe { std::hint::unreachable_unchecked() },
        };

        let no_borrows;
        *borrow = match NonZeroUsize::new(new_count) {
            Some(count) => {
                no_borrows = false;
                Some(Borrowed::Immutable { count })
            }
            None => {
                no_borrows = true;
                None
            }
        };
        drop(borrow);

        // If we removed the last immutable borrow, we need to check if it's our responsibility to
        // drop the value. This will only be the case if `state = ShouldDrop`.
        //
        // SAFETY: Again, references to the state are temporary, and the `Inner` behind `ptr` is
        // still allocated. We're all good.
        let state = unsafe { &mut *Inner::state_ptr(ptr) };

        if no_borrows && *state == State::ShouldDrop {
            // Dropping the value is pretty simple. We mark it as dropped beforehand, even though
            // weak pointers will still fail to produce new borrows because state = ShoulDrop,
            // because we shouldn't hold on to our reference to `state` while code that *could*
            // acquire a reference to `state` is run.
            *state = State::Dropped;
            drop(state);

            // SAFETY: We know that the value hasn't already been dropped, because `state` didn't
            // equal `Dropped`, and we now have no aliasing that could conflict with this.
            unsafe { drop_in_place(Inner::val_ptr(ptr)) };
        }
    }
}

impl<'r, T> Drop for BorrowMut<'r, T> {
    fn drop(&mut self) {
        // Because we have access to a mutable borrow, we know that the strong reference must
        // exist. We don't need to worry about any dropping/deallocation logic because the value is
        // still in use.
        //
        // SAFETY: the `OwnedCell` exists for this pointer; it's perfectly valid. The temporary
        // reference isn't aliased, because references to `borrow` are never held.
        unsafe { *Inner::borrow_ptr(self.base_ptr.as_ptr()) = None };
    }
}

impl<'r, T> Deref for Borrow<'r, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // SAFETY: `base_ptr.val` is always valid at least until the destructor for this type has
        // been called, which we know because:
        //  (a) the attached lifetime
        unsafe { &*(Inner::val_ptr(self.base_ptr.as_ptr()) as *const T) }
    }
}

impl<'r, T> Deref for BorrowMut<'r, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // SAFETY: `base_ptr.val` is always valid at least until the destructor for this type has
        // been called, which we know because of the attached lifetime that prevents the
        // `OwnedCell` from being dropped while this value is still alive.
        unsafe { &*(Inner::val_ptr(self.base_ptr.as_ptr()) as *const T) }
    }
}

impl<'r, T> DerefMut for BorrowMut<'r, T> {
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: Constructing a reference here is safe for the same reasons as in the
        // implementation of `Deref` for this type, but we know that we can construct a *mutable*
        // reference because:
        //  (a) only the single `OwnedCell` can produce `BorrowMut`s for the value;
        //  (b) the `BorrowMut` mutably borrows the `OwnedCell`, so there can only be one
        //      `BorrowMut` for a single value, AND the value hasn't been dropped; and
        //  (c) dynamically tracking borrows via `Inner.borrow` ensures that (1) there weren't any
        //      immutable borrows already, and (2) no new ones can be formed.
        unsafe { &mut *(Inner::val_ptr(self.base_ptr.as_ptr()) as *mut T) }
    }
}

/// An error resulting from calling [`Weak::try_borrow`] when the value is already mutably borrowed
pub struct BorrowError {
    _private: (),
}

impl Debug for BorrowError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("BorrowError").finish()
    }
}

impl Display for BorrowError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("already mutably borrowed")
    }
}

macro_rules! inner_ptr {
    ($method:ident: $field:ident as $ty:ty) => {
        pub fn $method(ptr: *mut Inner<T>) -> *mut $ty {
            let template: Inner<T> = Inner {
                val: MaybeUninit::uninit(),
                state: State::Dropped,
                weak_count: 0,
                borrow: None,
            };

            // Produce the offset (in bytes) of the field within the proper type:
            let template_ptr = &template as *const Inner<T> as *const u8;
            let offset_ptr = &template.$field as *const $ty as *const u8;
            let byte_offset = offset_ptr as usize - template_ptr as usize;

            // Offset `ptr` by the required amount:
            let ptr_as_usize = ptr as *mut u8 as usize;
            (ptr_as_usize + byte_offset) as *mut $ty
        }
    };
}

impl<T> Inner<T> {
    inner_ptr!(val_ptr: val as MaybeUninit<T>);
    inner_ptr!(state_ptr: state as State);
    inner_ptr!(weak_count_ptr: weak_count as usize);
    inner_ptr!(borrow_ptr: borrow as Option<Borrowed>);
}

// Tests replicated from the documentation above
#[cfg(test)]
mod doctests {
    use super::*;

    // @req "ranged::rc::OwnedCell::borrow_mut doctests" v0
    #[test]
    fn ownedcell_borrow_mut() {
        let mut x = OwnedCell::new(4_i32);
        let weak = x.weak();

        let mut borrow = x.borrow_mut();
        *borrow = 3;

        assert!(weak.try_borrow().is_err());

        drop(borrow);
        assert_eq!(*weak.borrow(), 3);
    }

    // @req "ranged::rc::OwnedCell::replace.0 doctests" v0
    #[test]
    fn ownedcell_replace_0() {
        let mut x: OwnedCell<Option<i32>> = OwnedCell::new(None);
        assert_eq!(x.replace(Some(5)), None);
    }

    // @req "ranged::rc::OwnedCell::replace.1 doctests" v0
    #[test]
    #[should_panic]
    fn ownedcell_replace_1() {
        let mut y: OwnedCell<Option<i32>> = OwnedCell::new(None);

        let weak = y.weak();
        let borrow = weak.borrow();
        assert_eq!(*borrow, None);

        y.replace(Some(5));
    }

    // @req "ranged::rc::OwnedCell::drop_and_promote_weaks doctests" v0
    #[test]
    fn ownedcell_drop_and_promote_weaks() {
        let x = OwnedCell::new(5);
        let y = x.weak();
        x.drop_and_promote_weaks();

        assert!(y.is_valid());
        assert_eq!(*y.borrow(), 5);

        let z = y.clone();
        assert_eq!(*z.borrow(), 5);
    }

    // @req "ranged::rc::Weak main doctests" v0
    #[test]
    fn weak_main() {
        fn try_get(weak: &Weak<i32>) -> Option<Borrow<'_, i32>> {
            if !weak.is_valid() {
                return None;
            }

            match weak.try_borrow() {
                Ok(b) => Some(b),
                Err(e) => {
                    println!("failed to borrow: {}", e);
                    None
                }
            }
        }

        // NOT INCLUDED ABOVE:
        let x = OwnedCell::new(3);
        let w = x.weak();
        assert!(try_get(&w).is_some());

        drop(x);
        assert!(try_get(&w).is_none());
    }

    // @req "ranged::rc::Weak::new doctests" v0
    #[test]
    fn weak_new() {
        let w: Weak<i32> = Weak::new();
        assert!(!w.is_valid());
        assert!(!w.clone().is_valid());
    }

    // @req "ranged::rc::Weak::borrow.0 doctests" v0
    #[test]
    fn weak_borrow_0() {
        let x = OwnedCell::new(3);
        let weak = x.weak();

        // We can make multiple borrows from the same weak reference, if we want:
        let borrows: Vec<_> = (0..10).map(|_| weak.borrow()).collect();

        for b in borrows {
            assert_eq!(*b, 3);
        }

        let mut x = x;
        x.borrow_mut();
    }

    // @req "ranged::rc::Weak::borrow.1 doctests" v0
    #[test]
    #[should_panic]
    fn weak_borrow_1() {
        let mut x = OwnedCell::new(3);
        let weak = x.weak();

        let mut b = x.borrow_mut();
        *b = 5;

        let _ = weak.borrow();
    }

    // @req "ranged::rc::Weak::borrow.2 doctests" v0
    #[test]
    fn weak_borrow_2() {
        let x = OwnedCell::new(3);

        let weak = x.weak();
        let borrow = weak.borrow();

        drop(x);

        assert!(!weak.is_valid());
        assert_eq!(*borrow, 3);
    }
}
