//! Wrapper module for [`OwnedCell`] and related types
//
// TODO-CORRECTNESS (MEM): There's a few cases in here where we have interior mutability that
// doesn't boil down to an `UnsafeCell`. `Weak::clone`, for example, increments the count behind
// the pointer. So: do we need to include this in the `PhantomData`?
//
// TODO-API: It might be better to allow `try_borrow` to return an error if `is_valid` is false,
// instead of simply panicking. We'd have to make `BorrowError` internally use an enum for this to
// be the case.

use std::fmt::{self, Debug, Display, Formatter};
use std::marker::PhantomData;
use std::mem::{self, ManuallyDrop, MaybeUninit};
use std::num::NonZeroUsize;
use std::ops::{Deref, DerefMut};
use std::ptr::{drop_in_place, null, NonNull};
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
/// [`drop_and_promote_weaks`]: Self::drop_and_promote_weaks
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
/// [`is_valid`]: Self::is_valid
/// [`try_borrow`]: Self::try_borrow
pub struct Weak<T> {
    // We use a trick from the standard library here.
    //
    // For any `Weak` not created with the `new` method, this pointer will correctly be non-null
    // and point to a valid `Inner<T>`.
    //
    // But when we create something with the `new` method, it can't be a null pointer. So we set
    // the pointer value to `usize::MAX` instead. Whether the pointer is set to such a value is
    // checked with the `is_dangling` method. Any method that wants access to `ptr` needs to check
    // that it isn't dangling first.
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
        let borrow_ptr = Inner::borrow_ptr(ptr);
        let b = unsafe { &mut *borrow_ptr };

        match b {
            None => *b = Some(Borrowed::Mutable),
            Some(Borrowed::Immutable { .. }) => panic!("already immutably borrowed"),
            Some(Borrowed::Mutable) => {
                panic!("internal invariant violated: double mutable borrow. this is a bug");
            }
        }

        BorrowMut {
            borrow_ptr,
            // SAFETY: The only way this fails is if the offset from `Inner::val_ptr` wraps around
            // to produce a value of zero. This won't happen; the allocated `Inner` needs to
            // already exist in memory in such a way that we can actually refer to each field.
            value: unsafe { NonNull::new_unchecked(Inner::val_ptr(ptr) as *mut T) },
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

// @req "uses #[may_dangle]" v0
unsafe impl<#[may_dangle] T> Drop for OwnedCell<T> {
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
                unsafe { drop_in_place(Inner::val_ptr(ptr) as *mut T) };

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
    /// This method does not allocate anything for the pointer. It can be assumed to have
    /// effectively no cost.
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
        // Doing what we described in the comment above `Weak.ptr`. We're creating a dangling
        // pointer that can't possibly exist as a valid allocation.
        let ptr = NonNull::new(usize::MAX as *mut Inner<T>).expect("usize::MAX should be non-zero");

        Weak {
            ptr,
            marker: PhantomData,
        }
    }

    /// (*Internal*) Returns whether the `Weak` is dangling, equivalent to whether it was created
    /// by [`new`]
    ///
    /// [`new`]: Self::new
    fn is_dangling(&self) -> bool {
        self.ptr.as_ptr() as usize == usize::MAX
    }

    /// Produces a pointer-formattable value that can be used to debug addresses
    pub fn fmt_ptr(&self) -> impl fmt::Pointer {
        // We'll do a little trickery here. It's better to display dangling pointers as null
        // instead of `usize::MAX`, so we'll check for that independently. (Also because any offset
        // from `self.ptr` via `Inner::val_ptr` might overflow...)
        if self.is_dangling() {
            null()
        } else {
            Inner::val_ptr(self.ptr.as_ptr()) as *const T
        }
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
        if self.is_dangling() {
            return false;
        }

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
        let borrow_ptr = Inner::borrow_ptr(ptr);
        let borrow = unsafe { &mut *borrow_ptr };
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

        // SAFETY: We now know that (a) `ptr.val` is not dropped, and (b) the current value of
        // `ptr.borrow` means that we've secured an immtuable borrow for ourselves at least until
        // we drop.
        let value = unsafe { &*(Inner::val_ptr(ptr) as *const T) };

        Ok(Borrow {
            // SAFETY: `ptr` came from a `NonNull`; it is already guaranteed to be non-null.
            base_ptr: self.ptr.cast(),
            do_drop: DropFn::Normal,
            borrow_ptr,
            value,
        })
    }

    /// Returns true if `self` was created by a call to `owned.weak()`, i.e. if they point to the
    /// same allocation
    ///
    /// In practice, this method is primarily used for debug assertions.
    ///
    /// ## Examples
    ///
    // @def "ranged::rc::Weak::is_from doctests" v0
    /// ```
    /// // Even though these values are the same, their allocations
    /// // are different. That's what we're detecting here.
    /// let x = OwnedCell::new(3_i32);
    /// let y = OwnedCell::new(3_i32);
    ///
    /// let w = x.weak();
    ///
    /// assert!(w.is_from(&x));
    /// assert!(!w.is_from(&y));
    ///
    /// // Anything created with `Weak::new` will return false
    /// // for any `OwnedCell`.
    /// let z = Weak::new();
    /// assert!(!z.is_from(&x));
    /// ```
    pub fn is_from(&self, owned: &OwnedCell<T>) -> bool {
        // We can just directly compare the pointers. We don't need to worry about whether this
        // pointer is dangling, because it'll still be ok to compare the value of the *pointers*.
        //
        // The implementation of equality for `NonNull` compares pointer equality.
        self.ptr == owned.ptr
    }
}

impl<T> Clone for Weak<T> {
    fn clone(&self) -> Self {
        if !self.is_dangling() {
            // Cloning a weak pointer is relatively simple; we just increment the weak count.
            //
            // SAFETY: By virtue of the original weak pointer being passed in, we know that the
            // backing allocation is still there -- it's still safe to read from (and write to) fields
            // of the `Inner`.
            unsafe { *Inner::weak_count_ptr(self.ptr.as_ptr()) += 1 };
        }

        // We've incremented the weak count, so we're now free to construct a new pointer:
        Weak {
            ptr: self.ptr,
            marker: PhantomData,
        }
    }
}

// @req "uses #[may_dangle]" v0
unsafe impl<#[may_dangle] T> Drop for Weak<T> {
    fn drop(&mut self) {
        // When dropping a weak pointer, there's a couple things that could happen.
        //
        // If this is the last weak pointer, we may need to deallocate. It might *also* be the case
        // that the weak pointers were assigned shared ownership of the value, meaning that we'll
        // have to drop the value before deallocating as well.
        //
        // But also... if this weak pointer was never allocated in the first place, we should just
        // return.
        if self.is_dangling() {
            return;
        }

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
/// Immutable borrows can be cloned with the associated [`clone`] function, in addition to mapped
/// by the associated [`map`] function.
///
/// [`clone`]: Self::clone
/// [`map`]: Self::map
//
// There's a couple things to know about this type. Normally, anything that can run the destructor
// for some type `T` needs to indicate as such - either by including a value that indicates it, or
// by using a `PhantomData`. But this type can be mapped to other types in a way that means we
// can't always indicate that dropping a `Borrow` can, in fact, drop a type.
//
// But in spite of this, let me make the argument that this type is still sound.
//
// Essentially, the only thing that can go wrong when we fail to include the proper PhantomData
// *for dropck* (ignoring other applications) is that we can produce a use-after-free or similar
// behavior (i.e. accessing a value after it's been dropped). In fact, this sort of behavior is
// exactly what dropck was designed to check. (See RFC #0769)
//
// ## Part 1: Mutually-referential
//
// Normally, the way this occurs is if two values have the same lifetime, and we assign one of them
// to reference the other, with a destructor that uses that borrow. The faulty reasoning here on
// the compiler's side usually takes the form of "this lifetime is expected to be at least as long
// as the other, which it is", when in fact *one* of the values must be dropped first, and so the
// lifetime must be strictly longer.
//
// So the idea here would be: If we can set the value behind two `Borrow`s in a way that references
// each other such that - when they both go out of scope - they run the destructor for each value
// and one uses dropped data. And so we could try this:
//
//    #[derive(Default)]
//    struct Contrived<'a> {
//        dropped: bool,
//        other: Cell<Option<&'a Contrived<'a>>>,
//    }
//
//    // The point here is that `Contrived` uses the `other` field in its destructor, which if we
//    // were trying to find a problem, we'd hope it was allowed to sucessfully do.
//    impl<'a> Drop for Contrived<'a> {
//        fn drop(&mut self) {
//            if let Some(other) = self.other.get() {
//                assert!(!other.dropped);
//            }
//
//            self.dropped = true;
//        }
//    }
//
//    // We create two values
//    let a_owned = OwnedCell::new(Contrived::default());
//    let b_owned = OwnedCell::new(Contrived::default());
//
//    // And extract references to them, with borrows:
//    let a_weak = a_owned.weak();
//    let a_borrow = a_weak.borrow();
//
//    let b_weak = b_owned.weak();
//    let b_borrow = b_weak.borrow();
//
//    // The borrows keep the value alive:
//    drop((a_owned, b_owned));
//
//    // And then we set the values to reference the other:
//    a_borrow.other.set(Some(&*b_borrow));
//    //                      ^^^^^^^^^^ b_borrow does not live long enough
//    b_borrow.other.set(Some(&*a_borrow));
//    //                      ^^^^^^^^^^ a_borrow does not live long enough
//
//    // When `a_borrow` and `b_borrow` go out of scope, the destructors for the inner `Contrived`
//    // will run, so one of them must fail.
//
// This example *would* wonderfully showcase that this type is unsound, except it doesn't compile.
// The reason it doesn't compile is because -- fundamentally -- both borrows are tied to their weak
// pointers, and the weak pointers *do* tell dropck that they own a `T` and will call its
// destructor. So even though the borrows themselves don't carry the necessary information,
// assignment will logically borrow from the original `Weak`s, which will cause dropck to correctly
// complain. We can actually see this in the hints in the error messages -- they indicate htat
// `a_weak` and `b_weak` are dropped at the end of the function while still borrowed.
//
// ## Part 2: Incorrect lifetime inference
//
// So we might think to some other kind of dropping "exploit" -- where failing to indicate to
// dropck that `Borrow` owns the value would allow us to create a dangling pointer that's accessed
// in the destructor. There's an example from an actual soundess issue along these lines that
// previously existed with `SyncOnceCell`:
//
//    use std::lazy::SyncOnceCell;
//
//    struct A<'a>(&'a str);
//
//    impl<'a> Drop for A<'a> {
//        fn drop(&mut self) {
//            dbg!(self.0);
//        }
//    }
//
//    fn main() {
//        let cell = SyncOnceCell::new();
//        {
//            let s = String::from("hello world");
//            let _ = cell.set(A(&s));
//        }
//    }
//
// (Source: https://github.com/rust-lang/rust/issues/76367)
//
// This code previously compiled due to an error in `SyncOnceCell<T>`: it did not indicate to
// dropck that it logically owned a `T`, and so it was incorretly assumed that the destructor for
// `A` wouldn't run. (Note that replacing `A` with `&str` *would* be correct, because `&str`
// doesn't have a destructor; it is allowed to dangle.)
//
// So how would we go about adapting this for `Borrow`? Well... we can try it directly:
//
//   // (using struct A from above)
//
//   use std::cell::Cell;
//
//   fn main() {
//       let owned: OwnedCell<Cell<Option<A>>> = OwnedCell::new(Cell::new(None));
//       let weak = owned.weak();
//
//       {
//           let b = weak.borrow();
//           drop(owned);
//           let s = String::from("hello world");
//           b.set(Some(A(&s)));
//       }
//   }
//
// But this doesn't work -- for a similar reason to why the example in Part 1 didn't. It still
// carries the lifetime information, and so even though it's actually the *borrow* running the
// destructor, the compiler's association between the `Borrow` and its `Weak` means that the borrow
// inherits the information from dropck.
pub struct Borrow<'r, T> {
    // The original pointer to the backing allocation. We've erased the type here, and it'll be
    // properly handled in the chosen function for `do_drop`.
    base_ptr: NonNull<u8>,
    // A callback for dropping the base pointer.
    do_drop: DropFn,

    // An additional pointer back to the `borrow` field of the backing `Inner`, so that we can
    // increment it when we clone.
    borrow_ptr: *mut Option<Borrowed>,

    // The actual reference to the value. This might be mapped, or it might not be. It's largely
    // independent of the other two fields.
    value: &'r T,
}

#[derive(Copy, Clone)]
enum DropFn {
    // The normal case: the borrow is of type `T` for a borrow on `OwnedCell<T>/Weak<T>`, and the
    // borrow hasn't been mapped at all. We separate this out so that the normal path can be
    // inlined.
    Normal,
    // Some separate drop function is being used. This is set in the implementation of
    // `Borrow::map`.
    Mapped(unsafe fn(NonNull<u8>)),
}

/// A mutable borrow, constructed by [`OwnedCell::borrow_mut`]
///
/// Mutable borrows can be mapped via the associated [`map`] function.
///
/// [`map`]: Self::map
pub struct BorrowMut<'r, T> {
    // The `borrow` pointer here is raw because we only ever construct temporary references; we
    // can't hold it indefinitely, but only accessing the raw pointer when we need to means we can
    // still do it safely.
    borrow_ptr: *mut Option<Borrowed>,

    // The actual value that's being borrowed. This may have been mapped, or not.
    //
    // This is essentially just a `&'r mut T`, but we have to store it as a raw pointer in order to
    // get around not being able to copy the field.
    value: NonNull<T>,
    marker: PhantomData<&'r mut T>,
}

impl<'r, T> Borrow<'r, T> {
    /// Clones the `Borrow`, producing a new owned reference to the underlying value
    ///
    /// This method may be useful in certain cases that otherwise wouldn't have a solution, like
    /// storing both a mapped and un-mapped borrow.
    ///
    /// The `clone` method is an associated function; it could not be a proper method because that
    /// would conflict with any inherited from `Deref<Target = T>`.
    ///
    /// ## Examples
    ///
    // @def "ranged::rc::Borrow::clone doctests" v0
    /// ```
    /// let x = OwnedCell::new(3_i32);
    /// let weak = x.weak();
    /// let b1 = weak.borrow();
    /// assert_eq!(*b1, 3);
    ///
    /// // Cloning must be called as an associated function:
    /// assert_eq!(*Borrow::clone(&b1), 3);
    /// ```
    pub fn clone(this: &Borrow<'r, T>) -> Borrow<'r, T> {
        let b = unsafe { &mut *this.borrow_ptr };
        match b {
            Some(Borrowed::Immutable { count }) => {
                let new_count = match count.get().checked_add(1) {
                    Some(c) => c,
                    None => panic!(
                        "integer overflow on borrow count: cannot add 1 to {}",
                        count.get()
                    ),
                };

                // SAFETY: We already checked that incrementing didn't overflow; this value cannot
                // be zero.
                *count = unsafe { NonZeroUsize::new_unchecked(new_count) };

                Borrow {
                    base_ptr: this.base_ptr,
                    do_drop: this.do_drop,
                    borrow_ptr: this.borrow_ptr,
                    value: this.value,
                }
            }

            #[cfg(debug_assertions)]
            None => panic!("called `Borrow::clone` while not borrowed"),
            #[cfg(debug_assertions)]
            Some(Borrowed::Mutable) => panic!("called `Borrow::clone` while mutably borrowed"),

            // SAFETY: We already have an existing immutable borrow. The only way that the borrowed
            // field could not have that would be if a destructor ran twice.
            #[cfg(not(debug_assertions))]
            None | Some(Borrowed::Mutable) => unsafe { std::hint::unreachable_unchecked() },
        }
    }

    /// Maps the borrow by the given function, returning a reference to a sub-value
    ///
    /// This method is typically used to restrict a borrow, either by singling out a field or by
    /// checking that an enum is of a certain variant. It is an associated function because a
    /// proper method would conflict with any inherited from `Deref<Target = T>`.
    ///
    /// ## Examples
    ///
    /// One of the useful things that can be done with this function, for example, is to process
    /// various kinds of enums that we may know in advance are a certain variant:
    ///
    // @def "ranged::rc::Borrow::map doctests" v0
    /// ```
    /// // Unwraps the inner value, returning a reference to it
    /// //
    /// // Note: you may wish to be careful when using this function or things
    /// // like it.
    /// fn unwrap_borrow<T, E>(b: Borrow<Result<T, E>>) -> Borrow<T> {
    ///     Borrow::map(b, |r| r.as_ref().unwrap())
    /// }
    ///
    /// // Usage of this function is pretty simple though!
    /// let owned: OwnedCell<Result<_, ()>> = OwnedCell::new(Ok("I'm ok!"));
    /// let weak = owned.weak();
    ///
    /// let borrow = weak.borrow();
    /// assert_eq!(*borrow, Ok("I'm ok!"));
    ///
    /// // If the value wasn't `Ok`, we'd panic at the construction of `mapped`;
    /// // not at the dereference.
    /// let mapped = unwrap_borrow(borrow);
    /// assert_eq!(*mapped, "I'm ok!");
    /// ```
    pub fn map<U, F>(this: Borrow<'r, T>, func: F) -> Borrow<'r, U>
    where
        F: FnOnce(&T) -> &U,
    {
        // We're essentially transferring the borrow from `this` to the returned one. We don't want
        // to run any destructors in this function.
        let this = ManuallyDrop::new(this);

        Borrow {
            base_ptr: this.base_ptr,
            do_drop: match this.do_drop {
                f @ DropFn::Mapped(_) => f,
                // If we haven't changed the drop function, we can set it to what it was going to
                // be anyways:
                DropFn::Normal => DropFn::Mapped(Self::do_normal_borrow_drop),
            },
            borrow_ptr: this.borrow_ptr,
            value: func(this.value),
        }
    }
}

impl<'r, T> BorrowMut<'r, T> {
    /// Maps the borrow by the given function, returning a handle on the mutable reference to a
    /// sub-value
    ///
    /// This method is just the mutable counterpart to [`Borrow::map`]; for more information and
    /// ideas, refer to that method's documentation.
    ///
    /// ## Examples
    ///
    // @def "ranged::rc::BorrowMut::map doctests" v0
    /// ```
    /// let mut owned: OwnedCell<Result<_, ()>> = OwnedCell::new(Ok("I'm ok!"));
    /// let mut just_the_string =
    ///     BorrowMut::map(owned.borrow_mut(), |r| r.as_mut().unwrap());
    ///
    /// assert_eq!(*just_the_string, "I'm ok!");
    /// *just_the_string = "Still ok!";
    /// drop(just_the_string);
    ///
    /// assert_eq!(owned.as_ref(), &Ok("Still ok!"));
    /// ```
    pub fn map<U, F>(this: BorrowMut<'r, T>, func: F) -> BorrowMut<'r, U>
    where
        F: FnOnce(&mut T) -> &mut U,
    {
        let this = ManuallyDrop::new(this);
        // SAFETY: `this.value` is always guaranteed to be identical to a `&'r mut T` by the
        // lifetime in the marker. It is only stored as a raw pointer so that we can extract the
        // mutable reference out of `this`, which has a destructor.
        let val: &'r mut T = unsafe { &mut *this.value.as_ptr() };

        BorrowMut {
            borrow_ptr: this.borrow_ptr,
            value: NonNull::from(func(val)),
            marker: PhantomData,
        }
    }
}

// We don't need #[may_dangle] here because dropck *already* assumes that we don't own a `T`.
// Which... we might actually not. If you're worried, have a read through the comment above
// `Borrow`, which makes a lengthy argument for its soundness.
impl<'r, T> Drop for Borrow<'r, T> {
    fn drop(&mut self) {
        match self.do_drop {
            DropFn::Normal => unsafe { Self::do_normal_borrow_drop(self.base_ptr) },
            DropFn::Mapped(f) => unsafe { f(self.base_ptr) },
        }
    }
}

impl<'r, T: 'r> Borrow<'r, T> {
    // Calls `do_borrow_drop`, assuming that `ptr` is the correct value for `*mut Inner<T>`
    unsafe fn do_normal_borrow_drop(ptr: NonNull<u8>) {
        let inner_ptr = ptr.as_ptr() as *mut Inner<T>;
        Self::do_borrow_drop(inner_ptr);
    }

    // Performs the logic for dropping a `Borrow` with the given pointer to `Inner`.
    //
    // All safety considerations can be considered from the inside of the `Drop` implementation
    // above.
    #[inline(always)]
    unsafe fn do_borrow_drop(ptr: *mut Inner<T>) {
        // Dropping an immtuable borrow is sometimes tricky. In general, we're guaranteed that
        // `ptr.val` is a valid reference, and `ptr` hasn't been deallocated -- so `base_ptr.state`
        // is anything *except* `State::Dropped`.
        //
        // But other than that, there's a couple things we need to do. We need to decrement the
        // number of immutable borrows (setting `base_ptr.borrow = None` if that would be zero),
        // and if the state is `ShouldDrop`, then we also need to actually drop the value if this
        // was the last borrow.

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
            unsafe { drop_in_place(Inner::val_ptr(ptr) as *mut T) };
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
        unsafe { *self.borrow_ptr = None };
    }
}

impl<'r, T> Deref for Borrow<'r, T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.value
    }
}

impl<'r, T> Deref for BorrowMut<'r, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // SAFETY: The value pointer is forced to be treated identically to a `&'r mut T`; it's
        // just stored as a raw pointer so we can get around copying. The lifetimes guarantee that
        // the pointer is valid.
        unsafe { self.value.as_ref() }
    }
}

impl<'r, T> DerefMut for BorrowMut<'r, T> {
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: The value pointer is forced to be treated identically to a `&'r mut T`; it's
        // just stored as a raw pointer so we can get around copying. The lifetimes guarantee that
        // the pointer is valid.
        unsafe { self.value.as_mut() }
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

    // @req "ranged::rc::Weak::is_from doctests" v0
    #[test]
    fn weak_is_from() {
        let x = OwnedCell::new(3_i32);
        let y = OwnedCell::new(3_i32);

        let w = x.weak();

        assert!(w.is_from(&x));
        assert!(!w.is_from(&y));

        let z = Weak::new();
        assert!(!z.is_from(&x));
    }

    // @req "ranged::rc::Borrow::clone doctests" v0
    #[test]
    fn borrow_clone() {
        let x = OwnedCell::new(3_i32);
        let weak = x.weak();
        let b1 = weak.borrow();
        assert_eq!(*b1, 3);

        assert_eq!(*Borrow::clone(&b1), 3);
    }

    // @req "ranged::rc::Borrow::map doctests" v0
    #[test]
    fn borrow_map() {
        fn unwrap_borrow<T, E>(b: Borrow<Result<T, E>>) -> Borrow<T> {
            Borrow::map(b, |r| match r.as_ref() {
                Ok(t) => t,
                Err(_) => panic!("expected `Ok`"),
            })
        }

        let owned: OwnedCell<Result<_, ()>> = OwnedCell::new(Ok("I'm ok!"));
        let weak = owned.weak();

        let borrow = weak.borrow();
        assert_eq!(*borrow, Ok("I'm ok!"));

        let mapped = unwrap_borrow(borrow);
        assert_eq!(*mapped, "I'm ok!");

        // Not included above: check that we can mutably borrow afterwards.
        drop(mapped);
        let mut owned = owned;
        *owned.borrow_mut() = Err(());
    }

    // @req "ranged::rc::BorrowMut::map doctests" v0
    #[test]
    fn borrowmut_map() {
        let mut owned: OwnedCell<Result<_, ()>> = OwnedCell::new(Ok("I'm ok!"));
        let mut just_the_string = BorrowMut::map(owned.borrow_mut(), |r| r.as_mut().unwrap());

        assert_eq!(*just_the_string, "I'm ok!");
        *just_the_string = "Still ok!";
        drop(just_the_string);

        assert_eq!(owned.as_ref(), &Ok("Still ok!"));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    // Helper struct that sets `dropped = true` when it drops.
    struct SetOnDrop<'r> {
        dropped: &'r Cell<bool>,
    }

    impl<'r> SetOnDrop<'r> {
        fn new(dropped: &'r Cell<bool>) -> Self {
            SetOnDrop { dropped }
        }
    }

    impl<'r> Drop for SetOnDrop<'r> {
        fn drop(&mut self) {
            println!("dropping `SetOnDrop`");
            self.dropped.set(true);
        }
    }

    // Checks that the inner value is dropped as expected when the `OwnedCell` is
    #[test]
    fn drops_with_owner() {
        let dropped = Cell::new(false);

        let owned = OwnedCell::new(SetOnDrop::new(&dropped));
        assert!(!dropped.get());

        drop(owned);
        assert!(dropped.get());
    }

    #[test]
    fn lone_borrow_drops_val() {
        // Checks that - if the `OwnedCell` is dropped, the last borrow drops the value.

        // Helper struct that tells us when it's been dropped.
        struct SetOnDrop<'r> {
            dropped: &'r Cell<bool>,
        }

        impl<'r> Drop for SetOnDrop<'r> {
            fn drop(&mut self) {
                println!("drop!");
                self.dropped.set(true);
            }
        }

        let dropped = Cell::new(false);
        let owned = OwnedCell::new(SetOnDrop { dropped: &dropped });
        let weak = owned.weak();

        // Take out a borrow. Dropping the `OwnedCell` means that the borrow is the only thing
        // keeping the value alive.
        let borrow: Borrow<SetOnDrop<'_>> = weak.borrow();
        drop(owned);

        assert!(!dropped.get());

        // Dropping the borrow should drop the value as well.
        drop(borrow);
        assert!(dropped.get());
    }
}
