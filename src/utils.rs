//! Various basic utilites that are used in places throughout the project
//!
//! This is more-or-less a miscellaneous collection.

use serde::{Deserialize, Serialize};
use std::fmt::{self, Debug, Formatter, Pointer};
use std::ops::{Deref, DerefMut};

/// A trait similar to [`std::convert::Into`]; a companion to [`XFrom`]
///
/// Just like [`Into`], this trait gives a conversion method into a target type. The only major
/// difference is that the type parameter is provided as part of a generic function, which
/// allows us to write things like:
/// ```ignore
/// foo = bar.xinto::<Foo>();
/// ```
///
/// Just like the standard library's [`Into`], this trait should not be implemented manually for
/// your type -- actually, you can't! There's a blanket implementation for that! Anyways, please
/// refer to the documentation for [`XFrom`]
///
/// [`Into`]: std::convert::Into
pub trait XInto: Sized {
    fn xinto<T: XFrom<Self>>(self) -> T {
        XFrom::xfrom(self)
    }
}

impl<T> XInto for T {}

/// A trait identical to [`std::convert::From`]; a companion to [`XInto`]
///
/// This trait is essentially identical in signature to the standard library's [`From`], with the
/// real difference coming from two things:
///   1. The lack of a blanket `impl XFrom<T> for T`, and
///   2. Being able to write `impl XFrom<T> for StdLibType<S>`
/// Both of these aspects are crucial in the places that they are used, and so this warranted using
/// a distinct trait.
///
/// Because the first aspect might not seem desirable at first, let's go through an example to show
/// why it's such a crucial part.
///
/// ## An example
///
/// Suppose we wanted to write something like:
/// ```ignore
/// impl<T> From<Foo<T>> for Foo<i32> { ... }
/// ```
///
/// While it might seem fine at first, this actually conflicts with the standard library's blanket
/// implementation of `From<T> for T` - because that includes `impl From<Foo<i32>> for Foo<i32>`.
/// In order to get around this, we need a distinct trait that doesn't have that blanket
/// implementation.
///
/// There are, of course, other uses as well - this is but one example. But hopefully this should
/// explain why this trait is present in so many places here.
pub trait XFrom<T> {
    fn xfrom(other: T) -> Self;
}

impl<T: XFrom<S>, S> XFrom<Vec<S>> for Vec<T> {
    fn xfrom(vec: Vec<S>) -> Self {
        vec.into_iter().map(XInto::xinto).collect()
    }
}

/// A custom "never" type that supports (de)serialization
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub enum Never {}

impl<T> XFrom<Never> for T {
    fn xfrom(never: Never) -> T {
        match never {}
    }
}

/// Provides a string consisting exactly of `length` spaces
pub fn blank_str(length: u16) -> &'static str {
    // The size of
    const BLANK_SIZE: usize = u16::MAX as usize;
    static BLANK: [u8; BLANK_SIZE] = [b' '; BLANK_SIZE];

    unsafe { &std::str::from_utf8_unchecked(&BLANK)[..length as usize] }
}

/// A helper value for providing a `Debug` implementation for `Option`s that otherwise wouldn't
///
/// For an `Option<T>` where `T` doesn't implement `Debug`, this type produces a debug
/// implementation that either outputs `"Some(...)"` or `"None"`.
///
/// `OpaqueOption` is for use in a couple places in order to provide a debug implementation that
/// otherwise wouldn't be available, for `Option<T>` where `T` doesn't implement `Debug` (e.g. for
/// function pointers or trait objects). The standard way to create this type is with the
/// [`new`](Self::new) method.
///
/// See also: [`DebugPtr`].
///
/// ## Example
///
/// ```
/// let mut x = Some(3_i32);
/// let s = format!("{:?}", OpaqueOption::new(&x));
/// assert!(x == "Some(...)");
///
/// x = None;
/// let s = format!("{:?}", OpaqueOption::new(&x));
/// assert!(x == "None");
/// ```
pub enum OpaqueOption {
    Some,
    None,
}

impl OpaqueOption {
    /// Constructs a new `OpaqueOption`, mapping `Some(_) => Some` and `None => None`
    pub fn new<T>(opt: &Option<T>) -> OpaqueOption {
        match opt {
            None => OpaqueOption::None,
            Some(_) => OpaqueOption::Some,
        }
    }
}

impl Debug for OpaqueOption {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        match self {
            Self::Some => fmt.write_str("Some(...)"),
            Self::None => fmt.write_str("None"),
        }
    }
}

/// Helper type implementing `Debug` as the inner type's [`Pointer`] formatting
///
/// There isn't much more to it - this type is pretty simple.
///
/// See also: [`OpaqueOption`].
pub struct DebugPtr<P>(pub P);

impl<P: Pointer> Debug for DebugPtr<P> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Pointer::fmt(&self.0, f)
    }
}

/// A generic item pairing a value with a direction
///
/// Usage of this type is typically through aliasing, but there are an assortment of methods made
/// available akin to those on [`Option`].
///
// @req enum-Extract v0
// @req enum-Direction v0
/// For some of the aliases, see [`Extract`] or [`Direction`].
///
/// [`Extract`]: crate::container::paint::Extract
/// [`Direction`]: crate::view::Direction
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub enum Directional<T> {
    Up(T),
    Down(T),
    Left(T),
    Right(T),
}

/// A helper trait for debugging during tests
///
/// We use specialization to provide an implementation of this trait for all `T`, but only return
/// `Some(_)` if `T` implements `Debug`.
///
/// Because it's *only* really for use during tests, we take the simple path and return a string;
/// efficiency doesn't matter here.
pub trait MaybeDbg {
    /// Returns the output of `format!("{:?}", self)`, if it impements `Debug`; otherwise `None`.
    fn maybe_dbg(&self) -> Option<String>;
}

impl<T> MaybeDbg for T {
    // @req #![feature(specialization)] v0
    default fn maybe_dbg(&self) -> Option<String> {
        None
    }
}

// We actually don't provide a meaningful implementation outside of `cfg(test)`. We could later, if
// it's something that becomes necessary for certain types of logging, but at time of writing
// that's not planned.
#[cfg(test)]
impl<T: Debug> MaybeDbg for T {
    fn maybe_dbg(&self) -> Option<String> {
        Some(format!("{:?}", self))
    }
}

/// A mapped guard, produced by the [`map_guard`] method of [`MapDeref`]
///
/// Provides access via `F` to something in `G`. The implementation of `Deref` works in the
/// expected way, given the bounds. For more information, refer to the documentation of
/// [`MapDeref`].
///
/// A version of this type implementing `DerefMut` is available as [`MappedMutGuard`].
///
/// [`map_guard`]: MapDeref::map_guard
pub struct MappedGuard<G, F> {
    guard: G,
    func: F,
}

/// A mutable mapped guard, produced by the [`map_mut_guard`] method of [`MapDerefMut`]
///
/// Provides mutable access via `Fm` to something in `G`, or immutable access via `Fi`. The
/// implementations of `Deref` and `DerefMut` work in the expected way, given that knowledge and
/// the bounds on the types. For more information, refer to the documentation of [`MapDerefMut`].
///
/// A version of this type that only implements `Deref` is available as [`MappedGuard`].
///
/// [`map_mut_guard`]: MapDerefMut::map_mut_guard
pub struct MappedMutGuard<G, Fi, Fm> {
    guard: G,
    imut_func: Fi,
    mut_func: Fm,
}

/// Extension trait for types implementing [`Deref`], allowing mapped access to the inner value(s)
///
/// Usage of this trait tends to involve various kinds of guards, e.g. `MutexGuard` or
/// `cell::Ref`, in order to provide access to something within the types.
///
/// For a version of this trait providing mutable access, see [`MapDerefMut`].
pub trait MapDeref: Deref + Sized {
    /// Maps the guard, returning a value that implements `Deref` by calling the provided function
    /// on each dereference
    ///
    /// The return of [`MappedGuard`] is only named as a concrete type because traits cannot use
    /// the `impl Trait` syntax; usually it will not be possible to name the generic parameter `F`.
    fn map_guard<T, F>(self, func: F) -> MappedGuard<Self, F>
    where
        F: Fn(&Self::Target) -> &T,
    {
        MappedGuard { guard: self, func }
    }
}

/// Extension trait for types implementing [`DerefMut`], allowing mapped access to the inner
/// value(s)
///
/// Usage of this trait tends to involve various kinds of guards, e.g. `MutexGuard` or
/// `cell::RefMut`, in order to provide access to something within the types.
///
/// The reason we require two distinct types `Fi` and `Fm` is because we can't turn the reference
/// mutable to pass to `Fm` in the implementation of `Deref` (that would be all kinds of
/// unsafe), and we can't reasonably expect that someone provides a function from `&G -> &mut T`,
/// which would either be unsafe or trivial. So the two separate functions handle the immutable and
/// mutable cases individually.
///
/// For a version of this trait providing only immutable access, see [`MapDeref`].
pub trait MapDerefMut: DerefMut + Sized {
    /// Maps the guard, returning a value that implements `Deref` and `DerefMut` by calling the
    /// appropriate provided function on each dereference.
    ///
    /// The return of [`MappedGuard`] is only named as a concrete type because traits cannot use
    /// the `impl Trait` syntax; usually it will not be possible to name the generic parameter `F`.
    fn map_mut_guard<T, Fi, Fm>(self, imut_func: Fi, mut_func: Fm) -> MappedMutGuard<Self, Fi, Fm>
    where
        Fi: Fn(&Self::Target) -> &T,
        Fm: FnMut(&mut Self::Target) -> &mut T,
    {
        MappedMutGuard {
            guard: self,
            imut_func,
            mut_func,
        }
    }
}

// Blanket implementations of `MapDeref[Mut]`
impl<G: Deref> MapDeref for G {}
impl<G: DerefMut> MapDerefMut for G {}

// Implementations of `Deref`/`DerefMut` for `Mapped[Mut]Guard`
impl<G, F, T> Deref for MappedGuard<G, F>
where
    G: Deref,
    F: Fn(&G::Target) -> &T,
{
    type Target = T;

    fn deref(&self) -> &T {
        (self.func)(&*self.guard)
    }
}

impl<G, Fi, Fm, T> Deref for MappedMutGuard<G, Fi, Fm>
where
    G: Deref,
    Fi: Fn(&G::Target) -> &T,
{
    type Target = T;

    fn deref(&self) -> &T {
        (self.imut_func)(&*self.guard)
    }
}

impl<G, Fi, Fm, T> DerefMut for MappedMutGuard<G, Fi, Fm>
where
    G: DerefMut,
    Fi: Fn(&G::Target) -> &T, // Need to constrict Fi here so that we also implement Deref
    Fm: FnMut(&mut G::Target) -> &mut T,
{
    fn deref_mut(&mut self) -> &mut T {
        (self.mut_func)(&mut *self.guard)
    }
}
