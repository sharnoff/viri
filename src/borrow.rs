//! Replacement for `std::borrow`, making `Cow` just for abstraction
//!
//! There's a particular problem with the standard library's [`Cow`](std::borrow::Cow): it has a
//! great interface for abstracting over owned or borrowed data, but requires the ability to clone
//! it. This is really quite unfortunate, because we'd like to use it for trait objects, where the
//! clone bound isn't possible to satisfy.
//!
//! So the utilities in this module provide a sort of "better" interface around this idea, making
//! the ability to clone an opt-in behavior. As such, the traits and types within [`std::borrow`]
//! are replicated here, to some extent.

use std::ops::{Deref, DerefMut};

/// We're just re-exporting `Borrow` and `BorrowMut`, because they're defined nicely
pub use std::borrow::{Borrow, BorrowMut};

// Just internally, it's nice not needing to write `Cow::` before each usage of these
use Cow::{Borrowed, Owned};

/// A modified version of [`std::borrow::Cow`], allowing greater flexibility in usage
///
/// The primary difference between this type and the one from the standard library is that
#[derive(Debug, Clone)]
pub enum Cow<B, W> {
    Borrowed(B),
    Owned(W),
}

impl<B: ToOwned<Owned = W>, W> Cow<B, W> {
    /// Extracts the owned data, cloning if it is not already owned
    fn into_owned(self) -> W {
        match self {
            Owned(w) => w,
            Borrowed(b) => b.to_owned(),
        }
    }

    /// Provides a mutable reference to the owned data, cloning if it is not already owned
    fn to_mut(&mut self) -> &mut W {
        if let Borrowed(b) = self {
            *self = Owned(b.to_owned());
        }

        match self {
            Owned(w) => w,
            Borrowed(_) => unreachable!(),
        }
    }
}

impl<B, W: Borrow<B>> AsRef<B> for Cow<B, W> {
    fn as_ref(&self) -> &B {
        match self {
            Borrowed(b) => b,
            Owned(w) => w.borrow(),
        }
    }
}

impl<B, W: Borrow<B>> Deref for Cow<B, W> {
    type Target = B;

    fn deref(&self) -> &B {
        match self {
            Borrowed(b) => b,
            Owned(w) => w.borrow(),
        }
    }
}

impl<B, W: BorrowMut<B>> DerefMut for Cow<B, W> {
    fn deref_mut(&mut self) -> &mut B {
        match self {
            Borrowed(b) => b,
            Owned(w) => w.borrow_mut(),
        }
    }
}
