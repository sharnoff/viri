//! Various basic utilites that are used in places throughout the project
//!
//! This is more-or-less a miscellaneous collection.

use serde::{Deserialize, Serialize};
use std::fmt::{self, Debug, Formatter};

/// A generic fallible type
pub trait Monad {
    type Success;
    type Error;

    fn is_success(&self) -> bool;
    fn is_error(&self) -> bool;

    fn pass(val: Self::Success) -> Self;
    fn fail(err: Self::Error) -> Self;

    fn unwrap(self) -> Self::Success;
    fn unwrap_err(self) -> Self::Error;
}

#[rustfmt::skip]
impl<T: std::fmt::Debug,E: std::fmt::Debug> Monad for Result<T,E> {
    type Success = T;
    type Error = E;

    fn is_success(&self) -> bool { self.is_ok() }
    fn is_error(&self) -> bool { self.is_err() }

    fn pass(val: T) -> Self { Ok(val) }
    fn fail(err: E) -> Self { Err(err) }

    fn unwrap(self) -> T { Result::unwrap(self) }
    fn unwrap_err(self) -> E { Result::unwrap_err(self) }
}

#[rustfmt::skip]
impl<T> Monad for Option<T> {
    type Success = T;
    type Error = ();

    fn is_success(&self) -> bool { self.is_some() }
    fn is_error(&self) -> bool { self.is_none() }

    fn pass(val: T) -> Self { Some(val) }
    fn fail(_err: ()) -> Self { None }

    fn unwrap(self) -> T { Option::unwrap(self) }
    fn unwrap_err(self) -> () { assert!(self.is_none()); () }
}

pub trait XInto<T> {
    fn xinto(self) -> T;
}

pub trait XFrom<T> {
    fn xfrom(other: T) -> Self;
}

impl<T, S: XFrom<T>> XInto<S> for T {
    fn xinto(self) -> S {
        S::xfrom(self)
    }
}

impl<T: XInto<S>, S> XFrom<Vec<T>> for Vec<S> {
    fn xfrom(vec: Vec<T>) -> Self {
        vec.into_iter().map(XInto::xinto).collect()
    }
}

/// A custom "never" type that supports (de)serialization
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub enum Never {}

impl<T> XFrom<Never> for T {
    fn xfrom(_never: Never) -> T {
        unreachable!()
    }
}

/// A large array of spaces, used in various places
///
/// `0x20` is the byte value for 'space', so we'll just store a whole bunch of them.
const BLANK: [u8; BLANK_SIZE] = [0x20; BLANK_SIZE];
const BLANK_SIZE: usize = u16::MAX as usize;

/// Provides a string consisting exactly of `length` spaces.
pub fn blank_str(length: u16) -> &'static str {
    unsafe { &std::str::from_utf8_unchecked(&BLANK)[..length as usize] }
}

/// A helper value for providing a `Debug` implementation for `Option`s that otherwise wouldn't
///
/// This is for use in a couple places in order to provide a debug implementation that otherwise
/// wouldn't be available, for `Option<T>` where `T` doesn't implement `Debug` (e.g. for function
/// pointers or trait objects).
///
/// These can be created by the implementation of `From` for `&Option<T>`.
///
/// The debug implementation simply outputs `None` or `Some(...)`.
pub enum OpaqueOption {
    Some,
    None,
}

impl<T> From<&Option<T>> for OpaqueOption {
    fn from(opt: &Option<T>) -> OpaqueOption {
        match opt {
            &Some(_) => OpaqueOption::Some,
            &None => OpaqueOption::None,
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
