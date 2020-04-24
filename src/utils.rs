//! Various basic utilites that are used in places throughout the project
use crate::prelude::*;

/// A convenience type for allowing efficient production of one or many values
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Seq<T> {
    One(T),
    Many(Vec<T>),
}

impl<T, S: XInto<T>> XFrom<Seq<S>> for Seq<T> {
    fn xfrom(seq: Seq<S>) -> Seq<T> {
        match seq {
            One(s) => One(s.xinto()),
            Many(v) => Many(v.into_iter().map(XInto::xinto).collect()),
        }
    }
}

impl<T> XFrom<Vec<T>> for Seq<T> {
    fn xfrom(v: Vec<T>) -> Self {
        Many(v)
    }
}

impl<T> Seq<T> {
    pub fn map<S>(self, f: impl Fn(T) -> S) -> Seq<S> {
        match self {
            One(t) => One(f(t)),
            Many(v) => Many(v.into_iter().map(f).collect()),
        }
    }
}

/// A generic fallible type
pub trait Monad {
    type Success;
    type Error;

    fn is_success(&self) -> bool;
    fn is_error(&self) -> bool;

    fn pass(val: Self::Success) -> Self;
    fn fail(err: Self::Error) -> Self;

    fn unwrap(self) -> Self::Success;
}

#[rustfmt::skip]
impl<T,E> Monad for Result<T,E> {
    type Success = T;
    type Error = E;

    fn is_success(&self) -> bool { self.is_ok() }
    fn is_error(&self) -> bool { self.is_err() }

    fn pass(val: T) -> Self { Ok(val) }
    fn fail(err: E) -> Self { Err(err) }

    fn unwrap(self) -> T { self.unwrap() }
}

#[rustfmt::skip]
impl<T> Monad for Option<T> {
    type Success = T;
    type Error = ();

    fn is_success(&self) -> bool { self.is_some() }
    fn is_error(&self) -> bool { self.is_none() }

    fn pass(val: T) -> Self { Some(val) }
    fn fail(err: ()) -> Self { None }

    fn unwrap(self) -> T { self.unwrap() }
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

/// A custom "never" type that supports (de)serialization
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub enum Never {}

impl<T> XFrom<Never> for T {
    fn xfrom(never: Never) -> T {
        unreachable!()
    }
}
