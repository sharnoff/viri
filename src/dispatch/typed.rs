//! Wrapper module around the utilities for the types of bindings

use crate::borrow::Cow;
use num_bigint::BigInt;
use std::collections::HashMap;
use uuid::Uuid;

use viri_macros::impl_core;

/// The structure of a type used to communicate with extensions
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeRepr {
    /// A value not restricted in a predetermined way
    Any,
    /// An integer
    Int,
    /// A boolean
    Bool,
    /// A string
    String,
    /// A "unit" type -- `()`
    Unit,
    /// An `enum`, represented by the names of the variants and their corresponding types - if they
    /// have values
    Enum(HashMap<String, Option<TypeRepr>>),
    /// A `struct`, represented by the names and types of each field
    Struct(HashMap<String, TypeRepr>),
    /// An array, given by the type of the elements
    Array(Box<TypeRepr>),
    /// A tuple, given by the list of types expected
    ///
    /// The list of types should have length at least one; an empty tuple is represented by the
    /// `Unit` type.
    ///
    /// This is often also available in the bindings as an array with dynamically-typed elements.
    Tuple(Vec<TypeRepr>),
}

/// A typed, dynamic value
///
/// This is simply a way of encapsulating a value of unknown type, alongside the actual typing
/// information
pub struct Value<'a> {
    pub repr: TypeRepr,
    pub val: Cow<&'a dyn TypedDeconstruct, Box<dyn TypedDeconstruct>>,
}

impl<'a> Clone for Value<'a> {
    fn clone(&self) -> Self {
        todo!()
    }
}

impl Value<'static> {
    /// Creates a new `Value` from the concrete type representing it
    pub fn new<T: TypedDeconstruct>(val: T) -> Self {
        let repr = val.get_repr();
        Value {
            repr,
            val: Cow::Owned(Box::new(val)),
        }
    }
}

impl<'a> Value<'a> {
    /// Creates a new, borrowed `Value` from a reference to the concrete type representing it
    pub fn from_ref<T: TypedDeconstruct>(val: &'a T) -> Self {
        let repr = val.get_repr();
        Value {
            repr,
            val: Cow::Borrowed(val),
        }
    }

    /// Analagous to [`Cow::to_owned`]; converts a borrowed `Value` to one that's owned
    pub fn to_owned(self) -> Value<'static> {
        match self.val {
            Cow::Borrowed(b) => b.clone_into_value(),
            Cow::Owned(boxed) => Value {
                repr: self.repr,
                val: Cow::Owned(boxed),
            },
        }
    }

    /// Converts a `Value` into a type that it could represent
    pub fn convert<T: Typed>(&self) -> T {
        match &self.repr {
            _ => todo!(),
        }
    }
}

macro_rules! no_decon {
    ($this:expr, $ty:expr) => {{
        panic!("cannot deconstruct type as {}: {:?}", $ty, $this.get_repr())
    }};
}

/// A version of [`Typed`] that provides the utilities for deconstructing a dynamic value
///
/// This provides the deconstruction half of the internal implementation for converting from a
/// [`Value`] to a compatible concrete type. All of the provided methods have default
/// implementations that panic; when implementing this trait, only the method that must have a
/// non-panicking implementation is the one corresponding to the top-level type returned by
/// `self.get_repr()`.
#[rustfmt::skip]
pub trait TypedDeconstruct: 'static + Send + Sync {
    fn get_repr(&self) -> TypeRepr;

    /// Clones the underlying object, re-creating a corresponding `Value`
    fn clone_into_value(&self) -> Value<'static>;

    fn as_any(&self) -> Value { no_decon!(self, "<any> (`Value`)") }
    // TODO-PERF: BigInt is kinda slow. Maybe make our own implementation?
    fn as_int(&self) -> BigInt { no_decon!(self, "int") }
    fn as_bool(&self) -> bool { no_decon!(self, "bool") }
    fn as_string(&self) -> String { no_decon!(self, "string") }
    fn as_unit(&self) -> () { no_decon!(self, "unit (`()`)") }
    fn as_struct(&self) -> HashMap<String, Value> { no_decon!(self, "struct") }
    fn as_enum(&self) -> (&str, Value) { no_decon!(self, "enum variant") }
    fn as_array(&self) -> Vec<Value> { no_decon!(self, "array") }
    fn as_tuple(&self) -> Vec<Value> { no_decon!(self, "tuple") }
}

macro_rules! no_cons {
    ($This:ty, $ty:expr) => {{
        panic!(
            "cannot construct with {} for type {:?}",
            $ty,
            <$This>::repr()
        )
    }};
}

/// Trait for types that can produce a [`TypeRepr`]
///
/// This can be derived by importing [`derive_typed`], and implementations are provided for most
/// primitives. A blanket implementation for all types that dereference into one implementing
/// [`TypeRepr`] is available as well -- i.e. the the implementation for `Box<T>` is the same as
/// `T`.
///
/// Please note that it is entirely possible to *accidentally* implement this for recursive types;
/// there is currently no support for them, and so the program will run out of memory trying to
/// construct the `TypeRepr`.
#[rustfmt::skip]
#[allow(unused_variables)]
pub trait Typed: Sized {
    /// Produces the representation of this type
    fn repr() -> TypeRepr;

    fn from_any(any: Value) -> Self { no_cons!(Self, "<any> (`Value`)") }
    fn from_int(int: BigInt) -> Self { no_cons!(Self, "int") }
    fn from_bool(b: bool) -> Self { no_cons!(Self, "bool") }
    fn from_string(s: String) -> Self { no_cons!(Self, "string") }
    fn from_unit(unit: ()) -> Self { no_cons!(Self, "unit (`()`)") }
    fn from_struct(fields: HashMap<String, Value>) -> Self { no_cons!(Self, "struct") }
    fn from_variant(varant: &str, value: Value) -> Self { no_cons!(Self, "enum variant") }
    fn from_array(array: Vec<Value>) -> Self { no_cons!(Self, "array") }
    fn from_tuple(values: Vec<Value>) -> Self { no_cons!(Self, "tuple") }
}

impl_core! {
    impl for Value<'static> {
        @repr = TypeRepr::Any;
        @clone_with &self: { self.clone() }
        fn as_any(&self) -> Value { self.clone() }
        fn from_any(any: Value) -> Self { any.to_owned() }
    }

    impl for BigInt {
        @repr = TypeRepr::Int;
        @clone_with &self: { Value::new(self.clone()) }
        fn as_int(&self) -> BigInt { self.clone() }
        fn from_int(int: BigInt) -> Self { int }
    }

    impl for bool {
        @repr = TypeRepr::Bool;
        @clone_with &self: { Value::new(*self) }
        fn as_bool(&self) -> bool { *self }
        fn from_bool(b: bool) -> Self { b }
    }

    impl for String {
        @repr = TypeRepr::String;
        @clone_with &self: { Value::new(self.clone()) }
        fn as_string(&self) -> String { self.clone() }
        fn from_string(s: String) -> Self { s }
    }

    impl for () {
        @repr = TypeRepr::Unit;
        @clone_with &self: { Value::new(()) }
        fn as_unit(&self) -> () {}
        fn from_unit(_: ()) -> Self {}
    }

    impl<T: Typed + TypedDeconstruct + Clone> for Vec<T> {
        @repr = TypeRepr::Array(Box::new(T::repr()));
        @clone_with &self: { Value::new(self.clone()) }
        fn as_array(&self) -> Vec<Value> { self.iter().map(Value::from_ref).collect() }

        fn from_array(array: Vec<Value>) -> Self {
            array.iter().map(Value::convert).collect()
        }
    }
}

macro_rules! impl_tuple {
    // Handle the recursive calls so that we implement for all sizes of tuple
    ($head:ident $($tail:ident)*) => {
        impl_tuple!(@do_impl $head $($tail)*);
        impl_tuple!($($tail)*);
    };
    () => {};

    // Special case for single tuple: it'll be equivalent to the base type
    (@do_impl $name:ident) => {
        impl<$name: Typed> Typed for ($name,) {
            fn repr() -> TypeRepr { $name::repr() }

            fn from_tuple(tup: Vec<Value>) -> Self {
                match tup.as_slice() {
                    [v] => (v.convert::<$name>(),),
                    vs => panic!("unexpected number of tuple elements; expected 1, found {}", vs.len()),
                }
            }
        }

        impl<$name: Typed + TypedDeconstruct + Clone> TypedDeconstruct for ($name,) {
            fn get_repr(&self) -> TypeRepr { <Self as Typed>::repr() }
            fn clone_into_value(&self) -> Value<'static> { Value::new(self.clone()) }
            fn as_tuple(&self) -> Vec<Value> { vec![Value::from_ref(&self.0)] }
        }
    };
    // Actually construct the implementation
    (@do_impl $($name:ident)*) => {
        impl<$($name: Typed),*> Typed for ($($name),*) {
            fn repr() -> TypeRepr {
                TypeRepr::Tuple(vec![$($name::repr()),*])
            }

            #[allow(non_snake_case)]
            fn from_tuple(tup: Vec<Value>) -> Self {
                match tup.as_slice() {
                    [$($name,)*] => ($($name.convert::<$name>(),)*),
                    vs => panic!(
                        "unexpected number of tuple elements; expected {}, found {}",
                        impl_tuple!(@count $($name)*),
                        vs.len()
                    ),
                }
            }
        }

        impl<$($name: Typed + TypedDeconstruct + Clone),*> TypedDeconstruct for ($($name),*) {
            fn get_repr(&self) -> TypeRepr { <Self as Typed>::repr() }
            fn clone_into_value(&self) -> Value<'static> { Value::new(self.clone()) }
            #[allow(non_snake_case)]
            fn as_tuple(&self) -> Vec<Value> {
                let ($($name),*) = self;
                vec![$( Value::from_ref($name) ),*]
            }
        }
    };
    // Count the number of names
    (@count) => {{ 0 }};
    (@count $head:ident $($tail:ident)*) => {{ 1 + impl_tuple!(@count $($tail)*) }};
}

impl_tuple! {
    A B C D E F G H I J K L M N O P
}

//////////////////////////////////
// Special-case implementations //
//////////////////////////////////

// UUIDs are represented as a string -- not every language might treat 128-bit integers nicely.
impl Typed for Uuid {
    fn repr() -> TypeRepr {
        TypeRepr::String
    }

    fn from_string(s: String) -> Self {
        Uuid::parse_str(s.as_str()).expect("invalid UUID")
    }
}

impl TypedDeconstruct for Uuid {
    fn get_repr(&self) -> TypeRepr {
        <Self as Typed>::repr()
    }

    fn clone_into_value(&self) -> Value<'static> {
        Value::new(*self)
    }

    fn as_string(&self) -> String {
        format!("{:x}", self.to_hyphenated_ref())
    }
}
