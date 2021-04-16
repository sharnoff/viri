//! Wrapper module around the utilities for the types of bindings

use crate::borrow::Cow;
use num_bigint::BigInt;
use std::collections::HashMap;
// use std::convert::TryInto;
// use uuid::Uuid;

use crate::macros::manual_derive_typed;

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
    /// The list of types should have length at least two; an empty tuple is represented by the
    /// `Unit` type and tuples containing a single type are treated as if they were the inner type
    /// itself.
    ///
    /// This is often also available in the bindings as an array with dynamically-typed elements.
    Tuple(Vec<TypeRepr>),
}

/// A typed, dynamic value
///
/// This is simply a way of encapsulating a value of unknown type, alongside the actual typing
/// information
pub struct Value<'a> {
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
        Value {
            val: Cow::Owned(Box::new(val)),
        }
    }
}

impl<'a> Value<'a> {
    /// Creates a new, borrowed `Value` from a reference to the concrete type representing it
    pub fn from_ref<T: TypedDeconstruct>(val: &'a T) -> Self {
        Value {
            val: Cow::Borrowed(val),
        }
    }

    /// Analagous to [`Cow::to_owned`]; converts a borrowed `Value` to one that's owned
    pub fn to_owned(self) -> Value<'static> {
        match self.val {
            Cow::Borrowed(b) => b.clone_into_value(),
            Cow::Owned(boxed) => Value {
                val: Cow::Owned(boxed),
            },
        }
    }

    /// Converts a `Value` into a type that it could represent
    pub fn convert<T: Typed>(&self) -> Result<T, String> {
        todo!()
    }
}

/// Types that can be converted back and forth within [`Value`]s
///
/// This trait is simply the union of [`TypedConstruct`] and [`TypedDeconstruct`], which appropriately
/// provide the two halves of these operations: construction and deconstruction. The two halves are
/// distinct because `Value` relies on being able to create a trait object for `TypedDeconstruct`,
/// which cannot be done with the functionality of `TypedConstruct`.
///
/// A blanket implementation for all types that both implement [`TypedConstruct`] and
/// [`TypedDeconstruct]` is provided here; this trait really just allows shorthand for requiring
/// that something implement both.
///
/// For more information, see the documentation for [`Value`] and the two respective halves of the
/// conversion system here. There is also a [derive macro](crate::macros::Typed) for generating
/// implementations of both of the supertraits.
pub trait Typed: TypedConstruct + TypedDeconstruct {}

impl<T: TypedConstruct + TypedDeconstruct> Typed for T {}

/// The deconstruction half of the facilities for [`Typed`] values.
///
/// This trait is provided separately so that it can be used as a trait object in [`Value`], for
/// converting an erased type into a concrete value.
///
/// ## Usage
///
/// The general way that this trait is used is by attempting to read the value as one of the
/// possible variants. This typically comes from within the implementation of [`TypedConstruct`],
/// though it *could* be used anywhere.
///
/// The default implementation of each method panics; only the method specified by the return value
/// will be called, so it is the only one for which this should (usually) be overriden.
///
/// ## Representations
///
/// There are sometimes multiple possible ways that a value can be represented - like enums, for
/// example. Let's look at a case here:
/// ```
/// enum Tricky<T> {
///     Unit,
///     Generic(T),
///     Struct { x: i32 },
/// }
/// ```
/// Using JSON as an indicator of the actual structure (because this format loosely mirrors it), we
/// could represent a value of type `Tricky` with any of:
///
/// ```js
/// // Tricky::Unit
/// "Unit"
/// { "Unit": {} }
///
/// // Tricky::Generic<()>
/// "Generic"
/// // Tricky::Generic<T>
/// { "Generic": <value for T> }
///
/// // Tricky::Struct
/// { "Struct": { "x": <integer> } }
/// ```
///
/// So converting to a value of type `Tricky` (and indeed, any other `enum`) might involve
/// attempting to construct from either a string, `enum`, or `struct` variant. This is somewhat
/// similar to the representations described in 
#[rustfmt::skip]
pub trait TypedDeconstruct: 'static + Send + Sync {
    /// Returns the kind of type this object is, as a hint for which one of the other methods to
    /// call
    fn type_kind(&self) -> TypeKind;

    /// Clones the underlying object, re-creating a corresponding [`Value`]
    ///
    /// This method is required so that we can have a `Clone` implementation on `Value`, as well as
    /// the [`to_owned`](Value::to_owned) method.
    fn clone_into_value(&self) -> Value<'static>;

    /// Provides access to the value as an integer, under the assumption that it has that type
    fn as_int(&self) -> BigInt { unimplemented!() }
    /// Provides access to the value as a boolean, under the assumption that it has that type
    fn as_bool(&self) -> bool { unimplemented!() }
    /// Provides access to the value as a string, under the assumption that it has that type
    fn as_string(&self) -> String { unimplemented!() }
    /// Provides access to the value as the map of struct fields, under the assumption that the
    /// value has a struct type
    fn as_struct(&self) -> HashMap<String, Value> { unimplemented!() }
    /// Provides access to the value as an array of values. Because there is no way to guarantee
    /// that these values are all the same type, this method is also used for providing access to
    /// tuples.
    fn as_array(&self) -> Vec<Value> { unimplemented!() }
}

/// Helper type for [`TypedConstruct`]: the different types that we might try to construct a value
/// from
///
/// The variants here serve to provide a sort of directive as to how we can parse a value with the
/// implementation of the associated functions in [`TypedConstruct`]. For more information, please
/// refer to the documentation of the trait itself.
#[derive(Copy, Clone)]
pub enum TypeKind {
    Any,
    Int,
    Bool,
    String,
    Unit,
    Struct,
    Array,
}

// TODO-DOC: all return types are Result<Self, T>,
// TODO-DOC: mostly exists to provide information to `Value::convert`
#[rustfmt::skip]
pub trait TypedConstruct: 'static + Sized {
    /// The set of types that we can attempt to construct a value of this type from
    ///
    /// For most types, this will be a single value, e.g. `String` or `Struct`. But for *some*
    /// others (particularly `enum`s), there are multiple possible ways to produce a value. Only
    /// the methods corresponding to types given here will be attempted.
    ///
    /// To clarify: if `cons_order()` only returns `&[TypeKind::String]`, then only `from_string`
    /// will be called, if anything.
    fn cons_order() -> &'static [TypeKind];

    /// Produces a diagnostic string to indicate that an error has occured. The string should be
    /// something along the lines of `"expected foobar"`.
    fn err_string() -> &'static str;

    /// Attempts to construct the type directly from the `Value` itself
    fn from_any(any: Value<'static>) -> Result<Self, String> { unimplemented!() }
    /// Attempts to produce the value from an integer
    fn from_int(int: BigInt) -> Result<Self, String> { unimplemented!() }
    /// Attempts to produce the value from a boolean
    fn from_bool(b: bool) -> Result<Self, String> { unimplemented!() }
    /// Attempts to produce the value from a string
    fn from_string(s: String) -> Result<Self, String> { unimplemented!() }
    /// Attempts to produce the value from a unit
    fn from_unit() -> Result<Self, String> { unimplemented!() }
    /// Attempts to construct a value from the fields of a struct
    fn from_struct(fields: HashMap<String, Value>) -> Result<Self, String> { unimplemented!() }
    /// Attempts to construct a value from a dynamically-typed array (i.e. the elements are not
    /// guaranteed to have the same type)
    fn from_array(array: Vec<Value>) -> Result<Self, String> { unimplemented!() }
}

macro_rules! impl_core {
    ($(
        impl$([$($generics:tt)*])? for $ty:ty {
            @repr = $repr:expr;
            @cons = $cons_order:expr;
            @err = $err_string:expr;
            @cons_fns = { $($cons_tt:tt)* };
            @decon_fns = { $($decon_tt:tt)* };
        }
    )*) => {
        $(
        impl$($($generics)*)? TypedConstruct for $ty {
            fn cons_order() -> &'static [TypeKind] { &$cons_order }
            fn err_string() -> &'static str { $err_string }

            $($cons_tt)*
        }

        impl$($($generics)*)? TypedDeconstruct for $ty {
            fn type_kind(&self) -> TypeKind { $repr }

            $($decon_tt)*
        }
        )*
    };
}

type ConsRes<T> = Result<T, String>;

impl_core! {
    impl for Value<'static> {
        @repr = TypeKind::Any;
        @cons = [TypeKind::Any];
        @err = "expected any value";
        @cons_fns = {
            fn from_any(any: Value<'static>) -> ConsRes<Self> { Ok(any) }
        };
        @decon_fns = {
            fn clone_into_value(&self) -> Value<'static> { self.clone() }
        };
    }

    impl for BigInt {
        @repr = TypeKind::Int;
        @cons = [TypeKind::Int];
        @err = "expected an integer";
        @cons_fns = {
            fn from_int(int: BigInt) -> ConsRes<Self> { Ok(int) }
        };
        @decon_fns = {
            fn clone_into_value(&self) -> Value<'static> { Value::new(self.clone()) }
            fn as_int(&self) -> BigInt { self.clone() }
        };
    }

    impl for bool {
        @repr = TypeKind::Bool;
        @cons = [TypeKind::Bool];
        @err = "expected a boolean";
        @cons_fns = {
            fn from_bool(b: bool) -> ConsRes<Self> { Ok(b) }
        };
        @decon_fns = {
            fn clone_into_value(&self) -> Value<'static> { Value::new(*self) }
            fn as_bool(&self) -> bool { *self }
        };
    }

    impl for String {
        @repr = TypeKind::String;
        @cons = [TypeKind::String];
        @err = "expected a string";
        @cons_fns = {
            fn from_string(s: String) -> ConsRes<Self> { Ok(s) }
        };
        @decon_fns = {
            fn clone_into_value(&self) -> Value<'static> { Value::new(self.clone()) }
            fn as_string(&self) -> String { *self }
        };
    }

    impl for () {
        @repr = TypeKind::Unit;
        @cons = [TypeKind::Unit, TypeKind::Struct, TypeKind::Array];
        @err = "expected a unit value, empty struct, or empty array";
        @cons_fns = {
            fn from_unit() -> ConsRes<Self> { Ok(()) }
            fn from_struct(fields: HashMap<String, Value>) -> ConsRes<Self> {
                match fields.is_empty() {
                    true => Ok(()),
                    false => Err("expected a struct with no fields".to_owned()),
                }
            }
            fn from_array(array: Vec<Value>) -> ConsRes<Self> {
                match array.is_empty() {
                    true => Ok(()),
                    false => Err("expected an array with no elements".to_owned()),
                }
            }
        };
        @decon_fns = {
            fn clone_into_value(&self) -> Value<'static> { Value::new(()) }
        };
    }

    impl[<T: Typed>] for (T,) {
        @repr = T::type_kind();
        @cons = T::cons_order();
        @err = T::err_string();
        @cons_fns = {
            fn from_any(any: Value<'static>) -> ConsRes<Self>
                { T::from_any(any).map(|t| (t,)) }
            fn from_int(int: BigInt) -> ConsRes<Self> { T::from_int(int).map(|t| (t,)) }
            fn from_bool(b: bool) -> ConsRes<Self> { T::from_bool(b).map(|t| (t,)) }
            fn from_string(s: String) -> ConsRes<Self> { T::from_string(s).map(|t| (t,)) }
            fn from_unit() -> ConsRes<Self> { T::from_unit().map(|t| (t,)) }
            fn from_struct(fs: HashMap<String, Value>) -> ConsRes<Self>
                { T::from_struct(fs).map(|t| (t,)) }
            fn from_array(a: Vec<Value>) -> ConsRes<Self> { T::from_array(a).map(|t| (t,)) }
        };
        @decon_fns = {
            fn clone_into_value(&self) -> Value<'static> { self.0.clone_into_value() }

            fn as_int(&self) -> BigInt { self.0.as_int() }
            fn as_bool(&self) -> bool { self.0.as_bool() }
            fn as_string(&self) -> String { self.0.as_string() }
            fn as_struct(&self) -> HashMap<String, Value> { self.0.as_struct() }
            fn as_array(&self) -> Vec<Value> { self.0.as_array() }
        };
    }

    impl[<T: Typed>] for Vec<T> {
        @repr = TypeKind::Array;
        @cons = [TypeKind::Array];
        @err = "expected an array";
        @cons_fns = {
            fn from_array(array: Vec<Value>) -> ConsRes<Self> {
                array.into_iter().map(Value::convert).collect()
            }
        };
        @decon_fns = {
            fn clone_into_value(&self) -> Value<'static> { todo!() }
            fn as_array(&self) -> Vec<Value> {
                self.iter().map(Value::from_ref).collect()
            }
        };
    }

    // impl[<T: Clone + Typed, const N: usize>] for [T; N] {
    //     @repr = TypeKind::Array;
    //     @cons = [TypeKind::Array];
    //     @err = "expected an array of length (TODO)";
    //     @cons_fns = {
    //         fn from_array(array: Vec<Value>) -> ConsRes<Self> {
    //             array.iter()
    //                 .map(Value::convert)
    //                 .collect::<Result<Self, _>>()?
    //                 .try_into()
    //                 .map_err(|e| e.to_string())
    //         }
    //     };
    //     @decon_fns = {
    //         fn clone_into_value(&self) -> Value<'static> { Value::new(self.clone()) }
    //         fn as_array(&self) -> Vec<Value> {
    //             self.iter().map(Value::from_ref).collect()
    //         }
    //     };
    // }
}

macro_rules! impl_int {
    ($($int_ty:ty: $convert:ident,)*) => {
        impl_core! {
            $(
            impl for $int_ty {
                @repr = TypeKind::Int;
                @cons = [TypeKind::Int];
                @err = concat!("expected ", stringify!($int_ty));
                @cons_fns = {
                    fn from_int(int: BigInt) -> ConsRes<Self> {
                        use num::cast::ToPrimitive;

                        int.$convert().ok_or_else(|| {
                            format!("integer {} cannot fit within {}", int, stringify!($int_ty))
                        })
                    }
                };
                @decon_fns = {
                    fn clone_into_value(&self) -> Value<'static> { Value::new(*self) }
                    fn as_int(&self) -> BigInt { self.into() }
                };
            }
            )*
        }
    }
}

impl_int! {
    u8: to_u8,
    u16: to_u16,
    u32: to_u32,
    u64: to_u64,
    u128: to_u128,
    usize: to_usize,
    i8: to_i8,
    i16: to_i16,
    i32: to_i32,
    i64: to_i64,
    i128: to_i128,
    isize: to_isize,
}

// Produces implementations for tuples of size >= 2. Tuples of size 1 are treated as equivalent to
// the inner type, so we ignore them. Tuples of size 0 are the "unit"; we exclude them.
macro_rules! impl_tuple {
    ($head:ident $next:ident $($tail:ident)*) => {
        impl_tuple!(@do_impl $head $next $($tail)*);
        impl_tuple!(@do_impl $next $($tail)*);
        impl_tuple!($($tail)*);
    };
    // Don't do anything for size 0 or 1
    ($($ignore:ident)?) => {};

    // The actual implementations for tuples of various sizes:
    (@do_impl $($name:ident)*) => {
        impl_core! {
            impl[<$($name: Typed + Clone),*>] for ($($name,)*) {
                @repr = TypeKind::Array;
                @cons = [TypeKind::Array];
                // TODO: This should include the length of the tuple, even though it's in a static
                // string.
                @err = "expected tuple (as array)";
                @cons_fns = {
                    #[allow(non_snake_case)]
                    fn from_array(array: Vec<Value>) -> ConsRes<Self> {
                        match array.as_slice() {
                            [$($name,)*] => Ok(($($name.convert::<$name>()?,)*)),
                            vs => Err(format!(
                                "expected tuple with {} elements, found {}",
                                impl_tuple!(@count $($name)*),
                                vs.len(),
                            )),
                        }
                    }
                };
                @decon_fns = {
                    fn clone_into_value(&self) -> Value<'static> { Value::new(self.clone()) }
                    #[allow(non_snake_case)]
                    fn as_array(&self) -> Vec<Value> {
                        let ($($name),*) = self;
                        vec![$( Value::from_ref($name) ),*]
                    }
                };
            }
        }
    };
    (@count) => {{ 0 }};
    (@count $head:ident $($tail:ident)*) => {{ 1 + impl_tuple!(@count $($tail)*) }};
}

use std::marker::PhantomData;

manual_derive_typed! {
    struct PhantomData<T>;
}

// manual_derive_typed! {
//     enum Result<T, E> {
//         Ok(T),
//         Err(E),
//     }
// }

impl_tuple! {
    A B C D E F G H I J K L M N O
}
