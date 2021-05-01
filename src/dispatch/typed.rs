//! Wrapper module around the utilities for the types of bindings

use crate::borrow::Cow;
use num_bigint::BigInt;
use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};
use std::ops::Deref;

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
    /// An `enum`, represented by the names of the variants and their corresponding types.
    /// Value-less enum variants are represented by `TypeRepr::Unit`.
    Enum(HashMap<String, TypeRepr>),
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

/// Type alias for convenience - the result of type conversion operations
pub type Result<T> = std::result::Result<T, Error>;

/// A contextual error for type construction
///
/// This error is primarily in the results returned by [`TypedConstruct`] methods. It serves to
/// pair the cause of the error with the access on the value that would lead to it.
///
/// ## An illustrative example
///
/// It's worth looking at an example to get a sense of what this error looks like. Let's suppose we
/// parsed the following JSON value:
/// ```text
/// { "id": 4, "values": [0, 1, 2, "three"] }
/// ```
/// We want to convert this abstract JSON value into our expected Rust type - say:
/// ```
/// #[derive(Typed)]
/// struct IdWithValues {
///     id: usize,
///     values: Vec<i32>,
/// }
/// ```
///
/// The problem here is clearly that the third element of the parsed `values` array isn't an
/// integer! And so the resulting error will looks something like:
/// ```text
/// in .values[3]: expected an integer
/// ```
///
/// ## Usage
///
/// The individual elements of the context are built in reverse order, by successive calls to the
/// [`context`](Self::context) method. So we could generate this error with:
///
/// ```
/// # use super::Error;
/// let err = Error::from_str("expected an integer")
///     .context("[3]")
///     .context(".values");
///
/// assert_eq!(err.to_string(), "in .values[3]: expected an integer");
/// ```
///
/// All `Error`s are initially constructed with the [`from_str`](Self::from_str) method.
#[derive(Debug, Clone)]
pub struct Error {
    // The context is stored backwards, so that wrapping with context is just appending to the end
    context: Vec<std::borrow::Cow<'static, str>>,
    message: std::borrow::Cow<'static, str>,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if !self.context.is_empty() {
            f.write_str("in ")?;
        }

        for s in self.context.iter().rev() {
            f.write_str(&s)?;
        }

        write!(f, ": {}", self.message)
    }
}

impl std::error::Error for Error {}

impl From<String> for Error {
    fn from(message: String) -> Self {
        Error::from_str(message)
    }
}

impl From<&'static str> for Error {
    fn from(message: &'static str) -> Self {
        Error::from_str(message)
    }
}

impl Error {
    /// Constructs an error with no context from the message
    pub fn from_str(message: impl Into<std::borrow::Cow<'static, str>>) -> Self {
        Error {
            context: Vec::new(),
            message: message.into(),
        }
    }

    /// Adds the contextual information to the error
    ///
    /// Because these errors can occur deep inside nested structs, contexts are always additive.
    /// Here, each piece of context gets prepended to the full error message. These usually
    /// indicate some kind of access into the value being deconstructed.
    ///
    /// Let's look at an example. Suppose our error says something like:
    /// ```text
    /// in .notifications[0].msg: expected a string
    /// ```
    /// The full context here is `".notifications[0].msg"`. If this occured as part of a deeper
    /// structure, we might add some context like: `".all_events"`, which would result in the
    /// following new error message:
    /// ```text
    /// in .all_events.notifications[0].msg: expected a string
    /// ```
    ///
    /// It's typically expected that this method will be called to provide the appropriate context
    /// to errors. The full error produced might otherwise appear incorrect.
    pub fn context(mut self, ctx: impl Into<std::borrow::Cow<'static, str>>) -> Self {
        self.context.push(ctx.into());
        self
    }
}

/// A typed, dynamic value
///
/// This is simply a way of encapsulating a value of unknown type, alongside the actual typing
/// information
pub struct Value<'a> {
    val: Cow<&'a dyn TypedDeconstruct, Box<dyn TypedDeconstruct>>,
}

impl<'a> Clone for Value<'a> {
    fn clone(&self) -> Self {
        match self.val {
            Cow::Owned(ref boxed) => return boxed.clone_into_value(),
            Cow::Borrowed(v) => Value {
                val: Cow::Borrowed(v),
            },
        }
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

    /// Returns a reference to the inner trait object
    pub fn inner(&self) -> &dyn TypedDeconstruct {
        match &self.val {
            Cow::Borrowed(r) => *r,
            Cow::Owned(boxed) => boxed.deref(),
        }
    }

    /// Converts a `Value` into a type that it could represent
    pub fn convert<T: TypedConstruct>(&self) -> Result<T> {
        let inner = self.inner();
        let self_kind = inner.type_kind();

        let kind = T::cons_order()
            .iter()
            .cloned()
            .find(|&k| k == self_kind)
            .ok_or_else(|| T::err_string())?;

        match kind {
            TypeKind::Any => T::from_any(inner.clone_into_value()),
            TypeKind::Int => T::from_int(inner.as_int()),
            TypeKind::Bool => T::from_bool(inner.as_bool()),
            TypeKind::String => T::from_string(inner.as_string()),
            TypeKind::Unit => Ok(T::from_unit()),
            TypeKind::Struct => T::from_struct(inner.as_struct()),
            TypeKind::Array => T::from_array(inner.as_array()),
        }
    }
}

/// Types that can be converted back and forth within [`Value`]s
///
/// This trait is primarily the union of [`TypedConstruct`] and [`TypedDeconstruct`], which
/// appropriately provide the two halves of the `Typed` system: construction and deconstruction.
/// These are distinct because [`Value`] relies on being able to create a trait object for
/// `TypedDeconstruct`, which cannot be done with the functionality of `TypedConstruct`.
///
/// For more information, see the documentation for [`Value`] and the two respective halves of the
/// conversion system here. There is also a [derive macro](crate::macros::Typed) for generating
/// implementations of both of the supertraits.
pub trait Typed: TypedConstruct + TypedDeconstruct {
    /// Produces the concrete representation of the type
    ///
    /// This allows named types to be used within the [`type_sig!`](crate::macros::type_sig) macro.
    fn repr() -> TypeRepr;
}

/// Helper type for [`TypedConstruct`]: the different types that we might try to construct a value
/// from
///
/// The variants here serve to provide a sort of directive as to how we can parse a value with the
/// implementation of the associated functions in [`TypedConstruct`]. For more information, please
/// refer to the documentation of the trait itself.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TypeKind {
    Any,
    Int,
    Bool,
    String,
    Unit,
    Struct,
    Array,
}

/// The construction half of the facilities for [`Typed`] values
///
/// This trait serves to define the way that the value of this type can be constructed. Each of the
/// `from_*` methods have a provided implementation that simply panics -- only the applicable
/// methods should be implemented.
///
/// The `cons_order` function indicates which construction functions can be attempted without
/// panicking. When using [`Value::convert`], only one such function will be attempted at a time,
/// given by the indicated `TypeKind` of the corresponding deconstructed type.
/// 
/// This trait really only exists to provide information to `Value::convert`.
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
    fn from_any(any: Value<'static>) -> Result<Self> { unimplemented!() }
    /// Attempts to produce the value from an integer
    fn from_int(int: BigInt) -> Result<Self> { unimplemented!() }
    /// Attempts to produce the value from a boolean
    fn from_bool(b: bool) -> Result<Self> { unimplemented!() }
    /// Attempts to produce the value from a string
    fn from_string(s: String) -> Result<Self> { unimplemented!() }
    /// Produces the value from a unit
    fn from_unit() -> Self { unimplemented!() }
    /// Attempts to construct a value from the fields of a struct
    fn from_struct(fields: HashMap<String, Value>) -> Result<Self> { unimplemented!() }
    /// Attempts to construct a value from a dynamically-typed array (i.e. the elements are not
    /// guaranteed to have the same type)
    fn from_array(array: Vec<Value>) -> Result<Self> { unimplemented!() }
}

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

// Implementations on "primitive" types
//
// These don't necessarily align with the standard library's "primitive" types, but are instead
// more along the lines of the set of primitive-like things that we could expect implementations
// for, e.g. `String`, `BigInt`, etc - alongside many of the standard library's primitives, as
// well.
mod primitive_impls {
    use super::*;

    macro_rules! impl_core {
        ($(
            impl$([ ($($typed_generics:tt)*)($($cons_generics:tt)*)($($decon_generics:tt)*) ])? for $ty:ty {
                @repr = $repr:expr;
                @kind = $kind:expr;
                @cons = $cons_order:expr;
                @err = $err_string:expr;
                @cons_fns = { $($cons_tt:tt)* };
                @decon_fns = { $($decon_tt:tt)* };
            }
        )*) => {
            $(
            impl$(<$($typed_generics)*>)? Typed for $ty {
                fn repr() -> TypeRepr { $repr }
            }

            impl$(<$($cons_generics)*>)? TypedConstruct for $ty {
                fn cons_order() -> &'static [TypeKind] { &$cons_order }
                fn err_string() -> &'static str { $err_string }

                $($cons_tt)*
            }

            impl$(<$($decon_generics)*>)? TypedDeconstruct for $ty {
                fn type_kind(&self) -> TypeKind { $kind }

                $($decon_tt)*
            }
            )*
        };
    }

    impl_core! {
        impl for Value<'static> {
            @repr = TypeRepr::Any;
            @kind = TypeKind::Any;
            @cons = [TypeKind::Any];
            @err = "expected any value";
            @cons_fns = {
                fn from_any(any: Value<'static>) -> Result<Self> { Ok(any) }
            };
            @decon_fns = {
                fn clone_into_value(&self) -> Value<'static> { self.clone() }
            };
        }

        impl for BigInt {
            @repr = TypeRepr::Int;
            @kind = TypeKind::Int;
            @cons = [TypeKind::Int];
            @err = "expected an integer";
            @cons_fns = {
                fn from_int(int: BigInt) -> Result<Self> { Ok(int) }
            };
            @decon_fns = {
                fn clone_into_value(&self) -> Value<'static> { Value::new(self.clone()) }
                fn as_int(&self) -> BigInt { self.clone() }
            };
        }

        impl for bool {
            @repr = TypeRepr::Bool;
            @kind = TypeKind::Bool;
            @cons = [TypeKind::Bool];
            @err = "expected a boolean";
            @cons_fns = {
                fn from_bool(b: bool) -> Result<Self> { Ok(b) }
            };
            @decon_fns = {
                fn clone_into_value(&self) -> Value<'static> { Value::new(*self) }
                fn as_bool(&self) -> bool { *self }
            };
        }

        impl for String {
            @repr = TypeRepr::String;
            @kind = TypeKind::String;
            @cons = [TypeKind::String];
            @err = "expected a string";
            @cons_fns = {
                fn from_string(s: String) -> Result<Self> { Ok(s) }
            };
            @decon_fns = {
                fn clone_into_value(&self) -> Value<'static> { Value::new(self.clone()) }
                fn as_string(&self) -> String { self.clone() }
            };
        }

        impl for () {
            @repr = TypeRepr::Unit;
            @kind = TypeKind::Unit;
            @cons = [TypeKind::Unit, TypeKind::Struct, TypeKind::Array];
            @err = "expected a unit value, empty struct, or empty array";
            @cons_fns = {
                fn from_unit() -> Self { () }
                fn from_struct(fields: HashMap<String, Value>) -> Result<Self> {
                    match fields.is_empty() {
                        true => Ok(()),
                        false => Err(Error::from_str("expected a struct with no fields")),
                    }
                }
                fn from_array(array: Vec<Value>) -> Result<Self> {
                    match array.is_empty() {
                        true => Ok(()),
                        false => Err(Error::from_str("expected an array with no elements")),
                    }
                }
            };
            @decon_fns = {
                fn clone_into_value(&self) -> Value<'static> { Value::new(()) }
            };
        }

        // impl[<T: Clone + Typed, const N: usize>] for [T; N] {
        //     @repr = TypeKind::Array;
        //     @cons = [TypeKind::Array];
        //     @err = "expected an array of length (TODO)";
        //     @cons_fns = {
        //         fn from_array(array: Vec<Value>) -> Result<Self> {
        //             array.iter()
        //                 .map(Value::convert)
        //                 .collect::<Result<Self>>()?
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
        ($($int_ty:ty: $from:ident => $into:ident,)*) => {
            impl_core! {
                $(
                impl for $int_ty {
                    @repr = TypeRepr::Int;
                    @kind = TypeKind::Int;
                    @cons = [TypeKind::Int];
                    @err = concat!("expected ", stringify!($int_ty));
                    @cons_fns = {
                        fn from_int(int: BigInt) -> Result<Self> {
                            use num::cast::ToPrimitive;

                            int.$into().ok_or_else(|| {
                                Error::from_str(format!("integer {} cannot fit within {}", int, stringify!($int_ty)))
                            })
                        }
                    };
                    @decon_fns = {
                        fn clone_into_value(&self) -> Value<'static> { Value::new(*self) }
                        fn as_int(&self) -> BigInt {
                            use num::cast::FromPrimitive;

                            FromPrimitive::$from(*self).unwrap()
                        }
                    };
                }
                )*
            }
        }
    }

    impl_int! {
        u8: from_u8 => to_u8,
        u16: from_u16 => to_u16,
        u32: from_u32 => to_u32,
        u64: from_u64 => to_u64,
        u128: from_u128 => to_u128,
        usize: from_usize => to_usize,
        i8: from_i8 => to_i8,
        i16: from_i16 => to_i16,
        i32: from_i32 => to_i32,
        i64: from_i64 => to_i64,
        i128: from_i128 => to_i128,
        isize: from_isize => to_isize,
    }

    ////////////////////////////////////////////////
    // Implementations on tuples of size 2,3,..15 //
    ////////////////////////////////////////////////

    // Produces implementations for tuples of size >= 2. Tuples of size 1 are treated as equivalent to
    // the inner type, so we ignore them. Tuples of size 0 are the "unit"; we exclude them.
    macro_rules! impl_tuple {
        ($($names:ident $indexes:literal,)*) => {
            impl_tuple!(@do_impl $($names $indexes)*);
        };

        // Don't do anything for tuples of length 1 and 2
        (@do_impl $($name:ident $index:literal)?) => {};

        // Helper functionality to extract all but the last pair of name + index
        (@init $($name:ident $index:literal)* @mark $l_name:ident $l_index:literal) => {
            impl_tuple!(@do_impl $($name $index)*);
        };
        (@init $($hn:ident $hi:literal)* @mark $n:ident $i:literal $($tn:ident $ti:literal)+) => {
            impl_tuple!(@init $($hn $hi)* $n $i @mark $($tn $ti)*);
        };

        (@count) => {{ 0 }};
        (@count $head:ident $($tail:ident)*) => {{ 1 + impl_tuple!(@count $($tail)*) }};

        // The actual implementations for tuples of various sizes:
        (@do_impl $($name:ident $index:literal)*) => {
            impl_tuple!(@init @mark $($name $index)*);

            impl_core! {
                impl[
                    ($($name: 'static + Send + Sync + Clone + Typed),*)
                    ($($name: 'static + TypedConstruct),*)
                    ($($name: 'static + Send + Sync + Clone + TypedDeconstruct),*)
                ] for ($($name,)*) {
                    @repr = TypeRepr::Tuple(vec![ $( $name::repr(), )* ]);
                    @kind = TypeKind::Array;
                    @cons = [TypeKind::Array];
                    @err = "expected tuple (as array)";
                    @cons_fns = {
                        #[allow(non_snake_case)]
                        fn from_array(array: Vec<Value>) -> Result<Self> {
                            match array.as_slice() {
                                [$($name,)*] => Ok(($(
                                    $name.convert::<$name>()
                                        .map_err(|e| e.context($index.to_owned()))?,
                                )*)),
                                vs => Err(Error::from_str(format!(
                                    "expected tuple with {} elements, found {}",
                                    impl_tuple!(@count $($name)*),
                                    vs.len(),
                                ))),
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
    }

    // Note that evaluating this macro requires an increased recursion limit.
    //   @def "dispatch::impl_tuple!" v0
    impl_tuple! {
        A ".0", B ".1", C ".2", D ".3", E ".4", F ".5", G ".6", H ".7",
        I ".8", J ".9", K ".10", L ".11", M ".12", N ".13", O ".14",
    }

    ////////////////////////////
    // Implementation on (T,) //
    ////////////////////////////

    impl<T: Typed> Typed for (T,)
    where
        Self: TypedConstruct + TypedDeconstruct,
    {
        fn repr() -> TypeRepr {
            T::repr()
        }
    }

    #[rustfmt::skip]
    impl<T: TypedConstruct> TypedConstruct for (T,) {
        fn cons_order() -> &'static [TypeKind] { T::cons_order() }
        fn err_string() -> &'static str { T::err_string() }

        fn from_any(any: Value<'static>) -> Result<Self> {
            Ok( (T::from_any(any)?,) )
        }

        fn from_int(int: BigInt) -> Result<Self> {
            Ok( (T::from_int(int)?,) )
        }

        fn from_bool(b: bool) -> Result<Self> {
            Ok( (T::from_bool(b)?,) )
        }

        fn from_string(s: String) -> Result<Self> {
            Ok( (T::from_string(s)?,) )
        }

        fn from_unit() -> Self {
            (T::from_unit(),)
        }

        fn from_struct(fields: HashMap<String, Value>) -> Result<Self> {
            Ok( (T::from_struct(fields)?,) )
        }

        fn from_array(array: Vec<Value>) -> Result<Self> {
            Ok( (T::from_array(array)?,) )
        }
    }

    #[rustfmt::skip]
    impl<T: TypedDeconstruct> TypedDeconstruct for (T,) {
        fn type_kind(&self) -> TypeKind { self.0.type_kind() }
        fn clone_into_value(&self) -> Value<'static> { self.0.clone_into_value() }

        fn as_int(&self) -> BigInt { self.0.as_int() }
        fn as_bool(&self) -> bool { self.0.as_bool() }
        fn as_string(&self) -> String { self.0.as_string() }
        fn as_struct(&self) -> HashMap<String, Value> { self.0.as_struct() }
        fn as_array(&self) -> Vec<Value> { self.0.as_array() }
    }
}

// All of the `Typed` implementations on non-primitive standard library types
mod std_impls {
    use super::*;

    use crate::macros::manual_derive_typed;
    use std::marker::PhantomData;
    // re-import `Result` because we're using super::*
    use std::result::Result;

    manual_derive_typed! {
        enum Result<T, E> {
            Ok(T),
            Err(E),
        }
    }

    manual_derive_typed! {
        enum Option<T> {
            Some(T),
            None,
        }
    }

    manual_derive_typed! {
        struct PhantomData<T>;
    }

    ///////////////////////////////
    // Implementation for Vec<T> //
    ///////////////////////////////

    impl<T: Typed> Typed for Vec<T>
    where
        Self: TypedConstruct + TypedDeconstruct,
    {
        fn repr() -> TypeRepr {
            TypeRepr::Array(Box::new(T::repr()))
        }
    }

    impl<T: 'static + TypedConstruct> TypedConstruct for Vec<T> {
        fn cons_order() -> &'static [TypeKind] {
            &[TypeKind::Array]
        }
        fn err_string() -> &'static str {
            "expected an array"
        }
        fn from_array(array: Vec<Value>) -> super::Result<Self> {
            array
                .into_iter()
                .enumerate()
                .map(|(i, v)| v.convert().map_err(|e| e.context(format!("[{}]", i))))
                .collect()
        }
    }

    impl<T: 'static + Send + Sync + Clone + TypedDeconstruct> TypedDeconstruct for Vec<T> {
        fn type_kind(&self) -> TypeKind {
            TypeKind::Array
        }
        fn clone_into_value(&self) -> Value<'static> {
            Value::new(self.clone())
        }
        fn as_array(&self) -> Vec<Value> {
            self.iter().map(Value::from_ref).collect()
        }
    }
}

// Implementations of `Typed` for external types -- e.g. Uuid
#[rustfmt::skip]
mod extern_impls {
    use super::*;
    use uuid::Uuid;

    impl Typed for Uuid {
        fn repr() -> TypeRepr { TypeRepr::String }
    }

    impl TypedConstruct for Uuid {
        fn cons_order() -> &'static [TypeKind] { &[TypeKind::String] }
        fn err_string() -> &'static str { "expected a UUID, as a string" }

        fn from_string(s: String) -> Result<Self> {
            Uuid::parse_str(&s).map_err(|e| Error::from_str(e.to_string()))
        }
    }

    impl TypedDeconstruct for Uuid {
        fn type_kind(&self) -> TypeKind { TypeKind::String }
        fn clone_into_value(&self) -> Value<'static> { Value::new(*self) }

        fn as_string(&self) -> String {
            self.to_simple().to_string()
        }
    }
}
