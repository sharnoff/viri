//! Support for (de-)serializable user-defined functions
//
// TODO-DOC - this module needs a fair amount of documentation to explain how it works

use super::Type;
use crate::macros::{async_fn, init};
use arc_swap::ArcSwapOption;
use lazy_static::lazy_static;
use serde::{Deserialize, Serialize, Serializer};
use std::any::Any;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt::{self, Debug, Display, Formatter};
use std::marker::PhantomData;
use std::sync::Arc;

fn collect_funcs() -> HashMap<&'static str, &'static RegisteredFunction> {
    inventory::iter::<RegisteredFunction>()
        .map(|func| (func.name, func))
        .collect()
}

init! {
    // This isn't really required to be here, but it's nice to have everything in one place.
    inventory::collect!(RegisteredFunction);

    let map = collect_funcs();
    REGISTRY.store(Some(Arc::new(map)));
}

lazy_static! {
    /// The internal registry of named functions
    static ref REGISTRY: ArcSwapOption<HashMap<&'static str, &'static RegisteredFunction>>
        = {
            // When we're testing, the initializers don't get run -- in order to handle this, we
            // just do that ourselves.
            if cfg!(test) {
                ArcSwapOption::new(Some(Arc::new(collect_funcs())))
            } else {
                ArcSwapOption::empty()
            }
        };
}

/// (*Internal*) The type of the function pointer generated by the [`named`] attribute macro
///
/// ```
/// // Note: the signature is actually more like this:
/// type FnPtr = async fn(Vec<Box<dyn Any + Send + Sync>>) -> Box<dyn Any + Send + Sync>;
/// ```
///
/// This is primarily for internal use, and exists only as an abbreviation.
///
/// [`named`]: crate::macros::named
pub type FnPtr = async_fn![fn(Vec<Box<dyn Any + Send + Sync>>) -> Box<dyn Any + Send + Sync>];

/// (*Internal*) The inner representation of a named function
///
/// This type is only exposed so that the [`named`] attribute macro can reference it for
/// registering the function under the given name.
///
/// [`named`]: crate::macros::named
#[derive(Clone)]
pub struct RegisteredFunction {
    name: &'static str,
    input: Vec<Type>,
    output: Type,
    fn_ptr: FnPtr,
}

impl RegisteredFunction {
    /// Constructs a new `RegisteredFunction`
    ///
    /// This is only really for internal use by the [`named`] attribue macro.
    ///
    /// [`named`]: crate::macros::named
    pub fn new(name: &'static str, input: Vec<Type>, output: Type, fn_ptr: FnPtr) -> Self {
        RegisteredFunction {
            name,
            input,
            output,
            fn_ptr,
        }
    }
}

/// A user-provided function, accessible by name
///
/// This type is exposed entirely for the purposes of (de-)serializing for configs. Typically, user
/// code will not need to manipulate these directly, but will instead go through configuration
/// files that serialize/deserialize these.
///
/// For creating a custom named function, please refer to the documentation for the [`named`]
/// attribute macro. For a general overview of named functions, see the
/// [module-level documentation](self).
///
/// [`named`]: crate::macros::named
#[derive(Copy, Clone, Debug, Deserialize)]
#[serde(try_from = "&str")]
pub struct NamedFunction(&'static RegisteredFunction);

impl NamedFunction {
    /// Returns an error if the provided input types don't match what's expected by this function
    pub fn correct_input_types<Iter>(&self, input_types: Iter) -> Result<(), BadInput>
    where
        Iter: IntoIterator<Item = Type>,
        Iter::IntoIter: ExactSizeIterator,
    {
        let input_types = input_types.into_iter();

        if input_types.len() != self.0.input.len() {
            return Err(BadInput::IncorrectNumberOfArgs {
                given: input_types.len(),
                func: self.0,
            });
        }

        for (idx, ty) in input_types.enumerate() {
            if ty != self.0.input[idx] {
                return Err(BadInput::TypeMismatch {
                    idx,
                    given: ty,
                    func: self.0,
                });
            }
        }

        Ok(())
    }

    /// Returns the name given to the function
    pub fn name(&self) -> &'static str {
        self.0.name
    }

    /// Returns the output type of the function
    pub fn output_type(&self) -> Type {
        self.0.output
    }

    /// Evaluates the function with the given inputs
    ///
    /// If the input types do not match what is expected, this function will panic. Input types
    /// should be validated before calling this function with [`correct_input_types`].
    ///
    /// [`correct_input_types`]: Self::correct_input_types
    pub async fn apply(
        &self,
        inputs: Vec<Box<dyn Any + Send + Sync>>,
    ) -> Box<dyn Any + Send + Sync> {
        let output = (self.0.fn_ptr)(inputs).await;
        debug_assert_eq!((&*output).type_id(), self.0.output.id());

        output
    }
}

/// An unexpected set of inputs to a function
///
/// This is generated by the [`correct_input_types`] method on [`NamedFunction`].
///
/// [`correct_input_types`]: NamedFunction::correct_input_types
#[derive(Copy, Clone, Debug)]
pub enum BadInput {
    IncorrectNumberOfArgs {
        given: usize,
        func: &'static RegisteredFunction,
    },
    TypeMismatch {
        /// The index of the argument that had a mismatched type
        idx: usize,
        given: Type,
        func: &'static RegisteredFunction,
    },
}

/// A [`NamedFunction`] with guarantees about the input/output types
///
/// This allows building configurations with [`NamedFunction`]s where the input and output types of
/// that function are known.
///
/// Usage of this type is typically much more ergonomic than [`NamedFunction`]; the version of the
/// `apply` method given here is statically-typed.
///
/// ## Example
///
/// Suppose we need to use a predicate on integers - i.e. a function from `i32`s to `bool`s. This
/// might be represented as:
/// ```
/// #[derive(serde::Deserialize)]
/// struct Foo {
///     predicate: TypedNamedFunction<dyn Fn(i32) -> bool>,
/// }
/// ```
/// In order to give a concrete type, the type argument for a `TypedNamedFunction` must be a
/// `dyn Fn(_) -> _` (with a variable number of arguments). The choice of `Fn` instead of `FnOnce`
/// or `FnMut` is purely stylistic; it makes no bearing on the actual ownership requirements to
/// execute the function.
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
#[serde(try_from = "NamedFunction")]
pub struct TypedNamedFunction<F: FuncType> {
    #[serde(flatten)]
    func: NamedFunction,
    #[serde(skip)]
    _marker: PhantomData<F>,
}

impl<F: FuncType> TypedNamedFunction<F> {
    /// The typed equivalent of [`NamedFunction::apply`]
    pub async fn apply(&self, inputs: F::Inputs) -> F::Output {
        let output = self.func.apply(F::inputs_to_dyn_vec(inputs)).await;
        *<Box<dyn Any + Send>>::downcast(output)
            .unwrap_or_else(|_| panic!("unexpected output type from typed named function"))
    }
}

////////////////////
// trait FuncType //
////////////////////

/// A marker trait for `dyn Fn(X0,X1,..XN) -> Y`
///
/// This trait is only used in the bound on [`TypedNamedFunction`], and implementations are
/// auto-generated for functions with up to 12 arguments. This trait is not intended for use
/// outside of the implementation of [`TypedNamedFunction`].
pub trait FuncType {
    /// The types expected as input to this function
    ///
    /// Ideally, this would have directly been a constant or static value, but limitations in the
    /// type system prevent this from happening. We *also* can't simply shift the location of a
    /// static value to return a reference here (like `&'static [Type]`), so we have to resort to
    /// constructing the list at "runtime" (primarily just allocation) instead.
    ///
    /// This isn't ideal, but it's a small, internal trait - it shouldn't really matter.
    fn input_types() -> Vec<Type>;

    /// The representation of the input types as a tuple, *within* the type system
    type Inputs: Any;

    /// The type of the returned value from this function
    const OUTPUT_TYPE: Type = Type::new::<Self::Output>();

    /// The representation of the output type of the function, within the type system
    type Output: Any;

    /// A helper function to convert to a list of inputs that can be supplied to
    /// [`NamedFunction::apply`]
    fn inputs_to_dyn_vec(inp: Self::Inputs) -> Vec<Box<dyn Any + Send + Sync>>;
}

macro_rules! impl_FuncType {
    ($out:ident; $head:ident $idx:tt $(, $tail:ident $tail_idx:tt)*) => {
        impl<$out: Any, $head $(, $tail)*> FuncType for dyn Fn($head $(, $tail)*) -> $out
        where
            $head: Any + Send + Sync,
            $($tail: Any + Send + Sync,)*
        {
            fn input_types() -> Vec<Type> {
                vec![Type::new::<$head>() $(, Type::new::<$tail>() )*]
            }

            type Inputs = ($head, $($tail,)*);

            type Output = $out;

            fn inputs_to_dyn_vec(inputs: Self::Inputs) -> Vec<Box<dyn Any + Send + Sync>> {
                let mut inps = <Vec<Box<dyn Any + Send + Sync>>>::new();
                inps.push(Box::new(inputs.$idx));
                $(inps.push(Box::new(inputs.$tail_idx));)*
                inps.reverse();
                inps
            }
        }
    };
    ($out:ident;) => {
        impl<$out: Any> FuncType for dyn Fn($head $(, $tail)*) -> $out {
            fn input_types() -> Vec<Type> { Vec::new() }

            type Inputs = ();

            type Output = $out;

            fn inputs_to_dyn_vec(inp: ()) -> Vec<Box<dyn Any + Send + Sync>> {
                Vec::new()
            }
        }
    };
}

impl_FuncType!(Z; L 11, K 10, J 9, I 8, H 7, G 6, F 5, E 4, D 3, C 2, B 1, A 0);

impl<F: FuncType> From<TypedNamedFunction<F>> for NamedFunction {
    fn from(typed: TypedNamedFunction<F>) -> NamedFunction {
        typed.func
    }
}

impl<F: FuncType> TryFrom<NamedFunction> for TypedNamedFunction<F> {
    type Error = String;

    fn try_from(func: NamedFunction) -> Result<Self, String> {
        let input_types = F::input_types();

        // First, check the number of inputs:
        if input_types.len() != func.0.input.len() {
            return Err(format!(
                "function {:?} has wrong number of arguments; expected `{}` but has `{}`",
                func.name(),
                input_types.len(),
                func.0.input.len(),
            ));
        }

        // Then, check each input individually:
        for (idx, ty) in input_types.into_iter().enumerate() {
            if func.0.input[idx] != ty {
                return Err(format!(
                    "type mismatch: argument {} of function '{}' is required to be `{}`, but is actually `{}`",
                    idx,
                    func.name(),
                    func.0.input[idx].name(),
                    ty.name(),
                ));
            }
        }

        // And finally, check the output type:
        if func.output_type() != F::OUTPUT_TYPE {
            return Err(format!(
                "type mismatch: output function '{}' is required to be `{}`, but is actually `{}`",
                func.name(),
                F::OUTPUT_TYPE.name(),
                func.output_type().name(),
            ));
        }

        Ok(TypedNamedFunction {
            func,
            _marker: PhantomData,
        })
    }
}

///////////////////////////////////
// Debug/Display implementations //
///////////////////////////////////

impl Debug for RegisteredFunction {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let fn_ptr_addr = self.fn_ptr as *const u8 as usize;

        f.debug_struct("RegisteredFunction")
            .field("name", &self.name)
            .field(
                "input",
                &(self.input).iter().map(Type::name).collect::<Vec<_>>(),
            )
            .field("output", &self.output.name())
            .field("fn_ptr", &format!("<fn pointer: {:#x}>", fn_ptr_addr))
            .finish()
    }
}

impl Display for BadInput {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use BadInput::{IncorrectNumberOfArgs, TypeMismatch};

        match self {
            IncorrectNumberOfArgs { given, func } => write!(
                f,
                "incorrect number of arguments to function '{}': expected {}, found {}",
                func.name,
                func.input.len(),
                given,
            ),
            TypeMismatch { idx, given, func } => write!(
                f,
                "type mismatch for function '{}' on argument {}: expected `{}`, found `{}`",
                func.name,
                idx,
                func.input[*idx].name(),
                given.name(),
            ),
        }
    }
}

impl std::error::Error for BadInput {}

////////////////////////////////////////////
// (De-)Serialization for `NamedFunction` //
////////////////////////////////////////////

impl Serialize for NamedFunction {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.0.name)
    }
}

impl TryFrom<&str> for NamedFunction {
    type Error = String;

    fn try_from(name: &str) -> Result<NamedFunction, String> {
        let guard = REGISTRY.load();
        let registry = guard
            .as_ref()
            .expect("cannot deserialize before `config::named_fn` has been initialized");

        match registry.get(name) {
            None => Err(format!("cannot find named function '{}'", name)),
            Some(func) => Ok(NamedFunction(*func)),
        }
    }
}
