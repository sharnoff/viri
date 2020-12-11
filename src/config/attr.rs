//! Utilities for handling attributes of objects
//
// TODO-DOC - this module needs a lot of documentation to explain what's going on

use super::Type;
use crate::any::{Any, BoxedAny, TypeId};
use crate::macros::{async_fn, async_method, init, AttrType};
use arc_swap::ArcSwapOption;
use lazy_static::lazy_static;
use serde::{Deserialize, Serialize, Serializer};
use std::collections::HashMap;
use std::convert::TryFrom;
use std::sync::Arc;

init! {
    inventory::collect!(AttributeDefinition);
    inventory::collect!(AttributeImplementation);

    let attrs_by_value = inventory::iter::<AttributeDefinition>()
        .map(|def| (def.value, def))
        .collect();

    let attrs_by_name = inventory::iter::<AttributeDefinition>()
        .map(|def| (def.name, def))
        .collect();

    let implementors = inventory::iter::<AttributeImplementation>()
        .map(|def| ((def.implementor, def.attr), def.func))
        .collect();

    REGISTRY.store(Some(Arc::new(Registry {
        attrs_by_value,
        attrs_by_name,
        implementors,
    })));
}

/// (*Internal*) An abbreviation to represent the generated functions that provide attributes
///
/// This is public so that it can be used from [`AttributeImplementation::new`], which exposes it.
///
/// ```
/// // Note: the signature is actually more like this:
/// type AttrFunction = async fn(&(dyn Any + Send + Sync)) -> BoxedAny;
/// ```
// @def AttrFunction-typedef v0
pub type AttrFunction = async_fn![fn(&(dyn Any + Send + Sync)) -> BoxedAny];

// The internal registry of attributes, their names, and the functions that produce them
struct Registry {
    attrs_by_value: HashMap<Attribute, &'static AttributeDefinition>,
    attrs_by_name: HashMap<&'static str, &'static AttributeDefinition>,
    implementors: HashMap<(TypeId, Attribute), AttrFunction>,
}

lazy_static! {
    /// The internal registry of named functions
    static ref REGISTRY: ArcSwapOption<Registry> = ArcSwapOption::empty();
}

/// The primary export of this module
///
/// Here you can find a list of all defined attributes as the associated constants for this type.
/// For more information on `Attribute`s and how to use them, refer to the
/// [module-level documentation](self).
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Deserialize)]
#[serde(try_from = "&str")]
pub struct Attribute(u16);

impl Attribute {
    /// Produces an `Attribute` from the provided value
    ///
    /// This is only provided for use by the macros that generate all of the attributes. It's
    /// specifically used by [`attrs`](crate::macros::attrs).
    #[doc(hidden)]
    pub const fn from(v: u16) -> Attribute {
        Attribute(v)
    }

    /// Returns the [`Type`] of the attribute
    ///
    /// The `Type` returned here is effectively a dynamic (runtime) version of the [`AttrType`]
    /// macro.
    ///
    /// This function will panic if the `Attribute` is not a recognized constant - this shouldn't
    /// be an issue unless you're doing something really funky.
    pub fn value_type(&self) -> Type {
        self.definition().type_info
    }

    /// Returns the name of the attribute
    ///
    /// The name of an attribute is given by the name of the associated constant that produced it.
    /// Incidentally, this is exactly equal to the string produced from serializing the value (and
    /// hence the same string will deserialize into the attribute).
    pub fn name(&self) -> &'static str {
        self.definition().name
    }

    /// Returns the default value of the attribute
    pub fn default(&self) -> BoxedAny {
        (self.definition().get_default)()
    }

    // A helper function to produce the original definition of an attribute
    fn definition(&self) -> &'static AttributeDefinition {
        *(REGISTRY.load())
            .as_ref()
            .expect("`config::attr` has not been initialized")
            .attrs_by_value
            .get(self)
            .expect(&format!(
                "attribute {:?} is not a recognized constant",
                self
            ))
    }
}

/// (*Internal*) Information about an individual [`Attribute`]
///
/// This is used internally to handle (de-)serialization and retrieving the type of attributes by
/// value (i.e. those not known at compile-time).
pub struct AttributeDefinition {
    name: &'static str,
    value: Attribute,
    type_info: Type,
    get_default: fn() -> BoxedAny,
}

impl AttributeDefinition {
    /// Constructs a new `AttributeDefinition`
    ///
    /// Like the type itself, this function is only intended to be used by macros.
    pub fn new(
        name: &'static str,
        value: Attribute,
        type_info: Type,
        get_default: fn() -> BoxedAny,
    ) -> AttributeDefinition {
        AttributeDefinition {
            name,
            value,
            type_info,
            get_default,
        }
    }
}

/// (*Internal*) Information about how to compute an attribute for a type
///
/// This is used internally to handle dispatching for the [`GetAttr`] trait.
pub struct AttributeImplementation {
    implementor: TypeId,
    attr: Attribute,
    func: AttrFunction,
}

impl AttributeImplementation {
    /// Constructs a new `AttributeImplementation` from the provided pieces
    ///
    /// Like the type itself, this function is only intended to be used by macros.
    pub fn new(implementor: TypeId, attr: Attribute, func: AttrFunction) -> Self {
        AttributeImplementation {
            implementor,
            attr,
            func,
        }
    }
}

/// A universally-implemented way to retrieve the values of [`Attribute`s](Attribute)
///
/// The two methods provided here give both static and dynamic ways of getting the values of
/// attributes. These are [`get_attr`] and [`get_attr_any`], respectively.
///
/// While this trait has a blanket implementation for all `T`, its implementation relies on
/// [`GetAttrAny`], which must be implemented for any type that provides attributes. More
/// information on implementing [`GetAttrAny`] can be found in its documentation.
///
/// It is also important to know that this trait is not object safe because of the generics in
/// [`get_attr`].
///
/// This trait is not object safe because of the generics in [`get_attr`], but the [`GetAttrAny`]
/// trait is provided to
///
/// For more information about attributes, please refer to the [module-level documentation](self).
///
/// [`get_attr`]: Self::get_attr
/// [`get_attr_any`]: GetAttrAny::get_attr_any
pub trait GetAttr: GetAttrAny {
    /// Returns the value of an attribute provided by the given type
    #[async_method]
    #[allow(non_upper_case_globals)]
    async fn get_attr<const Attr: Attribute>(&self) -> Option<AttrType![Attr]>
    where
        AttrToken<Attr>: TypedAttr;
}

/// An object-safe subset of the [`GetAttr`] trait
///
/// This trait is the one responsible for the internal implementation, and so must be implemented
/// manually for all attribute providers. Please note that this is typically just connecting the
/// component pieces; it must be done manually because a blanket implementation would interfere
/// with types like `Box<dyn GetAttrAny>` (by using `Box<dyn GetAttrAny>` as the provider instead
/// of dispatching to the underlying object).
///
/// For more information on what this trait does, please refer to [`GetAttr`]
///
/// ## Example implementations
///
/// All implementations of this trait will fall into one of two categories: either directly
/// implementing on the type, or dispatching (as would be the case with `Box<dyn GetAttrAny>`).
/// We'll go through both types as examples.
///
/// Those that are implemented directly on the type an be done with the
/// [`impl_GetAttrAny`](crate::macros::impl_GetAttrAny) macro:
///
/// ```
/// struct Foo;
///
/// impl_GetAttrAny!(Foo);
/// ```
// @req impl_GetAttrAny-syntax v0
///
/// Which really just desugars to:
///
/// ```
/// // Implementing for a concrete type:
///
/// use crate::config::{attr, GetAttrAny};
/// use crate::macros::async_method;
///
/// struct Foo;
///
/// impl GetAttrAny for Foo {
///     #[async_method]
///     async fn get_attr_any(&self, attr: Attribute) -> Option<BoxedAny> {
///         // The implementation just goes to the provided `get_attr_any` function,
///         // which does all of the heavy lifting.
///         attr::get_attr_any(self, attr).await
///     }
/// }
/// ```
///
/// ```
/// // Implementing on a dynamic type:
///
/// use crate::config::GetAttrAny;
/// use std::ops::Deref;
///
/// trait Foo: GetAttrAny {}
///
/// impl GetAttrAny for Box<dyn Foo> {
///     #[async_method]
///     async fn get_attr_any(&self, attr: Attribute) -> Option<BoxedAny> {
///         (Box::deref(self) as impl GetAttrAny).get_attr_any(attr).await
///     }
/// }
/// ```
pub trait GetAttrAny {
    /// Retrieves the value of an attribute provided by this type, if it exists
    ///
    /// While this method may look complex, it is actually just a desugared version of:
    /// ```
    /// async fn get_attr_any(&self, attr: Attribute) -> Option<BoxedAny> { ... }
    /// ```
    /// The returned type is guaranteed to have a [`Type`] equal to [`attr.value_type()`].
    ///
    /// For a statically-guaranteed version (where the value of the attribute is known at
    /// compile-time), refer to [`get_attr`](GetAttr::get_attr).
    ///
    /// [`attr.value_type()`]: Attribute::value_type
    #[async_method]
    async fn get_attr_any(&self, attr: Attribute) -> Option<BoxedAny>;
}

impl<T: GetAttrAny + Send + Sync> GetAttr for T {
    #[async_method]
    #[allow(non_upper_case_globals)]
    async fn get_attr<const Attr: Attribute>(&self) -> Option<AttrType![Attr]>
    where
        AttrToken<Attr>: TypedAttr,
    {
        self.get_attr_any(Attr).await.map(BoxedAny::downcast)
    }
}

/// A helper function for implementing [`GetAttrAny`]
///
/// An example for how to use this function to implement [`GetAttrAny`] can be found in the trait's
/// documentation.
///
/// This function is essentially responsible for providing the actual implementation of the
/// expected behavior, using the values provided by the macros. All method calls to get attributes
/// ultimately boil down to a call to this function.
pub async fn get_attr_any<T: Any + Send + Sync>(this: &T, attr: Attribute) -> Option<BoxedAny> {
    let guard = REGISTRY.load();
    let func = guard
        .as_ref()
        .expect("`config::attr` has not been initialized")
        .implementors
        .get(&(TypeId::of::<T>(), attr))?;

    Some(func(this).await)
}

/// A type that successfully provides no attributes
///
/// This is ideal for things that are generic over [`GetAttr`] when there might not already be an
/// item to hand them.
pub struct Nothing;

impl GetAttrAny for Nothing {
    #[async_method]
    async fn get_attr_any(&self, _attr: Attribute) -> Option<BoxedAny> {
        None
    }
}

/// (*Internal*) An empty type to pass attribute types around using the [`TypedAttr`] trait
///
/// This is the only implementor of [`TypedAttr`] and we use it to store the expected types of
/// each attribute.
///
/// For more information, please refer to the [`TypedAttr`] trait and the [module-level
/// documentation](self).
#[allow(non_upper_case_globals, dead_code)]
pub struct AttrToken<const Attr: Attribute>;

/// (*Internal*) A marker trait for giving the types of an attribute
///
/// This trait is only implemented for const parameterizations of [`AttrToken`] so that we can
/// assign each attribute a type known at compile-time. In fact, this is the basis of the
/// [`AttrType`] macro:
///
/// ```ignore
/// AttrType![Attr]
/// ```
/// expands to
/// ```
/// <AttrToken<{ Attr }> as TypedAttr>::Type
/// ```
///
/// For more information on the internals, please refer to the [module-level documentation](self).
pub trait TypedAttr {
    type Type: Send + Sync;

    /// The default value of the attribute
    fn default_value() -> Self::Type;
}

///////////////////////////////////////////
// Serialize/Deserialize implementations //
///////////////////////////////////////////

impl Serialize for Attribute {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.name())
    }
}

impl TryFrom<&str> for Attribute {
    type Error = String;

    fn try_from(name: &str) -> Result<Self, String> {
        let guard = REGISTRY.load();
        let registry = guard
            .as_ref()
            .expect("cannot deserialize before `config::attr` has been initialized");

        match registry.attrs_by_name.get(name) {
            Some(attr_def) => Ok(attr_def.value),
            None => Err(format!("cannot find attribute with name '{}'", name)),
        }
    }
}
