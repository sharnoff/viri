//! Various macros for use across the editor
//!
//! Broadly speaking, there are a few different categories of macros that you may be interested in:
//!  * [Configuration] - [`config`]
//!  * Initialization - [`init`], [`initialize`], [`require_initialized`]
//!  * [Attributes] - [`attrs`], [`provide_attrs`], [`AttrType`], [`impl_GetAttrAny`]
//!  * [Named functions] - [`named`]
//!  * [Dynamic (de-)serialization] - [`SerdeDynClone`], [`register_DynClone`]
//!  * Async functions - [`async_method`], [`async_fn`]
//!  * Miscellaneous pieces - [`id`]
//!
//! This module works in conjunction with the `viri-macros` crate, which provides some of the
//! backing procedural macros necessary for this to work. Generally, `viri-macros` is treated as
//! the backend workhorse, and this module just re-exports those with documentation that isn't
//! duplicated into the original crate.
//!
//! [Configuration]: crate::config
//! [Attributes]: crate::config::attr
//! [Named functions]: crate::config::named_fn
//! [Dynamic (de-)serialization]: crate::any::deserialize_dyn_clone

/// Produces a configuration struct with an associated implementation of [`Configurable`]
///
/// This macro may be invoked in either of two modes: with or without a leading `static <IDENT>`,
/// which indicates whether to treat the configuration struct as a component of another *or* as a
/// top-level coniguration with a related static item to store the value in.
///
/// ## Example
///
/// The typical usage that we might expect can be found in [`crate::config`]:
// @req main-config v1
/// ```
/// config! {
///     // Define the name of the static item storing the configuration
///     // This piece is optional; omitting it allows the config to be used as *part* of another,
///     // via the `use` statements below:
///     static ROOT_CONFIG;
///
///     // The main configuration name, paired with the name of the builder used to construct it
///     pub struct MainConfig (MainConfigBuilder) {
///         // Sub-configurations can be included with a `use` declaration:
///         #[flatten]
///         // the #[flatten] attribute allows us to specify that the fields of this configuration
///         // should be merged for deserialization into the builder. This isn't always used, but
///         // in the case of the main configuration, it's nice to have most things collected.
///         pub use crate::view::Config as view_config,
///
///         #[flatten]
///         pub use crate::container::Config as container_config,
///
///         // Each field is given a value to indicate what it defaults to if not provided
///         #[builder(Option<String>)]
///         // Because the default field type used for the builder is `Option<T>`, the `#[builder]`
///         // attribute allows us to specify the type of the builder's field. There are more
///         // options available here as well (see below).
///         //
///         // Additionally, because we're manually specifying the builder, we don't need to give a
///         // default value - that's taken from the implementation of `Default` for the builder.
///         // This is all given by the `FromBuilder` trait.
///         #[validate_with(|s: &Option<String>| match s.as_ref().map(|s| s.as_str()) {
///             Some("") => Err("`log_file` path must be non-empty"),
///             _ => Ok(()),
///         })]
///         // We can *also* have field validation! Validation is done with functions that return a
///         // `Result<(), String>`, but can be specified with expressions, as is shown here.
///         // Validation isn't just restricted to fields - we could have used it for the
///         // sub-configs we included above.
///         pub log_file: Option<String>,
///         pub log_level: LevelFilter = LevelFilter::Warn,
///     }
/// }
/// ```
///
/// As mentioned in a comment above, there is actually another way to use the `#[builder]` field
/// attribute - if the given type does not implement [`FromBuilder`](crate::config::FromBuilder)
/// for the builder, the conversion functions can be specified manually. This would look somehting
/// like:
/// ```ignore
/// config! {
///     // we'll just elide everything else we don't care about
///     struct Config (Builder) {
///         #[builder(Option<String> => std::convert::identity, Clone::clone)]
///         //                        1 ^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^ 2
///         // 1: This function gives a way to produce the configuration's type from the builder
///         // 2: And this produces the builder from a reference to the config
///         log_file: Option<String>,
///     }
/// }
/// ```
///
/// [`Configurable`]: crate::config::Configurable
pub use viri_macros::config;

/// A marker trait for modules that are initialized at some point
///
/// With each `init!` macro expansion, we insert a dummy type that's expected to have `Initialized`
/// implemented on it. If not, that causes a nice compiler error, using
/// `#[rustc_on_unimplemented]`.
#[rustc_on_unimplemented(
    message = "Initializer is never called",
    label = "generated by this macro"
)]
pub trait Initialized {
    type This;
}

/// Produces an intializer function for the current module
///
/// This macro just takes a block expression as input, with a small modification added to it: Each
/// statement on the *top level* that's of the form `mod <name>` will intead be transformed to run
/// the initializer for that module.
///
/// For a similar macro that does *not* wrap this in a function, see [`initialize`].
///
/// The [`require_initialized`] macro is also available for asserting that a module has been
/// initialized.
///
/// ## Example
///
/// To use an existing piece of code as an example, the [`runtime`](crate::runtime) module contains
/// the following snippet:
/// ```no_run
// @req runtime::init v0
/// init! {
///    lazy_static::initialize(&EXECUTOR);
///
///    mod panic; // equivalent to `initialize! { mod panic; }`
/// }
/// ```
/// So for the runtime, the `init` macro is used to ensure that the values
pub use viri_macros::init;

/// A version of the [`init`] macro that instead produces an expression
///
/// This is really only intended to be used as the entrypoint for initialization, in `main`. It's
/// *probably* not what you're looking for, but it's here nonetheless.
pub use viri_macros::initialize;

/// An assertion that a certain module has been initialized
///
/// This is mostly used in runtime-related functions (e.g. inside logger utilities) to ensure that
/// they aren't being called before they should be.
///
/// Typical usage might look like:
/// ```no_run
/// require_initialized!(crate::runtime);
/// ```
pub use viri_macros::require_initialized;

/// Produces the type corresponding to an attribute
///
/// The attribute should be given by a single identifier (note: not a path). This macro is
/// typically called with square-brackets, which allows snippets that look like:
///
/// ```ignore
/// fn foo() -> AttrType![MyFoo] {
///     /* magic! */
/// }
/// ```
///
/// At the technical level, this macro just expands to the value of [`TypedAttr::Type`] implemented
/// on [`AttrToken`].
///
/// An overview of how attributes work can be found in the [dedicated submodule]. For the other
/// attribute-related macros, see [`attrs`] and [`provide_attrs`].
///
/// [`TypedAttr::Type`]: crate::config::attr::TypedAttr
/// [`AttrToken`]: crate::config::attr::AttrToken
/// [dedicated submodule]: crate::config::attr
pub use viri_macros::attr_type as AttrType;

/// Defines a new set of attributes
///
/// The documentation here is split into two pieces. [Usage](#usage) is meant to provide a
/// quick-start guide to using this macro, and [Syntax](#syntax) (and beyond) is intended to give a
/// full explanation of the code that's generated by this macro.
///
/// ## Usage
///
/// Standard usage of this macro will be to define an attribute (maybe with some documentation) and
/// its type:
///
/// ```
/// # use super::attrs;
/// attrs! {
///     /// A custom attribute!
///     pub MyFoo: String,
/// }
///
/// ```
///
/// That's it - you're done! This attribute can now be used like all others through the [`GetAttr`]
/// trait:
/// ```
/// let f = Foo::new();
/// println!("{:?}", f.get_attr::<{Attribute::MyFoo}>());
/// ```
///
/// [`GetAttr`]: crate::config::attr::GetAttr
///
/// ## Syntax
///
/// To help explain what this macro does, we'll have a brief look at the syntax first. If this
/// macro were written as a declarative macro, its signature might look something like:
/// ```
/// macro_rules! attrs {
///     ($(
///         $(#[$attrs:meta])*
///         $vis:vis $name:ident: $ty:ty = $default_value:expr,
///     )*) => { /* magic! */ }
/// }
/// ```
///
/// For each triple above, we'd produce attribute definitions that look something like:
/// ```ignore
/// // The global constant in `Attribute`
/// impl Attribute {
///     $(#[$attrs:meta])* // <- forwarding doc comments
///     $vis const $name: $ty = /* auto-incremented, unique value */;
/// }
///
/// // and then the implementation of `TypedAttr`:
/// impl TypedAttr for AttrToken<{Attribute::$name}> {
///     type Type = $ty;
///
///     fn default_value() -> Self::Type {
///         $default_value
///     }
/// }
/// ```
///
/// An overview of how attributes work can be found in the [dedicated submodule]. For the other
/// attribute-related macros, see [`AttrType`], and [`provide_attrs`].
///
/// [dedicated submodule]: crate::config::attr
pub use viri_macros::new_attrs as attrs;

/// Registers the implementations for providing the value of attributes for a type
///
/// Typical usage of this macro looks something like:
/// ```
/// provide_attrs! {
///     MyType => {
///         FooAttr => self.foo.clone(),
///         BarAttr => self.get_bar(),
///     }
/// }
/// ```
///
/// where each inner right-hand side of the arrow gives the expression to calculate the attribute
/// on the left-hand side. In other words, if we have:
/// ```
/// provide_attrs! {
///     Foo => {
///         Bar => self.bar(),
///     }
/// }
/// ```
/// Then, the following two snippets will be equivalent:
/// ```
/// // First version: constructing it manually
/// let f = Foo::new();
/// let b = f.bar();
///
/// // Second version: retrieving the value of the attribute
/// let f = Foo::new();
/// let b = f.get_attr::<Attribute::Bar>().unwrap();
/// ```
///
/// ## Syntax and Semantics
///
/// If this macro were written as a declarative macro, its signature might look something like:
/// ```
/// macro_rules! provide_attrs {
///     ($base_type:ty => {
///         $( $attr_name:ident => $value:expr, )*
///     }) => { /* magic! */ }
/// }
/// ```
///
/// A key piece of information to know is that the expressions above (`$value`) are always placed
/// into an `async` block, and so async/await syntax is fully available.
///
/// Common pain points may be either of:
/// * Not returning an `Option<..>`
/// * Double implementations for the same type
///
/// An overview of how attributes work can be found in the [dedicated submodule]. For the other
/// attribute-related macros, see [`attrs`] and [`AttrType`].
///
/// [dedicated submodule]: crate::config::attr
pub use viri_macros::provide_attrs;

/// Provides a basic implementation of [`GetAttrAny`](crate::config::GetAttrAny) for a type
///
/// This macro is pretty simple - example usage might look like:
/// ```
/// struct Foo;
///
/// impl_GetAttrAny!(Foo);
/// ```
// @def impl_GetAttrAny-syntax v0
///
/// Which essentially desugars to:
/// ```
/// impl crate::config::GetAttrAny for #ty {
///     #[async_method]
///     async fn get_attr_any(&self, attr: Attribute) -> Option<BoxedAny> {
///         crate::config::attr::get_attr_any(self, attr).await
///     }
/// }
/// ```
/// For more on attributes, please refer to the [dedicated submodule].
///
/// [dedicated submodule]: crate::config::attr
pub use viri_macros::impl_get_attr_any as impl_GetAttrAny;

/// Allows a function to be used as a [`NamedFunction`]
///
/// ```
/// use crate::macros::named;
///
/// #[named("my-special-foo")]
/// fn foo(x: i32) -> u32 {
///     x.abs() as u32
/// }
/// ```
///
/// In the above example, naming the function `"my-special-foo"` allows deserializing that string
/// as a [`NamedFunction`] representing the locally-defined `foo`. For more information, please
/// refer to the [module-level documentation] about named functions.
///
/// This attribute macro can be applied to any "sensible" function - a key (necessary) restriction
/// is that it is not allowed for functions that take generics as input.
///
/// Additionally, this macro works with `async` functions! Because named function evaluation
/// internally uses async, if the provided function isn't already marked with `async`, the produced
/// wrapper function will be.
///
/// [`NamedFunction`]: crate::config::named_fn::NamedFunction
/// [module-level documentation]: crate::config::named_fn
pub use viri_macros::named;

/// A `#[derive]` macro to register a [`DynClone`] value for [dynamic deserialization] (and
/// serialization!)
///
/// Typical usage of this macro is simply to apply it to a value in order to make it
/// deserialization-compatible. For example:
///
/// ```
/// use crate::macros::SerdeDynClone;
///
/// #[derive(Clone, SerdeDynClone)]
/// //       ^^^^^ note that this implementation of `Clone` is required
/// //             for the implementation of `DynClone`
/// struct Foo {
///     bar: usize,
///     baz: String,
/// }
/// ```
///
/// This macro cannot be used on generic types; there isn't a way to collect all possible resulting
/// concrete types corresponding to a generic type. (It's actually worse - we can't even make a
/// blanket trait implementation to provide these implementations, because you can't use type
/// parameters from the implementation inside new items in the implementation, which is what
/// `inventory` creates.)
///
/// For more information, refer to the general introduction to dynamic deserialization in
/// [`crate::any::deserialize_dyn_clone`].
///
/// [`DynClone`]: crate::any::DynClone
/// [dynamic deserialization]: crate::any::deserialize_dyn_clone
pub use viri_macros::SerdeDynClone;

/// Registers a list of types to be [dynamically deserializable]
///
/// This is fairly trivial to use - simply supply the list of types. These types *must* implement
/// `DynClone`, but there are no complications beyond that. For more information, refer to the
/// general introduction to dynamic deserialization in [`crate::any::deserialize_dyn_clone`].
///
/// ## Usage
///
/// ```
/// # #[derive(Clone)] struct Foo; #[derive(Clone)] struct Bar; #[derive(Clone)] struct Baz;
/// use crate::macro::register_DynClone;
///
/// // Assume we have types Foo, Bar, and Baz pre-defined
/// register_DynClone![Foo, Bar, Baz];
/// ```
///
/// [dynamically deserializable]: crate::any::deserialize_dyn_clone
pub use viri_macros::register_dyn_clone as register_DynClone;

/// A helper macro for converting a function pointer type to an `async` function type
///
/// Because the standard way of writing a function pointer that works for `async` functions
/// includes wrapping the output type with `Pin<Box<dyn Future<Output = T>>>`, this macro makes that
/// simpler.
///
/// ## Usage
///
/// Sample usage can be found in the definition of [`AttrFunction`]:
/// ```
// @req AttrFunction-typedef v0
/// pub type AttrFunction = async_fn![fn(&dyn Any) -> Box<dyn Any>];
/// ```
/// This expands (roughly) to:
/// ```
/// pub type AttrFunction = fn(Box<dyn Any>) -> Pin<Box<dyn Future<Output = Box<dyn Any>>>>;
/// ```
///
/// Cases with references as input (e.g. `fn(&T) -> S`) also correctly produce a trailing `+ '_` in
/// the return type to indicate this.
///
/// [`AttrFunction`]: crate::config::attr::AttrFunction
pub use viri_macros::async_fn;

/// Transforms an `async` function inside a trait to a generic, desugared version
///
/// Because `async` methods (or associated functions) aren't permitted in traits, this macro allows
/// writing one as would normally be expected, and expands the signature to produce a
/// `Pin<Box<dyn Future>>` instead.
///
/// ## Usage
///
/// Using this macro is as simple as adding the `#[async_method]` attribute to a function:
/// ```
/// // Inside a trait:
/// trait Foo {
///     #[async_method]
///     async fn foo(&self) -> i32;
/// }
///
/// // As a free-standing function:
/// #[async_method]
/// async fn bar(x: i32) {
///     println!("Hello from async! Given: {}", x);
/// }
/// ```
///
/// ## Troubleshooting - References
///
/// This macro is generally *pretty good*, but it isn't perfect. Sometimes you might run into
/// lifetime mismatch errors that seem like they shouldn't be there. The following code, for
/// example won't compile (assuming all definitions make sense):
/// ```
/// impl Foo {
///     #[async_method]
///     fn bar(&self, baz: &Baz) -> bool { ... }
/// }
/// ```
/// Fixing this can be done simply by making the lifetimes explicit:
/// ```
/// impl Foo {
///     #[async_method]
///     fn bar<'a>(&'a self, baz: &'a Baz) -> bool { ... }
/// }
/// ```
pub use viri_macros::async_method;

/// Convenience macro to produce a newtype'd `usize` for use as a unique identifier
///
/// This macro is one with syntax further away from the code that's actually generated. It is still
/// fairly simple though, so we'll just go through a couple examples:
///
/// For our first example, we'll create an id type `Bar` that indexes arrays of `Foo` - the
/// indexing is optional (as we'll see later), but
///
/// ```
/// use crate::macros::id;
///
/// struct Foo;
///
/// id!(struct Bar in [Foo]);
/// ```
/// produces...
/// ```
/// #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// struct Bar(usize);
///
/// // Note both Index and IndexMut:
/// impl std::ops::Index<Bar> for [Foo] { /* -- snip -- */ }
/// impl std::ops::IndexMut<Bar> for [Foo] { /* -- snip -- */ }
/// // (and equivalent implementations for Vec<Foo> as well)
/// ```
///
/// You can actually specify multiple such array types to allow indexing into, by separating them
/// with commas:
/// ```
/// id!(struct Bar in [Foo], [Baz]);
/// ```
///
/// We can also add visibility modifiers:
///
/// ```
/// id![pub(super) struct Bar];
/// ```
///
/// Specifying generic bounds on the arrays is done by a prefixed angle-brackets notation, exactly
/// how you'd find in the syntax for implementation:
///
/// ```
/// id![struct Bar in <T> [Foo<T>], <S: Debug> [Baz<S>]
/// ```
pub use viri_macros::id;
