//! Individual components that can be displayed inside the bottom bar

use super::{Condition, Context, TimeFormat};
use crate::config::{Attribute, GetAttr, NamedFunction, Type};
use crate::macros::async_method;
use crate::runtime;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::convert::TryFrom;
use std::fmt::{self, Debug, Formatter};
use std::ops::Deref;
use std::sync::Arc;

#[derive(Clone, Serialize, Deserialize)]
#[serde(try_from = "ComponentBuilder")]
pub(super) enum Component {
    Func(NamedFunction, Vec<Arc<Component>>),
    //                      ^^^^^^^^^^^^^^
    // We need to wrap these in `Arc` in order to create futures that are 'static :(
    // It's unfortunate, because they don't *actually* need to be 'static.
    Attr(Attribute),
    Time(TimeFormat),
    IfElse(Condition, Box<Component>, Box<Component>),
    ErrorMessage,
    Input,
}

#[derive(Deserialize)]
enum ComponentBuilder {
    Func(NamedFunction, Vec<ComponentBuilder>),
    Attr(Attribute),
    Time(TimeFormat),
    IfElse(Condition, Box<ComponentBuilder>, Box<ComponentBuilder>),
    ErrorMessage,
    Input,
}

impl Component {
    /// Returns the type that the component produces
    pub fn output_type(&self) -> Type {
        use Component::*;

        match self {
            Func(f, _) => f.output_type(),
            Attr(attr) => attr.value_type(),
            Time(_) | ErrorMessage | Input => Type::new::<String>(),
            IfElse(_, component, _) => component.output_type(),
            //        ^^^^^^^^^
            // We only need to look at the first `IfElse` component because we've already verified
            // that the types are equal.
        }
    }

    /// Evaluates the `Component` asynchronously, returning the value
    ///
    /// The returned value is guaranteed to have a type equal to [`self.output_type()`].
    ///
    /// Please note that the signature of this function should properly be more like:
    /// ```ignore
    /// pub async fn evaluate<'a>(&'a self, ctx: &Arc<impl Context>) -> Box<dyn Any + Send + Sync> { ... }
    /// ```
    /// The reason we return a `Pin<Box<dyn Future>>` is due to constraints when defining recursive
    /// `async` functions.
    ///
    /// [`self.output_type()`]: Self::output_type
    #[async_method] // We need this because the function recurses
    pub async fn evaluate<'a>(&'a self, ctx: &'a Arc<impl Context>) -> Box<dyn Any + Send + Sync> {
        use Component::*;

        match self {
            Func(func, components) => {
                let iter = components.iter().cloned().map(|c| {
                    let ctx = ctx.clone();
                    async move { c.evaluate(&ctx).await }
                });
                let inputs = runtime::run_all(iter).await;
                func.apply(inputs).await
            }
            Attr(attr) => ctx
                .get_attr_any(*attr)
                .await
                .unwrap_or_else(|| attr.default()),
            Time(format) => Box::new(format.now()),
            IfElse(cond, if_true, if_false) => match cond.is_true(Arc::deref(ctx)) {
                true => if_true.evaluate(ctx).await,
                false => if_false.evaluate(ctx).await,
            },
            ErrorMessage => Box::new(String::from(ctx.get_error_message())),
            Input => Box::new(String::from(ctx.current_input().unwrap_or(""))),
        }
    }
}

impl ComponentBuilder {
    /// Checks that all of the types are correct, producing a verified `Component` if correct
    fn validate(self) -> Result<Component, String> {
        use ComponentBuilder::*;

        let comp = match self {
            Func(func, args) => {
                let args = args
                    .into_iter()
                    .map(|c| c.validate().map(Arc::new))
                    .collect::<Result<Vec<_>, _>>()?;
                func.correct_input_types(args.iter().map(|c| c.output_type()))
                    .map_err(|err| err.to_string())?;

                Component::Func(func, args)
            }
            Attr(attr) => Component::Attr(attr),
            Time(fmt) => Component::Time(fmt),
            IfElse(cond, if_true, if_false) => {
                let if_true = if_true.validate()?;
                let if_false = if_false.validate()?;

                let if_true_type = if_true.output_type();
                let if_false_type = if_false.output_type();

                let mismatched_types = if_true_type != if_false_type;
                let component = Component::IfElse(cond, Box::new(if_true), Box::new(if_false));

                if mismatched_types {
                    return Err(format!(
                        "mismatched types in `{:?}`: left-hand side was `{}`, right-hand side was `{}`",
                        component,
                        if_true_type.name(),
                        if_false_type.name(),
                    ));
                }

                component
            }
            ErrorMessage => Component::ErrorMessage,
            Input => Component::Input,
        };

        Ok(comp)
    }
}

///////////////////////////////////////
// Boilerplate trait implementations //
///////////////////////////////////////

impl TryFrom<ComponentBuilder> for Component {
    type Error = String;

    fn try_from(builder: ComponentBuilder) -> Result<Component, String> {
        builder.validate()
    }
}

impl Debug for Component {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use Component::*;

        match self {
            Func(func, components) => (f.debug_tuple("Func"))
                .field(&func.name())
                .field(components)
                .finish(),
            Attr(attr) => f.debug_tuple("Attr").field(attr).finish(),
            Time(time_format) => f.debug_tuple("Time").field(time_format).finish(),
            IfElse(cond, if_true, if_false) => (f.debug_tuple("If"))
                .field(cond)
                .field(if_true)
                .field(if_false)
                .finish(),
            ErrorMessage => f.write_str("ErrorMessage"),
            Input => f.write_str("Input"),
        }
    }
}
