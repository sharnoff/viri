//! Individual components that can be displayed inside the bottom bar

use super::{Context, TimeFormat};
use crate::config::{Attribute, GetAttr, NamedFunction, Type};
use crate::macros::async_method;
use crate::runtime;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::convert::TryFrom;
use std::fmt::{self, Debug, Formatter};
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
    IfElse(Box<Component>, Box<Component>, Box<Component>),
    Not(Box<Component>),
    Any(Vec<Component>),
    ErrorMessage,
    HasErrorMessage,
    Input,
    IsSelected,
}

#[derive(Deserialize)]
pub(super) enum ComponentBuilder {
    Func(NamedFunction, Vec<ComponentBuilder>),
    Attr(Attribute),
    Time(TimeFormat),
    IfElse(
        Box<ComponentBuilder>,
        Box<ComponentBuilder>,
        Box<ComponentBuilder>,
    ),
    Not(Box<ComponentBuilder>),
    Any(Vec<ComponentBuilder>),
    ErrorMessage,
    HasErrorMessage,
    Input,
    IsSelected,
}

impl Component {
    /// Returns the type that the component produces
    pub fn output_type(&self) -> Type {
        use Component::*;

        match self {
            Func(f, _) => f.output_type(),
            Attr(attr) => attr.value_type(),
            Time(_) | ErrorMessage | Input => Type::new::<String>(),
            Not(_) | Any(_) | HasErrorMessage | IsSelected => Type::new::<bool>(),
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
    #[async_method] // We need this because the function is recursive
    pub async fn evaluate<'a>(&'a self, ctx: &'a Arc<impl Context>) -> Box<dyn Any + Send + Sync> {
        use Component::{
            Any as CAny, Attr, ErrorMessage, Func, HasErrorMessage, IfElse, Input, IsSelected, Not,
            Time,
        };

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
            IfElse(cond, if_true, if_false) => match cond.evaluate_as_bool(ctx).await {
                true => if_true.evaluate(ctx).await,
                false => if_false.evaluate(ctx).await,
            },
            Not(c) => Box::new(!c.evaluate_as_bool(ctx).await),
            CAny(cs) => {
                for c in cs {
                    if c.evaluate_as_bool(ctx).await {
                        // For some reason, this one needs an explicit cast
                        return Box::new(true) as Box<dyn Any + Send + Sync>;
                    }
                }

                Box::new(false)
            }
            ErrorMessage => Box::new(String::from(ctx.get_error_message())),
            HasErrorMessage => Box::new(ctx.has_error_message()),
            Input => Box::new(String::from(ctx.current_input().unwrap_or(""))),
            IsSelected => Box::new(ctx.current_input().is_some()),
        }
    }

    /// A helper method to evaluate the `Component` as a boolean
    ///
    /// This requires that the output type is a boolean, but does not check.
    async fn evaluate_as_bool<'a>(&'a self, ctx: &'a Arc<impl Context>) -> bool {
        *self.evaluate(ctx).await.downcast_ref::<bool>().unwrap()
    }
}

impl ComponentBuilder {
    /// Checks that all of the types are correct, producing a verified `Component` if correct
    pub(super) fn validate(self) -> Result<Component, String> {
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
                let cond = Box::new(cond.validate()?);
                let if_true = Box::new(if_true.validate()?);
                let if_false = Box::new(if_false.validate()?);

                let if_true_type = if_true.output_type();
                let if_false_type = if_false.output_type();

                let mismatched_types = if_true_type != if_false_type;
                let component = Component::IfElse(cond, if_true, if_false);

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
            Not(comp) => {
                let component = comp.validate()?;
                let output_type = component.output_type();
                if output_type == Type::new::<bool>() {
                    return Err(format!(
                        "mismatched type from `{:?}`: expected boolean, found `{}`",
                        component,
                        output_type.name(),
                    ));
                }

                Component::Not(Box::new(component))
            }
            Any(components) => {
                let components: Vec<_> = components
                    .into_iter()
                    .map(|c| {
                        let c = c.validate()?;
                        let output_type = c.output_type();
                        if output_type != Type::new::<bool>() {
                            return Err(format!(
                                "mismatched type from `{:?}`: expected boolean, found `{}`",
                                c,
                                output_type.name(),
                            ));
                        }

                        Ok(c)
                    })
                    .collect::<Result<_, _>>()?;

                Component::Any(components)
            }
            ErrorMessage => Component::ErrorMessage,
            HasErrorMessage => Component::HasErrorMessage,
            Input => Component::Input,
            IsSelected => Component::IsSelected,
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
            Not(c) => f.debug_tuple("Not").field(c).finish(),
            Any(cs) => f.debug_tuple("Any").field(cs).finish(),
            ErrorMessage => f.write_str("ErrorMessage"),
            HasErrorMessage => f.write_str("HasErrorMessage"),
            Input => f.write_str("Input"),
            IsSelected => f.write_str("IsSelected"),
        }
    }
}
