use super::component::ComponentBuilder;
use super::{Component, Context};
use crate::macros::async_method;
use serde::{Deserialize, Serialize};
use std::convert::TryFrom;
use std::sync::Arc;

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(try_from = "ConditionBuilder")]
pub(super) enum Condition {
    Not(Box<Condition>),
    Any(Vec<Condition>),
    Expr(Box<Component>),
    HasErrorMessage,
    IsSelected,
}

impl Condition {
    /// Returns whether the condition evaluates to `true` within the given context
    #[async_method]
    pub async fn is_true<'a>(&'a self, ctx: &'a Arc<impl Context>) -> bool {
        use Condition::*;

        match self {
            Not(c) => !c.is_true(ctx).await,
            Any(cs) => {
                for c in cs.iter() {
                    if c.is_true(ctx).await {
                        return true;
                    }
                }

                false
            }
            Expr(component) => *component
                .evaluate(ctx)
                .await
                .downcast_ref::<bool>()
                .unwrap(),
            HasErrorMessage => ctx.has_error_message(),
            IsSelected => ctx.current_input().is_some(),
        }
    }
}

#[derive(Deserialize)]
pub(super) enum ConditionBuilder {
    Not(Box<ConditionBuilder>),
    Any(Vec<ConditionBuilder>),
    Expr(Box<ComponentBuilder>),
}

impl ConditionBuilder {
    pub(super) fn validate(self) -> Result<Condition, String> {
        use ConditionBuilder::*;

        let cond = match self {
            Not(cond) => Condition::Not(Box::new((*cond).validate()?)),
            Any(Vec<
        };

        Ok(cond)
    }
}

impl TryFrom<ConditionBuilder> for Condition {
    type Error = String;

    fn try_from(builder: ConditionBuilder) -> Result<Condition, String> {
        builder.validate()
    }
}
