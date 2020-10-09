use super::Context;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(super) enum Condition {
    Not(Box<Condition>),
    Any(Vec<Condition>),
    HasErrorMessage,
    IsSelected,
}

impl Condition {
    pub fn is_true(&self, ctx: &impl Context) -> bool {
        todo!()
    }
}
