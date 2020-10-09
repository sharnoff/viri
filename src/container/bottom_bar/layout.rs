//! The full layout of the displayed bottom bar

use super::{Component, Condition};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(super) struct Layout {
    left: Vec<Component>,
    center: Vec<Component>,
    right: Vec<Component>,
}

impl Default for Layout {
    fn default() -> Self {
        use Component::{ErrorMessage, IfElse, Input};
        use Condition::HasErrorMessage;

        let left = vec![IfElse(
            HasErrorMessage,
            Box::new(ErrorMessage),
            Box::new(Input),
        )];

        Layout {
            left,
            center: Vec::new(),
            right: Vec::new(),
        }
    }
}
