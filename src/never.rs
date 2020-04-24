//! Defines a custom "never" type that supports (de)serialization

use serde::{Serialize, Deserialize};

#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub enum Never {}
