//! Wrapper module for the various parameterizations of the [`Ranged`] type
//!
//! The raw type itself is typically far more verbose than most users might want. For information
//! about use cases, however, please refer to [its documentation].
//!
//! [its documentation]: Ranged

mod core;
mod index;
mod std_ranged;

pub use self::core::{AccumulatorSlice, NodeRef, Ranged};
pub use index::RangedIndex;
pub use std_ranged::{Constant, IndexedSlice, NoAccumulator, NoIndex, Slice, StdRanged};
