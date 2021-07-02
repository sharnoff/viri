//! Wrapper module for the various parameterizations of the [`Ranged`] type
//!
//! The raw type itself is typically far more verbose than most users might want. For information
//! about use cases, however, please refer to [its documentation], or the types present in this
//! module. Of particular note are the [`StdRanged`] and [`RelativeSet`] types.
//!
//! [its documentation]: Ranged

mod core;
mod index;
mod set;
mod std_ranged;

pub use self::core::{AccumulatorSlice, NodeRef, Ranged};
pub use index::RangedIndex;
pub use set::RelativeSet;
pub use std_ranged::{Constant, IndexedSlice, NoAccumulator, NoIndex, Slice, StdRanged};
