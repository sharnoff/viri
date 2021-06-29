//! Wrapper module for the various parameterizations of the [`Ranged`] type
//!
//! The raw type itself is typically far more verbose than most users might want. For information
//! about use cases, however, please refer to [its documentation].
//!
//! [its documentation]: Ranged

#[doc(hidden)]
mod core;
#[doc(hidden)]
mod index;
#[doc(hidden)]
mod std_ranged;

#[doc(inline)]
pub use self::core::{AccumulatorSlice, NodeRef, Ranged};
#[doc(inline)]
pub use index::RangedIndex;
#[doc(inline)]
pub use std_ranged::{Constant, IndexedSlice, NoAccumulator, NoIndex, Slice, StdRanged};
