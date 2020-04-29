//! Definitions of horizontal and vertical splits
//!
//! Horizontal splits are those that preserve the width of the [`View`]s, stacking them vertically.
//! Vertical splits are the opposite: placing them side by side, preserving the height.
//!
//! The two types corresponding to these are [`Horiz`] and [`Vert`], respectively. Their
//! implementations are very similar, but are extracted into separate types in order to allow for
//! simplified code.
//!
//! ## Visualizing layouts
//!
//! Creating a horizontal split can be visualized as the following change:
//! ```text
//! Before:                 After:
//! ╔═══════════════════╗  ╔═══════════════════╗
//! ║                   ║  ║       Upper       ║
//! ║                   ║  ║                   ║
//! ║     Main View     ║  ╠═══════════════════╣
//! ║                   ║  ║       Lower       ║
//! ║                   ║  ║                   ║
//! ╚═══════════════════╝  ╚═══════════════════╝
//! ```
//!
//! Whereas creating a vertical split can be visualized as:
//! ```text
//! Before:                 After:
//! ╔═══════════════════╗  ╔═════════╦═════════╗
//! ║                   ║  ║         ║         ║
//! ║                   ║  ║         ║         ║
//! ║     Main View     ║  ║  Left   ║  Right  ║
//! ║                   ║  ║         ║         ║
//! ║                   ║  ║         ║         ║
//! ╚═══════════════════╝  ╚═════════╩═════════╝
//! ```
//!
//! [`View`]: ../trait.View.html
//! [`Horiz`]: struct.Horiz.html
//! [`Vert`]: struct.Vert.html

/// A horizontally-split container of two (or more) [`View`]s
///
/// For the difference between horizontal and vertical splits, please refer to the
/// [module-level documentation].
///
/// [`View`]: ../trait.View.html
/// [module-level documentation]: index.html
struct Horiz {}

/// A vertically-split container of two (or more) [`View`]s
///
/// For the difference between horizontal and vertical splits, please refer to the
/// [module-level documentation].
///
/// [`View`]: ../trait.View.html
/// [module-level documentation]: index.html
struct Vert {}
