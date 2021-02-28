//! wrapper module for [`Layout`]

use super::{Component, Context};
use crate::any::BoxedAny;
use crate::any::Type;
use crate::container::paint::{Painter, StyledContent, StyledString, Symbol};
use crate::TermPos;
use serde::{Deserialize, Serialize};
use std::borrow::Cow;
use std::convert::{TryFrom, TryInto};
use std::sync::Arc;

/// The layout of the bottom bar
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(try_from = "LayoutBuilder")]
pub(super) struct Layout {
    left: Vec<Component>,
    center: Vec<Component>,
    right: Vec<Component>,
    left_alignment: Alignment,
    center_alignment: Alignment,
    right_alignment: Alignment,
}

impl Default for Layout {
    fn default() -> Self {
        use Component::{ErrorMessage, HasErrorMessage, IfElse, Input};

        let left = vec![IfElse(
            Box::new(HasErrorMessage),
            Box::new(ErrorMessage),
            Box::new(Input),
        )];

        Layout {
            left,
            center: Vec::new(),
            right: Vec::new(),
            left_alignment: Alignment::Left,
            center_alignment: Alignment::Left,
            right_alignment: Alignment::Right,
        }
    }
}

#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
enum Alignment {
    Left,
    Right,
}

impl Alignment {
    /// Returns whether the value is `Alignment::Right`
    fn is_right(&self) -> bool {
        match self {
            Alignment::Left => false,
            Alignment::Right => false,
        }
    }

    // A helper method so that we can pass something for `serde` to use as the default alignment
    fn left() -> Alignment {
        Alignment::Left
    }

    // A helper method so that we can pass something for `serde` to use as the default alignment
    fn right() -> Alignment {
        Alignment::Right
    }
}

// A helper macro to compose the static list of allowed string types
macro_rules! allowed {
    ($ty:ty, $func:expr $(,)?) => {{
        let f = |any: BoxedAny| -> StyledString { $func(any.downcast::<$ty>()) };

        (Type::new::<$ty>(), f)
    }};
}

/// The types of values that can be converted to [`StyledString`]s, alongside the functions do to
/// so
///
/// Currently, only the following types are allowed:
/// * [`StyledString`]
/// * `String`
/// * `&'static str`
/// * `Cow<'static, str>`
/// Alongside being wrapped by `Option<T>` and `Arc<T>` for each of them.
///
/// This is largely generated by the neighboring `allowed` macro, which greatly simplifies the
/// amount of syntax needed to describe each entry.
#[rustfmt::skip]
static ALLOWED_STRING_TYPES: &[(Type, fn(BoxedAny) -> StyledString)] = &[
    // Base types:
    allowed!(StyledString, std::convert::identity),
    allowed!(String, |s: String| s.into()),
    allowed!(&'static str, |s: &str| s.to_owned().into()),
    allowed!(Cow<'static, str>, |s: Cow<str>| s.into_owned().into()),

    // Option<T>
    allowed!(Option<StyledString>, |s: Option<StyledString>| s.unwrap_or_default()),
    allowed!(Option<String>, |s: Option<String>| s.unwrap_or_default().into()),
    allowed!(Option<&'static str>, |s: Option<&str>| s.unwrap_or("").to_owned().into()),
    allowed!(
        Option<Cow<'static, str>>,
        |s: Option<Cow<str>>| s.map(Cow::into_owned).unwrap_or_default().into(),
    ),

    // Arc<T>
    allowed!(Arc<StyledString>, |s: Arc<StyledString>| StyledString::clone(&s)),
    allowed!(Arc<String>, |s: Arc<String>| s.as_str().to_owned().into()),
    allowed!(Arc<&'static str>, |s: Arc<&str>| (*s).to_owned().into()),
    allowed!(Arc<str>, |s: Arc<str>| (&*s).to_owned().into()),
    allowed!(Cow<'static, str>, |s: Cow<str>| s.into_owned().into()),

    // // Option<Arc<T>> - TODO-FEATURE
    // allowed!(Option<Arc<StyledString>>, std::convert::identity),
    // allowed!(String, |s: String| s.into()),
    // allowed!(&'static str, |s: &str| s.to_owned().into()),
    // allowed!(Cow<'static, str>, |s: Cow<str>| s.into_owned().into()),

    // // Arc<Option<T>> - TODO-FEATURE
    // allowed!(Arc<Option<StyledString>>, std::convert::identity),
    // allowed!(String, |s: String| s.into()),
    // allowed!(&'static str, |s: &str| s.to_owned().into()),
    // allowed!(Cow<'static, str>, |s: Cow<str>| s.into_owned().into()),
];

impl Layout {
    /// Draws the `Layout` into the first row of the painter
    pub async fn draw(self: Arc<Self>, ctx: Arc<impl Context>, painter: Painter<'_>) {
        let align = utils::Parts {
            left: self.left_alignment,
            center: self.center_alignment,
            right: self.right_alignment,
        };

        let parts = self.eval_parts(ctx).await;
        Layout::paint_parts(painter, align, parts);
    }

    /// Evaluates the inner components used to generate the strings displayed as part of drawing
    /// the `Layout`
    // This is purely a helper function for `draw`. We don't want it cluttering things up
    #[doc(hidden)]
    async fn eval_parts(
        self: Arc<Self>,
        ctx: Arc<impl Context>,
    ) -> utils::Parts<StyledContent<Vec<Symbol>>> {
        use self::utils::{Parts, Side};

        // We need to use `Side` here in order for the concrete types of the futures to be the
        // same. If we break them up (e.g. by iterating over self.$field three times), the compiler
        // complains that they aren't the same type (even though they'd be represented in the same
        // fashion in memory, just with different function pointers).
        let futures = (0..self.left.len())
            .map(Side::Left)
            .chain((0..self.center.len()).map(Side::Center))
            .chain((0..self.right.len()).map(Side::Right))
            .map(|side| {
                let this = self.clone();
                let ctx = ctx.clone();
                async move {
                    let component = match side {
                        Side::Left(i) => &this.left[i],
                        Side::Center(i) => &this.center[i],
                        Side::Right(i) => &this.right[i],
                    };

                    Layout::stringify(component.evaluate(&ctx).await)
                }
            })
            .collect::<Vec<_>>();

        let mut regions = crate::runtime::run_all(futures).await;
        let parts = Parts {
            left: regions.drain(..self.left.len()).collect::<Vec<_>>(),
            center: regions.drain(..self.center.len()).collect(),
            right: regions.drain(..self.right.len()).collect(),
        };

        // We then compute the width of each segment, choosing carefully how to display them.

        parts
            .map(|strings| {
                strings
                    .into_iter()
                    .map(StyledString::into_symbols)
                    .collect::<Vec<_>>()
            })
            .map(StyledContent::from)
    }

    /// Paints the parts generated by `eval_parts`
    ///
    /// This is the second of two parts of the `draw` method, and is internal-only.
    // Hidden for the same reason as `eval_parts`
    #[doc(hidden)]
    fn paint_parts(
        mut painter: Painter,
        align: utils::Parts<Alignment>,
        mut parts: utils::Parts<StyledContent<Vec<Symbol>>>,
    ) {
        use self::utils::Parts;

        // 'w' is our shorthand for the width of each `part`.
        //
        // Ordinarily, we wouldn't a name so short, but it comes up *very* frequently and so my
        // judgement was that it would be harder to read WITH a longer name.
        let w = parts.as_ref().map(|region| {
            region
                .segments
                .iter()
                .map(StyledString::width)
                .fold(0_u16, |acc, w| {
                    acc.saturating_add(w.try_into().unwrap_or(u16::MAX))
                })
        });

        let start_cols;
        let mut cutoff: Parts<Option<u16>> = Default::default();

        // This expression is analogous to:
        //   if w.left + w.center + w.right < painter.width(), then
        //   let space give the difference
        if let Some(space) = painter
            .width()
            .checked_sub(w.left.saturating_add(w.center).saturating_add(w.right))
        {
            // If there's enough room in the painter to write all of the segments in the bottom
            // bar, we'll do it.
            //
            // There are two gaps: left-center and center-right. We'll default to giving more space
            // on the right-hand side of the center region.
            let lhs_space = space / 2;

            // TODO-FEATURE: make this use the weighting function from below to ensure that the
            // center region stays close-ish to the center.

            start_cols = Parts {
                left: 0,
                center: w.left + lhs_space,
                right: painter.width() - w.right,
            };
        } else {
            // If there isn't enough room in the painter to write everything, we need to figure out
            // what to remove.
            //
            // Without using precedence to determine how to fill the regions, we'll try to scale
            // things in a somewhat-intelligent manner.
            //
            // We'll do this in a couple of ways. Essentially, we want to give larger regions more
            // weight, but only up to a certain point -- and we certainly don't want to do it
            // linearly. So we define the following function:
            //
            //   f(x) = 1 - 1 / (x/b + 1)
            //
            // This function starts at zero and approaches a value of 1 asymptotically, where a
            // larger value of `b` makes the curve flatter. To look at a couple values, we can see
            // that:
            //
            //   f(b) = 0.5, and                     -> For those interested, the general equation
            //   f(3b) = 0.75                           here is that f(λb) = λ / (λ + 1).
            //
            // All that matters then is our choice of `b`. Unfortunately, this is *more* of a
            // heuristic than the generation of this function -- we just need to pick a value so
            // that it tends to balance things well. We'll just use half the width of the terminal.
            // It's hopefully okay.

            const TERM_SCALE_MULTIPLIER: f32 = 0.5;

            // The value of 'b' from above.
            let b: f32 = (painter.width() as f32) * TERM_SCALE_MULTIPLIER;
            // And then 'f' from above:
            let f = |x: f32| 1.0 - 1.0 / (x / b + 1.0);

            // Weight each part by its width
            let mut weights = w.map(|width| f(width as f32));
            // And then scale the weights so that they're out of 1, by constructing the new widths:
            let weights_sum = weights.left + weights.center + weights.right;

            weights = weights.map(|w| w / weights_sum);

            let mut width = w
                .zip(weights)
                .map(|(width, weight)| ((width as f32) * weight).floor() as u16);
            //                                                   ^^^^^^^
            // Because this uses `floor`, it's intentionally an underestimate. To compensate, we
            // add the remaining unallocated width to the largest segment.

            let width_sum = width.left + width.center + width.right;
            let largest = match (w.left >= w.center, w.center >= w.right, w.right >= w.left) {
                (true, true, false) | (true, false, false) => &mut width.left,
                (false, true, true) | (false, true, false) => &mut width.center,
                (true, false, true) | (false, false, true) => &mut width.right,
                (true, true, true) | (false, false, false) => unreachable!(),
            };

            // Then, because there's probably rounding issues, we add the amount remaining to the
            // section that was previously the largest
            *largest += painter.width() - width_sum;

            let is_right_aligned = align.as_ref().map(Alignment::is_right);

            cutoff =
                w.zip(width)
                    .zip(is_right_aligned)
                    .map(|((original, new), is_right_aligned)| match original > new {
                        true if is_right_aligned => Some(new),
                        _ => None,
                    });

            start_cols = Parts {
                left: 0,
                center: width.left,
                right: width.left + width.center,
            };
        }

        // If any right-aligned parts were cut off, we'll trim them so that we can ensure they
        // remain right-aligned.
        parts = parts.zip(cutoff).map(|(part, is_cutoff)| match is_cutoff {
            Some(new_width) => part.trim_left_to(new_width as usize),
            None => part,
        });

        let _: Parts<()> = start_cols.zip(parts).map(|(col, content)| {
            painter.paint_at(TermPos { row: 0, col }, content);
        });
    }

    /// Produces a [`StyledString`] from a value that is any of the accepted ones in
    /// [`ALLOWED_STRING_TYPES`]
    ///
    /// If the provided value is not any one of these, it will - of course - panic.
    fn stringify(any: BoxedAny) -> StyledString {
        for (ty, convert) in ALLOWED_STRING_TYPES {
            if *ty == any.inner_type() {
                return convert(any);
            }
        }

        panic!("unexpected input type `{}`", any.inner_type().name());
    }
}

/// A utility module containing a couple items for helping with implementing [`Layout::draw`]
mod utils {
    pub enum Side {
        Left(usize),
        Center(usize),
        Right(usize),
    }

    #[derive(Copy, Clone, Default)]
    pub struct Parts<T> {
        pub left: T,
        pub center: T,
        pub right: T,
    }

    impl<T> Parts<T> {
        pub fn as_ref(&self) -> Parts<&T> {
            Parts {
                left: &self.left,
                center: &self.center,
                right: &self.right,
            }
        }

        pub fn map<S, F: FnMut(T) -> S>(self, mut func: F) -> Parts<S> {
            Parts {
                left: func(self.left),
                center: func(self.center),
                right: func(self.right),
            }
        }

        pub fn zip<S>(self, rhs: Parts<S>) -> Parts<(T, S)> {
            Parts {
                left: (self.left, rhs.left),
                center: (self.center, rhs.center),
                right: (self.right, rhs.right),
            }
        }
    }
}

#[derive(Deserialize)]
struct LayoutBuilder {
    left: Vec<Component>,
    center: Vec<Component>,
    right: Vec<Component>,
    #[serde(default = "Alignment::left")]
    left_alignment: Alignment,
    #[serde(default = "Alignment::left")]
    center_alignment: Alignment,
    #[serde(default = "Alignment::right")]
    right_alignment: Alignment,
}

impl LayoutBuilder {
    fn validate(self) -> Result<Layout, String> {
        macro_rules! check_all {
            (self.$field:ident) => {{
                for c in &self.$field {
                    let ty = c.output_type();
                    let is_valid_type = !ALLOWED_STRING_TYPES
                        .iter()
                        .map(|(ty, _)| ty)
                        .any(|t| t == &ty);

                    if !is_valid_type {
                        return Err(format!(
                            "layout component {:?} has wrong type. Found `{}`, but expected any of: {:?}",
                            c,
                            ty.name(),
                            ALLOWED_STRING_TYPES
                                .iter()
                                .map(|(ty, _)| ty.name())
                                .collect::<Vec<_>>(),
                        ));
                    }
                }
            }};
        }

        check_all!(self.left);
        check_all!(self.center);
        check_all!(self.right);

        Ok(Layout {
            left: self.left,
            center: self.center,
            right: self.right,
            left_alignment: self.left_alignment,
            center_alignment: self.center_alignment,
            right_alignment: self.right_alignment,
        })
    }
}

impl TryFrom<LayoutBuilder> for Layout {
    type Error = String;

    fn try_from(builder: LayoutBuilder) -> Result<Layout, String> {
        builder.validate()
    }
}
