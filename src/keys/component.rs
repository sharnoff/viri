//! Wrapper module for [`Component`] and [`AnnotatedComponent`]

use super::MatchResult;
use crate::any::{BoxedAny, DynClone, Type};
use crate::config::NamedFunction;
use crate::event::{KeyCode, KeyEvent, KeyModifiers};
use crate::macros::async_method;
use serde::{Deserialize, Serialize, Serializer};
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Debug, Display, Formatter};
use std::sync::Arc;

/// The individual regex-like piece of a keybinding
///
/// `Component`s are the primary types involved in user-definition of keybindings. This is kind of
/// a fake status though, because it is primarily their *structure* that's used, not the actual
/// type itself. In other words, `Component`s only really exist as an intermediate step in
/// serializing.
// @def "Component field ordering" v0
#[derive(Serialize)]
pub enum Component {
    /// Any of a (nonempty) set of `Component`s. Conflicts are not allowed
    Union(Vec<Component>),
    /// Any (nonzero) number of `Component`s following each other. The end of each cannot conflict
    /// with the start of the next
    Concat(Vec<Component>),
    /// A single key
    Atom {
        /// The single key pressed
        key: KeySet,
        /// Whether this key may be repeated (treated as zero or more). If true, this `Component`
        /// will return a vector (of characters or key events). See [`KeySet`] for more information
        /// about the types returned.
        repeated: bool,
    },
    Map(NamedFunction, Box<Component>),
    /// A component named elsewhere in the [`KeybindingSet`]
    Named(String),
    /// A constant, with a type determined when we deserialize
    Const(Box<Component>, Arc<dyn DynClone>),
}

/// A fully-validated component, ready for use in keybinding matching
///
/// These are constructed by calling [`Component::validate_into`], which is done internally in the
/// process of generating a [`KeybindingSet`](super::KeybindingSet).
///
/// The core functionality provided by this type are the [`matches`](Self::matches) and
/// [`output`](Self::output) methods, which check whether an input matches the component and
/// provide the output of a component for a given input, respectively.
///
/// This type is essentially the same in structure as [`Component`], but with
/// [`AnnotatedComponentKind`] representing the different variants, and this struct providing
/// additional data.
#[derive(Clone)]
pub struct AnnotatedComponent<I> {
    /// The variant of the original [`Component`]
    pub(super) kind: AnnotatedComponentKind<I>,
    /// The additional information stored alongside the [`Component`]
    pub(super) info: I,
}

/// The typical set of information provided inside an [`AnnotatedComponent`]
#[derive(Clone)]
pub struct Info {
    /// The types of the value this component produces. This is a list due to a quirk with
    /// constructing types at runtime. For more information, see the
    /// [`Component` documentation](Component#implementation-details).
    pub(super) output_types: Vec<Type>,

    /// The set of keys this component can start with
    // TODO-ALG: this should probably use a more compact representation, but it's *okay* for the
    // time being.
    pub(super) starts_with: Vec<KeySet>,

    /// The set of keys this component can be followed with, while still continuing the same
    /// component. This can only ever be as a result of an optionally-repeated key at the end of
    /// the component.
    pub(super) follow_set: Vec<KeySet>,
}

/// A helper for [`AnnotatedComponent`]
///
/// This is structurally equivalent to [`Component`], with extra information coming from the inner
/// `AnnotatedComponent`.
// @def "Component variants" v0
#[derive(Clone)]
pub enum AnnotatedComponentKind<I> {
    Union(Vec<AnnotatedComponent<I>>),
    Concat(Vec<AnnotatedComponent<I>>),
    // @def "Component::Atom fields" v0
    Atom {
        key: KeySet,
        repeated: bool,
    },
    Map(NamedFunction, Box<AnnotatedComponent<I>>),
    Named(String),
    Const(
        // the inner, mapped component
        Box<AnnotatedComponent<I>>,
        // the originally deserialized value; and
        Arc<dyn DynClone>,
        // the newly-produced value, actually used as the desired constant
        Arc<dyn DynClone>,
    ),
}

/// A (minimal) description for sets of [`KeyEvent`](crate::event::KeyEvent)s
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub enum KeySet {
    // Note: range is inclusive, must have lhs <= rhs
    /// A range of characters, pressed under these key modifiers. When used in a [`Component`], the
    /// output type is a character.
    Range(char, char, #[serde(default = "none")] Option<KeyModifiers>),
    /// A single, raw key event
    Single(KeyEvent),
    /// Any character pressed with the given set of modifiers. If no modifiers are given, then
    /// `Shift` will be allowed as well, because all uppercase letters are shifted. When used in a
    /// [`Component`], the output type is a character.
    Any(Option<KeyModifiers>),
}

fn none<T>() -> Option<T> {
    None
}

////////////////////////////////////////////////////////////
// Matching on components                                 //
// ----                                                   //
// TODO-ALG: Matching should probably be stateful - i.e   //
// using some sort of dfa-like thing to avoid             //
// recomputation on each additional key. It's not super   //
// necessary, because - realistically - the length of key //
// sequences will tend to be quite short.                 //
////////////////////////////////////////////////////////////

/// A helper type definition for encompassing the named components in an [`AnnotatedComponent`]
pub type Namespace = HashMap<String, AnnotatedComponent<Info>>;

// TODO-CLEAN: The two methods defined below are very similar. This could probably be refactored to
// reduce duplication here.
impl AnnotatedComponent<Info> {
    /// Returns whether the given input matches the component
    pub fn matches(&self, input: &[KeyEvent], namespace: &Namespace) -> MatchResult {
        use AnnotatedComponentKind::{Atom, Concat, Const, Map, Named, Union};
        use MatchResult::{Matched, NeedsMore, NoMatch};

        if input.is_empty() {
            return NeedsMore;
        }

        match &self.kind {
            #[rustfmt::skip]
            Atom { key: key_set, repeated: false } => {
                match key_set.contains(&input[0]) {
                    true => Matched { len: 1 },
                    false => NoMatch { len: 1 },
                }
            },
            #[rustfmt::skip]
            Atom { key: key_set, repeated: true } => {
                // repeated atoms may match with a length of zero
                let len = input.iter().take_while(|k| key_set.contains(k)).count();
                Matched { len }
            }
            Map(_, comp) | Const(comp, _, _) => comp.matches(input, namespace),
            Named(s) => namespace[s].matches(input, namespace),
            Union(comps) => {
                for c in comps {
                    if c.info.starts_with.iter().any(|ks| ks.contains(&input[0])) {
                        return c.matches(input, namespace);
                    }
                }

                NoMatch { len: 1 }
            }
            #[rustfmt::skip]
            Concat(comps) => {
                let mut consumed = 0;
                for c in comps {
                    match c.matches(&input[consumed..], namespace) {
                        Matched { len } => consumed += len,
                        NoMatch { len } => return NoMatch { len: consumed + len },
                        res @ NeedsMore => return res,
                    }
                }

                Matched { len: consumed }
            }
        }
    }

    /// Produces the output for a matching key sequence
    ///
    /// This should only be called for valid matches, as given by [`AnnotatedComponent::matches`].
    /// This function will panic if that is not the case.
    #[async_method]
    pub async fn output_consumed<'a>(
        &'a self,
        input: &'a [KeyEvent],
        namespace: &'a Namespace,
    ) -> (usize, Vec<BoxedAny>) {
        use AnnotatedComponentKind::{Atom, Concat, Const, Map, Named, Union};
        use KeyCode::Char;
        use KeySet::{Any, Range, Single};

        macro_rules! any {
            ($ty:ty: $expr:expr) => {{
                BoxedAny::new($expr)
            }};
        }

        assert!(!input.is_empty());

        match &self.kind {
            #[rustfmt::skip]
            Atom { key: key_set, repeated: false } => {
                assert!(key_set.contains(&input[0]));

                // @req "KeySet output type" v0
                let out = match (key_set, input[0]) {
                    (Single(_), ev) => any!(KeyEvent: ev),
                    (Range(_, _, _), KeyEvent { code: Char(c), .. })
                    | (Any(_), KeyEvent { code: Char(c), .. }) => any!(char: c),
                    _ => unreachable!(),
                };

                (1, vec![out])
            }
            #[rustfmt::skip]
            Atom { key: key_set, repeated: true } => {
                let n = input.iter().take_while(|k| key_set.contains(k)).count();

                // @req "KeySet output type" v0
                let out = match key_set {
                    Single(_) => any!(Vec<KeyEvent>: Vec::from(&input[..n])),
                    Range { .. } | Any(_) => {
                        let list: Vec<char> = (input[..n].iter())
                            .map(|ev| match ev.code {
                                Char(c) => c,
                                _ => unreachable!(),
                            })
                            .collect();
                        any!(Vec<char>: list)
                    }
                };

                (n, vec![out])
            }
            Named(name) => namespace[name].output_consumed(input, namespace).await,
            Map(func, comp) => {
                let (n, output) = comp.output_consumed(input, namespace).await;
                let out = func.apply(output).await;
                (n, vec![out])
            }
            Concat(comps) => {
                let mut outs = Vec::new();
                let mut len = 0;
                for c in comps {
                    let (n, vs) = c.output_consumed(&input[len..], namespace).await;
                    outs.extend(vs);
                    len += n;
                }

                (len, outs)
            }
            Union(comps) => {
                for c in comps {
                    if c.info.starts_with.iter().any(|ks| ks.contains(&input[0])) {
                        return c.output_consumed(input, namespace).await;
                    }
                }

                unreachable!()
            }
            Const(comp, _, value) => {
                let consumed = match comp.matches(input, namespace) {
                    MatchResult::Matched { len } => len,
                    res => panic!(
                        "unexpected match result {:?}; expected successful match",
                        res
                    ),
                };

                // We need to do a double-dereference here because it's a &Arc<_>
                // A single dereference would just clone the Arc, not the underlying value, which
                // is *NOT* what we want.
                (consumed, vec![(&**value).clone_to_boxed_any()])
            }
        }
    }
}

////////////////////////////////////////////////////////////
// Validation                                             //
////////////////////////////////////////////////////////////

impl<I> AnnotatedComponent<I> {
    /// Registers all of the external names requried by the component into the provided accumulator
    pub(super) fn required_names(&self, accum: &mut HashSet<String>) {
        use AnnotatedComponentKind::{Atom, Concat, Const, Map, Named, Union};

        match &self.kind {
            Named(s) => drop(accum.insert(s.clone())),
            Union(cs) | Concat(cs) => cs.iter().for_each(|c| c.required_names(accum)),
            Const(c, _, _) | Map(_, c) => c.required_names(accum),
            Atom { .. } => (),
        }
    }
}

impl AnnotatedComponent<Vec<Type>> {
    /// Validates the component, returning the final version - i.e. the one with `Info` as its
    /// tagged value.
    ///
    /// The primary purpose of this method is to produce the starting keys and follow-sets for each
    /// value.
    ///
    /// This method assumes that any named components referenced by this will have entries in
    /// `namespace`, and will panic otherwise.
    pub(super) fn validate(
        self,
        namespace: &HashMap<String, AnnotatedComponent<Info>>,
    ) -> Result<AnnotatedComponent<Info>, String> {
        use AnnotatedComponentKind::{Atom, Concat, Const, Map, Named, Union};

        let starts_with;
        let follow_set;

        let kind = match self.kind {
            Atom { key, repeated } => {
                starts_with = vec![key];
                follow_set = match repeated {
                    true => vec![key],
                    false => vec![],
                };

                Atom { key, repeated }
            }
            Map(func, comp) => {
                let comp = comp.validate(namespace)?;
                starts_with = comp.info.starts_with.clone();
                follow_set = comp.info.follow_set.clone();

                Map(func, Box::new(comp))
            }
            Named(name) => {
                let c = &namespace[&name];
                starts_with = c.info.starts_with.clone();
                follow_set = c.info.follow_set.clone();

                Named(name)
            }
            Const(comp, original, value) => {
                let comp = comp.validate(namespace)?;
                starts_with = comp.info.starts_with.clone();
                follow_set = comp.info.follow_set.clone();

                Const(Box::new(comp), original, value)
            }
            Union(cs) => {
                let cs: Vec<_> = cs
                    .into_iter()
                    .map(|c| c.validate(namespace))
                    .collect::<Result<_, _>>()?;

                // Check that no two starting sets overlap (and create the new one)
                //
                // For each starting set, we'll additionally store a reference to the component it
                // came from, in case we find any overlaps.
                let mut new_starting_set = <Vec<(&AnnotatedComponent<_>, KeySet)>>::new();
                for comp in &cs {
                    for key_set in &comp.info.starts_with {
                        let nonempty_intersection = new_starting_set
                            .iter()
                            .filter_map(|(comp, s)| Some((comp, s.intersect(key_set)?)))
                            .next();

                        if let Some((original_comp, int)) = nonempty_intersection {
                            return Err(format!(
                                "conflict in starting sets for keybinding components; {} in both {:?} and {:?}",
                                int,
                                original_comp.debug_as_component(),
                                comp.debug_as_component(),
                            ));
                        }
                    }

                    new_starting_set
                        .extend(comp.info.starts_with.iter().cloned().map(|ks| (comp, ks)));
                }

                starts_with = new_starting_set.into_iter().map(|(_, ks)| ks).collect();

                // Merge the follow sets:
                follow_set = cs
                    .iter()
                    .map(|c| c.info.follow_set.iter())
                    .flatten()
                    .cloned()
                    .collect();

                Union(cs)
            }
            Concat(cs) => {
                let cs: Vec<_> = cs
                    .into_iter()
                    .map(|c| c.validate(namespace))
                    .collect::<Result<_, _>>()?;

                // For concatentation, we only need to check that the follow-set of each component
                // doesn't intersect with the starting set of the next:
                for (comp, next_comp) in cs.iter().zip(&cs[1..]) {
                    for key_set in &comp.info.follow_set {
                        let nonempty_intersection = (next_comp.info.starts_with.iter())
                            .filter_map(|ks| key_set.intersect(ks))
                            .next();
                        if let Some(int) = nonempty_intersection {
                            println!(
                                "individual follow-set: {:?}, starts_with: {:?}",
                                key_set, next_comp.info.starts_with
                            );

                            return Err(format!(
                                concat!(
                                    "conflict between follow-set of component and starting set of next; overlaps at {}:\n",
                                    "component: {:?}\n",
                                    "next component: {:?}",
                                ),
                                int,
                                comp.debug_as_component(),
                                next_comp.debug_as_component(),
                            ));
                        }
                    }
                }

                starts_with = cs[0].info.starts_with.clone();
                follow_set = cs[cs.len() - 1].info.follow_set.clone();

                Concat(cs)
            }
        };

        let info = Info {
            output_types: self.info,
            starts_with,
            follow_set,
        };

        Ok(AnnotatedComponent { kind, info })
    }
}

impl KeySet {
    /// If the `KeySet` is ranged, checks that the upper bound is not below the lower bound
    pub(super) fn validate_if_ranged(&self) -> Result<(), String> {
        use KeySet::{Any, Range, Single};

        match self {
            Range(lower, upper, _mods) if lower > upper => Err(format!(
                "invalid key range; lower key '{}' > '{}'",
                lower, upper
            )),
            Single(_) | Any(_) | Range(_, _, _) => Ok(()),
        }
    }

    /// Returns the type produced by this `KeySet`, given whether the keys are repeated
    pub(super) fn output_type(&self, repeated: bool) -> &'static [Type] {
        static VEC_CHAR: &[Type] = &[Type::new::<Vec<char>>()];
        static CHAR: &[Type] = &[Type::new::<char>()];
        static VEC_KEY_EVENT: &[Type] = &[Type::new::<Vec<KeyEvent>>()];
        static KEY_EVENT: &[Type] = &[Type::new::<KeyEvent>()];

        // @def "KeySet output type" v0
        match self {
            KeySet::Range { .. } | KeySet::Any(_) if repeated => VEC_CHAR,
            KeySet::Range { .. } | KeySet::Any(_) => CHAR,
            KeySet::Single(_) if repeated => VEC_KEY_EVENT,
            KeySet::Single(_) => KEY_EVENT,
        }
    }

    /// Returns the intersection between the two key sets, if it isn't empty
    fn intersect(&self, other: &KeySet) -> Option<KeySet> {
        use KeyCode::Char;
        use KeySet::{Any, Range, Single};

        match (self, other) {
            // (Any, *)
            (Any(mod_self), Any(mod_other)) if mod_self == mod_other => Some(*self),
            (Any(mods), Range(lo, hi, rmods)) | (Range(lo, hi, rmods), Any(mods))
                if mods == rmods =>
            {
                Some(Range(*lo, *hi, *rmods))
            }
            (Any(mods), Single(key)) | (Single(key), Any(mods)) if mods == &key.mods => {
                Some(Single(*key))
            }

            // (Range, *)
            (Range(xlo, xhi, xmods), Range(ylo, yhi, ymods)) if xmods == ymods => {
                match (xlo.max(ylo), xhi.min(yhi)) {
                    (lo, hi) if lo <= hi => Some(Range(*lo, *hi, *xmods)),
                    _ => None,
                }
            }
            (Range(lo, hi, rmods), Single(key)) | (Single(key), Range(lo, hi, rmods))
                if key.mods == *rmods =>
            {
                match &key.code {
                    Char(ref c) if lo <= c && c <= hi => Some(Single(*key)),
                    _ => None,
                }
            }

            // (Single, Single)
            (Single(x), Single(y)) if x == y => Some(*self),

            // else...
            _ => None,
        }
    }

    /// Returns whether the key set contains the key
    fn contains(&self, key_event: &KeyEvent) -> bool {
        match self {
            KeySet::Any(mods) => match key_event.code {
                KeyCode::Char(_) if &key_event.mods == mods => true,
                _ => false,
            },
            KeySet::Range(lo, hi, mods) => match key_event.code {
                KeyCode::Char(c) if &key_event.mods == mods && (*lo..=*hi).contains(&c) => true,
                _ => false,
            },
            KeySet::Single(ev) => ev == key_event,
        }
    }
}

impl<I> AnnotatedComponent<I> {
    fn debug_as_component<'a>(&'a self) -> impl 'a + Debug {
        struct AsComponent<'a, I>(&'a AnnotatedComponent<I>);

        impl<'a, I> Debug for AsComponent<'a, I> {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                use AnnotatedComponentKind::{Atom, Concat, Const, Map, Named, Union};

                match &self.0.kind {
                    Atom { key, repeated } => f
                        .debug_struct("Atom")
                        .field("key", &key)
                        .field("repeated", &repeated)
                        .finish(),
                    Const(comp, _, _) => f
                        .debug_tuple("Const")
                        .field(&comp.debug_as_component())
                        .field(&"_")
                        .finish(),
                    Map(func, comp) => f
                        .debug_tuple("Map")
                        .field(&func)
                        .field(&comp.debug_as_component())
                        .finish(),
                    Concat(cs) => f
                        .debug_tuple("Concat")
                        .field(
                            &cs.iter()
                                .map(|c| c.debug_as_component())
                                .collect::<Vec<_>>(),
                        )
                        .finish(),
                    Union(cs) => f
                        .debug_tuple("Union")
                        .field(
                            &cs.iter()
                                .map(|c| c.debug_as_component())
                                .collect::<Vec<_>>(),
                        )
                        .finish(),
                    Named(n) => f.debug_tuple("Named").field(&n).finish(),
                }
            }
        }

        AsComponent(self)
    }
}

////////////////////////////////////////////////////////////
// impl Display for ...                                   //
////////////////////////////////////////////////////////////

impl Display for KeySet {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use KeySet::{Any, Range, Single};

        match self {
            Single(KeyEvent { mods: None, code }) => match code {
                KeyCode::Char(c) => write!(f, "character {:?}", c),
                _ => write!(f, "key {:?}", code),
            },
            Single(KeyEvent { mods, code }) => match code {
                KeyCode::Char(c) => write!(f, "{:?}+{:?}", mods, c),
                // TODO-FEATURE: we should implement display for KeyCode so that certain cases look
                // better here
                _ => write!(f, "{:?}+{:?}", mods, code),
            },
            Range(lo, hi, None) => write!(f, "{:?} to {:?}", lo, hi),
            Range(lo, hi, Some(mods)) => write!(f, "{:?}+{{{:?} to {:?}}}", mods, lo, hi),
            Any(None) => write!(f, "any character"),
            Any(Some(mods)) => write!(f, "{:?} + any character", mods),
        }
    }
}

////////////////////////////////////////////////////////////
// Serialization                                          //
// ----                                                   //
//   Serializing isn't *too* bad; to make things easier   //
// for us, we convert to a `Component` first, which has   //
// its own implementation of `Serialize` that we piggy-   //
// back off of.                                           //
////////////////////////////////////////////////////////////

impl<I> Serialize for AnnotatedComponent<I> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.normal_component().serialize(serializer)
    }
}

impl<I> AnnotatedComponent<I> {
    fn normal_component(&self) -> Component {
        use AnnotatedComponentKind::{Atom, Concat, Const, Map, Named, Union};
        use Component as Co;

        match &self.kind {
            Union(cs) => Co::Union(
                cs.iter()
                    .map(AnnotatedComponent::normal_component)
                    .collect(),
            ),
            Concat(cs) => Co::Concat(
                cs.iter()
                    .map(AnnotatedComponent::normal_component)
                    .collect(),
            ),
            &Atom { key, repeated } => Co::Atom { key, repeated },
            Map(func, comp) => Co::Map(*func, Box::new(comp.normal_component())),
            Const(comp, original_value, _) => {
                Co::Const(Box::new(comp.normal_component()), original_value.clone())
            }
            Named(name) => Co::Named(name.clone()),
        }
    }
}
