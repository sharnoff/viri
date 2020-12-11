//! Everything keybindings - using, loading, etc.
//!
//! The primary export of this module is the [`KeybindingSet`], which encapsulates the majority of
//! the external usage that might be desired here.
//!
//! The way keybindings are manufactured in the editor is non-trivial. There are a few goals of
//! this system:
//! 1. Keybindings can be built from others - e.g. one way to delete is by the key 'd', followed by
//!    a `Movement`
//! 2. Users can easily define and override keybindings
//! 3. Conflicts between keybindings are disallowed and reported
//!
//! In order to do this, we build keybindings from the bottom up as a **very** limited subset of
//! regular expressions. All keybindings are determined purely from the global configuration file,
//! where they can be constructed in terms of each other. The global keybinding set is given by a
//! union-of-(concatenation-of-(union-of- ... (repetition-of keys) ... )). This allows us to match
//! greedily here, so long as there aren't any keybindings that exist as a prefix of another, e.g.
//! both "d" and "dd". Hence prefix-overlapping (a term I just made up) is not allowed.
//!
//! In addition to the *structure* given here, keybindings are also typed! They start as a simple
//! sequence of atomics (e.g. "[1-9]", "[0-9]*") but can be mapped by [named functions]. Hence a
//! sequence of numbered characters can be transformed to an integer, to later be used in
//! keybindings.
//!
//! For more information on the construction of keybindings, see [`Component`].
//!
//! [named functions]: crate::config::NamedFunction

use crate::any::{Any, BoxedAny, Type};
use crate::config::NamedFunction;
use crate::event::KeyCode;
use crate::macros::async_method;
use maplit::hashset;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
use std::fmt::{self, Debug, Display, Formatter};
use std::marker::PhantomData;

/// A set of keybindings, producing an output of type `T`
///
/// The interface is essentially defined by the methods on this type: [`matches`](Self::matches)
/// and [`output`](Self::output). For information about the internals, refer to the documentation
/// on [`Component`].
///
/// With the usage of this type, there really isn't much more here than meets the eye. Construction
/// is entirely through deserialization.
#[derive(Clone, Deserialize, Serialize)]
#[serde(try_from = "UncheckedKeybindingSet")]
pub struct KeybindingSet<T: Any + Send + Sync> {
    #[serde(skip)]
    keys: AnnotatedComponent,
    #[serde(flatten)]
    inner_unchecked: UncheckedKeybindingSet,
    #[serde(skip)]
    _marker: PhantomData<T>,
}

impl<T: Any + Send + Sync> KeybindingSet<T> {
    /// Returns whether there is a matching keybinding for the input
    #[inline(always)]
    pub fn matches(&self, input: &[KeyEvent]) -> MatchResult {
        self.keys.matches(input)
    }

    /// Produces the output of the keybinding, according to the input
    ///
    /// This will panic if the provided input isn't entirely matched by the component - i.e. if
    /// some input provides a successful [`MatchResult`], the input provided to this function
    /// should be the prefix of that input with the length of the successful match.
    ///
    /// For example:
    /// ```
    /// # struct Foo;
    /// use crate::keys::{KeybindingSet, KeyEvent, MatchResult};
    ///
    /// fn try_match(keybindings: KeybindingSet<Foo>, input: &[KeyEvent]) -> Option<Foo> {
    ///     match keybindings.matches(input) {
    ///         MatchResult::Matched { len } => Some(keybindings.output(&input[..len])),
    ///         _ => None,
    ///     }
    /// }
    /// ```
    pub async fn output(&self, input: &[KeyEvent]) -> T {
        let (len, mut vals) = self.keys.output_consumed(input).await;

        assert!(len == input.len());
        assert!(vals.len() == 1);
        vals.remove(0)
            .try_downcast()
            .map_err(|err| format!("unexpected type returned from keybinding output: {}", err))
            .unwrap()
    }
}

/// An unchecked version of [`KeybindingSet`]; used only for deserialization
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename = "KeybindingSet")]
struct UncheckedKeybindingSet {
    #[serde(flatten)]
    names: HashMap<String, Component>,
    output: Component,
}

/// A clone of [`crate::event::KeyModifiers`] without shifted keys
///
/// All that's left without 'shift' is just 'alt' and 'ctrl'.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub enum KeyModifiers {
    Alt,
    Ctrl,
}

/// A clone of [`crate::event::KeyEvent`] without shifted keys
#[derive(Copy, Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct KeyEvent {
    code: KeyCode,
    mods: Option<KeyModifiers>,
}

/// The individual regex-like piece of the keybinding
///
/// This is the type that's publicly exposed through (de-)serializing configuration files. We
/// validate `Component`s into [`AnnotatedComponent`]s, so that we can directly match on them.
///
/// ## Implementation details
///
/// There's a couple of quirks surrounding `Component`s. One source of inconsistency is due to a
/// lack of runtime type-creation: When we have a concatenation of components, they can be
/// different types. The natural conclusion of this is then that the concatenation `ABC` produces a
/// type that's the 3-tuple `(type(A), type(B), type(C))` (instead of - say - a vector, where all
/// the types must be the same). Unfortunately, because we're determining what the output type of
/// each component should be at *runtime*, we have no way to construct the type corresponding to
/// this tuple - and we **certainly** can't construct the actual value itself. So we compromise.
///
/// Concatenation isn't represented by tuples. Types, in fact, aren't represented as just the type.
/// Everything is given as a *list* of types, which can then be passed as separate arguments to a
/// [`NamedFunction`] when mapping. This is why the method [`validate`](Self::validate), for
/// example, returns a list of types.
///
/// The precise behavior when concatenating two lists of types is to join the lists. No matter the
/// split between the lists, the output type will be the same - i.e.
/// `Concat(Concat(A, B), Concat(C, D))` is the same as  `Concat(A, B, C, D)`)
#[derive(Clone, Debug, Serialize, Deserialize)]
enum Component {
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
}

/// A (minimal) description for sets of [`KeyEvent`](crate::event::KeyEvent)s
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
enum KeySet {
    // Note: range is inclusive, must have lhs <= rhs
    /// A range of characters, pressed under these key modifiers. When used in a [`Component`], the
    /// output type is a character.
    Range(Option<KeyModifiers>, char, char),
    /// A single, raw key event
    Single(KeyEvent),
    /// Any character pressed with the given set of modifiers. If no modifiers are given, then
    /// `Shift` will be allowed as well, because all uppercase letters are shifted. When used in a
    /// [`Component`], the output type is a character.
    Any(Option<KeyModifiers>),
}

/// A [`Component`], annotated with information about its type and how to parse it
///
/// The core functionality provide by this are the [`matches`](Self::matches) and
/// [`output`](Self::output) methods, which check whether an input matches the component and
/// provide the output of a component for given input, respectively.
///
/// Annotated components are constructed with the [`validate`](Component::validate) method.
///
/// This type is essentially the same in structure as [`Component`], but with
/// [`AnnotatedComponentKind`] representing the different variants, and this struct providing
/// additional data.
#[derive(Clone)]
pub struct AnnotatedComponent {
    /// The variant of the original [`Component`]
    kind: AnnotatedComponentKind,

    /// The types of the value this component produces. This is a list due to a quirk with
    /// constructing types at runtime. For more information, see the
    /// [`Component` documentation](Component#implementation-details).
    output_types: Vec<Type>,

    /// The set of keys this component can start with
    // TODO-ALG: this should probably use a more compact representation, but it's *okay* for the
    // time being.
    starts_with: Vec<KeySet>,

    /// The set of keys this component can be followed with, while still continuing the same
    /// component. This can only ever be as a result of an optionally-repeated key at the end of
    /// the component.
    follow_set: Vec<KeySet>,
}

/// A helper for [`AnnotatedComponent`]
///
/// This is structurally equivalent to [`Component`], with extra information coming from the inner
/// `AnnotatedComponent`.
#[derive(Clone)]
enum AnnotatedComponentKind {
    Union(Vec<AnnotatedComponent>),
    Concat(Vec<AnnotatedComponent>),
    Atom { key: KeySet, repeated: bool },
    Map(NamedFunction, Box<AnnotatedComponent>),
}

impl Component {
    /// Returns the list of names this `Component` from the namespace
    fn required_names(&self) -> HashSet<String> {
        use Component::{Atom, Concat, Map, Named, Union};

        match self {
            Named(name) => hashset![name.clone()],
            Atom { .. } => HashSet::new(),
            Map(_, comp) => comp.required_names(),
            Concat(cs) | Union(cs) => cs.iter().map(Component::required_names).flatten().collect(),
        }
    }

    /// Validates the component and returns a version annotated with additional information
    fn validate(
        &self,
        namespace: &HashMap<String, AnnotatedComponent>,
    ) -> Result<AnnotatedComponent, String> {
        use Component::{Atom, Concat, Map, Named, Union};

        // A helper macro for defining the type corresponding to a keyset
        macro_rules! atom_type {
            // @req "KeySet output type" v0
            (Atom { $key:expr, $repeated:expr } match { $($pat:pat => $ty:ty, )* }) => {{
                match $key {$(
                    $pat if $repeated => vec![Type::new::<Vec<$ty>>()],
                    $pat => vec![Type::new::<$ty>()],
                )*}
            }}
        }

        match self {
            Named(name) => Ok(namespace
                .get(name)
                .expect(&format!(
                    "unexpected lack of name '{}' in keybinding set",
                    name
                ))
                .clone()),
            Union(components) => Component::validate_union(&components, namespace),
            Concat(components) => Component::validate_concat(&components, namespace),
            Map(func, component) => {
                let annotated = component.validate(namespace)?;

                func.correct_input_types(annotated.output_types.iter().cloned())
                    .map_err(|e| e.to_string())?;
                Ok(AnnotatedComponent {
                    output_types: annotated.output_types.clone(),
                    starts_with: annotated.starts_with.clone(),
                    follow_set: annotated.follow_set.clone(),
                    kind: AnnotatedComponentKind::Map(*func, Box::new(annotated)),
                })
            }
            Atom { key, repeated } => {
                key.validate_if_ranged()?;
                // @def "KeySet output type" v0
                let output_types = atom_type!(Atom { key, *repeated } match {
                    KeySet::Range { .. } => char,
                    KeySet::Single(_) => KeyEvent,
                    KeySet::Any(_) => char,
                });

                Ok(AnnotatedComponent {
                    output_types,
                    starts_with: vec![*key],
                    follow_set: match repeated {
                        true => vec![*key],
                        false => vec![],
                    },
                    kind: AnnotatedComponentKind::Atom {
                        key: *key,
                        repeated: *repeated,
                    },
                })
            }
        }
    }

    fn validate_union(
        components: &[Component],
        namespace: &HashMap<String, AnnotatedComponent>,
    ) -> Result<AnnotatedComponent, String> {
        if components.is_empty() {
            return Err("empty union of components".to_owned());
        }

        // Step 0: validate all sub-components
        let annotated_comps: Vec<_> = (components.iter())
            .map(|c| c.validate(namespace))
            .collect::<Result<_, _>>()?;

        // Step 1: Check that all of the output types are the same:
        let output_types = match &annotated_comps[..] {
            [] => unreachable!(),
            [head, tail @ ..] => {
                let non_eq_type = tail
                    .iter()
                    .find(|comp| comp.output_types != head.output_types);

                if let Some(comp) = non_eq_type {
                    return Err(format!(
                        "Mismatched type: expected {}, found {}",
                        display_types(&head.output_types),
                        display_types(&comp.output_types)
                    ));
                }

                head.output_types.clone()
            }
        };

        // Step 2: Check that no two starting sets overlap (and create the new one)
        //
        // For each starting set, we'll additionally store a reference to the component it came
        // from, in case we find any overlaps.
        let mut new_starting_set = <Vec<(&AnnotatedComponent, KeySet)>>::new();
        for comp in &annotated_comps {
            for key_set in &comp.starts_with {
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

            new_starting_set.extend(comp.starts_with.iter().cloned().map(|ks| (comp, ks)));
        }

        let starts_with = new_starting_set.into_iter().map(|(_c, ks)| ks).collect();

        // Step 3: Merge the follow sets
        let follow_set = annotated_comps
            .iter()
            .map(|c| c.follow_set.clone())
            .flatten()
            .collect();

        Ok(AnnotatedComponent {
            output_types,
            starts_with,
            follow_set,
            kind: AnnotatedComponentKind::Union(annotated_comps),
        })
    }

    fn validate_concat(
        components: &[Component],
        namespace: &HashMap<String, AnnotatedComponent>,
    ) -> Result<AnnotatedComponent, String> {
        if components.is_empty() {
            return Err("empty concatentation of components".to_owned());
        }

        // Step 0: validate all sub-components
        let annotated_comps: Vec<_> = (components.iter())
            .map(|c| c.validate(namespace))
            .collect::<Result<_, _>>()?;

        // Step 1: Check that the follow-set of each component doesn't intersect with the starting
        // set of the next:
        for (comp, next_comp) in annotated_comps.iter().zip(&annotated_comps[1..]) {
            for key_set in &comp.follow_set {
                let nonempty_intersection = (next_comp.starts_with.iter())
                    .filter_map(|ks| key_set.intersect(ks))
                    .next();
                if let Some(int) = nonempty_intersection {
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

        // Step 2: Produce the output type(s)
        let output_types = annotated_comps
            .iter()
            .map(|c| c.output_types.iter().cloned())
            .flatten()
            .collect();

        Ok(AnnotatedComponent {
            output_types,
            starts_with: annotated_comps[0].starts_with.clone(),
            follow_set: annotated_comps.last().unwrap().follow_set.clone(),
            kind: AnnotatedComponentKind::Concat(annotated_comps),
        })
    }
}

fn display_types(types: &[Type]) -> String {
    assert!(!types.is_empty());

    if types.len() == 1 {
        return types[0].name().to_owned();
    }

    let mut s = format!("Seq[{} ", types[0].name());
    types[1..].iter().for_each(|t| {
        s.push_str(", ");
        s.push_str(t.name());
    });
    s.push(']');
    s
}

impl KeySet {
    fn validate_if_ranged(&self) -> Result<(), String> {
        use KeySet::{Any, Range, Single};

        match self {
            Range(_mods, lower, upper) if lower > upper => Err(format!(
                "invalid key range; lower key '{}' > '{}'",
                lower, upper
            )),
            Single(_) | Any(_) | Range(_, _, _) => Ok(()),
        }
    }

    /// Returns the intersection between the two key sets, if it isn't empty
    fn intersect(&self, other: &KeySet) -> Option<KeySet> {
        use KeySet::{Any, Range, Single};

        match (self, other) {
            // (Any, *)
            (Any(mod_self), Any(mod_other)) if mod_self == mod_other => Some(*self),
            (Any(mods), Single(key)) | (Single(key), Any(mods)) if mods == &key.mods => {
                Some(Single(*key))
            }
            (Any(mods), Range(rmods, low, hi)) | (Range(rmods, low, hi), Any(mods))
                if mods == rmods =>
            {
                Some(Range(*rmods, *low, *hi))
            }

            // (Range, *)
            (Range(xmods, xlow, xhi), Range(ymods, ylow, yhi)) if xmods == ymods => {
                if xlow <= yhi {
                    Some(Range(*xmods, *xlow, *xhi.min(yhi)))
                } else if ylow <= xhi {
                    Some(Range(*xmods, *ylow, *xhi.min(yhi)))
                } else {
                    None
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
            KeySet::Range(mods, lo, hi) => match key_event.code {
                KeyCode::Char(c) if &key_event.mods == mods && (*lo..=*hi).contains(&c) => true,
                _ => false,
            },
            KeySet::Single(ev) => ev == key_event,
        }
    }
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

/// The result of matching an input string on an [`AnnotatedComponent`]
///
/// This is produced by the [`match`](AnnotatedComponent::match) method. Wherever a conclusive
/// result is given, the number of keys required to reach that result is given as well.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum MatchResult {
    NeedsMore,
    Matched { len: usize },
    NoMatch { len: usize },
}

// TODO-CLEAN: The two methods defined below are very similar. This could probably be refactored to
// reduce duplication here.
impl AnnotatedComponent {
    /// Returns whether the given input matches the component
    fn matches(&self, input: &[KeyEvent]) -> MatchResult {
        use AnnotatedComponentKind::{Atom, Concat, Map, Union};
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
            Map(_, comp) => comp.matches(input),
            Union(comps) => {
                for c in comps {
                    if c.starts_with.iter().any(|ks| ks.contains(&input[0])) {
                        return c.matches(input);
                    }
                }

                NoMatch { len: 1 }
            }
            #[rustfmt::skip]
            Concat(comps) => {
                let mut consumed = 0;
                for c in comps {
                    match c.matches(&input[consumed..]) {
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
    async fn output_consumed<'a>(&'a self, input: &'a [KeyEvent]) -> (usize, Vec<BoxedAny>) {
        use AnnotatedComponentKind::{Atom, Concat, Map, Union};
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
            Map(func, comp) => {
                let (n, output) = comp.output_consumed(input).await;
                let out = func.apply(output).await;
                (n, vec![out])
            }
            Concat(comps) => {
                let mut outs = Vec::new();
                let mut len = 0;
                for c in comps {
                    let (n, vs) = c.output_consumed(&input[len..]).await;
                    outs.extend(vs);
                    len += n;
                }

                (len, outs)
            }
            Union(comps) => {
                for c in comps {
                    if c.starts_with.iter().any(|ks| ks.contains(&input[0])) {
                        return c.output_consumed(input).await;
                    }
                }

                unreachable!()
            }
        }
    }
}

////////////////////////////////////////////////////////////
// Component-like debug for AnnotatedComponent            //
////////////////////////////////////////////////////////////

impl AnnotatedComponent {
    fn debug_as_component<'a>(&'a self) -> impl 'a + Debug {
        struct DebugAsComponent<'a>(&'a AnnotatedComponent);

        impl Debug for DebugAsComponent<'_> {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                use AnnotatedComponentKind::*;

                match &self.0.kind {
                    Union(comps) => {
                        let v: Vec<_> = comps
                            .iter()
                            .map(AnnotatedComponent::debug_as_component)
                            .collect();
                        f.debug_tuple("Union").field(&v).finish()
                    }
                    Concat(comps) => {
                        let v: Vec<_> = comps
                            .iter()
                            .map(AnnotatedComponent::debug_as_component)
                            .collect();
                        f.debug_tuple("Concat").field(&v).finish()
                    }
                    Atom { key, repeated } => f
                        .debug_struct("Atom")
                        .field("key", key)
                        .field("repeated", repeated)
                        .finish(),
                    Map(func, comp) => f
                        .debug_tuple("Map")
                        .field(func)
                        .field(&comp.debug_as_component())
                        .finish(),
                }
            }
        }

        DebugAsComponent(self)
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
            Range(None, lo, hi) => write!(f, "{:?} to {:?}", lo, hi),
            Range(Some(mods), lo, hi) => write!(f, "{:?}+{{{:?} to {:?}}}", mods, lo, hi),
            Any(None) => write!(f, "any character"),
            Any(Some(mods)) => write!(f, "{:?} + any character", mods),
        }
    }
}

////////////////////////////////////////////////////////////
// impl Debug for KeybindingSet                           //
////////////////////////////////////////////////////////////

// TODO-CORRECTNESS: Why does this require the 'static bound on T?
impl<T: 'static + Any + Send + Sync> Debug for KeybindingSet<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("KeybindingSet")
            .field("keys", &"...")
            .field("inner", &self.inner_unchecked)
            .finish()
    }
}

////////////////////////////////////////////////////////////
// Conversion `UncheckedKeybindingSet` -> `KeybindingSet` //
////////////////////////////////////////////////////////////

impl<T: Any + Send + Sync> TryFrom<UncheckedKeybindingSet> for KeybindingSet<T> {
    type Error = String;

    fn try_from(set: UncheckedKeybindingSet) -> Result<Self, String> {
        let all_names: HashSet<_> = set.names.iter().map(|(n, _)| n).collect();

        // Store the remaining requirements for each component in the set.
        let mut requirements = (set.names)
            .iter()
            .map(|(name, comp)| {
                let reqs = comp.required_names();
                match reqs.iter().find(|s| !all_names.contains(s)) {
                    Some(n) => Err(format!("No keybinding component with name {:?}", n)),
                    None => Ok((name.clone(), reqs)),
                }
            })
            .collect::<Result<HashMap<String, HashSet<String>>, _>>()?;

        // (and double-check that the output component doesn't make any unrecognized references)
        let output_reqs = set.output.required_names();
        if let Some(n) = output_reqs.into_iter().find(|s| !all_names.contains(&s)) {
            return Err(format!("No keybinding component with name {:?}", n));
        }

        // And we'll construct the items in the namespace as we go.
        //
        // After validating each component, we remove it from the list of requirements on each
        // component. We then choose the next one by picking the first component with no remaining
        // requirements.
        let mut checked_components = HashMap::new();

        while let Some((n, _)) = requirements.iter().find(|(_, reqs)| reqs.is_empty()) {
            let comp = set.names.get(n).unwrap();
            let annotated = comp.validate(&checked_components)?;
            let name: String = n.clone();
            checked_components.insert(name.clone(), annotated);
            drop(n);

            requirements
                .iter_mut()
                .map(|(_, set)| set)
                .for_each(|set| drop(set.remove(&name)));
        }

        // If there's any remaining components still with requirements, there was a circular
        // dependency
        if requirements.iter().any(|(_, reqs)| !reqs.is_empty()) {
            return Err("".to_owned());
        }

        // We now have the *full* component responsible for constructing everything -- we don't
        // need the intermediate `checked_components` after this.
        let final_keys = set.output.validate(&checked_components)?;

        // Check that the output is of type `T`:
        let expected_type = vec![Type::new::<T>()];
        if final_keys.output_types != expected_type {
            return Err(format!(
                "mismatched keybinding set types: expected `{}`, got `{}`",
                display_types(&expected_type),
                display_types(&final_keys.output_types),
            ));
        }

        Ok(KeybindingSet {
            keys: final_keys,
            inner_unchecked: set,
            _marker: PhantomData,
        })
    }
}

////////////////////////////////////////////////////////////
// Testing!                                               //
////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use super::*;

    // TODO
    // Categories: check correctly recognizing overlaps, run a couple examples. Also verify that
    // `try_from` doesn't permit trailing

    fn single_atom(key: char, repeated: bool, mods: Option<KeyModifiers>) -> Component {
        Component::Atom {
            key: KeySet::Single(KeyEvent {
                code: KeyCode::Char(key),
                mods,
            }),
            repeated,
        }
    }

    // Check that empty unions / concats are not allowed
    #[test]
    fn fails_empty() {
        todo!()
    }

    // Check that overlaps between starting sub-components are not allowed
    #[test]
    fn fails_from_overlap() {
        use Component::*;

        let component = Union(vec![
            Concat(vec![
                single_atom('a', false, None),
                single_atom('b', false, None),
            ]),
            Concat(vec![
                single_atom('a', false, None),
                single_atom('c', false, None),
            ]),
        ]);

        let msg = match component.validate(&HashMap::new()) {
            Err(msg) => msg,
            Ok(_) => panic!("erroneous lack of error"),
        };

        assert!(msg.starts_with(
            "conflict in starting sets for keybinding components; character 'a' in both "
        ));
    }

    // Check that overlap is ok with different key modifiers
    #[test]
    fn overlap_different_mods_ok() {
        use Component::*;

        let component = Union(vec![
            Concat(vec![
                single_atom('a', false, None),
                single_atom('b', false, None),
            ]),
            Concat(vec![
                single_atom('a', false, Some(KeyModifiers::Alt)),
                single_atom('c', false, None),
            ]),
        ]);

        let _ = component
            .validate(&HashMap::new())
            .expect("different modifiers should not overlap");
    }

    // Create some sample output
    #[test]
    fn correct_output() {
        use crate::macros::named;

        #[derive(Debug, PartialEq, Eq)]
        struct Foo {
            c: char,
            cs: Vec<char>,
            k: KeyEvent,
        }

        #[named("create-foo")]
        fn create_foo(c: char, cs: Vec<char>, k: KeyEvent) -> Foo {
            Foo { c, cs, k }
        }

        use Component::*;

        #[rustfmt::skip]
        let component = Map(
            NamedFunction::try_from("create-foo").unwrap(),
            Box::new(Concat(vec![
                // single 'a..d'
                Atom { key: KeySet::Range(None, 'a', 'd'), repeated: false },
                // any length 'efg...'
                Atom { key: KeySet::Range(None, 'e', 'g'), repeated: true },
                // trailing '<Enter>'
                Atom {
                    key: KeySet::Single(KeyEvent {
                        code: KeyCode::Enter,
                        mods: None,
                    }),
                    repeated: false,
                },
            ])),
        );

        let comp = component.validate(&HashMap::new()).unwrap();

        #[rustfmt::skip]
        let input = vec![
            KeyEvent { code: KeyCode::Char('a'), mods: None },
            KeyEvent { code: KeyCode::Char('f'), mods: None },
            KeyEvent { code: KeyCode::Char('e'), mods: None },
            KeyEvent { code: KeyCode::Char('g'), mods: None },
            KeyEvent { code: KeyCode::Enter, mods: None },
            // Add an extra key event at the end, that we *don't* use
            KeyEvent { code: KeyCode::Char('t'), mods: None },
        ];

        assert_eq!(comp.matches(&input), MatchResult::Matched { len: 5 });

        let (len, mut out) = crate::runtime::block_on(comp.output_consumed(&input));
        assert!(out.len() == 1);

        let out: Foo = out
            .remove(0)
            .try_downcast()
            .map_err(|err| format!("unexpected output type: {}", err))
            .unwrap();

        assert_eq!(len, 5);

        assert_eq!(
            out,
            Foo {
                c: 'a',
                cs: vec!['f', 'e', 'g'],
                k: KeyEvent {
                    code: KeyCode::Enter,
                    mods: None
                }
            }
        );
    }
}
