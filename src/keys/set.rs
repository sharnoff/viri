//! Wrapper module for [`KeybindingSet`] and [`UncheckedKeybindingSet`]

use super::{AnnotatedComponent, Info, MatchResult};
use crate::any::{Any, Type};
use crate::event::KeyEvent;
use serde::Serialize;
use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;

/// A set of keybindings, producing an output of type `T`
///
/// This type is typically not touched by user code; the standard setup leaves everything to go
/// through [`crate::modes::ModeSet`]. That being said, this is all documented to make the program
/// easier to explore.
///
/// The interface is essentially defined by the methods on this type: [`matches`](Self::matches)
/// and [`output`](Self::output). For information about the internals, refer to the documentation
/// on [`Component`].
///
/// With the usage of this type, there really isn't much more here than meets the eye. Construction
/// is entirely through deserialization, both inherently and through dedicated methods.
/// Serialization stores the original deserialized values, and so no customization is needed.
#[derive(Clone, Serialize)]
#[serde(bound = "T: Any + Send + Sync")]
// @def "KeybindingSet fields" v0
pub struct KeybindingSet<T: Any + Send + Sync, I = Info> {
    pub(super) base: AnnotatedComponent<I>,
    #[serde(rename = "parts")]
    pub(super) namespace: HashMap<String, AnnotatedComponent<I>>,
    #[serde(skip)]
    pub(super) _marker: PhantomData<T>,
}

impl<T: Any + Send + Sync> KeybindingSet<T> {
    /// Returns whether there is a matching keybinding for the input
    pub fn matches(&self, input: &[KeyEvent]) -> MatchResult {
        self.base.matches(input, &self.namespace)
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
    /// async fn try_match(keybindings: KeybindingSet<Foo>, input: &[KeyEvent]) -> Option<Foo> {
    ///     match keybindings.matches(input) {
    ///         MatchResult::Matched { len } => Some(keybindings.output(&input[..len]).await),
    ///         _ => None,
    ///     }
    /// }
    /// ```
    pub async fn output(&self, input: &[KeyEvent]) -> T {
        let (len, mut vals) = self.base.output_consumed(input, &self.namespace).await;

        assert!(len == input.len());
        assert!(vals.len() == 1);
        vals.remove(0)
            .try_downcast()
            .map_err(|err| format!("unexpected type returned from keybinding output: {}", err))
            .unwrap()
    }
}

impl<T: Any + Send + Sync> KeybindingSet<T, Vec<Type>> {
    /// Validates the `KeybindingSet`, returning one with additional information attached
    ///
    /// This is used as the final step in deserializing a `KeybindingSet`.
    pub(super) fn validate<E>(mut self) -> Result<KeybindingSet<T>, E>
    where
        E: serde::de::Error,
    {
        use serde::de::Error;

        // There's just a couple things we need to do here.
        //
        // The first is to check that all referenced values are present within the list of ones
        // that were required. We'll do this with an additional run through the components (even
        // though this list is often computed beforehand - it's better to isolate
        // responsibilities).

        let all_names = self.namespace.keys().collect::<Vec<_>>();

        // Store the remaining requirements for each component in the set:
        //
        // We don't need to check that the set of names referenced are all valid, because that's
        // done at deserialization time.
        let mut requirements = (self.namespace)
            .iter()
            .map(|(name, comp)| {
                let mut reqs = HashSet::new();
                comp.required_names(&mut reqs);
                (name.to_owned(), reqs)
            })
            .collect::<HashMap<_, _>>();

        // We then go through the list of components, validating each one by one, as soon as we
        // have all of the requirements validated.
        //
        // After validating a component, we remove it from all remaining requirements sets. If we
        // get to a point where there are still components remaining but none without requirements,
        // we know there's a cycle; we'll report an error.
        //
        // This is mostly about constructing the starting-key- and follow-sets for each component,
        // which may produce errors.
        let mut checked_components = HashMap::new();

        while let Some((n, _)) = requirements.iter().find(|(_, reqs)| reqs.is_empty()) {
            let comp = self.namespace.remove(n).unwrap();
            let annotated = comp.validate(&checked_components).map_err(Error::custom)?;
            let name: String = n.clone();
            checked_components.insert(name.clone(), annotated);
            drop(n);

            requirements
                .iter_mut()
                .map(|(_, set)| set)
                .for_each(|set| drop(set.remove(&name)));
            requirements.remove(&name);
        }

        if requirements.iter().any(|(_, reqs)| !reqs.is_empty()) {
            return Err(Error::custom(
                "keybinding set has cyclic dependencies between named components",
            ));
        }

        // After this, the only thing we have left to do is to perform the same procedure with the
        // base component:
        let base = (self.base)
            .validate(&checked_components)
            .map_err(Error::custom)?;

        Ok(KeybindingSet {
            base,
            namespace: checked_components,
            _marker: PhantomData,
        })
    }
}
