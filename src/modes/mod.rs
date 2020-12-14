//! Various cursor modes, mode-switching, and handling of the mode stack
//!
//! To explain the purpose of this module, it's first worth describing what a "mode" actually is.
//! For the purposes of this module, a mode is an abstract interface, taking in a set of key
//! events and emitting commands to execute. These are collected into a "mode set", which
//! additionally handles switching between modes within the set.
//!
//! [`Mode`]s are generic over the output type; the output type is only required to have some way to
//! extract information about switching modes and limit

use crate::any::{Any, DynClone, TypedFnMap};
use crate::event::KeyEvent;
use crate::keys::KeybindingSet;
use crate::macros::id;
use smallvec::SmallVec;
use std::collections::HashMap;
use std::mem;
use std::sync::Arc;

mod ser_de;

/// A distinct set of [`Mode`]s; the primary executor for mode inputs
///
/// Constructing a `ModeSet` is done from a hashmap of each mode's name and a way to construct its
/// keybindings, using the [`ModeSet::new`] method.
#[derive(Clone)]
pub struct ModeSet<T: ModeOutput> {
    // Each individual mode in the set, represented by its name and the keybindings it's constructed
    // from
    set: Vec<(String, Arc<KeybindingSet<T>>)>,

    // The indices in `set` corresponding to each named mode
    index: HashMap<String, ModeKind>,

    // The current mode, alongside its name
    current: Mode<T>,

    // Stored for serialization; the first mode that we start with
    original_starting_mode: ModeKind,
}

/// An individual keybinding mode
///
/// These are typically only accessed as part of a [`ModeSet`]. For more information on how `Mode`s
/// work, refer to the [module-level documentation](self).
#[derive(Clone)]
pub struct Mode<T: ModeOutput> {
    // The user-defined name of the mode
    name: String,
    kind: ModeKind,
    // Any unprocessed input
    input: Vec<KeyEvent>,
    keys: Arc<KeybindingSet<T>>,
}

id! {
    /// A unqiue identifier for types of `Mode`s within a [`ModeSet`]
    ///
    /// Typical usage of these only exists as an argument to the [`KeybindingSet`] constructors
    /// given in [`ModeSet::new`], but `ModeKind`s can also be generated by the [`ModeSet::kind`]
    /// method.
    ///
    /// The interface here is intentionally restricted so that changing modes can be made infallible
    /// after program startup.
    pub struct ModeKind in <T: ModeOutput> [(String, Arc<KeybindingSet<T>>)];
}

/// A marker trait for types that may be used as a command output for [`Mode`]s
pub trait ModeOutput: 'static + Any + Send + Sync + Sized {
    /// The set of types this might allow to be converted under a namspace of `Mode`s.
    ///
    /// Types satisfying this can be represented very compactly; the documentation for
    /// [`FromWithModesSet`] explains this complex trait clearly.
    type WithModesSet: FromWithModesSet;

    /// If the output allows switching to a new mode, returns the mode that it switched to
    ///
    /// Switching modes will be respected, even if there
    // @def switch-modes-respected v0
    fn as_switch_mode(&self) -> Option<ModeKind>;

    /// Indicates that this output will cause a switch to a different [`ModeSet`] (typically a
    /// different signifying a different [`View`])
    ///
    /// This is used to end the batch of input processing early if that's the case.
    fn switches_provider(&self) -> bool;

    /// An error constructor, used to indicate that there was no matching keybinding for the
    /// provided input
    fn make_failed(keys: Vec<KeyEvent>) -> Self;
}

type ConstMap<'a> = TypedFnMap<&'a HashMap<String, ModeKind>>;

/// A marker trait for a set of types that implement [`TryFromWithModes`]
///
/// This is only used for providing the functionality required from [`ModeOutput::WithModesSet`].
/// The documentation here serves to (1) describe the goal of this trait, and (2) describe how it's
/// achieved.
///
/// ## The goal
///
/// When deserializing a [`ModeSet`], we require a set of types that can use a namespace of
/// available modes to convert into a validated type (e.g. `String` -> `ModeKind`). Treating this
/// as a set allows arbitrary types to be deserialized in this manner. Typically, this is done with
/// generic types, e.g. [`crate::view::Command`]:
/// ```
// @req view::Command v0
/// enum Command<T, M = ModeKind> {
///     ChangeMode(M),
///     // ... other commands ...
/// }
/// ```
/// The conversion here is from `Command<T, String>` to `Command<T, ModeKind>`, so that all mode
/// changes at runtime are already known to be valid (instead of allowing arbitrary strings to be
/// used, which we'd have no way of validating).
///
/// So the goal here is to provide a useful abstraction for the set of these mappings. We can't
/// just use `inventory` like some other applications; the generic parameters here make that
/// particular solution inviable.
///
/// ## The implementation
///
/// The actual way we achieve this goal is by requiring each [`ModeOutput`] to provide a list of
/// types that perform this sort of namespace'd conversion. The purpose of *this* trait is to allow
/// that list to take many forms; it can be a single type implementing [`TryFromWithModes`] or a
/// tuple of [`FromWithModesSet`]s. From these two alone, we get recursive lists - a crucial
/// feature for handling generics, as seen above.
///
/// These are given by the blanket implementations for `T: TryFromWithModes` and tuples - up to
/// length 8 - where each element implements `FromWithModesSet`.
pub trait FromWithModesSet {
    /// Adds all internal conversion functions to the map
    fn add_all(map: &mut ConstMap);
}

impl<T> FromWithModesSet for T
where
    T: TryFromWithModes + DynClone,
    T::Input: Any + Send + Sync,
{
    fn add_all(map: &mut ConstMap) {
        map.insert(|modes, input| T::try_from_with_modes(input, modes));
    }
}

// Implements `FromWithModesSet` for tuples of various sizes
macro_rules! impl_tuples {
    ($head:ident, $($tail:ident,)*) => {
        impl<$head, $($tail,)*> FromWithModesSet for ($head, $($tail,)*)
        where
            $head: FromWithModesSet,
            $($tail: FromWithModesSet,)*
        {
            fn add_all(map: &mut ConstMap) {
                $head::add_all(map);
                $($tail::add_all(map);)*
            }
        }
    };
    () => {
        /// The implementation for the empty tuple does nothing, and is included for completeness
        impl FromWithModesSet for () {
            fn add_all(_: &mut ConstMap) {}
        }
    };
}

impl_tuples!(A, B, C, D, E, F, G, H,);

impl TryFromWithModes for crate::utils::Never {
    type Input = Self;

    fn try_from_with_modes(this: Self, _: &HashMap<String, ModeKind>) -> Result<Self, String> {
        match this {}
    }
}

impl TryFromWithModes for ModeKind {
    type Input = String;

    fn try_from_with_modes(
        input: String,
        modes: &HashMap<String, ModeKind>,
    ) -> Result<Self, String> {
        match modes.get(&input) {
            Some(mode) => Ok(*mode),
            None => Err(format!("No mode with name {:?}", input)),
        }
    }
}

/// A trait for conversion under the namespace of [`ModeKind`]s
///
/// This type is used for deserializing [`ModeSet`]s, as a bound on the intermediate values
/// produced for constants in [`KeybindingSet`]s.
pub trait TryFromWithModes: Sized {
    /// The type to be deserialized
    type Input;

    /// Try to convert the types, with the namespace as context
    fn try_from_with_modes(
        input: Self::Input,
        modes: &HashMap<String, ModeKind>,
    ) -> Result<Self, String>;
}

/// (*Internal*) Indicates the result of an attempted keybinding match
enum MatchResult<T> {
    Ok(T),
    NeedsMore,
    Failed(Vec<KeyEvent>),
}

impl<T: ModeOutput> ModeSet<T> {
    /// Returns a unique identifier for the `Mode` with the given name in this set
    ///
    /// If there is no mode with that name in the set, this method returns `None`. It is the
    /// responsibility of the caller to handle resulting errors.
    pub fn kind(&self, name: &str) -> Option<ModeKind> {
        self.index.get(name).cloned()
    }

    /// Returns a reference to the name of the current mode
    pub fn current_mode_name(&self) -> &str {
        &self.current.name
    }

    /// Returns a reference to the keys that are currently waiting to be consumed
    ///
    /// If this list is non-empty, it indicates that the `ModeSet` is waiting for more input in
    /// order to determine what to do.
    pub fn current_buffer(&self) -> &[KeyEvent] {
        &self.current.input
    }

    /// Processes a batch of inputs, returning the relevant outputs, if any
    ///
    /// This function typically returns zero or one outputs of type `T`, and no unprocessed key
    /// events. In order to speed up processing of large sequences of key events (which do
    /// sometimes occur), we allow processing many at a time, returning the full set of outputs.
    /// If a keybinding is waiting on more input, the keys so far will be stored in a local buffer
    /// here until the next call to `get_outputs`.
    ///
    /// The [`switches_provider`] method on [`ModeOutput`] gives a way to stop early, if one of the
    /// outputs in the batch would change the handler for the rest of the input. Switching modes is
    /// not included in this.
    ///
    /// Batches will also stop early if no keybinding is found for a prefix of the provided input,
    /// in order to report the error as part of the output. (Note that the input is still appended
    /// to whatever input may be left in the buffer.
    ///
    /// Because of batching, it is not necessarily the case that returning an output indicates
    /// there are not more keys waiting. This can only be guaranteed if the ending output value
    /// either (a) satisfies [`switches_provider`], or (b) is constructed with
    /// [`ModeOutput::make_failed`] (indicating that there was no applicable keybinding to the
    /// start of the input).
    ///
    /// This function is `async` because evaluating keybindings may involve calling user-defined
    /// named functions, which are `async`.
    ///
    /// [`switches_provider`]: ModeOutput::switches_provider
    pub async fn get_outputs(
        &mut self,
        input: impl IntoIterator<Item = KeyEvent>,
    ) -> (Vec<KeyEvent>, SmallVec<[T; 1]>) {
        // First, pass the input along to the inner mode to be able to handle
        self.current.input.extend(input);

        // A flag to handle when exiting the loop below - if true, we need to return all inputs to
        // the caller.
        let mut clear_buffer = false;

        let mut output = <SmallVec<[T; 1]>>::new();

        loop {
            match self.current.get_output().await {
                MatchResult::Ok(t) => output.push(t),
                MatchResult::Failed(ks) => {
                    output.push(T::make_failed(ks));
                    // The keybinding failed; return the rest of the input to the caller so they
                    // can decide what to do about it
                    clear_buffer = true;
                    break;
                }
                MatchResult::NeedsMore => break,
            }

            // We only get to this point in the loop if we just got a successful match. We now need
            // to check for things about that value.
            let last_output = output.last().unwrap();

            // First up, we check if this requires switching modes. We perform this action, even if
            // the value *also* switches providers.
            //   @req switch-modes-respected v0
            if let Some(kind) = last_output.as_switch_mode() {
                let (name, keys) = self.set[kind].clone();
                let new_mode = Mode::new(name, kind, keys);
                let old = mem::replace(&mut self.current, new_mode);
                self.current.input = old.input;
            }

            // And then, if we need to exit, we do:
            if last_output.switches_provider() {
                clear_buffer = true;
                break;
            }
        }

        let mut returned_keys = Vec::new();
        if clear_buffer {
            returned_keys = mem::replace(&mut self.current.input, Vec::new());
        }

        (returned_keys, output)
    }
}

impl<T: ModeOutput> Mode<T> {
    /// (*Internal*) Constructs a new `Mode`, given the name and keybindings
    fn new(name: impl Into<String>, kind: ModeKind, keys: Arc<KeybindingSet<T>>) -> Self {
        Mode {
            name: name.into(),
            kind,
            input: Vec::new(),
            keys,
        }
    }

    /// (*Internal*) Gets the output from this `Mode`, removing the consumed keys from the internal
    /// buffer if the keybinding is not waiting for more.
    ///
    /// In other words, keys will be consumed if the match succeeds or fails; they will not be
    /// consumed if the `KeybindingSet` is looking for more.
    async fn get_output(&mut self) -> MatchResult<T> {
        use crate::keys::MatchResult::{Matched, NeedsMore, NoMatch};

        match self.keys.matches(&self.input) {
            NeedsMore => MatchResult::NeedsMore,
            Matched { len } => {
                let output = self.keys.output(&self.input[..len]).await;
                self.input.drain(..len);
                MatchResult::Ok(output)
            }
            NoMatch { len } => MatchResult::Failed(self.input.drain(..len).collect()),
        }
    }
}

////////////////////////////////////////////////////////////
// Testing ---------------------------------------------- //
////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};

    // Some sample output for use in tests
    #[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
    enum SampleOutput<T, M = ModeKind> {
        NoKeybinding(Vec<KeyEvent>),
        SwitchMode(M),
        SwitchProvider,
        SwitchModeAndProvider(M),
        Success(T),
    }

    impl<T> TryFromWithModes for SampleOutput<T> {
        type Input = SampleOutput<T, String>;

        fn try_from_with_modes(
            input: Self::Input,
            modes: &HashMap<String, ModeKind>,
        ) -> Result<Self, String> {
            use SampleOutput::*;

            let no_mode = |string| format!("no mode with name {:?}", string);

            let this = match input {
                NoKeybinding(ks) => NoKeybinding(ks),
                SwitchMode(m) => match modes.get(&m) {
                    Some(id) => SwitchMode(*id),
                    None => return Err(no_mode(m)),
                },
                SwitchProvider => SwitchProvider,
                SwitchModeAndProvider(m) => match modes.get(&m) {
                    Some(id) => SwitchModeAndProvider(*id),
                    None => return Err(no_mode(m)),
                },
                Success(v) => Success(v),
            };

            Ok(this)
        }
    }

    impl<T: Clone + Any + Send + Sync> ModeOutput for SampleOutput<T> {
        type WithModesSet = Self;

        fn as_switch_mode(&self) -> Option<ModeKind> {
            use SampleOutput::{SwitchMode, SwitchModeAndProvider};

            match self {
                SwitchMode(m) | SwitchModeAndProvider(m) => Some(*m),
                _ => None,
            }
        }

        fn switches_provider(&self) -> bool {
            use SampleOutput::{SwitchModeAndProvider, SwitchProvider};

            matches!(self, SwitchProvider | SwitchModeAndProvider(_))
        }

        fn make_failed(keys: Vec<KeyEvent>) -> Self {
            SampleOutput::NoKeybinding(keys)
        }
    }

    // A simple working demo.
    //
    // This works in a few stages, checking the output and current state of the mode set after
    // each. That way, we can check a range of functionalities within a single test.
    //
    // We're using a very simple set of modes: there's just two: "foo" and "bar", with different
    // keybindings. Both have a way way to generate each one of the four non-failure outputs given
    // above:
    //     SwitchMode, SwitchProvider, SwitchModeAndProvider, and Success
    // The keybindngs are a mix of lengths - some single-letter keybindings and other
    // multi-letters. They're created by mapping the constants for two `KeybindingSet`s to provide
    //
    // TODO-FEATURE: This test is waiting on additional features to be added to `KeybindingSet`s -
    // namely allowing constants.
    #[test]
    fn simple_working_demo() {
        macro_rules! concat_lines {
            ($($line:expr),* $(,)?) => {{
                concat!($($line, "\n",)*)
            }}
        }

        #[crate::macros::named("modes::test::fst")]
        fn fst(x: char, _: char) -> char {
            x
        }

        #[crate::macros::named("modes::test::success")]
        fn success(x: char) -> SampleOutput<char> {
            SampleOutput::Success(x)
        }

        #[crate::macros::named("modes::test::make_number")]
        fn make_number(head: char, tail: Vec<char>) -> u32 {
            let base = '0' as u32;
            let mut n = head as u32 - base;
            tail.into_iter().fold(n, |n, c| n * 10 + (c as u32) - base)
        }

        #[crate::macros::named("modes::test::add_to_char")]
        fn add_to_char(x: u32, c: char) -> char {
            std::char::from_u32(c as u32 + x).unwrap()
        }

        let yaml_str = concat_lines!(
            "mode_names: ['first', 'second', 'third']",
            "start_with: 'first'",
            "modes:",
            "  first:",
            "    base:",
            "      Union:",
            "      - Const:",
            "        - Atom: { key: { Single: { code: { Char: 'a' } } } }",
            "        - { SwitchMode: 'second' }",
            "      - Map:",
            "        - 'modes::test::success'",
            "        - Map:",
            "          - 'modes::test::fst'",
            "          - Concat:",
            "            - Atom: { key: { Range: ['b', 'd'] } }",
            "            - Atom: { key: { Range: ['e', 'f'] } }",
            "    parts: {}",
            "  second:",
            "    base:",
            "      Const:",
            "      - Atom: { key: { Single: { code: { Char: 'g' } } } }",
            "      - { SwitchModeAndProvider: 'third' }",
            "    parts: {}",
            "  third:",
            "    base:",
            "      Union:",
            "      - Map:",
            "        - 'modes::test::success'",
            "        - Map:",
            "          - 'modes::test::add_to_char'",
            "          - Concat:",
            "            - Named: 'numeric'",
            "            - Atom: { key: { Range: ['A', 'C'] } }",
            "      - Const:",
            "        - Atom: { key: { Single: { code: { Char: 's' } } } }",
            "        - SwitchProvider",
            "      - Const:",
            "        - Atom: { key: { Single: { code: { Char: 'F' } } } }",
            "        - { SwitchMode: 'first' }",
            "    parts:",
            "      numeric:",
            "        Map:",
            "        - 'modes::test::make_number'",
            "        - Concat:",
            "          - Atom: { key: { Range: ['1', '9'] } }",
            "          - Atom: { key: { Range: ['0', '9'] }, repeated: true }",
        );

        crate::macros::register_DynClone!(SampleOutput<char, String>);

        // Deserialize that string:
        let mut mode_set: ModeSet<SampleOutput<char>> = serde_yaml::from_str(&yaml_str)
            .unwrap_or_else(|e| panic!("failed to deserialize: {}", e));

        macro_rules! get_outputs {
            ($inputs:expr) => {{
                let (keys, outs) = crate::runtime::block_on({
                    let iter = $inputs.chars().map(|c| KeyEvent {
                        code: crate::event::KeyCode::Char(c),
                        mods: None,
                    });

                    mode_set.get_outputs(iter)
                });

                (keys, outs, mode_set.current_mode_name())
            }};
        }

        use SampleOutput::*;

        const FIRST: ModeKind = ModeKind(0);
        const SECOND: ModeKind = ModeKind(1);
        const THIRD: ModeKind = ModeKind(2);

        // (input, remaining keys, output, ending mode name)
        #[rustfmt::skip]
        static SEQUENCE: &[(&str, &str, &[SampleOutput<char>], &str)] = &[
            ("beagF", "F", &[
                Success('b'),
                SwitchMode(SECOND),
                SwitchModeAndProvider(THIRD),
                // Because we "switched" providers, the last 'F' doesn't go through.
            ], "third"),

            // Setting up a numeric sequence in the third mode:
            ("3", "", &[], "third"),
            ("2", "", &[], "third"),
            // 'B' + 32 = 'b':
            ("B", "", &[Success('b')], "third"),
        ];

        for (inp, expected_keys, expected_output, ending_mode) in SEQUENCE.iter() {
            let expected_keys = expected_keys
                .chars()
                .map(|c| KeyEvent {
                    code: crate::event::KeyCode::Char(c),
                    mods: None,
                })
                .collect::<Vec<_>>();

            let (keys, output, mode) = get_outputs!(inp);

            assert_eq!(keys, expected_keys);
            assert_eq!(output.as_slice(), *expected_output);
            assert_eq!(mode, *ending_mode);
        }
    }
}