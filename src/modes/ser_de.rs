//! Wrapper module for [`ModeSet`] serialization and deserialization
//!
//! In general, the type that we use for (de-)serialization is actually:
//! ```ignore
//! struct ModeSet<T> {
//!     mode_names: Vec<String>,
//!     start_with: String,
//!     modes: HashMap<String, KeybindingSet<T>>,
//! }
//! ```
//! The fields *must* be stored in this order, because the list of mode names is required in order
//! to actually parse `modes`.

use super::{FromWithModesSet, Mode, ModeKind, ModeOutput, ModeSet};
use crate::any::{Type, TypedFnMap};
use crate::keys::KeybindingSet;
use serde::de::{DeserializeSeed, Error, MapAccess, SeqAccess, Visitor};
use serde::ser::{SerializeMap, SerializeSeq, SerializeStruct};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::HashMap;
use std::fmt::{self, Formatter};
use std::marker::PhantomData;
use std::sync::Arc;

///////////////////
// Serialization //
///////////////////

impl<T: ModeOutput> Serialize for ModeSet<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        struct ModeNames<'a, T: ModeOutput>(&'a [(String, Arc<KeybindingSet<T>>)]);

        struct Modes<'a, T: ModeOutput>(&'a [(String, Arc<KeybindingSet<T>>)]);

        impl<'a, T: ModeOutput> Serialize for ModeNames<'a, T> {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                let mut seq = serializer.serialize_seq(Some(self.0.len()))?;
                for (name, _) in self.0 {
                    seq.serialize_element(name)?;
                }
                seq.end()
            }
        }

        impl<'a, T: ModeOutput> Serialize for Modes<'a, T> {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                let mut map = serializer.serialize_map(Some(self.0.len()))?;
                for (name, elem) in self.0 {
                    map.serialize_entry(name, elem)?;
                }
                map.end()
            }
        }

        // @def "ModeSet field ordering" v0
        let mut state = serializer.serialize_struct("ModeSet", 3)?;
        state.serialize_field("mode_names", &ModeNames(&self.set))?;
        state.serialize_field("start_with", &self.set[self.original_starting_mode].0)?;
        state.serialize_field("modes", &Modes(&self.set))?;
        state.end()
    }
}

/////////////////////
// Deserialization //
/////////////////////

struct ModeSetVisitor<T>(PhantomData<T>);

static MODE_SET_FIELDS: &[&str] = &["mode_names", "start_with", "modes"];

#[derive(Deserialize)]
#[serde(field_identifier, rename_all = "snake_case")]
enum ModeSetField {
    ModeNames,
    Modes,
}

impl<'de, T: ModeOutput> Deserialize<'de> for ModeSet<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_struct(
            "ModeSet",
            MODE_SET_FIELDS,
            ModeSetVisitor::<T>(PhantomData),
        )
    }
}

impl<'de, T: ModeOutput> Visitor<'de> for ModeSetVisitor<T> {
    type Value = ModeSet<T>;

    fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
        write!(
            formatter,
            "struct `ModeSet` with output type `{}`",
            Type::new::<T>().name()
        )
    }

    fn visit_seq<V>(self, mut seq: V) -> Result<ModeSet<T>, V::Error>
    where
        V: SeqAccess<'de>,
    {
        // @req "ModeSet field ordering" v0
        //
        // We read fields in the order given above:
        // 1. mode_names,
        // 2. start_with,
        // 3. modes,

        let index = seq
            .next_element_seed(ModeNamesVisitor)?
            .ok_or_else(|| Error::invalid_length(0, &"struct `ModeSet` with three fields"))?;

        let start_with: String = seq
            .next_element()?
            .ok_or_else(|| Error::invalid_length(1, &"struct `ModeSet` with three fields"))?;

        let original_starting_mode = match index.get(&start_with) {
            Some(kind) => *kind,
            None => return Err(Error::custom("starting mode must be inside the given list")),
        };

        let seed = ModeMapVisitor {
            index: &index,
            marker: PhantomData,
        };

        let set = seq
            .next_element_seed(seed)?
            .ok_or_else(|| Error::invalid_length(2, &"struct `ModeSet` with three fields"))?;

        let (name, keyset) = &set[original_starting_mode];
        let current = Mode::new(name, original_starting_mode, keyset.clone());

        Ok(ModeSet {
            set,
            index,
            current,
            original_starting_mode,
        })
    }

    fn visit_map<V>(self, mut map: V) -> Result<ModeSet<T>, V::Error>
    where
        V: MapAccess<'de>,
    {
        #[derive(Deserialize)]
        #[serde(field_identifier, rename_all = "snake_case")]
        enum Field {
            ModeNames,
            StartWith,
            Modes,
        }

        let mut index = None;
        let mut original_starting_mode = None;
        let mut set = None;

        while let Some(field) = map.next_key()? {
            match field {
                // Check for duplicates:
                Field::ModeNames if index.is_some() => {
                    return Err(Error::duplicate_field("mode_names"))
                }
                Field::StartWith if original_starting_mode.is_some() => {
                    return Err(Error::duplicate_field("start_with"))
                }
                Field::Modes if set.is_some() => return Err(Error::duplicate_field("modes")),

                Field::ModeNames => index = Some(map.next_value_seed(ModeNamesVisitor)?),
                // Individually, `modes` and `start_with` both require that `index` is present
                Field::StartWith => {
                    let index = index.as_ref().ok_or_else(|| {
                        Error::custom("`start_with` must come after `mode_names`")
                    })?;

                    let start_with: String = map.next_value()?;

                    match index.get(&start_with) {
                        Some(kind) => original_starting_mode = Some(*kind),
                        None => {
                            return Err(Error::custom(
                                "starting mode must be inside the given list",
                            ))
                        }
                    }
                }
                Field::Modes => {
                    let index = index
                        .as_ref()
                        .ok_or_else(|| Error::custom("`modes` must come after `mode_names`"))?;
                    let seed = ModeMapVisitor {
                        index,
                        marker: PhantomData,
                    };

                    set = Some(map.next_value_seed(seed)?);
                }
            }
        }

        let (index, original_starting_mode, set) = match (index, original_starting_mode, set) {
            (Some(i), Some(start), Some(set)) => (i, start, set),
            (None, _, _) => return Err(Error::missing_field("mode_names")),
            (_, None, _) => return Err(Error::missing_field("start_with")),
            (_, _, None) => return Err(Error::missing_field("modes")),
        };

        let (name, keyset) = &set[original_starting_mode];
        let current = Mode::new(name, original_starting_mode, keyset.clone());

        Ok(ModeSet {
            set,
            index,
            current,
            original_starting_mode,
        })
    }
}

struct ModeNamesVisitor;

impl<'de> DeserializeSeed<'de> for ModeNamesVisitor {
    // This is actually deserialized as a `Vec<String>` without duplicates
    type Value = HashMap<String, ModeKind>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_seq(self)
    }
}

impl<'de> Visitor<'de> for ModeNamesVisitor {
    type Value = HashMap<String, ModeKind>;

    fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
        formatter.write_str("a list of strings")
    }

    fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
    where
        V: SeqAccess<'de>,
    {
        let mut names = HashMap::new();
        let mut count = 0;

        while let Some(name) = seq.next_element()? as Option<String> {
            if names.insert(name.clone(), ModeKind(count)).is_some() {
                return Err(Error::custom(format!("duplicate named entry {:?}", name)));
            }

            count += 1;
        }

        Ok(names)
    }
}

struct ModeMapVisitor<'a, T> {
    index: &'a HashMap<String, ModeKind>,
    marker: PhantomData<T>,
}

impl<'a, 'de, T: ModeOutput> DeserializeSeed<'de> for ModeMapVisitor<'a, T> {
    type Value = Vec<(String, Arc<KeybindingSet<T>>)>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_map(self)
    }
}

impl<'a, 'de, T: ModeOutput> Visitor<'de> for ModeMapVisitor<'a, T> {
    type Value = Vec<(String, Arc<KeybindingSet<T>>)>;

    fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
        write!(
            formatter,
            "map of `String` -> `KeybindingSet<{}>`",
            Type::new::<T>().name(),
        )
    }

    fn visit_map<V>(self, mut map: V) -> Result<Self::Value, V::Error>
    where
        V: MapAccess<'de>,
    {
        let mut modes = Vec::new();
        modes.extend((0..self.index.len()).map(|_| (String::new(), None)));

        self.index
            .iter()
            .for_each(|(name, &ModeKind(idx))| modes[idx].0 = name.to_owned());

        while let Some(name) = map.next_key()? as Option<String> {
            let idx = match self.index.get(&name) {
                Some(&ModeKind(idx)) => idx,
                None => return Err(Error::custom(format!("no mode with name {:?}", name))),
            };

            let mode = map.next_value_seed(KeysetVisitor::<T>(self.index, PhantomData))?;
            modes[idx].1 = Some(mode);
        }

        modes
            .into_iter()
            .map(|(name, keyset)| match keyset {
                Some(k) => Ok((name, Arc::new(k))),
                None => Err(Error::custom(format!("missing entry for mode {:?}", name))),
            })
            .collect()
    }
}

struct KeysetVisitor<'a, T>(&'a HashMap<String, ModeKind>, PhantomData<T>);

impl<'a, 'de, T: ModeOutput> DeserializeSeed<'de> for KeysetVisitor<'a, T> {
    type Value = KeybindingSet<T>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        let mut consts_map = TypedFnMap::new();
        <T::WithModesSet as FromWithModesSet>::add_all(&mut consts_map);
        // ModeKind is the only type we automatically add, because it can't be incorrect to have
        // here.
        <ModeKind as FromWithModesSet>::add_all(&mut consts_map);

        KeybindingSet::deserialize(deserializer, &consts_map, self.0)
    }
}
