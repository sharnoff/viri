//! Deserialization for all keybinding-relevant components

use super::{AnnotatedComponent, AnnotatedComponentKind, KeySet, KeybindingSet};
use crate::any::{Any, Type, TypedFnMap};
use crate::config::NamedFunction;
use serde::de::{
    self, DeserializeSeed, Deserializer, EnumAccess, Error, MapAccess, SeqAccess, Visitor,
};
use serde::Deserialize;
use std::collections::HashMap;
use std::fmt::{self, Formatter};
use std::marker::PhantomData;

// README.
//
// Hey. This file is a bit of a mess - that's okay. It's doing some weird-ass shit: sharing mutable
// state across serde visitors, type-checking from the top-down (!), and others.
//
// My recommendation is not not poke your head in here for too long, if you value your sanity. If
// you do decide to venture into these deep, dark depths, you'll find a few things to guide your
// way:
//
//  1. Every section is very clearly labeled
//  2. Just because this file doesn't generate documentation for rustdoc, it doesn't mean that it's
//     been entirely abandoned - I've tried to provide brief explanations of what things do and why
//     they're there.
//  3. You have the following explanation of the architecture:
//
// -- Architecture --
//
// (Note: Instead of referring to them as `AnnotatedComponent`s, they're just called `Component`s
//  everwhere for simplicity.)
//
// This is all so complex because of a single core problem: the constants we deserialize in
// `Component::Const` can be any type -- and we don't know what that type needs to be until later.
// There's an easier solution that would have been *wonderful* - if it actually worked:
//
//    For the easy solution, whenever you need to deserialize a constant, you instead store the
//    deserializer and return a closure that has type `FnOnce(Type) -> Result<BoxedAny, ...>`. This
//    would be a perfect solution, except we aren't guaranteed the lifetime on the `Deserializer`
//    in order to make this happen.
//
// So without that possible plan of attack, we know that we can't delay deserialization at all - we
// need to know before deserializing what the type is. That restriction means that everything has
// to be top-down. And from that perspective, there's no sense in performing other validation
// post-deserializing (like checking follow-sets, for example); we're already doing most if it here.
//
// The top-down design manifests in a couple different ways:
//
//  * We record type restrictions for named components *as we use them*. If a named component is
//    required to be two different types, it's an error. Using a named component requires that it
//    be *already defined* when we come across a component that uses it.
//
//  * Relatedly: Named components can only output a single type (not multiple). When we're
//    deserializing a `Concat`, we don't know beforehand which components occupy which windows of
//    the list of types, and so we have to partially restrict those before handing everything back
//    up.
//
//  * Because of concat windowing, we need to "send up" information about componets as we get it.
//    This is why all of the visitors for `Component`s have a parent visitor stored: its job is to
//    relay and double-check new information about types.
//
// Well hopefully that helps at least a bit -- enjoy :)

// It's pretty critical that this be synched with the actual definition of `AnnotatedComponent`
// @req "Component variants" v0
static COMPONENT_VARIANTS: &[&str] = &["Union", "Concat", "Atom", "Map", "Named", "Const"];

// @req "KeybindingSet fields" v0
static KEYBINDING_SET_FIELDS: &[&str] = &["base", "parts"];

// @req "Component::Atom fields" v0
static ATOM_FIELDS: &[&str] = &["key", "repeated"];

////////////////////////////////////////////////////////////
// Env                                                    //
// ----                                                   //
// Managing the shared environment for use within         //
// `KeybindingVisitor` and the various `Component`        //
// visitors                                               //
////////////////////////////////////////////////////////////

// The environment required from a `KeybindingSet` in order to deserialize a `Component`. As we
// create the `Component`, we derive the requirements on other named components.
//
// If we find a conflict, that's an error. If there's any components that are used but never
// defined, that's also an error.
pub struct Env<'a, Ctx> {
    consts_map: &'a TypedFnMap<Ctx>,
    ctx: Ctx,
    required_types: HashMap<String, Type>,
}

impl<'a, Ctx: Copy> Env<'a, Ctx> {
    // Creates the environemnt from the set of constants required
    fn from_consts(ctx: Ctx, consts_map: &'a TypedFnMap<Ctx>) -> Self {
        Env {
            consts_map,
            ctx,
            required_types: HashMap::new(),
        }
    }

    // Adds a requirement to the environment, returning an error if it failed
    fn add_req<E: Error>(&mut self, name: &str, ty: Type) -> Result<(), E> {
        let old_ty = match self.required_types.insert(name.to_owned(), ty) {
            Some(t) if t != ty => t,
            _ => return Ok(()),
        };

        Err(E::custom(format!(
            "named Component {:?} was previously required to be type `{}`, but is required again as `{}`",
            name,
            old_ty.name(),
            ty.name(),
        )))
    }
}

////////////////////////////////////////////////////////////
// `KeybindingSet`                                        //
////////////////////////////////////////////////////////////

impl<T: Any + Send + Sync> KeybindingSet<T> {
    /// (*Internal*) The entrypoint for `KeybidingSet` deserialization
    pub fn deserialize<'de, D, Ctx>(
        deserializer: D,
        consts_map: &TypedFnMap<Ctx>,
        ctx: Ctx,
    ) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
        Ctx: Copy,
    {
        ////////////////////////////////////////
        // KeybindingVisitor                  //
        // ----                               //
        // This is the overall visitor for a  //
        // `KeybindingSet`. Other visitors    //
        // exist for the pieces of this type. //
        ////////////////////////////////////////

        // We'll Define everything inside the function, for the sake of having them grouped nicely
        struct KeybindingVisitor<'a, Ctx, T> {
            consts_map: &'a TypedFnMap<Ctx>,
            ctx: Ctx,
            marker: PhantomData<T>,
        }

        // Because `KeybindingSet` is a struct, we want to implement deserialization for sequences
        // *and* maps. For an different example, see: https://serde.rs/deserialize-struct.html
        //
        // This is basically because most data formats don't really care about structs as a
        // distinct type.
        impl<'a, 'de, Ctx, T> Visitor<'de> for KeybindingVisitor<'a, Ctx, T>
        where
            Ctx: Copy,
            T: Any + Send + Sync,
        {
            type Value = KeybindingSet<T>;

            fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
                write!(
                    formatter,
                    "struct Keybinding set of type `{}`",
                    Type::new::<T>().name()
                )
            }

            // Handle [base, parts..]
            fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
            where
                V: SeqAccess<'de>,
            {
                let mut env = Env::from_consts(self.ctx, self.consts_map);

                let req_ty = [Type::new::<T>()];
                let base_seed = ComponentVisitor {
                    env: &mut env,
                    req_types: KnownType::Exactly(&req_ty),
                };

                // Pass in the environment with `next_element_seed`
                let base = seq
                    .next_element_seed(base_seed)?
                    .ok_or_else(|| Error::invalid_length(0, &self))?;

                // Note: we could have flattened the parts into this sequence, but that adds extra
                // complication that we don't *really* need to deal with; it's not actually worth
                // the hassle.

                let parts = seq
                    .next_element_seed(PartsVisitor { env: &mut env })?
                    .ok_or_else(|| Error::invalid_length(0, &self))?;

                let this = KeybindingSet {
                    base,
                    namespace: parts,
                    _marker: PhantomData,
                };

                this.validate()
            }

            // Handle { "base": _, "parts": .. }
            fn visit_map<V>(self, mut map: V) -> Result<Self::Value, V::Error>
            where
                V: MapAccess<'de>,
            {
                #[derive(Deserialize)]
                #[serde(field_identifier, rename_all = "lowercase")]
                // @req "KeybindingSet fields" v0
                enum Field {
                    Base,
                    Parts,
                }

                let mut env = Env::from_consts(self.ctx, self.consts_map);

                let req_ty = [Type::new::<T>()];
                let base_seed = ComponentVisitor {
                    req_types: KnownType::Exactly(&req_ty),
                    env: &mut env,
                };

                // Check that the next key is `base`:
                match map.next_key()? {
                    None => return Err(Error::missing_field("base")),
                    Some(Field::Parts) => {
                        return Err(Error::custom("'base' field must come before 'parts'"))
                    }
                    Some(Field::Base) => (),
                }

                // And then deserialize that:
                let base = map.next_value_seed(base_seed)?;

                // And then check for `parts`:
                match map.next_key()? {
                    None => return Err(Error::missing_field("parts")),
                    Some(Field::Base) => return Err(Error::duplicate_field("base")),
                    Some(Field::Parts) => (),
                }

                let parts = map.next_value_seed(PartsVisitor { env: &mut env })?;

                let this = KeybindingSet {
                    base,
                    namespace: parts,
                    _marker: PhantomData,
                };

                this.validate()
            }
        }

        ////////////////////////////////////////
        // PartsVisitor                       //
        // ----                               //
        // A visitor for the hashmap of names //
        // to components.                     //
        ////////////////////////////////////////

        struct PartsVisitor<'a, Ctx> {
            env: &'a mut Env<'a, Ctx>,
        }

        impl<'a, 'de, Ctx: Copy> DeserializeSeed<'de> for PartsVisitor<'a, Ctx> {
            type Value = HashMap<String, AnnotatedComponent<Vec<Type>>>;

            fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where
                D: Deserializer<'de>,
            {
                deserializer.deserialize_map(self)
            }
        }

        impl<'a, 'de, Ctx: Copy> Visitor<'de> for PartsVisitor<'a, Ctx> {
            type Value = HashMap<String, AnnotatedComponent<Vec<Type>>>;

            fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
                write!(formatter, "a map of names to `Components`")
            }

            fn visit_map<V>(self, mut map: V) -> Result<Self::Value, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut parts = HashMap::new();

                while let Some(key) = map.next_key()? {
                    if parts.contains_key(&key) {
                        return Err(Error::custom(format!(
                            "duplicate map entries for name {:?}",
                            key
                        )));
                    }

                    let required_type: [Type; 1] = match self.env.required_types.get(&key) {
                        None => {
                            return Err(Error::custom(format!(
                                "named component {:?} defined before it is required",
                                key,
                            )));
                        }
                        Some(t) => [*t],
                    };

                    let visitor = ComponentVisitor {
                        env: self.env,
                        req_types: KnownType::Exactly(&required_type),
                    };
                    parts.insert(key, map.next_value_seed(visitor)?);
                }

                Ok(parts)
            }
        }

        ////////////////////////////////////////
        // Final steps - actually doing it    //
        ////////////////////////////////////////

        let visitor = KeybindingVisitor {
            consts_map,
            ctx,
            marker: PhantomData,
        };

        deserializer.deserialize_struct("KeybindingSet", KEYBINDING_SET_FIELDS, visitor)
    }
}

////////////////////////////////////////////////////////////
// `AnnotatedComponent`                                   //
// ----                                                   //
// The structure here is worth going through.             //
//                                                        //
// Essentially, we have, as the base-level visitor, the   //
// `ComponentVisitor`. This is the entrypoint to          //
// deserializing a `Component`, and every other visitor   //
// here is built on top of those. The `UnionVisitor`, for //
// example, is just defined (ignoring lifetimes) as:      //
//                                                        //
//    pub struct UnionVisitor(ComponentVisitor);          //
//                                                        //
// The difference is that a `UnionVisitor` will           //
// deserialize a list of `Component`s instead of a single //
// one, and carries additional context alongside it. The  //
// other visitors for each `Component` variant are        //
// defined similarly.                                     //
//                                                        //
// There's also some individual tricky things we need to  //
// do to get the variant names, but I'll leave that up to //
// you to discover ;)                                     //
////////////////////////////////////////////////////////////

// The base component visitor
pub struct ComponentVisitor<'e, 'p, Ctx> {
    // We need to have these two lifetimes here because this struct would otherwise "force" the
    // lifetime of the reference `&Env` to have the same lifetime as the underlying `Env` itself.
    // This is *probably* (?) a bug with the borrow-checker, but it's easy enough to deal with
    // here.
    env: &'p mut Env<'e, Ctx>,
    req_types: KnownType<'p>,
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

impl<'e, 'p, Ctx: Copy> ComponentVisitor<'e, 'p, Ctx> {
    // Given the expected set of types that we're about to output
    fn validate_output_types<E: Error>(&self, output_types: &[Type]) -> Result<(), E> {
        match self.req_types {
            KnownType::Exactly(ts) | KnownType::PrefixOf(ts @ [_]) if output_types != ts => {
                Err(Error::custom(format!(
                    "expected output type `{}`, found `{}`",
                    display_types(ts),
                    display_types(output_types),
                )))
            }
            KnownType::PrefixOf(ts) if !ts.starts_with(output_types) => {
                Err(Error::custom(format!(
                    "expected output type as a prefix of `{}`, found `{}`",
                    display_types(ts),
                    display_types(output_types),
                )))
            }
            KnownType::Exactly(_) | KnownType::PrefixOf(_) | KnownType::Unknown => Ok(()),
        }
    }

    // Creates a child `ComponentVisitor` with the same environment, but new type requirements
    fn child<'p2>(&'p2 mut self, req_types: KnownType<'p2>) -> ComponentVisitor<'e, 'p2, Ctx> {
        ComponentVisitor {
            env: self.env,
            req_types,
        }
    }
}

#[derive(Copy, Clone)]
enum KnownType<'p> {
    Exactly(&'p [Type]),
    PrefixOf(&'p [Type]),
    // An unknown type only comes from deserializing within a `Const` map. This largely has the
    // side-effect of preventing nested constants (which is probably a good thing).
    Unknown,
}

impl<'e, 'p, 'de, Ctx: Copy> DeserializeSeed<'de> for ComponentVisitor<'e, 'p, Ctx> {
    type Value = AnnotatedComponent<Vec<Type>>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_enum("Component", COMPONENT_VARIANTS, self)
    }
}

impl<'e, 'p, 'de, Ctx: Copy> Visitor<'de> for ComponentVisitor<'e, 'p, Ctx> {
    type Value = AnnotatedComponent<Vec<Type>>;

    fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
        // TODO-ERROR: we could also give some type information about the component we're
        // expecting - that can be done entirely by changing this message.
        write!(formatter, "enum `Component`")
    }

    fn visit_enum<A>(self, data: A) -> Result<Self::Value, A::Error>
    where
        A: EnumAccess<'de>,
    {
        use de::VariantAccess;

        // In order to deserialize an enum, we essentially need two things: (1) A visitor to drive
        // parsing the names of the variants, and (2) individual visitors for the types within
        // those variants.
        //
        // We're essentially directly copying from the code that serde emits for enum variant
        // parsing, becaues it's actually fairly complex.

        // @req "Component variants" v0
        enum Field {
            Union,
            Concat,
            Atom,
            Map,
            Named,
            Const,
        }

        impl<'de> Deserialize<'de> for Field {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                struct FieldVisitor;

                impl<'de> Visitor<'de> for FieldVisitor {
                    type Value = Field;

                    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        formatter.write_str("variant identifier")
                    }

                    fn visit_u64<E: Error>(self, value: u64) -> Result<Self::Value, E> {
                        // @req "Component variants" v0
                        // @req "Component field ordering" v0
                        match value {
                            0 => Ok(Field::Union),
                            1 => Ok(Field::Concat),
                            2 => Ok(Field::Atom),
                            3 => Ok(Field::Map),
                            4 => Ok(Field::Named),
                            5 => Ok(Field::Const),
                            _ => Err(Error::invalid_value(
                                de::Unexpected::Unsigned(value),
                                &"variant index 0 <= i < 6",
                            )),
                        }
                    }

                    fn visit_str<E: Error>(self, value: &str) -> Result<Self::Value, E> {
                        // @req "Component variants" v0
                        match value {
                            "Union" => Ok(Field::Union),
                            "Concat" => Ok(Field::Concat),
                            "Atom" => Ok(Field::Atom),
                            "Map" => Ok(Field::Map),
                            "Named" => Ok(Field::Named),
                            "Const" => Ok(Field::Const),
                            _ => Err(Error::unknown_variant(value, COMPONENT_VARIANTS)),
                        }
                    }

                    fn visit_bytes<E: Error>(self, value: &[u8]) -> Result<Self::Value, E> {
                        match value {
                            b"Union" => Ok(Field::Union),
                            b"Concat" => Ok(Field::Concat),
                            b"Atom" => Ok(Field::Atom),
                            b"Map" => Ok(Field::Map),
                            b"Named" => Ok(Field::Named),
                            b"Const" => Ok(Field::Const),
                            _ => Err(Error::unknown_variant(
                                &String::from_utf8_lossy(value),
                                COMPONENT_VARIANTS,
                            )),
                        }
                    }
                }

                deserializer.deserialize_identifier(FieldVisitor)
            }
        }

        match data.variant()? {
            (Field::Union, variant) => variant.newtype_variant_seed(UnionVisitor(self)),
            (Field::Concat, variant) => variant.newtype_variant_seed(ConcatVisitor(self)),
            (Field::Atom, variant) => variant.struct_variant(ATOM_FIELDS, AtomVisitor(self)),
            (Field::Map, variant) => variant.tuple_variant(2, MapVisitor(self)),
            (Field::Named, variant) => variant.newtype_variant_seed(NamedVisitor(self)),
            (Field::Const, variant) => variant.tuple_variant(2, ConstVisitor(self)),
        }
    }
}

////////////////////////////////////////
// `UnionVisitor`                     //
////////////////////////////////////////

pub struct UnionVisitor<'e, 'p, Ctx>(ComponentVisitor<'e, 'p, Ctx>);

impl<'e, 'p, 'de, Ctx: Copy> DeserializeSeed<'de> for UnionVisitor<'e, 'p, Ctx> {
    type Value = AnnotatedComponent<Vec<Type>>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_seq(self)
    }
}

impl<'e, 'p, 'de, Ctx: Copy> Visitor<'de> for UnionVisitor<'e, 'p, Ctx> {
    type Value = AnnotatedComponent<Vec<Type>>;

    fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
        // TODO-ERROR: we could also give some type information about the component we're
        // expecting - that can be done entirely by changing this message.
        write!(formatter, "a list of union'd `Component`s")
    }

    fn visit_seq<V>(mut self, mut seq: V) -> Result<Self::Value, V::Error>
    where
        V: SeqAccess<'de>,
    {
        let first_seed = ComponentVisitor {
            env: self.0.env,
            req_types: self.0.req_types,
        };

        let first_value = seq
            .next_element_seed(first_seed)?
            .ok_or_else(|| Error::invalid_length(0, &"expected ≥ 1 elements"))?;

        let output_types = first_value.info.clone();

        // We check the output types here, because all elements in the union must have the same
        // type; we don't want to give an error later because the first one was wrong.
        self.0.validate_output_types(&output_types)?;

        let mut components = vec![first_value];

        let type_reqs = KnownType::Exactly(&output_types);

        loop {
            let next = seq.next_element_seed(self.0.child(type_reqs))?;
            match next {
                None => break,
                Some(c) => {
                    // We don't need to check the output type of the component, because that should
                    // have already been handled internally:
                    components.push(c);
                }
            }
        }

        Ok(AnnotatedComponent {
            kind: AnnotatedComponentKind::Union(components),
            info: output_types,
        })
    }
}

////////////////////////////////////////
// `ConcatVisitor`                    //
////////////////////////////////////////

pub struct ConcatVisitor<'e, 'p, Ctx>(ComponentVisitor<'e, 'p, Ctx>);

impl<'e, 'p, 'de, Ctx: Copy> DeserializeSeed<'de> for ConcatVisitor<'e, 'p, Ctx> {
    type Value = AnnotatedComponent<Vec<Type>>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_seq(self)
    }
}

impl<'e, 'p, 'de, Ctx: Copy> Visitor<'de> for ConcatVisitor<'e, 'p, Ctx> {
    type Value = AnnotatedComponent<Vec<Type>>;

    fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
        // TODO-ERROR: we could also give some type information about the component we're
        // expecting - that can be done entirely by changing this message.
        write!(formatter, "a list of concatenated `Component`s")
    }

    fn visit_seq<V>(mut self, mut seq: V) -> Result<Self::Value, V::Error>
    where
        V: SeqAccess<'de>,
    {
        use KnownType::{Exactly, PrefixOf, Unknown};

        // While deserializing `Concat`, we progressively track the set of types that we use. If we
        // use up all of the types from above without
        let mut output_types = Vec::new();
        let mut components = Vec::new();

        loop {
            let req_types = match self.0.req_types {
                // We need to be careful here: we can't go around handing out empty lists of types,
                // because that'll mess indexing up for other visitors. So we'll just exit the
                // loop, knowing that the caller (the deserializer) will recognize that - if we
                // haven't used all of the items in the sequence - that's an error.
                Exactly([]) | PrefixOf([]) => break,

                // Otherwise, we get the type as expected:
                Exactly(ts) | PrefixOf(ts) => PrefixOf(&ts[output_types.len()..]),

                Unknown => Unknown,
            };

            match seq.next_element_seed(self.0.child(req_types))? {
                Some(e) => {
                    output_types.extend(e.info.iter().cloned());
                    components.push(e);
                }
                None => break,
            };
        }

        // The list of components unfortuantely is required to be non-empty. We'll produce an error
        // if it's empty:
        if components.is_empty() {
            return Err(Error::invalid_length(0, &"must have at least 1 element"));
        }

        self.0.validate_output_types(&output_types)?;

        Ok(AnnotatedComponent {
            kind: AnnotatedComponentKind::Concat(components),
            info: output_types,
        })
    }
}

////////////////////////////////////////
// `AtomVisitor`                      //
// ----                               //
//   Because `Component::Atom` is a   //
// struct, we need to do a little     //
// more than for other visitors; we   //
// field deserialization as well.     //
//   That' all included inside the    //
// function body, for your viewing    //
// pleasure :)                        //
////////////////////////////////////////

pub struct AtomVisitor<'e, 'p, Ctx>(ComponentVisitor<'e, 'p, Ctx>);

impl<'e, 'p, 'de, Ctx: Copy> Visitor<'de> for AtomVisitor<'e, 'p, Ctx> {
    type Value = AnnotatedComponent<Vec<Type>>;

    fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
        // TODO-ERROR: we could also give some type information about the component we're
        // expecting - that can be done entirely by changing this message.
        write!(formatter, "struct variant `Component::Atom`")
    }

    // Handle [key, (optional) repeated]
    fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
    where
        V: SeqAccess<'de>,
    {
        let key: KeySet = seq
            .next_element()?
            .ok_or_else(|| Error::invalid_length(0, &self))?;
        key.validate_if_ranged().map_err(Error::custom)?;

        let repeated: bool = seq.next_element()?.unwrap_or(false);

        let output_type = key.output_type(repeated);
        self.0.validate_output_types(output_type)?;

        Ok(AnnotatedComponent {
            kind: AnnotatedComponentKind::Atom { key, repeated },
            info: output_type.to_vec(),
        })
    }

    // Handle { key: KeySet, (optional) repeated: bool }
    fn visit_map<V>(self, mut map: V) -> Result<Self::Value, V::Error>
    where
        V: MapAccess<'de>,
    {
        // This is essentially the same as what we did for `KeybindingSet`
        #[derive(Deserialize)]
        #[serde(field_identifier, rename_all = "lowercase")]
        enum AtomField {
            Key,
            Repeated,
        }

        let mut key: Option<KeySet> = None;
        let mut repeated: Option<bool> = None;

        while let Some(field) = map.next_key()? {
            match field {
                // Check for duplicates
                AtomField::Key if key.is_some() => return Err(Error::duplicate_field("key")),
                AtomField::Repeated if repeated.is_some() => {
                    return Err(Error::duplicate_field("repeated"))
                }
                // If no duplicates, we're good:
                AtomField::Key => key = Some(map.next_value()?),
                AtomField::Repeated => repeated = Some(map.next_value()?),
            }
        }

        // We check that `key` is present. It's okay if `repeated` isn't, because we'll have that
        // field default to false.
        let key = match key {
            Some(k) => k,
            None => return Err(Error::missing_field("key")),
        };

        let repeated = repeated.unwrap_or(false);

        let output_type = key.output_type(repeated);
        self.0.validate_output_types(output_type)?;

        Ok(AnnotatedComponent {
            kind: AnnotatedComponentKind::Atom { key, repeated },
            info: output_type.to_vec(),
        })
    }
}

////////////////////////////////////////
// `MapVisitor`                       //
////////////////////////////////////////

pub struct MapVisitor<'e, 'p, Ctx>(ComponentVisitor<'e, 'p, Ctx>);

// impl<'e, 'p, 'de> DeserializeSeed<'de> for MapVisitor<'e, 'p> {
//     type Value = AnnotatedComponent<Vec<Type>>;
//
//     fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
//     where
//         D: Deserializer<'de>,
//     {
//         deserializer.deserialize_seq(self)
//     }
// }

impl<'e, 'p, 'de, Ctx: Copy> Visitor<'de> for MapVisitor<'e, 'p, Ctx> {
    type Value = AnnotatedComponent<Vec<Type>>;

    fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
        // TODO-ERROR: we could also give some type information about the component we're
        // expecting - that can be done entirely by changing this message.
        write!(formatter, "tuple variant `Component::Map`")
    }

    // (NamedFunction, Component)
    fn visit_seq<V>(mut self, mut seq: V) -> Result<Self::Value, V::Error>
    where
        V: SeqAccess<'de>,
    {
        let func: NamedFunction = seq.next_element()?.ok_or_else(|| {
            Error::invalid_length(0, &"tuple variant `Component::Map` with 2 elements")
        })?;

        let output_types = vec![func.output_type()];
        self.0.validate_output_types(&output_types)?;

        // With those output types, we now know exactly what the input types to the function must
        // be:
        let type_reqs = KnownType::Exactly(func.input_types());
        // Then just parse the next component:
        let component = seq
            .next_element_seed(self.0.child(type_reqs))?
            .ok_or_else(|| {
                Error::invalid_length(0, &"tuple variant `Component::Map` with 2 elements")
            })?;

        Ok(AnnotatedComponent {
            kind: AnnotatedComponentKind::Map(func, Box::new(component)),
            info: output_types,
        })
    }
}

////////////////////////////////////////
// `NamedVisitor`                     //
////////////////////////////////////////

pub struct NamedVisitor<'e, 'p, Ctx>(ComponentVisitor<'e, 'p, Ctx>);

impl<'e, 'p, 'de, Ctx: Copy> DeserializeSeed<'de> for NamedVisitor<'e, 'p, Ctx> {
    type Value = AnnotatedComponent<Vec<Type>>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        let name: String = Deserialize::deserialize(deserializer)?;

        // If we don't know the type, we don't have any information. So this is an error. (not
        // knowing the type only results from being inside a constant -- this really is a
        // limitation of the system, but users shoudln't need to do that)
        //
        // If we already have the info for what's required by this name, then we actually can
        // continue. :)

        let mut skip_add_req = false;

        let required_type = match self.0.req_types {
            // Note: this requires all instances of `KnownType([..])` to have non-empty lists. This
            // is a strict requirement adhered to elsewhere.
            KnownType::Exactly(ts) | KnownType::PrefixOf(ts) => ts[0],

            // If we don't know the type, but it's already required to be something, we can just
            // take that.
            //
            // Otherwise, this is an error.
            KnownType::Unknown => match self.0.env.required_types.get(&name) {
                Some(t) => {
                    skip_add_req = true;
                    *t
                }
                None => return Err(Error::custom(format!(
                    "Component::Named({:?}) first used without immediate type bounds (inside `Component::Const`)",
                    name,
                ))),
            }
        };

        // add the requirement to the environment:
        if !skip_add_req {
            self.0.env.add_req(&name, required_type)?;
        }

        Ok(AnnotatedComponent {
            kind: AnnotatedComponentKind::Named(name),
            info: vec![required_type],
        })
    }
}

////////////////////////////////////////
// `ConstVisitor`                     //
////////////////////////////////////////

pub struct ConstVisitor<'e, 'p, Ctx>(ComponentVisitor<'e, 'p, Ctx>);

impl<'e, 'p, 'de, Ctx: Copy> Visitor<'de> for ConstVisitor<'e, 'p, Ctx> {
    type Value = AnnotatedComponent<Vec<Type>>;

    fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
        // TODO-ERROR: we could also give some type information about the component we're
        // expecting - that can be done entirely by changing this message.
        write!(formatter, "tuple variant `Component::Const`")
    }

    // (Component, const)
    fn visit_seq<V>(mut self, mut seq: V) -> Result<Self::Value, V::Error>
    where
        V: SeqAccess<'de>,
    {
        let comp = seq
            .next_element_seed(self.0.child(KnownType::Unknown))?
            .ok_or_else(|| {
                Error::invalid_length(0, &"tuple variant `Component::Const` with 2 elements")
            })?;

        let target_type = match self.0.req_types {
            KnownType::Exactly(ts) | KnownType::PrefixOf(ts) => ts[0],
            KnownType::Unknown => return Err(Error::custom("Unknown type for component constant. Note: constants cannot be used inside other components")),
        };

        let ctx = self.0.env.ctx;
        let (original, value) =
            (self.0.env.consts_map).map(ctx, target_type, Error::custom, |ty| {
                seq.next_element_seed(ty)?.ok_or_else(|| {
                    Error::invalid_length(1, &"tuple variant `Component::Const` with 2 elements")
                })
            })?;

        // We don't need to check the output type because it's already given as `target_type`.

        Ok(AnnotatedComponent {
            info: vec![target_type],
            kind: AnnotatedComponentKind::Const(
                Box::new(comp),
                original.into(), // -> Arc<dyn DynClone>
                value.into(),    // -> Arc<dyn DynClone>,
            ),
        })
    }
}
