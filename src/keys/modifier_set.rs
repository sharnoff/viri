//! Wrapper module for the [`ModifierSet`] type
#![allow(non_upper_case_globals)]

use crate::event::KeyModifiers;
use bitflags::bitflags;
use std::ops::Add;

bitflags! {
    pub struct ModifierSet: u8 {
        const None    = 0b0000_0000;
        const Alt     = 0b0000_0001;
        const Ctrl    = 0b0000_0010;
        const AltCtrl = 0b0000_0100;
    }
}

impl Add for ModifierSet {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        // Redefining the constants so that we can use them in the patterns here.
        const None: ModifierSet = ModifierSet::None;
        const Alt: ModifierSet = ModifierSet::Alt;
        const Ctrl: ModifierSet = ModifierSet::Ctrl;
        const AltCtrl: ModifierSet = ModifierSet::AltCtrl;

        match (self, other) {
            (Alt, Ctrl) | (Ctrl, Alt) => AltCtrl,
            (None, x) | (x, None) => x,
            (AltCtrl, _) | (_, AltCtrl) => AltCtrl,
            (Alt, Alt) => Alt,
            (Ctrl, Ctrl) => Ctrl,
            _ => panic!("cannot add complex `ModifierSet`s"),
        }
    }
}

impl From<KeyModifiers> for ModifierSet {
    fn from(mods: KeyModifiers) -> Self {
        match mods {
            KeyModifiers::Alt => Self::Alt,
            KeyModifiers::Ctrl => Self::Ctrl,
            KeyModifiers::AltCtrl => Self::AltCtrl,
        }
    }
}

impl From<Option<KeyModifiers>> for ModifierSet {
    fn from(mods: Option<KeyModifiers>) -> Self {
        if let Some(m) = mods {
            m.into()
        } else {
            Self::None
        }
    }
}
