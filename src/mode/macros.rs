//! A collection of macros used for generating mode-switching boilerplate

macro_rules! modes {
    (
        $(#[$kind_attrs:meta])*
        $kind_vis:vis enum $kind:ident = ...;

        $(#[$set_attrs:meta])*
        $set_vis:vis struct $set:ident = ...;

        $(#[$modes_attrs:meta])*
        $modes_vis:vis enum $modes:ident<$param:ident> {
            $($variant:ident/$field:ident: $var_ty:ty,)+
        }
    ) => {
        /// An enumeration over the different types of available modes.
        ///
        /// This type implements
        // FIXME: Document
        $(#[$kind_attrs])*
        $kind_vis enum $kind {
            $($variant,)+
        }

        /// A standin type that may be any of the available modes
        // FIXME: Document
        $(#[$modes_attrs])*
        $modes_vis enum $modes<$param> {
            $($variant($var_ty),)*
        }

        /// A marker for which modes may be transitioned to by a handler
        // FIXME: Document
        $(#[$set_attrs])*
        $set_vis struct $set {
            $($field: bool,)+
        }

        $(impl<$param> XFrom<$var_ty> for $modes<$param> {
            fn xfrom(mode: $var_ty) -> Self {
                Self::$variant(mode)
            }
        })+

        impl<T> XFrom<$kind> for $modes<T> {
            fn xfrom(kind: $kind) -> Self {
                match kind {
                    $($kind::$variant => Self::$variant(<$var_ty>::default()),)+
                }
            }
        }

        impl<T> $modes<T> {
            fn kind(&self) -> $kind {
                match self {
                    $(Self::$variant(_) => $kind::$variant,)+
                }
            }
        }

        impl<$param: 'static> $modes<$param> {
            fn try_handle(&mut self, key: KeyEvent) -> Result<Seq<Cmd<$param>>, Error> {
                match self { $(Self::$variant(m) => m.try_handle(key),)+ }
            }

            fn cursor_style(&self) -> CursorStyle {
                match self { $(Self::$variant(m) => m.cursor_style(),)+ }
            }

            fn expecting_input(&self) -> bool {
                match self { $(Self::$variant(m) => m.expecting_input(),)+ }
            }

            fn try_name(&self) -> Option<&'static str> {
                match self { $(Self::$variant(_) => <$var_ty as Mode<_>>::NAME,)+ }
            }
        }

        impl $set {
            /// Produces a new set, where no modes are included
            pub fn none() -> Self {
                Self {
                    $($field: false,)+
                }
            }

            /// Produces a new set where all modes are included
            pub fn all() -> Self {
                Self {
                    $($field: true,)+
                }
            }

            /// Marks the given mode as being allowed
            pub fn allow(self, mode: $kind) -> Self {
                match mode {
                    $($kind::$variant => Self { $field: true, .. self },)+
                }
            }

            /// Marks the given mode as being forbidden
            pub fn forbid(self, mode: $kind) -> Self {
                match mode {
                    $($kind::$variant => Self { $field: false, .. self },)+
                }
            }

            /// Returns whether the set contains the given `ModeKind`
            pub fn contains(&self, kind: $kind) -> bool {
                match kind {
                    $($kind::$variant => self.$field,)+
                }
            }
        }
    }
}
