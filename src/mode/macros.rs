//! A collection of macros used for generating boilerplate involving all possible modes

macro_rules! modes {
    (
        $(#[$modes_attrs:meta])*
        $modes_vis:vis enum $modes:ident<$param:ident, Conf> {
            $($variant:ident/$sub_mod:ident: $var_ty:ty,)+
        }

        $(#[$kind_attrs:meta])*
        $kind_vis:vis enum $kind:ident = ...;

        $(#[$set_attrs:meta])*
        $set_vis:vis struct $set:ident = ...;
    ) => {
        $(pub mod $sub_mod;)*

        $(#[$kind_attrs])*
        $kind_vis enum $kind {
            $($variant,)+
        }

        $(#[$modes_attrs])*
        $modes_vis enum $modes<$param, Conf>
        where config::ExtConfig<Conf>: config::ExtendsCfg<$param> + ConfigPart,
        {
            $($variant($var_ty),)*
        }

        $(#[$set_attrs])*
        $set_vis struct $set {
            $($sub_mod: bool,)+
        }

        $(impl<$param, Conf> XFrom<$var_ty> for $modes<$param, Conf>
        where config::ExtConfig<Conf>: config::ExtendsCfg<$param> + ConfigPart,
        {
            fn xfrom(mode: $var_ty) -> Self {
                Self::$variant(mode)
            }
        })+

        impl<T, Conf> XFrom<$kind> for $modes<T, Conf>
        where config::ExtConfig<Conf>: config::ExtendsCfg<$param> + ConfigPart,
        {
            fn xfrom(kind: $kind) -> Self {
                match kind {
                    $($kind::$variant => Self::$variant(<$var_ty>::default()),)+
                }
            }
        }

        impl<T, Conf> $modes<T, Conf>
        where config::ExtConfig<Conf>: config::ExtendsCfg<$param> + ConfigPart,
        {
            fn kind(&self) -> $kind {
                match self {
                    $(Self::$variant(_) => $kind::$variant,)+
                }
            }
        }

        impl<$param, Conf> $modes<$param, Conf>
        where config::ExtConfig<Conf>: config::ExtendsCfg<$param> + ConfigPart,
              $param: 'static + Clone,
              Conf: 'static,
        {
            fn try_handle(&mut self, key: KeyEvent) -> Result<Vec<Cmd<$param>>, Error> {
                match self { $(Self::$variant(m) => m.try_handle(key),)+ }
            }

            fn cursor_style(&self) -> CursorStyle {
                match self { $(Self::$variant(m) => m.cursor_style(),)+ }
            }

            fn expecting_input(&self) -> bool {
                match self { $(Self::$variant(m) => m.expecting_input(),)+ }
            }

            fn try_name(&self) -> Option<&'static str> {
                match self { $(Self::$variant(_) => <$var_ty as Mode<_,_>>::NAME,)+ }
            }
        }

        impl $set {
            /// Produces a new set, where no modes are included
            pub fn none() -> Self {
                Self {
                    $($sub_mod: false,)+
                }
            }

            /// Produces a new set where all modes are included
            pub fn all() -> Self {
                Self {
                    $($sub_mod: true,)+
                }
            }

            /// Marks the given mode as being allowed
            pub fn allow(self, mode: $kind) -> Self {
                match mode {
                    $($kind::$variant => Self { $sub_mod: true, .. self },)+
                }
            }

            /// Marks the given mode as being forbidden
            pub fn forbid(self, mode: $kind) -> Self {
                match mode {
                    $($kind::$variant => Self { $sub_mod: false, .. self },)+
                }
            }

            /// Returns whether the set contains the given `ModeKind`
            pub fn contains(&self, kind: $kind) -> bool {
                match kind {
                    $($kind::$variant => self.$sub_mod,)+
                }
            }
        }
    }
}

macro_rules! mode_config_types {
    (
        $(#[$base_attrs:meta])*
        $base_vis:vis struct $base_cfg:ident {
            $($field_vis:vis $sub_mod:ident: $base_ty:ty => $ext_ty:ty,)+
        }

        $(#[$ext_attrs:meta])*
        $ext_vis:vis struct $ext_cfg:ident<$param:ident> = ...;
    ) => {
        $(#[$base_attrs])*
        $base_vis struct $base_cfg {
            $($field_vis $sub_mod: $base_ty,)+
        }

        $(#[$ext_attrs])*
        $ext_vis struct $ext_cfg<$param> {
            pub parent: ConfigParent<$param>,
            $($field_vis $sub_mod: $ext_ty,)+
        }
    }
}
