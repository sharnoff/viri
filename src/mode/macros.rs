//! A collection of macros used for generating boilerplate involving all possible modes
//!
//! The only definitions here are the [`modes`] and [`mode_config_types`] macro, which are both
//! explaind in detail with their respective documentation. These are both used in exactly one
//! place each, with `modes` in 'src/mode/mod.rs' and `mode_config_types` in 'src/mode/config.rs'.
//!
//! [`modes`]: macro.modes.html
//! [`mode_config_types`]: macro.mode_config_types.html

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

/// A macro for generating configuration types.
///
/// The actual usage looks something like:
/// ```
/// mode_config_types! {
///     /// Hopefully there's documentation?
///     #[derive(Default)]
///     pub struct BaseConfig {
///         pub insert: Config => ExtConfig<T>, impl ExtendsCfg<T>, <Ifn>,
///         // -- snip --
///     }
///
///     /// Okay, but what about here?
///     pub struct ExtConfig<T> = ...;
///     pub trait ExtendsCfg<T> {
///         fn parent(&self) -> Option<Box<dyn ExtendsCfg<T>>>;
///         ...
///     }
///
///     fn dyn_extends_cfg<...>(...) -> Box<dyn ExtendsCfg<T>>;
/// }
/// ```
///
/// All of the repetition is handled inside the `BaseConfig` definition-like structure, where each
/// field gives - in order - the name of a mode's submodule, that mode's base configuration type,
/// that mode's extension type, and that mode's extension *trait*. This is fairly complicated, so
/// more information is available in the [`config`] submodule.
///
/// [`config`]: ../config/index.html
macro_rules! mode_config_types {
    (
        $(#[$base_attrs:meta])*
        $base_vis:vis struct $base_cfg:ident {
            $($field_vis:vis $sub_mod:ident: $base_ty:ident => $ext_ty:ident<T>, impl $ext_trait:ident<T>, <$fn_param:ident>,)+
        }

        $(#[$ext_attrs:meta])*
        $ext_vis:vis struct $ext_cfg:ident<T> = ...;

        $(#[$trait_attrs:meta])*
        $trait_vis:vis trait $trait:ident<T> {
            $($fns:item)*
        }

        $(#[$dyn_attrs:meta])*
        $dyn_vis:vis fn $dyn_fn:ident<...>(...) -> Box<dyn $_:ident<T>>;
    ) => {
        $(#[$base_attrs])*
        $base_vis struct $base_cfg {
            // Expands to:
            //   pub insert: insert::Config,
            //   pub normal: normal::Config,
            //   ...
            $($field_vis $sub_mod: $sub_mod::$base_ty,)+
        }

        $(#[$ext_attrs])*
        $ext_vis struct $ext_cfg<T> {
            pub parent: ConfigParent<T>,
            // Expands to:
            //   pub insert: insert::ExtConfig<T>,
            //   pub normal: normal::ExtConfig<T>,
            //   ...
            $($field_vis $sub_mod: $sub_mod::$ext_ty<T>,)+
        }

        $(#[$trait_attrs])*
        $trait_vis trait $trait<T> {
            $($fns)*
            // Expands to:
            //   fn insert<'a>(&'a self) -> Box<dyn 'a + insert::ExtendsCfg<T>>;
            //   fn normal<'a>(&'a self) -> Box<dyn 'a + normal::ExtendsCfg<T>>;
            //   ...
            $(fn $sub_mod<'a>(&'a self) -> Box<dyn 'a + $sub_mod::$ext_trait<T>>;)+
        }

        // A helper function for creating manual trait objects for extension traits
        $dyn_vis fn $dyn_fn<Aux, AuxFn, ParentFn, $($fn_param),+, T>(
            aux_fn: AuxFn,
            parent: ParentFn,
            $($sub_mod: $fn_param,)+
        ) -> Box<dyn $trait<T>>
        where
            AuxFn: 'static + Fn() -> Aux,
            ParentFn: 'static + Fn(Aux) -> Option<Box<dyn $trait<T>>>,
            $($fn_param: 'static + Fn(Aux) -> Box<dyn $sub_mod::$ext_trait<T>>),+,
        {
            // This is the backing struct - it's essentially just a vtable + closure for generating
            // data
            struct DynExt<AuxFn, ParentFn, $($fn_param),+> {
                aux_fn: AuxFn,
                parent: ParentFn,
                $($sub_mod: $fn_param,)+
            }

            impl<Aux, AuxFn, ParentFn, $($fn_param),+, T> $trait<T> for DynExt<AuxFn, ParentFn, $($fn_param),+>
            where
                AuxFn: Fn() -> Aux,
                ParentFn: Fn(Aux) -> Option<Box<dyn $trait<T>>>,
                $($fn_param: 'static + Fn(Aux) -> Box<dyn $sub_mod::$ext_trait<T>>),+,
            {
                fn parent(&self) -> Option<Box<dyn $trait<T>>> {
                    (self.parent)((self.aux_fn)())
                }

                $(fn $sub_mod<'a>(&'a self) -> Box<dyn 'a + $sub_mod::$ext_trait<T>> {
                    (self.$sub_mod)((self.aux_fn)())
                })+
            }

            Box::new(DynExt { aux_fn, parent, $($sub_mod),+ })
        }

        // Implementing the extension trait for base and extension types

        impl<T: Clone> $trait<T> for $base_cfg {
            fn parent(&self) -> Option<Box<dyn $trait<T>>> { None }

            $(fn $sub_mod<'a>(&'a self) -> Box<dyn 'a + $sub_mod::$ext_trait<T>> {
                Box::new(&self.$sub_mod)
            })+
        }

        impl<E, T, D> $trait<T> for D
        where
            D: Deref<Target = E>,
            E: 'static + ExtendsCfg<T>,
        {
            fn parent(&self) -> Option<Box<dyn $trait<T>>> { self.deref().parent() }

            $(fn $sub_mod<'a>(&'a self) -> Box<dyn 'a + $sub_mod::$ext_trait<T>> {
                self.deref().$sub_mod()
            })+
        }

        // Implementing `ConfigPart` for `BaseConfig`

        #[derive(serde::Serialize, serde::Deserialize)]
        pub struct BaseConfigBuilder {
            $($sub_mod: $sub_mod::Builder,)+
        }

        lazy_static::lazy_static! {
            static ref GLOBAL: std::sync::Arc<std::sync::Mutex<$base_cfg>> =
                std::sync::Arc::new(std::sync::Mutex::new(Default::default()));
        }

        impl $crate::config::ConfigPart for $base_cfg {
            type Deref = std::sync::MutexGuard<'static, $base_cfg>;
            type DerefMut = std::sync::MutexGuard<'static, $base_cfg>;

            fn global() -> Self::Deref {
                GLOBAL.lock().unwrap()
            }

            fn global_mut() -> Self::DerefMut {
                GLOBAL.lock().unwrap()
            }

            fn update(&mut self, builder: BaseConfigBuilder) {
                $(self.$sub_mod.update(builder.$sub_mod);)+
            }
        }

        impl $crate::config::Build for $base_cfg {
            type Builder = BaseConfigBuilder;
        }

        impl $crate::utils::XFrom<BaseConfigBuilder> for $base_cfg {
            fn xfrom(builder: BaseConfigBuilder) -> Self {
                use $crate::utils::XInto;

                Self {
                    $($sub_mod: builder.$sub_mod.xinto(),)+
                }
            }
        }
    }
}
