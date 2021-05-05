/// We need this JUST ONLY for `::bumpalo::boxed::Box`, because it doesn't have
/// the reference to the bumpalo instance so it cannot clone themself.
pub trait FieldClone<'bump>: Sized {
    fn clone(&self) -> Self;
    #[cfg(feature = "puroro-bumpalo")]
    fn clone_in_bumpalo(&self, _bump: &'bump ::bumpalo::Bump) -> Self {
        <Self as FieldClone>::clone(self)
    }
}

#[cfg(feature = "puroro-bumpalo")]
impl<'bump, T: Clone> FieldClone<'bump> for ::bumpalo::boxed::Box<'bump, T> {
    fn clone(&self) -> Self {
        panic!("bumpalo box needs a bumpalo instance to clone!");
    }
    #[cfg(feature = "puroro-bumpalo")]
    fn clone_in_bumpalo(&self, bump: &'bump ::bumpalo::Bump) -> Self {
        ::bumpalo::boxed::Box::new_in(self.as_ref().clone(), bump)
    }
}

impl<'bump, T: FieldClone<'bump>> FieldClone<'bump> for Option<T> {
    fn clone(&self) -> Self {
        match self {
            Some(x) => Some(<T as FieldClone>::clone(x)),
            None => None,
        }
    }
    #[cfg(feature = "puroro-bumpalo")]
    fn clone_in_bumpalo(&self, bump: &'bump ::bumpalo::Bump) -> Self {
        match self {
            Some(x) => Some(<T as FieldClone>::clone_in_bumpalo(x, bump)),
            None => None,
        }
    }
}

macro_rules! define_field_clone {
    ($ty:ty) => {
        impl<'bump> FieldClone<'bump> for $ty {
            fn clone(&self) -> Self {
                <Self as Clone>::clone(self)
            }
        }
    };
    ($ty:ty, < $($gp:ident $( : $bound:ident)? ),* >) => {
        impl<'bump $(, $gp $( : $bound)?)+ > FieldClone<'bump> for $ty {
            fn clone(&self) -> Self {
                <Self as Clone>::clone(self)
            }
        }
    };
}
define_field_clone!(i32);
define_field_clone!(i64);
define_field_clone!(u32);
define_field_clone!(u64);
define_field_clone!(f32);
define_field_clone!(f64);
define_field_clone!(bool);
define_field_clone!(String);
define_field_clone!(std::result::Result<T, i32>, <T: Clone>);
define_field_clone!(Box<T>, <T: Clone>);
define_field_clone!(Vec<T>, <T: Clone>);
#[cfg(feature = "puroro-bumpalo")]
define_field_clone!(::bumpalo::collections::Vec<'bump, T>, <T: Clone>);
#[cfg(feature = "puroro-bumpalo")]
define_field_clone!(::bumpalo::collections::String<'bump>);
