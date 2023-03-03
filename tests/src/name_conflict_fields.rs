mod _root {
    #[allow(unused)]
    pub(crate) use super::super::_root::*;
}
mod _puroro {
    #[allow(unused)]
    pub(crate) use super::_root::_puroro::*;
}
mod _pinternal {
    #[allow(unused)]
    pub(crate) use super::_root::_pinternal::*;
}
#[derive(::std::default::Default)]
pub struct Conflict {
    body: self::_root::name_conflict_fields::_view::ConflictView,
}
impl Conflict {
    pub fn this_is_original_message_field_mut(&mut self) -> &mut i32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.body.fields.this_is_original_message_field,
            self.body.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn clear_this_is_original_message_field(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
        NonRepeatedFieldType::clear(
            &mut self.body.fields.this_is_original_message_field,
            self.body.shared.bitfield_mut(),
        )
    }
    pub const THIS_IS_ORIGINAL_MESSAGE_FIELD_FIELD_NUMBER: i32 = 1i32;
}
impl self::_puroro::Message for Conflict {
    fn from_bytes_iter<I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>>(
        iter: I,
    ) -> self::_puroro::Result<Self> {
        let mut msg = <Self as ::std::default::Default>::default();
        msg.merge_from_bytes_iter(iter)?;
        ::std::result::Result::Ok(msg)
    }
    fn merge_from_bytes_iter<I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>>(
        &mut self,
        iter: I,
    ) -> self::_puroro::Result<()> {
        let mut pos_iter = self::_pinternal::PosIter::new(iter);
        let mut scoped_iter = self::_pinternal::ScopedIter::from_mut_pos_iter(
            &mut pos_iter,
        );
        <Self as self::_pinternal::MessageInternal>::merge_from_scoped_bytes_iter(
            self,
            &mut scoped_iter,
        )?;
        scoped_iter.drop_and_check_scope_completed()?;
        Ok(())
    }
    fn to_bytes<W: ::std::io::Write>(
        &self,
        #[allow(unused)]
        out: &mut W,
    ) -> self::_puroro::Result<()> {
        #[allow(unused)]
        use self::_pinternal::OneofUnion as _;
        use self::_pinternal::{SharedItems as _, UnknownFields as _};
        self::_pinternal::FieldType::ser_to_write(
            &self.body.fields.this_is_original_message_field,
            self.body.shared.bitfield(),
            1i32,
            out,
        )?;
        self.shared.unknown_fields().ser_to_write(out)?;
        ::std::result::Result::Ok(())
    }
}
impl self::_pinternal::MessageInternal for Conflict {
    fn merge_from_scoped_bytes_iter<
        'a,
        I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>,
    >(
        &mut self,
        iter: &mut self::_pinternal::ScopedIter<'a, I>,
    ) -> self::_puroro::Result<()> {
        use self::_pinternal::ser::FieldData;
        #[allow(unused)]
        use self::_pinternal::OneofUnion as _;
        use self::_pinternal::{SharedItems as _, UnknownFields as _};
        #[allow(unused)]
        use ::std::result::Result;
        #[allow(unused)]
        use ::std::result::Result::{Ok, Err};
        #[allow(unused)]
        use ::std::vec::Vec;
        use self::_puroro::PuroroError;
        while let Some((number, field_data))
            = FieldData::from_bytes_scoped_iter(iter.by_ref())? {
            let result: self::_puroro::Result<()> = (|| {
                match number {
                    1i32 => {
                        self::_pinternal::FieldType::deser_from_field_data(
                            &mut self.body.fields.this_is_original_message_field,
                            self.body.shared.bitfield_mut(),
                            field_data,
                        )?
                    }
                    _ => {
                        let field_data = field_data
                            .map(|iter| { iter.collect::<Result<Vec<_>, _>>() })
                            .transpose()?;
                        Err(PuroroError::UnknownFieldNumber(field_data))?
                    }
                }
                Ok(())
            })();
            match result {
                Ok(_) => {}
                Err(PuroroError::UnknownFieldNumber(field_data)) => {
                    self.body.shared.unknown_fields_mut().push(number, field_data)?;
                }
                Err(e) => Err(e)?,
            }
        }
        Ok(())
    }
}
impl ::std::borrow::Borrow<self::_root::name_conflict_fields::_view::ConflictView>
for Conflict {
    fn borrow(&self) -> &self::_root::name_conflict_fields::_view::ConflictView {
        &self.body
    }
}
impl ::std::clone::Clone for Conflict {
    fn clone(&self) -> Self {
        #[allow(unused)]
        use ::std::borrow::ToOwned;
        ToOwned::to_owned(&self.body)
    }
}
impl ::std::fmt::Debug for Conflict {
    fn fmt(
        &self,
        fmt: &mut ::std::fmt::Formatter<'_>,
    ) -> ::std::result::Result<(), ::std::fmt::Error> {
        <self::_root::name_conflict_fields::_view::ConflictView as ::std::fmt::Debug>::fmt(
            &self.body,
            fmt,
        )
    }
}
impl ::std::ops::Deref for Conflict {
    type Target = self::_root::name_conflict_fields::_view::ConflictView;
    fn deref(&self) -> &Self::Target {
        &self.body
    }
}
impl ::std::cmp::PartialEq for Conflict {
    fn eq(&self, rhs: &Self) -> bool {
        &self.body == &rhs.body
    }
}
#[derive(::std::default::Default)]
pub struct ConflictFields {
    body: self::_root::name_conflict_fields::_view::ConflictFieldsView,
}
impl ConflictFields {
    pub fn this_is_fields_message_field_mut(&mut self) -> &mut i32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.body.fields.this_is_fields_message_field,
            self.body.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn clear_this_is_fields_message_field(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
        NonRepeatedFieldType::clear(
            &mut self.body.fields.this_is_fields_message_field,
            self.body.shared.bitfield_mut(),
        )
    }
    pub const THIS_IS_FIELDS_MESSAGE_FIELD_FIELD_NUMBER: i32 = 1i32;
}
impl self::_puroro::Message for ConflictFields {
    fn from_bytes_iter<I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>>(
        iter: I,
    ) -> self::_puroro::Result<Self> {
        let mut msg = <Self as ::std::default::Default>::default();
        msg.merge_from_bytes_iter(iter)?;
        ::std::result::Result::Ok(msg)
    }
    fn merge_from_bytes_iter<I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>>(
        &mut self,
        iter: I,
    ) -> self::_puroro::Result<()> {
        let mut pos_iter = self::_pinternal::PosIter::new(iter);
        let mut scoped_iter = self::_pinternal::ScopedIter::from_mut_pos_iter(
            &mut pos_iter,
        );
        <Self as self::_pinternal::MessageInternal>::merge_from_scoped_bytes_iter(
            self,
            &mut scoped_iter,
        )?;
        scoped_iter.drop_and_check_scope_completed()?;
        Ok(())
    }
    fn to_bytes<W: ::std::io::Write>(
        &self,
        #[allow(unused)]
        out: &mut W,
    ) -> self::_puroro::Result<()> {
        #[allow(unused)]
        use self::_pinternal::OneofUnion as _;
        use self::_pinternal::{SharedItems as _, UnknownFields as _};
        self::_pinternal::FieldType::ser_to_write(
            &self.body.fields.this_is_fields_message_field,
            self.body.shared.bitfield(),
            1i32,
            out,
        )?;
        self.shared.unknown_fields().ser_to_write(out)?;
        ::std::result::Result::Ok(())
    }
}
impl self::_pinternal::MessageInternal for ConflictFields {
    fn merge_from_scoped_bytes_iter<
        'a,
        I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>,
    >(
        &mut self,
        iter: &mut self::_pinternal::ScopedIter<'a, I>,
    ) -> self::_puroro::Result<()> {
        use self::_pinternal::ser::FieldData;
        #[allow(unused)]
        use self::_pinternal::OneofUnion as _;
        use self::_pinternal::{SharedItems as _, UnknownFields as _};
        #[allow(unused)]
        use ::std::result::Result;
        #[allow(unused)]
        use ::std::result::Result::{Ok, Err};
        #[allow(unused)]
        use ::std::vec::Vec;
        use self::_puroro::PuroroError;
        while let Some((number, field_data))
            = FieldData::from_bytes_scoped_iter(iter.by_ref())? {
            let result: self::_puroro::Result<()> = (|| {
                match number {
                    1i32 => {
                        self::_pinternal::FieldType::deser_from_field_data(
                            &mut self.body.fields.this_is_fields_message_field,
                            self.body.shared.bitfield_mut(),
                            field_data,
                        )?
                    }
                    _ => {
                        let field_data = field_data
                            .map(|iter| { iter.collect::<Result<Vec<_>, _>>() })
                            .transpose()?;
                        Err(PuroroError::UnknownFieldNumber(field_data))?
                    }
                }
                Ok(())
            })();
            match result {
                Ok(_) => {}
                Err(PuroroError::UnknownFieldNumber(field_data)) => {
                    self.body.shared.unknown_fields_mut().push(number, field_data)?;
                }
                Err(e) => Err(e)?,
            }
        }
        Ok(())
    }
}
impl ::std::borrow::Borrow<self::_root::name_conflict_fields::_view::ConflictFieldsView>
for ConflictFields {
    fn borrow(&self) -> &self::_root::name_conflict_fields::_view::ConflictFieldsView {
        &self.body
    }
}
impl ::std::clone::Clone for ConflictFields {
    fn clone(&self) -> Self {
        #[allow(unused)]
        use ::std::borrow::ToOwned;
        ToOwned::to_owned(&self.body)
    }
}
impl ::std::fmt::Debug for ConflictFields {
    fn fmt(
        &self,
        fmt: &mut ::std::fmt::Formatter<'_>,
    ) -> ::std::result::Result<(), ::std::fmt::Error> {
        <self::_root::name_conflict_fields::_view::ConflictFieldsView as ::std::fmt::Debug>::fmt(
            &self.body,
            fmt,
        )
    }
}
impl ::std::ops::Deref for ConflictFields {
    type Target = self::_root::name_conflict_fields::_view::ConflictFieldsView;
    fn deref(&self) -> &Self::Target {
        &self.body
    }
}
impl ::std::cmp::PartialEq for ConflictFields {
    fn eq(&self, rhs: &Self) -> bool {
        &self.body == &rhs.body
    }
}
#[doc(hidden)]
pub mod _view {
    mod _root {
        #[allow(unused)]
        pub(crate) use super::super::_root::*;
    }
    mod _puroro {
        #[allow(unused)]
        pub(crate) use super::_root::_puroro::*;
    }
    mod _pinternal {
        #[allow(unused)]
        pub(crate) use super::_root::_pinternal::*;
    }
    #[derive(::std::default::Default)]
    pub struct ConflictView {
        pub(super) fields: self::_root::name_conflict_fields::_fields::ConflictFields::<
            self::_pinternal::OptionalNumericalField::<
                i32,
                self::_pinternal::tags::Int32,
                0usize,
            >,
        >,
        pub(super) shared: self::_pinternal::SharedItemsImpl<1usize>,
    }
    impl ConflictView {
        pub fn this_is_original_message_field(&self) -> i32 {
            use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
            NonRepeatedFieldType::get_field_or_else(
                &self.fields.this_is_original_message_field,
                self.shared.bitfield(),
                ::std::default::Default::default,
            )
        }
        pub fn this_is_original_message_field_opt(
            &self,
        ) -> ::std::option::Option::<i32> {
            use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
            NonRepeatedFieldType::get_field_opt(
                &self.fields.this_is_original_message_field,
                self.shared.bitfield(),
            )
        }
        pub fn has_this_is_original_message_field(&self) -> bool {
            use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
            NonRepeatedFieldType::get_field_opt(
                    &self.fields.this_is_original_message_field,
                    self.shared.bitfield(),
                )
                .is_some()
        }
    }
    impl ::std::ops::Drop for ConflictView {
        fn drop(&mut self) {
            #[allow(unused)]
            use self::_pinternal::{OneofUnion as _, SharedItems as _};
        }
    }
    impl ::std::fmt::Debug for ConflictView {
        fn fmt(
            &self,
            fmt: &mut ::std::fmt::Formatter<'_>,
        ) -> ::std::result::Result<(), ::std::fmt::Error> {
            use self::_pinternal::{SharedItems as _, UnknownFields as _};
            let mut debug_struct = fmt.debug_struct(stringify!(ConflictView));
            debug_struct
                .field(
                    stringify!(this_is_original_message_field),
                    &self.this_is_original_message_field_opt(),
                );
            self.shared.unknown_fields().debug_struct_fields(&mut debug_struct)?;
            debug_struct.finish()
        }
    }
    impl ::std::cmp::PartialEq for ConflictView {
        fn eq(&self, rhs: &Self) -> bool {
            #[allow(unused)]
            use self::_pinternal::OneofUnion as _;
            use self::_pinternal::SharedItems as _;
            true
                && self.this_is_original_message_field_opt()
                    == rhs.this_is_original_message_field_opt()
                && self.shared.unknown_fields() == rhs.shared.unknown_fields()
        }
    }
    impl ::std::borrow::ToOwned for ConflictView {
        type Owned = self::_root::name_conflict_fields::Conflict;
        fn to_owned(&self) -> Self::Owned {
            #[allow(unused)]
            use self::_pinternal::SharedItems;
            self::_root::name_conflict_fields::Conflict {
                body: Self {
                    fields: self::_root::name_conflict_fields::_fields::ConflictFields {
                        this_is_original_message_field: ::std::clone::Clone::clone(
                            &self.fields.this_is_original_message_field,
                        ),
                    },
                    shared: ::std::clone::Clone::clone(&self.shared),
                },
            }
        }
    }
    #[derive(::std::default::Default)]
    pub struct ConflictFieldsView {
        pub(super) fields: self::_root::name_conflict_fields::_fields::ConflictFieldsFields::<
            self::_pinternal::OptionalNumericalField::<
                i32,
                self::_pinternal::tags::Int32,
                0usize,
            >,
        >,
        pub(super) shared: self::_pinternal::SharedItemsImpl<1usize>,
    }
    impl ConflictFieldsView {
        pub fn this_is_fields_message_field(&self) -> i32 {
            use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
            NonRepeatedFieldType::get_field_or_else(
                &self.fields.this_is_fields_message_field,
                self.shared.bitfield(),
                ::std::default::Default::default,
            )
        }
        pub fn this_is_fields_message_field_opt(&self) -> ::std::option::Option::<i32> {
            use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
            NonRepeatedFieldType::get_field_opt(
                &self.fields.this_is_fields_message_field,
                self.shared.bitfield(),
            )
        }
        pub fn has_this_is_fields_message_field(&self) -> bool {
            use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
            NonRepeatedFieldType::get_field_opt(
                    &self.fields.this_is_fields_message_field,
                    self.shared.bitfield(),
                )
                .is_some()
        }
    }
    impl ::std::ops::Drop for ConflictFieldsView {
        fn drop(&mut self) {
            #[allow(unused)]
            use self::_pinternal::{OneofUnion as _, SharedItems as _};
        }
    }
    impl ::std::fmt::Debug for ConflictFieldsView {
        fn fmt(
            &self,
            fmt: &mut ::std::fmt::Formatter<'_>,
        ) -> ::std::result::Result<(), ::std::fmt::Error> {
            use self::_pinternal::{SharedItems as _, UnknownFields as _};
            let mut debug_struct = fmt.debug_struct(stringify!(ConflictFieldsView));
            debug_struct
                .field(
                    stringify!(this_is_fields_message_field),
                    &self.this_is_fields_message_field_opt(),
                );
            self.shared.unknown_fields().debug_struct_fields(&mut debug_struct)?;
            debug_struct.finish()
        }
    }
    impl ::std::cmp::PartialEq for ConflictFieldsView {
        fn eq(&self, rhs: &Self) -> bool {
            #[allow(unused)]
            use self::_pinternal::OneofUnion as _;
            use self::_pinternal::SharedItems as _;
            true
                && self.this_is_fields_message_field_opt()
                    == rhs.this_is_fields_message_field_opt()
                && self.shared.unknown_fields() == rhs.shared.unknown_fields()
        }
    }
    impl ::std::borrow::ToOwned for ConflictFieldsView {
        type Owned = self::_root::name_conflict_fields::ConflictFields;
        fn to_owned(&self) -> Self::Owned {
            #[allow(unused)]
            use self::_pinternal::SharedItems;
            self::_root::name_conflict_fields::ConflictFields {
                body: Self {
                    fields: self::_root::name_conflict_fields::_fields::ConflictFieldsFields {
                        this_is_fields_message_field: ::std::clone::Clone::clone(
                            &self.fields.this_is_fields_message_field,
                        ),
                    },
                    shared: ::std::clone::Clone::clone(&self.shared),
                },
            }
        }
    }
}
#[doc(inline)]
pub use self::_view::*;
#[doc(hidden)]
pub mod _fields {
    mod _root {
        #[allow(unused)]
        pub(crate) use super::super::_root::*;
    }
    mod _puroro {
        #[allow(unused)]
        pub(crate) use super::_root::_puroro::*;
    }
    mod _pinternal {
        #[allow(unused)]
        pub(crate) use super::_root::_pinternal::*;
    }
    #[derive(::std::default::Default)]
    pub struct ConflictFields<TThisIsOriginalMessageField> {
        pub this_is_original_message_field: TThisIsOriginalMessageField,
    }
    #[derive(::std::default::Default)]
    pub struct ConflictFieldsFields<TThisIsFieldsMessageField> {
        pub this_is_fields_message_field: TThisIsFieldsMessageField,
    }
}
#[doc(hidden)]
pub use self::_fields::*;