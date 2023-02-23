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
/** The name of the uninterpreted option.  Each string represents a segment in
 a dot-separated name.  is_extension is true iff a segment represents an
 extension (denoted with parentheses in options specs in .proto files).
 E.g.,{ ["foo", false], ["bar.baz", true], ["qux", false] } represents
 "foo.(bar.baz).qux".
*/
pub struct NamePart {
    body: self::_root::google::protobuf::uninterpreted_option::_view::NamePartView,
}
impl NamePart {
    pub fn name_part_mut(&mut self) -> &mut ::std::string::String {
        use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.body.fields.name_part,
            self.body.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn clear_name_part(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
        NonRepeatedFieldType::clear(
            &mut self.body.fields.name_part,
            self.body.shared.bitfield_mut(),
        )
    }
    pub fn is_extension_mut(&mut self) -> &mut bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.body.fields.is_extension,
            self.body.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn clear_is_extension(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
        NonRepeatedFieldType::clear(
            &mut self.body.fields.is_extension,
            self.body.shared.bitfield_mut(),
        )
    }
}
impl self::_puroro::Message for NamePart {
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
            &self.body.fields.name_part,
            self.body.shared.bitfield(),
            1i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.body.fields.is_extension,
            self.body.shared.bitfield(),
            2i32,
            out,
        )?;
        self.shared.unknown_fields().ser_to_write(out)?;
        ::std::result::Result::Ok(())
    }
}
impl self::_pinternal::MessageInternal for NamePart {
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
                            &mut self.body.fields.name_part,
                            self.body.shared.bitfield_mut(),
                            field_data,
                        )?
                    }
                    2i32 => {
                        self::_pinternal::FieldType::deser_from_field_data(
                            &mut self.body.fields.is_extension,
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
impl ::std::borrow::Borrow<
    self::_root::google::protobuf::uninterpreted_option::_view::NamePartView,
> for NamePart {
    fn borrow(
        &self,
    ) -> &self::_root::google::protobuf::uninterpreted_option::_view::NamePartView {
        &self.body
    }
}
impl ::std::clone::Clone for NamePart {
    fn clone(&self) -> Self {
        #[allow(unused)]
        use ::std::borrow::ToOwned;
        ToOwned::to_owned(&self.body)
    }
}
impl ::std::fmt::Debug for NamePart {
    fn fmt(
        &self,
        fmt: &mut ::std::fmt::Formatter<'_>,
    ) -> ::std::result::Result<(), ::std::fmt::Error> {
        <self::_root::google::protobuf::uninterpreted_option::_view::NamePartView as ::std::fmt::Debug>::fmt(
            &self.body,
            fmt,
        )
    }
}
impl ::std::ops::Deref for NamePart {
    type Target = self::_root::google::protobuf::uninterpreted_option::_view::NamePartView;
    fn deref(&self) -> &Self::Target {
        &self.body
    }
}
impl ::std::cmp::PartialEq for NamePart {
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
    pub struct NamePartView {
        pub(super) fields: self::_root::google::protobuf::uninterpreted_option::_fields::NamePartFields::<
            self::_pinternal::OptionalUnsizedField::<
                ::std::string::String,
                self::_pinternal::tags::String,
                0usize,
            >,
            self::_pinternal::OptionalNumericalField::<
                bool,
                self::_pinternal::tags::Bool,
                1usize,
            >,
        >,
        pub(super) shared: self::_pinternal::SharedItemsImpl<1usize>,
    }
    impl NamePartView {
        pub fn name_part(&self) -> &str {
            use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
            NonRepeatedFieldType::get_field_or_else(
                &self.fields.name_part,
                self.shared.bitfield(),
                ::std::default::Default::default,
            )
        }
        pub fn name_part_opt(&self) -> ::std::option::Option::<&str> {
            use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
            NonRepeatedFieldType::get_field_opt(
                &self.fields.name_part,
                self.shared.bitfield(),
            )
        }
        pub fn has_name_part(&self) -> bool {
            use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
            NonRepeatedFieldType::get_field_opt(
                    &self.fields.name_part,
                    self.shared.bitfield(),
                )
                .is_some()
        }
        pub fn is_extension(&self) -> bool {
            use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
            NonRepeatedFieldType::get_field_or_else(
                &self.fields.is_extension,
                self.shared.bitfield(),
                ::std::default::Default::default,
            )
        }
        pub fn is_extension_opt(&self) -> ::std::option::Option::<bool> {
            use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
            NonRepeatedFieldType::get_field_opt(
                &self.fields.is_extension,
                self.shared.bitfield(),
            )
        }
        pub fn has_is_extension(&self) -> bool {
            use self::_pinternal::{NonRepeatedFieldType, SharedItems as _};
            NonRepeatedFieldType::get_field_opt(
                    &self.fields.is_extension,
                    self.shared.bitfield(),
                )
                .is_some()
        }
    }
    impl ::std::ops::Drop for NamePartView {
        fn drop(&mut self) {
            #[allow(unused)]
            use self::_pinternal::{OneofUnion as _, SharedItems as _};
        }
    }
    impl ::std::fmt::Debug for NamePartView {
        fn fmt(
            &self,
            fmt: &mut ::std::fmt::Formatter<'_>,
        ) -> ::std::result::Result<(), ::std::fmt::Error> {
            use self::_pinternal::{SharedItems as _, UnknownFields as _};
            let mut debug_struct = fmt.debug_struct(stringify!(NamePartView));
            debug_struct
                .field(stringify!(name_part), &self.name_part_opt())
                .field(stringify!(is_extension), &self.is_extension_opt());
            self.shared.unknown_fields().debug_struct_fields(&mut debug_struct)?;
            debug_struct.finish()
        }
    }
    impl ::std::cmp::PartialEq for NamePartView {
        fn eq(&self, rhs: &Self) -> bool {
            #[allow(unused)]
            use self::_pinternal::OneofUnion as _;
            use self::_pinternal::SharedItems as _;
            true && self.name_part_opt() == rhs.name_part_opt()
                && self.is_extension_opt() == rhs.is_extension_opt()
                && self.shared.unknown_fields() == rhs.shared.unknown_fields()
        }
    }
    impl ::std::borrow::ToOwned for NamePartView {
        type Owned = self::_root::google::protobuf::uninterpreted_option::NamePart;
        fn to_owned(&self) -> Self::Owned {
            #[allow(unused)]
            use self::_pinternal::SharedItems;
            self::_root::google::protobuf::uninterpreted_option::NamePart {
                body: Self {
                    fields: self::_root::google::protobuf::uninterpreted_option::_fields::NamePartFields {
                        name_part: ::std::clone::Clone::clone(&self.fields.name_part),
                        is_extension: ::std::clone::Clone::clone(
                            &self.fields.is_extension,
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
    pub struct NamePartFields<TNamePart, TIsExtension> {
        pub name_part: TNamePart,
        pub is_extension: TIsExtension,
    }
}
#[doc(hidden)]
pub use self::_fields::*;
