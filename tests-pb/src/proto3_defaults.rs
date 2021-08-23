// A generated source code by puroro library
// package proto3_defaults

pub mod _puroro_root {
    pub use super::super::_puroro_root::*;
}

pub use _puroro_impls::MsgSimple as Msg;
pub use _puroro_impls::SubmsgSimple as Submsg;
pub mod _puroro_impls {
    mod _puroro_root {
        pub use super::super::_puroro_root::*;
    }

#[derive(Clone, Default, PartialEq, Debug)]
pub struct MsgSimple {pub i32_unlabeled: i32,pub i32_optional: ::std::option::Option<i32>,pub i32_repeated: ::std::vec::Vec<i32>,pub f32_unlabeled: f32,pub string_unlabeled: ::std::string::String,pub submsg_unlabeled: ::std::option::Option<::std::boxed::Box<self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgSimple>>,
}
impl ::puroro::Message for MsgSimple {}

impl super::_puroro_traits::MsgTrait for MsgSimple {
    fn i32_unlabeled<'this>(&'this self) -> i32 {
        ::std::clone::Clone::clone(&self.i32_unlabeled)
    }
    fn i32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
        ::std::clone::Clone::clone(&self.i32_optional)
    }
    type Field3RepeatedType<'this> = ::puroro_internal::impls::simple::VecWrapper<'this, i32>;

    fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
        ::puroro_internal::impls::simple::VecWrapper::new(&self.i32_repeated)
    }
    fn f32_unlabeled<'this>(&'this self) -> f32 {
        ::std::clone::Clone::clone(&self.f32_unlabeled)
    }
    fn string_unlabeled<'this>(&'this self) -> ::std::borrow::Cow<'this, str> {
        ::std::borrow::Cow::Borrowed(&self.string_unlabeled)
    }
    type Field6MessageType<'this> = self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgSimple;
    fn submsg_unlabeled<'this>(&'this self) -> ::std::option::Option<::std::borrow::Cow<'this, Self::Field6MessageType<'this>>> {
        self.submsg_unlabeled.as_ref().map(|boxed| ::std::borrow::Cow::Borrowed(boxed.as_ref()))
    }
}

impl ::puroro::DeserFromBytesIter for MsgSimple {
    fn deser<I>(&mut self, iter: I) -> ::puroro::Result<()>
    where
        I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>
    {
        ::puroro_internal::de::from_iter::deser_from_iter(self, iter)
    }
}

impl ::puroro_internal::de::DeserFieldsFromBytesIter for MsgSimple {
    fn deser_field<I>(
        &mut self,
        field_number: i32,
        data: ::puroro::types::FieldData<&mut ::puroro_internal::de::from_iter::ScopedIter<I>>,
    ) -> ::puroro::Result<()>
    where
        I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>
    {
        match field_number {
            1 => ::puroro_internal::impls::simple::de::DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::Int32
            >::deser_field(&mut self.i32_unlabeled, data),
            2 => ::puroro_internal::impls::simple::de::DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int32
            >::deser_field(&mut self.i32_optional, data),
            3 => ::puroro_internal::impls::simple::de::DeserFieldFromBytesIter::<
                ::puroro::tags::Repeated, ::puroro::tags::Int32
            >::deser_field(&mut self.i32_repeated, data),
            4 => ::puroro_internal::impls::simple::de::DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::Float
            >::deser_field(&mut self.f32_unlabeled, data),
            5 => ::puroro_internal::impls::simple::de::DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::String
            >::deser_field(&mut self.string_unlabeled, data),
            6 => ::puroro_internal::impls::simple::de::DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::Message<self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgSimple>
            >::deser_field(&mut self.submsg_unlabeled, data),

            _ => unimplemented!("TODO: This case should be handled properly..."),
        }
    }
}

impl ::puroro::SerToIoWrite for MsgSimple {
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write
    {
        ::puroro_internal::impls::simple::se::SerFieldToIoWrite::<
            ::puroro::tags::Unlabeled, ::puroro::tags::Int32
        >::ser_field(&self.i32_unlabeled, 1, out)?;
        ::puroro_internal::impls::simple::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(&self.i32_optional, 2, out)?;
        ::puroro_internal::impls::simple::se::SerFieldToIoWrite::<
            ::puroro::tags::Repeated, ::puroro::tags::Int32
        >::ser_field(&self.i32_repeated, 3, out)?;
        ::puroro_internal::impls::simple::se::SerFieldToIoWrite::<
            ::puroro::tags::Unlabeled, ::puroro::tags::Float
        >::ser_field(&self.f32_unlabeled, 4, out)?;
        ::puroro_internal::impls::simple::se::SerFieldToIoWrite::<
            ::puroro::tags::Unlabeled, ::puroro::tags::String
        >::ser_field(&self.string_unlabeled, 5, out)?;
        ::puroro_internal::impls::simple::se::SerFieldToIoWrite::<
            ::puroro::tags::Unlabeled, ::puroro::tags::Message<self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgSimple>
        >::ser_field(&self.submsg_unlabeled, 6, out)?;
        ::std::result::Result::Ok(())
    }
}

#[derive(Clone, Default, PartialEq, Debug)]
pub struct MsgEmpty;

impl ::puroro::Message for MsgEmpty {}

impl super::_puroro_traits::MsgTrait for MsgEmpty {
    fn i32_unlabeled<'this>(&'this self) -> i32 {
        ::std::default::Default::default()
    }
    fn i32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
        None
    }
    type Field3RepeatedType<'this> = ::puroro_internal::impls::empty::EmptyRepeatedField<i32>;
    fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
        ::puroro_internal::impls::empty::EmptyRepeatedField::new()
    }
    fn f32_unlabeled<'this>(&'this self) -> f32 {
        ::std::default::Default::default()
    }
    fn string_unlabeled<'this>(&'this self) -> ::std::borrow::Cow<'this, str> {
        ::std::borrow::Cow::Owned(::std::default::Default::default())
    }
    type Field6MessageType<'this> = self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgEmpty;
    fn submsg_unlabeled<'this>(&'this self) -> ::std::option::Option<::std::borrow::Cow<'this, Self::Field6MessageType<'this>>> {
        None
    }
}

impl ::puroro::SerToIoWrite for MsgEmpty {
    fn ser<W>(&self, _out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write
    {
        ::std::result::Result::Ok(())
    }
}

#[derive(Clone, PartialEq, Debug)]
struct MsgSingleField1<FieldType> {
    field: FieldType,
}

impl<FieldType> ::puroro::Message for MsgSingleField1<FieldType> {}

impl<FieldType> super::_puroro_traits::MsgTrait for MsgSingleField1<FieldType>
where
    FieldType: Clone, PartialEq, Debug,
{
    fn i32_unlabeled<'this>(&'this self) -> i32 {
        ::std::default::Default::default()
    }
    fn i32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
        None
    }
    type Field3RepeatedType<'this> = ::puroro_internal::impls::empty::EmptyRepeatedField<i32>;
    fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
        ::puroro_internal::impls::empty::EmptyRepeatedField::new()
    }
    fn f32_unlabeled<'this>(&'this self) -> f32 {
        ::std::default::Default::default()
    }
    fn string_unlabeled<'this>(&'this self) -> ::std::borrow::Cow<'this, str> {
        ::std::borrow::Cow::Owned(::std::default::Default::default())
    }
    type Field6MessageType<'this> = self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgEmpty;
    fn submsg_unlabeled<'this>(&'this self) -> ::std::option::Option<::std::borrow::Cow<'this, Self::Field6MessageType<'this>>> {
        None
    }
}

#[derive(Clone, PartialEq, Debug)]
struct MsgSingleField2<FieldType> {
    field: FieldType,
}

impl<FieldType> ::puroro::Message for MsgSingleField2<FieldType> {}

impl<FieldType> super::_puroro_traits::MsgTrait for MsgSingleField2<FieldType>
where
    FieldType: Clone, PartialEq, Debug,
{
    fn i32_unlabeled<'this>(&'this self) -> i32 {
        ::std::default::Default::default()
    }
    fn i32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
        None
    }
    type Field3RepeatedType<'this> = ::puroro_internal::impls::empty::EmptyRepeatedField<i32>;
    fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
        ::puroro_internal::impls::empty::EmptyRepeatedField::new()
    }
    fn f32_unlabeled<'this>(&'this self) -> f32 {
        ::std::default::Default::default()
    }
    fn string_unlabeled<'this>(&'this self) -> ::std::borrow::Cow<'this, str> {
        ::std::borrow::Cow::Owned(::std::default::Default::default())
    }
    type Field6MessageType<'this> = self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgEmpty;
    fn submsg_unlabeled<'this>(&'this self) -> ::std::option::Option<::std::borrow::Cow<'this, Self::Field6MessageType<'this>>> {
        None
    }
}

#[derive(Clone, PartialEq, Debug)]
struct MsgSingleField3<FieldType> {
    field: FieldType,
}

impl<FieldType> ::puroro::Message for MsgSingleField3<FieldType> {}

impl<FieldType> super::_puroro_traits::MsgTrait for MsgSingleField3<FieldType>
where
    FieldType: Clone, PartialEq, Debug,
{
    fn i32_unlabeled<'this>(&'this self) -> i32 {
        ::std::default::Default::default()
    }
    fn i32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
        None
    }
    type Field3RepeatedType<'this> = ::puroro_internal::impls::empty::EmptyRepeatedField<i32>;
    fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
        ::puroro_internal::impls::empty::EmptyRepeatedField::new()
    }
    fn f32_unlabeled<'this>(&'this self) -> f32 {
        ::std::default::Default::default()
    }
    fn string_unlabeled<'this>(&'this self) -> ::std::borrow::Cow<'this, str> {
        ::std::borrow::Cow::Owned(::std::default::Default::default())
    }
    type Field6MessageType<'this> = self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgEmpty;
    fn submsg_unlabeled<'this>(&'this self) -> ::std::option::Option<::std::borrow::Cow<'this, Self::Field6MessageType<'this>>> {
        None
    }
}

#[derive(Clone, PartialEq, Debug)]
struct MsgSingleField4<FieldType> {
    field: FieldType,
}

impl<FieldType> ::puroro::Message for MsgSingleField4<FieldType> {}

impl<FieldType> super::_puroro_traits::MsgTrait for MsgSingleField4<FieldType>
where
    FieldType: Clone, PartialEq, Debug,
{
    fn i32_unlabeled<'this>(&'this self) -> i32 {
        ::std::default::Default::default()
    }
    fn i32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
        None
    }
    type Field3RepeatedType<'this> = ::puroro_internal::impls::empty::EmptyRepeatedField<i32>;
    fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
        ::puroro_internal::impls::empty::EmptyRepeatedField::new()
    }
    fn f32_unlabeled<'this>(&'this self) -> f32 {
        ::std::default::Default::default()
    }
    fn string_unlabeled<'this>(&'this self) -> ::std::borrow::Cow<'this, str> {
        ::std::borrow::Cow::Owned(::std::default::Default::default())
    }
    type Field6MessageType<'this> = self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgEmpty;
    fn submsg_unlabeled<'this>(&'this self) -> ::std::option::Option<::std::borrow::Cow<'this, Self::Field6MessageType<'this>>> {
        None
    }
}

#[derive(Clone, PartialEq, Debug)]
struct MsgSingleField5<FieldType> {
    field: FieldType,
}

impl<FieldType> ::puroro::Message for MsgSingleField5<FieldType> {}

impl<FieldType> super::_puroro_traits::MsgTrait for MsgSingleField5<FieldType>
where
    FieldType: Clone, PartialEq, Debug,
{
    fn i32_unlabeled<'this>(&'this self) -> i32 {
        ::std::default::Default::default()
    }
    fn i32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
        None
    }
    type Field3RepeatedType<'this> = ::puroro_internal::impls::empty::EmptyRepeatedField<i32>;
    fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
        ::puroro_internal::impls::empty::EmptyRepeatedField::new()
    }
    fn f32_unlabeled<'this>(&'this self) -> f32 {
        ::std::default::Default::default()
    }
    fn string_unlabeled<'this>(&'this self) -> ::std::borrow::Cow<'this, str> {
        ::std::borrow::Cow::Owned(::std::default::Default::default())
    }
    type Field6MessageType<'this> = self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgEmpty;
    fn submsg_unlabeled<'this>(&'this self) -> ::std::option::Option<::std::borrow::Cow<'this, Self::Field6MessageType<'this>>> {
        None
    }
}

#[derive(Clone, PartialEq, Debug)]
struct MsgSingleField6<FieldType> {
    field: FieldType,
}

impl<FieldType> ::puroro::Message for MsgSingleField6<FieldType> {}

impl<FieldType> super::_puroro_traits::MsgTrait for MsgSingleField6<FieldType>
where
    FieldType: Clone, PartialEq, Debug,
{
    fn i32_unlabeled<'this>(&'this self) -> i32 {
        ::std::default::Default::default()
    }
    fn i32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
        None
    }
    type Field3RepeatedType<'this> = ::puroro_internal::impls::empty::EmptyRepeatedField<i32>;
    fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
        ::puroro_internal::impls::empty::EmptyRepeatedField::new()
    }
    fn f32_unlabeled<'this>(&'this self) -> f32 {
        ::std::default::Default::default()
    }
    fn string_unlabeled<'this>(&'this self) -> ::std::borrow::Cow<'this, str> {
        ::std::borrow::Cow::Owned(::std::default::Default::default())
    }
    type Field6MessageType<'this> = self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgEmpty;
    fn submsg_unlabeled<'this>(&'this self) -> ::std::option::Option<::std::borrow::Cow<'this, Self::Field6MessageType<'this>>> {
        None
    }
}

#[derive(Clone, Default, PartialEq, Debug)]
pub struct SubmsgSimple {pub i32_unlabeled: i32,
}
impl ::puroro::Message for SubmsgSimple {}

impl super::_puroro_traits::SubmsgTrait for SubmsgSimple {
    fn i32_unlabeled<'this>(&'this self) -> i32 {
        ::std::clone::Clone::clone(&self.i32_unlabeled)
    }
}

impl ::puroro::DeserFromBytesIter for SubmsgSimple {
    fn deser<I>(&mut self, iter: I) -> ::puroro::Result<()>
    where
        I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>
    {
        ::puroro_internal::de::from_iter::deser_from_iter(self, iter)
    }
}

impl ::puroro_internal::de::DeserFieldsFromBytesIter for SubmsgSimple {
    fn deser_field<I>(
        &mut self,
        field_number: i32,
        data: ::puroro::types::FieldData<&mut ::puroro_internal::de::from_iter::ScopedIter<I>>,
    ) -> ::puroro::Result<()>
    where
        I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>
    {
        match field_number {
            1 => ::puroro_internal::impls::simple::de::DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::Int32
            >::deser_field(&mut self.i32_unlabeled, data),

            _ => unimplemented!("TODO: This case should be handled properly..."),
        }
    }
}

impl ::puroro::SerToIoWrite for SubmsgSimple {
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write
    {
        ::puroro_internal::impls::simple::se::SerFieldToIoWrite::<
            ::puroro::tags::Unlabeled, ::puroro::tags::Int32
        >::ser_field(&self.i32_unlabeled, 1, out)?;
        ::std::result::Result::Ok(())
    }
}

#[derive(Clone, Default, PartialEq, Debug)]
pub struct SubmsgEmpty;

impl ::puroro::Message for SubmsgEmpty {}

impl super::_puroro_traits::SubmsgTrait for SubmsgEmpty {
    fn i32_unlabeled<'this>(&'this self) -> i32 {
        ::std::default::Default::default()
    }
}

impl ::puroro::SerToIoWrite for SubmsgEmpty {
    fn ser<W>(&self, _out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write
    {
        ::std::result::Result::Ok(())
    }
}

#[derive(Clone, PartialEq, Debug)]
struct SubmsgSingleField1<FieldType> {
    field: FieldType,
}

impl<FieldType> ::puroro::Message for SubmsgSingleField1<FieldType> {}

impl<FieldType> super::_puroro_traits::SubmsgTrait for SubmsgSingleField1<FieldType>
where
    FieldType: Clone, PartialEq, Debug,
{
    fn i32_unlabeled<'this>(&'this self) -> i32 {
        ::std::default::Default::default()
    }
}
}
pub use _puroro_traits::*;
pub mod _puroro_traits {
    mod _puroro_root {
        pub use super::super::_puroro_root::*;
    }
    
    pub trait MsgTrait: ::std::clone::Clone {
        fn i32_unlabeled<'this>(&'this self) -> i32;
        fn i32_optional<'this>(&'this self) -> ::std::option::Option<i32>;
        type Field3RepeatedType<'this>: ::puroro::RepeatedField<'this, i32>;
    
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this>;
        fn f32_unlabeled<'this>(&'this self) -> f32;
        fn string_unlabeled<'this>(&'this self) -> ::std::borrow::Cow<'this, str>;
        type Field6MessageType<'this>: 'this + self::_puroro_root::proto3_defaults::_puroro_traits::SubmsgTrait;
        fn submsg_unlabeled<'this>(&'this self) -> ::std::option::Option<::std::borrow::Cow<'this, Self::Field6MessageType<'this>>>;
    }
    pub trait SubmsgTrait: ::std::clone::Clone {
        fn i32_unlabeled<'this>(&'this self) -> i32;
    }
}
pub use _puroro_nested::*;
pub mod _puroro_nested {
    pub mod msg {
        mod _puroro_root {
            pub use super::super::super::_puroro_root::*;
        }
        
    }
    pub mod submsg {
        mod _puroro_root {
            pub use super::super::super::_puroro_root::*;
        }
        
    }
}