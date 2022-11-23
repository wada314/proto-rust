pub mod _puroro_root {
    pub use super::super::_puroro_root::*;
}
pub mod _puroro {
    pub use ::puroro::*;
}
pub mod msg;
#[derive(::std::default::Default)]
pub struct Msg {
    i32_optional: self::_puroro::internal::field_type::OptionalNumericalField::<
        i32,
        self::_puroro::tags::Int32,
        0usize,
    >,
    i32_repeated: self::_puroro::internal::field_type::RepeatedNumericalField::<
        i32,
        self::_puroro::tags::Int32,
    >,
    float_optional: self::_puroro::internal::field_type::OptionalNumericalField::<
        f32,
        self::_puroro::tags::Float,
        1usize,
    >,
    float_repeated: self::_puroro::internal::field_type::RepeatedNumericalField::<
        f32,
        self::_puroro::tags::Float,
    >,
    string_optional: self::_puroro::internal::field_type::OptionalStringField::<2usize>,
    string_repeated: self::_puroro::internal::field_type::RepeatedStringField,
    submsg_optional: self::_puroro::internal::field_type::SingularHeapMessageField::<
        self::_puroro_root::ser_tests2::msg::Submsg,
    >,
    submsg_repeated: self::_puroro::internal::field_type::RepeatedMessageField::<
        self::_puroro_root::ser_tests2::msg::Submsg,
    >,
    enum_optional: self::_puroro::internal::field_type::OptionalNumericalField::<
        self::_puroro_root::ser_tests2::Enum,
        self::_puroro::tags::Enum2::<self::_puroro_root::ser_tests2::Enum>,
        3usize,
    >,
    enum_repeated: self::_puroro::internal::field_type::RepeatedNumericalField::<
        self::_puroro_root::ser_tests2::Enum,
        self::_puroro::tags::Enum2::<self::_puroro_root::ser_tests2::Enum>,
    >,
    very_large_field_number: self::_puroro::internal::field_type::OptionalNumericalField::<
        i32,
        self::_puroro::tags::Int32,
        4usize,
    >,
    _bitfield: self::_puroro::bitvec::BitArray<1usize>,
}
impl Msg {
    pub fn i32_optional(&self) -> i32 {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::OptionalNumericalField::<
            i32,
            self::_puroro::tags::Int32,
            0usize,
        > as NonRepeatedFieldType>::get_field(
            &self.i32_optional,
            &self._bitfield,
            ::std::default::Default::default,
        )
    }
    pub fn i32_repeated(&self) -> &[i32] {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedNumericalField::<
            i32,
            self::_puroro::tags::Int32,
        > as RepeatedFieldType>::get_field(&self.i32_repeated, &self._bitfield)
    }
    pub fn float_optional(&self) -> f32 {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::OptionalNumericalField::<
            f32,
            self::_puroro::tags::Float,
            1usize,
        > as NonRepeatedFieldType>::get_field(
            &self.float_optional,
            &self._bitfield,
            ::std::default::Default::default,
        )
    }
    pub fn float_repeated(&self) -> &[f32] {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedNumericalField::<
            f32,
            self::_puroro::tags::Float,
        > as RepeatedFieldType>::get_field(&self.float_repeated, &self._bitfield)
    }
    pub fn string_optional(&self) -> &str {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::OptionalStringField::<
            2usize,
        > as NonRepeatedFieldType>::get_field(
            &self.string_optional,
            &self._bitfield,
            ::std::default::Default::default,
        )
    }
    pub fn string_repeated(&self) -> &[impl ::std::ops::Deref::<Target = str>] {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedStringField as RepeatedFieldType>::get_field(
            &self.string_repeated,
            &self._bitfield,
        )
    }
    pub fn submsg_optional(
        &self,
    ) -> ::std::option::Option::<&self::_puroro_root::ser_tests2::msg::Submsg> {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularHeapMessageField::<
            self::_puroro_root::ser_tests2::msg::Submsg,
        > as NonRepeatedFieldType>::get_field(
            &self.submsg_optional,
            &self._bitfield,
            ::std::default::Default::default,
        )
    }
    pub fn submsg_repeated(&self) -> &[self::_puroro_root::ser_tests2::msg::Submsg] {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedMessageField::<
            self::_puroro_root::ser_tests2::msg::Submsg,
        > as RepeatedFieldType>::get_field(&self.submsg_repeated, &self._bitfield)
    }
    pub fn enum_optional(&self) -> self::_puroro_root::ser_tests2::Enum {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::OptionalNumericalField::<
            self::_puroro_root::ser_tests2::Enum,
            self::_puroro::tags::Enum2::<self::_puroro_root::ser_tests2::Enum>,
            3usize,
        > as NonRepeatedFieldType>::get_field(
            &self.enum_optional,
            &self._bitfield,
            ::std::default::Default::default,
        )
    }
    pub fn enum_repeated(&self) -> &[self::_puroro_root::ser_tests2::Enum] {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedNumericalField::<
            self::_puroro_root::ser_tests2::Enum,
            self::_puroro::tags::Enum2::<self::_puroro_root::ser_tests2::Enum>,
        > as RepeatedFieldType>::get_field(&self.enum_repeated, &self._bitfield)
    }
    pub fn very_large_field_number(&self) -> i32 {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::OptionalNumericalField::<
            i32,
            self::_puroro::tags::Int32,
            4usize,
        > as NonRepeatedFieldType>::get_field(
            &self.very_large_field_number,
            &self._bitfield,
            ::std::default::Default::default,
        )
    }
}
impl self::_puroro::Message for Msg {
    fn from_bytes_iter<I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>>(
        iter: I,
    ) -> self::_puroro::Result<Self> {
        let mut msg = <Self as ::std::default::Default>::default();
        msg.merge_from_bytes_iter(iter)?;
        ::std::result::Result::Ok(msg)
    }
    fn merge_from_bytes_iter<I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>>(
        &mut self,
        mut iter: I,
    ) -> self::_puroro::Result<()> {
        #[allow(unused)]
        use ::std::result::Result::Ok;
        #[allow(unused)]
        use ::std::option::Option::Some;
        #[allow(unused)]
        use self::_puroro::internal::field_type::FieldType;
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofUnion;
        use self::_puroro::internal::ser::FieldData;
        while let Some((number, field_data))
            = FieldData::from_bytes_iter(iter.by_ref())? {
            todo!()
        }
        Ok(())
    }
    fn to_bytes<W: ::std::io::Write>(
        &self,
        #[allow(unused)]
        out: &mut W,
    ) -> self::_puroro::Result<()> {
        #[allow(unused)]
        use ::std::result::Result::Ok;
        Ok(todo!())
    }
}
impl ::std::clone::Clone for Msg {
    fn clone(&self) -> Self {
        Self {
            i32_optional: <self::_puroro::internal::field_type::OptionalNumericalField::<
                i32,
                self::_puroro::tags::Int32,
                0usize,
            > as ::std::clone::Clone>::clone(&self.i32_optional),
            i32_repeated: <self::_puroro::internal::field_type::RepeatedNumericalField::<
                i32,
                self::_puroro::tags::Int32,
            > as ::std::clone::Clone>::clone(&self.i32_repeated),
            float_optional: <self::_puroro::internal::field_type::OptionalNumericalField::<
                f32,
                self::_puroro::tags::Float,
                1usize,
            > as ::std::clone::Clone>::clone(&self.float_optional),
            float_repeated: <self::_puroro::internal::field_type::RepeatedNumericalField::<
                f32,
                self::_puroro::tags::Float,
            > as ::std::clone::Clone>::clone(&self.float_repeated),
            string_optional: <self::_puroro::internal::field_type::OptionalStringField::<
                2usize,
            > as ::std::clone::Clone>::clone(&self.string_optional),
            string_repeated: <self::_puroro::internal::field_type::RepeatedStringField as ::std::clone::Clone>::clone(
                &self.string_repeated,
            ),
            submsg_optional: <self::_puroro::internal::field_type::SingularHeapMessageField::<
                self::_puroro_root::ser_tests2::msg::Submsg,
            > as ::std::clone::Clone>::clone(&self.submsg_optional),
            submsg_repeated: <self::_puroro::internal::field_type::RepeatedMessageField::<
                self::_puroro_root::ser_tests2::msg::Submsg,
            > as ::std::clone::Clone>::clone(&self.submsg_repeated),
            enum_optional: <self::_puroro::internal::field_type::OptionalNumericalField::<
                self::_puroro_root::ser_tests2::Enum,
                self::_puroro::tags::Enum2::<self::_puroro_root::ser_tests2::Enum>,
                3usize,
            > as ::std::clone::Clone>::clone(&self.enum_optional),
            enum_repeated: <self::_puroro::internal::field_type::RepeatedNumericalField::<
                self::_puroro_root::ser_tests2::Enum,
                self::_puroro::tags::Enum2::<self::_puroro_root::ser_tests2::Enum>,
            > as ::std::clone::Clone>::clone(&self.enum_repeated),
            very_large_field_number: <self::_puroro::internal::field_type::OptionalNumericalField::<
                i32,
                self::_puroro::tags::Int32,
                4usize,
            > as ::std::clone::Clone>::clone(&self.very_large_field_number),
            _bitfield: ::std::clone::Clone::clone(&self._bitfield),
        }
    }
}
#[derive(
    ::std::clone::Clone,
    ::std::marker::Copy,
    ::std::cmp::PartialEq,
    ::std::cmp::Eq,
    ::std::cmp::PartialOrd,
    ::std::cmp::Ord,
    ::std::hash::Hash,
)]
pub enum Enum {
    Zeroth,
    First,
    Tenth,
}
impl ::std::default::Default for Enum {
    fn default() -> Self {
        Self::Zeroth
    }
}
impl ::std::convert::From::<Enum> for i32 {
    fn from(val: Enum) -> i32 {
        match val {
            Enum::Zeroth => 0i32,
            Enum::First => 1i32,
            Enum::Tenth => 10i32,
        }
    }
}
impl ::std::convert::TryFrom::<i32> for Enum {
    type Error = self::_puroro::PuroroError;
    fn try_from(val: i32) -> ::std::result::Result<Self, Self::Error> {
        use ::std::result::Result::{Ok, Err};
        match val {
            0i32 => Ok(self::Enum::Zeroth),
            1i32 => Ok(self::Enum::First),
            10i32 => Ok(self::Enum::Tenth),
            _ => Err(self::_puroro::ErrorKind::UnknownEnumVariant(val))?,
        }
    }
}
