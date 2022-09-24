// A generated source code by puroro library
// package ser_tests3
pub mod msg;

pub mod _puroro_root {
    pub use super::super::_puroro_root::*;
}

pub mod _puroro {
    pub use ::puroro::*;
}

#[derive(Default, Clone)]
pub struct Msg {
    // Singular, Variant(Int32)
    i32_unlabeled: self::_puroro::internal::field_type::SingularNumericalField<
        i32,
        self::_puroro::tags::Int32,
    >,
    // Repeated, Variant(Int32)
    i32_repeated: self::_puroro::internal::field_type::RepeatedNumericalField<
        i32,
        self::_puroro::tags::Int32,
    >,
    // Singular, Bits32(Float)
    float_unlabeled: self::_puroro::internal::field_type::SingularNumericalField<
        f32,
        self::_puroro::tags::Float,
    >,
    // Repeated, Bits32(Float)
    float_repeated: self::_puroro::internal::field_type::RepeatedNumericalField<
        f32,
        self::_puroro::tags::Float,
    >,
    // Singular, LengthDelimited(String)
    string_unlabeled: self::_puroro::internal::field_type::SingularStringField,
    // Repeated, LengthDelimited(String)
    string_repeated: self::_puroro::internal::field_type::RepeatedStringField,
    // Singular, LengthDelimited(Message(Fqtn(".ser_tests3.Msg.Submsg")))
    submsg_unlabeled: self::_puroro::internal::field_type::SingularHeapMessageField<
        _puroro_root::ser_tests3::msg::Submsg,
    >,
    // Repeated, LengthDelimited(Message(Fqtn(".ser_tests3.Msg.Submsg")))
    submsg_repeated: self::_puroro::internal::field_type::RepeatedMessageField<
        _puroro_root::ser_tests3::msg::Submsg,
    >,
    // Singular, Variant(Enum3(Fqtn(".ser_tests3.Enum")))
    enum_unlabeled: self::_puroro::internal::field_type::SingularNumericalField<
        _puroro_root::ser_tests3::Enum,
        self::_puroro::tags::Enum3<_puroro_root::ser_tests3::Enum>,
    >,
    // Repeated, Variant(Enum3(Fqtn(".ser_tests3.Enum")))
    enum_repeated: self::_puroro::internal::field_type::RepeatedNumericalField<
        _puroro_root::ser_tests3::Enum,
        self::_puroro::tags::Enum3<_puroro_root::ser_tests3::Enum>,
    >,
    // Singular, Variant(Int32)
    very_large_field_number: self::_puroro::internal::field_type::SingularNumericalField<
        i32,
        self::_puroro::tags::Int32,
    >,

    _bitfield: self::_puroro::bitvec::BitArray<0>,
}

impl Msg {
    // Singular, Variant(Int32)
    pub fn i32_unlabeled(&self) -> i32 {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<i32, self::_puroro::tags::Int32> as NonRepeatedFieldType>::get_field(
            &self.i32_unlabeled, &self._bitfield, ::std::default::Default::default,
        )
    }
    pub fn i32_unlabeled_opt(&self) -> ::std::option::Option<i32> {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<i32, self::_puroro::tags::Int32> as NonRepeatedFieldType>::get_field_opt(
            &self.i32_unlabeled, &self._bitfield,
        )
    }
    pub fn has_i32_unlabeled(&self) -> bool {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<i32, self::_puroro::tags::Int32> as NonRepeatedFieldType>::get_field_opt(
            &self.i32_unlabeled, &self._bitfield,
        ).is_some()
    }
    pub fn i32_unlabeled_mut(&mut self) -> &mut i32 {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<i32, self::_puroro::tags::Int32> as NonRepeatedFieldType>::mut_field(
            &mut self.i32_unlabeled, &mut self._bitfield, ::std::default::Default::default,
        )
    }
    pub fn clear_i32_unlabeled(&mut self) {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<i32, self::_puroro::tags::Int32> as NonRepeatedFieldType>::clear(
            &mut self.i32_unlabeled, &mut self._bitfield,
        )
    }
    // Repeated, Variant(Int32)
    pub fn i32_repeated(&self) -> &[i32] {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedNumericalField<i32, self::_puroro::tags::Int32> as RepeatedFieldType>::get_field(
            &self.i32_repeated, &self._bitfield, 
        )
    }
    pub fn i32_repeated_mut(&mut self) -> &mut ::std::vec::Vec<i32> {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedNumericalField<i32, self::_puroro::tags::Int32> as RepeatedFieldType>::mut_field(
            &mut self.i32_repeated, &mut self._bitfield, 
        )
    }
    pub fn clear_i32_repeated(&mut self) {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedNumericalField<i32, self::_puroro::tags::Int32> as RepeatedFieldType>::clear(
            &mut self.i32_repeated, &mut self._bitfield, 
        )
    }
    // Singular, Bits32(Float)
    pub fn float_unlabeled(&self) -> f32 {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<f32, self::_puroro::tags::Float> as NonRepeatedFieldType>::get_field(
            &self.float_unlabeled, &self._bitfield, ::std::default::Default::default,
        )
    }
    pub fn float_unlabeled_opt(&self) -> ::std::option::Option<f32> {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<f32, self::_puroro::tags::Float> as NonRepeatedFieldType>::get_field_opt(
            &self.float_unlabeled, &self._bitfield,
        )
    }
    pub fn has_float_unlabeled(&self) -> bool {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<f32, self::_puroro::tags::Float> as NonRepeatedFieldType>::get_field_opt(
            &self.float_unlabeled, &self._bitfield,
        ).is_some()
    }
    pub fn float_unlabeled_mut(&mut self) -> &mut f32 {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<f32, self::_puroro::tags::Float> as NonRepeatedFieldType>::mut_field(
            &mut self.float_unlabeled, &mut self._bitfield, ::std::default::Default::default,
        )
    }
    pub fn clear_float_unlabeled(&mut self) {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<f32, self::_puroro::tags::Float> as NonRepeatedFieldType>::clear(
            &mut self.float_unlabeled, &mut self._bitfield,
        )
    }
    // Repeated, Bits32(Float)
    pub fn float_repeated(&self) -> &[f32] {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedNumericalField<f32, self::_puroro::tags::Float> as RepeatedFieldType>::get_field(
            &self.float_repeated, &self._bitfield, 
        )
    }
    pub fn float_repeated_mut(&mut self) -> &mut ::std::vec::Vec<f32> {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedNumericalField<f32, self::_puroro::tags::Float> as RepeatedFieldType>::mut_field(
            &mut self.float_repeated, &mut self._bitfield, 
        )
    }
    pub fn clear_float_repeated(&mut self) {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedNumericalField<f32, self::_puroro::tags::Float> as RepeatedFieldType>::clear(
            &mut self.float_repeated, &mut self._bitfield, 
        )
    }
    // Singular, LengthDelimited(String)
    pub fn string_unlabeled(&self) -> &str {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularStringField as NonRepeatedFieldType>::get_field(
            &self.string_unlabeled, &self._bitfield, ::std::default::Default::default,
        )
    }
    pub fn string_unlabeled_opt(&self) -> ::std::option::Option<&str> {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularStringField as NonRepeatedFieldType>::get_field_opt(
            &self.string_unlabeled, &self._bitfield,
        )
    }
    pub fn has_string_unlabeled(&self) -> bool {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularStringField as NonRepeatedFieldType>::get_field_opt(
            &self.string_unlabeled, &self._bitfield,
        ).is_some()
    }
    pub fn string_unlabeled_mut(&mut self) -> &mut ::std::string::String {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularStringField as NonRepeatedFieldType>::mut_field(
            &mut self.string_unlabeled, &mut self._bitfield, ::std::default::Default::default,
        )
    }
    pub fn clear_string_unlabeled(&mut self) {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularStringField as NonRepeatedFieldType>::clear(
            &mut self.string_unlabeled,
            &mut self._bitfield,
        )
    }
    // Repeated, LengthDelimited(String)
    pub fn string_repeated(&self) -> &[::std::string::String] {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedStringField as RepeatedFieldType>::get_field(
            &self.string_repeated,
            &self._bitfield,
        )
    }
    pub fn string_repeated_mut(&mut self) -> &mut ::std::vec::Vec<::std::string::String> {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedStringField as RepeatedFieldType>::mut_field(
            &mut self.string_repeated,
            &mut self._bitfield,
        )
    }
    pub fn clear_string_repeated(&mut self) {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedStringField as RepeatedFieldType>::clear(
            &mut self.string_repeated,
            &mut self._bitfield,
        )
    }
    // Singular, LengthDelimited(Message(Fqtn(".ser_tests3.Msg.Submsg")))
    pub fn submsg_unlabeled(&self) -> Option<&_puroro_root::ser_tests3::msg::Submsg> {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularHeapMessageField<
            _puroro_root::ser_tests3::msg::Submsg,
        > as NonRepeatedFieldType>::get_field(
            &self.submsg_unlabeled,
            &self._bitfield,
            ::std::default::Default::default,
        )
    }
    pub fn submsg_unlabeled_opt(
        &self,
    ) -> ::std::option::Option<&_puroro_root::ser_tests3::msg::Submsg> {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularHeapMessageField<
            _puroro_root::ser_tests3::msg::Submsg,
        > as NonRepeatedFieldType>::get_field_opt(&self.submsg_unlabeled, &self._bitfield)
    }
    pub fn has_submsg_unlabeled(&self) -> bool {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularHeapMessageField<
            _puroro_root::ser_tests3::msg::Submsg,
        > as NonRepeatedFieldType>::get_field_opt(&self.submsg_unlabeled, &self._bitfield)
        .is_some()
    }
    pub fn submsg_unlabeled_mut(&mut self) -> &mut _puroro_root::ser_tests3::msg::Submsg {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularHeapMessageField<
            _puroro_root::ser_tests3::msg::Submsg,
        > as NonRepeatedFieldType>::mut_field(
            &mut self.submsg_unlabeled,
            &mut self._bitfield,
            ::std::default::Default::default,
        )
    }
    pub fn clear_submsg_unlabeled(&mut self) {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularHeapMessageField<
            _puroro_root::ser_tests3::msg::Submsg,
        > as NonRepeatedFieldType>::clear(&mut self.submsg_unlabeled, &mut self._bitfield)
    }
    // Repeated, LengthDelimited(Message(Fqtn(".ser_tests3.Msg.Submsg")))
    pub fn submsg_repeated(&self) -> &[_puroro_root::ser_tests3::msg::Submsg] {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedMessageField<
            _puroro_root::ser_tests3::msg::Submsg,
        > as RepeatedFieldType>::get_field(&self.submsg_repeated, &self._bitfield)
    }
    pub fn submsg_repeated_mut(
        &mut self,
    ) -> &mut ::std::vec::Vec<_puroro_root::ser_tests3::msg::Submsg> {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedMessageField<
            _puroro_root::ser_tests3::msg::Submsg,
        > as RepeatedFieldType>::mut_field(&mut self.submsg_repeated, &mut self._bitfield)
    }
    pub fn clear_submsg_repeated(&mut self) {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedMessageField<
            _puroro_root::ser_tests3::msg::Submsg,
        > as RepeatedFieldType>::clear(&mut self.submsg_repeated, &mut self._bitfield)
    }
    // Singular, Variant(Enum3(Fqtn(".ser_tests3.Enum")))
    pub fn enum_unlabeled(&self) -> _puroro_root::ser_tests3::Enum {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<
            _puroro_root::ser_tests3::Enum,
            self::_puroro::tags::Enum3<_puroro_root::ser_tests3::Enum>,
        > as NonRepeatedFieldType>::get_field(
            &self.enum_unlabeled,
            &self._bitfield,
            ::std::default::Default::default,
        )
    }
    pub fn enum_unlabeled_opt(&self) -> ::std::option::Option<_puroro_root::ser_tests3::Enum> {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<
            _puroro_root::ser_tests3::Enum,
            self::_puroro::tags::Enum3<_puroro_root::ser_tests3::Enum>,
        > as NonRepeatedFieldType>::get_field_opt(&self.enum_unlabeled, &self._bitfield)
    }
    pub fn has_enum_unlabeled(&self) -> bool {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<
            _puroro_root::ser_tests3::Enum,
            self::_puroro::tags::Enum3<_puroro_root::ser_tests3::Enum>,
        > as NonRepeatedFieldType>::get_field_opt(&self.enum_unlabeled, &self._bitfield)
        .is_some()
    }
    pub fn enum_unlabeled_mut(&mut self) -> &mut _puroro_root::ser_tests3::Enum {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<
            _puroro_root::ser_tests3::Enum,
            self::_puroro::tags::Enum3<_puroro_root::ser_tests3::Enum>,
        > as NonRepeatedFieldType>::mut_field(
            &mut self.enum_unlabeled,
            &mut self._bitfield,
            ::std::default::Default::default,
        )
    }
    pub fn clear_enum_unlabeled(&mut self) {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<
            _puroro_root::ser_tests3::Enum,
            self::_puroro::tags::Enum3<_puroro_root::ser_tests3::Enum>,
        > as NonRepeatedFieldType>::clear(&mut self.enum_unlabeled, &mut self._bitfield)
    }
    // Repeated, Variant(Enum3(Fqtn(".ser_tests3.Enum")))
    pub fn enum_repeated(&self) -> &[_puroro_root::ser_tests3::Enum] {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedNumericalField<
            _puroro_root::ser_tests3::Enum,
            self::_puroro::tags::Enum3<_puroro_root::ser_tests3::Enum>,
        > as RepeatedFieldType>::get_field(&self.enum_repeated, &self._bitfield)
    }
    pub fn enum_repeated_mut(&mut self) -> &mut ::std::vec::Vec<_puroro_root::ser_tests3::Enum> {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedNumericalField<
            _puroro_root::ser_tests3::Enum,
            self::_puroro::tags::Enum3<_puroro_root::ser_tests3::Enum>,
        > as RepeatedFieldType>::mut_field(&mut self.enum_repeated, &mut self._bitfield)
    }
    pub fn clear_enum_repeated(&mut self) {
        use self::_puroro::internal::field_type::RepeatedFieldType;
        <self::_puroro::internal::field_type::RepeatedNumericalField<
            _puroro_root::ser_tests3::Enum,
            self::_puroro::tags::Enum3<_puroro_root::ser_tests3::Enum>,
        > as RepeatedFieldType>::clear(&mut self.enum_repeated, &mut self._bitfield)
    }
    // Singular, Variant(Int32)
    pub fn very_large_field_number(&self) -> i32 {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<i32, self::_puroro::tags::Int32> as NonRepeatedFieldType>::get_field(
            &self.very_large_field_number, &self._bitfield, ::std::default::Default::default,
        )
    }
    pub fn very_large_field_number_opt(&self) -> ::std::option::Option<i32> {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<i32, self::_puroro::tags::Int32> as NonRepeatedFieldType>::get_field_opt(
            &self.very_large_field_number, &self._bitfield,
        )
    }
    pub fn has_very_large_field_number(&self) -> bool {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<i32, self::_puroro::tags::Int32> as NonRepeatedFieldType>::get_field_opt(
            &self.very_large_field_number, &self._bitfield,
        ).is_some()
    }
    pub fn very_large_field_number_mut(&mut self) -> &mut i32 {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<i32, self::_puroro::tags::Int32> as NonRepeatedFieldType>::mut_field(
            &mut self.very_large_field_number, &mut self._bitfield, ::std::default::Default::default,
        )
    }
    pub fn clear_very_large_field_number(&mut self) {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField<i32, self::_puroro::tags::Int32> as NonRepeatedFieldType>::clear(
            &mut self.very_large_field_number, &mut self._bitfield,
        )
    }
}

impl self::_puroro::Message for Msg {
    fn from_bytes_iter<I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>>(
        iter: I,
    ) -> self::_puroro::Result<Self> {
        #[allow(unused)]
        use ::std::result::Result::Ok;
        let mut msg: Self = ::std::default::Default::default();
        msg.merge_from_bytes_iter(iter)?;
        Ok(msg)
    }

    fn merge_from_bytes_iter<I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>>(
        &mut self,
        mut iter: I,
    ) -> self::_puroro::Result<()> {
        #[allow(unused)]
        use ::std::option::Option::Some;
        #[allow(unused)]
        use ::std::result::Result::Ok;
        while let Some((number, _field_data)) =
            self::_puroro::internal::ser::FieldData::from_bytes_iter(iter.by_ref())?
        {
            match number {
                1 => <
                    self::_puroro::internal::field_type::SingularNumericalField<i32, self::_puroro::tags::Int32> as self::_puroro::internal::field_type::FieldType
                >::deser_from_iter(
                    &mut self.i32_unlabeled,
                    &mut self._bitfield,
                    _field_data,
                )?,
                2 => <
                    self::_puroro::internal::field_type::RepeatedNumericalField<i32, self::_puroro::tags::Int32> as self::_puroro::internal::field_type::FieldType
                >::deser_from_iter(
                    &mut self.i32_repeated,
                    &mut self._bitfield,
                    _field_data,
                )?,
                3 => <
                    self::_puroro::internal::field_type::SingularNumericalField<f32, self::_puroro::tags::Float> as self::_puroro::internal::field_type::FieldType
                >::deser_from_iter(
                    &mut self.float_unlabeled,
                    &mut self._bitfield,
                    _field_data,
                )?,
                4 => <
                    self::_puroro::internal::field_type::RepeatedNumericalField<f32, self::_puroro::tags::Float> as self::_puroro::internal::field_type::FieldType
                >::deser_from_iter(
                    &mut self.float_repeated,
                    &mut self._bitfield,
                    _field_data,
                )?,
                5 => <
                    self::_puroro::internal::field_type::SingularStringField as self::_puroro::internal::field_type::FieldType
                >::deser_from_iter(
                    &mut self.string_unlabeled,
                    &mut self._bitfield,
                    _field_data,
                )?,
                6 => <
                    self::_puroro::internal::field_type::RepeatedStringField as self::_puroro::internal::field_type::FieldType
                >::deser_from_iter(
                    &mut self.string_repeated,
                    &mut self._bitfield,
                    _field_data,
                )?,
                7 => <
                    self::_puroro::internal::field_type::SingularHeapMessageField<_puroro_root::ser_tests3::msg::Submsg> as self::_puroro::internal::field_type::FieldType
                >::deser_from_iter(
                    &mut self.submsg_unlabeled,
                    &mut self._bitfield,
                    _field_data,
                )?,
                8 => <
                    self::_puroro::internal::field_type::RepeatedMessageField<_puroro_root::ser_tests3::msg::Submsg> as self::_puroro::internal::field_type::FieldType
                >::deser_from_iter(
                    &mut self.submsg_repeated,
                    &mut self._bitfield,
                    _field_data,
                )?,
                9 => <
                    self::_puroro::internal::field_type::SingularNumericalField<_puroro_root::ser_tests3::Enum, self::_puroro::tags::Enum3<_puroro_root::ser_tests3::Enum>> as self::_puroro::internal::field_type::FieldType
                >::deser_from_iter(
                    &mut self.enum_unlabeled,
                    &mut self._bitfield,
                    _field_data,
                )?,
                10 => <
                    self::_puroro::internal::field_type::RepeatedNumericalField<_puroro_root::ser_tests3::Enum, self::_puroro::tags::Enum3<_puroro_root::ser_tests3::Enum>> as self::_puroro::internal::field_type::FieldType
                >::deser_from_iter(
                    &mut self.enum_repeated,
                    &mut self._bitfield,
                    _field_data,
                )?,
                536870911 => <
                    self::_puroro::internal::field_type::SingularNumericalField<i32, self::_puroro::tags::Int32> as self::_puroro::internal::field_type::FieldType
                >::deser_from_iter(
                    &mut self.very_large_field_number,
                    &mut self._bitfield,
                    _field_data,
                )?,
                _ => todo!(),
            }
        }
        Ok(())
    }
}
pub mod msg {

    mod _puroro {
        pub use super::super::_puroro::*;
    }
    mod _puroro_root {
        pub use super::super::_puroro_root::*;
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Enum {
    ZEROTH,
    FIRST,
    TENTH,
    _None(i32),
}

impl ::std::default::Default for Enum {
    fn default() -> Self {
        Enum::ZEROTH
    }
}

impl ::std::convert::From<i32> for Enum {
    fn from(x: i32) -> Self {
        match x {
            0 => self::Enum::ZEROTH,
            1 => self::Enum::FIRST,
            10 => self::Enum::TENTH,
            e => self::Enum::_None(e),
        }
    }
}

impl ::std::convert::From<Enum> for i32 {
    fn from(x: Enum) -> i32 {
        match x {
            self::Enum::ZEROTH => 0,
            self::Enum::FIRST => 1,
            self::Enum::TENTH => 10,
            self::Enum::_None(y) => y,
        }
    }
}
