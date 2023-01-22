mod _root {
    #[allow(unused)]
    pub(crate) use super::super::_root::*;
}
mod _puroro {
    #[allow(unused)]
    pub(crate) use ::puroro::*;
}
mod _pinternal {
    #[allow(unused)]
    pub(crate) use ::puroro::internal::*;
}
pub mod msg;
#[derive(::std::default::Default)]
pub struct Msg {
    fields: self::_root::full_coverage3::_fields::MsgFields<
        self::_pinternal::SingularNumericalField::<i32, self::_pinternal::tags::Int32>,
        self::_pinternal::OptionalNumericalField::<
            i32,
            self::_pinternal::tags::Int32,
            0usize,
        >,
        self::_pinternal::RepeatedNumericalField::<i32, self::_pinternal::tags::Int32>,
        self::_pinternal::SingularNumericalField::<f32, self::_pinternal::tags::Float>,
        self::_pinternal::OptionalNumericalField::<
            f32,
            self::_pinternal::tags::Float,
            1usize,
        >,
        self::_pinternal::RepeatedNumericalField::<f32, self::_pinternal::tags::Float>,
        self::_pinternal::SingularUnsizedField::<
            ::std::vec::Vec<u8>,
            self::_pinternal::tags::Bytes,
        >,
        self::_pinternal::OptionalUnsizedField::<
            ::std::vec::Vec<u8>,
            self::_pinternal::tags::Bytes,
            2usize,
        >,
        self::_pinternal::RepeatedUnsizedField::<
            ::std::vec::Vec<u8>,
            self::_pinternal::tags::Bytes,
        >,
        self::_pinternal::SingularUnsizedField::<
            ::std::string::String,
            self::_pinternal::tags::String,
        >,
        self::_pinternal::OptionalUnsizedField::<
            ::std::string::String,
            self::_pinternal::tags::String,
            3usize,
        >,
        self::_pinternal::RepeatedUnsizedField::<
            ::std::string::String,
            self::_pinternal::tags::String,
        >,
        self::_pinternal::SingularNumericalField::<
            self::_root::full_coverage3::Enum,
            self::_pinternal::tags::Enum3::<self::_root::full_coverage3::Enum>,
        >,
        self::_pinternal::OptionalNumericalField::<
            self::_root::full_coverage3::Enum,
            self::_pinternal::tags::Enum3::<self::_root::full_coverage3::Enum>,
            4usize,
        >,
        self::_pinternal::RepeatedNumericalField::<
            self::_root::full_coverage3::Enum,
            self::_pinternal::tags::Enum3::<self::_root::full_coverage3::Enum>,
        >,
        self::_pinternal::SingularHeapMessageField::<
            self::_root::full_coverage3::msg::Submsg,
        >,
        self::_pinternal::SingularHeapMessageField::<
            self::_root::full_coverage3::msg::Submsg,
        >,
        self::_pinternal::RepeatedMessageField::<
            self::_root::full_coverage3::msg::Submsg,
        >,
        self::_pinternal::SingularNumericalField::<i64, self::_pinternal::tags::Int64>,
        self::_pinternal::OptionalNumericalField::<
            i64,
            self::_pinternal::tags::Int64,
            5usize,
        >,
        self::_pinternal::RepeatedNumericalField::<i64, self::_pinternal::tags::Int64>,
        self::_pinternal::SingularNumericalField::<u32, self::_pinternal::tags::UInt32>,
        self::_pinternal::OptionalNumericalField::<
            u32,
            self::_pinternal::tags::UInt32,
            6usize,
        >,
        self::_pinternal::RepeatedNumericalField::<u32, self::_pinternal::tags::UInt32>,
        self::_pinternal::SingularNumericalField::<u64, self::_pinternal::tags::UInt64>,
        self::_pinternal::OptionalNumericalField::<
            u64,
            self::_pinternal::tags::UInt64,
            7usize,
        >,
        self::_pinternal::RepeatedNumericalField::<u64, self::_pinternal::tags::UInt64>,
        self::_pinternal::SingularNumericalField::<i32, self::_pinternal::tags::SInt32>,
        self::_pinternal::OptionalNumericalField::<
            i32,
            self::_pinternal::tags::SInt32,
            8usize,
        >,
        self::_pinternal::RepeatedNumericalField::<i32, self::_pinternal::tags::SInt32>,
        self::_pinternal::SingularNumericalField::<i64, self::_pinternal::tags::SInt64>,
        self::_pinternal::OptionalNumericalField::<
            i64,
            self::_pinternal::tags::SInt64,
            9usize,
        >,
        self::_pinternal::RepeatedNumericalField::<i64, self::_pinternal::tags::SInt64>,
        self::_pinternal::SingularNumericalField::<u32, self::_pinternal::tags::Fixed32>,
        self::_pinternal::OptionalNumericalField::<
            u32,
            self::_pinternal::tags::Fixed32,
            10usize,
        >,
        self::_pinternal::RepeatedNumericalField::<u32, self::_pinternal::tags::Fixed32>,
        self::_pinternal::SingularNumericalField::<u64, self::_pinternal::tags::Fixed64>,
        self::_pinternal::OptionalNumericalField::<
            u64,
            self::_pinternal::tags::Fixed64,
            11usize,
        >,
        self::_pinternal::RepeatedNumericalField::<u64, self::_pinternal::tags::Fixed64>,
        self::_pinternal::SingularNumericalField::<
            i32,
            self::_pinternal::tags::SFixed32,
        >,
        self::_pinternal::OptionalNumericalField::<
            i32,
            self::_pinternal::tags::SFixed32,
            12usize,
        >,
        self::_pinternal::RepeatedNumericalField::<
            i32,
            self::_pinternal::tags::SFixed32,
        >,
        self::_pinternal::SingularNumericalField::<
            i64,
            self::_pinternal::tags::SFixed64,
        >,
        self::_pinternal::OptionalNumericalField::<
            i64,
            self::_pinternal::tags::SFixed64,
            13usize,
        >,
        self::_pinternal::RepeatedNumericalField::<
            i64,
            self::_pinternal::tags::SFixed64,
        >,
        self::_pinternal::SingularNumericalField::<f64, self::_pinternal::tags::Double>,
        self::_pinternal::OptionalNumericalField::<
            f64,
            self::_pinternal::tags::Double,
            14usize,
        >,
        self::_pinternal::RepeatedNumericalField::<f64, self::_pinternal::tags::Double>,
    >,
    shared: self::_pinternal::SharedItems<1usize>,
}
impl Msg {
    pub fn i32_unlabeled(&self) -> i32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.i32_unlabeled,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn i32_unlabeled_opt(&self) -> ::std::option::Option::<i32> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.i32_unlabeled,
            self.shared.bitfield(),
        )
    }
    pub fn i32_unlabeled_mut(&mut self) -> &mut i32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.i32_unlabeled,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_i32_unlabeled(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.i32_unlabeled,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_i32_unlabeled(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.i32_unlabeled,
            self.shared.bitfield_mut(),
        )
    }
    pub fn i32_optional(&self) -> i32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.i32_optional,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn i32_optional_opt(&self) -> ::std::option::Option::<i32> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.i32_optional,
            self.shared.bitfield(),
        )
    }
    pub fn i32_optional_mut(&mut self) -> &mut i32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.i32_optional,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_i32_optional(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.i32_optional,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_i32_optional(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.i32_optional,
            self.shared.bitfield_mut(),
        )
    }
    pub fn i32_repeated(&self) -> &[i32] {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field(&self.fields.i32_repeated, self.shared.bitfield())
    }
    pub fn i32_repeated_mut(&mut self) -> &mut ::std::vec::Vec::<i32> {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field_mut(
            &mut self.fields.i32_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn clear_i32_repeated(&mut self) {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::clear(
            &mut self.fields.i32_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn float_unlabeled(&self) -> f32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.float_unlabeled,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn float_unlabeled_opt(&self) -> ::std::option::Option::<f32> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.float_unlabeled,
            self.shared.bitfield(),
        )
    }
    pub fn float_unlabeled_mut(&mut self) -> &mut f32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.float_unlabeled,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_float_unlabeled(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.float_unlabeled,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_float_unlabeled(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.float_unlabeled,
            self.shared.bitfield_mut(),
        )
    }
    pub fn float_optional(&self) -> f32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.float_optional,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn float_optional_opt(&self) -> ::std::option::Option::<f32> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.float_optional,
            self.shared.bitfield(),
        )
    }
    pub fn float_optional_mut(&mut self) -> &mut f32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.float_optional,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_float_optional(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.float_optional,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_float_optional(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.float_optional,
            self.shared.bitfield_mut(),
        )
    }
    pub fn float_repeated(&self) -> &[f32] {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field(&self.fields.float_repeated, self.shared.bitfield())
    }
    pub fn float_repeated_mut(&mut self) -> &mut ::std::vec::Vec::<f32> {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field_mut(
            &mut self.fields.float_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn clear_float_repeated(&mut self) {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::clear(
            &mut self.fields.float_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn bytes_unlabeled(&self) -> &[u8] {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.bytes_unlabeled,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn bytes_unlabeled_opt(&self) -> ::std::option::Option::<&[u8]> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.bytes_unlabeled,
            self.shared.bitfield(),
        )
    }
    pub fn bytes_unlabeled_mut(&mut self) -> &mut ::std::vec::Vec::<u8> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.bytes_unlabeled,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_bytes_unlabeled(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.bytes_unlabeled,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_bytes_unlabeled(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.bytes_unlabeled,
            self.shared.bitfield_mut(),
        )
    }
    pub fn bytes_optional(&self) -> &[u8] {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.bytes_optional,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn bytes_optional_opt(&self) -> ::std::option::Option::<&[u8]> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.bytes_optional,
            self.shared.bitfield(),
        )
    }
    pub fn bytes_optional_mut(&mut self) -> &mut ::std::vec::Vec::<u8> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.bytes_optional,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_bytes_optional(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.bytes_optional,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_bytes_optional(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.bytes_optional,
            self.shared.bitfield_mut(),
        )
    }
    pub fn bytes_repeated(
        &self,
    ) -> &[impl ::std::ops::Deref::<
        Target = [u8],
    > + ::std::fmt::Debug + ::std::cmp::PartialEq] {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field(&self.fields.bytes_repeated, self.shared.bitfield())
    }
    pub fn bytes_repeated_mut(&mut self) -> &mut ::std::vec::Vec::<::std::vec::Vec<u8>> {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field_mut(
            &mut self.fields.bytes_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn clear_bytes_repeated(&mut self) {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::clear(
            &mut self.fields.bytes_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn string_unlabeled(&self) -> &str {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.string_unlabeled,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn string_unlabeled_opt(&self) -> ::std::option::Option::<&str> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.string_unlabeled,
            self.shared.bitfield(),
        )
    }
    pub fn string_unlabeled_mut(&mut self) -> &mut ::std::string::String {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.string_unlabeled,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_string_unlabeled(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.string_unlabeled,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_string_unlabeled(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.string_unlabeled,
            self.shared.bitfield_mut(),
        )
    }
    pub fn string_optional(&self) -> &str {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.string_optional,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn string_optional_opt(&self) -> ::std::option::Option::<&str> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.string_optional,
            self.shared.bitfield(),
        )
    }
    pub fn string_optional_mut(&mut self) -> &mut ::std::string::String {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.string_optional,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_string_optional(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.string_optional,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_string_optional(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.string_optional,
            self.shared.bitfield_mut(),
        )
    }
    pub fn string_repeated(
        &self,
    ) -> &[impl ::std::ops::Deref::<
        Target = str,
    > + ::std::fmt::Debug + ::std::cmp::PartialEq] {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field(
            &self.fields.string_repeated,
            self.shared.bitfield(),
        )
    }
    pub fn string_repeated_mut(
        &mut self,
    ) -> &mut ::std::vec::Vec::<::std::string::String> {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field_mut(
            &mut self.fields.string_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn clear_string_repeated(&mut self) {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::clear(
            &mut self.fields.string_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn enum_unlabeled(&self) -> self::_root::full_coverage3::Enum {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.enum_unlabeled,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn enum_unlabeled_opt(
        &self,
    ) -> ::std::option::Option::<self::_root::full_coverage3::Enum> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.enum_unlabeled,
            self.shared.bitfield(),
        )
    }
    pub fn enum_unlabeled_mut(&mut self) -> &mut self::_root::full_coverage3::Enum {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.enum_unlabeled,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_enum_unlabeled(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.enum_unlabeled,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_enum_unlabeled(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.enum_unlabeled,
            self.shared.bitfield_mut(),
        )
    }
    pub fn enum_optional(&self) -> self::_root::full_coverage3::Enum {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.enum_optional,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn enum_optional_opt(
        &self,
    ) -> ::std::option::Option::<self::_root::full_coverage3::Enum> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.enum_optional,
            self.shared.bitfield(),
        )
    }
    pub fn enum_optional_mut(&mut self) -> &mut self::_root::full_coverage3::Enum {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.enum_optional,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_enum_optional(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.enum_optional,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_enum_optional(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.enum_optional,
            self.shared.bitfield_mut(),
        )
    }
    pub fn enum_repeated(&self) -> &[self::_root::full_coverage3::Enum] {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field(&self.fields.enum_repeated, self.shared.bitfield())
    }
    pub fn enum_repeated_mut(
        &mut self,
    ) -> &mut ::std::vec::Vec::<self::_root::full_coverage3::Enum> {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field_mut(
            &mut self.fields.enum_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn clear_enum_repeated(&mut self) {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::clear(
            &mut self.fields.enum_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn submsg_unlabeled(
        &self,
    ) -> ::std::option::Option::<&self::_root::full_coverage3::msg::Submsg> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.submsg_unlabeled,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn submsg_unlabeled_opt(
        &self,
    ) -> ::std::option::Option::<&self::_root::full_coverage3::msg::Submsg> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.submsg_unlabeled,
            self.shared.bitfield(),
        )
    }
    pub fn submsg_unlabeled_mut(
        &mut self,
    ) -> &mut self::_root::full_coverage3::msg::Submsg {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.submsg_unlabeled,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_submsg_unlabeled(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.submsg_unlabeled,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_submsg_unlabeled(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.submsg_unlabeled,
            self.shared.bitfield_mut(),
        )
    }
    pub fn submsg_optional(
        &self,
    ) -> ::std::option::Option::<&self::_root::full_coverage3::msg::Submsg> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.submsg_optional,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn submsg_optional_opt(
        &self,
    ) -> ::std::option::Option::<&self::_root::full_coverage3::msg::Submsg> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.submsg_optional,
            self.shared.bitfield(),
        )
    }
    pub fn submsg_optional_mut(
        &mut self,
    ) -> &mut self::_root::full_coverage3::msg::Submsg {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.submsg_optional,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_submsg_optional(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.submsg_optional,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_submsg_optional(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.submsg_optional,
            self.shared.bitfield_mut(),
        )
    }
    pub fn submsg_repeated(&self) -> &[self::_root::full_coverage3::msg::Submsg] {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field(
            &self.fields.submsg_repeated,
            self.shared.bitfield(),
        )
    }
    pub fn submsg_repeated_mut(
        &mut self,
    ) -> &mut ::std::vec::Vec::<self::_root::full_coverage3::msg::Submsg> {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field_mut(
            &mut self.fields.submsg_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn clear_submsg_repeated(&mut self) {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::clear(
            &mut self.fields.submsg_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn i64_unlabeled(&self) -> i64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.i64_unlabeled,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn i64_unlabeled_opt(&self) -> ::std::option::Option::<i64> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.i64_unlabeled,
            self.shared.bitfield(),
        )
    }
    pub fn i64_unlabeled_mut(&mut self) -> &mut i64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.i64_unlabeled,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_i64_unlabeled(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.i64_unlabeled,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_i64_unlabeled(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.i64_unlabeled,
            self.shared.bitfield_mut(),
        )
    }
    pub fn i64_optional(&self) -> i64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.i64_optional,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn i64_optional_opt(&self) -> ::std::option::Option::<i64> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.i64_optional,
            self.shared.bitfield(),
        )
    }
    pub fn i64_optional_mut(&mut self) -> &mut i64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.i64_optional,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_i64_optional(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.i64_optional,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_i64_optional(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.i64_optional,
            self.shared.bitfield_mut(),
        )
    }
    pub fn i64_repeated(&self) -> &[i64] {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field(&self.fields.i64_repeated, self.shared.bitfield())
    }
    pub fn i64_repeated_mut(&mut self) -> &mut ::std::vec::Vec::<i64> {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field_mut(
            &mut self.fields.i64_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn clear_i64_repeated(&mut self) {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::clear(
            &mut self.fields.i64_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn u32_unlabeled(&self) -> u32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.u32_unlabeled,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn u32_unlabeled_opt(&self) -> ::std::option::Option::<u32> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.u32_unlabeled,
            self.shared.bitfield(),
        )
    }
    pub fn u32_unlabeled_mut(&mut self) -> &mut u32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.u32_unlabeled,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_u32_unlabeled(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.u32_unlabeled,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_u32_unlabeled(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.u32_unlabeled,
            self.shared.bitfield_mut(),
        )
    }
    pub fn u32_optional(&self) -> u32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.u32_optional,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn u32_optional_opt(&self) -> ::std::option::Option::<u32> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.u32_optional,
            self.shared.bitfield(),
        )
    }
    pub fn u32_optional_mut(&mut self) -> &mut u32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.u32_optional,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_u32_optional(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.u32_optional,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_u32_optional(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.u32_optional,
            self.shared.bitfield_mut(),
        )
    }
    pub fn u32_repeated(&self) -> &[u32] {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field(&self.fields.u32_repeated, self.shared.bitfield())
    }
    pub fn u32_repeated_mut(&mut self) -> &mut ::std::vec::Vec::<u32> {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field_mut(
            &mut self.fields.u32_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn clear_u32_repeated(&mut self) {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::clear(
            &mut self.fields.u32_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn u64_unlabeled(&self) -> u64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.u64_unlabeled,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn u64_unlabeled_opt(&self) -> ::std::option::Option::<u64> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.u64_unlabeled,
            self.shared.bitfield(),
        )
    }
    pub fn u64_unlabeled_mut(&mut self) -> &mut u64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.u64_unlabeled,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_u64_unlabeled(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.u64_unlabeled,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_u64_unlabeled(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.u64_unlabeled,
            self.shared.bitfield_mut(),
        )
    }
    pub fn u64_optional(&self) -> u64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.u64_optional,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn u64_optional_opt(&self) -> ::std::option::Option::<u64> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.u64_optional,
            self.shared.bitfield(),
        )
    }
    pub fn u64_optional_mut(&mut self) -> &mut u64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.u64_optional,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_u64_optional(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.u64_optional,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_u64_optional(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.u64_optional,
            self.shared.bitfield_mut(),
        )
    }
    pub fn u64_repeated(&self) -> &[u64] {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field(&self.fields.u64_repeated, self.shared.bitfield())
    }
    pub fn u64_repeated_mut(&mut self) -> &mut ::std::vec::Vec::<u64> {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field_mut(
            &mut self.fields.u64_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn clear_u64_repeated(&mut self) {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::clear(
            &mut self.fields.u64_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn s32_unlabeled(&self) -> i32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.s32_unlabeled,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn s32_unlabeled_opt(&self) -> ::std::option::Option::<i32> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.s32_unlabeled,
            self.shared.bitfield(),
        )
    }
    pub fn s32_unlabeled_mut(&mut self) -> &mut i32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.s32_unlabeled,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_s32_unlabeled(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.s32_unlabeled,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_s32_unlabeled(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.s32_unlabeled,
            self.shared.bitfield_mut(),
        )
    }
    pub fn s32_optional(&self) -> i32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.s32_optional,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn s32_optional_opt(&self) -> ::std::option::Option::<i32> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.s32_optional,
            self.shared.bitfield(),
        )
    }
    pub fn s32_optional_mut(&mut self) -> &mut i32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.s32_optional,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_s32_optional(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.s32_optional,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_s32_optional(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.s32_optional,
            self.shared.bitfield_mut(),
        )
    }
    pub fn s32_repeated(&self) -> &[i32] {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field(&self.fields.s32_repeated, self.shared.bitfield())
    }
    pub fn s32_repeated_mut(&mut self) -> &mut ::std::vec::Vec::<i32> {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field_mut(
            &mut self.fields.s32_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn clear_s32_repeated(&mut self) {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::clear(
            &mut self.fields.s32_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn s64_unlabeled(&self) -> i64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.s64_unlabeled,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn s64_unlabeled_opt(&self) -> ::std::option::Option::<i64> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.s64_unlabeled,
            self.shared.bitfield(),
        )
    }
    pub fn s64_unlabeled_mut(&mut self) -> &mut i64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.s64_unlabeled,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_s64_unlabeled(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.s64_unlabeled,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_s64_unlabeled(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.s64_unlabeled,
            self.shared.bitfield_mut(),
        )
    }
    pub fn s64_optional(&self) -> i64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.s64_optional,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn s64_optional_opt(&self) -> ::std::option::Option::<i64> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.s64_optional,
            self.shared.bitfield(),
        )
    }
    pub fn s64_optional_mut(&mut self) -> &mut i64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.s64_optional,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_s64_optional(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.s64_optional,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_s64_optional(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.s64_optional,
            self.shared.bitfield_mut(),
        )
    }
    pub fn s64_repeated(&self) -> &[i64] {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field(&self.fields.s64_repeated, self.shared.bitfield())
    }
    pub fn s64_repeated_mut(&mut self) -> &mut ::std::vec::Vec::<i64> {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field_mut(
            &mut self.fields.s64_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn clear_s64_repeated(&mut self) {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::clear(
            &mut self.fields.s64_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn fixed32_unlabeled(&self) -> u32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.fixed32_unlabeled,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn fixed32_unlabeled_opt(&self) -> ::std::option::Option::<u32> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.fixed32_unlabeled,
            self.shared.bitfield(),
        )
    }
    pub fn fixed32_unlabeled_mut(&mut self) -> &mut u32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.fixed32_unlabeled,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_fixed32_unlabeled(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.fixed32_unlabeled,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_fixed32_unlabeled(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.fixed32_unlabeled,
            self.shared.bitfield_mut(),
        )
    }
    pub fn fixed32_optional(&self) -> u32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.fixed32_optional,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn fixed32_optional_opt(&self) -> ::std::option::Option::<u32> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.fixed32_optional,
            self.shared.bitfield(),
        )
    }
    pub fn fixed32_optional_mut(&mut self) -> &mut u32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.fixed32_optional,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_fixed32_optional(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.fixed32_optional,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_fixed32_optional(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.fixed32_optional,
            self.shared.bitfield_mut(),
        )
    }
    pub fn fixed32_repeated(&self) -> &[u32] {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field(
            &self.fields.fixed32_repeated,
            self.shared.bitfield(),
        )
    }
    pub fn fixed32_repeated_mut(&mut self) -> &mut ::std::vec::Vec::<u32> {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field_mut(
            &mut self.fields.fixed32_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn clear_fixed32_repeated(&mut self) {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::clear(
            &mut self.fields.fixed32_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn fixed64_unlabeled(&self) -> u64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.fixed64_unlabeled,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn fixed64_unlabeled_opt(&self) -> ::std::option::Option::<u64> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.fixed64_unlabeled,
            self.shared.bitfield(),
        )
    }
    pub fn fixed64_unlabeled_mut(&mut self) -> &mut u64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.fixed64_unlabeled,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_fixed64_unlabeled(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.fixed64_unlabeled,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_fixed64_unlabeled(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.fixed64_unlabeled,
            self.shared.bitfield_mut(),
        )
    }
    pub fn fixed64_optional(&self) -> u64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.fixed64_optional,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn fixed64_optional_opt(&self) -> ::std::option::Option::<u64> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.fixed64_optional,
            self.shared.bitfield(),
        )
    }
    pub fn fixed64_optional_mut(&mut self) -> &mut u64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.fixed64_optional,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_fixed64_optional(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.fixed64_optional,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_fixed64_optional(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.fixed64_optional,
            self.shared.bitfield_mut(),
        )
    }
    pub fn fixed64_repeated(&self) -> &[u64] {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field(
            &self.fields.fixed64_repeated,
            self.shared.bitfield(),
        )
    }
    pub fn fixed64_repeated_mut(&mut self) -> &mut ::std::vec::Vec::<u64> {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field_mut(
            &mut self.fields.fixed64_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn clear_fixed64_repeated(&mut self) {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::clear(
            &mut self.fields.fixed64_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn sfixed32_unlabeled(&self) -> i32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.sfixed32_unlabeled,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn sfixed32_unlabeled_opt(&self) -> ::std::option::Option::<i32> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.sfixed32_unlabeled,
            self.shared.bitfield(),
        )
    }
    pub fn sfixed32_unlabeled_mut(&mut self) -> &mut i32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.sfixed32_unlabeled,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_sfixed32_unlabeled(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.sfixed32_unlabeled,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_sfixed32_unlabeled(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.sfixed32_unlabeled,
            self.shared.bitfield_mut(),
        )
    }
    pub fn sfixed32_optional(&self) -> i32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.sfixed32_optional,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn sfixed32_optional_opt(&self) -> ::std::option::Option::<i32> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.sfixed32_optional,
            self.shared.bitfield(),
        )
    }
    pub fn sfixed32_optional_mut(&mut self) -> &mut i32 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.sfixed32_optional,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_sfixed32_optional(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.sfixed32_optional,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_sfixed32_optional(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.sfixed32_optional,
            self.shared.bitfield_mut(),
        )
    }
    pub fn sfixed32_repeated(&self) -> &[i32] {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field(
            &self.fields.sfixed32_repeated,
            self.shared.bitfield(),
        )
    }
    pub fn sfixed32_repeated_mut(&mut self) -> &mut ::std::vec::Vec::<i32> {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field_mut(
            &mut self.fields.sfixed32_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn clear_sfixed32_repeated(&mut self) {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::clear(
            &mut self.fields.sfixed32_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn sfixed64_unlabeled(&self) -> i64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.sfixed64_unlabeled,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn sfixed64_unlabeled_opt(&self) -> ::std::option::Option::<i64> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.sfixed64_unlabeled,
            self.shared.bitfield(),
        )
    }
    pub fn sfixed64_unlabeled_mut(&mut self) -> &mut i64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.sfixed64_unlabeled,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_sfixed64_unlabeled(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.sfixed64_unlabeled,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_sfixed64_unlabeled(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.sfixed64_unlabeled,
            self.shared.bitfield_mut(),
        )
    }
    pub fn sfixed64_optional(&self) -> i64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.sfixed64_optional,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn sfixed64_optional_opt(&self) -> ::std::option::Option::<i64> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.sfixed64_optional,
            self.shared.bitfield(),
        )
    }
    pub fn sfixed64_optional_mut(&mut self) -> &mut i64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.sfixed64_optional,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_sfixed64_optional(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.sfixed64_optional,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_sfixed64_optional(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.sfixed64_optional,
            self.shared.bitfield_mut(),
        )
    }
    pub fn sfixed64_repeated(&self) -> &[i64] {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field(
            &self.fields.sfixed64_repeated,
            self.shared.bitfield(),
        )
    }
    pub fn sfixed64_repeated_mut(&mut self) -> &mut ::std::vec::Vec::<i64> {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field_mut(
            &mut self.fields.sfixed64_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn clear_sfixed64_repeated(&mut self) {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::clear(
            &mut self.fields.sfixed64_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn f64_unlabeled(&self) -> f64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.f64_unlabeled,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn f64_unlabeled_opt(&self) -> ::std::option::Option::<f64> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.f64_unlabeled,
            self.shared.bitfield(),
        )
    }
    pub fn f64_unlabeled_mut(&mut self) -> &mut f64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.f64_unlabeled,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_f64_unlabeled(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.f64_unlabeled,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_f64_unlabeled(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.f64_unlabeled,
            self.shared.bitfield_mut(),
        )
    }
    pub fn f64_optional(&self) -> f64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_or_else(
            &self.fields.f64_optional,
            self.shared.bitfield(),
            ::std::default::Default::default,
        )
    }
    pub fn f64_optional_opt(&self) -> ::std::option::Option::<f64> {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
            &self.fields.f64_optional,
            self.shared.bitfield(),
        )
    }
    pub fn f64_optional_mut(&mut self) -> &mut f64 {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_mut(
            &mut self.fields.f64_optional,
            self.shared.bitfield_mut(),
            ::std::default::Default::default,
        )
    }
    pub fn has_f64_optional(&self) -> bool {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::get_field_opt(
                &self.fields.f64_optional,
                self.shared.bitfield(),
            )
            .is_some()
    }
    pub fn clear_f64_optional(&mut self) {
        use self::_pinternal::{NonRepeatedFieldType, SharedItemsTrait as _};
        NonRepeatedFieldType::clear(
            &mut self.fields.f64_optional,
            self.shared.bitfield_mut(),
        )
    }
    pub fn f64_repeated(&self) -> &[f64] {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field(&self.fields.f64_repeated, self.shared.bitfield())
    }
    pub fn f64_repeated_mut(&mut self) -> &mut ::std::vec::Vec::<f64> {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::get_field_mut(
            &mut self.fields.f64_repeated,
            self.shared.bitfield_mut(),
        )
    }
    pub fn clear_f64_repeated(&mut self) {
        use self::_pinternal::{RepeatedFieldType, SharedItemsTrait as _};
        RepeatedFieldType::clear(
            &mut self.fields.f64_repeated,
            self.shared.bitfield_mut(),
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
        use self::_pinternal::ser::FieldData;
        #[allow(unused)]
        use self::_pinternal::OneofUnion as _;
        use self::_pinternal::{SharedItemsTrait as _, UnknownFields as _};
        #[allow(unused)]
        use ::std::result::Result::{Ok, Err};
        use self::_puroro::PuroroError;
        while let Some((number, mut field_data))
            = FieldData::from_bytes_iter(iter.by_ref())? {
            let result: self::_puroro::Result<()> = (|| {
                match number {
                    1i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.i32_unlabeled,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    2i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.i32_optional,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    3i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.i32_repeated,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    11i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.float_unlabeled,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    12i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.float_optional,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    13i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.float_repeated,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    21i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.bytes_unlabeled,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    22i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.bytes_optional,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    23i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.bytes_repeated,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    31i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.string_unlabeled,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    32i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.string_optional,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    33i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.string_repeated,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    41i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.enum_unlabeled,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    42i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.enum_optional,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    43i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.enum_repeated,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    51i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.submsg_unlabeled,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    52i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.submsg_optional,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    53i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.submsg_repeated,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    101i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.i64_unlabeled,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    102i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.i64_optional,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    103i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.i64_repeated,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    111i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.u32_unlabeled,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    112i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.u32_optional,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    113i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.u32_repeated,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    121i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.u64_unlabeled,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    122i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.u64_optional,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    123i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.u64_repeated,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    131i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.s32_unlabeled,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    132i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.s32_optional,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    133i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.s32_repeated,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    141i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.s64_unlabeled,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    142i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.s64_optional,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    143i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.s64_repeated,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    151i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.fixed32_unlabeled,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    152i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.fixed32_optional,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    153i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.fixed32_repeated,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    161i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.fixed64_unlabeled,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    162i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.fixed64_optional,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    163i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.fixed64_repeated,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    171i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.sfixed32_unlabeled,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    172i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.sfixed32_optional,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    173i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.sfixed32_repeated,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    181i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.sfixed64_unlabeled,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    182i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.sfixed64_optional,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    183i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.sfixed64_repeated,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    191i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.f64_unlabeled,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    192i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.f64_optional,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    193i32 => {
                        self::_pinternal::FieldType::deser_from_iter(
                            &mut self.fields.f64_repeated,
                            self.shared.bitfield_mut(),
                            &mut field_data,
                        )?
                    }
                    _ => Err(PuroroError::UnknownFieldNumber)?,
                }
                Ok(())
            })();
            match result {
                Ok(_) => {}
                Err(
                    PuroroError::UnknownFieldNumber | PuroroError::UnknownEnumVariant(_),
                ) => {
                    self.shared.unknown_fields_mut().push(number, field_data)?;
                }
                Err(e) => Err(e)?,
            }
        }
        Ok(())
    }
    fn to_bytes<W: ::std::io::Write>(
        &self,
        #[allow(unused)]
        out: &mut W,
    ) -> self::_puroro::Result<()> {
        #[allow(unused)]
        use self::_pinternal::OneofUnion as _;
        use self::_pinternal::{SharedItemsTrait as _, UnknownFields as _};
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.i32_unlabeled,
            self.shared.bitfield(),
            1i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.i32_optional,
            self.shared.bitfield(),
            2i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.i32_repeated,
            self.shared.bitfield(),
            3i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.float_unlabeled,
            self.shared.bitfield(),
            11i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.float_optional,
            self.shared.bitfield(),
            12i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.float_repeated,
            self.shared.bitfield(),
            13i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.bytes_unlabeled,
            self.shared.bitfield(),
            21i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.bytes_optional,
            self.shared.bitfield(),
            22i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.bytes_repeated,
            self.shared.bitfield(),
            23i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.string_unlabeled,
            self.shared.bitfield(),
            31i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.string_optional,
            self.shared.bitfield(),
            32i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.string_repeated,
            self.shared.bitfield(),
            33i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.enum_unlabeled,
            self.shared.bitfield(),
            41i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.enum_optional,
            self.shared.bitfield(),
            42i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.enum_repeated,
            self.shared.bitfield(),
            43i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.submsg_unlabeled,
            self.shared.bitfield(),
            51i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.submsg_optional,
            self.shared.bitfield(),
            52i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.submsg_repeated,
            self.shared.bitfield(),
            53i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.i64_unlabeled,
            self.shared.bitfield(),
            101i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.i64_optional,
            self.shared.bitfield(),
            102i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.i64_repeated,
            self.shared.bitfield(),
            103i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.u32_unlabeled,
            self.shared.bitfield(),
            111i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.u32_optional,
            self.shared.bitfield(),
            112i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.u32_repeated,
            self.shared.bitfield(),
            113i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.u64_unlabeled,
            self.shared.bitfield(),
            121i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.u64_optional,
            self.shared.bitfield(),
            122i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.u64_repeated,
            self.shared.bitfield(),
            123i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.s32_unlabeled,
            self.shared.bitfield(),
            131i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.s32_optional,
            self.shared.bitfield(),
            132i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.s32_repeated,
            self.shared.bitfield(),
            133i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.s64_unlabeled,
            self.shared.bitfield(),
            141i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.s64_optional,
            self.shared.bitfield(),
            142i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.s64_repeated,
            self.shared.bitfield(),
            143i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.fixed32_unlabeled,
            self.shared.bitfield(),
            151i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.fixed32_optional,
            self.shared.bitfield(),
            152i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.fixed32_repeated,
            self.shared.bitfield(),
            153i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.fixed64_unlabeled,
            self.shared.bitfield(),
            161i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.fixed64_optional,
            self.shared.bitfield(),
            162i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.fixed64_repeated,
            self.shared.bitfield(),
            163i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.sfixed32_unlabeled,
            self.shared.bitfield(),
            171i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.sfixed32_optional,
            self.shared.bitfield(),
            172i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.sfixed32_repeated,
            self.shared.bitfield(),
            173i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.sfixed64_unlabeled,
            self.shared.bitfield(),
            181i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.sfixed64_optional,
            self.shared.bitfield(),
            182i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.sfixed64_repeated,
            self.shared.bitfield(),
            183i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.f64_unlabeled,
            self.shared.bitfield(),
            191i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.f64_optional,
            self.shared.bitfield(),
            192i32,
            out,
        )?;
        self::_pinternal::FieldType::ser_to_write(
            &self.fields.f64_repeated,
            self.shared.bitfield(),
            193i32,
            out,
        )?;
        self.shared.unknown_fields().ser_to_write(out)?;
        ::std::result::Result::Ok(())
    }
}
impl ::std::clone::Clone for Msg {
    fn clone(&self) -> Self {
        #[allow(unused)]
        use self::_pinternal::SharedItemsTrait as _;
        Self {
            fields: self::_fields::MsgFields {
                i32_unlabeled: ::std::clone::Clone::clone(&self.fields.i32_unlabeled),
                i32_optional: ::std::clone::Clone::clone(&self.fields.i32_optional),
                i32_repeated: ::std::clone::Clone::clone(&self.fields.i32_repeated),
                float_unlabeled: ::std::clone::Clone::clone(
                    &self.fields.float_unlabeled,
                ),
                float_optional: ::std::clone::Clone::clone(&self.fields.float_optional),
                float_repeated: ::std::clone::Clone::clone(&self.fields.float_repeated),
                bytes_unlabeled: ::std::clone::Clone::clone(
                    &self.fields.bytes_unlabeled,
                ),
                bytes_optional: ::std::clone::Clone::clone(&self.fields.bytes_optional),
                bytes_repeated: ::std::clone::Clone::clone(&self.fields.bytes_repeated),
                string_unlabeled: ::std::clone::Clone::clone(
                    &self.fields.string_unlabeled,
                ),
                string_optional: ::std::clone::Clone::clone(
                    &self.fields.string_optional,
                ),
                string_repeated: ::std::clone::Clone::clone(
                    &self.fields.string_repeated,
                ),
                enum_unlabeled: ::std::clone::Clone::clone(&self.fields.enum_unlabeled),
                enum_optional: ::std::clone::Clone::clone(&self.fields.enum_optional),
                enum_repeated: ::std::clone::Clone::clone(&self.fields.enum_repeated),
                submsg_unlabeled: ::std::clone::Clone::clone(
                    &self.fields.submsg_unlabeled,
                ),
                submsg_optional: ::std::clone::Clone::clone(
                    &self.fields.submsg_optional,
                ),
                submsg_repeated: ::std::clone::Clone::clone(
                    &self.fields.submsg_repeated,
                ),
                i64_unlabeled: ::std::clone::Clone::clone(&self.fields.i64_unlabeled),
                i64_optional: ::std::clone::Clone::clone(&self.fields.i64_optional),
                i64_repeated: ::std::clone::Clone::clone(&self.fields.i64_repeated),
                u32_unlabeled: ::std::clone::Clone::clone(&self.fields.u32_unlabeled),
                u32_optional: ::std::clone::Clone::clone(&self.fields.u32_optional),
                u32_repeated: ::std::clone::Clone::clone(&self.fields.u32_repeated),
                u64_unlabeled: ::std::clone::Clone::clone(&self.fields.u64_unlabeled),
                u64_optional: ::std::clone::Clone::clone(&self.fields.u64_optional),
                u64_repeated: ::std::clone::Clone::clone(&self.fields.u64_repeated),
                s32_unlabeled: ::std::clone::Clone::clone(&self.fields.s32_unlabeled),
                s32_optional: ::std::clone::Clone::clone(&self.fields.s32_optional),
                s32_repeated: ::std::clone::Clone::clone(&self.fields.s32_repeated),
                s64_unlabeled: ::std::clone::Clone::clone(&self.fields.s64_unlabeled),
                s64_optional: ::std::clone::Clone::clone(&self.fields.s64_optional),
                s64_repeated: ::std::clone::Clone::clone(&self.fields.s64_repeated),
                fixed32_unlabeled: ::std::clone::Clone::clone(
                    &self.fields.fixed32_unlabeled,
                ),
                fixed32_optional: ::std::clone::Clone::clone(
                    &self.fields.fixed32_optional,
                ),
                fixed32_repeated: ::std::clone::Clone::clone(
                    &self.fields.fixed32_repeated,
                ),
                fixed64_unlabeled: ::std::clone::Clone::clone(
                    &self.fields.fixed64_unlabeled,
                ),
                fixed64_optional: ::std::clone::Clone::clone(
                    &self.fields.fixed64_optional,
                ),
                fixed64_repeated: ::std::clone::Clone::clone(
                    &self.fields.fixed64_repeated,
                ),
                sfixed32_unlabeled: ::std::clone::Clone::clone(
                    &self.fields.sfixed32_unlabeled,
                ),
                sfixed32_optional: ::std::clone::Clone::clone(
                    &self.fields.sfixed32_optional,
                ),
                sfixed32_repeated: ::std::clone::Clone::clone(
                    &self.fields.sfixed32_repeated,
                ),
                sfixed64_unlabeled: ::std::clone::Clone::clone(
                    &self.fields.sfixed64_unlabeled,
                ),
                sfixed64_optional: ::std::clone::Clone::clone(
                    &self.fields.sfixed64_optional,
                ),
                sfixed64_repeated: ::std::clone::Clone::clone(
                    &self.fields.sfixed64_repeated,
                ),
                f64_unlabeled: ::std::clone::Clone::clone(&self.fields.f64_unlabeled),
                f64_optional: ::std::clone::Clone::clone(&self.fields.f64_optional),
                f64_repeated: ::std::clone::Clone::clone(&self.fields.f64_repeated),
            },
            shared: ::std::clone::Clone::clone(&self.shared),
        }
    }
}
impl ::std::ops::Drop for Msg {
    fn drop(&mut self) {
        #[allow(unused)]
        use self::_pinternal::OneofUnion as _;
        use self::_pinternal::SharedItemsTrait as _;
    }
}
impl ::std::fmt::Debug for Msg {
    fn fmt(
        &self,
        fmt: &mut ::std::fmt::Formatter<'_>,
    ) -> ::std::result::Result<(), ::std::fmt::Error> {
        use self::_pinternal::{SharedItemsTrait as _, UnknownFields as _};
        let mut debug_struct = fmt.debug_struct(stringify!(Msg));
        debug_struct
            .field(stringify!(i32_unlabeled), &self.i32_unlabeled_opt())
            .field(stringify!(i32_optional), &self.i32_optional_opt())
            .field(stringify!(i32_repeated), &self.i32_repeated())
            .field(stringify!(float_unlabeled), &self.float_unlabeled_opt())
            .field(stringify!(float_optional), &self.float_optional_opt())
            .field(stringify!(float_repeated), &self.float_repeated())
            .field(stringify!(bytes_unlabeled), &self.bytes_unlabeled_opt())
            .field(stringify!(bytes_optional), &self.bytes_optional_opt())
            .field(stringify!(bytes_repeated), &self.bytes_repeated())
            .field(stringify!(string_unlabeled), &self.string_unlabeled_opt())
            .field(stringify!(string_optional), &self.string_optional_opt())
            .field(stringify!(string_repeated), &self.string_repeated())
            .field(stringify!(enum_unlabeled), &self.enum_unlabeled_opt())
            .field(stringify!(enum_optional), &self.enum_optional_opt())
            .field(stringify!(enum_repeated), &self.enum_repeated())
            .field(stringify!(submsg_unlabeled), &self.submsg_unlabeled_opt())
            .field(stringify!(submsg_optional), &self.submsg_optional_opt())
            .field(stringify!(submsg_repeated), &self.submsg_repeated())
            .field(stringify!(i64_unlabeled), &self.i64_unlabeled_opt())
            .field(stringify!(i64_optional), &self.i64_optional_opt())
            .field(stringify!(i64_repeated), &self.i64_repeated())
            .field(stringify!(u32_unlabeled), &self.u32_unlabeled_opt())
            .field(stringify!(u32_optional), &self.u32_optional_opt())
            .field(stringify!(u32_repeated), &self.u32_repeated())
            .field(stringify!(u64_unlabeled), &self.u64_unlabeled_opt())
            .field(stringify!(u64_optional), &self.u64_optional_opt())
            .field(stringify!(u64_repeated), &self.u64_repeated())
            .field(stringify!(s32_unlabeled), &self.s32_unlabeled_opt())
            .field(stringify!(s32_optional), &self.s32_optional_opt())
            .field(stringify!(s32_repeated), &self.s32_repeated())
            .field(stringify!(s64_unlabeled), &self.s64_unlabeled_opt())
            .field(stringify!(s64_optional), &self.s64_optional_opt())
            .field(stringify!(s64_repeated), &self.s64_repeated())
            .field(stringify!(fixed32_unlabeled), &self.fixed32_unlabeled_opt())
            .field(stringify!(fixed32_optional), &self.fixed32_optional_opt())
            .field(stringify!(fixed32_repeated), &self.fixed32_repeated())
            .field(stringify!(fixed64_unlabeled), &self.fixed64_unlabeled_opt())
            .field(stringify!(fixed64_optional), &self.fixed64_optional_opt())
            .field(stringify!(fixed64_repeated), &self.fixed64_repeated())
            .field(stringify!(sfixed32_unlabeled), &self.sfixed32_unlabeled_opt())
            .field(stringify!(sfixed32_optional), &self.sfixed32_optional_opt())
            .field(stringify!(sfixed32_repeated), &self.sfixed32_repeated())
            .field(stringify!(sfixed64_unlabeled), &self.sfixed64_unlabeled_opt())
            .field(stringify!(sfixed64_optional), &self.sfixed64_optional_opt())
            .field(stringify!(sfixed64_repeated), &self.sfixed64_repeated())
            .field(stringify!(f64_unlabeled), &self.f64_unlabeled_opt())
            .field(stringify!(f64_optional), &self.f64_optional_opt())
            .field(stringify!(f64_repeated), &self.f64_repeated());
        self.shared.unknown_fields().debug_struct_fields(&mut debug_struct)?;
        debug_struct.finish()
    }
}
impl ::std::cmp::PartialEq for Msg {
    fn eq(&self, rhs: &Self) -> bool {
        #[allow(unused)]
        use self::_pinternal::OneofUnion as _;
        use self::_pinternal::SharedItemsTrait as _;
        true && self.i32_unlabeled_opt() == rhs.i32_unlabeled_opt()
            && self.i32_optional_opt() == rhs.i32_optional_opt()
            && self.i32_repeated() == rhs.i32_repeated()
            && self.float_unlabeled_opt() == rhs.float_unlabeled_opt()
            && self.float_optional_opt() == rhs.float_optional_opt()
            && self.float_repeated() == rhs.float_repeated()
            && self.bytes_unlabeled_opt() == rhs.bytes_unlabeled_opt()
            && self.bytes_optional_opt() == rhs.bytes_optional_opt()
            && self.bytes_repeated() == rhs.bytes_repeated()
            && self.string_unlabeled_opt() == rhs.string_unlabeled_opt()
            && self.string_optional_opt() == rhs.string_optional_opt()
            && self.string_repeated() == rhs.string_repeated()
            && self.enum_unlabeled_opt() == rhs.enum_unlabeled_opt()
            && self.enum_optional_opt() == rhs.enum_optional_opt()
            && self.enum_repeated() == rhs.enum_repeated()
            && self.submsg_unlabeled_opt() == rhs.submsg_unlabeled_opt()
            && self.submsg_optional_opt() == rhs.submsg_optional_opt()
            && self.submsg_repeated() == rhs.submsg_repeated()
            && self.i64_unlabeled_opt() == rhs.i64_unlabeled_opt()
            && self.i64_optional_opt() == rhs.i64_optional_opt()
            && self.i64_repeated() == rhs.i64_repeated()
            && self.u32_unlabeled_opt() == rhs.u32_unlabeled_opt()
            && self.u32_optional_opt() == rhs.u32_optional_opt()
            && self.u32_repeated() == rhs.u32_repeated()
            && self.u64_unlabeled_opt() == rhs.u64_unlabeled_opt()
            && self.u64_optional_opt() == rhs.u64_optional_opt()
            && self.u64_repeated() == rhs.u64_repeated()
            && self.s32_unlabeled_opt() == rhs.s32_unlabeled_opt()
            && self.s32_optional_opt() == rhs.s32_optional_opt()
            && self.s32_repeated() == rhs.s32_repeated()
            && self.s64_unlabeled_opt() == rhs.s64_unlabeled_opt()
            && self.s64_optional_opt() == rhs.s64_optional_opt()
            && self.s64_repeated() == rhs.s64_repeated()
            && self.fixed32_unlabeled_opt() == rhs.fixed32_unlabeled_opt()
            && self.fixed32_optional_opt() == rhs.fixed32_optional_opt()
            && self.fixed32_repeated() == rhs.fixed32_repeated()
            && self.fixed64_unlabeled_opt() == rhs.fixed64_unlabeled_opt()
            && self.fixed64_optional_opt() == rhs.fixed64_optional_opt()
            && self.fixed64_repeated() == rhs.fixed64_repeated()
            && self.sfixed32_unlabeled_opt() == rhs.sfixed32_unlabeled_opt()
            && self.sfixed32_optional_opt() == rhs.sfixed32_optional_opt()
            && self.sfixed32_repeated() == rhs.sfixed32_repeated()
            && self.sfixed64_unlabeled_opt() == rhs.sfixed64_unlabeled_opt()
            && self.sfixed64_optional_opt() == rhs.sfixed64_optional_opt()
            && self.sfixed64_repeated() == rhs.sfixed64_repeated()
            && self.f64_unlabeled_opt() == rhs.f64_unlabeled_opt()
            && self.f64_optional_opt() == rhs.f64_optional_opt()
            && self.f64_repeated() == rhs.f64_repeated()
            && self.shared.unknown_fields() == rhs.shared.unknown_fields()
    }
}
pub mod _fields {
    mod _root {
        #[allow(unused)]
        pub use super::super::_root::*;
    }
    mod _puroro {
        #[allow(unused)]
        pub use ::puroro::*;
    }
    mod _pinternal {
        #[allow(unused)]
        pub use ::puroro::internal::*;
    }
    #[derive(::std::default::Default)]
    pub struct MsgFields<
        TI32Unlabeled,
        TI32Optional,
        TI32Repeated,
        TFloatUnlabeled,
        TFloatOptional,
        TFloatRepeated,
        TBytesUnlabeled,
        TBytesOptional,
        TBytesRepeated,
        TStringUnlabeled,
        TStringOptional,
        TStringRepeated,
        TEnumUnlabeled,
        TEnumOptional,
        TEnumRepeated,
        TSubmsgUnlabeled,
        TSubmsgOptional,
        TSubmsgRepeated,
        TI64Unlabeled,
        TI64Optional,
        TI64Repeated,
        TU32Unlabeled,
        TU32Optional,
        TU32Repeated,
        TU64Unlabeled,
        TU64Optional,
        TU64Repeated,
        TS32Unlabeled,
        TS32Optional,
        TS32Repeated,
        TS64Unlabeled,
        TS64Optional,
        TS64Repeated,
        TFixed32Unlabeled,
        TFixed32Optional,
        TFixed32Repeated,
        TFixed64Unlabeled,
        TFixed64Optional,
        TFixed64Repeated,
        TSfixed32Unlabeled,
        TSfixed32Optional,
        TSfixed32Repeated,
        TSfixed64Unlabeled,
        TSfixed64Optional,
        TSfixed64Repeated,
        TF64Unlabeled,
        TF64Optional,
        TF64Repeated,
    > {
        pub i32_unlabeled: TI32Unlabeled,
        pub i32_optional: TI32Optional,
        pub i32_repeated: TI32Repeated,
        pub float_unlabeled: TFloatUnlabeled,
        pub float_optional: TFloatOptional,
        pub float_repeated: TFloatRepeated,
        pub bytes_unlabeled: TBytesUnlabeled,
        pub bytes_optional: TBytesOptional,
        pub bytes_repeated: TBytesRepeated,
        pub string_unlabeled: TStringUnlabeled,
        pub string_optional: TStringOptional,
        pub string_repeated: TStringRepeated,
        pub enum_unlabeled: TEnumUnlabeled,
        pub enum_optional: TEnumOptional,
        pub enum_repeated: TEnumRepeated,
        pub submsg_unlabeled: TSubmsgUnlabeled,
        pub submsg_optional: TSubmsgOptional,
        pub submsg_repeated: TSubmsgRepeated,
        pub i64_unlabeled: TI64Unlabeled,
        pub i64_optional: TI64Optional,
        pub i64_repeated: TI64Repeated,
        pub u32_unlabeled: TU32Unlabeled,
        pub u32_optional: TU32Optional,
        pub u32_repeated: TU32Repeated,
        pub u64_unlabeled: TU64Unlabeled,
        pub u64_optional: TU64Optional,
        pub u64_repeated: TU64Repeated,
        pub s32_unlabeled: TS32Unlabeled,
        pub s32_optional: TS32Optional,
        pub s32_repeated: TS32Repeated,
        pub s64_unlabeled: TS64Unlabeled,
        pub s64_optional: TS64Optional,
        pub s64_repeated: TS64Repeated,
        pub fixed32_unlabeled: TFixed32Unlabeled,
        pub fixed32_optional: TFixed32Optional,
        pub fixed32_repeated: TFixed32Repeated,
        pub fixed64_unlabeled: TFixed64Unlabeled,
        pub fixed64_optional: TFixed64Optional,
        pub fixed64_repeated: TFixed64Repeated,
        pub sfixed32_unlabeled: TSfixed32Unlabeled,
        pub sfixed32_optional: TSfixed32Optional,
        pub sfixed32_repeated: TSfixed32Repeated,
        pub sfixed64_unlabeled: TSfixed64Unlabeled,
        pub sfixed64_optional: TSfixed64Optional,
        pub sfixed64_repeated: TSfixed64Repeated,
        pub f64_unlabeled: TF64Unlabeled,
        pub f64_optional: TF64Optional,
        pub f64_repeated: TF64Repeated,
    }
}
pub use self::_fields::*;
#[derive(
    ::std::clone::Clone,
    ::std::marker::Copy,
    ::std::cmp::PartialEq,
    ::std::cmp::Eq,
    ::std::cmp::PartialOrd,
    ::std::cmp::Ord,
    ::std::hash::Hash,
    ::std::fmt::Debug,
)]
pub enum Enum {
    Zeroth,
    First,
    Tenth,
    _None(i32),
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
            self::Enum::_None(i) => i,
        }
    }
}
impl ::std::convert::From::<i32> for Enum {
    fn from(val: i32) -> Self {
        match val {
            0i32 => self::Enum::Zeroth,
            1i32 => self::Enum::First,
            10i32 => self::Enum::Tenth,
            _ => Enum::_None(val),
        }
    }
}
