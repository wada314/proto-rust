// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

pub mod compiler;

use super::GenericMessageExt;
use crate::generic_message::GenericMessage;
use crate::internal::impl_message_trait_for_trivial_types;
use crate::variant::variant_types::{Bool, Enum, Int32, Int64, UInt64};
use crate::Result;
use ::derive_more::{Deref as DDeref, DerefMut as DDerefMut, From as DFrom, Into as DInto};
use ::ref_cast::RefCast;
use ::std::alloc::Allocator;

#[derive(DDeref, DDerefMut, DFrom, DInto, Default, Debug, RefCast)]
#[repr(transparent)]
pub struct FileDescriptorSet(GenericMessage);
impl FileDescriptorSet {
    pub fn file(&self) -> impl Iterator<Item = &FileDescriptorProto> {
        self.0.as_repeated_message(1)
    }
}

#[derive(Default, Debug)]
pub enum Edition {
    #[default]
    EditionUnknown = 0,
    EditionProto2 = 998,
    EditionProto3 = 999,
    Edition2023 = 1000,
    Edition2024 = 1001,
    Edition1TestOnly = 1,
    Edition2TestOnly = 2,
    Edition99997TestOnly = 99997,
    Edition99998TestOnly = 99998,
    Edition99999TestOnly = 99999,
}
impl TryFrom<i32> for Edition {
    type Error = i32;
    fn try_from(value: i32) -> ::std::result::Result<Self, i32> {
        match value {
            0 => Ok(Self::EditionUnknown),
            998 => Ok(Self::EditionProto2),
            999 => Ok(Self::EditionProto3),
            1000 => Ok(Self::Edition2023),
            1001 => Ok(Self::Edition2024),
            1 => Ok(Self::Edition1TestOnly),
            2 => Ok(Self::Edition2TestOnly),
            99997 => Ok(Self::Edition99997TestOnly),
            99998 => Ok(Self::Edition99998TestOnly),
            99999 => Ok(Self::Edition99999TestOnly),
            _ => Err(value),
        }
    }
}
impl From<Edition> for i32 {
    fn from(value: Edition) -> i32 {
        value as i32
    }
}

#[derive(DDeref, DDerefMut, DFrom, DInto, Default, Debug, RefCast)]
#[repr(transparent)]
pub struct FileDescriptorProto(GenericMessage);
impl FileDescriptorProto {
    pub fn name(&self) -> &str {
        self.as_scalar_string(1)
    }
    pub fn package(&self) -> &str {
        self.as_scalar_string(2)
    }
    pub fn dependency(&self) -> impl Iterator<Item = &str> {
        self.as_repeated_string(3)
    }
    pub fn public_dependency(&self) -> impl '_ + Iterator<Item = i32> {
        self.as_repeated_int32(10)
    }
    pub fn weak_dependency(&self) -> impl '_ + Iterator<Item = i32> {
        self.as_repeated_int32(11)
    }
    pub fn message_type(&self) -> impl Iterator<Item = &DescriptorProto> {
        self.as_repeated_message(4)
    }
    pub fn enum_type(&self) -> impl Iterator<Item = &EnumDescriptorProto> {
        self.as_repeated_message(5)
    }
    pub fn syntax(&self) -> &str {
        self.as_scalar_string(12)
    }
    pub fn edition(&self) -> Edition {
        self.as_scalar_enum(14)
    }
}

#[derive(DDeref, DDerefMut, DFrom, DInto, Default, Debug, RefCast)]
#[repr(transparent)]
pub struct DescriptorProto(GenericMessage);
impl DescriptorProto {
    pub fn name(&self) -> &str {
        self.as_scalar_string(1)
    }
    pub fn field(&self) -> impl Iterator<Item = &FieldDescriptorProto> {
        self.as_repeated_message(2)
    }
    pub fn extension(&self) -> impl Iterator<Item = &FieldDescriptorProto> {
        self.as_repeated_message(6)
    }
    pub fn nested_type(&self) -> impl Iterator<Item = &DescriptorProto> {
        self.as_repeated_message(3)
    }
    pub fn enum_type(&self) -> impl Iterator<Item = &EnumDescriptorProto> {
        self.as_repeated_message(4)
    }
    pub fn oneof_decl(&self) -> impl Iterator<Item = &OneofDescriptorProto> {
        self.as_repeated_message(8)
    }
}

#[derive(DDeref, DDerefMut, DFrom, DInto, Default, Debug, RefCast)]
#[repr(transparent)]
pub struct FieldDescriptorProto(GenericMessage);
impl FieldDescriptorProto {
    pub fn name(&self) -> &str {
        self.as_scalar_string(1)
    }
    pub fn number(&self) -> i32 {
        self.as_scalar_int32(3)
    }
    pub fn label(&self) -> self::field_descriptor_proto::Label {
        self.as_scalar_enum(4)
    }
    pub fn type_(&self) -> field_descriptor_proto::Type {
        self.as_scalar_enum(5)
    }
    pub fn type_name(&self) -> &str {
        self.as_scalar_string(6)
    }
    pub fn extendee(&self) -> &str {
        self.as_scalar_string(2)
    }
    pub fn default_value(&self) -> &str {
        self.as_scalar_string(7)
    }
    pub fn oneof_index(&self) -> i32 {
        self.as_scalar_int32(9)
    }
    pub fn json_name(&self) -> &str {
        self.as_scalar_string(10)
    }
    pub fn proto3_optional(&self) -> bool {
        self.as_scalar_int32(17) != 0
    }
}

pub mod field_descriptor_proto {
    #[derive(Default, Debug)]
    pub enum Type {
        TypeDouble = 1,
        TypeFloat = 2,
        TypeInt64 = 3,
        TypeUInt64 = 4,
        #[default]
        TypeInt32 = 5,
        TypeFixed64 = 6,
        TypeFixed32 = 7,
        TypeBool = 8,
        TypeString = 9,
        TypeGroup = 10,
        TypeMessage = 11,
        TypeBytes = 12,
        TypeUInt32 = 13,
        TypeEnum = 14,
        TypeSFixed32 = 15,
        TypeSFixed64 = 16,
        TypeSInt32 = 17,
        TypeSInt64 = 18,
    }

    #[derive(Default, Debug)]
    pub enum Label {
        #[default]
        LabelOptional = 1,
        LabelRepeated = 3,
        LabelRequired = 2,
    }

    impl TryFrom<i32> for Type {
        type Error = i32;
        fn try_from(value: i32) -> ::std::result::Result<Self, i32> {
            match value {
                1 => Ok(Self::TypeDouble),
                2 => Ok(Self::TypeFloat),
                3 => Ok(Self::TypeInt64),
                4 => Ok(Self::TypeUInt64),
                5 => Ok(Self::TypeInt32),
                6 => Ok(Self::TypeFixed64),
                7 => Ok(Self::TypeFixed32),
                8 => Ok(Self::TypeBool),
                9 => Ok(Self::TypeString),
                10 => Ok(Self::TypeGroup),
                11 => Ok(Self::TypeMessage),
                12 => Ok(Self::TypeBytes),
                13 => Ok(Self::TypeUInt32),
                14 => Ok(Self::TypeEnum),
                15 => Ok(Self::TypeSFixed32),
                16 => Ok(Self::TypeSFixed64),
                17 => Ok(Self::TypeSInt32),
                18 => Ok(Self::TypeSInt64),
                _ => Err(value),
            }
        }
    }
    impl From<Type> for i32 {
        fn from(value: Type) -> i32 {
            value as i32
        }
    }

    impl TryFrom<i32> for Label {
        type Error = i32;
        fn try_from(value: i32) -> ::std::result::Result<Self, i32> {
            match value {
                1 => Ok(Self::LabelOptional),
                3 => Ok(Self::LabelRepeated),
                2 => Ok(Self::LabelRequired),
                _ => Err(value),
            }
        }
    }
    impl From<Label> for i32 {
        fn from(value: Label) -> i32 {
            value as i32
        }
    }
}

#[derive(DDeref, DDerefMut, DFrom, DInto, Default, Debug, RefCast)]
#[repr(transparent)]
pub struct OneofDescriptorProto(GenericMessage);
impl OneofDescriptorProto {
    pub fn name(&self) -> &str {
        self.as_scalar_string(1)
    }
}

#[derive(DDeref, DDerefMut, DFrom, DInto, Default, Debug, RefCast)]
#[repr(transparent)]
pub struct EnumDescriptorProto(GenericMessage);
impl EnumDescriptorProto {
    pub fn name(&self) -> &str {
        self.as_scalar_string(1)
    }
    pub fn value(&self) -> impl Iterator<Item = &EnumValueDescriptorProto> {
        self.as_repeated_message(2)
    }
}

#[derive(DDeref, DDerefMut, DFrom, DInto, Default, Debug, RefCast)]
#[repr(transparent)]
pub struct EnumValueDescriptorProto(GenericMessage);
impl EnumValueDescriptorProto {
    pub fn name(&self) -> &str {
        self.as_scalar_string(1)
    }
    pub fn number(&self) -> i32 {
        self.as_scalar_int32(2)
    }
}

impl_message_trait_for_trivial_types! {
    pub trait FileDescriptorSetTrait {
        fn file(&self) -> impl Iterator<Item = impl FileDescriptorTrait>;
    }

    pub trait FileDescriptorTrait {
        fn name(&self) -> &str;
        fn package(&self) -> &str;
        fn dependency(&self) -> impl Iterator<Item = &str>;
        fn public_dependency(&self) -> impl Iterator<Item = i32>;
        fn weak_dependency(&self) -> impl Iterator<Item = i32>;
        fn message_type(&self) -> impl Iterator<Item = impl DescriptorTrait>;
        fn enum_type(&self) -> impl Iterator<Item = impl EnumDescriptorTrait>;
        fn syntax(&self) -> &str;
        fn edition(&self) -> Edition;
    }

    pub trait DescriptorTrait {
        fn name(&self) -> &str;
        fn field(&self) -> impl Iterator<Item = impl FieldDescriptorTrait>;
        fn extension(&self) -> impl Iterator<Item = impl FieldDescriptorTrait>;
        fn nested_type(&self) -> impl Iterator<Item = impl DescriptorTrait>;
        fn enum_type(&self) -> impl Iterator<Item = impl EnumDescriptorTrait>;
        fn oneof_decl(&self) -> impl Iterator<Item = impl OneofDescriptorTrait>;
    }

    pub trait FieldDescriptorTrait {
        fn name(&self) -> &str;
        fn number(&self) -> i32;
        fn label(&self) -> field_descriptor_proto::Label;
        fn r#type(&self) -> field_descriptor_proto::Type;
        fn type_name(&self) -> &str;
        fn extendee(&self) -> &str;
        fn default_value(&self) -> &str;
        fn oneof_index(&self) -> i32;
        fn json_name(&self) -> &str;
        fn proto3_optional(&self) -> bool;
    }

    pub trait OneofDescriptorTrait {
        fn name(&self) -> &str;
    }

    pub trait EnumDescriptorTrait {
        fn name(&self) -> &str;
        fn value(&self) -> impl Iterator<Item = impl EnumValueDescriptorTrait>;
    }

    pub trait EnumValueDescriptorTrait {
        fn name(&self) -> &str;
        fn number(&self) -> i32;
    }
}

impl<A: Allocator + Clone> FileDescriptorSetTrait for GenericMessage<A> {
    fn file(&self) -> impl Iterator<Item = impl FileDescriptorTrait> {
        self.field(1).as_repeated_message()
    }
}

impl<A: Allocator + Clone> FileDescriptorTrait for GenericMessage<A> {
    fn name(&self) -> &str {
        self.field(1).as_scalar_string()
    }
    fn package(&self) -> &str {
        self.field(2).as_scalar_string()
    }
    fn dependency(&self) -> impl Iterator<Item = &str> {
        self.field(3).as_repeated_string()
    }
    fn public_dependency(&self) -> impl Iterator<Item = i32> {
        self.field(10).as_repeated_variant::<Int32>(false)
    }
    fn weak_dependency(&self) -> impl Iterator<Item = i32> {
        self.field(11).as_repeated_variant::<Int32>(false)
    }
    fn message_type(&self) -> impl Iterator<Item = impl DescriptorTrait> {
        self.field(4).as_repeated_message()
    }
    fn enum_type(&self) -> impl Iterator<Item = impl EnumDescriptorTrait> {
        self.field(5).as_repeated_message()
    }
    fn syntax(&self) -> &str {
        self.field(12).as_scalar_string()
    }
    fn edition(&self) -> Edition {
        self.field(14).as_scalar_variant::<Enum<Edition>>(false)
    }
}

impl<A: Allocator + Clone> DescriptorTrait for GenericMessage<A> {
    fn name(&self) -> &str {
        self.field(1).as_scalar_string()
    }
    fn field(&self) -> impl Iterator<Item = impl FieldDescriptorTrait> {
        self.field(2).as_repeated_message()
    }
    fn extension(&self) -> impl Iterator<Item = impl FieldDescriptorTrait> {
        self.field(6).as_repeated_message()
    }
    fn nested_type(&self) -> impl Iterator<Item = impl DescriptorTrait> {
        self.field(3).as_repeated_message()
    }
    fn enum_type(&self) -> impl Iterator<Item = impl EnumDescriptorTrait> {
        self.field(4).as_repeated_message()
    }
    fn oneof_decl(&self) -> impl Iterator<Item = impl OneofDescriptorTrait> {
        self.field(8).as_repeated_message()
    }
}

impl<A: Allocator + Clone> FieldDescriptorTrait for GenericMessage<A> {
    fn name(&self) -> &str {
        self.field(1).as_scalar_string()
    }
    fn number(&self) -> i32 {
        self.field(3).as_scalar_variant::<Int32>(false)
    }
    fn label(&self) -> field_descriptor_proto::Label {
        self.field(4)
            .as_scalar_variant::<Enum<field_descriptor_proto::Label>>(false)
    }
    fn r#type(&self) -> field_descriptor_proto::Type {
        self.field(5)
            .as_scalar_variant::<Enum<field_descriptor_proto::Type>>(false)
    }
    fn type_name(&self) -> &str {
        self.field(6).as_scalar_string()
    }
    fn extendee(&self) -> &str {
        self.field(2).as_scalar_string()
    }
    fn default_value(&self) -> &str {
        self.field(7).as_scalar_string()
    }
    fn oneof_index(&self) -> i32 {
        self.field(9).as_scalar_variant::<Int32>(false)
    }
    fn json_name(&self) -> &str {
        self.field(10).as_scalar_string()
    }
    fn proto3_optional(&self) -> bool {
        self.field(17).as_scalar_variant::<Bool>(false)
    }
}

impl<A: Allocator + Clone> OneofDescriptorTrait for GenericMessage<A> {
    fn name(&self) -> &str {
        self.field(1).as_scalar_string()
    }
}

impl<A: Allocator + Clone> EnumDescriptorTrait for GenericMessage<A> {
    fn name(&self) -> &str {
        self.field(1).as_scalar_string()
    }
    fn value(&self) -> impl Iterator<Item = impl EnumValueDescriptorTrait> {
        self.field(2).as_repeated_message()
    }
}

impl<A: Allocator + Clone> EnumValueDescriptorTrait for GenericMessage<A> {
    fn name(&self) -> &str {
        self.field(1).as_scalar_string()
    }
    fn number(&self) -> i32 {
        self.field(2).as_scalar_variant::<Int32>(false)
    }
}
