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

use crate::bitvec::BitSlice;
use crate::internal::ser::FieldData;
use crate::{tags, ErrorKind, Result};
use ::std::io::Result as IoResult;
use ::std::marker::PhantomData;

pub trait FieldType {
    type GetterType<'a>
    where
        Self: 'a;
    fn get_field<B: BitSlice>(&self, bitvec: &B) -> Self::GetterType<'_>;
    #[allow(unused)]
    fn deser_from_iter<I: Iterator<Item = IoResult<u8>>, B: BitSlice>(
        &mut self,
        bitvec: &mut B,
        field_data: FieldData<I>,
    ) -> Result<()> {
        todo!()
    }
}

#[derive(Default, Clone)]
pub struct Dummy;
impl FieldType for Dummy {
    type GetterType<'a> = ()
    where
        Self: 'a;
    fn get_field<B: BitSlice>(&self, _bitvec: &B) -> Self::GetterType<'_> {
        todo!()
    }
}

#[derive(Default, Clone)]
pub struct SingularVariantField<RustType, ProtoType>(RustType, PhantomData<ProtoType>);
#[derive(Default, Clone)]
pub struct OptionalVariantField<RustType, ProtoType, const BITFIELD_INDEX: usize>(
    RustType,
    PhantomData<ProtoType>,
);
#[derive(Default, Clone)]
pub struct RepeatedVariantField<RustType, ProtoType>(Vec<RustType>, PhantomData<ProtoType>);

#[derive(Default, Clone)]
pub struct SingularStringField(String);
#[derive(Default, Clone)]
pub struct OptionalStringField<const BITFIELD_INDEX: usize>(String);
#[derive(Default, Clone)]
pub struct SingularHeapMessageField<M>(Option<Box<M>>);

impl<RustType: Clone, ProtoType: tags::VariantType + tags::NumericalType<RustType = RustType>>
    FieldType for SingularVariantField<RustType, ProtoType>
{
    type GetterType<'a> = RustType where Self: 'a;
    fn get_field<B: BitSlice>(&self, _bitvec: &B) -> Self::GetterType<'_> {
        self.0.clone()
    }
    fn deser_from_iter<I: Iterator<Item = IoResult<u8>>, B: BitSlice>(
        &mut self,
        _bitvec: &mut B,
        field_data: FieldData<I>,
    ) -> Result<()> {
        if let FieldData::Variant(var) = &field_data {
            self.0 = var.get::<ProtoType>()?;
        } else {
            Err(ErrorKind::InvalidWireType(field_data.wire_type() as i32))?
        }
        Ok(())
    }
}

impl<RustType: Clone + Default, ProtoType, const BITFIELD_INDEX: usize> FieldType
    for OptionalVariantField<RustType, ProtoType, BITFIELD_INDEX>
{
    type GetterType<'a> = RustType where Self: 'a;
    fn get_field<B: BitSlice>(&self, bitvec: &B) -> Self::GetterType<'_> {
        if bitvec.get::<BITFIELD_INDEX>() {
            self.0.clone()
        } else {
            Default::default() // TODO: proto specified default value
        }
    }
}

impl<RustType: Clone, ProtoType: tags::VariantType + tags::NumericalType<RustType = RustType>>
    FieldType for RepeatedVariantField<RustType, ProtoType>
{
    type GetterType<'a> = &'a [RustType]
    where
        Self: 'a;
    fn get_field<B: BitSlice>(&self, _bitvec: &B) -> Self::GetterType<'_> {
        self.0.as_slice()
    }
    fn deser_from_iter<I: Iterator<Item = IoResult<u8>>, B: BitSlice>(
        &mut self,
        bitvec: &mut B,
        mut field_data: FieldData<I>,
    ) -> Result<()> {
        match field_data {
            FieldData::Variant(var) => self.0.push(var.get::<ProtoType>()?),
            FieldData::LengthDelimited(iter) => {
                let mut piter = iter.peekable();
                
            },
            _ => todo!(),
        }
        Ok(())
    }
}

impl FieldType for SingularStringField {
    type GetterType<'a> = &'a str where Self: 'a;
    fn get_field<B: BitSlice>(&self, _bitvec: &B) -> Self::GetterType<'_> {
        self.0.as_ref()
    }
    fn deser_from_iter<I: Iterator<Item = IoResult<u8>>, B: BitSlice>(
        &mut self,
        _bitvec: &mut B,
        mut field_data: FieldData<I>,
    ) -> Result<()> {
        if let FieldData::LengthDelimited(iter) = &mut field_data {
            let vec = iter.collect::<IoResult<Vec<u8>>>()?;
            self.0 = String::from_utf8(vec)?;
        } else {
            Err(ErrorKind::InvalidWireType(field_data.wire_type() as i32))?
        }
        Ok(())
    }
}

impl<const BITFIELD_INDEX: usize> FieldType for OptionalStringField<BITFIELD_INDEX> {
    type GetterType<'a> = &'a str where Self: 'a;
    fn get_field<B: BitSlice>(&self, bitvec: &B) -> Self::GetterType<'_> {
        if bitvec.get::<BITFIELD_INDEX>() {
            self.0.as_ref()
        } else {
            Default::default() // TODO: proto specified default value
        }
    }
}

impl<M> FieldType for SingularHeapMessageField<M> {
    type GetterType<'a> = Option<&'a M> where Self: 'a;
    fn get_field<B: BitSlice>(&self, _bitvec: &B) -> Self::GetterType<'_> {
        self.0.as_deref()
    }
}
