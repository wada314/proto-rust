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

use crate::internal::variant::Variant;
use crate::{tags, Result};
use ::std::io::Result as IoResult;
use ::std::marker::PhantomData;
use ::std::ops::{Index, IndexMut};

pub trait FieldType {
    type GetterType<'a>
    where
        Self: 'a;
    fn get_field<B: Index<usize, Output = bool>>(&self, bitvec: &B) -> Self::GetterType<'_>;
    #[allow(unused)]
    fn deser_from_iter<I: Iterator<Item = IoResult<u8>>, B: IndexMut<usize, Output = bool>>(
        &mut self,
        bitvec: &mut B,
        iter: &mut I,
    ) -> Result<()> {
        todo!()
    }
}

pub struct SingularVariantField<RustType, ProtoType>(RustType, PhantomData<ProtoType>);
pub struct OptionalVariantField<RustType, ProtoType, const BITFIELD_INDEX: usize>(
    RustType,
    PhantomData<ProtoType>,
);

pub struct SingularStringField(String);
pub struct OptionalStringField<const BITFIELD_INDEX: usize>(String);
pub struct SingularHeapMessageField<M>(Option<Box<M>>);

impl<RustType: Clone, ProtoType: tags::VariantType + tags::NumericalType<RustType = RustType>>
    FieldType for SingularVariantField<RustType, ProtoType>
{
    type GetterType<'a> = RustType where Self: 'a;
    fn get_field<B: Index<usize, Output = bool>>(&self, _bitvec: &B) -> Self::GetterType<'_> {
        self.0.clone()
    }
    fn deser_from_iter<I: Iterator<Item = IoResult<u8>>, B: IndexMut<usize, Output = bool>>(
        &mut self,
        _bitvec: &mut B,
        iter: &mut I,
    ) -> Result<()> {
        let var = Variant::decode_bytes(iter.by_ref())?;
        self.0 = var.get::<ProtoType>()?;
        Ok(())
    }
}

impl<RustType: Clone + Default, ProtoType, const BITFIELD_INDEX: usize> FieldType
    for OptionalVariantField<RustType, ProtoType, BITFIELD_INDEX>
{
    type GetterType<'a> = RustType where Self: 'a;
    fn get_field<B: Index<usize, Output = bool>>(&self, bitvec: &B) -> Self::GetterType<'_> {
        if bitvec[BITFIELD_INDEX] {
            self.0.clone()
        } else {
            Default::default() // TODO: proto specified default value
        }
    }
}

impl FieldType for SingularStringField {
    type GetterType<'a> = &'a str where Self: 'a;
    fn get_field<B: Index<usize, Output = bool>>(&self, _bitvec: &B) -> Self::GetterType<'_> {
        self.0.as_ref()
    }
}

impl<const BITFIELD_INDEX: usize> FieldType for OptionalStringField<BITFIELD_INDEX> {
    type GetterType<'a> = &'a str where Self: 'a;
    fn get_field<B: Index<usize, Output = bool>>(&self, bitvec: &B) -> Self::GetterType<'_> {
        if bitvec[BITFIELD_INDEX] {
            self.0.as_ref()
        } else {
            Default::default() // TODO: proto specified default value
        }
    }
}

impl<M> FieldType for SingularHeapMessageField<M> {
    type GetterType<'a> = Option<&'a M> where Self: 'a;
    fn get_field<B: Index<usize, Output = bool>>(&self, _bitvec: &B) -> Self::GetterType<'_> {
        self.0.as_deref()
    }
}
