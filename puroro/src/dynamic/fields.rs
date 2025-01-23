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

use crate::dynamic::payload::{DynamicLenPayload, WireTypeAndPayload};
use crate::dynamic::DynamicMessage;
use crate::internal::utils::{OnceList1, PairWithOnceList1Ext2};
use crate::variant::{ReadExtVariant, Variant, VariantIntegerType, WriteExtVariant};
use crate::{ErrorKind, Result};
use ::cached_pair::{EitherOrBoth, Pair};
use ::derive_more::{Debug, Deref, DerefMut, TryUnwrap};
use ::itertools::Either;
use ::std::alloc::{Allocator, Global};
use ::std::str;
use ::std::vec::Vec;

#[derive(Clone, Debug, Deref, DerefMut)]
pub struct DynamicField<A: Allocator = Global> {
    payloads: Pair<Vec<WireTypeAndPayload<A>, A>, OnceList1<FieldCustomView<A>, A>>,
}

#[derive(Clone, Debug, TryUnwrap, ::derive_more::TryInto, ::derive_more::From)]
#[try_unwrap(ref, ref_mut)]
#[try_into(owned, ref)]
pub enum FieldCustomView<A: Allocator = Global> {
    ScalarMessage(#[debug("{:?}", _0.0)] (Option<DynamicMessage<A>>, A)),
}

#[derive(Clone, Copy, Debug)]
pub enum FieldReducingErrorStrategy {
    Abort,
    Skip,
    AsDefault,
}

impl<A: Allocator + Clone> DynamicField<A> {
    pub fn as_scalar_variant<T: VariantIntegerType>(
        &self,
        allow_packed: bool,
        error_strategy: FieldReducingErrorStrategy,
    ) -> Result<Option<T::RustType>> {
        reduce_iter(self.as_repeated_variant::<T>(allow_packed)?, error_strategy)
    }

    pub fn as_repeated_variant<T: VariantIntegerType>(
        &self,
        allow_packed: bool,
    ) -> Result<impl '_ + Iterator<Item = Result<T::RustType>>> {
        Ok(self
            .as_payloads()
            .iter()
            .flat_map(move |record| match (allow_packed, record) {
                (_, WireTypeAndPayload::Variant(variant)) => {
                    Either::Left(Some(Ok(variant.clone())).into_iter())
                }
                (true, WireTypeAndPayload::Len(dyn_len_payload)) => {
                    Either::Right(dyn_len_payload.as_buf().into_variant_iter())
                }
                _ => Either::Left(Some(Err(ErrorKind::DynamicMessageFieldTypeError)).into_iter()),
            })
            .map(|rv| rv.and_then(T::try_from_variant)))
    }

    pub fn as_scalar_i32(
        &self,
        error_strategy: FieldReducingErrorStrategy,
    ) -> Result<Option<[u8; 4]>> {
        reduce_iter(self.as_repeated_i32()?, error_strategy)
    }

    pub fn as_repeated_i32(&self) -> Result<impl '_ + Iterator<Item = Result<[u8; 4]>>> {
        Ok(self.as_payloads().iter().map(|record| match record {
            WireTypeAndPayload::I32(buf) => Ok(*buf),
            _ => Err(ErrorKind::DynamicMessageFieldTypeError),
        }))
    }

    pub fn as_scalar_i64(
        &self,
        error_strategy: FieldReducingErrorStrategy,
    ) -> Result<Option<[u8; 8]>> {
        reduce_iter(self.as_repeated_i64()?, error_strategy)
    }

    pub fn as_repeated_i64(&self) -> Result<impl '_ + Iterator<Item = Result<[u8; 8]>>> {
        Ok(self.as_payloads().iter().map(|record| match record {
            WireTypeAndPayload::I64(buf) => Ok(*buf),
            _ => Err(ErrorKind::DynamicMessageFieldTypeError),
        }))
    }

    pub fn as_scalar_string(
        &self,
        error_strategy: FieldReducingErrorStrategy,
    ) -> Result<Option<&str>> {
        reduce_iter(self.as_repeated_string()?, error_strategy)
    }

    pub fn as_repeated_string(&self) -> Result<impl '_ + Iterator<Item = Result<&str>>> {
        Ok(self.as_payloads().iter().map(|record| match record {
            WireTypeAndPayload::Len(bytes_or_msg) => {
                Ok(::std::str::from_utf8(bytes_or_msg.as_buf())?)
            }
            _ => Err(ErrorKind::DynamicMessageFieldTypeError),
        }))
    }

    pub fn as_scalar_bytes(
        &self,
        error_strategy: FieldReducingErrorStrategy,
    ) -> Result<Option<&[u8]>> {
        reduce_iter(self.as_repeated_bytes()?, error_strategy)
    }

    pub fn as_repeated_bytes(&self) -> Result<impl '_ + Iterator<Item = Result<&[u8]>>> {
        Ok(self.as_payloads().iter().map(|record| match record {
            WireTypeAndPayload::Len(bytes_or_msg) => Ok(bytes_or_msg.as_buf().as_slice()),
            _ => Err(ErrorKind::DynamicMessageFieldTypeError),
        }))
    }

    pub fn as_scalar_message(&self) -> Result<Option<&DynamicMessage<A>>> {
        let &(ref scalar_message_ref, _) = self.payloads.try_get_or_insert_into_right2(
            |payloads| {
                Ok((
                    FieldCustomView::try_scalar_message_from_payloads(payloads.into_iter())?,
                    payloads.allocator().clone(),
                ))
            },
            self.allocator().clone(),
        )?;
        Ok(scalar_message_ref.as_ref())
    }

    pub fn as_repeated_message(&self) -> Result<impl Iterator<Item = Result<&DynamicMessage<A>>>> {
        Ok(self.as_payloads().iter().map(|wire_and_payload| {
            let WireTypeAndPayload::Len(dyn_len_payload) = wire_and_payload else {
                Err(ErrorKind::DynamicMessageFieldTypeError)?
            };
            Ok(dyn_len_payload.as_message()?)
        }))
    }

    pub fn clear(&mut self) {
        self.as_payloads_mut().clear();
    }

    pub fn push_variant(&mut self, val: Variant, allow_packed: bool) {
        let payloads = self.as_payloads_mut();
        if allow_packed {
            if let Some(WireTypeAndPayload::Len(dyn_len_payload)) = payloads.last_mut() {
                if let Ok(packed_variants) = dyn_len_payload.as_packed_variants() {
                    todo!(); // packed_variants.push(val);
                    return;
                }
            }
        }

        payloads.push(WireTypeAndPayload::Variant(val));
    }

    pub fn push_variant_from<T: VariantIntegerType>(&mut self, val: T::RustType) {
        self.as_payloads_mut()
            .push(WireTypeAndPayload::Variant(Variant::from::<T>(val)));
    }

    pub fn push_i32(&mut self, val: [u8; 4]) {
        self.as_payloads_mut().push(WireTypeAndPayload::I32(val));
    }

    pub fn push_i64(&mut self, val: [u8; 8]) {
        self.as_payloads_mut().push(WireTypeAndPayload::I64(val));
    }

    pub fn push_string(&mut self, val: &str) {
        let alloc = self.allocator().clone();
        let mut buf = Vec::with_capacity_in(val.len(), alloc);
        buf.extend_from_slice(val.as_bytes());
        self.as_payloads_mut()
            .push(WireTypeAndPayload::Len(DynamicLenPayload::from_buf(buf)));
    }

    pub fn push_bytes(&mut self, val: &[u8]) {
        let alloc = self.allocator().clone();
        let mut buf = Vec::with_capacity_in(val.len(), alloc);
        buf.extend_from_slice(val);
        self.as_payloads_mut()
            .push(WireTypeAndPayload::Len(DynamicLenPayload::from_buf(buf)));
    }

    pub fn push_message(&mut self, val: DynamicMessage<A>) {
        let alloc = self.allocator().clone();
        self.as_payloads_mut()
            .push(WireTypeAndPayload::Len(DynamicLenPayload::from_message(
                val, &alloc,
            )));
    }

    pub(crate) fn default_in(alloc: A) -> Self {
        Self {
            payloads: Pair::from_left(Vec::new_in(alloc)),
        }
    }

    pub(crate) fn as_payloads(&self) -> &Vec<WireTypeAndPayload<A>, A> {
        self.left_with(|f_list| f_list.first().to_field())
    }

    pub(crate) fn as_payloads_mut(&mut self) -> &mut Vec<WireTypeAndPayload<A>, A> {
        self.left_mut_with(|f_list| f_list.first().to_field())
    }

    pub(crate) fn into_payloads(self) -> Vec<WireTypeAndPayload<A>, A> {
        self.payloads
            .into_left_with(|f_list| f_list.first().to_field())
    }

    pub fn extend_variants<T, I>(&mut self, iter: I, allow_packed: bool)
    where
        T: VariantIntegerType,
        I: IntoIterator<Item = T::RustType>,
    {
        if allow_packed {
            let alloc = self.allocator().clone();
            let mut buf = Vec::new_in(alloc);
            for val in iter {
                buf.write_variant(Variant::from::<T>(val)).unwrap();
            }
            if !buf.is_empty() {
                self.as_payloads_mut()
                    .push(WireTypeAndPayload::Len(DynamicLenPayload::from_buf(buf)));
            }
        } else {
            self.extend(iter.into_iter().map(|v| Variant::from::<T>(v)));
        }
    }
}

impl<A: Allocator> DynamicField<A> {
    fn allocator(&self) -> &A {
        let as_ref = self.payloads.as_ref();
        match as_ref {
            EitherOrBoth::Left(vec) | EitherOrBoth::Both(vec, _) => vec.allocator(),
            EitherOrBoth::Right(list) => list.allocator(),
        }
    }
}

impl<A: Allocator + Clone> FieldCustomView<A> {
    fn to_field(&self) -> Vec<WireTypeAndPayload<A>, A> {
        let encoded_bytes = match self {
            FieldCustomView::ScalarMessage((Some(msg), alloc)) => {
                let mut buf = Vec::new_in(alloc.clone());
                msg.write_to_vec(&mut buf);
                buf
            }
            FieldCustomView::ScalarMessage((None, alloc)) => Vec::new_in(alloc.clone()),
        };
        let mut payload_vec = Vec::with_capacity_in(1, encoded_bytes.allocator().clone());
        payload_vec.push(WireTypeAndPayload::Len(encoded_bytes.into()));
        payload_vec
    }

    fn try_scalar_message_from_payloads<'a>(
        mut iter: impl Iterator<Item = &'a WireTypeAndPayload<A>>,
    ) -> Result<Option<DynamicMessage<A>>>
    where
        A: 'a,
    {
        let mut msg = None;
        while let Some(payload) = iter.next() {
            let WireTypeAndPayload::Len(dyn_payload) = payload else {
                return Err(ErrorKind::DynamicMessageFieldTypeError);
            };
            let msg_mut =
                msg.get_or_insert_with(|| DynamicMessage::new_in(dyn_payload.allocator().clone()));
            msg_mut.merge(dyn_payload.as_message()?.clone());
        }
        Ok(msg)
    }
}

impl<A: Allocator + Clone> TryFrom<&FieldCustomView<A>> for Vec<WireTypeAndPayload<A>, A> {
    type Error = ErrorKind;
    fn try_from(value: &FieldCustomView<A>) -> Result<Self> {
        Ok(value.to_field())
    }
}

fn reduce_iter<T: Default>(
    iter: impl Iterator<Item = Result<T>>,
    strategy: FieldReducingErrorStrategy,
) -> Result<Option<T>> {
    let mut last = None;
    for item in iter {
        match item {
            Ok(value) => {
                last = Some(value);
            }
            Err(e) => match strategy {
                FieldReducingErrorStrategy::Abort => return Err(e),
                FieldReducingErrorStrategy::Skip => continue,
                FieldReducingErrorStrategy::AsDefault => {
                    last = Some(T::default());
                }
            },
        }
    }
    Ok(last)
}

impl<A: Allocator + Clone> Extend<Variant> for DynamicField<A> {
    fn extend<T: IntoIterator<Item = Variant>>(&mut self, iter: T) {
        self.as_payloads_mut()
            .extend(iter.into_iter().map(WireTypeAndPayload::Variant));
    }
}

impl<A: Allocator + Clone> Extend<[u8; 4]> for DynamicField<A> {
    fn extend<T: IntoIterator<Item = [u8; 4]>>(&mut self, iter: T) {
        self.as_payloads_mut()
            .extend(iter.into_iter().map(WireTypeAndPayload::I32));
    }
}

impl<A: Allocator + Clone> Extend<[u8; 8]> for DynamicField<A> {
    fn extend<T: IntoIterator<Item = [u8; 8]>>(&mut self, iter: T) {
        self.as_payloads_mut()
            .extend(iter.into_iter().map(WireTypeAndPayload::I64));
    }
}

impl<A: Allocator + Clone> Extend<String> for DynamicField<A> {
    fn extend<T: IntoIterator<Item = String>>(&mut self, iter: T) {
        let alloc = self.allocator().clone();
        self.as_payloads_mut().extend(iter.into_iter().map(|val| {
            let mut buf = Vec::with_capacity_in(val.len(), alloc.clone());
            buf.extend_from_slice(val.as_bytes());
            WireTypeAndPayload::Len(DynamicLenPayload::from_buf(buf))
        }));
    }
}

impl<A: Allocator + Clone> Extend<Vec<u8, A>> for DynamicField<A> {
    fn extend<T: IntoIterator<Item = Vec<u8, A>>>(&mut self, iter: T) {
        self.as_payloads_mut().extend(
            iter.into_iter()
                .map(|val| WireTypeAndPayload::Len(DynamicLenPayload::from_buf(val))),
        );
    }
}

impl<A: Allocator + Clone> Extend<DynamicMessage<A>> for DynamicField<A> {
    fn extend<T: IntoIterator<Item = DynamicMessage<A>>>(&mut self, iter: T) {
        let alloc = self.allocator().clone();
        self.as_payloads_mut().extend(
            iter.into_iter()
                .map(|val| WireTypeAndPayload::Len(DynamicLenPayload::from_message(val, &alloc))),
        );
    }
}
