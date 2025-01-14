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

pub mod payload;

use self::payload::{DynamicLenPayload, WireTypeAndPayload};
use crate::internal::deser::{
    deser_from_bufread, DeserMessageHandlerBase, DeserMessageHandlerForRead,
};
use crate::internal::utils::{OnceList1, PairWithOnceList1Ext};
use crate::message::{Message, MessageMut};
use crate::variant::variant_types::Int32;
use crate::variant::{
    variant_types::UInt32, ReadExtVariant, Variant, VariantIntegerType, WriteExtVariant,
};
use crate::{ErrorKind, Result};
use ::cached_pair::{EitherOrBoth, Pair};
use ::derive_more::{Debug, Deref, DerefMut, TryUnwrap};
use ::hashbrown::hash_map::Entry;
use ::hashbrown::DefaultHashBuilder;
use ::hashbrown::HashMap;
use ::itertools::Either;
use ::std::alloc::{Allocator, Global};
use ::std::io::{BufRead, Read, Write};
use ::std::vec::Vec;

/// A Message implementation which is expected to be used in the situation where
/// the protocol buffer schema is not known at compile time.
///
/// This implementation's interface is designed to be wrapped by a higher-level
/// interface which knows about the schema, so it misses some of the common methods:
/// - No "Unknown field"s. By definition, unknown fields requires the schema.
/// - TBD
#[derive(Default, Clone)]
pub struct DynamicMessage<A: Allocator = Global> {
    fields: HashMap<i32, DynamicField<A>, DefaultHashBuilder, A>,
}

#[derive(Clone, Debug, Deref, DerefMut)]
pub struct DynamicField<A: Allocator = Global> {
    payloads: Pair<Vec<WireTypeAndPayload<A>, A>, OnceList1<FieldCustomView<A>, A>>,
}

#[derive(Clone, Debug, TryUnwrap)]
#[try_unwrap(ref, ref_mut)]
pub enum FieldCustomView<A: Allocator = Global> {
    ScalarMessage(Option<DynamicMessage<A>>),
}

#[derive(Clone, Copy, Debug)]
pub enum FieldReducingErrorStrategy {
    Abort,
    Skip,
    AsDefault,
}

impl DynamicMessage<Global> {
    pub fn new() -> Self {
        Self {
            fields: HashMap::new(),
        }
    }
}

impl<A: Allocator> DynamicMessage<A> {
    pub fn new_in(alloc: A) -> Self {
        Self {
            fields: HashMap::new_in(alloc),
        }
    }

    pub fn field(&self, number: i32) -> Option<&DynamicField<A>> {
        self.fields.get(&number)
    }

    pub fn allocator(&self) -> &A {
        self.fields.allocator()
    }
}

impl<A: Allocator + Clone> DynamicMessage<A> {
    pub fn field_mut(&mut self, number: i32) -> &mut DynamicField<A> {
        let alloc = self.allocator().clone();
        self.fields
            .entry(number)
            .or_insert_with(|| DynamicField::default_in(alloc))
    }

    pub fn merge(&mut self, other: DynamicMessage<A>) {
        for (number, other_field) in other.fields {
            match self.fields.entry(number) {
                Entry::Occupied(mut entry) => {
                    let payloads = entry.get_mut().as_payloads_mut();
                    payloads.extend(other_field.into_payloads().into_iter());
                }
                Entry::Vacant(entry) => {
                    entry.insert(other_field);
                }
            }
        }
    }

    fn write_to_vec<A2: Allocator>(&self, buf: &mut Vec<u8, A2>) -> usize {
        // Writing to a Vec<u8> is always successful.
        unsafe { self.write(buf).unwrap_unchecked() }
    }
}

impl<A: Allocator> Debug for DynamicMessage<A> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        let mut ds = f.debug_struct("DynamicMessage");
        for (number, field) in &self.fields {
            ds.field(&format!("field{}", number), field);
        }
        ds.finish()
    }
}

impl<A: Allocator + Clone> Message for DynamicMessage<A> {
    fn write<W: Write>(&self, mut write: W) -> Result<usize> {
        let mut total_bytes = 0;
        for (number, field) in &self.fields {
            for wire_and_payload in field.as_payloads() {
                let tag = (TryInto::<u32>::try_into(*number)? << 3)
                    | Into::<u32>::into(wire_and_payload.wire_type());
                total_bytes += write.write_variant(UInt32::into_variant(tag))?;
                total_bytes += match wire_and_payload {
                    WireTypeAndPayload::Variant(variant) => write.write_variant(variant.clone())?,
                    WireTypeAndPayload::I64(buf) => {
                        write.write_all(buf)?;
                        4usize
                    }
                    WireTypeAndPayload::I32(buf) => {
                        write.write_all(buf)?;
                        8usize
                    }
                    WireTypeAndPayload::Len(len_payload) => {
                        let bytes = len_payload.as_buf();
                        let len = bytes.len();
                        write.write_variant(Variant::from::<Int32>(len.try_into()?))?;
                        write.write_all(bytes)?;
                        len
                    }
                };
            }
        }
        Ok(total_bytes)
    }
}

impl<A: Allocator + Clone> MessageMut<A> for DynamicMessage<A> {
    fn merge_from_bufread<R: BufRead>(&mut self, read: R) -> Result<()> {
        deser_from_bufread(read, self)
    }
}

impl<A: Allocator + Clone> DeserMessageHandlerBase for DynamicMessage<A> {
    fn parse_variant(&mut self, num: i32, var: Variant) -> Result<()> {
        self.field_mut(num).push_variant(var);
        Ok(())
    }
    fn parse_i32(&mut self, num: i32, val: [u8; 4]) -> Result<()> {
        self.field_mut(num).push_i32(val);
        Ok(())
    }
    fn parse_i64(&mut self, num: i32, val: [u8; 8]) -> Result<()> {
        self.field_mut(num).push_i64(val);
        Ok(())
    }
    fn is_message_field(&self, _num: i32) -> bool {
        false
    }
    fn start_message(&mut self, _num: i32) -> Result<()> {
        // Every message fields are deserialized as a bytes initially,
        // and then might be deserialized on demand.
        unreachable!()
    }
    fn end_message(&mut self) -> Result<()> {
        unreachable!()
    }
}

impl<A: Allocator + Clone, R: Read> DeserMessageHandlerForRead<R> for DynamicMessage<A> {
    fn parse_len(&mut self, num: i32, read: &mut R) -> Result<usize> {
        let alloc = self.allocator().clone();
        // Facepalm
        let (buf, len) = {
            let mut std_buf = ::std::vec::Vec::new();
            let len = read.read_to_end(&mut std_buf)?;
            let mut buf = Vec::with_capacity_in(len, A::clone(&alloc));
            buf.extend_from_slice(&std_buf);
            (buf, len)
        };
        self.field_mut(num)
            .as_payloads_mut()
            .push(WireTypeAndPayload::Len(DynamicLenPayload::from_buf(buf)));
        Ok(len)
    }
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
        let field_custom_view = self.payloads.try_get_or_insert_into_right(
            |v| v.try_unwrap_scalar_message_ref().is_ok(),
            || FieldCustomView::try_scalar_message_from_payloads(self.as_payloads().into_iter()),
            self.allocator(),
        )?;
        Ok(field_custom_view
            .try_unwrap_scalar_message_ref()
            .unwrap()
            .as_ref())
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

    pub fn push_variant(&mut self, val: Variant) {
        self.as_payloads_mut()
            .push(WireTypeAndPayload::Variant(val));
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

    fn default_in(alloc: A) -> Self {
        Self {
            payloads: Pair::from_left(Vec::new_in(alloc)),
        }
    }
}

impl<A: Allocator + Clone> DynamicField<A> {
    fn as_payloads(&self) -> &Vec<WireTypeAndPayload<A>, A> {
        self.left_with(|f_list| f_list.first().to_field(self.allocator()))
    }

    fn as_payloads_mut(&mut self) -> &mut Vec<WireTypeAndPayload<A>, A> {
        let alloc = A::clone(self.allocator());
        self.left_mut_with(|f_list| f_list.first().to_field(&alloc))
    }

    fn into_payloads(self) -> Vec<WireTypeAndPayload<A>, A> {
        let alloc = A::clone(self.allocator());
        self.payloads
            .into_left_with(|f_list| f_list.first().to_field(&alloc))
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
    fn to_field(&self, alloc: &A) -> Vec<WireTypeAndPayload<A>, A> {
        let encoded_bytes = match self {
            FieldCustomView::ScalarMessage(Some(msg)) => {
                let mut buf = Vec::new_in(A::clone(alloc));
                msg.write_to_vec(&mut buf);
                buf
            }
            FieldCustomView::ScalarMessage(None) => Vec::new_in(A::clone(alloc)),
        };
        let mut payload_vec = Vec::with_capacity_in(1, A::clone(alloc));
        payload_vec.push(WireTypeAndPayload::Len(encoded_bytes.into()));
        payload_vec
    }

    fn try_scalar_message_from_payloads<'a>(
        mut iter: impl Iterator<Item = &'a WireTypeAndPayload<A>>,
    ) -> Result<Self>
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
        Ok(FieldCustomView::ScalarMessage(msg))
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
