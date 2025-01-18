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

use crate::internal::utils::{OnceList1, PairWithOnceList1Ext};
use crate::internal::WireType;
use crate::message::MessageMut;
use crate::variant::{ReadExtVariant, Variant, WriteExtVariant};
use crate::{ErrorKind, Result};
use ::cached_pair::{EitherOrBoth, Pair};
use ::derive_more::{Debug, Deref, DerefMut, TryUnwrap};
use ::std::alloc::{Allocator, Global};

use super::DynamicMessage;

#[derive(Clone, Debug, Deref, DerefMut)]
pub struct DynamicLenPayload<A: Allocator = Global> {
    payload: Pair<Vec<u8, A>, OnceList1<LenCustomPayloadView<A>, A>>,
}

#[derive(Clone, Debug)]
pub enum WireTypeAndPayload<A: Allocator = Global> {
    Variant(Variant),
    I64([u8; 8]),
    I32([u8; 4]),
    Len(DynamicLenPayload<A>),
}

impl<A: Allocator> WireTypeAndPayload<A> {
    pub(crate) fn wire_type(&self) -> WireType {
        match self {
            WireTypeAndPayload::Variant(_) => WireType::Variant,
            WireTypeAndPayload::I64(_) => WireType::I64,
            WireTypeAndPayload::I32(_) => WireType::I32,
            WireTypeAndPayload::Len(_) => WireType::Len,
        }
    }
}

#[derive(Clone, Debug, TryUnwrap)]
#[try_unwrap(ref, ref_mut)]
pub enum LenCustomPayloadView<A: Allocator = Global> {
    Message(DynamicMessage<A>),
    PackedVariants(Vec<Variant, A>),
}

impl<A: Allocator + Clone> LenCustomPayloadView<A> {
    pub(crate) fn to_buf(&self, alloc: &A) -> Vec<u8, A> {
        match self {
            LenCustomPayloadView::Message(msg) => {
                let mut buf = Vec::new_in(A::clone(alloc));
                msg.write_to_vec(&mut buf);
                buf
            }
            LenCustomPayloadView::PackedVariants(variants) => {
                let mut buf = Vec::new_in(A::clone(alloc));
                for v in variants {
                    buf.write_variant(v.clone()).unwrap();
                }
                buf
            }
        }
    }
}

impl<A: Allocator + Clone> DynamicLenPayload<A> {
    pub(crate) fn from_buf(buf: Vec<u8, A>) -> Self {
        Self {
            payload: Pair::from_left(buf),
        }
    }

    pub(crate) fn from_message(msg: DynamicMessage<A>, alloc: &A) -> Self {
        Self {
            payload: Pair::from_right(OnceList1::new_in(
                LenCustomPayloadView::Message(msg),
                alloc.clone(),
            )),
        }
    }

    pub(crate) fn from_variant(variant: Variant, alloc: &A) -> Self {
        let mut vec = Vec::new_in(alloc.clone());
        vec.push(variant);
        Self {
            payload: Pair::from_right(OnceList1::new_in(
                LenCustomPayloadView::PackedVariants(vec),
                alloc.clone(),
            )),
        }
    }

    pub(crate) fn as_buf(&self) -> &Vec<u8, A> {
        let alloc = self.allocator();
        self.payload.left_with(|list| list.first().to_buf(alloc))
    }

    pub(crate) fn as_buf_mut(&mut self) -> &mut Vec<u8, A> {
        let alloc = self.allocator().clone();
        self.payload
            .left_mut_with(|list| list.first().to_buf(&alloc))
    }

    pub(crate) fn as_message(&self) -> Result<&DynamicMessage<A>> {
        Ok(self
            .try_get_or_insert_into_right(
                |lcpv| lcpv.try_unwrap_message_ref().is_ok(),
                |_| {
                    let mut message = DynamicMessage::new_in(self.allocator().clone());
                    message.merge_from_read(self.as_buf().as_slice())?;
                    Ok(LenCustomPayloadView::Message(message))
                },
                |lcpv| Ok(lcpv.to_buf(self.allocator())),
                self.allocator(),
            )?
            .try_unwrap_message_ref()
            .unwrap())
    }

    pub(crate) fn as_packed_variants(&self) -> Result<&Vec<Variant, A>> {
        Ok(self
            .try_get_or_insert_into_right(
                |lcpv| lcpv.try_unwrap_packed_variants_ref().is_ok(),
                |_| {
                    let mut vec = Vec::new_in(self.allocator().clone());
                    for v in self.as_buf().as_slice().into_variant_iter() {
                        vec.push(v?);
                    }
                    Ok(LenCustomPayloadView::PackedVariants(vec))
                },
                |lcpv| Ok(lcpv.to_buf(self.allocator())),
                self.allocator(),
            )?
            .try_unwrap_packed_variants_ref()
            .unwrap())
    }
}

impl<A: Allocator> DynamicLenPayload<A> {
    pub(crate) fn allocator(&self) -> &A {
        match self.payload.as_ref() {
            EitherOrBoth::Left(vec) | EitherOrBoth::Both(vec, _) => vec.allocator(),
            EitherOrBoth::Right(list) => list.allocator(),
        }
    }
}

impl<A: Allocator> From<Vec<u8, A>> for DynamicLenPayload<A> {
    fn from(value: Vec<u8, A>) -> Self {
        Self {
            payload: Pair::from_left(value),
        }
    }
}

impl<A: Allocator + Clone> TryFrom<LenCustomPayloadView<A>> for Vec<u8, A> {
    type Error = ErrorKind;

    fn try_from(value: LenCustomPayloadView<A>) -> Result<Self> {
        match value {
            LenCustomPayloadView::Message(msg) => {
                let mut buf = Vec::new_in(msg.allocator().clone());
                msg.write_to_vec(&mut buf);
                Ok(buf)
            }
            LenCustomPayloadView::PackedVariants(variants) => {
                let mut buf = Vec::new_in(variants.allocator().clone());
                for v in variants {
                    buf.write_variant(v)?;
                }
                Ok(buf)
            }
        }
    }
}
