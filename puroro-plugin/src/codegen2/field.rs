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

use super::*;
use crate::codegen::utils::StrExt;
use crate::Result;
use ::proc_macro2::TokenStream;
use ::puroro_protobuf_compiled::google::protobuf::{DescriptorProto, FieldDescriptorProto};
use ::quote::{format_ident, quote};
use ::std::ops::Deref;

pub struct ContextForField<'a> {
    pub(super) parent_context: &'a ContextForMessage<'a>,
    pub(super) parent_message_proto: &'a DescriptorProto,
}
impl ContextForField<'_> {
    pub fn parent_message_proto(&self) -> &DescriptorProto {
        self.parent_message_proto
    }
}
impl<'a> Deref for ContextForField<'a> {
    type Target = ContextForMessage<'a>;
    fn deref(&self) -> &Self::Target {
        self.parent_context
    }
}

pub trait FieldTrait: Sized {
    fn try_new(proto: &FieldDescriptorProto) -> Result<Self>;
}

#[derive(Debug)]
pub struct FieldImpl {
    name: String,
}

pub type Field = FieldImpl;

impl FieldTrait for FieldImpl {
    fn try_new(proto: &FieldDescriptorProto) -> Result<Self> {
        Ok(FieldImpl {
            name: proto.name().to_string(),
        })
    }
}

impl FieldImpl {
    pub fn gen_struct_field_decl(&self) -> Result<TokenStream> {
        let name = format_ident!("{}", self.name.to_lower_snake_case().escape_rust_keywords());
        Ok(quote! {
            #name: (),
        })
    }
}

#[derive(Debug, Clone, Copy)]
pub enum FieldRule {
    Optional,
    Singular,
    Repeated,
}

impl FieldRule {
    pub fn try_from_field_descriptor(fd: &FieldDescriptorProto) -> Result<Self> {
        // requires syntax!
        todo!()
    }
}
