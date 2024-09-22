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

use super::gen_message_trait::{Field as TraitField, FieldWrapper, GenTrait};
use crate::descriptor::{
    DescriptorExt, FieldDescriptorExt, I32Type, I64Type, LenType, VariantType, WireType,
};
use crate::generator::CodeGeneratorOptions;
use crate::proto_path::{ProtoPath, ProtoPathBuf};
use crate::Result;
use ::quote::quote;
use ::std::rc::Rc;
use ::syn::{parse2, parse_str, Ident, Item};
use ::syn::{Expr, Type};

pub struct GenDynamicMessageImpls {
    rust_trait_name: Ident,
    fields: Vec<Field>,
    options: Rc<CodeGeneratorOptions>,
}

impl GenDynamicMessageImpls {
    pub fn try_new<'a>(
        desc: &'a DescriptorExt<'a>,
        options: Rc<CodeGeneratorOptions>,
    ) -> Result<Self> {
        let current_path = Rc::new(desc.current_path().to_owned());
        Ok(Self {
            rust_trait_name: GenTrait::rust_name_from_message_name(desc.name())?,
            fields: desc
                .non_oneof_fields()?
                .into_iter()
                .map(|f| Field::try_new(f, Rc::clone(&current_path), Rc::clone(&options)))
                .collect::<Result<Vec<_>>>()?,
            options,
        })
    }

    pub fn gen_impl_message_trait(&self) -> Result<Item> {
        let trait_name = &self.rust_trait_name;
        let getters = self
            .fields
            .iter()
            .map(Field::gen_getter)
            .collect::<Result<Vec<_>>>()?;
        Ok(parse2(quote! {
            impl<A: ::std::alloc::Allocator + ::std::clone::Clone> self::#trait_name
            for ::puroro::generic_message::DynamicMessage<A> {
                #(#getters)*
            }
        })?)
    }
}

pub struct Field {
    number: i32,
    trait_field: TraitField,
    current_path: Rc<ProtoPathBuf>,
    options: Rc<CodeGeneratorOptions>,
}

impl Field {
    fn try_new<'a>(
        desc: &'a FieldDescriptorExt<'a>,
        current_path: Rc<ProtoPathBuf>,
        options: Rc<CodeGeneratorOptions>,
    ) -> Result<Self> {
        Ok(Self {
            number: desc.number(),
            trait_field: TraitField::try_new(desc, Rc::clone(&current_path), Rc::clone(&options))?,
            current_path,
            options,
        })
    }

    fn gen_getter(&self) -> Result<Item> {
        let signature = self.trait_field.gen_getter_signature()?;
        let number = self.number;
        let body = self.gen_getter_body(&parse_str("f_opt")?)?;
        Ok(parse2(quote! {
            #signature {
                let f_opt = self.field(#number);
                #body
            }
        })?)
    }

    fn gen_getter_body(&self, field_opt_expr: &Expr) -> Result<Expr> {
        let wire_type: WireType<_, _, _, _> = self.trait_field.scalar_type().into();
        let field_expr: Expr = parse_str("f")?;
        Ok(match self.trait_field.wrapper() {
            FieldWrapper::Vec => {
                let body = match wire_type {
                    WireType::Variant(t) => {
                        self.gen_repeated_variant_getter_body(&field_expr, t)?
                    }
                    WireType::I32(t) => self.gen_repeated_i32_getter_body(&field_expr, t)?,
                    WireType::I64(t) => self.gen_repeated_i64_getter_body(&field_expr, t)?,
                    WireType::Len(t) => self.gen_repeated_len_getter_body(&field_expr, t)?,
                    _ => todo!(), // Start / end group
                };
                parse2(quote! {
                    (#field_opt_expr).into_iter().flat_map(|f| #body)
                })?
            }
            FieldWrapper::Bare | FieldWrapper::Optional | FieldWrapper::OptionalBoxed => {
                let body = match wire_type {
                    WireType::Variant(t) => {
                        self.gen_non_repeated_varint_getter_body(&field_expr, t)?
                    }
                    WireType::I32(t) => self.gen_non_repeated_i32_getter_body(&field_expr, t)?,
                    WireType::I64(t) => self.gen_non_repeated_i64_getter_body(&field_expr, t)?,
                    WireType::Len(t) => self.gen_non_repeated_len_getter_body(&field_expr, t)?,
                    _ => todo!(), // Start / end group
                };
                let maybe_unwrap = match self.trait_field.wrapper() {
                    FieldWrapper::Bare => quote! { .unwrap_or_default() },
                    _ => quote! {},
                };
                parse2(quote! {
                    (#field_opt_expr).map(|f| #body) #maybe_unwrap
                })?
            }
        })
    }

    fn gen_non_repeated_varint_getter_body(
        &self,
        field_expr: &Expr,
        t: VariantType<&ProtoPath>,
    ) -> Result<Expr> {
        let vt_type: Type = parse2(match t {
            VariantType::Int32 => quote! { ::puroro::variant::variant_types::Int32 },
            VariantType::Int64 => quote! { ::puroro::variant::variant_types::Int64 },
            VariantType::UInt32 => quote! { ::puroro::variant::variant_types::UInt32 },
            VariantType::UInt64 => quote! { ::puroro::variant::variant_types::UInt64 },
            VariantType::SInt32 => quote! { ::puroro::variant::variant_types::SInt32 },
            VariantType::SInt64 => quote! { ::puroro::variant::variant_types::SInt64 },
            VariantType::Bool => quote! { ::puroro::variant::variant_types::Bool },
            VariantType::Enum(path) => {
                let path = path.to_relative_path(&self.current_path).unwrap_or(path);
                let enum_path = path.to_rust_path(&self.options)?;
                quote! { ::puroro::variant::variant_types::Enum::<#enum_path> }
            }
        })?;
        Ok(parse2(quote! {
            (#field_expr).as_scalar_variant::<#vt_type>(true /* TODO: packed check */)
        })?)
    }
    fn gen_non_repeated_i32_getter_body(&self, field_expr: &Expr, t: I32Type) -> Result<Expr> {
        let bytes_expr: Expr = parse2(quote! { (#field_expr).as_scalar_i32() })?;
        let primitive_type: Type = match t {
            I32Type::Float => self.options.primitive_type("f32")?,
            I32Type::Fixed32 => self.options.primitive_type("u32")?,
            I32Type::SFixed32 => self.options.primitive_type("i32")?,
        };
        Ok(parse2(
            quote! { #primitive_type::from_le_bytes(#bytes_expr) },
        )?)
    }
    fn gen_non_repeated_i64_getter_body(&self, field_expr: &Expr, t: I64Type) -> Result<Expr> {
        let bytes_expr: Expr = parse2(quote! { (#field_expr).as_scalar_i64() })?;
        let primitive_type: Type = match t {
            I64Type::Double => self.options.primitive_type("f64")?,
            I64Type::Fixed64 => self.options.primitive_type("u64")?,
            I64Type::SFixed64 => self.options.primitive_type("i64")?,
        };
        Ok(parse2(
            quote! { #primitive_type::from_le_bytes(#bytes_expr) },
        )?)
    }
    fn gen_non_repeated_len_getter_body(
        &self,
        field_expr: &Expr,
        t: LenType<&ProtoPath>,
    ) -> Result<Expr> {
        Ok(parse2(match t {
            LenType::String => {
                quote! { (#field_expr).as_scalar_string() }
            }
            LenType::Bytes => {
                quote! { (#field_expr).as_scalar_bytes() }
            }
            LenType::Message(_) => {
                quote! { (#field_expr).as_scalar_message() }
            }
        })?)
    }

    fn gen_repeated_variant_getter_body(
        &self,
        field_expr: &Expr,
        t: VariantType<&ProtoPath>,
    ) -> Result<Expr> {
        let vt_type: Type = parse2(match t {
            VariantType::Int32 => quote! { ::puroro::variant::variant_types::Int32 },
            VariantType::Int64 => quote! { ::puroro::variant::variant_types::Int64 },
            VariantType::UInt32 => quote! { ::puroro::variant::variant_types::UInt32 },
            VariantType::UInt64 => quote! { ::puroro::variant::variant_types::UInt64 },
            VariantType::SInt32 => quote! { ::puroro::variant::variant_types::SInt32 },
            VariantType::SInt64 => quote! { ::puroro::variant::variant_types::SInt64 },
            VariantType::Bool => quote! { ::puroro::variant::variant_types::Bool },
            VariantType::Enum(path) => {
                let path = path.to_relative_path(&self.current_path).unwrap_or(path);
                let enum_path = path.to_rust_path(&self.options)?;
                quote! { ::puroro::variant::variant_types::Enum::<#enum_path> }
            }
        })?;
        Ok(parse2(quote! {
            (#field_expr).as_repeated_variant::<#vt_type>(true /* TODO: packed check */)
        })?)
    }
    fn gen_repeated_i32_getter_body(&self, field_expr: &Expr, t: I32Type) -> Result<Expr> {
        let primitive_type: Type = match t {
            I32Type::Float => self.options.primitive_type("f32")?,
            I32Type::Fixed32 => self.options.primitive_type("u32")?,
            I32Type::SFixed32 => self.options.primitive_type("i32")?,
        };
        Ok(parse2(quote! {
            (#field_expr).as_repeated_i32().map(#primitive_type::from_le_bytes)
        })?)
    }
    fn gen_repeated_i64_getter_body(&self, field_expr: &Expr, t: I64Type) -> Result<Expr> {
        let primitive_type: Type = match t {
            I64Type::Double => self.options.primitive_type("f64")?,
            I64Type::Fixed64 => self.options.primitive_type("u64")?,
            I64Type::SFixed64 => self.options.primitive_type("i64")?,
        };
        Ok(parse2(quote! {
            (#field_expr).as_repeated_i64().map(#primitive_type::from_le_bytes)
        })?)
    }
    fn gen_repeated_len_getter_body(
        &self,
        field_expr: &Expr,
        t: LenType<&ProtoPath>,
    ) -> Result<Expr> {
        Ok(parse2(match t {
            LenType::String => quote! { (#field_expr).as_repeated_string() },
            LenType::Bytes => quote! { (#field_expr).as_repeated_bytes() },
            LenType::Message(_) => {
                quote! { (#field_expr).as_repeated_message() }
            }
        })?)
    }
}
