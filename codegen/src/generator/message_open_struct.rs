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

use crate::cases::{convert_into_case, Case};
use crate::descriptor::{
    DescriptorWithContext, FieldDescriptorWithContext, FieldLabel, FieldType as ProtoFieldType,
};
use crate::generator::r#enum::Enum;
use crate::proto_path::ProtoPath;
use crate::Result;
use ::proc_macro2::TokenStream;
use ::quote::{format_ident, quote, ToTokens, TokenStreamExt};
use ::std::any::Any;
use ::std::cell::OnceCell;
use ::std::collections::HashMap;
use ::std::sync::RwLock;
use ::syn::{parse2, parse_str, Ident, Item, Type};

#[derive(Default)]
struct Cache(RwLock<HashMap<*const (), OnceCell<Box<dyn Any>>>>);
impl Cache {
    fn get<T, R: Any>(&self, key: &T, f: impl FnOnce() -> Result<R>) -> Result<&R> {
        let ref_cell = self
            .0
            .write()
            .map_err(|_| "RwLock write failed".to_string())?
            .entry(::std::ptr::from_ref(key) as *const ())
            .or_default();
        Ok(ref_cell
            .get_or_try_init(|| -> Result<_> { Ok(Box::new(f()?) as Box<dyn Any>) })?
            .downcast_ref::<R>()
            .ok_or_else(|| "downcast failed".to_string())?)
    }
}

pub struct MessageOpenStruct<'a> {
    name: Ident,
    fields: Vec<Field<'a>>,
}

struct Field<'a> {
    name: Ident,
    r#type: Type,
    proto_type: ProtoFieldType<'a>,
    field_wrapper: FieldWrapper,
}

enum FieldWrapper {
    Bare,
    Optional,
    OptionalBoxed,
    Vec,
}

impl<'a> MessageOpenStruct<'a> {
    pub fn try_new(desc: &'a DescriptorWithContext<'a>) -> Result<Self> {
        Ok(Self {
            name: Self::rust_name_from_message_name(desc.name()?)?,
            fields: desc
                .non_oneof_fields()?
                .into_iter()
                .map(Field::try_new)
                .collect::<Result<Vec<_>>>()?,
        })
    }

    pub fn rust_name_from_message_name(name: &str) -> Result<Ident> {
        Ok(format_ident!(
            "{}Struct",
            convert_into_case(name, Case::CamelCase)
        ))
    }

    pub fn rust_path_from_message_path(
        path: impl AsRef<ProtoPath>,
        allocator: &Type,
    ) -> Result<Type> {
        let modules = path
            .as_ref()
            .parent()
            .into_iter()
            .flat_map(|p| p.components())
            .map(|name| Ok(parse_str(&convert_into_case(name, Case::LowerSnakeCase))?))
            .collect::<Result<Vec<Ident>>>()?;
        let struct_name = Self::rust_name_from_message_name(
            path.as_ref()
                .last_component()
                .ok_or_else(|| format!("Invalid message path: {:?}", path.as_ref()))?,
        )?;
        Ok(parse2(quote! {
            crate #(:: #modules)* :: #struct_name :: <#allocator>
        })?)
    }

    pub fn rust_items(&self) -> Result<Vec<Item>> {
        Ok(vec![
            self.rust_struct_item()?,
            self.rust_impl_message_lite()?,
        ])
    }

    fn rust_struct_item(&self) -> Result<Item> {
        let name = &self.name;
        let fields = &self.fields;
        Ok(parse2(quote! {
            pub struct #name<#[cfg(allocator)]A: ::std::alloc::Allocator = ::std::alloc::Global> {
                #(#fields)*
            }
        })?)
    }
    fn rust_impl_message_lite(&self) -> Result<Item> {
        let name = &self.name;
        let scalar_variant_fields = self
            .fields
            .iter()
            .filter(|f| f.r#type.to_token_stream().to_string().contains("Variant"));
        Ok(parse2(quote! {
            impl<#[cfg(allocator)]A: ::std::alloc::Allocator> ::puroro::MessageLite<A> for self::#name<A> {
                fn merge_from_bufread<R: ::std::io::BufRead>(
                    &mut self, _bufread: &mut R,
                ) -> ::puroro::Result<Self> {
                    use ::puroro::Result;
                    use ::puroro::internal::deser::{DeserMessageHandlerBase, DeserMessageHandlerForRead}
                    use ::puroro::variant::Variant;
                    impl DeserMessageHandlerBase for Self {
                        fn parse_variant(&mut self, num: i32, var: Variant) -> Result<()>;
                        fn parse_i32(&mut self, num: i32, val: [u8; 4]) -> Result<()>;
                        fn parse_i64(&mut self, num: i32, val: [u8; 8]) -> Result<()>;
                        fn is_message_field(&self, num: i32) -> bool;
                        fn start_message(&mut self, num: i32) -> Result<()>;
                        fn end_message(&mut self) -> Result<()>;
                    }
                    impl<R: ::std::io::Read> DeserMessageHandlerForRead<R> for Self {
                        fn parse_len(&mut self, num: i32, read: &mut R) -> Result<usize>;
                    }
                    todo!()
                }
                fn write<W: ::std::io::Write>(&self, _write: &mut W) -> Result<usize> {
                    unimplemented!()
                }
            }
        })?)
    }
}

impl<'a> Field<'a> {
    pub fn try_new(desc: &'a FieldDescriptorWithContext<'a>) -> Result<Self> {
        Ok(Self {
            name: parse_str(&convert_into_case(desc.name()?, Case::LowerSnakeCase))?,
            r#type: Self::gen_type(desc.r#type()?, desc.label()?, desc.is_proto3_optional()?)?,
            proto_type: desc.r#type()?,
            field_wrapper: match (desc.label()?, desc.r#type()?, desc.is_proto3_optional()?) {
                (Some(FieldLabel::Repeated), _, _) => FieldWrapper::Vec,
                (_ /* Not repeated */, ProtoFieldType::Message(_), _) => {
                    FieldWrapper::OptionalBoxed
                }
                (None, _ /* Not message */, false) => FieldWrapper::Bare,
                _ => FieldWrapper::Optional,
            },
        })
    }

    fn gen_type(
        ty: ProtoFieldType,
        label: Option<FieldLabel>,
        is_proto3_optional: bool,
    ) -> Result<Type> {
        match (label, is_proto3_optional) {
            (Some(FieldLabel::Repeated), _) => Self::gen_repeated_type(ty),
            (None, false) => Self::gen_scalar_type(ty),
            _ => Self::gen_optional_type(ty),
        }
    }

    fn gen_scalar_type(ty: ProtoFieldType) -> Result<Type> {
        Ok(parse2(match ty {
            ProtoFieldType::Bool => quote! { bool },
            ProtoFieldType::Bytes => quote! { ::std::vec::Vec<u8, A> },
            ProtoFieldType::Double => quote! { f64 },
            ProtoFieldType::Enum(e) => {
                let enum_path = Enum::rust_path_from_enum_path(e.full_path()?)?;
                quote! { #enum_path }
            }
            ProtoFieldType::Fixed32 => quote! { u32 },
            ProtoFieldType::Fixed64 => quote! { u64 },
            ProtoFieldType::Float => quote! { f32 },
            ProtoFieldType::Group => todo!(),
            ProtoFieldType::Int32 => quote! { i32 },
            ProtoFieldType::Int64 => quote! { i64 },
            ProtoFieldType::Message(m) => {
                let struct_path = MessageOpenStruct::rust_path_from_message_path(
                    m.full_path()?,
                    &parse_str("A")?,
                )?;
                quote! {
                    ::std::boxed::Box::<#struct_path, A>
                }
            }
            ProtoFieldType::SFixed32 => quote! { i32 },
            ProtoFieldType::SFixed64 => quote! { i64 },
            ProtoFieldType::SInt32 => quote! { i32 },
            ProtoFieldType::SInt64 => quote! { i64 },
            ProtoFieldType::String => quote! { ::puroro::string::String<A> },
            ProtoFieldType::UInt32 => quote! { u32 },
            ProtoFieldType::UInt64 => quote! { u64 },
        })?)
    }

    fn gen_optional_type(ty: ProtoFieldType) -> Result<Type> {
        let scalar = Self::gen_scalar_type(ty)?;
        Ok(parse2(quote! {
            ::std::option::Option::<#scalar>
        })?)
    }

    fn gen_repeated_type(ty: ProtoFieldType) -> Result<Type> {
        let scalar_type = match ty {
            ProtoFieldType::Message(m) => {
                MessageOpenStruct::rust_path_from_message_path(m.full_path()?, &parse_str("A")?)?
            }
            _ => Self::gen_scalar_type(ty)?,
        };
        Ok(parse2(quote! { ::std::vec::Vec::<#scalar_type, A> })?)
    }
}

impl ToTokens for Field<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let name = &self.name;
        let ty = &self.r#type;
        tokens.append_all(quote! {
            pub #name: #ty,
        })
    }
}
