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
use crate::descriptor::{DescriptorExt, FieldDescriptorExt, FieldLabel, FieldType, LenType};
use crate::generator::{to_ident, CodeGeneratorOptions};
use crate::proto_path::{ProtoPath, ProtoPathBuf};
use crate::Result;
use ::itertools::Itertools;
use ::quote::{format_ident, quote};
use ::std::rc::Rc;
use ::syn::{parse2, parse_str, Expr, Ident, Item, Path, Type};
use ::syn::{Lifetime, Signature};

pub struct GenTrait {
    rust_name: Ident,
    rust_mut_name: Ident,
    rust_app_name: Ident,
    fields: Vec<Field>,
    options: Rc<CodeGeneratorOptions>,
}

impl GenTrait {
    pub fn try_new<'a>(
        desc: &'a DescriptorExt<'a>,
        options: Rc<CodeGeneratorOptions>,
    ) -> Result<Self> {
        let current_path = Rc::new(desc.current_path().to_owned());
        Ok(Self {
            rust_name: Self::rust_name_from_message_name(desc.name())?,
            rust_mut_name: Self::rust_mut_name_from_message_name(desc.name())?,
            rust_app_name: Self::rust_app_name_from_message_name(desc.name())?,
            fields: desc
                .non_oneof_fields()?
                .into_iter()
                .map(|f| Field::try_new(f, Rc::clone(&current_path), Rc::clone(&options)))
                .collect::<Result<Vec<_>>>()?,
            options,
        })
    }

    pub fn rust_name_from_message_name(name: &str) -> Result<Ident> {
        Ok(format_ident!(
            "{}Trait",
            convert_into_case(name, Case::CamelCase)
        ))
    }

    pub fn rust_app_name_from_message_name(name: &str) -> Result<Ident> {
        Ok(format_ident!(
            "{}AppTrait",
            convert_into_case(name, Case::CamelCase)
        ))
    }

    pub fn rust_mut_name_from_message_name(name: &str) -> Result<Ident> {
        Ok(format_ident!(
            "{}MutTrait",
            convert_into_case(name, Case::CamelCase)
        ))
    }

    pub fn rust_path_from_proto_path(self, path: &ProtoPath) -> Result<Path> {
        path.to_rust_path_with(&self.options, |s| {
            let ident = Self::rust_name_from_message_name(s)?;
            Ok(parse2(quote! { #ident })?)
        })
    }

    pub fn gen_items(&self) -> Result<Vec<Item>> {
        let trait_def = self.gen_message_trait()?;
        let trait_mut_def = self.gen_message_mut_trait()?;
        let mut blanket_impls = Vec::new();
        blanket_impls.append(&mut self.gen_blanket_ref_impls()?);
        blanket_impls.push(self.gen_blanket_option_impl()?);
        Ok([trait_def, trait_mut_def]
            .into_iter()
            .chain(blanket_impls)
            .collect())
    }

    fn gen_message_trait(&self) -> Result<Item> {
        let trait_name = &self.rust_name;
        let getters = self
            .fields
            .iter()
            .map(Field::gen_get_method_signature)
            .collect::<Result<Vec<_>>>()?;
        Ok(parse2(quote! {
            pub trait #trait_name {
                #(#getters;)*
            }
        })?)
    }

    fn gen_message_mut_trait(&self) -> Result<Item> {
        let trait_name = &self.rust_mut_name;
        let base_trait_name = &self.rust_app_name;
        let base_trait_path = self
            .options
            .path_in_self_module(&base_trait_name.clone().into())?;
        let allocator_ident: Ident = parse_str("A")?;
        let allocator: Type = parse2(quote! { #allocator_ident})?;
        let methods = self
            .fields
            .iter()
            .map(|f| f.gen_mutable_methods_signatures(&allocator))
            .flatten_ok()
            .collect::<Result<Vec<_>>>()?;
        Ok(parse2(quote! {
            pub trait #trait_name < #allocator_ident: ::std::alloc::Allocator >
                : #base_trait_path < #allocator_ident >
            {
                #(#methods;)*
            }
        })?)
    }

    fn gen_blanket_ref_impls(&self) -> Result<Vec<Item>> {
        let trait_name = &self.rust_name;
        let trait_path: Path = self
            .options
            .path_in_self_module(&trait_name.clone().into())?;
        let blanket_type: Ident = parse_str("T")?;
        let getter_signatures = self
            .fields
            .iter()
            .map(Field::gen_get_method_signature)
            .collect::<Result<Vec<_>>>()?;
        let getter_bodies = self
            .fields
            .iter()
            .map(|f| f.gen_blanket_ref_get_method_body(&blanket_type, &trait_path))
            .collect::<Result<Vec<_>>>()?;
        Ok(vec![
            parse2(quote! {
                impl<T: #trait_path> #trait_path for &T {
                    #(#getter_signatures {
                        #getter_bodies
                    })*
                }
            })?,
            parse2(quote! {
                impl<T: self::#trait_name> #trait_path for &mut T {
                    #(#getter_signatures {
                        #getter_bodies
                    })*
                }
            })?,
        ])
    }

    fn gen_blanket_option_impl(&self) -> Result<Item> {
        let trait_name = &self.rust_name;
        let trait_path = self
            .options
            .path_in_self_module(&trait_name.clone().into())?;
        let blanket_type_ident: Ident = parse_str("T")?;
        let blanket_type = parse2(quote! { #blanket_type_ident })?;
        let blanket_opt_type = self.options.option_type(&blanket_type)?;
        let getter_signatures = self
            .fields
            .iter()
            .map(Field::gen_get_method_signature)
            .collect::<Result<Vec<_>>>()?;
        let getter_bodies = self
            .fields
            .iter()
            .map(|f| f.gen_blanket_option_get_method_body(&blanket_type_ident, &trait_path))
            .collect::<Result<Vec<_>>>()?;
        Ok(parse2(quote! {
            impl<T: #trait_path> #trait_path for #blanket_opt_type {
                #(#getter_signatures {
                    #getter_bodies
                })*
            }
        })?)
    }
}

pub struct Field {
    original_name: String,
    presense: FieldPresense,
    current_path: Rc<ProtoPathBuf>,
    scalar_type: FieldType<ProtoPathBuf, ProtoPathBuf>,
    options: Rc<CodeGeneratorOptions>,
}

impl Field {
    pub fn try_new<'a>(
        desc: &'a FieldDescriptorExt<'a>,
        current_path: Rc<ProtoPathBuf>,
        options: Rc<CodeGeneratorOptions>,
    ) -> Result<Self> {
        Ok(Self {
            original_name: desc.name().to_string(),
            presense: FieldPresense::from_field_desc(desc),
            current_path,
            scalar_type: desc.type_with_full_path()?,
            options,
        })
    }

    pub fn scalar_type(&self) -> FieldType<&ProtoPath, &ProtoPath> {
        self.scalar_type.as_deref()
    }

    pub fn wrapper(&self) -> FieldPresense {
        self.presense
    }

    // Getters

    fn gen_get_method_name(&self) -> Result<Ident> {
        let lower_cased = convert_into_case(&self.original_name, Case::LowerSnakeCase);
        Ok(to_ident(&lower_cased))
    }

    pub fn gen_get_method_signature(&self) -> Result<Signature> {
        let getter_name = self.gen_get_method_name()?;
        let scalar_ref_type =
            self.scalar_type
                .gen_scalar_maybe_ref_type(&self.current_path, None, &self.options)?;
        let getter_type = match self.presense {
            FieldPresense::Repeated => parse2(quote! {
                impl ::puroro::repeated::RepeatedView<Item = #scalar_ref_type>
            })?,
            FieldPresense::Explicit => self.options.option_type(&scalar_ref_type)?,
            FieldPresense::Implicit => scalar_ref_type,
        };
        Ok(parse2(quote! {
            fn #getter_name(&self) -> #getter_type
        })?)
    }

    fn gen_blanket_ref_get_method_body(
        &self,
        blanket_type: &Ident,
        trait_path: &Path,
    ) -> Result<Expr> {
        let getter_name = self.gen_get_method_name()?;
        Ok(parse2(quote! {
            <#blanket_type as #trait_path>::#getter_name(self)
        })?)
    }

    fn gen_blanket_option_get_method_body(
        &self,
        blanket_type_ident: &Ident,
        trait_path: &Path,
    ) -> Result<Expr> {
        let getter_name = self.gen_get_method_name()?;
        Ok(parse2(match self.presense {
            FieldPresense::Repeated => quote! {
                self.as_ref().map(<#blanket_type_ident as #trait_path>::#getter_name).into_iter().flatten()
            },
            FieldPresense::Explicit => quote! {
                self.as_ref().and_then(<#blanket_type_ident as #trait_path>::#getter_name)
            },
            FieldPresense::Implicit => quote! {
                self.as_ref().map(<#blanket_type_ident as #trait_path>::#getter_name).unwrap_or_default()
            },
        })?)
    }

    // Mutators

    pub fn gen_mutable_methods_signatures(&self, allocator: &Type) -> Result<Vec<Signature>> {
        let result = vec![
            self.gen_mut_method_signature(allocator)?,
            self.gen_clear_method_signature()?,
        ];
        Ok(result)
    }

    fn gen_mut_method_name(&self) -> Result<Ident> {
        let lower_cased = convert_into_case(&self.original_name, Case::LowerSnakeCase);
        Ok(to_ident(&format!("{}_mut", &lower_cased)))
    }

    pub fn gen_mut_method_signature(&self, allocator: &Type) -> Result<Signature> {
        let mutator_name = self.gen_mut_method_name()?;
        let mutator_type: Type = match self.presense {
            FieldPresense::Repeated => {
                // A type returned from the iterator. e.g. i32, &str, &impl MessageTrait
                let item_type = self.scalar_type.gen_scalar_maybe_ref_type(
                    &self.current_path,
                    None,
                    &self.options,
                )?;
                // A type used by setter. e.g. i32, String, impl MessageTrait
                let value_type = self.scalar_type.gen_scalar_owned_type(
                    &self.current_path,
                    allocator,
                    &self.options,
                )?;
                parse2(quote! {
                    impl ::puroro::repeated::RepeatedViewMut<Item = #item_type, Value = #value_type>
                })?
            }
            _ => {
                let bare_type = self.scalar_type.gen_scalar_owned_type(
                    &self.current_path,
                    allocator,
                    &self.options,
                )?;
                let deref_mut_trait = self.options.deref_mut_trait(&bare_type)?;
                parse2(quote! {
                    impl #deref_mut_trait
                })?
            }
        };
        Ok(parse2(quote! {
            fn #mutator_name(&mut self) -> #mutator_type
        })?)
    }

    fn gen_clear_method_name(&self) -> Result<Ident> {
        let lower_cased = convert_into_case(&self.original_name, Case::LowerSnakeCase);
        Ok(to_ident(&format!("clear_{}", &lower_cased)))
    }

    fn gen_clear_method_signature(&self) -> Result<Signature> {
        let clear_method_name = self.gen_clear_method_name()?;
        Ok(parse2(quote! {
            fn #clear_method_name(&mut self)
        })?)
    }

    // Others
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FieldPresense {
    Implicit,
    Explicit,
    Repeated,
}

impl FieldPresense {
    fn from_field_desc<'a>(field: &'a FieldDescriptorExt<'a>) -> Self {
        if field.has_presence() {
            FieldPresense::Explicit
        } else if field.label() == Some(FieldLabel::Repeated) {
            FieldPresense::Repeated
        } else {
            FieldPresense::Implicit
        }
    }
}

impl<M: AsRef<ProtoPath>, E: AsRef<ProtoPath>> FieldType<M, E> {
    pub fn gen_scalar_maybe_ref_type(
        &self,
        current_path: &ProtoPath,
        lifetime: Option<&Lifetime>,
        options: &CodeGeneratorOptions,
    ) -> Result<Type> {
        let lifetime = lifetime.iter();
        match self
            .as_ref()
            .maybe_into_primitive_type(current_path, options)?
        {
            Ok(primitive_type) => Ok(primitive_type),
            Err(len_type) => match len_type {
                LenType::Message(path) => {
                    let path = path
                        .as_ref()
                        .to_relative_path(current_path)
                        .unwrap_or(path.as_ref());
                    let path = path.to_rust_path_with(options, |name| {
                        let ident = GenTrait::rust_name_from_message_name(name)?;
                        Ok(parse2(quote! { #ident })?)
                    })?;
                    Ok(parse2(quote! { impl #(#lifetime +)* #path })?)
                }
                LenType::String => {
                    let str_type = options.primitive_type("str")?;
                    Ok(parse2(quote! { & #(#lifetime)* #str_type })?)
                }
                LenType::Bytes => {
                    let u8_type = options.primitive_type("u8")?;
                    Ok(parse2(quote! { & #(#lifetime)* [#u8_type] })?)
                }
            },
        }
    }

    pub fn gen_scalar_owned_type(
        &self,
        current_path: &ProtoPath,
        allocator: &Type,
        options: &CodeGeneratorOptions,
    ) -> Result<Type> {
        match self
            .as_ref()
            .maybe_into_primitive_type(current_path, options)?
        {
            Ok(primitive_type) => Ok(primitive_type),
            Err(len_type) => match len_type {
                LenType::Message(path) => {
                    let path = path
                        .as_ref()
                        .to_relative_path(current_path)
                        .unwrap_or(path.as_ref());
                    let path = path.to_rust_path_with(options, |name| {
                        let ident = GenTrait::rust_mut_name_from_message_name(name)?;
                        Ok(parse2(quote! { #ident })?)
                    })?;
                    Ok(parse2(quote! { impl #path<#allocator> })?)
                }
                LenType::String => Ok(parse2(quote! { ::puroro::string::String<#allocator> })?),
                LenType::Bytes => {
                    let u8_type = options.primitive_type("u8")?;
                    Ok(options.vec_type(&u8_type, Some(allocator))?)
                }
            },
        }
    }

    pub fn gen_scalar_nonzero_type(
        &self,
        current_path: &ProtoPath,
        allocator: &Type,
        options: &CodeGeneratorOptions,
    ) -> Result<Type> {
        let scalar_owned_type = self.gen_scalar_owned_type(current_path, allocator, options)?;
        if matches!(self, FieldType::Message(_)) {
            Ok(scalar_owned_type)
        } else {
            Ok(parse2(quote! { ::puroro::NonEmpty<#scalar_owned_type> })?)
        }
    }
}
