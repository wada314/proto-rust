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

//! For the enum details, see the official documents:
//!  - [proto2 document](https://developers.google.com/protocol-buffers/docs/proto#enum)
//!  - [proto3 document](https://developers.google.com/protocol-buffers/docs/proto3#enum)
//!  - [c++ generated code](https://developers.google.com/protocol-buffers/docs/reference/cpp-generated#enum)

use super::super::util::*;
use super::super::{Enum, PackageOrMessageExt, Syntax};
use crate::syn;
use crate::{ErrorKind, Result};
use ::once_cell::unsync::OnceCell;
use ::proc_macro2::TokenStream;
use ::quote::{format_ident, quote};
use ::std::fmt::Debug;
use ::std::rc::Rc;

pub trait EnumExt {
    fn gen_enum(&self) -> Result<TokenStream>;
    fn gen_rust_enum_path(&self) -> Result<Rc<syn::Path>>;
    fn gen_rust_enum_type(&self) -> Result<Rc<syn::Type>>;
}

#[derive(Debug, Default)]
struct Cache {
    rust_enum_path: OnceCell<Rc<syn::Path>>,
    rust_enum_type: OnceCell<Rc<syn::Type>>,
}

impl<T: ?Sized + Enum> EnumExt for T {
    fn gen_enum(&self) -> Result<TokenStream> {
        let ident = format_ident!("{}", self.name().to_camel_case().escape_rust_keywords());
        let value_idents = self
            .values()?
            .map(|(name, _)| format_ident!("{}", name.to_camel_case().escape_rust_keywords()))
            .collect::<Vec<_>>();
        let syntax = self.syntax()?;
        let maybe_extra_value = match syntax {
            Syntax::Proto2 => quote! {},
            Syntax::Proto3 => quote! { _None(i32), },
        };
        let first_value_ident = value_idents.first().ok_or(ErrorKind::NoEnumValues)?;
        let into_i32 = gen_enum_into_i32(self)?;
        let from_i32 = match syntax {
            Syntax::Proto2 => gen_enum_try_from_i32(self)?,
            Syntax::Proto3 => gen_enum_from_i32(self)?,
        };

        Ok(quote! {
            #[derive(
                ::std::clone::Clone,
                ::std::marker::Copy,
                ::std::cmp::PartialEq,
                ::std::cmp::Eq,
                ::std::cmp::PartialOrd,
                ::std::cmp::Ord,
                ::std::hash::Hash,
                ::std::fmt::Debug,
            )]
            pub enum #ident {
                #(#value_idents,)*
                #maybe_extra_value
            }

            impl ::std::default::Default for #ident {
                fn default() -> Self {
                    Self::#first_value_ident
                }
            }

            #into_i32
            #from_i32
        })
    }

    fn gen_rust_enum_path(&self) -> Result<Rc<syn::Path>> {
        self.cache()
            .get::<Cache>()?
            .rust_enum_path
            .get_or_try_init(|| {
                let ident = format_ident!("{}", self.name().to_camel_case().escape_rust_keywords());
                let parent = self.parent()?.gen_rust_module_path()?;
                Ok(Rc::new(syn::parse2(quote! { #parent :: #ident })?))
            })
            .cloned()
    }

    fn gen_rust_enum_type(&self) -> Result<Rc<syn::Type>> {
        self.cache()
            .get::<Cache>()?
            .rust_enum_type
            .get_or_try_init(|| {
                let path = self.gen_rust_enum_path()?;
                Ok(Rc::new(syn::parse2(quote! { #path })?))
            })
            .cloned()
    }
}

fn gen_enum_into_i32(this: &(impl ?Sized + Enum)) -> Result<TokenStream> {
    let ident = format_ident!("{}", this.name().to_camel_case().escape_rust_keywords());
    let syntax = this.syntax()?;
    let value_idents = this
        .values()?
        .map(|(name, _)| format_ident!("{}", name.to_camel_case().escape_rust_keywords()))
        .collect::<Vec<_>>();
    let value_numbers = this.values()?.map(|(_, number)| number).collect::<Vec<_>>();
    let maybe_none_arm = match syntax {
        Syntax::Proto2 => quote! {},
        Syntax::Proto3 => quote! {
            self::#ident::_None(i) => i,
        },
    };

    Ok(quote! {
        impl ::std::convert::From::<#ident> for i32 {
            fn from(val: #ident) -> i32 {
                match val {
                    #(#ident::#value_idents => #value_numbers,)*
                    #maybe_none_arm
                }
            }
        }
    })
}

fn gen_enum_from_i32(this: &(impl ?Sized + Enum)) -> Result<TokenStream> {
    if matches!(this.syntax()?, Syntax::Proto2) {
        return Ok(quote! {});
    }
    let ident = format_ident!("{}", this.name().to_camel_case().escape_rust_keywords());
    let value_idents = this
        .values()?
        .map(|(name, _)| format_ident!("{}", name.to_camel_case().escape_rust_keywords()))
        .collect::<Vec<_>>();
    let value_numbers = this.values()?.map(|(_, number)| number).collect::<Vec<_>>();
    Ok(quote! {
        impl ::std::convert::From::<i32> for #ident {
            fn from(val: i32) -> Self {
                match val {
                    #(#value_numbers => self::#ident::#value_idents,)*
                    _ => #ident::_None(val),
                }
            }
        }
    })
}

fn gen_enum_try_from_i32(this: &(impl ?Sized + Enum)) -> Result<TokenStream> {
    if matches!(this.syntax()?, Syntax::Proto3) {
        return Ok(quote! {});
    }
    let ident = format_ident!("{}", this.name().to_camel_case().escape_rust_keywords());
    let value_idents = this
        .values()?
        .map(|(name, _)| format_ident!("{}", name.to_camel_case().escape_rust_keywords()))
        .collect::<Vec<_>>();
    let value_numbers = this.values()?.map(|(_, number)| number).collect::<Vec<_>>();
    Ok(quote! {
        impl ::std::convert::TryFrom::<i32> for #ident {
            type Error = self::_puroro::PuroroError;
            fn try_from(val: i32) -> ::std::result::Result<Self, Self::Error> {
                match val {
                    #(#value_numbers => ::std::result::Result::Ok(self::#ident::#value_idents),)*
                    _ => ::std::result::Result::Err(self::_puroro::ErrorKind::UnknownEnumVariant(val))?,
                }
            }
        }
    })
}