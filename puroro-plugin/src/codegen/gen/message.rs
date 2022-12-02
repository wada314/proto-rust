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

use super::super::util::*;
use super::super::{FieldExt, Message, PackageOrMessageExt};
use super::{OneofExt, OneofFieldExt};
use crate::Result;
use ::itertools::Itertools;
use ::once_cell::unsync::OnceCell;
use ::proc_macro2::TokenStream;
use ::quote::{format_ident, quote};
use ::std::fmt::Debug;
use ::std::rc::Rc;

pub trait MessageExt: Debug {
    fn bitfield_size(&self) -> Result<usize>;
    fn gen_rust_struct_path(&self) -> Result<Rc<TokenStream>>;
    fn gen_struct(&self) -> Result<TokenStream>;
}

#[derive(Debug, Default)]
struct Cache {
    rust_struct_path: OnceCell<Rc<TokenStream>>,
    bitfield_size: OnceCell<usize>,
}
impl<T: ?Sized + Message> MessageExt for T {
    fn bitfield_size(&self) -> Result<usize> {
        <Self as Message>::cache(self)
            .get::<Cache>()?
            .bitfield_size
            .get_or_try_init(|| {
                let mut tail = 0;

                // bits for each field
                for field in self.fields()? {
                    if let Some(next_tail) = field.maybe_allocated_bitfield_tail()? {
                        tail = next_tail;
                    } else {
                        tail = field.assign_and_get_bitfield_tail(tail)?;
                    }
                }

                // bits for oneofs
                for oneof in self.oneofs()? {
                    if let Some(next_tail) = oneof.maybe_allocated_bitfield_tail()? {
                        tail = next_tail;
                    } else {
                        tail = oneof.assign_and_get_bitfield_tail(tail)?;
                    }
                }

                Ok(tail)
            })
            .cloned()
    }

    fn gen_rust_struct_path(&self) -> Result<Rc<TokenStream>> {
        <Self as Message>::cache(self)
            .get::<Cache>()?
            .rust_struct_path
            .get_or_try_init(|| {
                let parent = <Self as Message>::parent(self)?.gen_rust_module_path()?;
                let ident =
                    format_ident!("{}", self.name()?.to_camel_case().escape_rust_keywords());
                Ok(Rc::new(quote! { #parent :: #ident }))
            })
            .cloned()
    }

    fn gen_struct(&self) -> Result<TokenStream> {
        let ident = gen_struct_ident(self)?;
        let field_decls = self
            .fields()?
            .map(|f| f.gen_struct_field_decl())
            .collect::<Result<Vec<_>>>()?;
        let oneof_decls = self
            .oneofs()?
            .map(|o| o.gen_struct_field_decl())
            .collect::<Result<Vec<_>>>()?;
        let field_methods = self
            .fields()?
            .map(|f| f.gen_struct_field_methods())
            .collect::<Result<Vec<_>>>()?;
        let oneof_methods = self
            .oneofs()?
            .map(|o| o.gen_struct_field_methods())
            .collect::<Result<Vec<_>>>()?;
        let oneofs = self.oneofs()?.collect::<Vec<_>>();
        let oneof_fields_methods = oneofs
            .iter()
            .map(|o| o.fields())
            .flatten_ok()
            .map(|f| f?.gen_struct_field_methods())
            .collect::<Result<Vec<_>>>()?;
        let bitfield_size_in_u32_array = (self.bitfield_size()? + 31) / 32;
        let message_impl = gen_struct_message_impl(self)?;
        let clone_impl = gen_struct_clone_impl(self)?;
        let drop_impl = gen_struct_drop_impl(self)?;
        let debug_impl = gen_struct_debug_impl(self)?;
        let partial_eq_impl = gen_struct_partial_eq_impl(self)?;
        Ok(quote! {
            #[derive(::std::default::Default)]
            pub struct #ident {
                #(#field_decls)*
                #(#oneof_decls)*
                _bitfield: self::_puroro::bitvec::BitArray<#bitfield_size_in_u32_array>,
            }

            impl #ident {
                #(#field_methods)*
                #(#oneof_methods)*
                #(#oneof_fields_methods)*
            }

            #message_impl
            #clone_impl
            #drop_impl
            #debug_impl
            #partial_eq_impl
        })
    }
}

fn gen_struct_ident(this: &(impl ?Sized + Message)) -> Result<TokenStream> {
    let ident = format_ident!(
        "{}",
        this.name()?
            .to_camel_case()
            .escape_rust_keywords()
            .to_string()
    );
    Ok(quote! { #ident })
}

fn gen_struct_message_impl(this: &(impl ?Sized + Message)) -> Result<TokenStream> {
    let ident = gen_struct_ident(this)?;
    let field_data_ident = quote! { field_data };
    let out_ident = quote! { out };
    let field_deser_arms = this
        .fields()?
        .map(|f| f.gen_struct_field_deser_arm(&field_data_ident))
        .collect::<Result<Vec<_>>>()?;
    let oneof_deser_arms = this
        .oneofs()?
        .map(|o| o.gen_struct_field_deser_arms(&field_data_ident))
        .collect::<Result<Vec<_>>>()?;
    let ser_fields = this
        .fields()?
        .map(|f| f.gen_struct_field_ser(&out_ident))
        .collect::<Result<Vec<_>>>()?;
    let ser_oneofs = this
        .oneofs()?
        .map(|o| o.gen_struct_field_ser(&out_ident))
        .collect::<Result<Vec<_>>>()?;

    Ok(quote! {
        impl self::_puroro::Message for #ident {
            fn from_bytes_iter<I: ::std::iter::Iterator<Item=::std::io::Result<u8>>>(iter: I) -> self::_puroro::Result<Self> {
                let mut msg = <Self as ::std::default::Default>::default();
                msg.merge_from_bytes_iter(iter)?;
                ::std::result::Result::Ok(msg)
            }

            fn merge_from_bytes_iter<I: ::std::iter::Iterator<Item =::std::io::Result<u8>>>(&mut self, mut iter: I) -> self::_puroro::Result<()> {
                use self::_puroro::internal::ser::FieldData;
                #[allow(unused)] use self::_puroro::internal::oneof_type::OneofUnion as _;
                while let Some((number, #field_data_ident)) = FieldData::from_bytes_iter(iter.by_ref())? {
                    match number {
                        #(#field_deser_arms)*
                        #(#oneof_deser_arms)*
                        _ => todo!(), // Unknown field number
                    }
                }
                ::std::result::Result::Ok(())
            }

            fn to_bytes<W: ::std::io::Write>(&self, #[allow(unused)] #out_ident: &mut W) -> self::_puroro::Result<()> {
                #[allow(unused)] use self::_puroro::internal::oneof_type::OneofUnion as _;
                #(#ser_fields)*
                #(#ser_oneofs)*
                ::std::result::Result::Ok(())
            }
        }
    })
}

fn gen_struct_clone_impl(this: &(impl ?Sized + Message)) -> Result<TokenStream> {
    let ident = gen_struct_ident(this)?;
    let field_clones = this
        .fields()?
        .map(|f| f.gen_struct_field_clone_arm())
        .collect::<Result<Vec<_>>>()?;
    let oneof_clones = this
        .oneofs()?
        .map(|o| o.gen_struct_field_clone_arm())
        .collect::<Result<Vec<_>>>()?;
    Ok(quote! {
        impl ::std::clone::Clone for #ident {
            fn clone(&self) -> Self {
                Self {
                    #(#field_clones)*
                    #(#oneof_clones)*
                    _bitfield: ::std::clone::Clone::clone(&self._bitfield),
                }
            }
        }
    })
}

fn gen_struct_drop_impl(this: &(impl ?Sized + Message)) -> Result<TokenStream> {
    let ident = gen_struct_ident(this)?;
    let oneof_idents = this
        .oneofs()?
        .map(|o| o.gen_struct_field_ident())
        .collect::<Result<Vec<_>>>()?;
    // We need to explicitly clear the oneof unions.
    Ok(quote! {
        impl ::std::ops::Drop for #ident {
            fn drop(&mut self) {
                #[allow(unused)] use self::_puroro::internal::oneof_type::OneofUnion as _;

                #(self.#oneof_idents.clear(&mut self._bitfield);)*
            }
        }
    })
}

fn gen_struct_debug_impl(this: &(impl ?Sized + Message)) -> Result<TokenStream> {
    let ident = gen_struct_ident(this)?;
    let from_fields = this
        .fields()?
        .map(|f| f.gen_struct_field_debug())
        .collect::<Result<Vec<_>>>()?;
    let oneofs = this.oneofs()?.collect::<Vec<_>>();
    let from_oneofs = oneofs
        .iter()
        .map(|o| o.fields())
        .flatten_ok()
        .map(|f| f?.gen_struct_field_debug())
        .collect::<Result<Vec<_>>>()?;
    Ok(quote! {
        impl ::std::fmt::Debug for #ident {
            fn fmt(&self, fmt: &mut ::std::fmt::Formatter<'_>) -> ::std::result::Result<(), ::std::fmt::Error> {
                fmt.debug_struct(stringify!(#ident))
                    #(#from_fields)*
                    #(#from_oneofs)*
                    .finish()
            }
        }
    })
}

fn gen_struct_partial_eq_impl(this: &(impl ?Sized + Message)) -> Result<TokenStream> {
    let ident = gen_struct_ident(this)?;
    let rhs_ident = format_ident!("rhs");
    let rhs = quote! { #rhs_ident };
    let field_cmps = this
        .fields()?
        .map(|f| f.gen_struct_field_partial_eq_cmp(&rhs))
        .collect::<Result<Vec<_>>>()?;
    let oneof_cmps = this
        .oneofs()?
        .map(|o| o.gen_struct_field_partial_eq_cmp(&rhs))
        .collect::<Result<Vec<_>>>()?;
    Ok(quote! {
        impl ::std::cmp::PartialEq for #ident {
            fn eq(&self, rhs: &Self) -> bool {
                #[allow(unused)] use self::_puroro::internal::oneof_type::OneofUnion as _;

                true
                    #(#field_cmps)*
                    #(#oneof_cmps)*
            }
        }
    })
}