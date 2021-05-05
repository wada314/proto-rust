use std::borrow::Cow;

use itertools::Itertools;

use crate::context::{AllocatorType, Context, ImplType};
use crate::utils::{get_keyword_safe_ident, to_lower_snake_case};
use crate::wrappers::{
    FieldDescriptor, FieldLabel, FieldType, MessageDescriptor, NonTrivialFieldType,
};
use crate::{ErrorKind, Result};

pub struct MessageImplFragmentGenerator<'a, 'c> {
    context: &'a Context<'c>,
    msg: &'c MessageDescriptor<'c>,
}
impl<'a, 'c> MessageImplFragmentGenerator<'a, 'c> {
    pub fn new(context: &'a Context<'c>, msg: &'c MessageDescriptor<'c>) -> Self {
        Self { context, msg }
    }

    /// A raw generated struct identifier.
    /// e.g. "FieldDescriptorProto", "DescriptorProtoBumpalo"
    pub fn struct_ident(&self, msg: &'c MessageDescriptor<'c>) -> Result<Cow<'c, str>> {
        let postfix1 = match self.context.impl_type() {
            ImplType::Default => "",
            ImplType::SliceRef => "SliceRef",
        };
        let postfix2 = match self.context.alloc_type() {
            AllocatorType::Default => "",
            AllocatorType::Bumpalo => "Bumpalo",
        };
        Ok(format!(
            "{name}{postfix1}{postfix2}",
            name = msg.native_ident()?,
            postfix1 = postfix1,
            postfix2 = postfix2,
        )
        .into())
    }

    /// A struct ident with relative path from the given package.
    /// Note this is still not a typename; the generic params are not bound.
    pub fn struct_ident_with_relative_path(
        &self,
        msg: &'c MessageDescriptor<'c>,
    ) -> Result<String> {
        let struct_name = self.struct_ident(msg)?;
        let mut struct_package_iter = msg.package()?.split('.').peekable();
        let mut cur_package_iter = self.msg.package()?.split('.').peekable();
        while let (Some(p1), Some(p2)) = (struct_package_iter.peek(), cur_package_iter.peek()) {
            if *p1 == *p2 {
                struct_package_iter.next();
                cur_package_iter.next();
            } else {
                break;
            }
        }
        Ok(format!(
            "self::{supers}{mods}{name}",
            name = struct_name,
            supers = std::iter::repeat("super::")
                .take(cur_package_iter.count())
                .collect::<String>(),
            mods = struct_package_iter
                .map(|s| get_keyword_safe_ident(&to_lower_snake_case(s)) + "::")
                .collect::<String>(),
        ))
    }

    /// A type name of the struct with a relative path from the current msg.
    /// Includes generic param bounds if there is any.
    pub fn type_name_of_msg(&self, msg: &'c MessageDescriptor<'c>) -> Result<String> {
        let generic_args_iter = match self.context.alloc_type() {
            AllocatorType::Default => None,
            AllocatorType::Bumpalo => Some("'bump"),
        }
        .into_iter();
        if generic_args_iter.clone().count() == 0 {
            Ok(self.struct_ident_with_relative_path(msg)?)
        } else {
            let generic_args = Itertools::intersperse(generic_args_iter, ", ").collect::<String>();
            Ok(format!(
                "{name}<{gargs}>",
                name = self.struct_ident_with_relative_path(msg)?,
                gargs = generic_args,
            ))
        }
    }

    pub fn cfg_condition(&self) -> &'static str {
        match self.context.alloc_type() {
            AllocatorType::Bumpalo => "#[cfg(feature = \"puroro-bumpalo\")]",
            _ => "",
        }
    }

    pub fn is_default_available(&self) -> bool {
        match (self.context.impl_type(), self.context.alloc_type()) {
            (ImplType::SliceRef, _) | (_, AllocatorType::Bumpalo) => false,
            _ => true,
        }
    }

    pub fn field_visibility(&self) -> &'static str {
        match self.context.impl_type() {
            ImplType::Default => "pub ",
            ImplType::SliceRef => "",
        }
    }

    pub fn field_scalar_item_type_for(
        &self,
        field: &'c FieldDescriptor<'c>,
    ) -> Result<Cow<'c, str>> {
        Ok(match self.context.impl_type() {
            ImplType::Default => match field.type_()?.native_trivial_type_name() {
                Ok(name) => name.into(),
                Err(nontrivial_type) => match nontrivial_type {
                    NonTrivialFieldType::Group => Err(ErrorKind::GroupNotSupported)?,
                    NonTrivialFieldType::String => self.string_type().into(),
                    NonTrivialFieldType::Bytes => self.vec_type("u8").into(),
                    NonTrivialFieldType::Enum(e) => format!(
                        "::std::result::Result<{type_}, i32>",
                        type_ = e.native_ident_with_relative_path(field.package()?)?
                    )
                    .into(),
                    NonTrivialFieldType::Message(m) => self.type_name_of_msg(m)?.into(),
                },
            },
            ImplType::SliceRef => {
                unimplemented!()
            }
        })
    }

    pub fn field_type_for(&self, field: &'c FieldDescriptor<'c>) -> Result<Cow<'c, str>> {
        if let FieldType::Message(m) = field.type_()? {
            if m.is_map_entry() {
                // Special treatment for map field
                let (key_field, value_field) = m.key_value_of_map_entry()?;
                return Ok(format!(
                    "::std::collections::HashMap<{key}, {value}>",
                    key = self.field_type_for(key_field)?,
                    value = self.field_type_for(value_field)?,
                )
                .into());
            }
        }
        // Non-map normal fields
        let scalar_type = self.field_scalar_item_type_for(field)?;
        Ok(match self.context.impl_type() {
            ImplType::Default => match field.label()? {
                FieldLabel::Optional2 => {
                    if matches!(field.type_()?, FieldType::Message(_)) {
                        format!(
                            "::std::option::Option<{boxed_type}>",
                            boxed_type = self.box_type(scalar_type.as_ref()),
                        )
                        .into()
                    } else {
                        format!(
                            "::std::option::Option<{scalar_type}>",
                            scalar_type = scalar_type,
                        )
                        .into()
                    }
                }
                FieldLabel::Optional3 => {
                    if matches!(field.type_()?, FieldType::Message(_)) {
                        format!(
                            "::std::option::Option<{boxed_type}>",
                            boxed_type = self.box_type(scalar_type.as_ref()),
                        )
                        .into()
                    } else {
                        scalar_type.into()
                    }
                }
                FieldLabel::Required => scalar_type.into(),
                FieldLabel::Repeated => self.vec_type(scalar_type.as_ref()).into(),
            },
            ImplType::SliceRef => {
                unimplemented!()
            }
        })
    }

    pub fn type_tag_for(&self, field: &'c FieldDescriptor<'c>) -> Result<String> {
        Ok(match field.type_()? {
            FieldType::Double => "Double".into(),
            FieldType::Float => "Float".into(),
            FieldType::Int32 => "Int32".into(),
            FieldType::Int64 => "Int64".into(),
            FieldType::UInt32 => "UInt32".into(),
            FieldType::UInt64 => "UInt64".into(),
            FieldType::SInt32 => "SInt32".into(),
            FieldType::SInt64 => "SInt64".into(),
            FieldType::Fixed32 => "Fixed32".into(),
            FieldType::Fixed64 => "Fixed64".into(),
            FieldType::SFixed32 => "SFixed32".into(),
            FieldType::SFixed64 => "SFixed64".into(),
            FieldType::Bool => "Bool".into(),
            FieldType::Group => Err(ErrorKind::GroupNotSupported)?,
            FieldType::String => "String".into(),
            FieldType::Bytes => "Bytes".into(),
            FieldType::Enum(e) => format!(
                "Enum<{}>",
                e.native_ident_with_relative_path(self.msg.package()?)?,
            ),
            FieldType::Message(m) => {
                format!("Message<{}>", self.type_name_of_msg(m,)?)
            }
        })
    }

    pub fn default_func_for(&self, field: &'c FieldDescriptor<'c>) -> Result<Cow<'c, str>> {
        Ok(match self.context.impl_type() {
            ImplType::Default => match self.context.alloc_type() {
                AllocatorType::Default => match field.type_()? {
                    FieldType::Group => Err(ErrorKind::GroupNotSupported)?,
                    FieldType::Enum(_) => "|| 0i32.try_into()".into(),
                    _ => "::std::default::Default::default".into(),
                },
                AllocatorType::Bumpalo => match field.type_()? {
                    // Before this place, a local var puroro_internal is bound.
                    // let puroro_internal = &self.puroro_internal;
                    // We need this proxy var to tell the borrow checker that we are splitting
                    // the `self`.
                    FieldType::String => {
                        "|| ::bumpalo::collections::String::new_in(puroro_internal.bumpalo())"
                            .into()
                    }
                    FieldType::Bytes => {
                        "|| ::bumpalo::collections::Vec::new_in(puroro_internal.bumpalo())".into()
                    }
                    FieldType::Group => Err(ErrorKind::GroupNotSupported)?,
                    FieldType::Enum(_) => "|| 0i32.try_into()".into(),
                    FieldType::Message(m) => match field.label()? {
                        FieldLabel::Optional2 | FieldLabel::Optional3 => format!(
                            "|| ::bumpalo::boxed::Box::new_in({msg}::new_in(\
                                puroro_internal.bumpalo()\
                            ), puroro_internal.bumpalo())",
                            msg = self.struct_ident_with_relative_path(m)?,
                        )
                        .into(),
                        FieldLabel::Required | FieldLabel::Repeated => format!(
                            "|| {msg}::new_in(puroro_internal.bumpalo())",
                            msg = self.struct_ident_with_relative_path(m)?,
                        )
                        .into(),
                    },
                    _ => "::std::default::Default::default".into(),
                },
            },
            ImplType::SliceRef => {
                unimplemented!()
            }
        })
    }

    pub fn struct_generic_params(&self, params: &[&'static str]) -> String {
        let iter = params
            .iter()
            .cloned()
            .chain(match self.context.alloc_type() {
                AllocatorType::Default => None.into_iter(),
                AllocatorType::Bumpalo => Some("'bump").into_iter(),
            });
        if iter.clone().count() == 0 {
            "".to_string()
        } else {
            format!(
                "<{}>",
                Itertools::intersperse(iter, ", ").collect::<String>()
            )
        }
    }

    pub fn struct_generic_params_bounds(&self, params: &[&'static str]) -> String {
        self.struct_generic_params(params)
    }

    pub fn new_method_declaration(&self) -> &'static str {
        match self.context.alloc_type() {
            AllocatorType::Default => "fn new() -> Self",
            AllocatorType::Bumpalo => "fn new_in(bump: &'bump ::bumpalo::Bump) -> Self",
        }
    }
    pub fn field_clone(&self, field_ident: &str, field_type: &str) -> String {
        match self.context.alloc_type() {
            AllocatorType::Default => format!(
                "<{field_type} as FieldClone>::clone(&self.{field_ident})",
                field_ident = field_ident,
                field_type = field_type
            ),
            AllocatorType::Bumpalo => format!(
                "<{field_type} as FieldClone>::clone_in_bumpalo(\
                    &self.{field_ident}, self.puroro_internal.bumpalo())",
                field_ident = field_ident,
                field_type = field_type
            ),
        }
    }

    pub fn box_type(&self, item: &str) -> String {
        match self.context.alloc_type() {
            AllocatorType::Default => format!("::std::boxed::Box<{item}>", item = item),
            AllocatorType::Bumpalo => format!("::bumpalo::boxed::Box<'bump, {item}>", item = item),
        }
    }

    pub fn vec_type(&self, item: &str) -> String {
        match self.context.alloc_type() {
            AllocatorType::Default => format!("::std::vec::Vec<{item}>", item = item),
            AllocatorType::Bumpalo => {
                format!("::bumpalo::collections::Vec<'bump, {item}>", item = item)
            }
        }
    }

    pub fn string_type(&self) -> &'static str {
        match self.context.alloc_type() {
            AllocatorType::Default => "::std::string::String",
            AllocatorType::Bumpalo => "::bumpalo::collections::String<'bump>",
        }
    }

    pub fn internal_data_type(&self) -> &'static str {
        match self.context.alloc_type() {
            AllocatorType::Default => "::puroro_internal::helpers::InternalDataForNormalStruct",
            AllocatorType::Bumpalo => {
                "::puroro_internal::helpers::InternalDataForBumpaloStruct<'bump>"
            }
        }
    }

    pub fn internal_field_init_value(&self) -> &'static str {
        match self.context.alloc_type() {
            AllocatorType::Default => {
                "::puroro_internal::helpers::InternalDataForNormalStruct::new()"
            }
            AllocatorType::Bumpalo => {
                "::puroro_internal::helpers::InternalDataForBumpaloStruct::new(bump)"
            }
        }
    }
}
