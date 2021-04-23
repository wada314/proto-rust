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
}
impl<'a, 'c> MessageImplFragmentGenerator<'a, 'c> {
    pub fn new(context: &'a Context<'c>) -> Self {
        Self { context }
    }

    pub fn struct_name(&self, msg: &'c MessageDescriptor<'c>) -> Result<Cow<'c, str>> {
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
            name = msg.native_bare_type_name(),
            postfix1 = postfix1,
            postfix2 = postfix2,
        )
        .into())
    }

    pub fn struct_name_with_relative_path(
        &self,
        msg: &'c MessageDescriptor<'c>,
        cur_package: &'c str,
    ) -> Result<String> {
        let struct_name = self.struct_name(msg)?;
        let mut struct_package_iter = msg.package().split('.').peekable();
        let mut cur_package_iter = cur_package.split('.').peekable();
        while let (Some(p1), Some(p2)) = (struct_package_iter.peek(), cur_package_iter.peek()) {
            if *p1 == *p2 {
                struct_package_iter.next();
                cur_package_iter.next();
            } else {
                break;
            }
        }
        Ok(format!(
            "{supers}{mods}{name}",
            name = struct_name,
            supers = std::iter::repeat("super::")
                .take(cur_package_iter.count())
                .collect::<String>(),
            mods = struct_package_iter
                .map(|s| get_keyword_safe_ident(&to_lower_snake_case(s)) + "::")
                .collect::<String>(),
        ))
    }

    pub fn type_name_of_msg(
        &self,
        msg: &'c MessageDescriptor<'c>,
        cur_package: &'c str,
    ) -> Result<String> {
        let generic_args_iter = match self.context.alloc_type() {
            AllocatorType::Default => None,
            AllocatorType::Bumpalo => Some("'bump"),
        }
        .into_iter();
        if generic_args_iter.clone().count() == 0 {
            Ok(self.struct_name_with_relative_path(msg, cur_package)?)
        } else {
            let generic_args = Itertools::intersperse(generic_args_iter, ", ").collect::<String>();
            Ok(format!(
                "{name}<{gargs}>",
                name = self.struct_name_with_relative_path(msg, cur_package)?,
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

    pub fn field_type_for(&self, field: &'c FieldDescriptor<'c>) -> Result<Cow<'c, str>> {
        Ok(match self.context.impl_type() {
            ImplType::Default => {
                let scalar_type: Cow<'static, str> = match field.type_()?.native_trivial_type_name()
                {
                    Ok(name) => name.into(),
                    Err(nontrivial_type) => match nontrivial_type {
                        NonTrivialFieldType::Group => Err(ErrorKind::GroupNotSupported)?,
                        NonTrivialFieldType::String => self.string_type().into(),
                        NonTrivialFieldType::Bytes => self.vec_type("u8").into(),

                        NonTrivialFieldType::Enum(e) => format!(
                            "::std::result::Result<{type_}, i32>",
                            type_ = e.native_fully_qualified_type_name(field.path_to_root_mod())
                        )
                        .into(),
                        NonTrivialFieldType::Message(m) => {
                            self.type_name_of_msg(m, field.package())?.into()
                        }
                    },
                };
                match field.label()? {
                    FieldLabel::Optional => {
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
                }
            }
            ImplType::SliceRef => {
                let scalar_type: Cow<'static, str> = match field.type_()?.native_trivial_type_name()
                {
                    Ok(name) => name.into(),
                    Err(nontrivial_type) => match nontrivial_type {
                        NonTrivialFieldType::Group => Err(ErrorKind::GroupNotSupported)?,
                        NonTrivialFieldType::String => "Cow<'slice, str>".into(),
                        NonTrivialFieldType::Bytes => "&'slice [u8]".into(),
                        NonTrivialFieldType::Enum(e) => format!(
                            "::std::result::Result<{type_}, i32>",
                            type_ = e.native_fully_qualified_type_name(field.path_to_root_mod())
                        )
                        .into(),
                        NonTrivialFieldType::Message(m) => self
                            .struct_name_with_relative_path(m, field.package())?
                            .into(),
                    },
                };
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
            AllocatorType::Default => "::puroro::helpers::InternalDataForNormalStruct",
            AllocatorType::Bumpalo => "::puroro::helpers::InternalDataForBumpaloStruct<'bump>",
        }
    }

    pub fn internal_field_init_value(&self) -> &'static str {
        match self.context.alloc_type() {
            AllocatorType::Default => "::puroro::helpers::InternalDataForNormalStruct::new()",
            AllocatorType::Bumpalo => "::puroro::helpers::InternalDataForBumpaloStruct::new(bump)",
        }
    }
}
