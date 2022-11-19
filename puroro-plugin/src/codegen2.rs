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

mod r#enum;
mod field;
mod field_rule;
mod field_type;
mod input_file;
mod message;
mod oneof;
mod package;
mod util;
use self::r#enum::*;
use self::field::*;
use self::field_rule::*;
use self::field_type::*;
use self::input_file::*;
use self::message::*;
use self::oneof::*;
use self::package::*;
use self::util::*;
use crate::{ErrorKind, GeneratorError, Result};
use ::proc_macro2::TokenStream;
use ::puroro_protobuf_compiled::google::protobuf::compiler::code_generator_response::File;
use ::puroro_protobuf_compiled::google::protobuf::compiler::CodeGeneratorResponse;
use ::puroro_protobuf_compiled::google::protobuf::FileDescriptorProto;
use ::std::iter;
use ::std::ops::Deref;
use ::std::rc::Rc;

#[derive(Debug, Clone, Copy)]
enum Syntax {
    Proto2,
    Proto3,
}
impl TryFrom<&str> for Syntax {
    type Error = GeneratorError;
    fn try_from(value: &str) -> Result<Self> {
        Ok(match value {
            "" | "proto2" => Syntax::Proto2,
            "proto3" => Syntax::Proto3,
            _ => Err(ErrorKind::UnknownProtoSyntax {
                name: value.to_string(),
            })?,
        })
    }
}

#[derive(Debug, Clone, Copy)]
enum MessageOrPackage<M, P> {
    Message(M),
    Package(P),
}

#[derive(Debug, Clone, Copy)]
enum MessageOrEnum<M, E> {
    Message(M),
    Enum(E),
}

fn all_packages(root: &dyn PackageTrait) -> Vec<&dyn PackageTrait> {
    let mut ret = Vec::new();
    let mut stack = vec![root];
    while let Some(p) = stack.pop() {
        stack.extend(p.subpackages());
        ret.push(p);
    }
    ret
}

pub fn generate_file_names_and_tokens<'a>(
    files: impl Iterator<Item = &'a FileDescriptorProto>,
) -> Result<impl IntoIterator<Item = (String, TokenStream)>> {
    let root_package = Package::try_new_from_files(files)?;
    Ok(all_packages(Box::deref(Rc::deref(&root_package)))
        .into_iter()
        .map(|p| -> Result<_> { Ok((p.module_file_name()?, p.gen_module_file()?)) })
        .chain(iter::once(Ok((
            root_package.module_file_name()?,
            root_package.gen_module_file()?,
        ))))
        .collect::<Result<Vec<_>>>()?)
}

pub fn generate_output_file_protos<'a>(
    files: impl Iterator<Item = &'a FileDescriptorProto>,
) -> Result<CodeGeneratorResponse> {
    let mut cgr = CodeGeneratorResponse::default();
    *cgr.file_mut() = generate_file_names_and_tokens(files)?
        .into_iter()
        .map(|(file_name, ts)| {
            let syn_file = syn::parse2::<syn::File>(ts).unwrap();
            let formatted = prettyplease::unparse(&syn_file);

            let mut output_file = File::default();
            *output_file.name_mut() = file_name;
            *output_file.content_mut() = formatted;
            Ok(output_file)
        })
        .collect::<Result<Vec<_>>>()?;

    Ok(cgr)
}