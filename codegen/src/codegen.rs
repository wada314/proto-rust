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

mod data;
mod gen;
mod util;

use self::data::*;
use self::gen::*;

use crate::{ErrorKind, GeneratorError, Result};
use ::proc_macro2::TokenStream;
use ::puroro_protobuf_compiled::google::protobuf::compiler::code_generator_response::File;
use ::puroro_protobuf_compiled::google::protobuf::compiler::CodeGeneratorResponse;
use ::puroro_protobuf_compiled::google::protobuf::FileDescriptorProto;
use ::std::iter;
use ::std::rc::Rc;

#[derive(Debug, Clone, Copy)]
pub enum Syntax {
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
pub enum MessageOrEnum<M, E> {
    Message(M),
    Enum(E),
}

pub fn generate_file_names_and_tokens<'a>(
    files: impl Iterator<Item = &'a FileDescriptorProto>,
) -> Result<impl IntoIterator<Item = (String, TokenStream)>> {
    let root_package = RootPackage::new(files);
    let from_packages = root_package
        .all_packages()?
        .into_iter()
        .chain(iter::once(Rc::clone(&root_package) as Rc<dyn Package>))
        .map(|p| -> Result<_> { Ok((p.module_file_path()?.to_string(), p.gen_module_file()?)) });
    let from_messages = root_package
        .all_messages()?
        .into_iter()
        .filter_map(|m| match m.should_generate_module_file() {
            Ok(true) => Some(Ok(m)),
            Ok(false) => None,
            Err(e) => Some(Err(e)),
        })
        .map(|rm| {
            let m = rm?;
            Ok((m.module_file_path()?.to_string(), m.gen_module_file()?))
        });

    from_packages
        .chain(from_messages)
        .collect::<Result<Vec<_>>>()
}

pub fn generate_output_file_protos<'a>(
    files: impl Iterator<Item = &'a FileDescriptorProto>,
) -> Result<CodeGeneratorResponse> {
    let mut cgr = CodeGeneratorResponse::default();
    *cgr.file_mut() = generate_file_names_and_tokens(files)?
        .into_iter()
        .map(|(file_name, ts)| {
            let formatted = if let Ok(syn_file) = syn::parse2::<syn::File>(ts.clone()) {
                prettyplease::unparse(&syn_file)
            } else {
                // Parse failed route. Print the output file for debugging.
                eprintln!("Generated code error!");
                format!("{}", ts)
            };
            let mut output_file = File::default();
            *output_file.name_mut() = file_name;
            *output_file.content_mut() = formatted;
            Ok(output_file)
        })
        .collect::<Result<Vec<_>>>()?;

    Ok(cgr)
}

pub fn generate_tokens_for_inline<'a>(
    files: impl Iterator<Item = &'a FileDescriptorProto>,
) -> Result<TokenStream> {
    let root_package = RootPackage::new(files);
    root_package.gen_inline_code()
}