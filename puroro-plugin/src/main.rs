#![cfg_attr(feature = "puroro-nightly", feature(backtrace))]
#![feature(generic_associated_types)]
#![feature(arc_new_cyclic)]
#![allow(incomplete_features)]

mod error;
mod generators;
mod impls;
mod protos;
mod utils;
mod wrappers;

use ::itertools::Itertools;
use ::puroro::{DeserFromBytesIter, SerToIoWrite};

use error::{ErrorKind, GeneratorError};
type Result<T> = std::result::Result<T, GeneratorError>;

use std::collections::{HashMap, HashSet};
use std::io::Read;
use std::io::{stdin, stdout};
use std::rc::Rc;

pub use protos::google;
use protos::google::protobuf::compiler::code_generator_response::File;
use protos::google::protobuf::compiler::{CodeGeneratorRequest, CodeGeneratorResponse};

use ::askama::Template as _;

fn make_package_to_subpackages_map(
    files: &Vec<google::protobuf::FileDescriptorProto>,
) -> HashMap<String, HashSet<String>> {
    let mut map = HashMap::new();
    for file in files {
        let package_string = file.package.clone().unwrap_or_default();
        let package_vec = package_string
            .split('.')
            .filter_map(|p| {
                if p.is_empty() {
                    None
                } else {
                    Some(p.to_string())
                }
            })
            .collect::<Vec<_>>();
        for i in 0..(package_vec.len()) {
            let cur_package = package_vec.iter().take(i).join(".");
            let subpackage = package_vec[i].clone();
            map.entry(cur_package)
                .or_insert(HashSet::new())
                .insert(subpackage);
        }
    }
    map
}

fn package_to_filename(package: &str) -> String {
    if package.is_empty() {
        "mod.rs".to_string()
    } else {
        package
            .split('.')
            .map(|f| utils::get_keyword_safe_ident(f))
            .join("/")
            + ".rs"
    }
}
/*
#[derive(Template, Default)]
#[template(path = "file.rs.txt")]
pub struct OutputFile {
    subpackages: HashSet<String>,
    file: Option<Rc<wrappers::InputFile>>,
}

#[derive(Template, Default)]
#[template(path = "messages.rs.txt")]
pub struct Messages {
    messages: Vec<Rc<wrappers::Message>>,
}

#[derive(Template)]
#[template(path = "message.rs.txt")]
pub struct Message {
    message: Rc<wrappers::Message>,
}

#[derive(Template)]
#[template(path = "trait.rs.txt")]
pub struct Trait {
    message: Rc<wrappers::Message>,
}

#[derive(Template)]
#[template(path = "enums.rs.txt")]
pub struct Enums {
    enums: Vec<Rc<wrappers::Enum>>,
}

#[derive(Template)]
#[template(path = "oneofs.rs.txt")]
pub struct Oneofs {
    oneofs: Vec<Rc<wrappers::Oneof>>,
}

impl Messages {
    pub fn has_nested_items(&self) -> bool {
        self.messages.iter().any(|m| m.has_nested_items())
    }
}

mod filters {
    use super::*;
    pub fn render_messages(messages: &[Rc<wrappers::Message>]) -> ::askama::Result<Messages> {
        Ok(Messages {
            messages: messages.to_vec(),
        })
    }
    pub fn render_message(message: &Rc<wrappers::Message>) -> ::askama::Result<Message> {
        Ok(Message {
            message: Clone::clone(message),
        })
    }
    pub fn render_impl_simple(
        message: &Rc<wrappers::Message>,
    ) -> ::askama::Result<impls::SimpleImpl> {
        Ok(impls::SimpleImpl::try_new(message).unwrap())
    }
    pub fn render_oneof_simple(
        oneof: &Rc<wrappers::Oneof>,
    ) -> ::askama::Result<impls::SimpleOneof> {
        Ok(impls::SimpleOneof::try_new(oneof).unwrap())
    }
    pub fn render_trait(message: &Rc<wrappers::Message>) -> ::askama::Result<Trait> {
        Ok(Trait {
            message: Clone::clone(message),
        })
    }
    pub fn render_enums(enums: &[Rc<wrappers::Enum>]) -> ::askama::Result<Enums> {
        Ok(Enums {
            enums: enums.to_vec(),
        })
    }
    pub fn render_oneofs(oneofs: &[Rc<wrappers::Oneof>]) -> ::askama::Result<Oneofs> {
        Ok(Oneofs {
            oneofs: oneofs.to_vec(),
        })
    }
}
 */

fn main() -> Result<()> {
    let mut cgreq: CodeGeneratorRequest = CodeGeneratorRequest::default();
    cgreq.deser(&mut stdin().bytes()).unwrap();

    let wrapped_cgreq = wrappers::Context::try_from_proto(cgreq.clone())?;

    let mut cgres: CodeGeneratorResponse = CodeGeneratorResponse::default();
    cgres.supported_features = Some(1); // TODO: Use Feature enum

    let mut mod_rs: File = File::default();
    mod_rs.name = Some("mod.rs".into());
    let package_to_subpackage_map = make_package_to_subpackages_map(&cgreq.proto_file);
    let package_to_file_descriptor_map = wrapped_cgreq
        .input_files()
        .iter()
        .map(|file| {
            Ok((
                file.package().iter().join("."),
                Rc::new(generators::InputFile::try_new(file)?),
            ))
        })
        .collect::<Result<HashMap<_, _>>>()?;

    // merge 2 hashmaps, create a HashMap of OutputFile
    let mut output_file_contexts = HashMap::<String, generators::OutputFile>::new();
    for (package, subpackages) in package_to_subpackage_map {
        let mut v = subpackages.into_iter().collect_vec();
        v.sort();
        output_file_contexts
            .entry(package.clone())
            .or_insert_with(|| generators::OutputFile::new(&package))
            .subpackages = v;
    }
    for (package, file) in package_to_file_descriptor_map {
        output_file_contexts
            .entry(package.clone())
            .or_insert_with(|| generators::OutputFile::new(&package))
            .input_file = Some(file);
    }

    for output_contexts in output_file_contexts.values() {
        let filename = package_to_filename(&output_contexts.package);
        // Do render!
        let contents = output_contexts.render().unwrap();

        let mut output_file = <File as Default>::default();
        output_file.name = Some(filename.into());
        output_file.content = Some(contents.into());
        cgres.file.push(output_file);
    }

    cgres.ser(&mut stdout())?;
    Ok(())
}
