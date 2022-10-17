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

#![feature(error_generic_member_access)]
#![feature(provide_any)]
#![feature(generic_associated_types)]
#![feature(is_some_with)]

mod codegen;
mod error;
mod rustfmt;

use ::puroro_protobuf_compiled::google::protobuf::compiler::CodeGeneratorRequest;
use ::puroro_protobuf_compiled::puroro;
use ::puroro_protobuf_compiled::puroro::Message;
use ::std::io::{stdin, stdout, Read};

use error::{ErrorKind, GeneratorError};
type Result<T> = std::result::Result<T, GeneratorError>;

fn main() -> Result<()> {
    let request = CodeGeneratorRequest::from_bytes_iter(&mut stdin().bytes()).unwrap();
    let config = codegen::Config::default();
    let response = codegen::generate_response_from_request(request, &config)?;
    response.to_bytes(&mut stdout())?;
    Ok(())
}
