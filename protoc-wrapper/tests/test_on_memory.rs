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

use ::puroro::google::protobuf::compiler::code_generator_response::File as ResFile;
use ::puroro::google::protobuf::compiler::{CodeGeneratorRequest, CodeGeneratorResponse};
use ::puroro_protoc_wrapper::ProtocOnMemory;

#[test]
fn test_on_memory() {
    let out_file_name = "empty_test.rs";
    let out_file_content = "This\nis\na\ntest";
    let proto_file_name = "empty_input.rs";
    let proto_file_content = "
syntax = \"proto3\";
package empty;
    ";

    let result_files = ProtocOnMemory::new()
        .add_file(proto_file_name, proto_file_content)
        .run(|req| {
            Ok(test_call_wrapper_inner(
                req,
                out_file_name,
                out_file_content,
            ))
        })
        .unwrap();

    assert_eq!(result_files.len(), 1);
    let (result_name, result_content) = &result_files[0];
    assert_eq!(result_name, out_file_name);
    assert_eq!(result_content, out_file_content);
}

fn test_call_wrapper_inner(
    req: CodeGeneratorRequest,
    out_file_name: &str,
    out_file_content: &str,
) -> CodeGeneratorResponse<'static> {
    let input_files = req.proto_file().collect::<Result<Vec<_>, _>>().unwrap();
    assert_eq!(input_files.len(), 1);
    let mut res = CodeGeneratorResponse::default();
    let mut file = ResFile::default();
    file.set_name(out_file_name).unwrap();
    file.set_content(out_file_content).unwrap();
    res.push_file(file).unwrap();
    res
}
