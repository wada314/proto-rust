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

use crate::tests_pb::self_recursive::Msg;

#[test]
fn test_new() {
    let msg = Msg::default();
    let msg: Msg;
}

fn hoge(msg: &mut Msg) {
    use ::puroro::internal::DeserializableMessageFromBytesIterator;
    use std::io::Read;
    let buf = vec![0u8];
    msg.deser(buf.bytes());
}
