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

use crate::descriptor::FieldDescriptor;
use crate::internal::variant::Variant;

use crate::{ErrorKind, Result};

pub struct GenericMessage {
    fields: Vec<Field>,
}

impl GenericMessage {
    fn set_field_descriptor(&mut self, descriptor: &FieldDescriptor) -> Result<()> {
        todo!()
    }
}

pub struct Field {
    number: i32,
    name: String,
    records: Vec<WireTypeAndPayload>,
}

trait FieldBody {
    fn as_i32(&self) -> Result<i32>;
    fn as_opt_i32(&self) -> Result<Option<i32>>;
    fn as_repeated_i32(&self) -> Result<impl IntoIterator<Item = i32>>;
}

enum WireTypeAndPayload {
    Varint(Variant),
    Fixed64([u8; 8]),
    Fixed32([u8; 4]),
    LengthDelimited(Vec<u8>),
    // StartGroup,
    // EndGroup,
}