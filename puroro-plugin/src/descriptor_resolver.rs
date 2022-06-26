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

use super::descriptor_ext::{DescriptorExt, EnumDescriptorExt, FileDescriptorExt};
use crate::{ErrorKind, Result};
use ::std::collections::HashMap;
use ::std::rc::Rc;

#[derive(Debug)]
pub struct DescriptorResolver {
    fqtn_to_desc_map: HashMap<String, RcMessageOrEnum>,
}
impl<'a> DescriptorResolver {
    pub fn new<I>(file_descriptors_iter: I) -> Result<Self>
    where
        I: Iterator<Item = Rc<FileDescriptorExt>>,
    {
        let mut fqtn_to_desc_map = HashMap::new();
        for f in file_descriptors_iter {
            f.for_each_message(|m| {
                fqtn_to_desc_map.insert(m.fqtn().unwrap().to_string(), RcMessageOrEnum::Message(m));
            });
            f.for_each_enum(|e| {
                fqtn_to_desc_map.insert(e.fqtn().unwrap().to_string(), RcMessageOrEnum::Enum(e));
            });
        }
        Ok(Self { fqtn_to_desc_map })
    }

    pub fn fqtn_to_desc(&self, fqtn: &str) -> Option<RcMessageOrEnum> {
        self.fqtn_to_desc_map.get(fqtn).cloned()
    }
}

#[derive(Debug, Clone)]
pub enum RcMessageOrEnum {
    Message(Rc<DescriptorExt>),
    Enum(Rc<EnumDescriptorExt>),
}
