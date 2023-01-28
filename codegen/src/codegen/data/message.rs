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

use super::super::util::*;
use super::{
    DataTypeBase, Enum, Field, FieldOrOneof, InputFile, Oneof, Package, PackageOrMessage,
    PackageOrMessageCase, RootPackage,
};
use crate::Result;
use ::puroro_protobuf_compiled::google::protobuf::DescriptorProto;
use ::std::fmt::Debug;
use ::std::iter;
use ::std::rc::{Rc, Weak};

pub trait Message: Debug + PackageOrMessage {
    fn input_file(&self) -> Result<Rc<dyn InputFile>>;
    fn parent(&self) -> Result<Rc<dyn PackageOrMessage>>;
    fn fields(&self) -> Result<Box<dyn '_ + Iterator<Item = Rc<Field>>>>;
    fn fields_or_oneofs(&self) -> Result<Box<dyn '_ + Iterator<Item = Rc<dyn FieldOrOneof>>>>;

    fn should_generate_module_file(&self) -> Result<bool> {
        let has_submessages = self.messages()?.next().is_some();
        let has_subenums = self.enums()?.next().is_some();
        let has_oneofs = self.oneofs()?.next().is_some();
        Ok(has_submessages || has_subenums || has_oneofs)
    }
}

#[derive(Debug)]
pub struct MessageImpl {
    cache: AnonymousCache,
    name: String,
    fields: Vec<Rc<Field>>,
    messages: Vec<Rc<dyn Message>>,
    enums: Vec<Rc<Enum>>,
    oneofs: Vec<Rc<Oneof>>,
    input_file: Weak<dyn InputFile>,
    parent: Weak<dyn PackageOrMessage>,
}

impl MessageImpl {
    pub fn new(
        proto: &DescriptorProto,
        input_file: Weak<dyn InputFile>,
        parent: Weak<dyn PackageOrMessage>,
    ) -> Rc<Self> {
        Self::new_with(proto, input_file, parent, MessageImpl::new)
    }

    pub fn new_with<FM, M>(
        proto: &DescriptorProto,
        input_file: Weak<dyn InputFile>,
        parent: Weak<dyn PackageOrMessage>,
        fm: FM,
    ) -> Rc<Self>
    where
        FM: Fn(&DescriptorProto, Weak<dyn InputFile>, Weak<dyn PackageOrMessage>) -> Rc<M>,
        M: 'static + Message,
    {
        let name = proto.name().to_string();
        Rc::new_cyclic(|weak_message| {
            let fields = proto
                .field()
                .into_iter()
                .filter(|f| !f.has_oneof_index() || f.has_proto3_optional())
                .map(|f| Field::new(f, Weak::clone(weak_message) as Weak<dyn Message>) as Rc<Field>)
                .collect();
            let messages = proto
                .nested_type()
                .into_iter()
                .map(|m| {
                    fm(
                        m,
                        Weak::clone(&input_file),
                        Weak::clone(weak_message) as Weak<dyn PackageOrMessage>,
                    ) as Rc<dyn Message>
                })
                .collect();
            let enums = proto
                .enum_type()
                .into_iter()
                .map(|e| {
                    Enum::new(
                        e,
                        Weak::clone(&input_file),
                        Weak::clone(weak_message) as Weak<dyn PackageOrMessage>,
                    )
                })
                .collect();
            let oneof_num = proto
                .field()
                .iter()
                .filter_map(|f| match (f.oneof_index_opt(), f.proto3_optional()) {
                    (Some(i), false) => Some(i as usize),
                    _ => None,
                })
                .max()
                .map_or(0, |i| i + 1);
            let oneofs = (0..oneof_num)
                .into_iter()
                .map(|i| {
                    Oneof::new(
                        proto,
                        &proto.oneof_decl()[i],
                        i,
                        Weak::clone(weak_message) as Weak<dyn Message>,
                    )
                })
                .collect();
            MessageImpl {
                cache: Default::default(),
                name,
                input_file: Weak::clone(&input_file),
                parent,
                fields,
                messages,
                enums,
                oneofs,
            }
        })
    }
}

impl DataTypeBase for MessageImpl {
    fn cache(&self) -> &AnonymousCache {
        &self.cache
    }
    fn name(&self) -> Result<&str> {
        Ok(&self.name)
    }
}

impl PackageOrMessage for MessageImpl {
    fn either(&self) -> PackageOrMessageCase<&dyn Package, &dyn Message> {
        PackageOrMessageCase::Message(self)
    }

    fn messages(&self) -> Result<Box<dyn '_ + Iterator<Item = Rc<dyn Message>>>> {
        Ok(Box::new(self.messages.iter().cloned()))
    }
    fn enums(&self) -> Result<Box<dyn '_ + Iterator<Item = Rc<Enum>>>> {
        Ok(Box::new(self.enums.iter().cloned()))
    }
    fn oneofs(&self) -> Result<Box<dyn '_ + Iterator<Item = Rc<Oneof>>>> {
        Ok(Box::new(self.oneofs.iter().cloned()))
    }
    fn subpackages(&self) -> Result<Box<dyn '_ + Iterator<Item = Rc<dyn Package>>>> {
        Ok(Box::new(iter::empty()))
    }
    fn root_package(&self) -> Result<Rc<RootPackage>> {
        self.parent.try_upgrade()?.root_package()
    }
    fn parent(&self) -> Result<Option<Rc<dyn PackageOrMessage>>> {
        Ok(Some(self.parent.try_upgrade()?))
    }
}

impl Message for MessageImpl {
    fn input_file(&self) -> Result<Rc<dyn InputFile>> {
        Ok(self.input_file.try_upgrade()?)
    }
    fn parent(&self) -> Result<Rc<dyn PackageOrMessage>> {
        Ok(self.parent.try_upgrade()?)
    }
    fn fields(&self) -> Result<Box<dyn '_ + Iterator<Item = Rc<Field>>>> {
        Ok(Box::new(self.fields.iter().cloned()))
    }
    fn fields_or_oneofs(&self) -> Result<Box<dyn '_ + Iterator<Item = Rc<dyn FieldOrOneof>>>> {
        let fields = self
            .fields
            .iter()
            .map(|f| f.clone() as Rc<dyn FieldOrOneof>);
        let oneofs = self
            .oneofs
            .iter()
            .map(|o| o.clone() as Rc<dyn FieldOrOneof>);
        Ok(Box::new(fields.chain(oneofs)))
    }
}
