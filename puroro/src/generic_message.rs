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

use super::FieldDescriptorType;
use crate::Result;

pub trait GenericMessage {
    type StringType<'a, FD>: AsRef<str> + Default
    where
        Self: 'a;
    type MessageType<'a, FD>: GenericMessage
    where
        Self: 'a;
    fn get_string<FD: FieldDescriptorType>(&self) -> Result<Self::StringType<'_, FD>>;
    fn get_message<FD: FieldDescriptorType>(&self) -> Result<Self::MessageType<'_, FD>>;
}

impl<T: GenericMessage> GenericMessage for Option<T> {
    type StringType<'a, FD> = T::StringType<'a, FD>
    where
        Self: 'a;
    type MessageType<'a, FD> = Option<T::MessageType<'a, FD>>
    where
        Self: 'a;
    fn get_string<FD: FieldDescriptorType>(&self) -> Result<Self::StringType<'_, FD>> {
        self.as_ref()
            .map_or_else(|| Ok(Default::default()), |t| T::get_string::<FD>(t))
    }
    fn get_message<FD: FieldDescriptorType>(&self) -> Result<Self::MessageType<'_, FD>> {
        self.as_ref().map(|t| T::get_message(t)).transpose()
    }
}

impl<'a, T: GenericMessage> GenericMessage for &'a T {
    type StringType<'b, FD> = T::StringType<'b, FD>
    where
        Self: 'b;
    type MessageType<'b, FD> = T::MessageType<'b, FD>
    where
        Self: 'b;
    fn get_string<FD: FieldDescriptorType>(&self) -> Result<Self::StringType<'_, FD>> {
        T::get_string(*self)
    }
    fn get_message<FD: FieldDescriptorType>(&self) -> Result<Self::MessageType<'_, FD>> {
        T::get_message(*self)
    }
}
