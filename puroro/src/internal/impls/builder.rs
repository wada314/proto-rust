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

//! # Builders and SingleField structs
//!
//! puroro also generates a set of structs which is postfixed by "SingleField***N***"
//! (***N*** is the number of the field), which stores only a certain field.
//! You normally don't need to directly use these structs, but instead you can use
//! the `Builder` struct which is also generated by puroro to compose a struct:
//!
//! ```protobuf
//! syntax = "proto3";
//! message MyMessage {
//!     int32 my_number = 1;
//!     repeated string my_name = 2;
//!     MyMessage my_child = 3;
//! }
//! ```
//!
//! ```rust
//! # use ::std::ops::Deref;
//! # trait MyMessageTrait {}
//! pub struct MyMessageBuilder<T>(T);
//! impl MyMessageBuilder<()> {
//!     pub fn new() -> Self {
//! #       todo!()
//!         /* ... */
//!     }
//! }
//! impl<T: MyMessageTrait> MyMessageBuilder<T> {
//!     pub fn append_my_number(self, value: i32)
//!     -> MyMessageBuilder<(T, MyMessageSingleField1)> {
//! #       todo!()
//!         /* ... */
//!     }
//!     pub fn append_my_name<U, V>(self, value: U)
//!     -> MyMessageBuilder<(T, MyMessageSingleField2<U, V>)>
//!     where
//!         for<'a> &'a U: IntoIterator<Item=&'a V>,
//!         V: AsRef<str>,
//!     {
//! #       todo!()
//!         /* ... */
//!     }
//!     pub fn append_my_child<U: MyMessageTrait>(self, value: U)
//!     -> MyMessageBuilder<(T, MyMessageSingleField3<U>)> {
//! #       todo!()
//!         /* ... */
//!     }
//! }
//!
//! pub struct MyMessageSingleField1 {
//!     /* ... */
//! }
//! pub struct MyMessageSingleField2<T, U> {
//!     /* ... */
//! #     dummy: (T, U),
//! }
//! pub struct MyMessageSingleField3<T> {
//!     /* ... */
//! #     dummy: T,
//! }
//! ```
//!
//! Usage:
//!
//! ```ignored
//! let my_message = MyMessageBuilder::new()
//!     .append_my_number(10)
//!     .append_my_name(vec!["foo", "bar"])
//!     .build();
//! assert_eq!(10, my_message.my_number());
//! ```
//!
//! The biggest benefit of this builder is that the generated message only
//! consumes the memory for existing fields.
//! Even if you have a message which have 100 `int32` fields, if you use
//! this builder and set only 1 field, then the generated
//! struct only consumes as same memory size as an 1 field struct.
//!
//! # Field types
//!
//! For every fields (including the fields of nested oneof fields),
//! a method `append_<fieldname>` is generated for the builder struct.
//! The parameter types that these `append_*` methods can take are:
//!
//! | base protobuf type | `required` / `optional | (unlabeled) / `oneof` field | `repeated` |
//! |--------------------|----------------------- |-----------------------------|------------|
//! | `int32` | `Option<i32>` | `i32` | (see below) |
//! | (any numeric types) | `Option<T>` | `T` | (see below) |
//! | `bytes` | `Option<impl AsRef<[u8]>>` | impl AsRef<[u8]> | (see below) |
//! | `string` | `Option<impl AsRef<str>>` | impl AsRef<str> | (see below) |
//! | `SomeMessage` | `Option<impl SomeMessageTrait>` | Option<impl SomeMessageTrait> | (see below) |
//!
//! For repeated fields, a type `<RepeatedType>` where:
//!
//! `for <'a> &'a RepeatedType: IntoIterator<Item=&'a ScalarType>`
//!
//! can be passed. For example, `Vec<T>` or `&[T]` can be passed.
//!
//! # Limitations
//! You may feel strange that the methods are named as `append_something`, not `set_something`.
//! This is because that our builder methods have some limitations:
//!
//! - For non-message optional / required fields, you cannot "clear" the field
//! once you have set some value.
//! - Same for message non-repeated fields, you cannot "clear" the existing field
//! but you can only merge into the existing field.
//! - For non-message proto3 unlabeled fields, you cannot set the field value to
//! a default value (e.g. `0` for int32, `""` for string) once you have set a value.
//! - For repeated fields, you can only append the items. You cannot remove any
//! items from the existing field.
//!
//! These limitations come from the protobuf language spec and our implementation
//! of builder structs. Our builder's append methods are literally appending the
//! field into the existing message. When the generated message is serialized,
//! the fields are serialized in the same order with the append methods' call order.
//! In the protocol buffer's specification, it is legal that the same field appears
//! several times in the serialized bytes array and the behavior for that is well
//! defined (as the above limitations).
//!
//! # Samples
//! File `tests/src/cases/builder.rs` contains some test cases against
//! `tests-pb/protos/full-coverage3.proto` .
//!
