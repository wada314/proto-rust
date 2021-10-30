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

//! Yet another Rust implementation of [Google Protocol Buffer](https://developers.google.com/protocol-buffers).
//!
//! # Generated structs
//!
//! For an input .proto file like this:
//! ```protobuf
//! syntax = "proto3";
//! message MyMessage {
//!     int32 my_number = 1;
//!     repeated string my_name = 2;
//!     MyMessage my_child = 3;
//! }
//! ```
//!
//! A struct like this is output ([detailed doc](internal::impls::simple)):
//! ```rust
//! pub struct MyMessage {
//!     pub my_number: i32,
//!     pub my_name: Vec<String>,
//!     pub my_child: Option<Box<MyMessage>>,
//! }
//! ```
//!
//! You can deserialize a struct from `Iterator<std::io::Result<u8>>`
//! (which is a return type of `std::io::Read::bytes()` method):
//! ```rust
//! # #[derive(Default)]
//! # pub struct MyMessage {
//! #     pub my_number: i32,
//! # }
//! # use ::puroro::*;
//! # impl Message<MyMessage> for MyMessage {}
//! # impl internal::DeserializableMessageFromBytesIterator for MyMessage {
//! #     fn deser<I>(&mut self, iter: I) -> Result<()>
//! #     where
//! #         I: Iterator<Item = ::std::io::Result<u8>>
//! #     {
//! #         internal::de::from_iter::deser_from_iter(self, iter)
//! #     }
//! # }
//! # impl internal::de::DeserFieldsFromBytesIter for MyMessage {
//! #     fn deser_field<I>(
//! #         &mut self,
//! #         field_number: i32,
//! #         data: internal::types::FieldData<&mut internal::de::from_iter::ScopedIter<I>>,
//! #     ) -> Result<()>
//! #     where
//! #         I: Iterator<Item = ::std::io::Result<u8>>,
//! #     {
//! #         use internal::impls::simple::de::DeserFieldFromBytesIter;
//! #         match field_number {
//! #             1 => DeserFieldFromBytesIter::<
//! #                 tags::Unlabeled, tags::Int32
//! #             >::deser_field(&mut self.my_number, data),
//! #             _ => panic!(),
//! #         }
//! #     }
//! # }
//! use puroro::Message; // For from_bytes() method
//! use std::io::Read; // For bytes() method
//! let input = vec![0x08, 0x0a];
//! let msg = MyMessage::from_bytes(input.bytes()).unwrap();
//! assert_eq!(10, msg.my_number);
//! ```
//!
//! And serialize it to `std::io::Write`:
//! ```rust
//! # #[derive(Default)]
//! # pub struct MyMessage {
//! #     pub my_number: i32,
//! # }
//! # use ::puroro::{internal, Result, tags};
//! # impl Message<MyMessage> for MyMessage {}
//! # impl ::puroro::internal::SerializableMessageToIoWrite for MyMessage {
//! #     fn ser<W>(&self, out: &mut W) -> Result<()> where W: std::io::Write {
//! #         internal::impls::simple::se::SerFieldToIoWrite::<tags::Unlabeled, tags::Int32>::ser_field(
//! #             &self.my_number, 1, out
//! #         )
//! #     }
//! # }
//! use puroro::Message; // For ser() method
//! let mut output = vec![];
//! let mut msg = MyMessage::default();
//! msg.my_number = 10;
//! msg.ser(&mut output).unwrap();
//! assert_eq!(vec![0x08, 0x0a], output);
//! ```
//!
//! # Generated traits
//! ([Detailed doc](internal::impls::traits))
//!
//! For the same input as above:
//! ```protobuf
//! syntax = "proto3";
//! message MyMessage {
//!     int32 my_number = 1;
//!     repeated string my_name = 2;
//!     MyMessage my_child = 3;
//! }
//! ```
//!
//! Trait like this is generated
//! (Omitting some bounds for explanation. Please check the [traits](internal::impls::traits) page for detail):
//!
//! ```rust
//! // A readonly trait for message `MyMessage`
//! # #![feature(generic_associated_types)]
//! # use ::std::ops::Deref;
//! pub trait MyMessageTrait {
//!     fn my_number(&self) -> i32;
//!     fn my_number_opt(&self) -> Option<i32>;
//!     fn has_my_number(&self) -> bool;
//!     type Field2RepeatedType<'this>: IntoIterator<Item=&'this str>;
//!     fn my_name(&self) -> Self::Field2RepeatedType<'_>;
//!     type Field3MessageType<'this>: MyMessageTrait;
//!     fn my_child(&self) -> Option<Self::Field3MessageType<'_>>;
//!     fn my_child_opt(&self) -> Option<Self::Field3MessageType<'_>>;
//!     fn has_my_child(&self) -> bool;
//! }
//! ```
//!
//! The trait is implemented for the struct `MyMessage` and few other items:
//!
//! ```rust
//! # trait MyMessageTrait {}
//! impl MyMessageTrait for () { /* ... */ }
//! impl<'a, T: MyMessageTrait> MyMessageTrait for &'a T { /* ... */ }
//! impl<'a, T: MyMessageTrait> MyMessageTrait for &'a mut T { /* ... */ }
//! impl<T: MyMessageTrait> MyMessageTrait for Box<T> { /* ... */ }
//! impl<T: MyMessageTrait> MyMessageTrait for Option<T> { /* ... */ }
//! impl<T: MyMessageTrait, U: MyMessageTrait> MyMessageTrait for (T, U) { /* ... */ }
//! impl<T: MyMessageTrait, U: MyMessageTrait> MyMessageTrait for puroro::Either<T, U> { /* ... */ }
//! ```
//!
//! # Builder struct
//! ([Detailed doc](internal::impls::builder))
//!
//! puroro also generates a message builder.
//! A message generated by this builder has an advantage against
//! the normal message struct in memory size: It only consumes
//! the memory for the explicitly set fields.
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
//! # pub struct MyMessageSingleField1();
//! # pub struct MyMessageSingleField2<T, U>(T, U);
//! # pub struct MyMessageSingleField3<T>(T);
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
#![allow(incomplete_features)]
#![feature(backtrace)]
#![feature(generic_associated_types)]
#![feature(type_alias_impl_trait)]

mod common_traits;
pub mod desc;
mod error;
pub mod internal;
pub mod tags;

pub use self::common_traits::*;
pub use self::error::{ErrorKind, PuroroError};
pub type Result<T> = ::std::result::Result<T, PuroroError>;

// Re-exports
#[cfg(feature = "puroro-bumpalo")]
pub use ::bumpalo;
pub use ::either::Either;
pub use ::once_cell;
