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

use tests_pb::full_coverage3::MsgTrait;

use crate::tests_pb::full_coverage2::msg::Submsg as Submsg2;
use crate::tests_pb::full_coverage2::{Enum as Enum2, Msg as Msg2};
use crate::tests_pb::full_coverage3::msg::Submsg as Submsg3;
use crate::tests_pb::full_coverage3::{Enum as Enum3, Msg as Msg3};

#[test]
fn simple2_get_set_int32() {
    let mut msg = Msg2::new();
    assert_eq!(0, msg.i32_optional());
    assert_eq!(0, msg.i32_repeated().len());
    assert!(!msg.has_i32_optional());

    *msg.i32_optional_mut();
    assert_eq!(0, msg.i32_optional());
    assert!(msg.has_i32_optional());

    *msg.i32_optional_mut() = 10;
    msg.i32_repeated_mut().extend([30, 40].iter());
    assert_eq!(10, msg.i32_optional());
    assert_eq!(&[30, 40], msg.i32_repeated());
    assert!(msg.has_i32_optional());
}

#[test]
fn simple3_get_set_int32() {
    let mut msg = Msg3::new();
    assert_eq!(0, msg.i32_unlabeled());
    assert_eq!(0, msg.i32_optional());
    assert_eq!(0, msg.i32_repeated().len());
    assert!(!msg.has_i32_unlabeled());
    assert!(!msg.has_i32_optional());

    *msg.i32_optional_mut();
    assert_eq!(0, msg.i32_optional());
    assert!(msg.has_i32_optional());

    *msg.i32_optional_mut() = 10;
    *msg.i32_unlabeled_mut() = 20;
    msg.i32_repeated_mut().extend([30, 40].iter());
    assert_eq!(10, msg.i32_optional());
    assert_eq!(20, msg.i32_unlabeled());
    assert_eq!(&[30, 40], msg.i32_repeated());
    assert!(msg.has_i32_optional());
    assert!(msg.has_i32_unlabeled());
}
