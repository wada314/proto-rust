// A generated source code by puroro library
// package full_coverage3

pub mod _puroro_root {
    pub use super::super::_puroro_root::*;
}

pub use _puroro_impls::MsgSimple as Msg;
pub use _puroro_impls::SomeSimple as Some;
pub mod _puroro_impls {
    mod _puroro_root {
        pub use super::super::_puroro_root::*;
    }
    use super::_puroro_traits::*;
    #[derive(
        ::std::clone::Clone, ::std::default::Default, ::std::cmp::PartialEq, ::std::fmt::Debug,
    )]
    pub struct MsgSimple {
    pub i32_unlabeled: i32,
    pub i32_optional: ::std::option::Option<i32>,
    pub i32_repeated: ::std::vec::Vec<i32>,
    pub float_unlabeled: f32,
    pub float_optional: ::std::option::Option<f32>,
    pub float_repeated: ::std::vec::Vec<f32>,
    pub bytes_unlabeled: ::std::borrow::Cow<'static, [u8]>,
    pub bytes_optional: ::std::option::Option<::std::borrow::Cow<'static, [u8]>>,
    pub bytes_repeated: ::std::vec::Vec<::std::borrow::Cow<'static, [u8]>>,
    pub string_unlabeled: ::std::borrow::Cow<'static, str>,
    pub string_optional: ::std::option::Option<::std::borrow::Cow<'static, str>>,
    pub string_repeated: ::std::vec::Vec<::std::borrow::Cow<'static, str>>,
    pub enum_unlabeled: self::_puroro_root::full_coverage3::Enum,
    pub enum_optional: ::std::option::Option<self::_puroro_root::full_coverage3::Enum>,
    pub enum_repeated: ::std::vec::Vec<self::_puroro_root::full_coverage3::Enum>,
    pub submsg_unlabeled: ::std::option::Option<::std::boxed::Box<self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple>>,
    pub submsg_optional: ::std::option::Option<::std::boxed::Box<self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple>>,
    pub submsg_repeated: ::std::vec::Vec<self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple>,
    pub i64_unlabeled: i64,
    pub i64_optional: ::std::option::Option<i64>,
    pub i64_repeated: ::std::vec::Vec<i64>,
    pub u32_unlabeled: u32,
    pub u32_optional: ::std::option::Option<u32>,
    pub u32_repeated: ::std::vec::Vec<u32>,
    pub u64_unlabeled: u64,
    pub u64_optional: ::std::option::Option<u64>,
    pub u64_repeated: ::std::vec::Vec<u64>,
    pub s32_unlabeled: i32,
    pub s32_optional: ::std::option::Option<i32>,
    pub s32_repeated: ::std::vec::Vec<i32>,
    pub s64_unlabeled: i64,
    pub s64_optional: ::std::option::Option<i64>,
    pub s64_repeated: ::std::vec::Vec<i64>,
    pub fixed32_unlabeled: u32,
    pub fixed32_optional: ::std::option::Option<u32>,
    pub fixed32_repeated: ::std::vec::Vec<u32>,
    pub fixed64_unlabeled: u64,
    pub fixed64_optional: ::std::option::Option<u64>,
    pub fixed64_repeated: ::std::vec::Vec<u64>,
    pub sfixed32_unlabeled: i32,
    pub sfixed32_optional: ::std::option::Option<i32>,
    pub sfixed32_repeated: ::std::vec::Vec<i32>,
    pub sfixed64_unlabeled: i64,
    pub sfixed64_optional: ::std::option::Option<i64>,
    pub sfixed64_repeated: ::std::vec::Vec<i64>,
    pub f64_unlabeled: f64,
    pub f64_optional: ::std::option::Option<f64>,
    pub f64_repeated: ::std::vec::Vec<f64>,
}
    impl ::puroro::Message<MsgSimple> for MsgSimple {}

    impl MsgTrait for MsgSimple {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Clone::clone(&self.i32_unlabeled)
        }
        fn i32_optional<'this>(&'this self) -> Option<i32> {
            Clone::clone(&self.i32_optional)
        }
        type Field3RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, i32>>;

        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            self.i32_repeated.iter().cloned()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Clone::clone(&self.float_unlabeled)
        }
        fn float_optional<'this>(&'this self) -> Option<f32> {
            Clone::clone(&self.float_optional)
        }
        type Field13RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, f32>>;

        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            self.float_repeated.iter().cloned()
        }
        type Field21BytesType<'this> = &'this [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &self.bytes_unlabeled
        }
        type Field22BytesType<'this> = &'this [u8];
        fn bytes_optional<'this>(&'this self) -> Option<Self::Field22BytesType<'this>> {
            self.bytes_optional.as_ref().map(|v| v.as_ref())
        }
        type Field23BytesType<'this> = &'this [u8];
        type Field23RepeatedType<'this> = ::puroro::internal::impls::simple::BorrowedIter<
            [u8],
            ::std::slice::Iter<'this, ::std::borrow::Cow<'static, [u8]>>,
        >;

        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::simple::BorrowedIter::new(self.bytes_repeated.iter())
        }
        type Field31StringType<'this> = &'this str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            &self.string_unlabeled
        }
        type Field32StringType<'this> = &'this str;
        fn string_optional<'this>(&'this self) -> Option<Self::Field32StringType<'this>> {
            self.string_optional.as_ref().map(|v| v.as_ref())
        }
        type Field33StringType<'this> = &'this str;
        type Field33RepeatedType<'this> = ::puroro::internal::impls::simple::BorrowedIter<
            str,
            ::std::slice::Iter<'this, ::std::borrow::Cow<'static, str>>,
        >;

        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::simple::BorrowedIter::new(self.string_repeated.iter())
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Clone::clone(&self.enum_unlabeled)
        }
        fn enum_optional<'this>(&'this self) -> Option<self::_puroro_root::full_coverage3::Enum> {
            Clone::clone(&self.enum_optional)
        }
        type Field43RepeatedType<'this> = ::std::iter::Cloned<
            ::std::slice::Iter<'this, self::_puroro_root::full_coverage3::Enum>,
        >;

        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            self.enum_repeated.iter().cloned()
        }
        type Field51MessageType<'this> = &'this self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple;
        fn submsg_unlabeled<'this>(&'this self) -> Option<Self::Field51MessageType<'this>> {
            self.submsg_unlabeled.as_ref().map(|v| v.as_ref())
        }
        type Field52MessageType<'this> = &'this self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple;
        fn submsg_optional<'this>(&'this self) -> Option<Self::Field52MessageType<'this>> {
            self.submsg_optional.as_ref().map(|v| v.as_ref())
        }
        type Field53MessageType<'this> = &'this self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple;
        type Field53RepeatedType<'this> = ::puroro::internal::impls::simple::BorrowedIter<
    self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple,
    ::std::slice::Iter<'this, self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple>>;

        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::simple::BorrowedIter::new(self.submsg_repeated.iter())
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Clone::clone(&self.i64_unlabeled)
        }
        fn i64_optional<'this>(&'this self) -> Option<i64> {
            Clone::clone(&self.i64_optional)
        }
        type Field103RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, i64>>;

        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            self.i64_repeated.iter().cloned()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Clone::clone(&self.u32_unlabeled)
        }
        fn u32_optional<'this>(&'this self) -> Option<u32> {
            Clone::clone(&self.u32_optional)
        }
        type Field113RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, u32>>;

        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            self.u32_repeated.iter().cloned()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Clone::clone(&self.u64_unlabeled)
        }
        fn u64_optional<'this>(&'this self) -> Option<u64> {
            Clone::clone(&self.u64_optional)
        }
        type Field123RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, u64>>;

        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            self.u64_repeated.iter().cloned()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Clone::clone(&self.s32_unlabeled)
        }
        fn s32_optional<'this>(&'this self) -> Option<i32> {
            Clone::clone(&self.s32_optional)
        }
        type Field133RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, i32>>;

        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            self.s32_repeated.iter().cloned()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Clone::clone(&self.s64_unlabeled)
        }
        fn s64_optional<'this>(&'this self) -> Option<i64> {
            Clone::clone(&self.s64_optional)
        }
        type Field143RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, i64>>;

        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            self.s64_repeated.iter().cloned()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Clone::clone(&self.fixed32_unlabeled)
        }
        fn fixed32_optional<'this>(&'this self) -> Option<u32> {
            Clone::clone(&self.fixed32_optional)
        }
        type Field153RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, u32>>;

        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            self.fixed32_repeated.iter().cloned()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Clone::clone(&self.fixed64_unlabeled)
        }
        fn fixed64_optional<'this>(&'this self) -> Option<u64> {
            Clone::clone(&self.fixed64_optional)
        }
        type Field163RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, u64>>;

        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            self.fixed64_repeated.iter().cloned()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Clone::clone(&self.sfixed32_unlabeled)
        }
        fn sfixed32_optional<'this>(&'this self) -> Option<i32> {
            Clone::clone(&self.sfixed32_optional)
        }
        type Field173RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, i32>>;

        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            self.sfixed32_repeated.iter().cloned()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Clone::clone(&self.sfixed64_unlabeled)
        }
        fn sfixed64_optional<'this>(&'this self) -> Option<i64> {
            Clone::clone(&self.sfixed64_optional)
        }
        type Field183RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, i64>>;

        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            self.sfixed64_repeated.iter().cloned()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Clone::clone(&self.f64_unlabeled)
        }
        fn f64_optional<'this>(&'this self) -> Option<f64> {
            Clone::clone(&self.f64_optional)
        }
        type Field193RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, f64>>;

        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            self.f64_repeated.iter().cloned()
        }
    }

    impl ::puroro::MessageRepresentativeImpl for MsgSimple {
        fn descriptor() -> &'static ::puroro::desc::MessageDescriptor {
            use ::puroro::once_cell::sync::Lazy;
            static LAZY_FIELD_DESCRIPTOR_ARRAY: Lazy<[::puroro::desc::FieldDescriptor; 48]> =
                Lazy::new(|| {
                    [
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i32_unlabeled",
                                number: 1,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i32_optional",
                                number: 2,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i32_repeated",
                                number: 3,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "float_unlabeled",
                                number: 11,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "float_optional",
                                number: 12,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "float_repeated",
                                number: 13,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "bytes_unlabeled",
                                number: 21,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "bytes_optional",
                                number: 22,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "bytes_repeated",
                                number: 23,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "string_unlabeled",
                                number: 31,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "string_optional",
                                number: 32,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "string_repeated",
                                number: 33,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "enum_unlabeled",
                                number: 41,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "enum_optional",
                                number: 42,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "enum_repeated",
                                number: 43,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "submsg_unlabeled",
                                number: 51,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "submsg_optional",
                                number: 52,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "submsg_repeated",
                                number: 53,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i64_unlabeled",
                                number: 101,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i64_optional",
                                number: 102,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i64_repeated",
                                number: 103,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u32_unlabeled",
                                number: 111,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u32_optional",
                                number: 112,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u32_repeated",
                                number: 113,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u64_unlabeled",
                                number: 121,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u64_optional",
                                number: 122,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u64_repeated",
                                number: 123,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "s32_unlabeled",
                                number: 131,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "s32_optional",
                                number: 132,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "s32_repeated",
                                number: 133,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "s64_unlabeled",
                                number: 141,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "s64_optional",
                                number: 142,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "s64_repeated",
                                number: 143,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "fixed32_unlabeled",
                                number: 151,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "fixed32_optional",
                                number: 152,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "fixed32_repeated",
                                number: 153,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "fixed64_unlabeled",
                                number: 161,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "fixed64_optional",
                                number: 162,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "fixed64_repeated",
                                number: 163,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "sfixed32_unlabeled",
                                number: 171,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "sfixed32_optional",
                                number: 172,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "sfixed32_repeated",
                                number: 173,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "sfixed64_unlabeled",
                                number: 181,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "sfixed64_optional",
                                number: 182,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "sfixed64_repeated",
                                number: 183,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "f64_unlabeled",
                                number: 191,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "f64_optional",
                                number: 192,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "f64_repeated",
                                number: 193,
                                lazy_containing_type: Lazy::new(|| {
                                    <MsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                    ]
                });
            static LAZY_DESCRIPTOR: Lazy<::puroro::desc::MessageDescriptor> = Lazy::new(|| {
                let init = ::puroro::internal::MessageDescriptorInitializer {
                    name: "Msg",
                    lazy_fields: Lazy::new(|| Lazy::force(&LAZY_FIELD_DESCRIPTOR_ARRAY).as_ref()),
                };
                ::puroro::internal::init_message_descriptor(init)
            });
            Lazy::force(&LAZY_DESCRIPTOR)
        }
    }

    impl ::puroro::DeserFromBytesIter for MsgSimple {
        fn deser<I>(&mut self, iter: I) -> ::puroro::Result<()>
        where
            I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>,
        {
            ::puroro::internal::de::from_iter::deser_from_iter(self, iter)
        }
    }

    impl ::puroro::internal::de::DeserFieldsFromBytesIter for MsgSimple {
        fn deser_field<I>(
            &mut self,
            field_number: i32,
            data: ::puroro::types::FieldData<&mut ::puroro::internal::de::from_iter::ScopedIter<I>>,
        ) -> ::puroro::Result<()>
        where
            I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>,
        {
            use ::puroro::internal::impls::simple::de::DeserFieldFromBytesIter;
            match field_number {
            1 => DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::Int32
            >::deser_field(&mut self.i32_unlabeled, data),
            2 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int32
            >::deser_field(&mut self.i32_optional, data),
            3 => DeserFieldFromBytesIter::<
                ::puroro::tags::Repeated, ::puroro::tags::Int32
            >::deser_field(&mut self.i32_repeated, data),
            11 => DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::Float
            >::deser_field(&mut self.float_unlabeled, data),
            12 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Float
            >::deser_field(&mut self.float_optional, data),
            13 => DeserFieldFromBytesIter::<
                ::puroro::tags::Repeated, ::puroro::tags::Float
            >::deser_field(&mut self.float_repeated, data),
            21 => DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::Bytes
            >::deser_field(&mut self.bytes_unlabeled, data),
            22 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Bytes
            >::deser_field(&mut self.bytes_optional, data),
            23 => DeserFieldFromBytesIter::<
                ::puroro::tags::Repeated, ::puroro::tags::Bytes
            >::deser_field(&mut self.bytes_repeated, data),
            31 => DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::String
            >::deser_field(&mut self.string_unlabeled, data),
            32 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::String
            >::deser_field(&mut self.string_optional, data),
            33 => DeserFieldFromBytesIter::<
                ::puroro::tags::Repeated, ::puroro::tags::String
            >::deser_field(&mut self.string_repeated, data),
            41 => DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::Enum3<self::_puroro_root::full_coverage3::Enum>
            >::deser_field(&mut self.enum_unlabeled, data),
            42 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Enum3<self::_puroro_root::full_coverage3::Enum>
            >::deser_field(&mut self.enum_optional, data),
            43 => DeserFieldFromBytesIter::<
                ::puroro::tags::Repeated, ::puroro::tags::Enum3<self::_puroro_root::full_coverage3::Enum>
            >::deser_field(&mut self.enum_repeated, data),
            51 => DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::Message<self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple>
            >::deser_field(&mut self.submsg_unlabeled, data),
            52 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Message<self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple>
            >::deser_field(&mut self.submsg_optional, data),
            53 => DeserFieldFromBytesIter::<
                ::puroro::tags::Repeated, ::puroro::tags::Message<self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple>
            >::deser_field(&mut self.submsg_repeated, data),
            101 => DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::Int64
            >::deser_field(&mut self.i64_unlabeled, data),
            102 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int64
            >::deser_field(&mut self.i64_optional, data),
            103 => DeserFieldFromBytesIter::<
                ::puroro::tags::Repeated, ::puroro::tags::Int64
            >::deser_field(&mut self.i64_repeated, data),
            111 => DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::UInt32
            >::deser_field(&mut self.u32_unlabeled, data),
            112 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::UInt32
            >::deser_field(&mut self.u32_optional, data),
            113 => DeserFieldFromBytesIter::<
                ::puroro::tags::Repeated, ::puroro::tags::UInt32
            >::deser_field(&mut self.u32_repeated, data),
            121 => DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::UInt64
            >::deser_field(&mut self.u64_unlabeled, data),
            122 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::UInt64
            >::deser_field(&mut self.u64_optional, data),
            123 => DeserFieldFromBytesIter::<
                ::puroro::tags::Repeated, ::puroro::tags::UInt64
            >::deser_field(&mut self.u64_repeated, data),
            131 => DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::SInt32
            >::deser_field(&mut self.s32_unlabeled, data),
            132 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::SInt32
            >::deser_field(&mut self.s32_optional, data),
            133 => DeserFieldFromBytesIter::<
                ::puroro::tags::Repeated, ::puroro::tags::SInt32
            >::deser_field(&mut self.s32_repeated, data),
            141 => DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::SInt64
            >::deser_field(&mut self.s64_unlabeled, data),
            142 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::SInt64
            >::deser_field(&mut self.s64_optional, data),
            143 => DeserFieldFromBytesIter::<
                ::puroro::tags::Repeated, ::puroro::tags::SInt64
            >::deser_field(&mut self.s64_repeated, data),
            151 => DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::Fixed32
            >::deser_field(&mut self.fixed32_unlabeled, data),
            152 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Fixed32
            >::deser_field(&mut self.fixed32_optional, data),
            153 => DeserFieldFromBytesIter::<
                ::puroro::tags::Repeated, ::puroro::tags::Fixed32
            >::deser_field(&mut self.fixed32_repeated, data),
            161 => DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::Fixed64
            >::deser_field(&mut self.fixed64_unlabeled, data),
            162 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Fixed64
            >::deser_field(&mut self.fixed64_optional, data),
            163 => DeserFieldFromBytesIter::<
                ::puroro::tags::Repeated, ::puroro::tags::Fixed64
            >::deser_field(&mut self.fixed64_repeated, data),
            171 => DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::SFixed32
            >::deser_field(&mut self.sfixed32_unlabeled, data),
            172 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::SFixed32
            >::deser_field(&mut self.sfixed32_optional, data),
            173 => DeserFieldFromBytesIter::<
                ::puroro::tags::Repeated, ::puroro::tags::SFixed32
            >::deser_field(&mut self.sfixed32_repeated, data),
            181 => DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::SFixed64
            >::deser_field(&mut self.sfixed64_unlabeled, data),
            182 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::SFixed64
            >::deser_field(&mut self.sfixed64_optional, data),
            183 => DeserFieldFromBytesIter::<
                ::puroro::tags::Repeated, ::puroro::tags::SFixed64
            >::deser_field(&mut self.sfixed64_repeated, data),
            191 => DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::Double
            >::deser_field(&mut self.f64_unlabeled, data),
            192 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Double
            >::deser_field(&mut self.f64_optional, data),
            193 => DeserFieldFromBytesIter::<
                ::puroro::tags::Repeated, ::puroro::tags::Double
            >::deser_field(&mut self.f64_repeated, data),

            _ => unimplemented!("TODO: This case should be handled properly..."),
        }
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimple {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::Int32>::ser_field(
                &self.i32_unlabeled,
                1,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field(
                &self.i32_optional,
                2,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::Int32>::ser_field(
                &self.i32_repeated,
                3,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::Float>::ser_field(
                &self.float_unlabeled,
                11,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field(
                &self.float_optional,
                12,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::Float>::ser_field(
                &self.float_repeated,
                13,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::Bytes>::ser_field(
                &self.bytes_unlabeled,
                21,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bytes>::ser_field(
                &self.bytes_optional,
                22,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::Bytes>::ser_field(
                &self.bytes_repeated,
                23,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::String>::ser_field(
                &self.string_unlabeled,
                31,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::String>::ser_field(
                &self.string_optional,
                32,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::String>::ser_field(
                &self.string_repeated,
                33,
                out,
            )?;
            SerFieldToIoWrite::<
                ::puroro::tags::Unlabeled,
                ::puroro::tags::Enum3<self::_puroro_root::full_coverage3::Enum>,
            >::ser_field(&self.enum_unlabeled, 41, out)?;
            SerFieldToIoWrite::<
                ::puroro::tags::Optional,
                ::puroro::tags::Enum3<self::_puroro_root::full_coverage3::Enum>,
            >::ser_field(&self.enum_optional, 42, out)?;
            SerFieldToIoWrite::<
                ::puroro::tags::Repeated,
                ::puroro::tags::Enum3<self::_puroro_root::full_coverage3::Enum>,
            >::ser_field(&self.enum_repeated, 43, out)?;
            SerFieldToIoWrite::<
            ::puroro::tags::Unlabeled, ::puroro::tags::Message<self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple>
        >::ser_field(&self.submsg_unlabeled, 51, out)?;
            SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Message<self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple>
        >::ser_field(&self.submsg_optional, 52, out)?;
            SerFieldToIoWrite::<
            ::puroro::tags::Repeated, ::puroro::tags::Message<self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple>
        >::ser_field(&self.submsg_repeated, 53, out)?;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::Int64>::ser_field(
                &self.i64_unlabeled,
                101,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field(
                &self.i64_optional,
                102,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::Int64>::ser_field(
                &self.i64_repeated,
                103,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::UInt32>::ser_field(
                &self.u32_unlabeled,
                111,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt32>::ser_field(
                &self.u32_optional,
                112,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::UInt32>::ser_field(
                &self.u32_repeated,
                113,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::UInt64>::ser_field(
                &self.u64_unlabeled,
                121,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt64>::ser_field(
                &self.u64_optional,
                122,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::UInt64>::ser_field(
                &self.u64_repeated,
                123,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::SInt32>::ser_field(
                &self.s32_unlabeled,
                131,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::SInt32>::ser_field(
                &self.s32_optional,
                132,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::SInt32>::ser_field(
                &self.s32_repeated,
                133,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::SInt64>::ser_field(
                &self.s64_unlabeled,
                141,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::SInt64>::ser_field(
                &self.s64_optional,
                142,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::SInt64>::ser_field(
                &self.s64_repeated,
                143,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::Fixed32>::ser_field(
                &self.fixed32_unlabeled,
                151,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Fixed32>::ser_field(
                &self.fixed32_optional,
                152,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::Fixed32>::ser_field(
                &self.fixed32_repeated,
                153,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::Fixed64>::ser_field(
                &self.fixed64_unlabeled,
                161,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Fixed64>::ser_field(
                &self.fixed64_optional,
                162,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::Fixed64>::ser_field(
                &self.fixed64_repeated,
                163,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::SFixed32>::ser_field(
                &self.sfixed32_unlabeled,
                171,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::SFixed32>::ser_field(
                &self.sfixed32_optional,
                172,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::SFixed32>::ser_field(
                &self.sfixed32_repeated,
                173,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::SFixed64>::ser_field(
                &self.sfixed64_unlabeled,
                181,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::SFixed64>::ser_field(
                &self.sfixed64_optional,
                182,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::SFixed64>::ser_field(
                &self.sfixed64_repeated,
                183,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::Double>::ser_field(
                &self.f64_unlabeled,
                191,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Double>::ser_field(
                &self.f64_optional,
                192,
                out,
            )?;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::Double>::ser_field(
                &self.f64_repeated,
                193,
                out,
            )?;

            ::std::result::Result::Ok(())
        }
    }
    impl MsgTrait for () {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }
    impl<T, U> MsgTrait for (T, U)
    where
        T: MsgTrait,
        U: MsgTrait,
    {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            let right = <U as MsgTrait>::i32_unlabeled(&self.1);
            if right != ::std::default::Default::default() {
                right
            } else {
                <T as MsgTrait>::i32_unlabeled(&self.0)
            }
        }
        fn i32_optional<'this>(&'this self) -> Option<i32> {
            <U as MsgTrait>::i32_optional(&self.1)
                .or_else(|| <T as MsgTrait>::i32_optional(&self.0))
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::merged::MergedRepeatedField<
            <T as MsgTrait>::Field3RepeatedType<'this>,
            <U as MsgTrait>::Field3RepeatedType<'this>,
        >;

        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::merged::MergedRepeatedField::new(
                <T as MsgTrait>::i32_repeated(&self.0),
                <U as MsgTrait>::i32_repeated(&self.1),
            )
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            let right = <U as MsgTrait>::float_unlabeled(&self.1);
            if right != ::std::default::Default::default() {
                right
            } else {
                <T as MsgTrait>::float_unlabeled(&self.0)
            }
        }
        fn float_optional<'this>(&'this self) -> Option<f32> {
            <U as MsgTrait>::float_optional(&self.1)
                .or_else(|| <T as MsgTrait>::float_optional(&self.0))
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::merged::MergedRepeatedField<
            <T as MsgTrait>::Field13RepeatedType<'this>,
            <U as MsgTrait>::Field13RepeatedType<'this>,
        >;

        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::merged::MergedRepeatedField::new(
                <T as MsgTrait>::float_repeated(&self.0),
                <U as MsgTrait>::float_repeated(&self.1),
            )
        }
        type Field21BytesType<'this> = ::puroro::Either<
            <T as MsgTrait>::Field21BytesType<'this>,
            <U as MsgTrait>::Field21BytesType<'this>,
        >;
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            let right = <U as MsgTrait>::bytes_unlabeled(&self.1);
            if !right.is_empty() {
                ::puroro::Either::Right(right)
            } else {
                ::puroro::Either::Left(<T as MsgTrait>::bytes_unlabeled(&self.0))
            }
        }
        type Field22BytesType<'this> = ::puroro::Either<
            <T as MsgTrait>::Field22BytesType<'this>,
            <U as MsgTrait>::Field22BytesType<'this>,
        >;
        fn bytes_optional<'this>(&'this self) -> Option<Self::Field22BytesType<'this>> {
            if let Some(right) = <U as MsgTrait>::bytes_optional(&self.1) {
                Some(::puroro::Either::Right(right))
            } else if let Some(left) = <T as MsgTrait>::bytes_optional(&self.0) {
                Some(::puroro::Either::Left(left))
            } else {
                None
            }
        }
        type Field23BytesType<'this> = ::puroro::Either<
            <T as MsgTrait>::Field23BytesType<'this>,
            <U as MsgTrait>::Field23BytesType<'this>,
        >;
        type Field23RepeatedType<'this> = ::puroro::internal::impls::merged::MergedRepeatedLDField<
            <T as MsgTrait>::Field23RepeatedType<'this>,
            <U as MsgTrait>::Field23RepeatedType<'this>,
        >;

        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::merged::MergedRepeatedLDField::new(
                <T as MsgTrait>::bytes_repeated(&self.0),
                <U as MsgTrait>::bytes_repeated(&self.1),
            )
        }
        type Field31StringType<'this> = ::puroro::Either<
            <T as MsgTrait>::Field31StringType<'this>,
            <U as MsgTrait>::Field31StringType<'this>,
        >;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            let right = <U as MsgTrait>::string_unlabeled(&self.1);
            if !right.is_empty() {
                ::puroro::Either::Right(right)
            } else {
                ::puroro::Either::Left(<T as MsgTrait>::string_unlabeled(&self.0))
            }
        }
        type Field32StringType<'this> = ::puroro::Either<
            <T as MsgTrait>::Field32StringType<'this>,
            <U as MsgTrait>::Field32StringType<'this>,
        >;
        fn string_optional<'this>(&'this self) -> Option<Self::Field32StringType<'this>> {
            if let Some(right) = <U as MsgTrait>::string_optional(&self.1) {
                Some(::puroro::Either::Right(right))
            } else if let Some(left) = <T as MsgTrait>::string_optional(&self.0) {
                Some(::puroro::Either::Left(left))
            } else {
                None
            }
        }
        type Field33StringType<'this> = ::puroro::Either<
            <T as MsgTrait>::Field33StringType<'this>,
            <U as MsgTrait>::Field33StringType<'this>,
        >;
        type Field33RepeatedType<'this> = ::puroro::internal::impls::merged::MergedRepeatedLDField<
            <T as MsgTrait>::Field33RepeatedType<'this>,
            <U as MsgTrait>::Field33RepeatedType<'this>,
        >;

        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::merged::MergedRepeatedLDField::new(
                <T as MsgTrait>::string_repeated(&self.0),
                <U as MsgTrait>::string_repeated(&self.1),
            )
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            let right = <U as MsgTrait>::enum_unlabeled(&self.1);
            if right != ::std::default::Default::default() {
                right
            } else {
                <T as MsgTrait>::enum_unlabeled(&self.0)
            }
        }
        fn enum_optional<'this>(&'this self) -> Option<self::_puroro_root::full_coverage3::Enum> {
            <U as MsgTrait>::enum_optional(&self.1)
                .or_else(|| <T as MsgTrait>::enum_optional(&self.0))
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::merged::MergedRepeatedField<
            <T as MsgTrait>::Field43RepeatedType<'this>,
            <U as MsgTrait>::Field43RepeatedType<'this>,
        >;

        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::merged::MergedRepeatedField::new(
                <T as MsgTrait>::enum_repeated(&self.0),
                <U as MsgTrait>::enum_repeated(&self.1),
            )
        }
        type Field51MessageType<'this> = ::puroro::Either<
            ::puroro::Either<
                <T as MsgTrait>::Field51MessageType<'this>,
                <U as MsgTrait>::Field51MessageType<'this>,
            >,
            (
                <T as MsgTrait>::Field51MessageType<'this>,
                <U as MsgTrait>::Field51MessageType<'this>,
            ),
        >;
        fn submsg_unlabeled<'this>(&'this self) -> Option<Self::Field51MessageType<'this>> {
            match (
                <T as MsgTrait>::submsg_unlabeled(&self.0),
                <U as MsgTrait>::submsg_unlabeled(&self.1),
            ) {
                (None, None) => None,
                (Some(t), None) => Some(::puroro::Either::Left(::puroro::Either::Left(t))),
                (None, Some(u)) => Some(::puroro::Either::Left(::puroro::Either::Right(u))),
                (Some(t), Some(u)) => Some(::puroro::Either::Right((t, u))),
            }
        }
        type Field52MessageType<'this> = ::puroro::Either<
            ::puroro::Either<
                <T as MsgTrait>::Field52MessageType<'this>,
                <U as MsgTrait>::Field52MessageType<'this>,
            >,
            (
                <T as MsgTrait>::Field52MessageType<'this>,
                <U as MsgTrait>::Field52MessageType<'this>,
            ),
        >;
        fn submsg_optional<'this>(&'this self) -> Option<Self::Field52MessageType<'this>> {
            match (
                <T as MsgTrait>::submsg_optional(&self.0),
                <U as MsgTrait>::submsg_optional(&self.1),
            ) {
                (None, None) => None,
                (Some(t), None) => Some(::puroro::Either::Left(::puroro::Either::Left(t))),
                (None, Some(u)) => Some(::puroro::Either::Left(::puroro::Either::Right(u))),
                (Some(t), Some(u)) => Some(::puroro::Either::Right((t, u))),
            }
        }
        type Field53MessageType<'this> = ::puroro::Either<
            <T as MsgTrait>::Field53MessageType<'this>,
            <U as MsgTrait>::Field53MessageType<'this>,
        >;
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::merged::MergedRepeatedMessageField<
                <T as MsgTrait>::Field53RepeatedType<'this>,
                <U as MsgTrait>::Field53RepeatedType<'this>,
            >;

        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::merged::MergedRepeatedMessageField::new(
                <T as MsgTrait>::submsg_repeated(&self.0),
                <U as MsgTrait>::submsg_repeated(&self.1),
            )
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            let right = <U as MsgTrait>::i64_unlabeled(&self.1);
            if right != ::std::default::Default::default() {
                right
            } else {
                <T as MsgTrait>::i64_unlabeled(&self.0)
            }
        }
        fn i64_optional<'this>(&'this self) -> Option<i64> {
            <U as MsgTrait>::i64_optional(&self.1)
                .or_else(|| <T as MsgTrait>::i64_optional(&self.0))
        }
        type Field103RepeatedType<'this> = ::puroro::internal::impls::merged::MergedRepeatedField<
            <T as MsgTrait>::Field103RepeatedType<'this>,
            <U as MsgTrait>::Field103RepeatedType<'this>,
        >;

        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::merged::MergedRepeatedField::new(
                <T as MsgTrait>::i64_repeated(&self.0),
                <U as MsgTrait>::i64_repeated(&self.1),
            )
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            let right = <U as MsgTrait>::u32_unlabeled(&self.1);
            if right != ::std::default::Default::default() {
                right
            } else {
                <T as MsgTrait>::u32_unlabeled(&self.0)
            }
        }
        fn u32_optional<'this>(&'this self) -> Option<u32> {
            <U as MsgTrait>::u32_optional(&self.1)
                .or_else(|| <T as MsgTrait>::u32_optional(&self.0))
        }
        type Field113RepeatedType<'this> = ::puroro::internal::impls::merged::MergedRepeatedField<
            <T as MsgTrait>::Field113RepeatedType<'this>,
            <U as MsgTrait>::Field113RepeatedType<'this>,
        >;

        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::merged::MergedRepeatedField::new(
                <T as MsgTrait>::u32_repeated(&self.0),
                <U as MsgTrait>::u32_repeated(&self.1),
            )
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            let right = <U as MsgTrait>::u64_unlabeled(&self.1);
            if right != ::std::default::Default::default() {
                right
            } else {
                <T as MsgTrait>::u64_unlabeled(&self.0)
            }
        }
        fn u64_optional<'this>(&'this self) -> Option<u64> {
            <U as MsgTrait>::u64_optional(&self.1)
                .or_else(|| <T as MsgTrait>::u64_optional(&self.0))
        }
        type Field123RepeatedType<'this> = ::puroro::internal::impls::merged::MergedRepeatedField<
            <T as MsgTrait>::Field123RepeatedType<'this>,
            <U as MsgTrait>::Field123RepeatedType<'this>,
        >;

        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::merged::MergedRepeatedField::new(
                <T as MsgTrait>::u64_repeated(&self.0),
                <U as MsgTrait>::u64_repeated(&self.1),
            )
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            let right = <U as MsgTrait>::s32_unlabeled(&self.1);
            if right != ::std::default::Default::default() {
                right
            } else {
                <T as MsgTrait>::s32_unlabeled(&self.0)
            }
        }
        fn s32_optional<'this>(&'this self) -> Option<i32> {
            <U as MsgTrait>::s32_optional(&self.1)
                .or_else(|| <T as MsgTrait>::s32_optional(&self.0))
        }
        type Field133RepeatedType<'this> = ::puroro::internal::impls::merged::MergedRepeatedField<
            <T as MsgTrait>::Field133RepeatedType<'this>,
            <U as MsgTrait>::Field133RepeatedType<'this>,
        >;

        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::merged::MergedRepeatedField::new(
                <T as MsgTrait>::s32_repeated(&self.0),
                <U as MsgTrait>::s32_repeated(&self.1),
            )
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            let right = <U as MsgTrait>::s64_unlabeled(&self.1);
            if right != ::std::default::Default::default() {
                right
            } else {
                <T as MsgTrait>::s64_unlabeled(&self.0)
            }
        }
        fn s64_optional<'this>(&'this self) -> Option<i64> {
            <U as MsgTrait>::s64_optional(&self.1)
                .or_else(|| <T as MsgTrait>::s64_optional(&self.0))
        }
        type Field143RepeatedType<'this> = ::puroro::internal::impls::merged::MergedRepeatedField<
            <T as MsgTrait>::Field143RepeatedType<'this>,
            <U as MsgTrait>::Field143RepeatedType<'this>,
        >;

        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::merged::MergedRepeatedField::new(
                <T as MsgTrait>::s64_repeated(&self.0),
                <U as MsgTrait>::s64_repeated(&self.1),
            )
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            let right = <U as MsgTrait>::fixed32_unlabeled(&self.1);
            if right != ::std::default::Default::default() {
                right
            } else {
                <T as MsgTrait>::fixed32_unlabeled(&self.0)
            }
        }
        fn fixed32_optional<'this>(&'this self) -> Option<u32> {
            <U as MsgTrait>::fixed32_optional(&self.1)
                .or_else(|| <T as MsgTrait>::fixed32_optional(&self.0))
        }
        type Field153RepeatedType<'this> = ::puroro::internal::impls::merged::MergedRepeatedField<
            <T as MsgTrait>::Field153RepeatedType<'this>,
            <U as MsgTrait>::Field153RepeatedType<'this>,
        >;

        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::merged::MergedRepeatedField::new(
                <T as MsgTrait>::fixed32_repeated(&self.0),
                <U as MsgTrait>::fixed32_repeated(&self.1),
            )
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            let right = <U as MsgTrait>::fixed64_unlabeled(&self.1);
            if right != ::std::default::Default::default() {
                right
            } else {
                <T as MsgTrait>::fixed64_unlabeled(&self.0)
            }
        }
        fn fixed64_optional<'this>(&'this self) -> Option<u64> {
            <U as MsgTrait>::fixed64_optional(&self.1)
                .or_else(|| <T as MsgTrait>::fixed64_optional(&self.0))
        }
        type Field163RepeatedType<'this> = ::puroro::internal::impls::merged::MergedRepeatedField<
            <T as MsgTrait>::Field163RepeatedType<'this>,
            <U as MsgTrait>::Field163RepeatedType<'this>,
        >;

        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::merged::MergedRepeatedField::new(
                <T as MsgTrait>::fixed64_repeated(&self.0),
                <U as MsgTrait>::fixed64_repeated(&self.1),
            )
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            let right = <U as MsgTrait>::sfixed32_unlabeled(&self.1);
            if right != ::std::default::Default::default() {
                right
            } else {
                <T as MsgTrait>::sfixed32_unlabeled(&self.0)
            }
        }
        fn sfixed32_optional<'this>(&'this self) -> Option<i32> {
            <U as MsgTrait>::sfixed32_optional(&self.1)
                .or_else(|| <T as MsgTrait>::sfixed32_optional(&self.0))
        }
        type Field173RepeatedType<'this> = ::puroro::internal::impls::merged::MergedRepeatedField<
            <T as MsgTrait>::Field173RepeatedType<'this>,
            <U as MsgTrait>::Field173RepeatedType<'this>,
        >;

        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::merged::MergedRepeatedField::new(
                <T as MsgTrait>::sfixed32_repeated(&self.0),
                <U as MsgTrait>::sfixed32_repeated(&self.1),
            )
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            let right = <U as MsgTrait>::sfixed64_unlabeled(&self.1);
            if right != ::std::default::Default::default() {
                right
            } else {
                <T as MsgTrait>::sfixed64_unlabeled(&self.0)
            }
        }
        fn sfixed64_optional<'this>(&'this self) -> Option<i64> {
            <U as MsgTrait>::sfixed64_optional(&self.1)
                .or_else(|| <T as MsgTrait>::sfixed64_optional(&self.0))
        }
        type Field183RepeatedType<'this> = ::puroro::internal::impls::merged::MergedRepeatedField<
            <T as MsgTrait>::Field183RepeatedType<'this>,
            <U as MsgTrait>::Field183RepeatedType<'this>,
        >;

        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::merged::MergedRepeatedField::new(
                <T as MsgTrait>::sfixed64_repeated(&self.0),
                <U as MsgTrait>::sfixed64_repeated(&self.1),
            )
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            let right = <U as MsgTrait>::f64_unlabeled(&self.1);
            if right != ::std::default::Default::default() {
                right
            } else {
                <T as MsgTrait>::f64_unlabeled(&self.0)
            }
        }
        fn f64_optional<'this>(&'this self) -> Option<f64> {
            <U as MsgTrait>::f64_optional(&self.1)
                .or_else(|| <T as MsgTrait>::f64_optional(&self.0))
        }
        type Field193RepeatedType<'this> = ::puroro::internal::impls::merged::MergedRepeatedField<
            <T as MsgTrait>::Field193RepeatedType<'this>,
            <U as MsgTrait>::Field193RepeatedType<'this>,
        >;

        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::merged::MergedRepeatedField::new(
                <T as MsgTrait>::f64_repeated(&self.0),
                <U as MsgTrait>::f64_repeated(&self.1),
            )
        }
    }
    impl<T, U> MsgTrait for ::puroro::Either<T, U>
    where
        T: MsgTrait,
        U: MsgTrait,
    {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_unlabeled(t),
                |u| <U as MsgTrait>::i32_unlabeled(u),
            )
        }
        fn i32_optional<'this>(&'this self) -> Option<i32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_optional(t),
                |u| <U as MsgTrait>::i32_optional(u),
            )
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::either::EitherRepeatedField<
            <T as MsgTrait>::Field3RepeatedType<'this>,
            <U as MsgTrait>::Field3RepeatedType<'this>,
        >;

        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::either::EitherRepeatedField::new(
                self.as_ref()
                    .map_left(|t| <T as MsgTrait>::i32_repeated(t))
                    .map_right(|u| <U as MsgTrait>::i32_repeated(u)),
            )
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            self.as_ref().either(
                |t| <T as MsgTrait>::float_unlabeled(t),
                |u| <U as MsgTrait>::float_unlabeled(u),
            )
        }
        fn float_optional<'this>(&'this self) -> Option<f32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::float_optional(t),
                |u| <U as MsgTrait>::float_optional(u),
            )
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::either::EitherRepeatedField<
            <T as MsgTrait>::Field13RepeatedType<'this>,
            <U as MsgTrait>::Field13RepeatedType<'this>,
        >;

        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::either::EitherRepeatedField::new(
                self.as_ref()
                    .map_left(|t| <T as MsgTrait>::float_repeated(t))
                    .map_right(|u| <U as MsgTrait>::float_repeated(u)),
            )
        }
        type Field21BytesType<'this> = ::puroro::Either<
            <T as MsgTrait>::Field21BytesType<'this>,
            <U as MsgTrait>::Field21BytesType<'this>,
        >;
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            self.as_ref().either(
                |t| ::puroro::Either::Left(<T as MsgTrait>::bytes_unlabeled(t)),
                |u| ::puroro::Either::Right(<U as MsgTrait>::bytes_unlabeled(u)),
            )
        }
        type Field22BytesType<'this> = ::puroro::Either<
            <T as MsgTrait>::Field22BytesType<'this>,
            <U as MsgTrait>::Field22BytesType<'this>,
        >;
        fn bytes_optional<'this>(&'this self) -> Option<Self::Field22BytesType<'this>> {
            self.as_ref().either(
                |t| <T as MsgTrait>::bytes_optional(t).map(|t| ::puroro::Either::Left(t)),
                |u| <U as MsgTrait>::bytes_optional(u).map(|u| ::puroro::Either::Right(u)),
            )
        }
        type Field23BytesType<'this> = ::puroro::Either<
            <T as MsgTrait>::Field23BytesType<'this>,
            <U as MsgTrait>::Field23BytesType<'this>,
        >;
        type Field23RepeatedType<'this> = ::puroro::internal::impls::either::EitherRepeatedLDField<
            <T as MsgTrait>::Field23RepeatedType<'this>,
            <U as MsgTrait>::Field23RepeatedType<'this>,
        >;

        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::either::EitherRepeatedLDField::new(
                self.as_ref()
                    .map_left(|t| <T as MsgTrait>::bytes_repeated(t))
                    .map_right(|u| <U as MsgTrait>::bytes_repeated(u)),
            )
        }
        type Field31StringType<'this> = ::puroro::Either<
            <T as MsgTrait>::Field31StringType<'this>,
            <U as MsgTrait>::Field31StringType<'this>,
        >;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            self.as_ref().either(
                |t| ::puroro::Either::Left(<T as MsgTrait>::string_unlabeled(t)),
                |u| ::puroro::Either::Right(<U as MsgTrait>::string_unlabeled(u)),
            )
        }
        type Field32StringType<'this> = ::puroro::Either<
            <T as MsgTrait>::Field32StringType<'this>,
            <U as MsgTrait>::Field32StringType<'this>,
        >;
        fn string_optional<'this>(&'this self) -> Option<Self::Field32StringType<'this>> {
            self.as_ref().either(
                |t| <T as MsgTrait>::string_optional(t).map(|t| ::puroro::Either::Left(t)),
                |u| <U as MsgTrait>::string_optional(u).map(|u| ::puroro::Either::Right(u)),
            )
        }
        type Field33StringType<'this> = ::puroro::Either<
            <T as MsgTrait>::Field33StringType<'this>,
            <U as MsgTrait>::Field33StringType<'this>,
        >;
        type Field33RepeatedType<'this> = ::puroro::internal::impls::either::EitherRepeatedLDField<
            <T as MsgTrait>::Field33RepeatedType<'this>,
            <U as MsgTrait>::Field33RepeatedType<'this>,
        >;

        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::either::EitherRepeatedLDField::new(
                self.as_ref()
                    .map_left(|t| <T as MsgTrait>::string_repeated(t))
                    .map_right(|u| <U as MsgTrait>::string_repeated(u)),
            )
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            self.as_ref().either(
                |t| <T as MsgTrait>::enum_unlabeled(t),
                |u| <U as MsgTrait>::enum_unlabeled(u),
            )
        }
        fn enum_optional<'this>(&'this self) -> Option<self::_puroro_root::full_coverage3::Enum> {
            self.as_ref().either(
                |t| <T as MsgTrait>::enum_optional(t),
                |u| <U as MsgTrait>::enum_optional(u),
            )
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::either::EitherRepeatedField<
            <T as MsgTrait>::Field43RepeatedType<'this>,
            <U as MsgTrait>::Field43RepeatedType<'this>,
        >;

        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::either::EitherRepeatedField::new(
                self.as_ref()
                    .map_left(|t| <T as MsgTrait>::enum_repeated(t))
                    .map_right(|u| <U as MsgTrait>::enum_repeated(u)),
            )
        }
        type Field51MessageType<'this> = ::puroro::Either<
            <T as MsgTrait>::Field51MessageType<'this>,
            <U as MsgTrait>::Field51MessageType<'this>,
        >;
        fn submsg_unlabeled<'this>(&'this self) -> Option<Self::Field51MessageType<'this>> {
            self.as_ref().either(
                |t| <T as MsgTrait>::submsg_unlabeled(t).map(|t| ::puroro::Either::Left(t)),
                |u| <U as MsgTrait>::submsg_unlabeled(u).map(|u| ::puroro::Either::Right(u)),
            )
        }
        type Field52MessageType<'this> = ::puroro::Either<
            <T as MsgTrait>::Field52MessageType<'this>,
            <U as MsgTrait>::Field52MessageType<'this>,
        >;
        fn submsg_optional<'this>(&'this self) -> Option<Self::Field52MessageType<'this>> {
            self.as_ref().either(
                |t| <T as MsgTrait>::submsg_optional(t).map(|t| ::puroro::Either::Left(t)),
                |u| <U as MsgTrait>::submsg_optional(u).map(|u| ::puroro::Either::Right(u)),
            )
        }
        type Field53MessageType<'this> = ::puroro::Either<
            <T as MsgTrait>::Field53MessageType<'this>,
            <U as MsgTrait>::Field53MessageType<'this>,
        >;
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::either::EitherRepeatedMessageField<
                <T as MsgTrait>::Field53RepeatedType<'this>,
                <U as MsgTrait>::Field53RepeatedType<'this>,
            >;

        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::either::EitherRepeatedMessageField::new(
                self.as_ref()
                    .map_left(|t| <T as MsgTrait>::submsg_repeated(t))
                    .map_right(|u| <U as MsgTrait>::submsg_repeated(u)),
            )
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_unlabeled(t),
                |u| <U as MsgTrait>::i64_unlabeled(u),
            )
        }
        fn i64_optional<'this>(&'this self) -> Option<i64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_optional(t),
                |u| <U as MsgTrait>::i64_optional(u),
            )
        }
        type Field103RepeatedType<'this> = ::puroro::internal::impls::either::EitherRepeatedField<
            <T as MsgTrait>::Field103RepeatedType<'this>,
            <U as MsgTrait>::Field103RepeatedType<'this>,
        >;

        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::either::EitherRepeatedField::new(
                self.as_ref()
                    .map_left(|t| <T as MsgTrait>::i64_repeated(t))
                    .map_right(|u| <U as MsgTrait>::i64_repeated(u)),
            )
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            self.as_ref().either(
                |t| <T as MsgTrait>::u32_unlabeled(t),
                |u| <U as MsgTrait>::u32_unlabeled(u),
            )
        }
        fn u32_optional<'this>(&'this self) -> Option<u32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::u32_optional(t),
                |u| <U as MsgTrait>::u32_optional(u),
            )
        }
        type Field113RepeatedType<'this> = ::puroro::internal::impls::either::EitherRepeatedField<
            <T as MsgTrait>::Field113RepeatedType<'this>,
            <U as MsgTrait>::Field113RepeatedType<'this>,
        >;

        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::either::EitherRepeatedField::new(
                self.as_ref()
                    .map_left(|t| <T as MsgTrait>::u32_repeated(t))
                    .map_right(|u| <U as MsgTrait>::u32_repeated(u)),
            )
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            self.as_ref().either(
                |t| <T as MsgTrait>::u64_unlabeled(t),
                |u| <U as MsgTrait>::u64_unlabeled(u),
            )
        }
        fn u64_optional<'this>(&'this self) -> Option<u64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::u64_optional(t),
                |u| <U as MsgTrait>::u64_optional(u),
            )
        }
        type Field123RepeatedType<'this> = ::puroro::internal::impls::either::EitherRepeatedField<
            <T as MsgTrait>::Field123RepeatedType<'this>,
            <U as MsgTrait>::Field123RepeatedType<'this>,
        >;

        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::either::EitherRepeatedField::new(
                self.as_ref()
                    .map_left(|t| <T as MsgTrait>::u64_repeated(t))
                    .map_right(|u| <U as MsgTrait>::u64_repeated(u)),
            )
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            self.as_ref().either(
                |t| <T as MsgTrait>::s32_unlabeled(t),
                |u| <U as MsgTrait>::s32_unlabeled(u),
            )
        }
        fn s32_optional<'this>(&'this self) -> Option<i32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::s32_optional(t),
                |u| <U as MsgTrait>::s32_optional(u),
            )
        }
        type Field133RepeatedType<'this> = ::puroro::internal::impls::either::EitherRepeatedField<
            <T as MsgTrait>::Field133RepeatedType<'this>,
            <U as MsgTrait>::Field133RepeatedType<'this>,
        >;

        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::either::EitherRepeatedField::new(
                self.as_ref()
                    .map_left(|t| <T as MsgTrait>::s32_repeated(t))
                    .map_right(|u| <U as MsgTrait>::s32_repeated(u)),
            )
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            self.as_ref().either(
                |t| <T as MsgTrait>::s64_unlabeled(t),
                |u| <U as MsgTrait>::s64_unlabeled(u),
            )
        }
        fn s64_optional<'this>(&'this self) -> Option<i64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::s64_optional(t),
                |u| <U as MsgTrait>::s64_optional(u),
            )
        }
        type Field143RepeatedType<'this> = ::puroro::internal::impls::either::EitherRepeatedField<
            <T as MsgTrait>::Field143RepeatedType<'this>,
            <U as MsgTrait>::Field143RepeatedType<'this>,
        >;

        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::either::EitherRepeatedField::new(
                self.as_ref()
                    .map_left(|t| <T as MsgTrait>::s64_repeated(t))
                    .map_right(|u| <U as MsgTrait>::s64_repeated(u)),
            )
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            self.as_ref().either(
                |t| <T as MsgTrait>::fixed32_unlabeled(t),
                |u| <U as MsgTrait>::fixed32_unlabeled(u),
            )
        }
        fn fixed32_optional<'this>(&'this self) -> Option<u32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::fixed32_optional(t),
                |u| <U as MsgTrait>::fixed32_optional(u),
            )
        }
        type Field153RepeatedType<'this> = ::puroro::internal::impls::either::EitherRepeatedField<
            <T as MsgTrait>::Field153RepeatedType<'this>,
            <U as MsgTrait>::Field153RepeatedType<'this>,
        >;

        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::either::EitherRepeatedField::new(
                self.as_ref()
                    .map_left(|t| <T as MsgTrait>::fixed32_repeated(t))
                    .map_right(|u| <U as MsgTrait>::fixed32_repeated(u)),
            )
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            self.as_ref().either(
                |t| <T as MsgTrait>::fixed64_unlabeled(t),
                |u| <U as MsgTrait>::fixed64_unlabeled(u),
            )
        }
        fn fixed64_optional<'this>(&'this self) -> Option<u64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::fixed64_optional(t),
                |u| <U as MsgTrait>::fixed64_optional(u),
            )
        }
        type Field163RepeatedType<'this> = ::puroro::internal::impls::either::EitherRepeatedField<
            <T as MsgTrait>::Field163RepeatedType<'this>,
            <U as MsgTrait>::Field163RepeatedType<'this>,
        >;

        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::either::EitherRepeatedField::new(
                self.as_ref()
                    .map_left(|t| <T as MsgTrait>::fixed64_repeated(t))
                    .map_right(|u| <U as MsgTrait>::fixed64_repeated(u)),
            )
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            self.as_ref().either(
                |t| <T as MsgTrait>::sfixed32_unlabeled(t),
                |u| <U as MsgTrait>::sfixed32_unlabeled(u),
            )
        }
        fn sfixed32_optional<'this>(&'this self) -> Option<i32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::sfixed32_optional(t),
                |u| <U as MsgTrait>::sfixed32_optional(u),
            )
        }
        type Field173RepeatedType<'this> = ::puroro::internal::impls::either::EitherRepeatedField<
            <T as MsgTrait>::Field173RepeatedType<'this>,
            <U as MsgTrait>::Field173RepeatedType<'this>,
        >;

        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::either::EitherRepeatedField::new(
                self.as_ref()
                    .map_left(|t| <T as MsgTrait>::sfixed32_repeated(t))
                    .map_right(|u| <U as MsgTrait>::sfixed32_repeated(u)),
            )
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            self.as_ref().either(
                |t| <T as MsgTrait>::sfixed64_unlabeled(t),
                |u| <U as MsgTrait>::sfixed64_unlabeled(u),
            )
        }
        fn sfixed64_optional<'this>(&'this self) -> Option<i64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::sfixed64_optional(t),
                |u| <U as MsgTrait>::sfixed64_optional(u),
            )
        }
        type Field183RepeatedType<'this> = ::puroro::internal::impls::either::EitherRepeatedField<
            <T as MsgTrait>::Field183RepeatedType<'this>,
            <U as MsgTrait>::Field183RepeatedType<'this>,
        >;

        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::either::EitherRepeatedField::new(
                self.as_ref()
                    .map_left(|t| <T as MsgTrait>::sfixed64_repeated(t))
                    .map_right(|u| <U as MsgTrait>::sfixed64_repeated(u)),
            )
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            self.as_ref().either(
                |t| <T as MsgTrait>::f64_unlabeled(t),
                |u| <U as MsgTrait>::f64_unlabeled(u),
            )
        }
        fn f64_optional<'this>(&'this self) -> Option<f64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::f64_optional(t),
                |u| <U as MsgTrait>::f64_optional(u),
            )
        }
        type Field193RepeatedType<'this> = ::puroro::internal::impls::either::EitherRepeatedField<
            <T as MsgTrait>::Field193RepeatedType<'this>,
            <U as MsgTrait>::Field193RepeatedType<'this>,
        >;

        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::either::EitherRepeatedField::new(
                self.as_ref()
                    .map_left(|t| <T as MsgTrait>::f64_repeated(t))
                    .map_right(|u| <U as MsgTrait>::f64_repeated(u)),
            )
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField1 {
        i32_unlabeled: i32,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField1 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField1 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Clone::clone(&self.i32_unlabeled)
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField1 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::Int32>::ser_field(
                &self.i32_unlabeled,
                1,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField2 {
        i32_optional: ::std::option::Option<i32>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField2 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField2 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        fn i32_optional<'this>(&'this self) -> Option<i32> {
            Clone::clone(&self.i32_optional)
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField2 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field(
                &self.i32_optional,
                2,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField3 {
        i32_repeated: ::std::vec::Vec<i32>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField3 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField3 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, i32>>;

        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            self.i32_repeated.iter().cloned()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField3 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::Int32>::ser_field(
                &self.i32_repeated,
                3,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField11 {
        float_unlabeled: f32,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField11 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField11 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Clone::clone(&self.float_unlabeled)
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField11 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::Float>::ser_field(
                &self.float_unlabeled,
                11,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField12 {
        float_optional: ::std::option::Option<f32>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField12 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField12 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        fn float_optional<'this>(&'this self) -> Option<f32> {
            Clone::clone(&self.float_optional)
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField12 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field(
                &self.float_optional,
                12,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField13 {
        float_repeated: ::std::vec::Vec<f32>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField13 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField13 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, f32>>;

        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            self.float_repeated.iter().cloned()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField13 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::Float>::ser_field(
                &self.float_repeated,
                13,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField21 {
        bytes_unlabeled: ::std::borrow::Cow<'static, [u8]>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField21 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField21 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'this [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &self.bytes_unlabeled
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField21 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::Bytes>::ser_field(
                &self.bytes_unlabeled,
                21,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField22 {
        bytes_optional: ::std::option::Option<::std::borrow::Cow<'static, [u8]>>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField22 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField22 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'this [u8];
        fn bytes_optional<'this>(&'this self) -> Option<Self::Field22BytesType<'this>> {
            self.bytes_optional.as_ref().map(|v| v.as_ref())
        }
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField22 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bytes>::ser_field(
                &self.bytes_optional,
                22,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField23 {
        bytes_repeated: ::std::vec::Vec<::std::borrow::Cow<'static, [u8]>>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField23 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField23 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'this [u8];
        type Field23RepeatedType<'this> = ::puroro::internal::impls::simple::BorrowedIter<
            [u8],
            ::std::slice::Iter<'this, ::std::borrow::Cow<'static, [u8]>>,
        >;

        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::simple::BorrowedIter::new(self.bytes_repeated.iter())
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField23 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::Bytes>::ser_field(
                &self.bytes_repeated,
                23,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField31 {
        string_unlabeled: ::std::borrow::Cow<'static, str>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField31 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField31 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'this str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            &self.string_unlabeled
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField31 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::String>::ser_field(
                &self.string_unlabeled,
                31,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField32 {
        string_optional: ::std::option::Option<::std::borrow::Cow<'static, str>>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField32 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField32 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'this str;
        fn string_optional<'this>(&'this self) -> Option<Self::Field32StringType<'this>> {
            self.string_optional.as_ref().map(|v| v.as_ref())
        }
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField32 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::String>::ser_field(
                &self.string_optional,
                32,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField33 {
        string_repeated: ::std::vec::Vec<::std::borrow::Cow<'static, str>>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField33 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField33 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'this str;
        type Field33RepeatedType<'this> = ::puroro::internal::impls::simple::BorrowedIter<
            str,
            ::std::slice::Iter<'this, ::std::borrow::Cow<'static, str>>,
        >;

        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::simple::BorrowedIter::new(self.string_repeated.iter())
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField33 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::String>::ser_field(
                &self.string_repeated,
                33,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField41 {
        enum_unlabeled: self::_puroro_root::full_coverage3::Enum,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField41 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField41 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Clone::clone(&self.enum_unlabeled)
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField41 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<
                ::puroro::tags::Unlabeled,
                ::puroro::tags::Enum3<self::_puroro_root::full_coverage3::Enum>,
            >::ser_field(&self.enum_unlabeled, 41, out)?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField42 {
        enum_optional: ::std::option::Option<self::_puroro_root::full_coverage3::Enum>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField42 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField42 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        fn enum_optional<'this>(&'this self) -> Option<self::_puroro_root::full_coverage3::Enum> {
            Clone::clone(&self.enum_optional)
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField42 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<
                ::puroro::tags::Optional,
                ::puroro::tags::Enum3<self::_puroro_root::full_coverage3::Enum>,
            >::ser_field(&self.enum_optional, 42, out)?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField43 {
        enum_repeated: ::std::vec::Vec<self::_puroro_root::full_coverage3::Enum>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField43 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField43 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::std::iter::Cloned<
            ::std::slice::Iter<'this, self::_puroro_root::full_coverage3::Enum>,
        >;

        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            self.enum_repeated.iter().cloned()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField43 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<
                ::puroro::tags::Repeated,
                ::puroro::tags::Enum3<self::_puroro_root::full_coverage3::Enum>,
            >::ser_field(&self.enum_repeated, 43, out)?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField51 {
    submsg_unlabeled: ::std::option::Option<::std::boxed::Box<self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple>>,
}

    impl ::puroro::Message<MsgSimple> for MsgSimpleField51 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField51 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = &'this self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple;
        fn submsg_unlabeled<'this>(&'this self) -> Option<Self::Field51MessageType<'this>> {
            self.submsg_unlabeled.as_ref().map(|v| v.as_ref())
        }
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField51 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<
            ::puroro::tags::Unlabeled, ::puroro::tags::Message<self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple>
        >::ser_field(&self.submsg_unlabeled, 51, out)?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField52 {
    submsg_optional: ::std::option::Option<::std::boxed::Box<self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple>>,
}

    impl ::puroro::Message<MsgSimple> for MsgSimpleField52 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField52 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = &'this self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple;
        fn submsg_optional<'this>(&'this self) -> Option<Self::Field52MessageType<'this>> {
            self.submsg_optional.as_ref().map(|v| v.as_ref())
        }
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField52 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Message<self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple>
        >::ser_field(&self.submsg_optional, 52, out)?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField53 {
        submsg_repeated: ::std::vec::Vec<
            self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple,
        >,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField53 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField53 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = &'this self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple;
        type Field53RepeatedType<'this> = ::puroro::internal::impls::simple::BorrowedIter<
    self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple,
    ::std::slice::Iter<'this, self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple>>;

        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::simple::BorrowedIter::new(self.submsg_repeated.iter())
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField53 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<
            ::puroro::tags::Repeated, ::puroro::tags::Message<self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple>
        >::ser_field(&self.submsg_repeated, 53, out)?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField101 {
        i64_unlabeled: i64,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField101 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField101 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Clone::clone(&self.i64_unlabeled)
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField101 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::Int64>::ser_field(
                &self.i64_unlabeled,
                101,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField102 {
        i64_optional: ::std::option::Option<i64>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField102 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField102 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        fn i64_optional<'this>(&'this self) -> Option<i64> {
            Clone::clone(&self.i64_optional)
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField102 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field(
                &self.i64_optional,
                102,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField103 {
        i64_repeated: ::std::vec::Vec<i64>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField103 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField103 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, i64>>;

        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            self.i64_repeated.iter().cloned()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField103 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::Int64>::ser_field(
                &self.i64_repeated,
                103,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField111 {
        u32_unlabeled: u32,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField111 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField111 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Clone::clone(&self.u32_unlabeled)
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField111 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::UInt32>::ser_field(
                &self.u32_unlabeled,
                111,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField112 {
        u32_optional: ::std::option::Option<u32>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField112 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField112 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        fn u32_optional<'this>(&'this self) -> Option<u32> {
            Clone::clone(&self.u32_optional)
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField112 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt32>::ser_field(
                &self.u32_optional,
                112,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField113 {
        u32_repeated: ::std::vec::Vec<u32>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField113 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField113 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, u32>>;

        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            self.u32_repeated.iter().cloned()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField113 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::UInt32>::ser_field(
                &self.u32_repeated,
                113,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField121 {
        u64_unlabeled: u64,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField121 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField121 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Clone::clone(&self.u64_unlabeled)
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField121 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::UInt64>::ser_field(
                &self.u64_unlabeled,
                121,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField122 {
        u64_optional: ::std::option::Option<u64>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField122 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField122 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        fn u64_optional<'this>(&'this self) -> Option<u64> {
            Clone::clone(&self.u64_optional)
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField122 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt64>::ser_field(
                &self.u64_optional,
                122,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField123 {
        u64_repeated: ::std::vec::Vec<u64>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField123 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField123 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, u64>>;

        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            self.u64_repeated.iter().cloned()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField123 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::UInt64>::ser_field(
                &self.u64_repeated,
                123,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField131 {
        s32_unlabeled: i32,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField131 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField131 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Clone::clone(&self.s32_unlabeled)
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField131 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::SInt32>::ser_field(
                &self.s32_unlabeled,
                131,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField132 {
        s32_optional: ::std::option::Option<i32>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField132 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField132 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        fn s32_optional<'this>(&'this self) -> Option<i32> {
            Clone::clone(&self.s32_optional)
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField132 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::SInt32>::ser_field(
                &self.s32_optional,
                132,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField133 {
        s32_repeated: ::std::vec::Vec<i32>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField133 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField133 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, i32>>;

        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            self.s32_repeated.iter().cloned()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField133 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::SInt32>::ser_field(
                &self.s32_repeated,
                133,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField141 {
        s64_unlabeled: i64,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField141 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField141 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Clone::clone(&self.s64_unlabeled)
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField141 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::SInt64>::ser_field(
                &self.s64_unlabeled,
                141,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField142 {
        s64_optional: ::std::option::Option<i64>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField142 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField142 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        fn s64_optional<'this>(&'this self) -> Option<i64> {
            Clone::clone(&self.s64_optional)
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField142 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::SInt64>::ser_field(
                &self.s64_optional,
                142,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField143 {
        s64_repeated: ::std::vec::Vec<i64>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField143 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField143 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, i64>>;

        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            self.s64_repeated.iter().cloned()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField143 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::SInt64>::ser_field(
                &self.s64_repeated,
                143,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField151 {
        fixed32_unlabeled: u32,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField151 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField151 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Clone::clone(&self.fixed32_unlabeled)
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField151 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::Fixed32>::ser_field(
                &self.fixed32_unlabeled,
                151,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField152 {
        fixed32_optional: ::std::option::Option<u32>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField152 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField152 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        fn fixed32_optional<'this>(&'this self) -> Option<u32> {
            Clone::clone(&self.fixed32_optional)
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField152 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Fixed32>::ser_field(
                &self.fixed32_optional,
                152,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField153 {
        fixed32_repeated: ::std::vec::Vec<u32>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField153 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField153 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, u32>>;

        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            self.fixed32_repeated.iter().cloned()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField153 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::Fixed32>::ser_field(
                &self.fixed32_repeated,
                153,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField161 {
        fixed64_unlabeled: u64,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField161 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField161 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Clone::clone(&self.fixed64_unlabeled)
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField161 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::Fixed64>::ser_field(
                &self.fixed64_unlabeled,
                161,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField162 {
        fixed64_optional: ::std::option::Option<u64>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField162 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField162 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        fn fixed64_optional<'this>(&'this self) -> Option<u64> {
            Clone::clone(&self.fixed64_optional)
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField162 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Fixed64>::ser_field(
                &self.fixed64_optional,
                162,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField163 {
        fixed64_repeated: ::std::vec::Vec<u64>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField163 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField163 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, u64>>;

        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            self.fixed64_repeated.iter().cloned()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField163 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::Fixed64>::ser_field(
                &self.fixed64_repeated,
                163,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField171 {
        sfixed32_unlabeled: i32,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField171 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField171 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Clone::clone(&self.sfixed32_unlabeled)
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField171 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::SFixed32>::ser_field(
                &self.sfixed32_unlabeled,
                171,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField172 {
        sfixed32_optional: ::std::option::Option<i32>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField172 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField172 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        fn sfixed32_optional<'this>(&'this self) -> Option<i32> {
            Clone::clone(&self.sfixed32_optional)
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField172 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::SFixed32>::ser_field(
                &self.sfixed32_optional,
                172,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField173 {
        sfixed32_repeated: ::std::vec::Vec<i32>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField173 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField173 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, i32>>;

        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            self.sfixed32_repeated.iter().cloned()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField173 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::SFixed32>::ser_field(
                &self.sfixed32_repeated,
                173,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField181 {
        sfixed64_unlabeled: i64,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField181 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField181 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Clone::clone(&self.sfixed64_unlabeled)
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField181 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::SFixed64>::ser_field(
                &self.sfixed64_unlabeled,
                181,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField182 {
        sfixed64_optional: ::std::option::Option<i64>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField182 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField182 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        fn sfixed64_optional<'this>(&'this self) -> Option<i64> {
            Clone::clone(&self.sfixed64_optional)
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField182 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::SFixed64>::ser_field(
                &self.sfixed64_optional,
                182,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField183 {
        sfixed64_repeated: ::std::vec::Vec<i64>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField183 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField183 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, i64>>;

        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            self.sfixed64_repeated.iter().cloned()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField183 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::SFixed64>::ser_field(
                &self.sfixed64_repeated,
                183,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField191 {
        f64_unlabeled: f64,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField191 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField191 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Clone::clone(&self.f64_unlabeled)
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField191 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::Double>::ser_field(
                &self.f64_unlabeled,
                191,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField192 {
        f64_optional: ::std::option::Option<f64>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField192 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField192 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        fn f64_optional<'this>(&'this self) -> Option<f64> {
            Clone::clone(&self.f64_optional)
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField192 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Double>::ser_field(
                &self.f64_optional,
                192,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField193 {
        f64_repeated: ::std::vec::Vec<f64>,
    }

    impl ::puroro::Message<MsgSimple> for MsgSimpleField193 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField193 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            Default::default()
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field21BytesType<'this> = &'static [u8];
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            &[]
        }
        type Field22BytesType<'this> = &'static [u8];
        type Field23BytesType<'this> = &'static [u8];
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field31StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            ""
        }
        type Field32StringType<'this> = &'static str;
        type Field33StringType<'this> = &'static str;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            Default::default()
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        type Field51MessageType<'this> = ();
        type Field52MessageType<'this> = ();
        type Field53MessageType<'this> = ();
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            Default::default()
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            Default::default()
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            Default::default()
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            ::puroro::internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            Default::default()
        }
        type Field193RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, f64>>;

        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            self.f64_repeated.iter().cloned()
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimpleField193 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Repeated, ::puroro::tags::Double>::ser_field(
                &self.f64_repeated,
                193,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }
    #[derive(
        ::std::clone::Clone, ::std::default::Default, ::std::cmp::PartialEq, ::std::fmt::Debug,
    )]
    pub struct MsgSimpleByValue {}
    impl ::puroro::Message<MsgSimple> for MsgSimpleByValue {}

    impl MsgTrait for MsgSimpleByValue {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn i32_optional<'this>(&'this self) -> Option<i32> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field3RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn float_unlabeled<'this>(&'this self) -> f32 {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn float_optional<'this>(&'this self) -> Option<f32> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field13RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field21BytesType<'this> = ::std::borrow::Cow<'this, [u8]>;
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field22BytesType<'this> = ::std::borrow::Cow<'this, [u8]>;
        fn bytes_optional<'this>(&'this self) -> Option<Self::Field22BytesType<'this>> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field23BytesType<'this> = ::std::borrow::Cow<'this, [u8]>;
        type Field23RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field31StringType<'this> = ::std::borrow::Cow<'this, str>;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field32StringType<'this> = ::std::borrow::Cow<'this, str>;
        fn string_optional<'this>(&'this self) -> Option<Self::Field32StringType<'this>> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field33StringType<'this> = ::std::borrow::Cow<'this, str>;
        type Field33RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn enum_optional<'this>(&'this self) -> Option<self::_puroro_root::full_coverage3::Enum> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field43RepeatedType<'this> = ::puroro::internal::impls::empty::EmptyRepeatedField<
            self::_puroro_root::full_coverage3::Enum,
        >;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field51MessageType<'this> = ::std::boxed::Box<
            self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple,
        >;
        fn submsg_unlabeled<'this>(&'this self) -> Option<Self::Field51MessageType<'this>> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field52MessageType<'this> = ::std::boxed::Box<
            self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple,
        >;
        fn submsg_optional<'this>(&'this self) -> Option<Self::Field52MessageType<'this>> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field53MessageType<'this> = ::std::boxed::Box<
            self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_impls::SubmsgSimple,
        >;
        type Field53RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn i64_unlabeled<'this>(&'this self) -> i64 {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn i64_optional<'this>(&'this self) -> Option<i64> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field103RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn u32_unlabeled<'this>(&'this self) -> u32 {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn u32_optional<'this>(&'this self) -> Option<u32> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field113RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn u64_unlabeled<'this>(&'this self) -> u64 {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn u64_optional<'this>(&'this self) -> Option<u64> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field123RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn s32_unlabeled<'this>(&'this self) -> i32 {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn s32_optional<'this>(&'this self) -> Option<i32> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field133RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn s64_unlabeled<'this>(&'this self) -> i64 {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn s64_optional<'this>(&'this self) -> Option<i64> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field143RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn fixed32_unlabeled<'this>(&'this self) -> u32 {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn fixed32_optional<'this>(&'this self) -> Option<u32> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field153RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn fixed64_unlabeled<'this>(&'this self) -> u64 {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn fixed64_optional<'this>(&'this self) -> Option<u64> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field163RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn sfixed32_optional<'this>(&'this self) -> Option<i32> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field173RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn sfixed64_optional<'this>(&'this self) -> Option<i64> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field183RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn f64_unlabeled<'this>(&'this self) -> f64 {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        fn f64_optional<'this>(&'this self) -> Option<f64> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
        type Field193RepeatedType<'this> =
            ::puroro::internal::impls::empty::EmptyRepeatedField<f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
    }
    #[derive(
        ::std::clone::Clone, ::std::default::Default, ::std::cmp::PartialEq, ::std::fmt::Debug,
    )]
    pub struct SomeSimple {
        pub i32_unlabeled: i32,
    }
    impl ::puroro::Message<SomeSimple> for SomeSimple {}

    impl SomeTrait for SomeSimple {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Clone::clone(&self.i32_unlabeled)
        }
    }

    impl ::puroro::MessageRepresentativeImpl for SomeSimple {
        fn descriptor() -> &'static ::puroro::desc::MessageDescriptor {
            use ::puroro::once_cell::sync::Lazy;
            static LAZY_FIELD_DESCRIPTOR_ARRAY: Lazy<[::puroro::desc::FieldDescriptor; 1]> =
                Lazy::new(|| {
                    [{
                        let init = ::puroro::internal::FieldDescriptorInitializer {
                            name: "i32_unlabeled",
                            number: 1,
                            lazy_containing_type: Lazy::new(|| {
                                <SomeSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                            }),
                        };
                        ::puroro::internal::init_field_descriptor(init)
                    }]
                });
            static LAZY_DESCRIPTOR: Lazy<::puroro::desc::MessageDescriptor> = Lazy::new(|| {
                let init = ::puroro::internal::MessageDescriptorInitializer {
                    name: "Some",
                    lazy_fields: Lazy::new(|| Lazy::force(&LAZY_FIELD_DESCRIPTOR_ARRAY).as_ref()),
                };
                ::puroro::internal::init_message_descriptor(init)
            });
            Lazy::force(&LAZY_DESCRIPTOR)
        }
    }

    impl ::puroro::DeserFromBytesIter for SomeSimple {
        fn deser<I>(&mut self, iter: I) -> ::puroro::Result<()>
        where
            I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>,
        {
            ::puroro::internal::de::from_iter::deser_from_iter(self, iter)
        }
    }

    impl ::puroro::internal::de::DeserFieldsFromBytesIter for SomeSimple {
        fn deser_field<I>(
            &mut self,
            field_number: i32,
            data: ::puroro::types::FieldData<&mut ::puroro::internal::de::from_iter::ScopedIter<I>>,
        ) -> ::puroro::Result<()>
        where
            I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>,
        {
            use ::puroro::internal::impls::simple::de::DeserFieldFromBytesIter;
            match field_number {
            1 => DeserFieldFromBytesIter::<
                ::puroro::tags::Unlabeled, ::puroro::tags::Int32
            >::deser_field(&mut self.i32_unlabeled, data),

            _ => unimplemented!("TODO: This case should be handled properly..."),
        }
        }
    }

    impl ::puroro::SerToIoWrite for SomeSimple {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::Int32>::ser_field(
                &self.i32_unlabeled,
                1,
                out,
            )?;

            ::std::result::Result::Ok(())
        }
    }
    impl SomeTrait for () {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Default::default()
        }
    }
    impl<T, U> SomeTrait for (T, U)
    where
        T: SomeTrait,
        U: SomeTrait,
    {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            let right = <U as SomeTrait>::i32_unlabeled(&self.1);
            if right != ::std::default::Default::default() {
                right
            } else {
                <T as SomeTrait>::i32_unlabeled(&self.0)
            }
        }
    }
    impl<T, U> SomeTrait for ::puroro::Either<T, U>
    where
        T: SomeTrait,
        U: SomeTrait,
    {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            self.as_ref().either(
                |t| <T as SomeTrait>::i32_unlabeled(t),
                |u| <U as SomeTrait>::i32_unlabeled(u),
            )
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct SomeSimpleField1 {
        i32_unlabeled: i32,
    }

    impl ::puroro::Message<SomeSimple> for SomeSimpleField1 {}

    impl super::_puroro_traits::SomeTrait for SomeSimpleField1 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            Clone::clone(&self.i32_unlabeled)
        }
    }

    impl ::puroro::SerToIoWrite for SomeSimpleField1 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Unlabeled, ::puroro::tags::Int32>::ser_field(
                &self.i32_unlabeled,
                1,
                out,
            )?;
            ::std::result::Result::Ok(())
        }
    }
    #[derive(
        ::std::clone::Clone, ::std::default::Default, ::std::cmp::PartialEq, ::std::fmt::Debug,
    )]
    pub struct SomeSimpleByValue {}
    impl ::puroro::Message<SomeSimple> for SomeSimpleByValue {}

    impl SomeTrait for SomeSimpleByValue {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            unimplemented!("Please don't use / instantiate this struct!!")
        }
    }
}
pub use _puroro_traits::*;
pub mod _puroro_traits {
    mod _puroro_root {
        pub use super::super::_puroro_root::*;
    }

    pub trait MsgTrait {
        fn i32_unlabeled<'this>(&'this self) -> i32;
        fn i32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::default::Default::default()
        }
        type Field3RepeatedType<'this>: ::puroro::RepeatedField<'this>
            + ::std::iter::IntoIterator<Item = i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this>;
        fn float_unlabeled<'this>(&'this self) -> f32;
        fn float_optional<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::default::Default::default()
        }
        type Field13RepeatedType<'this>: ::puroro::RepeatedField<'this>
            + ::std::iter::IntoIterator<Item = f32>;
        fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this>;
        type Field21BytesType<'this>: ::std::ops::Deref<Target = [u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug;
        fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this>;
        type Field22BytesType<'this>: ::std::ops::Deref<Target = [u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug;
        fn bytes_optional<'this>(
            &'this self,
        ) -> ::std::option::Option<Self::Field22BytesType<'this>> {
            ::std::default::Default::default()
        }
        type Field23BytesType<'this>: ::std::ops::Deref<Target = [u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug;
        type Field23RepeatedType<'this>: ::puroro::RepeatedField<'this>
            + ::std::iter::IntoIterator<Item = Self::Field23BytesType<'this>>;
        fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this>;
        type Field31StringType<'this>: ::std::ops::Deref<Target = str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug;
        fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this>;
        type Field32StringType<'this>: ::std::ops::Deref<Target = str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug;
        fn string_optional<'this>(
            &'this self,
        ) -> ::std::option::Option<Self::Field32StringType<'this>> {
            ::std::default::Default::default()
        }
        type Field33StringType<'this>: ::std::ops::Deref<Target = str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug;
        type Field33RepeatedType<'this>: ::puroro::RepeatedField<'this>
            + ::std::iter::IntoIterator<Item = Self::Field33StringType<'this>>;
        fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this>;
        fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum;
        fn enum_optional<'this>(
            &'this self,
        ) -> ::std::option::Option<self::_puroro_root::full_coverage3::Enum> {
            ::std::default::Default::default()
        }
        type Field43RepeatedType<'this>: ::puroro::RepeatedField<'this>
            + ::std::iter::IntoIterator<Item = self::_puroro_root::full_coverage3::Enum>;
        fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this>;
        type Field51MessageType<'this>:
            self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_traits::SubmsgTrait + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug;
        fn submsg_unlabeled<'this>(
            &'this self,
        ) -> ::std::option::Option<Self::Field51MessageType<'this>> {
            ::std::default::Default::default()
        }
        type Field52MessageType<'this>:
            self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_traits::SubmsgTrait + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug;
        fn submsg_optional<'this>(
            &'this self,
        ) -> ::std::option::Option<Self::Field52MessageType<'this>> {
            ::std::default::Default::default()
        }
        type Field53MessageType<'this>:
            self::_puroro_root::full_coverage3::_puroro_nested::msg::_puroro_traits::SubmsgTrait + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug;
        type Field53RepeatedType<'this>: ::puroro::RepeatedField<'this>
            + ::std::iter::IntoIterator<Item = Self::Field53MessageType<'this>>;
        fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this>;
        fn i64_unlabeled<'this>(&'this self) -> i64;
        fn i64_optional<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::default::Default::default()
        }
        type Field103RepeatedType<'this>: ::puroro::RepeatedField<'this>
            + ::std::iter::IntoIterator<Item = i64>;
        fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this>;
        fn u32_unlabeled<'this>(&'this self) -> u32;
        fn u32_optional<'this>(&'this self) -> ::std::option::Option<u32> {
            ::std::default::Default::default()
        }
        type Field113RepeatedType<'this>: ::puroro::RepeatedField<'this>
            + ::std::iter::IntoIterator<Item = u32>;
        fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this>;
        fn u64_unlabeled<'this>(&'this self) -> u64;
        fn u64_optional<'this>(&'this self) -> ::std::option::Option<u64> {
            ::std::default::Default::default()
        }
        type Field123RepeatedType<'this>: ::puroro::RepeatedField<'this>
            + ::std::iter::IntoIterator<Item = u64>;
        fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this>;
        fn s32_unlabeled<'this>(&'this self) -> i32;
        fn s32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::default::Default::default()
        }
        type Field133RepeatedType<'this>: ::puroro::RepeatedField<'this>
            + ::std::iter::IntoIterator<Item = i32>;
        fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this>;
        fn s64_unlabeled<'this>(&'this self) -> i64;
        fn s64_optional<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::default::Default::default()
        }
        type Field143RepeatedType<'this>: ::puroro::RepeatedField<'this>
            + ::std::iter::IntoIterator<Item = i64>;
        fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this>;
        fn fixed32_unlabeled<'this>(&'this self) -> u32;
        fn fixed32_optional<'this>(&'this self) -> ::std::option::Option<u32> {
            ::std::default::Default::default()
        }
        type Field153RepeatedType<'this>: ::puroro::RepeatedField<'this>
            + ::std::iter::IntoIterator<Item = u32>;
        fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this>;
        fn fixed64_unlabeled<'this>(&'this self) -> u64;
        fn fixed64_optional<'this>(&'this self) -> ::std::option::Option<u64> {
            ::std::default::Default::default()
        }
        type Field163RepeatedType<'this>: ::puroro::RepeatedField<'this>
            + ::std::iter::IntoIterator<Item = u64>;
        fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this>;
        fn sfixed32_unlabeled<'this>(&'this self) -> i32;
        fn sfixed32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::default::Default::default()
        }
        type Field173RepeatedType<'this>: ::puroro::RepeatedField<'this>
            + ::std::iter::IntoIterator<Item = i32>;
        fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this>;
        fn sfixed64_unlabeled<'this>(&'this self) -> i64;
        fn sfixed64_optional<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::default::Default::default()
        }
        type Field183RepeatedType<'this>: ::puroro::RepeatedField<'this>
            + ::std::iter::IntoIterator<Item = i64>;
        fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this>;
        fn f64_unlabeled<'this>(&'this self) -> f64;
        fn f64_optional<'this>(&'this self) -> ::std::option::Option<f64> {
            ::std::default::Default::default()
        }
        type Field193RepeatedType<'this>: ::puroro::RepeatedField<'this>
            + ::std::iter::IntoIterator<Item = f64>;
        fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this>;
    }

    macro_rules! msg_delegate {
        ($ty:ty) => {
            fn i32_unlabeled<'this>(&'this self) -> i32 {
                (**self).i32_unlabeled()
            }
            fn i32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
                (**self).i32_optional()
            }
            type Field3RepeatedType<'this> = <$ty>::Field3RepeatedType<'this>;
            fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
                (**self).i32_repeated()
            }
            fn float_unlabeled<'this>(&'this self) -> f32 {
                (**self).float_unlabeled()
            }
            fn float_optional<'this>(&'this self) -> ::std::option::Option<f32> {
                (**self).float_optional()
            }
            type Field13RepeatedType<'this> = <$ty>::Field13RepeatedType<'this>;
            fn float_repeated<'this>(&'this self) -> Self::Field13RepeatedType<'this> {
                (**self).float_repeated()
            }
            type Field21BytesType<'this> = <$ty>::Field21BytesType<'this>;
            fn bytes_unlabeled<'this>(&'this self) -> Self::Field21BytesType<'this> {
                (**self).bytes_unlabeled()
            }
            type Field22BytesType<'this> = <$ty>::Field22BytesType<'this>;
            fn bytes_optional<'this>(
                &'this self,
            ) -> ::std::option::Option<Self::Field22BytesType<'this>> {
                (**self).bytes_optional()
            }
            type Field23BytesType<'this> = <$ty>::Field23BytesType<'this>;
            type Field23RepeatedType<'this> = <$ty>::Field23RepeatedType<'this>;
            fn bytes_repeated<'this>(&'this self) -> Self::Field23RepeatedType<'this> {
                (**self).bytes_repeated()
            }
            type Field31StringType<'this> = <$ty>::Field31StringType<'this>;
            fn string_unlabeled<'this>(&'this self) -> Self::Field31StringType<'this> {
                (**self).string_unlabeled()
            }
            type Field32StringType<'this> = <$ty>::Field32StringType<'this>;
            fn string_optional<'this>(
                &'this self,
            ) -> ::std::option::Option<Self::Field32StringType<'this>> {
                (**self).string_optional()
            }
            type Field33StringType<'this> = <$ty>::Field33StringType<'this>;
            type Field33RepeatedType<'this> = <$ty>::Field33RepeatedType<'this>;
            fn string_repeated<'this>(&'this self) -> Self::Field33RepeatedType<'this> {
                (**self).string_repeated()
            }
            fn enum_unlabeled<'this>(&'this self) -> self::_puroro_root::full_coverage3::Enum {
                (**self).enum_unlabeled()
            }
            fn enum_optional<'this>(
                &'this self,
            ) -> ::std::option::Option<self::_puroro_root::full_coverage3::Enum> {
                (**self).enum_optional()
            }
            type Field43RepeatedType<'this> = <$ty>::Field43RepeatedType<'this>;
            fn enum_repeated<'this>(&'this self) -> Self::Field43RepeatedType<'this> {
                (**self).enum_repeated()
            }
            type Field51MessageType<'this> = <$ty>::Field51MessageType<'this>;
            fn submsg_unlabeled<'this>(
                &'this self,
            ) -> ::std::option::Option<Self::Field51MessageType<'this>> {
                (**self).submsg_unlabeled()
            }
            type Field52MessageType<'this> = <$ty>::Field52MessageType<'this>;
            fn submsg_optional<'this>(
                &'this self,
            ) -> ::std::option::Option<Self::Field52MessageType<'this>> {
                (**self).submsg_optional()
            }
            type Field53MessageType<'this> = <$ty>::Field53MessageType<'this>;
            type Field53RepeatedType<'this> = <$ty>::Field53RepeatedType<'this>;
            fn submsg_repeated<'this>(&'this self) -> Self::Field53RepeatedType<'this> {
                (**self).submsg_repeated()
            }
            fn i64_unlabeled<'this>(&'this self) -> i64 {
                (**self).i64_unlabeled()
            }
            fn i64_optional<'this>(&'this self) -> ::std::option::Option<i64> {
                (**self).i64_optional()
            }
            type Field103RepeatedType<'this> = <$ty>::Field103RepeatedType<'this>;
            fn i64_repeated<'this>(&'this self) -> Self::Field103RepeatedType<'this> {
                (**self).i64_repeated()
            }
            fn u32_unlabeled<'this>(&'this self) -> u32 {
                (**self).u32_unlabeled()
            }
            fn u32_optional<'this>(&'this self) -> ::std::option::Option<u32> {
                (**self).u32_optional()
            }
            type Field113RepeatedType<'this> = <$ty>::Field113RepeatedType<'this>;
            fn u32_repeated<'this>(&'this self) -> Self::Field113RepeatedType<'this> {
                (**self).u32_repeated()
            }
            fn u64_unlabeled<'this>(&'this self) -> u64 {
                (**self).u64_unlabeled()
            }
            fn u64_optional<'this>(&'this self) -> ::std::option::Option<u64> {
                (**self).u64_optional()
            }
            type Field123RepeatedType<'this> = <$ty>::Field123RepeatedType<'this>;
            fn u64_repeated<'this>(&'this self) -> Self::Field123RepeatedType<'this> {
                (**self).u64_repeated()
            }
            fn s32_unlabeled<'this>(&'this self) -> i32 {
                (**self).s32_unlabeled()
            }
            fn s32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
                (**self).s32_optional()
            }
            type Field133RepeatedType<'this> = <$ty>::Field133RepeatedType<'this>;
            fn s32_repeated<'this>(&'this self) -> Self::Field133RepeatedType<'this> {
                (**self).s32_repeated()
            }
            fn s64_unlabeled<'this>(&'this self) -> i64 {
                (**self).s64_unlabeled()
            }
            fn s64_optional<'this>(&'this self) -> ::std::option::Option<i64> {
                (**self).s64_optional()
            }
            type Field143RepeatedType<'this> = <$ty>::Field143RepeatedType<'this>;
            fn s64_repeated<'this>(&'this self) -> Self::Field143RepeatedType<'this> {
                (**self).s64_repeated()
            }
            fn fixed32_unlabeled<'this>(&'this self) -> u32 {
                (**self).fixed32_unlabeled()
            }
            fn fixed32_optional<'this>(&'this self) -> ::std::option::Option<u32> {
                (**self).fixed32_optional()
            }
            type Field153RepeatedType<'this> = <$ty>::Field153RepeatedType<'this>;
            fn fixed32_repeated<'this>(&'this self) -> Self::Field153RepeatedType<'this> {
                (**self).fixed32_repeated()
            }
            fn fixed64_unlabeled<'this>(&'this self) -> u64 {
                (**self).fixed64_unlabeled()
            }
            fn fixed64_optional<'this>(&'this self) -> ::std::option::Option<u64> {
                (**self).fixed64_optional()
            }
            type Field163RepeatedType<'this> = <$ty>::Field163RepeatedType<'this>;
            fn fixed64_repeated<'this>(&'this self) -> Self::Field163RepeatedType<'this> {
                (**self).fixed64_repeated()
            }
            fn sfixed32_unlabeled<'this>(&'this self) -> i32 {
                (**self).sfixed32_unlabeled()
            }
            fn sfixed32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
                (**self).sfixed32_optional()
            }
            type Field173RepeatedType<'this> = <$ty>::Field173RepeatedType<'this>;
            fn sfixed32_repeated<'this>(&'this self) -> Self::Field173RepeatedType<'this> {
                (**self).sfixed32_repeated()
            }
            fn sfixed64_unlabeled<'this>(&'this self) -> i64 {
                (**self).sfixed64_unlabeled()
            }
            fn sfixed64_optional<'this>(&'this self) -> ::std::option::Option<i64> {
                (**self).sfixed64_optional()
            }
            type Field183RepeatedType<'this> = <$ty>::Field183RepeatedType<'this>;
            fn sfixed64_repeated<'this>(&'this self) -> Self::Field183RepeatedType<'this> {
                (**self).sfixed64_repeated()
            }
            fn f64_unlabeled<'this>(&'this self) -> f64 {
                (**self).f64_unlabeled()
            }
            fn f64_optional<'this>(&'this self) -> ::std::option::Option<f64> {
                (**self).f64_optional()
            }
            type Field193RepeatedType<'this> = <$ty>::Field193RepeatedType<'this>;
            fn f64_repeated<'this>(&'this self) -> Self::Field193RepeatedType<'this> {
                (**self).f64_repeated()
            }
        };
    }

    impl<T> MsgTrait for &'_ T
    where
        T: MsgTrait,
    {
        msg_delegate!(T);
    }

    impl<T> MsgTrait for ::std::boxed::Box<T>
    where
        T: MsgTrait,
    {
        msg_delegate!(T);
    }
    pub trait SomeTrait {
        fn i32_unlabeled<'this>(&'this self) -> i32;
    }

    macro_rules! some_delegate {
        ($ty:ty) => {
            fn i32_unlabeled<'this>(&'this self) -> i32 {
                (**self).i32_unlabeled()
            }
        };
    }

    impl<T> SomeTrait for &'_ T
    where
        T: SomeTrait,
    {
        some_delegate!(T);
    }

    impl<T> SomeTrait for ::std::boxed::Box<T>
    where
        T: SomeTrait,
    {
        some_delegate!(T);
    }
}
#[derive(::std::fmt::Debug, ::std::clone::Clone, ::std::cmp::PartialEq)]
pub enum Enum {
    Zeroth,
    First,
    Tenth,
    _Unknown(i32),
}

impl ::puroro::Enum3 for Enum {}
impl ::std::convert::From<i32> for Enum {
    fn from(value: i32) -> Self {
        match value {
            0 => Enum::Zeroth,
            1 => Enum::First,
            10 => Enum::Tenth,
            _ => Enum::_Unknown(value),
        }
    }
}

impl ::std::convert::From<Enum> for i32 {
    fn from(value: Enum) -> i32 {
        match value {
            Enum::Zeroth => 0,
            Enum::First => 1,
            Enum::Tenth => 10,
            Enum::_Unknown(ivalue) => ivalue,
        }
    }
}

impl ::std::default::Default for Enum {
    fn default() -> Self {
        Enum::Zeroth
    }
}
pub use _puroro_nested::*;
pub mod _puroro_nested {
    pub mod msg {
        mod _puroro_root {
            pub use super::super::super::_puroro_root::*;
        }

        pub use _puroro_impls::SubmsgSimple as Submsg;
        pub mod _puroro_impls {
            mod _puroro_root {
                pub use super::super::_puroro_root::*;
            }
            use super::_puroro_traits::*;
            #[derive(
                ::std::clone::Clone,
                ::std::default::Default,
                ::std::cmp::PartialEq,
                ::std::fmt::Debug,
            )]
            pub struct SubmsgSimple {
                pub i32_unlabeled: i32,
            }
            impl ::puroro::Message<SubmsgSimple> for SubmsgSimple {}

            impl SubmsgTrait for SubmsgSimple {
                fn i32_unlabeled<'this>(&'this self) -> i32 {
                    Clone::clone(&self.i32_unlabeled)
                }
            }

            impl ::puroro::MessageRepresentativeImpl for SubmsgSimple {
                fn descriptor() -> &'static ::puroro::desc::MessageDescriptor {
                    use ::puroro::once_cell::sync::Lazy;
                    static LAZY_FIELD_DESCRIPTOR_ARRAY: Lazy<[::puroro::desc::FieldDescriptor; 1]> =
                        Lazy::new(|| {
                            [{
                                let init = ::puroro::internal::FieldDescriptorInitializer {
                                    name: "i32_unlabeled",
                                    number: 1,
                                    lazy_containing_type: Lazy::new(|| {
                                        <SubmsgSimple as ::puroro::MessageRepresentativeImpl>::descriptor()
                                    }),
                                };
                                ::puroro::internal::init_field_descriptor(init)
                            }]
                        });
                    static LAZY_DESCRIPTOR: Lazy<::puroro::desc::MessageDescriptor> =
                        Lazy::new(|| {
                            let init = ::puroro::internal::MessageDescriptorInitializer {
                                name: "Submsg",
                                lazy_fields: Lazy::new(|| {
                                    Lazy::force(&LAZY_FIELD_DESCRIPTOR_ARRAY).as_ref()
                                }),
                            };
                            ::puroro::internal::init_message_descriptor(init)
                        });
                    Lazy::force(&LAZY_DESCRIPTOR)
                }
            }

            impl ::puroro::DeserFromBytesIter for SubmsgSimple {
                fn deser<I>(&mut self, iter: I) -> ::puroro::Result<()>
                where
                    I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>,
                {
                    ::puroro::internal::de::from_iter::deser_from_iter(self, iter)
                }
            }

            impl ::puroro::internal::de::DeserFieldsFromBytesIter for SubmsgSimple {
                fn deser_field<I>(
                    &mut self,
                    field_number: i32,
                    data: ::puroro::types::FieldData<
                        &mut ::puroro::internal::de::from_iter::ScopedIter<I>,
                    >,
                ) -> ::puroro::Result<()>
                where
                    I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>,
                {
                    use ::puroro::internal::impls::simple::de::DeserFieldFromBytesIter;
                    match field_number {
                        1 => DeserFieldFromBytesIter::<
                            ::puroro::tags::Unlabeled,
                            ::puroro::tags::Int32,
                        >::deser_field(&mut self.i32_unlabeled, data),

                        _ => unimplemented!("TODO: This case should be handled properly..."),
                    }
                }
            }

            impl ::puroro::SerToIoWrite for SubmsgSimple {
                fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
                where
                    W: ::std::io::Write,
                {
                    use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
                    SerFieldToIoWrite::<
                    ::puroro::tags::Unlabeled, ::puroro::tags::Int32
                >::ser_field(&self.i32_unlabeled, 1, out)?;

                    ::std::result::Result::Ok(())
                }
            }
            impl SubmsgTrait for () {
                fn i32_unlabeled<'this>(&'this self) -> i32 {
                    Default::default()
                }
            }
            impl<T, U> SubmsgTrait for (T, U)
            where
                T: SubmsgTrait,
                U: SubmsgTrait,
            {
                fn i32_unlabeled<'this>(&'this self) -> i32 {
                    let right = <U as SubmsgTrait>::i32_unlabeled(&self.1);
                    if right != ::std::default::Default::default() {
                        right
                    } else {
                        <T as SubmsgTrait>::i32_unlabeled(&self.0)
                    }
                }
            }
            impl<T, U> SubmsgTrait for ::puroro::Either<T, U>
            where
                T: SubmsgTrait,
                U: SubmsgTrait,
            {
                fn i32_unlabeled<'this>(&'this self) -> i32 {
                    self.as_ref().either(
                        |t| <T as SubmsgTrait>::i32_unlabeled(t),
                        |u| <U as SubmsgTrait>::i32_unlabeled(u),
                    )
                }
            }

            #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
            struct SubmsgSimpleField1 {
                i32_unlabeled: i32,
            }

            impl ::puroro::Message<SubmsgSimple> for SubmsgSimpleField1 {}

            impl super::_puroro_traits::SubmsgTrait for SubmsgSimpleField1 {
                fn i32_unlabeled<'this>(&'this self) -> i32 {
                    Clone::clone(&self.i32_unlabeled)
                }
            }

            impl ::puroro::SerToIoWrite for SubmsgSimpleField1 {
                fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
                where
                    W: ::std::io::Write,
                {
                    use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
                    SerFieldToIoWrite::<
                    ::puroro::tags::Unlabeled, ::puroro::tags::Int32
                >::ser_field(&self.i32_unlabeled, 1, out)?;
                    ::std::result::Result::Ok(())
                }
            }
            #[derive(
                ::std::clone::Clone,
                ::std::default::Default,
                ::std::cmp::PartialEq,
                ::std::fmt::Debug,
            )]
            pub struct SubmsgSimpleByValue {}
            impl ::puroro::Message<SubmsgSimple> for SubmsgSimpleByValue {}

            impl SubmsgTrait for SubmsgSimpleByValue {
                fn i32_unlabeled<'this>(&'this self) -> i32 {
                    unimplemented!("Please don't use / instantiate this struct!!")
                }
            }
        }
        pub use _puroro_traits::*;
        pub mod _puroro_traits {
            mod _puroro_root {
                pub use super::super::_puroro_root::*;
            }

            pub trait SubmsgTrait {
                fn i32_unlabeled<'this>(&'this self) -> i32;
            }

            macro_rules! submsg_delegate {
                ($ty:ty) => {
                    fn i32_unlabeled<'this>(&'this self) -> i32 {
                        (**self).i32_unlabeled()
                    }
                };
            }

            impl<T> SubmsgTrait for &'_ T
            where
                T: SubmsgTrait,
            {
                submsg_delegate!(T);
            }

            impl<T> SubmsgTrait for ::std::boxed::Box<T>
            where
                T: SubmsgTrait,
            {
                submsg_delegate!(T);
            }
        }
        pub use _puroro_nested::*;
        pub mod _puroro_nested {
            pub mod submsg {
                mod _puroro_root {
                    pub use super::super::super::_puroro_root::*;
                }
            }
        }
    }
    pub mod some {
        mod _puroro_root {
            pub use super::super::super::_puroro_root::*;
        }
    }
}
