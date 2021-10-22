// A generated source code by puroro library
// package proto2_defaults

pub mod _puroro_root {
    pub use super::super::_puroro_root::*;
}

pub use _puroro_simple_impl::Msg;
pub mod _puroro_simple_impl {
    mod _puroro_root {
        pub use super::super::_puroro_root::*;
    }
    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    pub struct Msg {
        pub i32_default: ::std::option::Option<i32>,
        pub i32_0: ::std::option::Option<i32>,
        pub i32_42: ::std::option::Option<i32>,
        pub i32_m42: ::std::option::Option<i32>,
        pub i32_2147483647: ::std::option::Option<i32>,
        pub i32_m2147483648: ::std::option::Option<i32>,
        pub i32_0123: ::std::option::Option<i32>,
        pub i32_0x123: ::std::option::Option<i32>,
        pub u32_default: ::std::option::Option<u32>,
        pub u32_0: ::std::option::Option<u32>,
        pub u32_42: ::std::option::Option<u32>,
        pub u32_4294967295: ::std::option::Option<u32>,
        pub u32_0123: ::std::option::Option<u32>,
        pub u32_0x123: ::std::option::Option<u32>,
        pub i64_default: ::std::option::Option<i64>,
        pub i64_0: ::std::option::Option<i64>,
        pub i64_42: ::std::option::Option<i64>,
        pub i64_m42: ::std::option::Option<i64>,
        pub i64_9223372036854775807: ::std::option::Option<i64>,
        pub i64_m9223372036854775808: ::std::option::Option<i64>,
        pub i64_0123: ::std::option::Option<i64>,
        pub i64_0x123: ::std::option::Option<i64>,
        pub u64_default: ::std::option::Option<u64>,
        pub u64_0: ::std::option::Option<u64>,
        pub u64_42: ::std::option::Option<u64>,
        pub u64_18446744073709551615: ::std::option::Option<u64>,
        pub u64_0123: ::std::option::Option<u64>,
        pub u64_0x123: ::std::option::Option<u64>,
        pub f32_default: ::std::option::Option<f32>,
        pub f32_0: ::std::option::Option<f32>,
        pub f32_m0: ::std::option::Option<f32>,
        pub f32_0p: ::std::option::Option<f32>,
        pub f32_p0: ::std::option::Option<f32>,
        pub f32_0p0: ::std::option::Option<f32>,
        pub f32_42: ::std::option::Option<f32>,
        pub f32_m42: ::std::option::Option<f32>,
        pub f32_0p25: ::std::option::Option<f32>,
        pub f32_1p5e2: ::std::option::Option<f32>,
        pub f32_inf: ::std::option::Option<f32>,
        pub f32_minf: ::std::option::Option<f32>,
        pub f32_nan: ::std::option::Option<f32>,
        pub f32_mnan: ::std::option::Option<f32>,
        pub bool_default: ::std::option::Option<bool>,
        pub bool_true: ::std::option::Option<bool>,
        pub bool_false: ::std::option::Option<bool>,
        pub string_default: ::std::option::Option<::std::string::String>,
        pub string_empty: ::std::option::Option<::std::string::String>,
        pub string_abc: ::std::option::Option<::std::string::String>,
        pub string_aiu: ::std::option::Option<::std::string::String>,
        pub string_backslash: ::std::option::Option<::std::string::String>,
        pub string_tab: ::std::option::Option<::std::string::String>,
        pub string_crlf: ::std::option::Option<::std::string::String>,
        pub bytes_default: ::std::option::Option<::std::vec::Vec<u8>>,
        pub bytes_empty: ::std::option::Option<::std::vec::Vec<u8>>,
        pub bytes_abc: ::std::option::Option<::std::vec::Vec<u8>>,
        pub bytes_aiu: ::std::option::Option<::std::vec::Vec<u8>>,
        pub bytes_backslash: ::std::option::Option<::std::vec::Vec<u8>>,
        pub bytes_tab: ::std::option::Option<::std::vec::Vec<u8>>,
        pub bytes_crlf: ::std::option::Option<::std::vec::Vec<u8>>,
        pub enum_default: ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum>,
        pub enum_one: ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum>,
        pub enum_fourty_two: ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum>,
    }
    impl ::puroro::Message<Msg> for Msg {}

    impl super::_puroro_traits::MsgTrait for Msg {
        fn i32_default_opt<'this>(&'this self) -> Option<i32> {
            Clone::clone(&self.i32_default)
        }
        fn i32_0_opt<'this>(&'this self) -> Option<i32> {
            Clone::clone(&self.i32_0)
        }
        fn i32_42_opt<'this>(&'this self) -> Option<i32> {
            Clone::clone(&self.i32_42)
        }
        fn i32_m42_opt<'this>(&'this self) -> Option<i32> {
            Clone::clone(&self.i32_m42)
        }
        fn i32_2147483647_opt<'this>(&'this self) -> Option<i32> {
            Clone::clone(&self.i32_2147483647)
        }
        fn i32_m2147483648_opt<'this>(&'this self) -> Option<i32> {
            Clone::clone(&self.i32_m2147483648)
        }
        fn i32_0123_opt<'this>(&'this self) -> Option<i32> {
            Clone::clone(&self.i32_0123)
        }
        fn i32_0x123_opt<'this>(&'this self) -> Option<i32> {
            Clone::clone(&self.i32_0x123)
        }
        fn u32_default_opt<'this>(&'this self) -> Option<u32> {
            Clone::clone(&self.u32_default)
        }
        fn u32_0_opt<'this>(&'this self) -> Option<u32> {
            Clone::clone(&self.u32_0)
        }
        fn u32_42_opt<'this>(&'this self) -> Option<u32> {
            Clone::clone(&self.u32_42)
        }
        fn u32_4294967295_opt<'this>(&'this self) -> Option<u32> {
            Clone::clone(&self.u32_4294967295)
        }
        fn u32_0123_opt<'this>(&'this self) -> Option<u32> {
            Clone::clone(&self.u32_0123)
        }
        fn u32_0x123_opt<'this>(&'this self) -> Option<u32> {
            Clone::clone(&self.u32_0x123)
        }
        fn i64_default_opt<'this>(&'this self) -> Option<i64> {
            Clone::clone(&self.i64_default)
        }
        fn i64_0_opt<'this>(&'this self) -> Option<i64> {
            Clone::clone(&self.i64_0)
        }
        fn i64_42_opt<'this>(&'this self) -> Option<i64> {
            Clone::clone(&self.i64_42)
        }
        fn i64_m42_opt<'this>(&'this self) -> Option<i64> {
            Clone::clone(&self.i64_m42)
        }
        fn i64_9223372036854775807_opt<'this>(&'this self) -> Option<i64> {
            Clone::clone(&self.i64_9223372036854775807)
        }
        fn i64_m9223372036854775808_opt<'this>(&'this self) -> Option<i64> {
            Clone::clone(&self.i64_m9223372036854775808)
        }
        fn i64_0123_opt<'this>(&'this self) -> Option<i64> {
            Clone::clone(&self.i64_0123)
        }
        fn i64_0x123_opt<'this>(&'this self) -> Option<i64> {
            Clone::clone(&self.i64_0x123)
        }
        fn u64_default_opt<'this>(&'this self) -> Option<u64> {
            Clone::clone(&self.u64_default)
        }
        fn u64_0_opt<'this>(&'this self) -> Option<u64> {
            Clone::clone(&self.u64_0)
        }
        fn u64_42_opt<'this>(&'this self) -> Option<u64> {
            Clone::clone(&self.u64_42)
        }
        fn u64_18446744073709551615_opt<'this>(&'this self) -> Option<u64> {
            Clone::clone(&self.u64_18446744073709551615)
        }
        fn u64_0123_opt<'this>(&'this self) -> Option<u64> {
            Clone::clone(&self.u64_0123)
        }
        fn u64_0x123_opt<'this>(&'this self) -> Option<u64> {
            Clone::clone(&self.u64_0x123)
        }
        fn f32_default_opt<'this>(&'this self) -> Option<f32> {
            Clone::clone(&self.f32_default)
        }
        fn f32_0_opt<'this>(&'this self) -> Option<f32> {
            Clone::clone(&self.f32_0)
        }
        fn f32_m0_opt<'this>(&'this self) -> Option<f32> {
            Clone::clone(&self.f32_m0)
        }
        fn f32_0p_opt<'this>(&'this self) -> Option<f32> {
            Clone::clone(&self.f32_0p)
        }
        fn f32_p0_opt<'this>(&'this self) -> Option<f32> {
            Clone::clone(&self.f32_p0)
        }
        fn f32_0p0_opt<'this>(&'this self) -> Option<f32> {
            Clone::clone(&self.f32_0p0)
        }
        fn f32_42_opt<'this>(&'this self) -> Option<f32> {
            Clone::clone(&self.f32_42)
        }
        fn f32_m42_opt<'this>(&'this self) -> Option<f32> {
            Clone::clone(&self.f32_m42)
        }
        fn f32_0p25_opt<'this>(&'this self) -> Option<f32> {
            Clone::clone(&self.f32_0p25)
        }
        fn f32_1p5e2_opt<'this>(&'this self) -> Option<f32> {
            Clone::clone(&self.f32_1p5e2)
        }
        fn f32_inf_opt<'this>(&'this self) -> Option<f32> {
            Clone::clone(&self.f32_inf)
        }
        fn f32_minf_opt<'this>(&'this self) -> Option<f32> {
            Clone::clone(&self.f32_minf)
        }
        fn f32_nan_opt<'this>(&'this self) -> Option<f32> {
            Clone::clone(&self.f32_nan)
        }
        fn f32_mnan_opt<'this>(&'this self) -> Option<f32> {
            Clone::clone(&self.f32_mnan)
        }
        fn bool_default_opt<'this>(&'this self) -> Option<bool> {
            Clone::clone(&self.bool_default)
        }
        fn bool_true_opt<'this>(&'this self) -> Option<bool> {
            Clone::clone(&self.bool_true)
        }
        fn bool_false_opt<'this>(&'this self) -> Option<bool> {
            Clone::clone(&self.bool_false)
        }
        fn string_default_opt<'this>(&'this self) -> Option<&'this str> {
            self.string_default.as_ref().map(|v| v.as_ref())
        }
        fn string_empty_opt<'this>(&'this self) -> Option<&'this str> {
            self.string_empty.as_ref().map(|v| v.as_ref())
        }
        fn string_abc_opt<'this>(&'this self) -> Option<&'this str> {
            self.string_abc.as_ref().map(|v| v.as_ref())
        }
        fn string_aiu_opt<'this>(&'this self) -> Option<&'this str> {
            self.string_aiu.as_ref().map(|v| v.as_ref())
        }
        fn string_backslash_opt<'this>(&'this self) -> Option<&'this str> {
            self.string_backslash.as_ref().map(|v| v.as_ref())
        }
        fn string_tab_opt<'this>(&'this self) -> Option<&'this str> {
            self.string_tab.as_ref().map(|v| v.as_ref())
        }
        fn string_crlf_opt<'this>(&'this self) -> Option<&'this str> {
            self.string_crlf.as_ref().map(|v| v.as_ref())
        }
        fn bytes_default_opt<'this>(&'this self) -> Option<&'this [u8]> {
            self.bytes_default.as_ref().map(|v| v.as_ref())
        }
        fn bytes_empty_opt<'this>(&'this self) -> Option<&'this [u8]> {
            self.bytes_empty.as_ref().map(|v| v.as_ref())
        }
        fn bytes_abc_opt<'this>(&'this self) -> Option<&'this [u8]> {
            self.bytes_abc.as_ref().map(|v| v.as_ref())
        }
        fn bytes_aiu_opt<'this>(&'this self) -> Option<&'this [u8]> {
            self.bytes_aiu.as_ref().map(|v| v.as_ref())
        }
        fn bytes_backslash_opt<'this>(&'this self) -> Option<&'this [u8]> {
            self.bytes_backslash.as_ref().map(|v| v.as_ref())
        }
        fn bytes_tab_opt<'this>(&'this self) -> Option<&'this [u8]> {
            self.bytes_tab.as_ref().map(|v| v.as_ref())
        }
        fn bytes_crlf_opt<'this>(&'this self) -> Option<&'this [u8]> {
            self.bytes_crlf.as_ref().map(|v| v.as_ref())
        }
        fn enum_default_opt<'this>(
            &'this self,
        ) -> Option<self::_puroro_root::proto2_defaults::MyEnum> {
            Clone::clone(&self.enum_default)
        }
        fn enum_one_opt<'this>(&'this self) -> Option<self::_puroro_root::proto2_defaults::MyEnum> {
            Clone::clone(&self.enum_one)
        }
        fn enum_fourty_two_opt<'this>(
            &'this self,
        ) -> Option<self::_puroro_root::proto2_defaults::MyEnum> {
            Clone::clone(&self.enum_fourty_two)
        }
    }

    impl ::puroro::MessageRepresentativeImpl for Msg {
        fn descriptor() -> &'static ::puroro::desc::MessageDescriptor {
            use ::puroro::once_cell::sync::Lazy;
            static LAZY_FIELD_DESCRIPTOR_ARRAY: Lazy<[::puroro::desc::FieldDescriptor; 62]> =
                Lazy::new(|| {
                    [
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i32_default",
                                number: 1,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i32_0",
                                number: 2,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i32_42",
                                number: 3,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i32_m42",
                                number: 4,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i32_2147483647",
                                number: 5,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i32_m2147483648",
                                number: 6,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i32_0123",
                                number: 7,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i32_0x123",
                                number: 8,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u32_default",
                                number: 11,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u32_0",
                                number: 12,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u32_42",
                                number: 13,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u32_4294967295",
                                number: 15,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u32_0123",
                                number: 17,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u32_0x123",
                                number: 18,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i64_default",
                                number: 21,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i64_0",
                                number: 22,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i64_42",
                                number: 23,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i64_m42",
                                number: 24,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i64_9223372036854775807",
                                number: 25,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i64_m9223372036854775808",
                                number: 26,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i64_0123",
                                number: 27,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "i64_0x123",
                                number: 28,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u64_default",
                                number: 31,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u64_0",
                                number: 32,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u64_42",
                                number: 33,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u64_18446744073709551615",
                                number: 35,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u64_0123",
                                number: 37,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "u64_0x123",
                                number: 38,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "f32_default",
                                number: 41,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "f32_0",
                                number: 42,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "f32_m0",
                                number: 43,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "f32_0p",
                                number: 44,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "f32_p0",
                                number: 45,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "f32_0p0",
                                number: 46,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "f32_42",
                                number: 47,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "f32_m42",
                                number: 48,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "f32_0p25",
                                number: 49,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "f32_1p5e2",
                                number: 50,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "f32_inf",
                                number: 51,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "f32_minf",
                                number: 52,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "f32_nan",
                                number: 53,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "f32_mnan",
                                number: 54,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "bool_default",
                                number: 61,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "bool_true",
                                number: 62,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "bool_false",
                                number: 63,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "string_default",
                                number: 71,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "string_empty",
                                number: 72,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "string_abc",
                                number: 73,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "string_aiu",
                                number: 74,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "string_backslash",
                                number: 75,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "string_tab",
                                number: 76,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "string_crlf",
                                number: 77,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "bytes_default",
                                number: 81,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "bytes_empty",
                                number: 82,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "bytes_abc",
                                number: 83,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "bytes_aiu",
                                number: 84,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "bytes_backslash",
                                number: 85,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "bytes_tab",
                                number: 86,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "bytes_crlf",
                                number: 87,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "enum_default",
                                number: 91,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "enum_one",
                                number: 92,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
                                }),
                            };
                            ::puroro::internal::init_field_descriptor(init)
                        },
                        {
                            let init = ::puroro::internal::FieldDescriptorInitializer {
                                name: "enum_fourty_two",
                                number: 93,
                                lazy_containing_type: Lazy::new(|| {
                                    <Msg as ::puroro::MessageRepresentativeImpl>::descriptor()
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

    impl ::puroro::internal::DeserializableMessageFromBytesIterator for Msg {
        fn deser<I>(&mut self, iter: I) -> ::puroro::Result<()>
        where
            I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>,
        {
            ::puroro::internal::de::from_iter::deser_from_iter(self, iter)
        }
    }

    impl ::puroro::internal::de::DeserFieldsFromBytesIter for Msg {
        fn deser_field<I>(
            &mut self,
            field_number: i32,
            data: ::puroro::internal::types::FieldData<
                &mut ::puroro::internal::de::from_iter::ScopedIter<I>,
            >,
        ) -> ::puroro::Result<()>
        where
            I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>,
        {
            use ::puroro::internal::impls::simple::de::DeserFieldFromBytesIter;
            match field_number {
            1 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int32
            >::deser_field(&mut self.i32_default, data),
            2 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int32
            >::deser_field(&mut self.i32_0, data),
            3 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int32
            >::deser_field(&mut self.i32_42, data),
            4 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int32
            >::deser_field(&mut self.i32_m42, data),
            5 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int32
            >::deser_field(&mut self.i32_2147483647, data),
            6 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int32
            >::deser_field(&mut self.i32_m2147483648, data),
            7 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int32
            >::deser_field(&mut self.i32_0123, data),
            8 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int32
            >::deser_field(&mut self.i32_0x123, data),
            11 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::UInt32
            >::deser_field(&mut self.u32_default, data),
            12 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::UInt32
            >::deser_field(&mut self.u32_0, data),
            13 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::UInt32
            >::deser_field(&mut self.u32_42, data),
            15 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::UInt32
            >::deser_field(&mut self.u32_4294967295, data),
            17 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::UInt32
            >::deser_field(&mut self.u32_0123, data),
            18 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::UInt32
            >::deser_field(&mut self.u32_0x123, data),
            21 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int64
            >::deser_field(&mut self.i64_default, data),
            22 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int64
            >::deser_field(&mut self.i64_0, data),
            23 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int64
            >::deser_field(&mut self.i64_42, data),
            24 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int64
            >::deser_field(&mut self.i64_m42, data),
            25 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int64
            >::deser_field(&mut self.i64_9223372036854775807, data),
            26 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int64
            >::deser_field(&mut self.i64_m9223372036854775808, data),
            27 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int64
            >::deser_field(&mut self.i64_0123, data),
            28 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Int64
            >::deser_field(&mut self.i64_0x123, data),
            31 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::UInt64
            >::deser_field(&mut self.u64_default, data),
            32 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::UInt64
            >::deser_field(&mut self.u64_0, data),
            33 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::UInt64
            >::deser_field(&mut self.u64_42, data),
            35 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::UInt64
            >::deser_field(&mut self.u64_18446744073709551615, data),
            37 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::UInt64
            >::deser_field(&mut self.u64_0123, data),
            38 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::UInt64
            >::deser_field(&mut self.u64_0x123, data),
            41 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Float
            >::deser_field(&mut self.f32_default, data),
            42 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Float
            >::deser_field(&mut self.f32_0, data),
            43 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Float
            >::deser_field(&mut self.f32_m0, data),
            44 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Float
            >::deser_field(&mut self.f32_0p, data),
            45 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Float
            >::deser_field(&mut self.f32_p0, data),
            46 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Float
            >::deser_field(&mut self.f32_0p0, data),
            47 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Float
            >::deser_field(&mut self.f32_42, data),
            48 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Float
            >::deser_field(&mut self.f32_m42, data),
            49 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Float
            >::deser_field(&mut self.f32_0p25, data),
            50 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Float
            >::deser_field(&mut self.f32_1p5e2, data),
            51 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Float
            >::deser_field(&mut self.f32_inf, data),
            52 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Float
            >::deser_field(&mut self.f32_minf, data),
            53 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Float
            >::deser_field(&mut self.f32_nan, data),
            54 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Float
            >::deser_field(&mut self.f32_mnan, data),
            61 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Bool
            >::deser_field(&mut self.bool_default, data),
            62 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Bool
            >::deser_field(&mut self.bool_true, data),
            63 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Bool
            >::deser_field(&mut self.bool_false, data),
            71 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::String
            >::deser_field(&mut self.string_default, data),
            72 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::String
            >::deser_field(&mut self.string_empty, data),
            73 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::String
            >::deser_field(&mut self.string_abc, data),
            74 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::String
            >::deser_field(&mut self.string_aiu, data),
            75 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::String
            >::deser_field(&mut self.string_backslash, data),
            76 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::String
            >::deser_field(&mut self.string_tab, data),
            77 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::String
            >::deser_field(&mut self.string_crlf, data),
            81 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Bytes
            >::deser_field(&mut self.bytes_default, data),
            82 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Bytes
            >::deser_field(&mut self.bytes_empty, data),
            83 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Bytes
            >::deser_field(&mut self.bytes_abc, data),
            84 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Bytes
            >::deser_field(&mut self.bytes_aiu, data),
            85 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Bytes
            >::deser_field(&mut self.bytes_backslash, data),
            86 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Bytes
            >::deser_field(&mut self.bytes_tab, data),
            87 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Bytes
            >::deser_field(&mut self.bytes_crlf, data),
            91 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>
            >::deser_field(&mut self.enum_default, data),
            92 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>
            >::deser_field(&mut self.enum_one, data),
            93 => DeserFieldFromBytesIter::<
                ::puroro::tags::Optional, ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>
            >::deser_field(&mut self.enum_fourty_two, data),

            _ => unimplemented!("TODO: This case should be handled properly..."),
        }
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for Msg {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::simple::se::SerFieldToIoWrite;
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field(
                    &self.i32_default,
                    1,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::i32_0(self)
                != <() as super::_puroro_traits::MsgTrait>::i32_0(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field(
                    &self.i32_0,
                    2,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::i32_42(self)
                != <() as super::_puroro_traits::MsgTrait>::i32_42(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field(
                    &self.i32_42,
                    3,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::i32_m42(self)
                != <() as super::_puroro_traits::MsgTrait>::i32_m42(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field(
                    &self.i32_m42,
                    4,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::i32_2147483647(self)
                != <() as super::_puroro_traits::MsgTrait>::i32_2147483647(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field(
                    &self.i32_2147483647,
                    5,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::i32_m2147483648(self)
                != <() as super::_puroro_traits::MsgTrait>::i32_m2147483648(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field(
                    &self.i32_m2147483648,
                    6,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::i32_0123(self)
                != <() as super::_puroro_traits::MsgTrait>::i32_0123(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field(
                    &self.i32_0123,
                    7,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::i32_0x123(self)
                != <() as super::_puroro_traits::MsgTrait>::i32_0x123(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field(
                    &self.i32_0x123,
                    8,
                    out,
                )?;
            }
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt32>::ser_field(
                    &self.u32_default,
                    11,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::u32_0(self)
                != <() as super::_puroro_traits::MsgTrait>::u32_0(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt32>::ser_field(
                    &self.u32_0,
                    12,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::u32_42(self)
                != <() as super::_puroro_traits::MsgTrait>::u32_42(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt32>::ser_field(
                    &self.u32_42,
                    13,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::u32_4294967295(self)
                != <() as super::_puroro_traits::MsgTrait>::u32_4294967295(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt32>::ser_field(
                    &self.u32_4294967295,
                    15,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::u32_0123(self)
                != <() as super::_puroro_traits::MsgTrait>::u32_0123(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt32>::ser_field(
                    &self.u32_0123,
                    17,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::u32_0x123(self)
                != <() as super::_puroro_traits::MsgTrait>::u32_0x123(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt32>::ser_field(
                    &self.u32_0x123,
                    18,
                    out,
                )?;
            }
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field(
                    &self.i64_default,
                    21,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::i64_0(self)
                != <() as super::_puroro_traits::MsgTrait>::i64_0(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field(
                    &self.i64_0,
                    22,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::i64_42(self)
                != <() as super::_puroro_traits::MsgTrait>::i64_42(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field(
                    &self.i64_42,
                    23,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::i64_m42(self)
                != <() as super::_puroro_traits::MsgTrait>::i64_m42(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field(
                    &self.i64_m42,
                    24,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::i64_9223372036854775807(self)
                != <() as super::_puroro_traits::MsgTrait>::i64_9223372036854775807(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field(
                    &self.i64_9223372036854775807,
                    25,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::i64_m9223372036854775808(self)
                != <() as super::_puroro_traits::MsgTrait>::i64_m9223372036854775808(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field(
                    &self.i64_m9223372036854775808,
                    26,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::i64_0123(self)
                != <() as super::_puroro_traits::MsgTrait>::i64_0123(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field(
                    &self.i64_0123,
                    27,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::i64_0x123(self)
                != <() as super::_puroro_traits::MsgTrait>::i64_0x123(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field(
                    &self.i64_0x123,
                    28,
                    out,
                )?;
            }
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt64>::ser_field(
                    &self.u64_default,
                    31,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::u64_0(self)
                != <() as super::_puroro_traits::MsgTrait>::u64_0(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt64>::ser_field(
                    &self.u64_0,
                    32,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::u64_42(self)
                != <() as super::_puroro_traits::MsgTrait>::u64_42(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt64>::ser_field(
                    &self.u64_42,
                    33,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::u64_18446744073709551615(self)
                != <() as super::_puroro_traits::MsgTrait>::u64_18446744073709551615(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt64>::ser_field(
                    &self.u64_18446744073709551615,
                    35,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::u64_0123(self)
                != <() as super::_puroro_traits::MsgTrait>::u64_0123(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt64>::ser_field(
                    &self.u64_0123,
                    37,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::u64_0x123(self)
                != <() as super::_puroro_traits::MsgTrait>::u64_0x123(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt64>::ser_field(
                    &self.u64_0x123,
                    38,
                    out,
                )?;
            }
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field(
                    &self.f32_default,
                    41,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::f32_0(self)
                != <() as super::_puroro_traits::MsgTrait>::f32_0(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field(
                    &self.f32_0,
                    42,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::f32_m0(self)
                != <() as super::_puroro_traits::MsgTrait>::f32_m0(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field(
                    &self.f32_m0,
                    43,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::f32_0p(self)
                != <() as super::_puroro_traits::MsgTrait>::f32_0p(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field(
                    &self.f32_0p,
                    44,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::f32_p0(self)
                != <() as super::_puroro_traits::MsgTrait>::f32_p0(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field(
                    &self.f32_p0,
                    45,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::f32_0p0(self)
                != <() as super::_puroro_traits::MsgTrait>::f32_0p0(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field(
                    &self.f32_0p0,
                    46,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::f32_42(self)
                != <() as super::_puroro_traits::MsgTrait>::f32_42(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field(
                    &self.f32_42,
                    47,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::f32_m42(self)
                != <() as super::_puroro_traits::MsgTrait>::f32_m42(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field(
                    &self.f32_m42,
                    48,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::f32_0p25(self)
                != <() as super::_puroro_traits::MsgTrait>::f32_0p25(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field(
                    &self.f32_0p25,
                    49,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::f32_1p5e2(self)
                != <() as super::_puroro_traits::MsgTrait>::f32_1p5e2(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field(
                    &self.f32_1p5e2,
                    50,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::f32_inf(self)
                != <() as super::_puroro_traits::MsgTrait>::f32_inf(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field(
                    &self.f32_inf,
                    51,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::f32_minf(self)
                != <() as super::_puroro_traits::MsgTrait>::f32_minf(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field(
                    &self.f32_minf,
                    52,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::f32_nan(self)
                != <() as super::_puroro_traits::MsgTrait>::f32_nan(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field(
                    &self.f32_nan,
                    53,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::f32_mnan(self)
                != <() as super::_puroro_traits::MsgTrait>::f32_mnan(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field(
                    &self.f32_mnan,
                    54,
                    out,
                )?;
            }
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bool>::ser_field(
                    &self.bool_default,
                    61,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::bool_true(self)
                != <() as super::_puroro_traits::MsgTrait>::bool_true(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bool>::ser_field(
                    &self.bool_true,
                    62,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::bool_false(self)
                != <() as super::_puroro_traits::MsgTrait>::bool_false(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bool>::ser_field(
                    &self.bool_false,
                    63,
                    out,
                )?;
            }
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::String>::ser_field(
                    &self.string_default,
                    71,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::string_empty(self)
                != <() as super::_puroro_traits::MsgTrait>::string_empty(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::String>::ser_field(
                    &self.string_empty,
                    72,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::string_abc(self)
                != <() as super::_puroro_traits::MsgTrait>::string_abc(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::String>::ser_field(
                    &self.string_abc,
                    73,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::string_aiu(self)
                != <() as super::_puroro_traits::MsgTrait>::string_aiu(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::String>::ser_field(
                    &self.string_aiu,
                    74,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::string_backslash(self)
                != <() as super::_puroro_traits::MsgTrait>::string_backslash(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::String>::ser_field(
                    &self.string_backslash,
                    75,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::string_tab(self)
                != <() as super::_puroro_traits::MsgTrait>::string_tab(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::String>::ser_field(
                    &self.string_tab,
                    76,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::string_crlf(self)
                != <() as super::_puroro_traits::MsgTrait>::string_crlf(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::String>::ser_field(
                    &self.string_crlf,
                    77,
                    out,
                )?;
            }
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bytes>::ser_field(
                    &self.bytes_default,
                    81,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::bytes_empty(self)
                != <() as super::_puroro_traits::MsgTrait>::bytes_empty(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bytes>::ser_field(
                    &self.bytes_empty,
                    82,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::bytes_abc(self)
                != <() as super::_puroro_traits::MsgTrait>::bytes_abc(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bytes>::ser_field(
                    &self.bytes_abc,
                    83,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::bytes_aiu(self)
                != <() as super::_puroro_traits::MsgTrait>::bytes_aiu(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bytes>::ser_field(
                    &self.bytes_aiu,
                    84,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::bytes_backslash(self)
                != <() as super::_puroro_traits::MsgTrait>::bytes_backslash(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bytes>::ser_field(
                    &self.bytes_backslash,
                    85,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::bytes_tab(self)
                != <() as super::_puroro_traits::MsgTrait>::bytes_tab(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bytes>::ser_field(
                    &self.bytes_tab,
                    86,
                    out,
                )?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::bytes_crlf(self)
                != <() as super::_puroro_traits::MsgTrait>::bytes_crlf(&())
            {
                SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bytes>::ser_field(
                    &self.bytes_crlf,
                    87,
                    out,
                )?;
            }
            {
                SerFieldToIoWrite::<
                    ::puroro::tags::Optional,
                    ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>,
                >::ser_field(&self.enum_default, 91, out)?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::enum_one(self)
                != <() as super::_puroro_traits::MsgTrait>::enum_one(&())
            {
                SerFieldToIoWrite::<
                    ::puroro::tags::Optional,
                    ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>,
                >::ser_field(&self.enum_one, 92, out)?;
            }
            if <Self as super::_puroro_traits::MsgTrait>::enum_fourty_two(self)
                != <() as super::_puroro_traits::MsgTrait>::enum_fourty_two(&())
            {
                SerFieldToIoWrite::<
                    ::puroro::tags::Optional,
                    ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>,
                >::ser_field(&self.enum_fourty_two, 93, out)?;
            }

            ::std::result::Result::Ok(())
        }
    }

    impl ::std::default::Default for Msg {
        fn default() -> Self {
            Self {
                i32_default: ::std::default::Default::default(),
                i32_0: ::std::option::Option::Some(0),
                i32_42: ::std::option::Option::Some(42),
                i32_m42: ::std::option::Option::Some(-42),
                i32_2147483647: ::std::option::Option::Some(2147483647),
                i32_m2147483648: ::std::option::Option::Some(-2147483648),
                i32_0123: ::std::option::Option::Some(83),
                i32_0x123: ::std::option::Option::Some(291),
                u32_default: ::std::default::Default::default(),
                u32_0: ::std::option::Option::Some(0),
                u32_42: ::std::option::Option::Some(42),
                u32_4294967295: ::std::option::Option::Some(4294967295),
                u32_0123: ::std::option::Option::Some(83),
                u32_0x123: ::std::option::Option::Some(291),
                i64_default: ::std::default::Default::default(),
                i64_0: ::std::option::Option::Some(0),
                i64_42: ::std::option::Option::Some(42),
                i64_m42: ::std::option::Option::Some(-42),
                i64_9223372036854775807: ::std::option::Option::Some(9223372036854775807),
                i64_m9223372036854775808: ::std::option::Option::Some(-9223372036854775808),
                i64_0123: ::std::option::Option::Some(83),
                i64_0x123: ::std::option::Option::Some(291),
                u64_default: ::std::default::Default::default(),
                u64_0: ::std::option::Option::Some(0),
                u64_42: ::std::option::Option::Some(42),
                u64_18446744073709551615: ::std::option::Option::Some(18446744073709551615),
                u64_0123: ::std::option::Option::Some(83),
                u64_0x123: ::std::option::Option::Some(291),
                f32_default: ::std::default::Default::default(),
                f32_0: ::std::option::Option::Some(0f32),
                f32_m0: ::std::option::Option::Some(-0f32),
                f32_0p: ::std::option::Option::Some(0f32),
                f32_p0: ::std::option::Option::Some(0f32),
                f32_0p0: ::std::option::Option::Some(0f32),
                f32_42: ::std::option::Option::Some(42f32),
                f32_m42: ::std::option::Option::Some(-42f32),
                f32_0p25: ::std::option::Option::Some(0.25f32),
                f32_1p5e2: ::std::option::Option::Some(150f32),
                f32_inf: ::std::option::Option::Some(f32::INFINITY),
                f32_minf: ::std::option::Option::Some(f32::NEG_INFINITY),
                f32_nan: ::std::option::Option::Some(f32::NAN),
                f32_mnan: ::std::option::Option::Some(f32::NAN),
                bool_default: ::std::default::Default::default(),
                bool_true: ::std::option::Option::Some(true),
                bool_false: ::std::option::Option::Some(false),
                string_default: ::std::default::Default::default(),
                string_empty: ::std::option::Option::Some("".to_string()),
                string_abc: ::std::option::Option::Some("abc".to_string()),
                string_aiu: ::std::option::Option::Some("\u{3042}\u{3044}\u{3046}".to_string()),
                string_backslash: ::std::option::Option::Some("\\".to_string()),
                string_tab: ::std::option::Option::Some("\t".to_string()),
                string_crlf: ::std::option::Option::Some("\r\n".to_string()),
                bytes_default: ::std::default::Default::default(),
                bytes_empty: ::std::option::Option::Some(b"".to_vec()),
                bytes_abc: ::std::option::Option::Some(b"\x61\x62\x63".to_vec()),
                bytes_aiu: ::std::option::Option::Some(
                    b"\xe3\x81\x82\xe3\x81\x84\xe3\x81\x86".to_vec(),
                ),
                bytes_backslash: ::std::option::Option::Some(b"\x5c".to_vec()),
                bytes_tab: ::std::option::Option::Some(b"\x09".to_vec()),
                bytes_crlf: ::std::option::Option::Some(b"\x0d\x0a".to_vec()),
                enum_default: ::std::default::Default::default(),
                enum_one: ::std::option::Option::Some(
                    self::_puroro_root::proto2_defaults::MyEnum::One,
                ),
                enum_fourty_two: ::std::option::Option::Some(
                    self::_puroro_root::proto2_defaults::MyEnum::FourtyTwo,
                ),
            }
        }
    }
}

pub use _puroro_impls::*;
pub mod _puroro_impls {
    mod _puroro_root {
        pub use super::super::_puroro_root::*;
    }
    use super::_puroro_traits::*;
    impl MsgTrait for () {}
    impl<T, U> MsgTrait for (T, U)
    where
        T: MsgTrait,
        U: MsgTrait,
    {
        fn i32_default_opt<'this>(&'this self) -> Option<i32> {
            <U as MsgTrait>::i32_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i32_default_opt(&self.0))
        }
        fn i32_0_opt<'this>(&'this self) -> Option<i32> {
            <U as MsgTrait>::i32_0_opt(&self.1).or_else(|| <T as MsgTrait>::i32_0_opt(&self.0))
        }
        fn i32_42_opt<'this>(&'this self) -> Option<i32> {
            <U as MsgTrait>::i32_42_opt(&self.1).or_else(|| <T as MsgTrait>::i32_42_opt(&self.0))
        }
        fn i32_m42_opt<'this>(&'this self) -> Option<i32> {
            <U as MsgTrait>::i32_m42_opt(&self.1).or_else(|| <T as MsgTrait>::i32_m42_opt(&self.0))
        }
        fn i32_2147483647_opt<'this>(&'this self) -> Option<i32> {
            <U as MsgTrait>::i32_2147483647_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i32_2147483647_opt(&self.0))
        }
        fn i32_m2147483648_opt<'this>(&'this self) -> Option<i32> {
            <U as MsgTrait>::i32_m2147483648_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i32_m2147483648_opt(&self.0))
        }
        fn i32_0123_opt<'this>(&'this self) -> Option<i32> {
            <U as MsgTrait>::i32_0123_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i32_0123_opt(&self.0))
        }
        fn i32_0x123_opt<'this>(&'this self) -> Option<i32> {
            <U as MsgTrait>::i32_0x123_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i32_0x123_opt(&self.0))
        }
        fn u32_default_opt<'this>(&'this self) -> Option<u32> {
            <U as MsgTrait>::u32_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u32_default_opt(&self.0))
        }
        fn u32_0_opt<'this>(&'this self) -> Option<u32> {
            <U as MsgTrait>::u32_0_opt(&self.1).or_else(|| <T as MsgTrait>::u32_0_opt(&self.0))
        }
        fn u32_42_opt<'this>(&'this self) -> Option<u32> {
            <U as MsgTrait>::u32_42_opt(&self.1).or_else(|| <T as MsgTrait>::u32_42_opt(&self.0))
        }
        fn u32_4294967295_opt<'this>(&'this self) -> Option<u32> {
            <U as MsgTrait>::u32_4294967295_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u32_4294967295_opt(&self.0))
        }
        fn u32_0123_opt<'this>(&'this self) -> Option<u32> {
            <U as MsgTrait>::u32_0123_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u32_0123_opt(&self.0))
        }
        fn u32_0x123_opt<'this>(&'this self) -> Option<u32> {
            <U as MsgTrait>::u32_0x123_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u32_0x123_opt(&self.0))
        }
        fn i64_default_opt<'this>(&'this self) -> Option<i64> {
            <U as MsgTrait>::i64_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i64_default_opt(&self.0))
        }
        fn i64_0_opt<'this>(&'this self) -> Option<i64> {
            <U as MsgTrait>::i64_0_opt(&self.1).or_else(|| <T as MsgTrait>::i64_0_opt(&self.0))
        }
        fn i64_42_opt<'this>(&'this self) -> Option<i64> {
            <U as MsgTrait>::i64_42_opt(&self.1).or_else(|| <T as MsgTrait>::i64_42_opt(&self.0))
        }
        fn i64_m42_opt<'this>(&'this self) -> Option<i64> {
            <U as MsgTrait>::i64_m42_opt(&self.1).or_else(|| <T as MsgTrait>::i64_m42_opt(&self.0))
        }
        fn i64_9223372036854775807_opt<'this>(&'this self) -> Option<i64> {
            <U as MsgTrait>::i64_9223372036854775807_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i64_9223372036854775807_opt(&self.0))
        }
        fn i64_m9223372036854775808_opt<'this>(&'this self) -> Option<i64> {
            <U as MsgTrait>::i64_m9223372036854775808_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i64_m9223372036854775808_opt(&self.0))
        }
        fn i64_0123_opt<'this>(&'this self) -> Option<i64> {
            <U as MsgTrait>::i64_0123_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i64_0123_opt(&self.0))
        }
        fn i64_0x123_opt<'this>(&'this self) -> Option<i64> {
            <U as MsgTrait>::i64_0x123_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i64_0x123_opt(&self.0))
        }
        fn u64_default_opt<'this>(&'this self) -> Option<u64> {
            <U as MsgTrait>::u64_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u64_default_opt(&self.0))
        }
        fn u64_0_opt<'this>(&'this self) -> Option<u64> {
            <U as MsgTrait>::u64_0_opt(&self.1).or_else(|| <T as MsgTrait>::u64_0_opt(&self.0))
        }
        fn u64_42_opt<'this>(&'this self) -> Option<u64> {
            <U as MsgTrait>::u64_42_opt(&self.1).or_else(|| <T as MsgTrait>::u64_42_opt(&self.0))
        }
        fn u64_18446744073709551615_opt<'this>(&'this self) -> Option<u64> {
            <U as MsgTrait>::u64_18446744073709551615_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u64_18446744073709551615_opt(&self.0))
        }
        fn u64_0123_opt<'this>(&'this self) -> Option<u64> {
            <U as MsgTrait>::u64_0123_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u64_0123_opt(&self.0))
        }
        fn u64_0x123_opt<'this>(&'this self) -> Option<u64> {
            <U as MsgTrait>::u64_0x123_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u64_0x123_opt(&self.0))
        }
        fn f32_default_opt<'this>(&'this self) -> Option<f32> {
            <U as MsgTrait>::f32_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_default_opt(&self.0))
        }
        fn f32_0_opt<'this>(&'this self) -> Option<f32> {
            <U as MsgTrait>::f32_0_opt(&self.1).or_else(|| <T as MsgTrait>::f32_0_opt(&self.0))
        }
        fn f32_m0_opt<'this>(&'this self) -> Option<f32> {
            <U as MsgTrait>::f32_m0_opt(&self.1).or_else(|| <T as MsgTrait>::f32_m0_opt(&self.0))
        }
        fn f32_0p_opt<'this>(&'this self) -> Option<f32> {
            <U as MsgTrait>::f32_0p_opt(&self.1).or_else(|| <T as MsgTrait>::f32_0p_opt(&self.0))
        }
        fn f32_p0_opt<'this>(&'this self) -> Option<f32> {
            <U as MsgTrait>::f32_p0_opt(&self.1).or_else(|| <T as MsgTrait>::f32_p0_opt(&self.0))
        }
        fn f32_0p0_opt<'this>(&'this self) -> Option<f32> {
            <U as MsgTrait>::f32_0p0_opt(&self.1).or_else(|| <T as MsgTrait>::f32_0p0_opt(&self.0))
        }
        fn f32_42_opt<'this>(&'this self) -> Option<f32> {
            <U as MsgTrait>::f32_42_opt(&self.1).or_else(|| <T as MsgTrait>::f32_42_opt(&self.0))
        }
        fn f32_m42_opt<'this>(&'this self) -> Option<f32> {
            <U as MsgTrait>::f32_m42_opt(&self.1).or_else(|| <T as MsgTrait>::f32_m42_opt(&self.0))
        }
        fn f32_0p25_opt<'this>(&'this self) -> Option<f32> {
            <U as MsgTrait>::f32_0p25_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_0p25_opt(&self.0))
        }
        fn f32_1p5e2_opt<'this>(&'this self) -> Option<f32> {
            <U as MsgTrait>::f32_1p5e2_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_1p5e2_opt(&self.0))
        }
        fn f32_inf_opt<'this>(&'this self) -> Option<f32> {
            <U as MsgTrait>::f32_inf_opt(&self.1).or_else(|| <T as MsgTrait>::f32_inf_opt(&self.0))
        }
        fn f32_minf_opt<'this>(&'this self) -> Option<f32> {
            <U as MsgTrait>::f32_minf_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_minf_opt(&self.0))
        }
        fn f32_nan_opt<'this>(&'this self) -> Option<f32> {
            <U as MsgTrait>::f32_nan_opt(&self.1).or_else(|| <T as MsgTrait>::f32_nan_opt(&self.0))
        }
        fn f32_mnan_opt<'this>(&'this self) -> Option<f32> {
            <U as MsgTrait>::f32_mnan_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_mnan_opt(&self.0))
        }
        fn bool_default_opt<'this>(&'this self) -> Option<bool> {
            <U as MsgTrait>::bool_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bool_default_opt(&self.0))
        }
        fn bool_true_opt<'this>(&'this self) -> Option<bool> {
            <U as MsgTrait>::bool_true_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bool_true_opt(&self.0))
        }
        fn bool_false_opt<'this>(&'this self) -> Option<bool> {
            <U as MsgTrait>::bool_false_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bool_false_opt(&self.0))
        }
        fn string_default_opt<'this>(&'this self) -> Option<&'this str> {
            <U as MsgTrait>::string_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::string_default_opt(&self.0))
        }
        fn string_empty_opt<'this>(&'this self) -> Option<&'this str> {
            <U as MsgTrait>::string_empty_opt(&self.1)
                .or_else(|| <T as MsgTrait>::string_empty_opt(&self.0))
        }
        fn string_abc_opt<'this>(&'this self) -> Option<&'this str> {
            <U as MsgTrait>::string_abc_opt(&self.1)
                .or_else(|| <T as MsgTrait>::string_abc_opt(&self.0))
        }
        fn string_aiu_opt<'this>(&'this self) -> Option<&'this str> {
            <U as MsgTrait>::string_aiu_opt(&self.1)
                .or_else(|| <T as MsgTrait>::string_aiu_opt(&self.0))
        }
        fn string_backslash_opt<'this>(&'this self) -> Option<&'this str> {
            <U as MsgTrait>::string_backslash_opt(&self.1)
                .or_else(|| <T as MsgTrait>::string_backslash_opt(&self.0))
        }
        fn string_tab_opt<'this>(&'this self) -> Option<&'this str> {
            <U as MsgTrait>::string_tab_opt(&self.1)
                .or_else(|| <T as MsgTrait>::string_tab_opt(&self.0))
        }
        fn string_crlf_opt<'this>(&'this self) -> Option<&'this str> {
            <U as MsgTrait>::string_crlf_opt(&self.1)
                .or_else(|| <T as MsgTrait>::string_crlf_opt(&self.0))
        }
        fn bytes_default_opt<'this>(&'this self) -> Option<&'this [u8]> {
            <U as MsgTrait>::bytes_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bytes_default_opt(&self.0))
        }
        fn bytes_empty_opt<'this>(&'this self) -> Option<&'this [u8]> {
            <U as MsgTrait>::bytes_empty_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bytes_empty_opt(&self.0))
        }
        fn bytes_abc_opt<'this>(&'this self) -> Option<&'this [u8]> {
            <U as MsgTrait>::bytes_abc_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bytes_abc_opt(&self.0))
        }
        fn bytes_aiu_opt<'this>(&'this self) -> Option<&'this [u8]> {
            <U as MsgTrait>::bytes_aiu_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bytes_aiu_opt(&self.0))
        }
        fn bytes_backslash_opt<'this>(&'this self) -> Option<&'this [u8]> {
            <U as MsgTrait>::bytes_backslash_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bytes_backslash_opt(&self.0))
        }
        fn bytes_tab_opt<'this>(&'this self) -> Option<&'this [u8]> {
            <U as MsgTrait>::bytes_tab_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bytes_tab_opt(&self.0))
        }
        fn bytes_crlf_opt<'this>(&'this self) -> Option<&'this [u8]> {
            <U as MsgTrait>::bytes_crlf_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bytes_crlf_opt(&self.0))
        }
        fn enum_default_opt<'this>(
            &'this self,
        ) -> Option<self::_puroro_root::proto2_defaults::MyEnum> {
            <U as MsgTrait>::enum_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::enum_default_opt(&self.0))
        }
        fn enum_one_opt<'this>(&'this self) -> Option<self::_puroro_root::proto2_defaults::MyEnum> {
            <U as MsgTrait>::enum_one_opt(&self.1)
                .or_else(|| <T as MsgTrait>::enum_one_opt(&self.0))
        }
        fn enum_fourty_two_opt<'this>(
            &'this self,
        ) -> Option<self::_puroro_root::proto2_defaults::MyEnum> {
            <U as MsgTrait>::enum_fourty_two_opt(&self.1)
                .or_else(|| <T as MsgTrait>::enum_fourty_two_opt(&self.0))
        }
    }
    impl<T, U> MsgTrait for ::puroro::Either<T, U>
    where
        T: MsgTrait,
        U: MsgTrait,
    {
        fn i32_default_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_default_opt(t),
                |u| <U as MsgTrait>::i32_default_opt(u),
            )
        }
        fn i32_0_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_0_opt(t),
                |u| <U as MsgTrait>::i32_0_opt(u),
            )
        }
        fn i32_42_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_42_opt(t),
                |u| <U as MsgTrait>::i32_42_opt(u),
            )
        }
        fn i32_m42_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_m42_opt(t),
                |u| <U as MsgTrait>::i32_m42_opt(u),
            )
        }
        fn i32_2147483647_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_2147483647_opt(t),
                |u| <U as MsgTrait>::i32_2147483647_opt(u),
            )
        }
        fn i32_m2147483648_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_m2147483648_opt(t),
                |u| <U as MsgTrait>::i32_m2147483648_opt(u),
            )
        }
        fn i32_0123_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_0123_opt(t),
                |u| <U as MsgTrait>::i32_0123_opt(u),
            )
        }
        fn i32_0x123_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_0x123_opt(t),
                |u| <U as MsgTrait>::i32_0x123_opt(u),
            )
        }
        fn u32_default_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::u32_default_opt(t),
                |u| <U as MsgTrait>::u32_default_opt(u),
            )
        }
        fn u32_0_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::u32_0_opt(t),
                |u| <U as MsgTrait>::u32_0_opt(u),
            )
        }
        fn u32_42_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::u32_42_opt(t),
                |u| <U as MsgTrait>::u32_42_opt(u),
            )
        }
        fn u32_4294967295_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::u32_4294967295_opt(t),
                |u| <U as MsgTrait>::u32_4294967295_opt(u),
            )
        }
        fn u32_0123_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::u32_0123_opt(t),
                |u| <U as MsgTrait>::u32_0123_opt(u),
            )
        }
        fn u32_0x123_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::u32_0x123_opt(t),
                |u| <U as MsgTrait>::u32_0x123_opt(u),
            )
        }
        fn i64_default_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_default_opt(t),
                |u| <U as MsgTrait>::i64_default_opt(u),
            )
        }
        fn i64_0_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_0_opt(t),
                |u| <U as MsgTrait>::i64_0_opt(u),
            )
        }
        fn i64_42_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_42_opt(t),
                |u| <U as MsgTrait>::i64_42_opt(u),
            )
        }
        fn i64_m42_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_m42_opt(t),
                |u| <U as MsgTrait>::i64_m42_opt(u),
            )
        }
        fn i64_9223372036854775807_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_9223372036854775807_opt(t),
                |u| <U as MsgTrait>::i64_9223372036854775807_opt(u),
            )
        }
        fn i64_m9223372036854775808_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_m9223372036854775808_opt(t),
                |u| <U as MsgTrait>::i64_m9223372036854775808_opt(u),
            )
        }
        fn i64_0123_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_0123_opt(t),
                |u| <U as MsgTrait>::i64_0123_opt(u),
            )
        }
        fn i64_0x123_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_0x123_opt(t),
                |u| <U as MsgTrait>::i64_0x123_opt(u),
            )
        }
        fn u64_default_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::u64_default_opt(t),
                |u| <U as MsgTrait>::u64_default_opt(u),
            )
        }
        fn u64_0_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::u64_0_opt(t),
                |u| <U as MsgTrait>::u64_0_opt(u),
            )
        }
        fn u64_42_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::u64_42_opt(t),
                |u| <U as MsgTrait>::u64_42_opt(u),
            )
        }
        fn u64_18446744073709551615_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::u64_18446744073709551615_opt(t),
                |u| <U as MsgTrait>::u64_18446744073709551615_opt(u),
            )
        }
        fn u64_0123_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::u64_0123_opt(t),
                |u| <U as MsgTrait>::u64_0123_opt(u),
            )
        }
        fn u64_0x123_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            self.as_ref().either(
                |t| <T as MsgTrait>::u64_0x123_opt(t),
                |u| <U as MsgTrait>::u64_0x123_opt(u),
            )
        }
        fn f32_default_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_default_opt(t),
                |u| <U as MsgTrait>::f32_default_opt(u),
            )
        }
        fn f32_0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_0_opt(t),
                |u| <U as MsgTrait>::f32_0_opt(u),
            )
        }
        fn f32_m0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_m0_opt(t),
                |u| <U as MsgTrait>::f32_m0_opt(u),
            )
        }
        fn f32_0p_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_0p_opt(t),
                |u| <U as MsgTrait>::f32_0p_opt(u),
            )
        }
        fn f32_p0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_p0_opt(t),
                |u| <U as MsgTrait>::f32_p0_opt(u),
            )
        }
        fn f32_0p0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_0p0_opt(t),
                |u| <U as MsgTrait>::f32_0p0_opt(u),
            )
        }
        fn f32_42_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_42_opt(t),
                |u| <U as MsgTrait>::f32_42_opt(u),
            )
        }
        fn f32_m42_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_m42_opt(t),
                |u| <U as MsgTrait>::f32_m42_opt(u),
            )
        }
        fn f32_0p25_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_0p25_opt(t),
                |u| <U as MsgTrait>::f32_0p25_opt(u),
            )
        }
        fn f32_1p5e2_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_1p5e2_opt(t),
                |u| <U as MsgTrait>::f32_1p5e2_opt(u),
            )
        }
        fn f32_inf_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_inf_opt(t),
                |u| <U as MsgTrait>::f32_inf_opt(u),
            )
        }
        fn f32_minf_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_minf_opt(t),
                |u| <U as MsgTrait>::f32_minf_opt(u),
            )
        }
        fn f32_nan_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_nan_opt(t),
                |u| <U as MsgTrait>::f32_nan_opt(u),
            )
        }
        fn f32_mnan_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_mnan_opt(t),
                |u| <U as MsgTrait>::f32_mnan_opt(u),
            )
        }
        fn bool_default_opt<'this>(&'this self) -> ::std::option::Option<bool> {
            self.as_ref().either(
                |t| <T as MsgTrait>::bool_default_opt(t),
                |u| <U as MsgTrait>::bool_default_opt(u),
            )
        }
        fn bool_true_opt<'this>(&'this self) -> ::std::option::Option<bool> {
            self.as_ref().either(
                |t| <T as MsgTrait>::bool_true_opt(t),
                |u| <U as MsgTrait>::bool_true_opt(u),
            )
        }
        fn bool_false_opt<'this>(&'this self) -> ::std::option::Option<bool> {
            self.as_ref().either(
                |t| <T as MsgTrait>::bool_false_opt(t),
                |u| <U as MsgTrait>::bool_false_opt(u),
            )
        }
        fn string_default_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            self.as_ref().either(
                |t| <T as MsgTrait>::string_default_opt(t),
                |u| <U as MsgTrait>::string_default_opt(u),
            )
        }
        fn string_empty_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            self.as_ref().either(
                |t| <T as MsgTrait>::string_empty_opt(t),
                |u| <U as MsgTrait>::string_empty_opt(u),
            )
        }
        fn string_abc_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            self.as_ref().either(
                |t| <T as MsgTrait>::string_abc_opt(t),
                |u| <U as MsgTrait>::string_abc_opt(u),
            )
        }
        fn string_aiu_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            self.as_ref().either(
                |t| <T as MsgTrait>::string_aiu_opt(t),
                |u| <U as MsgTrait>::string_aiu_opt(u),
            )
        }
        fn string_backslash_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            self.as_ref().either(
                |t| <T as MsgTrait>::string_backslash_opt(t),
                |u| <U as MsgTrait>::string_backslash_opt(u),
            )
        }
        fn string_tab_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            self.as_ref().either(
                |t| <T as MsgTrait>::string_tab_opt(t),
                |u| <U as MsgTrait>::string_tab_opt(u),
            )
        }
        fn string_crlf_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            self.as_ref().either(
                |t| <T as MsgTrait>::string_crlf_opt(t),
                |u| <U as MsgTrait>::string_crlf_opt(u),
            )
        }
        fn bytes_default_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            self.as_ref().either(
                |t| <T as MsgTrait>::bytes_default_opt(t),
                |u| <U as MsgTrait>::bytes_default_opt(u),
            )
        }
        fn bytes_empty_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            self.as_ref().either(
                |t| <T as MsgTrait>::bytes_empty_opt(t),
                |u| <U as MsgTrait>::bytes_empty_opt(u),
            )
        }
        fn bytes_abc_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            self.as_ref().either(
                |t| <T as MsgTrait>::bytes_abc_opt(t),
                |u| <U as MsgTrait>::bytes_abc_opt(u),
            )
        }
        fn bytes_aiu_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            self.as_ref().either(
                |t| <T as MsgTrait>::bytes_aiu_opt(t),
                |u| <U as MsgTrait>::bytes_aiu_opt(u),
            )
        }
        fn bytes_backslash_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            self.as_ref().either(
                |t| <T as MsgTrait>::bytes_backslash_opt(t),
                |u| <U as MsgTrait>::bytes_backslash_opt(u),
            )
        }
        fn bytes_tab_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            self.as_ref().either(
                |t| <T as MsgTrait>::bytes_tab_opt(t),
                |u| <U as MsgTrait>::bytes_tab_opt(u),
            )
        }
        fn bytes_crlf_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            self.as_ref().either(
                |t| <T as MsgTrait>::bytes_crlf_opt(t),
                |u| <U as MsgTrait>::bytes_crlf_opt(u),
            )
        }
        fn enum_default_opt<'this>(
            &'this self,
        ) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
            self.as_ref().either(
                |t| <T as MsgTrait>::enum_default_opt(t),
                |u| <U as MsgTrait>::enum_default_opt(u),
            )
        }
        fn enum_one_opt<'this>(
            &'this self,
        ) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
            self.as_ref().either(
                |t| <T as MsgTrait>::enum_one_opt(t),
                |u| <U as MsgTrait>::enum_one_opt(u),
            )
        }
        fn enum_fourty_two_opt<'this>(
            &'this self,
        ) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
            self.as_ref().either(
                |t| <T as MsgTrait>::enum_fourty_two_opt(t),
                |u| <U as MsgTrait>::enum_fourty_two_opt(u),
            )
        }
    }
    impl<T> MsgTrait for ::std::option::Option<T>
    where
        T: MsgTrait,
    {
        fn i32_default_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            self.as_ref().and_then(|msg| msg.i32_default_opt())
        }
        fn i32_0_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            self.as_ref().and_then(|msg| msg.i32_0_opt())
        }
        fn i32_42_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            self.as_ref().and_then(|msg| msg.i32_42_opt())
        }
        fn i32_m42_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            self.as_ref().and_then(|msg| msg.i32_m42_opt())
        }
        fn i32_2147483647_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            self.as_ref().and_then(|msg| msg.i32_2147483647_opt())
        }
        fn i32_m2147483648_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            self.as_ref().and_then(|msg| msg.i32_m2147483648_opt())
        }
        fn i32_0123_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            self.as_ref().and_then(|msg| msg.i32_0123_opt())
        }
        fn i32_0x123_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            self.as_ref().and_then(|msg| msg.i32_0x123_opt())
        }
        fn u32_default_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            self.as_ref().and_then(|msg| msg.u32_default_opt())
        }
        fn u32_0_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            self.as_ref().and_then(|msg| msg.u32_0_opt())
        }
        fn u32_42_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            self.as_ref().and_then(|msg| msg.u32_42_opt())
        }
        fn u32_4294967295_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            self.as_ref().and_then(|msg| msg.u32_4294967295_opt())
        }
        fn u32_0123_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            self.as_ref().and_then(|msg| msg.u32_0123_opt())
        }
        fn u32_0x123_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            self.as_ref().and_then(|msg| msg.u32_0x123_opt())
        }
        fn i64_default_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            self.as_ref().and_then(|msg| msg.i64_default_opt())
        }
        fn i64_0_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            self.as_ref().and_then(|msg| msg.i64_0_opt())
        }
        fn i64_42_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            self.as_ref().and_then(|msg| msg.i64_42_opt())
        }
        fn i64_m42_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            self.as_ref().and_then(|msg| msg.i64_m42_opt())
        }
        fn i64_9223372036854775807_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            self.as_ref()
                .and_then(|msg| msg.i64_9223372036854775807_opt())
        }
        fn i64_m9223372036854775808_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            self.as_ref()
                .and_then(|msg| msg.i64_m9223372036854775808_opt())
        }
        fn i64_0123_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            self.as_ref().and_then(|msg| msg.i64_0123_opt())
        }
        fn i64_0x123_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            self.as_ref().and_then(|msg| msg.i64_0x123_opt())
        }
        fn u64_default_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            self.as_ref().and_then(|msg| msg.u64_default_opt())
        }
        fn u64_0_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            self.as_ref().and_then(|msg| msg.u64_0_opt())
        }
        fn u64_42_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            self.as_ref().and_then(|msg| msg.u64_42_opt())
        }
        fn u64_18446744073709551615_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            self.as_ref()
                .and_then(|msg| msg.u64_18446744073709551615_opt())
        }
        fn u64_0123_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            self.as_ref().and_then(|msg| msg.u64_0123_opt())
        }
        fn u64_0x123_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            self.as_ref().and_then(|msg| msg.u64_0x123_opt())
        }
        fn f32_default_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().and_then(|msg| msg.f32_default_opt())
        }
        fn f32_0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().and_then(|msg| msg.f32_0_opt())
        }
        fn f32_m0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().and_then(|msg| msg.f32_m0_opt())
        }
        fn f32_0p_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().and_then(|msg| msg.f32_0p_opt())
        }
        fn f32_p0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().and_then(|msg| msg.f32_p0_opt())
        }
        fn f32_0p0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().and_then(|msg| msg.f32_0p0_opt())
        }
        fn f32_42_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().and_then(|msg| msg.f32_42_opt())
        }
        fn f32_m42_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().and_then(|msg| msg.f32_m42_opt())
        }
        fn f32_0p25_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().and_then(|msg| msg.f32_0p25_opt())
        }
        fn f32_1p5e2_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().and_then(|msg| msg.f32_1p5e2_opt())
        }
        fn f32_inf_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().and_then(|msg| msg.f32_inf_opt())
        }
        fn f32_minf_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().and_then(|msg| msg.f32_minf_opt())
        }
        fn f32_nan_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().and_then(|msg| msg.f32_nan_opt())
        }
        fn f32_mnan_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            self.as_ref().and_then(|msg| msg.f32_mnan_opt())
        }
        fn bool_default_opt<'this>(&'this self) -> ::std::option::Option<bool> {
            self.as_ref().and_then(|msg| msg.bool_default_opt())
        }
        fn bool_true_opt<'this>(&'this self) -> ::std::option::Option<bool> {
            self.as_ref().and_then(|msg| msg.bool_true_opt())
        }
        fn bool_false_opt<'this>(&'this self) -> ::std::option::Option<bool> {
            self.as_ref().and_then(|msg| msg.bool_false_opt())
        }
        fn string_default_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            self.as_ref().and_then(|msg| msg.string_default_opt())
        }
        fn string_empty_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            self.as_ref().and_then(|msg| msg.string_empty_opt())
        }
        fn string_abc_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            self.as_ref().and_then(|msg| msg.string_abc_opt())
        }
        fn string_aiu_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            self.as_ref().and_then(|msg| msg.string_aiu_opt())
        }
        fn string_backslash_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            self.as_ref().and_then(|msg| msg.string_backslash_opt())
        }
        fn string_tab_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            self.as_ref().and_then(|msg| msg.string_tab_opt())
        }
        fn string_crlf_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            self.as_ref().and_then(|msg| msg.string_crlf_opt())
        }
        fn bytes_default_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            self.as_ref().and_then(|msg| msg.bytes_default_opt())
        }
        fn bytes_empty_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            self.as_ref().and_then(|msg| msg.bytes_empty_opt())
        }
        fn bytes_abc_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            self.as_ref().and_then(|msg| msg.bytes_abc_opt())
        }
        fn bytes_aiu_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            self.as_ref().and_then(|msg| msg.bytes_aiu_opt())
        }
        fn bytes_backslash_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            self.as_ref().and_then(|msg| msg.bytes_backslash_opt())
        }
        fn bytes_tab_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            self.as_ref().and_then(|msg| msg.bytes_tab_opt())
        }
        fn bytes_crlf_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            self.as_ref().and_then(|msg| msg.bytes_crlf_opt())
        }
        fn enum_default_opt<'this>(
            &'this self,
        ) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
            self.as_ref().and_then(|msg| msg.enum_default_opt())
        }
        fn enum_one_opt<'this>(
            &'this self,
        ) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
            self.as_ref().and_then(|msg| msg.enum_one_opt())
        }
        fn enum_fourty_two_opt<'this>(
            &'this self,
        ) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
            self.as_ref().and_then(|msg| msg.enum_fourty_two_opt())
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField1 {
        pub i32_default: i32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField1 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField1 {
        fn i32_default_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.i32_default))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField1 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.i32_default), 1, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<i32> for MsgSingleField1 {
        fn from(value: i32) -> Self {
            Self { i32_default: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField2 {
        pub i32_0: i32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField2 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField2 {
        fn i32_0_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.i32_0))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField2 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::i32_0(self)
                == <() as super::_puroro_traits::MsgTrait>::i32_0(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.i32_0), 2, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<i32> for MsgSingleField2 {
        fn from(value: i32) -> Self {
            Self { i32_0: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField3 {
        pub i32_42: i32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField3 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField3 {
        fn i32_42_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.i32_42))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField3 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::i32_42(self)
                == <() as super::_puroro_traits::MsgTrait>::i32_42(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.i32_42), 3, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<i32> for MsgSingleField3 {
        fn from(value: i32) -> Self {
            Self { i32_42: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField4 {
        pub i32_m42: i32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField4 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField4 {
        fn i32_m42_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.i32_m42))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField4 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::i32_m42(self)
                == <() as super::_puroro_traits::MsgTrait>::i32_m42(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.i32_m42), 4, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<i32> for MsgSingleField4 {
        fn from(value: i32) -> Self {
            Self { i32_m42: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField5 {
        pub i32_2147483647: i32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField5 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField5 {
        fn i32_2147483647_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.i32_2147483647))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField5 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::i32_2147483647(self)
                == <() as super::_puroro_traits::MsgTrait>::i32_2147483647(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.i32_2147483647), 5, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<i32> for MsgSingleField5 {
        fn from(value: i32) -> Self {
            Self {
                i32_2147483647: value,
            }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField6 {
        pub i32_m2147483648: i32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField6 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField6 {
        fn i32_m2147483648_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.i32_m2147483648))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField6 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::i32_m2147483648(self)
                == <() as super::_puroro_traits::MsgTrait>::i32_m2147483648(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.i32_m2147483648), 6, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<i32> for MsgSingleField6 {
        fn from(value: i32) -> Self {
            Self {
                i32_m2147483648: value,
            }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField7 {
        pub i32_0123: i32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField7 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField7 {
        fn i32_0123_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.i32_0123))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField7 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::i32_0123(self)
                == <() as super::_puroro_traits::MsgTrait>::i32_0123(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.i32_0123), 7, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<i32> for MsgSingleField7 {
        fn from(value: i32) -> Self {
            Self { i32_0123: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField8 {
        pub i32_0x123: i32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField8 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField8 {
        fn i32_0x123_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.i32_0x123))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField8 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::i32_0x123(self)
                == <() as super::_puroro_traits::MsgTrait>::i32_0x123(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int32>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.i32_0x123), 8, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<i32> for MsgSingleField8 {
        fn from(value: i32) -> Self {
            Self { i32_0x123: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField11 {
        pub u32_default: u32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField11 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField11 {
        fn u32_default_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.u32_default))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField11 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt32>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.u32_default), 11, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<u32> for MsgSingleField11 {
        fn from(value: u32) -> Self {
            Self { u32_default: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField12 {
        pub u32_0: u32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField12 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField12 {
        fn u32_0_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.u32_0))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField12 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::u32_0(self)
                == <() as super::_puroro_traits::MsgTrait>::u32_0(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt32>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.u32_0), 12, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<u32> for MsgSingleField12 {
        fn from(value: u32) -> Self {
            Self { u32_0: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField13 {
        pub u32_42: u32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField13 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField13 {
        fn u32_42_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.u32_42))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField13 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::u32_42(self)
                == <() as super::_puroro_traits::MsgTrait>::u32_42(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt32>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.u32_42), 13, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<u32> for MsgSingleField13 {
        fn from(value: u32) -> Self {
            Self { u32_42: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField15 {
        pub u32_4294967295: u32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField15 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField15 {
        fn u32_4294967295_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.u32_4294967295))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField15 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::u32_4294967295(self)
                == <() as super::_puroro_traits::MsgTrait>::u32_4294967295(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt32>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.u32_4294967295), 15, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<u32> for MsgSingleField15 {
        fn from(value: u32) -> Self {
            Self {
                u32_4294967295: value,
            }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField17 {
        pub u32_0123: u32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField17 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField17 {
        fn u32_0123_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.u32_0123))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField17 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::u32_0123(self)
                == <() as super::_puroro_traits::MsgTrait>::u32_0123(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt32>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.u32_0123), 17, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<u32> for MsgSingleField17 {
        fn from(value: u32) -> Self {
            Self { u32_0123: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField18 {
        pub u32_0x123: u32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField18 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField18 {
        fn u32_0x123_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.u32_0x123))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField18 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::u32_0x123(self)
                == <() as super::_puroro_traits::MsgTrait>::u32_0x123(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt32>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.u32_0x123), 18, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<u32> for MsgSingleField18 {
        fn from(value: u32) -> Self {
            Self { u32_0x123: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField21 {
        pub i64_default: i64,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField21 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField21 {
        fn i64_default_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.i64_default))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField21 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.i64_default), 21, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<i64> for MsgSingleField21 {
        fn from(value: i64) -> Self {
            Self { i64_default: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField22 {
        pub i64_0: i64,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField22 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField22 {
        fn i64_0_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.i64_0))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField22 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::i64_0(self)
                == <() as super::_puroro_traits::MsgTrait>::i64_0(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.i64_0), 22, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<i64> for MsgSingleField22 {
        fn from(value: i64) -> Self {
            Self { i64_0: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField23 {
        pub i64_42: i64,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField23 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField23 {
        fn i64_42_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.i64_42))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField23 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::i64_42(self)
                == <() as super::_puroro_traits::MsgTrait>::i64_42(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.i64_42), 23, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<i64> for MsgSingleField23 {
        fn from(value: i64) -> Self {
            Self { i64_42: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField24 {
        pub i64_m42: i64,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField24 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField24 {
        fn i64_m42_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.i64_m42))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField24 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::i64_m42(self)
                == <() as super::_puroro_traits::MsgTrait>::i64_m42(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.i64_m42), 24, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<i64> for MsgSingleField24 {
        fn from(value: i64) -> Self {
            Self { i64_m42: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField25 {
        pub i64_9223372036854775807: i64,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField25 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField25 {
        fn i64_9223372036854775807_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.i64_9223372036854775807))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField25 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::i64_9223372036854775807(self)
                == <() as super::_puroro_traits::MsgTrait>::i64_9223372036854775807(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.i64_9223372036854775807), 25, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<i64> for MsgSingleField25 {
        fn from(value: i64) -> Self {
            Self {
                i64_9223372036854775807: value,
            }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField26 {
        pub i64_m9223372036854775808: i64,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField26 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField26 {
        fn i64_m9223372036854775808_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.i64_m9223372036854775808))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField26 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::i64_m9223372036854775808(self)
                == <() as super::_puroro_traits::MsgTrait>::i64_m9223372036854775808(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.i64_m9223372036854775808), 26, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<i64> for MsgSingleField26 {
        fn from(value: i64) -> Self {
            Self {
                i64_m9223372036854775808: value,
            }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField27 {
        pub i64_0123: i64,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField27 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField27 {
        fn i64_0123_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.i64_0123))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField27 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::i64_0123(self)
                == <() as super::_puroro_traits::MsgTrait>::i64_0123(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.i64_0123), 27, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<i64> for MsgSingleField27 {
        fn from(value: i64) -> Self {
            Self { i64_0123: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField28 {
        pub i64_0x123: i64,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField28 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField28 {
        fn i64_0x123_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.i64_0x123))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField28 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::i64_0x123(self)
                == <() as super::_puroro_traits::MsgTrait>::i64_0x123(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Int64>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.i64_0x123), 28, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<i64> for MsgSingleField28 {
        fn from(value: i64) -> Self {
            Self { i64_0x123: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField31 {
        pub u64_default: u64,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField31 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField31 {
        fn u64_default_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.u64_default))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField31 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt64>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.u64_default), 31, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<u64> for MsgSingleField31 {
        fn from(value: u64) -> Self {
            Self { u64_default: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField32 {
        pub u64_0: u64,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField32 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField32 {
        fn u64_0_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.u64_0))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField32 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::u64_0(self)
                == <() as super::_puroro_traits::MsgTrait>::u64_0(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt64>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.u64_0), 32, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<u64> for MsgSingleField32 {
        fn from(value: u64) -> Self {
            Self { u64_0: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField33 {
        pub u64_42: u64,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField33 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField33 {
        fn u64_42_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.u64_42))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField33 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::u64_42(self)
                == <() as super::_puroro_traits::MsgTrait>::u64_42(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt64>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.u64_42), 33, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<u64> for MsgSingleField33 {
        fn from(value: u64) -> Self {
            Self { u64_42: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField35 {
        pub u64_18446744073709551615: u64,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField35 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField35 {
        fn u64_18446744073709551615_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.u64_18446744073709551615))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField35 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::u64_18446744073709551615(self)
                == <() as super::_puroro_traits::MsgTrait>::u64_18446744073709551615(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt64>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.u64_18446744073709551615), 35, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<u64> for MsgSingleField35 {
        fn from(value: u64) -> Self {
            Self {
                u64_18446744073709551615: value,
            }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField37 {
        pub u64_0123: u64,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField37 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField37 {
        fn u64_0123_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.u64_0123))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField37 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::u64_0123(self)
                == <() as super::_puroro_traits::MsgTrait>::u64_0123(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt64>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.u64_0123), 37, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<u64> for MsgSingleField37 {
        fn from(value: u64) -> Self {
            Self { u64_0123: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField38 {
        pub u64_0x123: u64,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField38 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField38 {
        fn u64_0x123_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.u64_0x123))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField38 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::u64_0x123(self)
                == <() as super::_puroro_traits::MsgTrait>::u64_0x123(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::UInt64>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.u64_0x123), 38, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<u64> for MsgSingleField38 {
        fn from(value: u64) -> Self {
            Self { u64_0x123: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField41 {
        pub f32_default: f32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField41 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField41 {
        fn f32_default_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.f32_default))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField41 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.f32_default), 41, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<f32> for MsgSingleField41 {
        fn from(value: f32) -> Self {
            Self { f32_default: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField42 {
        pub f32_0: f32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField42 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField42 {
        fn f32_0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.f32_0))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField42 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::f32_0(self)
                == <() as super::_puroro_traits::MsgTrait>::f32_0(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.f32_0), 42, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<f32> for MsgSingleField42 {
        fn from(value: f32) -> Self {
            Self { f32_0: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField43 {
        pub f32_m0: f32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField43 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField43 {
        fn f32_m0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.f32_m0))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField43 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::f32_m0(self)
                == <() as super::_puroro_traits::MsgTrait>::f32_m0(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.f32_m0), 43, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<f32> for MsgSingleField43 {
        fn from(value: f32) -> Self {
            Self { f32_m0: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField44 {
        pub f32_0p: f32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField44 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField44 {
        fn f32_0p_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.f32_0p))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField44 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::f32_0p(self)
                == <() as super::_puroro_traits::MsgTrait>::f32_0p(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.f32_0p), 44, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<f32> for MsgSingleField44 {
        fn from(value: f32) -> Self {
            Self { f32_0p: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField45 {
        pub f32_p0: f32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField45 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField45 {
        fn f32_p0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.f32_p0))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField45 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::f32_p0(self)
                == <() as super::_puroro_traits::MsgTrait>::f32_p0(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.f32_p0), 45, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<f32> for MsgSingleField45 {
        fn from(value: f32) -> Self {
            Self { f32_p0: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField46 {
        pub f32_0p0: f32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField46 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField46 {
        fn f32_0p0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.f32_0p0))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField46 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::f32_0p0(self)
                == <() as super::_puroro_traits::MsgTrait>::f32_0p0(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.f32_0p0), 46, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<f32> for MsgSingleField46 {
        fn from(value: f32) -> Self {
            Self { f32_0p0: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField47 {
        pub f32_42: f32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField47 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField47 {
        fn f32_42_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.f32_42))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField47 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::f32_42(self)
                == <() as super::_puroro_traits::MsgTrait>::f32_42(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.f32_42), 47, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<f32> for MsgSingleField47 {
        fn from(value: f32) -> Self {
            Self { f32_42: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField48 {
        pub f32_m42: f32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField48 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField48 {
        fn f32_m42_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.f32_m42))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField48 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::f32_m42(self)
                == <() as super::_puroro_traits::MsgTrait>::f32_m42(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.f32_m42), 48, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<f32> for MsgSingleField48 {
        fn from(value: f32) -> Self {
            Self { f32_m42: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField49 {
        pub f32_0p25: f32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField49 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField49 {
        fn f32_0p25_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.f32_0p25))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField49 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::f32_0p25(self)
                == <() as super::_puroro_traits::MsgTrait>::f32_0p25(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.f32_0p25), 49, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<f32> for MsgSingleField49 {
        fn from(value: f32) -> Self {
            Self { f32_0p25: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField50 {
        pub f32_1p5e2: f32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField50 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField50 {
        fn f32_1p5e2_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.f32_1p5e2))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField50 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::f32_1p5e2(self)
                == <() as super::_puroro_traits::MsgTrait>::f32_1p5e2(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.f32_1p5e2), 50, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<f32> for MsgSingleField50 {
        fn from(value: f32) -> Self {
            Self { f32_1p5e2: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField51 {
        pub f32_inf: f32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField51 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField51 {
        fn f32_inf_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.f32_inf))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField51 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::f32_inf(self)
                == <() as super::_puroro_traits::MsgTrait>::f32_inf(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.f32_inf), 51, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<f32> for MsgSingleField51 {
        fn from(value: f32) -> Self {
            Self { f32_inf: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField52 {
        pub f32_minf: f32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField52 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField52 {
        fn f32_minf_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.f32_minf))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField52 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::f32_minf(self)
                == <() as super::_puroro_traits::MsgTrait>::f32_minf(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.f32_minf), 52, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<f32> for MsgSingleField52 {
        fn from(value: f32) -> Self {
            Self { f32_minf: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField53 {
        pub f32_nan: f32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField53 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField53 {
        fn f32_nan_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.f32_nan))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField53 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::f32_nan(self)
                == <() as super::_puroro_traits::MsgTrait>::f32_nan(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.f32_nan), 53, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<f32> for MsgSingleField53 {
        fn from(value: f32) -> Self {
            Self { f32_nan: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField54 {
        pub f32_mnan: f32,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField54 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField54 {
        fn f32_mnan_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.f32_mnan))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField54 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::f32_mnan(self)
                == <() as super::_puroro_traits::MsgTrait>::f32_mnan(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Float>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.f32_mnan), 54, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<f32> for MsgSingleField54 {
        fn from(value: f32) -> Self {
            Self { f32_mnan: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField61 {
        pub bool_default: bool,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField61 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField61 {
        fn bool_default_opt<'this>(&'this self) -> ::std::option::Option<bool> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.bool_default))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField61 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bool>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.bool_default), 61, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<bool> for MsgSingleField61 {
        fn from(value: bool) -> Self {
            Self {
                bool_default: value,
            }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField62 {
        pub bool_true: bool,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField62 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField62 {
        fn bool_true_opt<'this>(&'this self) -> ::std::option::Option<bool> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.bool_true))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField62 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::bool_true(self)
                == <() as super::_puroro_traits::MsgTrait>::bool_true(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bool>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.bool_true), 62, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<bool> for MsgSingleField62 {
        fn from(value: bool) -> Self {
            Self { bool_true: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField63 {
        pub bool_false: bool,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField63 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField63 {
        fn bool_false_opt<'this>(&'this self) -> ::std::option::Option<bool> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.bool_false))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField63 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::bool_false(self)
                == <() as super::_puroro_traits::MsgTrait>::bool_false(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bool>::ser_field::<
                (),
                _,
                _,
            >(::std::iter::once(&self.bool_false), 63, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<bool> for MsgSingleField63 {
        fn from(value: bool) -> Self {
            Self { bool_false: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField71<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        pub string_default: ScalarType,
    }

    impl<ScalarType> ::puroro::Message<super::Msg> for MsgSingleField71<ScalarType> where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug
    {
    }

    impl<ScalarType> super::_puroro_traits::MsgTrait for MsgSingleField71<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn string_default_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            ::std::option::Option::Some(self.string_default.as_ref())
        }
    }

    impl<ScalarType> ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField71<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::String>::ser_field::<
                ScalarType,
                _,
                _,
            >(::std::iter::once(&self.string_default), 71, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl<ScalarType> ::std::convert::From<ScalarType> for MsgSingleField71<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn from(value: ScalarType) -> Self {
            Self {
                string_default: value,
            }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField72<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        pub string_empty: ScalarType,
    }

    impl<ScalarType> ::puroro::Message<super::Msg> for MsgSingleField72<ScalarType> where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug
    {
    }

    impl<ScalarType> super::_puroro_traits::MsgTrait for MsgSingleField72<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn string_empty_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            ::std::option::Option::Some(self.string_empty.as_ref())
        }
    }

    impl<ScalarType> ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField72<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::string_empty(self)
                == <() as super::_puroro_traits::MsgTrait>::string_empty(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::String>::ser_field::<
                ScalarType,
                _,
                _,
            >(::std::iter::once(&self.string_empty), 72, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl<ScalarType> ::std::convert::From<ScalarType> for MsgSingleField72<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn from(value: ScalarType) -> Self {
            Self {
                string_empty: value,
            }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField73<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        pub string_abc: ScalarType,
    }

    impl<ScalarType> ::puroro::Message<super::Msg> for MsgSingleField73<ScalarType> where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug
    {
    }

    impl<ScalarType> super::_puroro_traits::MsgTrait for MsgSingleField73<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn string_abc_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            ::std::option::Option::Some(self.string_abc.as_ref())
        }
    }

    impl<ScalarType> ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField73<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::string_abc(self)
                == <() as super::_puroro_traits::MsgTrait>::string_abc(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::String>::ser_field::<
                ScalarType,
                _,
                _,
            >(::std::iter::once(&self.string_abc), 73, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl<ScalarType> ::std::convert::From<ScalarType> for MsgSingleField73<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn from(value: ScalarType) -> Self {
            Self { string_abc: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField74<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        pub string_aiu: ScalarType,
    }

    impl<ScalarType> ::puroro::Message<super::Msg> for MsgSingleField74<ScalarType> where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug
    {
    }

    impl<ScalarType> super::_puroro_traits::MsgTrait for MsgSingleField74<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn string_aiu_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            ::std::option::Option::Some(self.string_aiu.as_ref())
        }
    }

    impl<ScalarType> ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField74<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::string_aiu(self)
                == <() as super::_puroro_traits::MsgTrait>::string_aiu(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::String>::ser_field::<
                ScalarType,
                _,
                _,
            >(::std::iter::once(&self.string_aiu), 74, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl<ScalarType> ::std::convert::From<ScalarType> for MsgSingleField74<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn from(value: ScalarType) -> Self {
            Self { string_aiu: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField75<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        pub string_backslash: ScalarType,
    }

    impl<ScalarType> ::puroro::Message<super::Msg> for MsgSingleField75<ScalarType> where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug
    {
    }

    impl<ScalarType> super::_puroro_traits::MsgTrait for MsgSingleField75<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn string_backslash_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            ::std::option::Option::Some(self.string_backslash.as_ref())
        }
    }

    impl<ScalarType> ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField75<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::string_backslash(self)
                == <() as super::_puroro_traits::MsgTrait>::string_backslash(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::String>::ser_field::<
                ScalarType,
                _,
                _,
            >(::std::iter::once(&self.string_backslash), 75, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl<ScalarType> ::std::convert::From<ScalarType> for MsgSingleField75<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn from(value: ScalarType) -> Self {
            Self {
                string_backslash: value,
            }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField76<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        pub string_tab: ScalarType,
    }

    impl<ScalarType> ::puroro::Message<super::Msg> for MsgSingleField76<ScalarType> where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug
    {
    }

    impl<ScalarType> super::_puroro_traits::MsgTrait for MsgSingleField76<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn string_tab_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            ::std::option::Option::Some(self.string_tab.as_ref())
        }
    }

    impl<ScalarType> ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField76<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::string_tab(self)
                == <() as super::_puroro_traits::MsgTrait>::string_tab(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::String>::ser_field::<
                ScalarType,
                _,
                _,
            >(::std::iter::once(&self.string_tab), 76, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl<ScalarType> ::std::convert::From<ScalarType> for MsgSingleField76<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn from(value: ScalarType) -> Self {
            Self { string_tab: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField77<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        pub string_crlf: ScalarType,
    }

    impl<ScalarType> ::puroro::Message<super::Msg> for MsgSingleField77<ScalarType> where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug
    {
    }

    impl<ScalarType> super::_puroro_traits::MsgTrait for MsgSingleField77<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn string_crlf_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            ::std::option::Option::Some(self.string_crlf.as_ref())
        }
    }

    impl<ScalarType> ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField77<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::string_crlf(self)
                == <() as super::_puroro_traits::MsgTrait>::string_crlf(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::String>::ser_field::<
                ScalarType,
                _,
                _,
            >(::std::iter::once(&self.string_crlf), 77, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl<ScalarType> ::std::convert::From<ScalarType> for MsgSingleField77<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<str>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn from(value: ScalarType) -> Self {
            Self { string_crlf: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField81<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        pub bytes_default: ScalarType,
    }

    impl<ScalarType> ::puroro::Message<super::Msg> for MsgSingleField81<ScalarType> where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug
    {
    }

    impl<ScalarType> super::_puroro_traits::MsgTrait for MsgSingleField81<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn bytes_default_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            ::std::option::Option::Some(self.bytes_default.as_ref())
        }
    }

    impl<ScalarType> ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField81<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bytes>::ser_field::<
                ScalarType,
                _,
                _,
            >(::std::iter::once(&self.bytes_default), 81, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl<ScalarType> ::std::convert::From<ScalarType> for MsgSingleField81<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn from(value: ScalarType) -> Self {
            Self {
                bytes_default: value,
            }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField82<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        pub bytes_empty: ScalarType,
    }

    impl<ScalarType> ::puroro::Message<super::Msg> for MsgSingleField82<ScalarType> where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug
    {
    }

    impl<ScalarType> super::_puroro_traits::MsgTrait for MsgSingleField82<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn bytes_empty_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            ::std::option::Option::Some(self.bytes_empty.as_ref())
        }
    }

    impl<ScalarType> ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField82<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::bytes_empty(self)
                == <() as super::_puroro_traits::MsgTrait>::bytes_empty(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bytes>::ser_field::<
                ScalarType,
                _,
                _,
            >(::std::iter::once(&self.bytes_empty), 82, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl<ScalarType> ::std::convert::From<ScalarType> for MsgSingleField82<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn from(value: ScalarType) -> Self {
            Self { bytes_empty: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField83<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        pub bytes_abc: ScalarType,
    }

    impl<ScalarType> ::puroro::Message<super::Msg> for MsgSingleField83<ScalarType> where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug
    {
    }

    impl<ScalarType> super::_puroro_traits::MsgTrait for MsgSingleField83<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn bytes_abc_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            ::std::option::Option::Some(self.bytes_abc.as_ref())
        }
    }

    impl<ScalarType> ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField83<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::bytes_abc(self)
                == <() as super::_puroro_traits::MsgTrait>::bytes_abc(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bytes>::ser_field::<
                ScalarType,
                _,
                _,
            >(::std::iter::once(&self.bytes_abc), 83, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl<ScalarType> ::std::convert::From<ScalarType> for MsgSingleField83<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn from(value: ScalarType) -> Self {
            Self { bytes_abc: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField84<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        pub bytes_aiu: ScalarType,
    }

    impl<ScalarType> ::puroro::Message<super::Msg> for MsgSingleField84<ScalarType> where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug
    {
    }

    impl<ScalarType> super::_puroro_traits::MsgTrait for MsgSingleField84<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn bytes_aiu_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            ::std::option::Option::Some(self.bytes_aiu.as_ref())
        }
    }

    impl<ScalarType> ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField84<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::bytes_aiu(self)
                == <() as super::_puroro_traits::MsgTrait>::bytes_aiu(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bytes>::ser_field::<
                ScalarType,
                _,
                _,
            >(::std::iter::once(&self.bytes_aiu), 84, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl<ScalarType> ::std::convert::From<ScalarType> for MsgSingleField84<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn from(value: ScalarType) -> Self {
            Self { bytes_aiu: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField85<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        pub bytes_backslash: ScalarType,
    }

    impl<ScalarType> ::puroro::Message<super::Msg> for MsgSingleField85<ScalarType> where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug
    {
    }

    impl<ScalarType> super::_puroro_traits::MsgTrait for MsgSingleField85<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn bytes_backslash_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            ::std::option::Option::Some(self.bytes_backslash.as_ref())
        }
    }

    impl<ScalarType> ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField85<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::bytes_backslash(self)
                == <() as super::_puroro_traits::MsgTrait>::bytes_backslash(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bytes>::ser_field::<
                ScalarType,
                _,
                _,
            >(::std::iter::once(&self.bytes_backslash), 85, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl<ScalarType> ::std::convert::From<ScalarType> for MsgSingleField85<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn from(value: ScalarType) -> Self {
            Self {
                bytes_backslash: value,
            }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField86<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        pub bytes_tab: ScalarType,
    }

    impl<ScalarType> ::puroro::Message<super::Msg> for MsgSingleField86<ScalarType> where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug
    {
    }

    impl<ScalarType> super::_puroro_traits::MsgTrait for MsgSingleField86<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn bytes_tab_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            ::std::option::Option::Some(self.bytes_tab.as_ref())
        }
    }

    impl<ScalarType> ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField86<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::bytes_tab(self)
                == <() as super::_puroro_traits::MsgTrait>::bytes_tab(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bytes>::ser_field::<
                ScalarType,
                _,
                _,
            >(::std::iter::once(&self.bytes_tab), 86, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl<ScalarType> ::std::convert::From<ScalarType> for MsgSingleField86<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn from(value: ScalarType) -> Self {
            Self { bytes_tab: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField87<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        pub bytes_crlf: ScalarType,
    }

    impl<ScalarType> ::puroro::Message<super::Msg> for MsgSingleField87<ScalarType> where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug
    {
    }

    impl<ScalarType> super::_puroro_traits::MsgTrait for MsgSingleField87<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn bytes_crlf_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            ::std::option::Option::Some(self.bytes_crlf.as_ref())
        }
    }

    impl<ScalarType> ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField87<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::bytes_crlf(self)
                == <() as super::_puroro_traits::MsgTrait>::bytes_crlf(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<::puroro::tags::Optional, ::puroro::tags::Bytes>::ser_field::<
                ScalarType,
                _,
                _,
            >(::std::iter::once(&self.bytes_crlf), 87, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl<ScalarType> ::std::convert::From<ScalarType> for MsgSingleField87<ScalarType>
    where
        ScalarType: ::std::convert::AsRef<[u8]>
            + ::std::clone::Clone
            + ::std::cmp::PartialEq
            + ::std::fmt::Debug,
    {
        fn from(value: ScalarType) -> Self {
            Self { bytes_crlf: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField91 {
        pub enum_default: self::_puroro_root::proto2_defaults::MyEnum,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField91 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField91 {
        fn enum_default_opt<'this>(
            &'this self,
        ) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.enum_default))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField91 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            SerFieldToIoWrite::<
                ::puroro::tags::Optional,
                ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>,
            >::ser_field::<(), _, _>(::std::iter::once(&self.enum_default), 91, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<self::_puroro_root::proto2_defaults::MyEnum> for MsgSingleField91 {
        fn from(value: self::_puroro_root::proto2_defaults::MyEnum) -> Self {
            Self {
                enum_default: value,
            }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField92 {
        pub enum_one: self::_puroro_root::proto2_defaults::MyEnum,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField92 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField92 {
        fn enum_one_opt<'this>(
            &'this self,
        ) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.enum_one))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField92 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::enum_one(self)
                == <() as super::_puroro_traits::MsgTrait>::enum_one(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<
                ::puroro::tags::Optional,
                ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>,
            >::ser_field::<(), _, _>(::std::iter::once(&self.enum_one), 92, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<self::_puroro_root::proto2_defaults::MyEnum> for MsgSingleField92 {
        fn from(value: self::_puroro_root::proto2_defaults::MyEnum) -> Self {
            Self { enum_one: value }
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

    pub struct MsgSingleField93 {
        pub enum_fourty_two: self::_puroro_root::proto2_defaults::MyEnum,
    }

    impl ::puroro::Message<super::Msg> for MsgSingleField93 {}

    impl super::_puroro_traits::MsgTrait for MsgSingleField93 {
        fn enum_fourty_two_opt<'this>(
            &'this self,
        ) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
            ::std::option::Option::Some(::std::clone::Clone::clone(&self.enum_fourty_two))
        }
    }

    impl ::puroro::internal::SerializableMessageToIoWrite for MsgSingleField93 {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            use ::puroro::internal::impls::single_field::se::SerFieldToIoWrite;
            if <Self as super::_puroro_traits::MsgTrait>::enum_fourty_two(self)
                == <() as super::_puroro_traits::MsgTrait>::enum_fourty_two(&())
            {
                return ::std::result::Result::Ok(());
            }
            SerFieldToIoWrite::<
                ::puroro::tags::Optional,
                ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>,
            >::ser_field::<(), _, _>(::std::iter::once(&self.enum_fourty_two), 93, out)?;
            ::std::result::Result::Ok(())
        }
    }

    impl ::std::convert::From<self::_puroro_root::proto2_defaults::MyEnum> for MsgSingleField93 {
        fn from(value: self::_puroro_root::proto2_defaults::MyEnum) -> Self {
            Self {
                enum_fourty_two: value,
            }
        }
    }
    pub struct MsgBuilder<T>(T);

    impl<T> MsgBuilder<T>
    where
        T: MsgTrait,
    {
        pub fn append_i32_default(self, value: i32) -> MsgBuilder<(T, MsgSingleField1)> {
            MsgBuilder((self.0, MsgSingleField1 { i32_default: value }))
        }

        pub fn append_i32_0(self, value: i32) -> MsgBuilder<(T, MsgSingleField2)> {
            MsgBuilder((self.0, MsgSingleField2 { i32_0: value }))
        }

        pub fn append_i32_42(self, value: i32) -> MsgBuilder<(T, MsgSingleField3)> {
            MsgBuilder((self.0, MsgSingleField3 { i32_42: value }))
        }

        pub fn append_i32_m42(self, value: i32) -> MsgBuilder<(T, MsgSingleField4)> {
            MsgBuilder((self.0, MsgSingleField4 { i32_m42: value }))
        }

        pub fn append_i32_2147483647(self, value: i32) -> MsgBuilder<(T, MsgSingleField5)> {
            MsgBuilder((
                self.0,
                MsgSingleField5 {
                    i32_2147483647: value,
                },
            ))
        }

        pub fn append_i32_m2147483648(self, value: i32) -> MsgBuilder<(T, MsgSingleField6)> {
            MsgBuilder((
                self.0,
                MsgSingleField6 {
                    i32_m2147483648: value,
                },
            ))
        }

        pub fn append_i32_0123(self, value: i32) -> MsgBuilder<(T, MsgSingleField7)> {
            MsgBuilder((self.0, MsgSingleField7 { i32_0123: value }))
        }

        pub fn append_i32_0x123(self, value: i32) -> MsgBuilder<(T, MsgSingleField8)> {
            MsgBuilder((self.0, MsgSingleField8 { i32_0x123: value }))
        }

        pub fn append_u32_default(self, value: u32) -> MsgBuilder<(T, MsgSingleField11)> {
            MsgBuilder((self.0, MsgSingleField11 { u32_default: value }))
        }

        pub fn append_u32_0(self, value: u32) -> MsgBuilder<(T, MsgSingleField12)> {
            MsgBuilder((self.0, MsgSingleField12 { u32_0: value }))
        }

        pub fn append_u32_42(self, value: u32) -> MsgBuilder<(T, MsgSingleField13)> {
            MsgBuilder((self.0, MsgSingleField13 { u32_42: value }))
        }

        pub fn append_u32_4294967295(self, value: u32) -> MsgBuilder<(T, MsgSingleField15)> {
            MsgBuilder((
                self.0,
                MsgSingleField15 {
                    u32_4294967295: value,
                },
            ))
        }

        pub fn append_u32_0123(self, value: u32) -> MsgBuilder<(T, MsgSingleField17)> {
            MsgBuilder((self.0, MsgSingleField17 { u32_0123: value }))
        }

        pub fn append_u32_0x123(self, value: u32) -> MsgBuilder<(T, MsgSingleField18)> {
            MsgBuilder((self.0, MsgSingleField18 { u32_0x123: value }))
        }

        pub fn append_i64_default(self, value: i64) -> MsgBuilder<(T, MsgSingleField21)> {
            MsgBuilder((self.0, MsgSingleField21 { i64_default: value }))
        }

        pub fn append_i64_0(self, value: i64) -> MsgBuilder<(T, MsgSingleField22)> {
            MsgBuilder((self.0, MsgSingleField22 { i64_0: value }))
        }

        pub fn append_i64_42(self, value: i64) -> MsgBuilder<(T, MsgSingleField23)> {
            MsgBuilder((self.0, MsgSingleField23 { i64_42: value }))
        }

        pub fn append_i64_m42(self, value: i64) -> MsgBuilder<(T, MsgSingleField24)> {
            MsgBuilder((self.0, MsgSingleField24 { i64_m42: value }))
        }

        pub fn append_i64_9223372036854775807(
            self,
            value: i64,
        ) -> MsgBuilder<(T, MsgSingleField25)> {
            MsgBuilder((
                self.0,
                MsgSingleField25 {
                    i64_9223372036854775807: value,
                },
            ))
        }

        pub fn append_i64_m9223372036854775808(
            self,
            value: i64,
        ) -> MsgBuilder<(T, MsgSingleField26)> {
            MsgBuilder((
                self.0,
                MsgSingleField26 {
                    i64_m9223372036854775808: value,
                },
            ))
        }

        pub fn append_i64_0123(self, value: i64) -> MsgBuilder<(T, MsgSingleField27)> {
            MsgBuilder((self.0, MsgSingleField27 { i64_0123: value }))
        }

        pub fn append_i64_0x123(self, value: i64) -> MsgBuilder<(T, MsgSingleField28)> {
            MsgBuilder((self.0, MsgSingleField28 { i64_0x123: value }))
        }

        pub fn append_u64_default(self, value: u64) -> MsgBuilder<(T, MsgSingleField31)> {
            MsgBuilder((self.0, MsgSingleField31 { u64_default: value }))
        }

        pub fn append_u64_0(self, value: u64) -> MsgBuilder<(T, MsgSingleField32)> {
            MsgBuilder((self.0, MsgSingleField32 { u64_0: value }))
        }

        pub fn append_u64_42(self, value: u64) -> MsgBuilder<(T, MsgSingleField33)> {
            MsgBuilder((self.0, MsgSingleField33 { u64_42: value }))
        }

        pub fn append_u64_18446744073709551615(
            self,
            value: u64,
        ) -> MsgBuilder<(T, MsgSingleField35)> {
            MsgBuilder((
                self.0,
                MsgSingleField35 {
                    u64_18446744073709551615: value,
                },
            ))
        }

        pub fn append_u64_0123(self, value: u64) -> MsgBuilder<(T, MsgSingleField37)> {
            MsgBuilder((self.0, MsgSingleField37 { u64_0123: value }))
        }

        pub fn append_u64_0x123(self, value: u64) -> MsgBuilder<(T, MsgSingleField38)> {
            MsgBuilder((self.0, MsgSingleField38 { u64_0x123: value }))
        }

        pub fn append_f32_default(self, value: f32) -> MsgBuilder<(T, MsgSingleField41)> {
            MsgBuilder((self.0, MsgSingleField41 { f32_default: value }))
        }

        pub fn append_f32_0(self, value: f32) -> MsgBuilder<(T, MsgSingleField42)> {
            MsgBuilder((self.0, MsgSingleField42 { f32_0: value }))
        }

        pub fn append_f32_m0(self, value: f32) -> MsgBuilder<(T, MsgSingleField43)> {
            MsgBuilder((self.0, MsgSingleField43 { f32_m0: value }))
        }

        pub fn append_f32_0p(self, value: f32) -> MsgBuilder<(T, MsgSingleField44)> {
            MsgBuilder((self.0, MsgSingleField44 { f32_0p: value }))
        }

        pub fn append_f32_p0(self, value: f32) -> MsgBuilder<(T, MsgSingleField45)> {
            MsgBuilder((self.0, MsgSingleField45 { f32_p0: value }))
        }

        pub fn append_f32_0p0(self, value: f32) -> MsgBuilder<(T, MsgSingleField46)> {
            MsgBuilder((self.0, MsgSingleField46 { f32_0p0: value }))
        }

        pub fn append_f32_42(self, value: f32) -> MsgBuilder<(T, MsgSingleField47)> {
            MsgBuilder((self.0, MsgSingleField47 { f32_42: value }))
        }

        pub fn append_f32_m42(self, value: f32) -> MsgBuilder<(T, MsgSingleField48)> {
            MsgBuilder((self.0, MsgSingleField48 { f32_m42: value }))
        }

        pub fn append_f32_0p25(self, value: f32) -> MsgBuilder<(T, MsgSingleField49)> {
            MsgBuilder((self.0, MsgSingleField49 { f32_0p25: value }))
        }

        pub fn append_f32_1p5e2(self, value: f32) -> MsgBuilder<(T, MsgSingleField50)> {
            MsgBuilder((self.0, MsgSingleField50 { f32_1p5e2: value }))
        }

        pub fn append_f32_inf(self, value: f32) -> MsgBuilder<(T, MsgSingleField51)> {
            MsgBuilder((self.0, MsgSingleField51 { f32_inf: value }))
        }

        pub fn append_f32_minf(self, value: f32) -> MsgBuilder<(T, MsgSingleField52)> {
            MsgBuilder((self.0, MsgSingleField52 { f32_minf: value }))
        }

        pub fn append_f32_nan(self, value: f32) -> MsgBuilder<(T, MsgSingleField53)> {
            MsgBuilder((self.0, MsgSingleField53 { f32_nan: value }))
        }

        pub fn append_f32_mnan(self, value: f32) -> MsgBuilder<(T, MsgSingleField54)> {
            MsgBuilder((self.0, MsgSingleField54 { f32_mnan: value }))
        }

        pub fn append_bool_default(self, value: bool) -> MsgBuilder<(T, MsgSingleField61)> {
            MsgBuilder((
                self.0,
                MsgSingleField61 {
                    bool_default: value,
                },
            ))
        }

        pub fn append_bool_true(self, value: bool) -> MsgBuilder<(T, MsgSingleField62)> {
            MsgBuilder((self.0, MsgSingleField62 { bool_true: value }))
        }

        pub fn append_bool_false(self, value: bool) -> MsgBuilder<(T, MsgSingleField63)> {
            MsgBuilder((self.0, MsgSingleField63 { bool_false: value }))
        }

        pub fn append_string_default<ScalarType>(
            self,
            value: ScalarType,
        ) -> MsgBuilder<(T, MsgSingleField71<ScalarType>)>
        where
            ScalarType: ::std::convert::AsRef<str>
                + ::std::clone::Clone
                + ::std::cmp::PartialEq
                + ::std::fmt::Debug,
        {
            MsgBuilder((
                self.0,
                MsgSingleField71 {
                    string_default: value,
                },
            ))
        }

        pub fn append_string_empty<ScalarType>(
            self,
            value: ScalarType,
        ) -> MsgBuilder<(T, MsgSingleField72<ScalarType>)>
        where
            ScalarType: ::std::convert::AsRef<str>
                + ::std::clone::Clone
                + ::std::cmp::PartialEq
                + ::std::fmt::Debug,
        {
            MsgBuilder((
                self.0,
                MsgSingleField72 {
                    string_empty: value,
                },
            ))
        }

        pub fn append_string_abc<ScalarType>(
            self,
            value: ScalarType,
        ) -> MsgBuilder<(T, MsgSingleField73<ScalarType>)>
        where
            ScalarType: ::std::convert::AsRef<str>
                + ::std::clone::Clone
                + ::std::cmp::PartialEq
                + ::std::fmt::Debug,
        {
            MsgBuilder((self.0, MsgSingleField73 { string_abc: value }))
        }

        pub fn append_string_aiu<ScalarType>(
            self,
            value: ScalarType,
        ) -> MsgBuilder<(T, MsgSingleField74<ScalarType>)>
        where
            ScalarType: ::std::convert::AsRef<str>
                + ::std::clone::Clone
                + ::std::cmp::PartialEq
                + ::std::fmt::Debug,
        {
            MsgBuilder((self.0, MsgSingleField74 { string_aiu: value }))
        }

        pub fn append_string_backslash<ScalarType>(
            self,
            value: ScalarType,
        ) -> MsgBuilder<(T, MsgSingleField75<ScalarType>)>
        where
            ScalarType: ::std::convert::AsRef<str>
                + ::std::clone::Clone
                + ::std::cmp::PartialEq
                + ::std::fmt::Debug,
        {
            MsgBuilder((
                self.0,
                MsgSingleField75 {
                    string_backslash: value,
                },
            ))
        }

        pub fn append_string_tab<ScalarType>(
            self,
            value: ScalarType,
        ) -> MsgBuilder<(T, MsgSingleField76<ScalarType>)>
        where
            ScalarType: ::std::convert::AsRef<str>
                + ::std::clone::Clone
                + ::std::cmp::PartialEq
                + ::std::fmt::Debug,
        {
            MsgBuilder((self.0, MsgSingleField76 { string_tab: value }))
        }

        pub fn append_string_crlf<ScalarType>(
            self,
            value: ScalarType,
        ) -> MsgBuilder<(T, MsgSingleField77<ScalarType>)>
        where
            ScalarType: ::std::convert::AsRef<str>
                + ::std::clone::Clone
                + ::std::cmp::PartialEq
                + ::std::fmt::Debug,
        {
            MsgBuilder((self.0, MsgSingleField77 { string_crlf: value }))
        }

        pub fn append_bytes_default<ScalarType>(
            self,
            value: ScalarType,
        ) -> MsgBuilder<(T, MsgSingleField81<ScalarType>)>
        where
            ScalarType: ::std::convert::AsRef<[u8]>
                + ::std::clone::Clone
                + ::std::cmp::PartialEq
                + ::std::fmt::Debug,
        {
            MsgBuilder((
                self.0,
                MsgSingleField81 {
                    bytes_default: value,
                },
            ))
        }

        pub fn append_bytes_empty<ScalarType>(
            self,
            value: ScalarType,
        ) -> MsgBuilder<(T, MsgSingleField82<ScalarType>)>
        where
            ScalarType: ::std::convert::AsRef<[u8]>
                + ::std::clone::Clone
                + ::std::cmp::PartialEq
                + ::std::fmt::Debug,
        {
            MsgBuilder((self.0, MsgSingleField82 { bytes_empty: value }))
        }

        pub fn append_bytes_abc<ScalarType>(
            self,
            value: ScalarType,
        ) -> MsgBuilder<(T, MsgSingleField83<ScalarType>)>
        where
            ScalarType: ::std::convert::AsRef<[u8]>
                + ::std::clone::Clone
                + ::std::cmp::PartialEq
                + ::std::fmt::Debug,
        {
            MsgBuilder((self.0, MsgSingleField83 { bytes_abc: value }))
        }

        pub fn append_bytes_aiu<ScalarType>(
            self,
            value: ScalarType,
        ) -> MsgBuilder<(T, MsgSingleField84<ScalarType>)>
        where
            ScalarType: ::std::convert::AsRef<[u8]>
                + ::std::clone::Clone
                + ::std::cmp::PartialEq
                + ::std::fmt::Debug,
        {
            MsgBuilder((self.0, MsgSingleField84 { bytes_aiu: value }))
        }

        pub fn append_bytes_backslash<ScalarType>(
            self,
            value: ScalarType,
        ) -> MsgBuilder<(T, MsgSingleField85<ScalarType>)>
        where
            ScalarType: ::std::convert::AsRef<[u8]>
                + ::std::clone::Clone
                + ::std::cmp::PartialEq
                + ::std::fmt::Debug,
        {
            MsgBuilder((
                self.0,
                MsgSingleField85 {
                    bytes_backslash: value,
                },
            ))
        }

        pub fn append_bytes_tab<ScalarType>(
            self,
            value: ScalarType,
        ) -> MsgBuilder<(T, MsgSingleField86<ScalarType>)>
        where
            ScalarType: ::std::convert::AsRef<[u8]>
                + ::std::clone::Clone
                + ::std::cmp::PartialEq
                + ::std::fmt::Debug,
        {
            MsgBuilder((self.0, MsgSingleField86 { bytes_tab: value }))
        }

        pub fn append_bytes_crlf<ScalarType>(
            self,
            value: ScalarType,
        ) -> MsgBuilder<(T, MsgSingleField87<ScalarType>)>
        where
            ScalarType: ::std::convert::AsRef<[u8]>
                + ::std::clone::Clone
                + ::std::cmp::PartialEq
                + ::std::fmt::Debug,
        {
            MsgBuilder((self.0, MsgSingleField87 { bytes_crlf: value }))
        }

        pub fn append_enum_default(
            self,
            value: self::_puroro_root::proto2_defaults::MyEnum,
        ) -> MsgBuilder<(T, MsgSingleField91)> {
            MsgBuilder((
                self.0,
                MsgSingleField91 {
                    enum_default: value,
                },
            ))
        }

        pub fn append_enum_one(
            self,
            value: self::_puroro_root::proto2_defaults::MyEnum,
        ) -> MsgBuilder<(T, MsgSingleField92)> {
            MsgBuilder((self.0, MsgSingleField92 { enum_one: value }))
        }

        pub fn append_enum_fourty_two(
            self,
            value: self::_puroro_root::proto2_defaults::MyEnum,
        ) -> MsgBuilder<(T, MsgSingleField93)> {
            MsgBuilder((
                self.0,
                MsgSingleField93 {
                    enum_fourty_two: value,
                },
            ))
        }

        pub fn build(self) -> T {
            self.0
        }
    }

    impl MsgBuilder<()> {
        pub fn new() -> Self {
            Self(())
        }
    }
}
pub use _puroro_traits::*;
pub mod _puroro_traits {
    mod _puroro_root {
        pub use super::super::_puroro_root::*;
    }

    pub trait MsgTrait {
        fn i32_default<'this>(&'this self) -> i32 {
            self.i32_default_opt()
                .unwrap_or_else(::std::default::Default::default)
        }
        fn has_i32_default<'this>(&'this self) -> bool {
            self.i32_default_opt().is_some()
        }
        fn i32_default_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::option::Option::None
        }
        fn i32_0<'this>(&'this self) -> i32 {
            self.i32_0_opt().unwrap_or(0)
        }
        fn has_i32_0<'this>(&'this self) -> bool {
            self.i32_0_opt().is_some()
        }
        fn i32_0_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::option::Option::None
        }
        fn i32_42<'this>(&'this self) -> i32 {
            self.i32_42_opt().unwrap_or(42)
        }
        fn has_i32_42<'this>(&'this self) -> bool {
            self.i32_42_opt().is_some()
        }
        fn i32_42_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::option::Option::None
        }
        fn i32_m42<'this>(&'this self) -> i32 {
            self.i32_m42_opt().unwrap_or(-42)
        }
        fn has_i32_m42<'this>(&'this self) -> bool {
            self.i32_m42_opt().is_some()
        }
        fn i32_m42_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::option::Option::None
        }
        fn i32_2147483647<'this>(&'this self) -> i32 {
            self.i32_2147483647_opt().unwrap_or(2147483647)
        }
        fn has_i32_2147483647<'this>(&'this self) -> bool {
            self.i32_2147483647_opt().is_some()
        }
        fn i32_2147483647_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::option::Option::None
        }
        fn i32_m2147483648<'this>(&'this self) -> i32 {
            self.i32_m2147483648_opt().unwrap_or(-2147483648)
        }
        fn has_i32_m2147483648<'this>(&'this self) -> bool {
            self.i32_m2147483648_opt().is_some()
        }
        fn i32_m2147483648_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::option::Option::None
        }
        fn i32_0123<'this>(&'this self) -> i32 {
            self.i32_0123_opt().unwrap_or(83)
        }
        fn has_i32_0123<'this>(&'this self) -> bool {
            self.i32_0123_opt().is_some()
        }
        fn i32_0123_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::option::Option::None
        }
        fn i32_0x123<'this>(&'this self) -> i32 {
            self.i32_0x123_opt().unwrap_or(291)
        }
        fn has_i32_0x123<'this>(&'this self) -> bool {
            self.i32_0x123_opt().is_some()
        }
        fn i32_0x123_opt<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::option::Option::None
        }
        fn u32_default<'this>(&'this self) -> u32 {
            self.u32_default_opt()
                .unwrap_or_else(::std::default::Default::default)
        }
        fn has_u32_default<'this>(&'this self) -> bool {
            self.u32_default_opt().is_some()
        }
        fn u32_default_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            ::std::option::Option::None
        }
        fn u32_0<'this>(&'this self) -> u32 {
            self.u32_0_opt().unwrap_or(0)
        }
        fn has_u32_0<'this>(&'this self) -> bool {
            self.u32_0_opt().is_some()
        }
        fn u32_0_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            ::std::option::Option::None
        }
        fn u32_42<'this>(&'this self) -> u32 {
            self.u32_42_opt().unwrap_or(42)
        }
        fn has_u32_42<'this>(&'this self) -> bool {
            self.u32_42_opt().is_some()
        }
        fn u32_42_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            ::std::option::Option::None
        }
        fn u32_4294967295<'this>(&'this self) -> u32 {
            self.u32_4294967295_opt().unwrap_or(4294967295)
        }
        fn has_u32_4294967295<'this>(&'this self) -> bool {
            self.u32_4294967295_opt().is_some()
        }
        fn u32_4294967295_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            ::std::option::Option::None
        }
        fn u32_0123<'this>(&'this self) -> u32 {
            self.u32_0123_opt().unwrap_or(83)
        }
        fn has_u32_0123<'this>(&'this self) -> bool {
            self.u32_0123_opt().is_some()
        }
        fn u32_0123_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            ::std::option::Option::None
        }
        fn u32_0x123<'this>(&'this self) -> u32 {
            self.u32_0x123_opt().unwrap_or(291)
        }
        fn has_u32_0x123<'this>(&'this self) -> bool {
            self.u32_0x123_opt().is_some()
        }
        fn u32_0x123_opt<'this>(&'this self) -> ::std::option::Option<u32> {
            ::std::option::Option::None
        }
        fn i64_default<'this>(&'this self) -> i64 {
            self.i64_default_opt()
                .unwrap_or_else(::std::default::Default::default)
        }
        fn has_i64_default<'this>(&'this self) -> bool {
            self.i64_default_opt().is_some()
        }
        fn i64_default_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::option::Option::None
        }
        fn i64_0<'this>(&'this self) -> i64 {
            self.i64_0_opt().unwrap_or(0)
        }
        fn has_i64_0<'this>(&'this self) -> bool {
            self.i64_0_opt().is_some()
        }
        fn i64_0_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::option::Option::None
        }
        fn i64_42<'this>(&'this self) -> i64 {
            self.i64_42_opt().unwrap_or(42)
        }
        fn has_i64_42<'this>(&'this self) -> bool {
            self.i64_42_opt().is_some()
        }
        fn i64_42_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::option::Option::None
        }
        fn i64_m42<'this>(&'this self) -> i64 {
            self.i64_m42_opt().unwrap_or(-42)
        }
        fn has_i64_m42<'this>(&'this self) -> bool {
            self.i64_m42_opt().is_some()
        }
        fn i64_m42_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::option::Option::None
        }
        fn i64_9223372036854775807<'this>(&'this self) -> i64 {
            self.i64_9223372036854775807_opt()
                .unwrap_or(9223372036854775807)
        }
        fn has_i64_9223372036854775807<'this>(&'this self) -> bool {
            self.i64_9223372036854775807_opt().is_some()
        }
        fn i64_9223372036854775807_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::option::Option::None
        }
        fn i64_m9223372036854775808<'this>(&'this self) -> i64 {
            self.i64_m9223372036854775808_opt()
                .unwrap_or(-9223372036854775808)
        }
        fn has_i64_m9223372036854775808<'this>(&'this self) -> bool {
            self.i64_m9223372036854775808_opt().is_some()
        }
        fn i64_m9223372036854775808_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::option::Option::None
        }
        fn i64_0123<'this>(&'this self) -> i64 {
            self.i64_0123_opt().unwrap_or(83)
        }
        fn has_i64_0123<'this>(&'this self) -> bool {
            self.i64_0123_opt().is_some()
        }
        fn i64_0123_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::option::Option::None
        }
        fn i64_0x123<'this>(&'this self) -> i64 {
            self.i64_0x123_opt().unwrap_or(291)
        }
        fn has_i64_0x123<'this>(&'this self) -> bool {
            self.i64_0x123_opt().is_some()
        }
        fn i64_0x123_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::option::Option::None
        }
        fn u64_default<'this>(&'this self) -> u64 {
            self.u64_default_opt()
                .unwrap_or_else(::std::default::Default::default)
        }
        fn has_u64_default<'this>(&'this self) -> bool {
            self.u64_default_opt().is_some()
        }
        fn u64_default_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            ::std::option::Option::None
        }
        fn u64_0<'this>(&'this self) -> u64 {
            self.u64_0_opt().unwrap_or(0)
        }
        fn has_u64_0<'this>(&'this self) -> bool {
            self.u64_0_opt().is_some()
        }
        fn u64_0_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            ::std::option::Option::None
        }
        fn u64_42<'this>(&'this self) -> u64 {
            self.u64_42_opt().unwrap_or(42)
        }
        fn has_u64_42<'this>(&'this self) -> bool {
            self.u64_42_opt().is_some()
        }
        fn u64_42_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            ::std::option::Option::None
        }
        fn u64_18446744073709551615<'this>(&'this self) -> u64 {
            self.u64_18446744073709551615_opt()
                .unwrap_or(18446744073709551615)
        }
        fn has_u64_18446744073709551615<'this>(&'this self) -> bool {
            self.u64_18446744073709551615_opt().is_some()
        }
        fn u64_18446744073709551615_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            ::std::option::Option::None
        }
        fn u64_0123<'this>(&'this self) -> u64 {
            self.u64_0123_opt().unwrap_or(83)
        }
        fn has_u64_0123<'this>(&'this self) -> bool {
            self.u64_0123_opt().is_some()
        }
        fn u64_0123_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            ::std::option::Option::None
        }
        fn u64_0x123<'this>(&'this self) -> u64 {
            self.u64_0x123_opt().unwrap_or(291)
        }
        fn has_u64_0x123<'this>(&'this self) -> bool {
            self.u64_0x123_opt().is_some()
        }
        fn u64_0x123_opt<'this>(&'this self) -> ::std::option::Option<u64> {
            ::std::option::Option::None
        }
        fn f32_default<'this>(&'this self) -> f32 {
            self.f32_default_opt()
                .unwrap_or_else(::std::default::Default::default)
        }
        fn has_f32_default<'this>(&'this self) -> bool {
            self.f32_default_opt().is_some()
        }
        fn f32_default_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::None
        }
        fn f32_0<'this>(&'this self) -> f32 {
            self.f32_0_opt().unwrap_or(0f32)
        }
        fn has_f32_0<'this>(&'this self) -> bool {
            self.f32_0_opt().is_some()
        }
        fn f32_0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::None
        }
        fn f32_m0<'this>(&'this self) -> f32 {
            self.f32_m0_opt().unwrap_or(-0f32)
        }
        fn has_f32_m0<'this>(&'this self) -> bool {
            self.f32_m0_opt().is_some()
        }
        fn f32_m0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::None
        }
        fn f32_0p<'this>(&'this self) -> f32 {
            self.f32_0p_opt().unwrap_or(0f32)
        }
        fn has_f32_0p<'this>(&'this self) -> bool {
            self.f32_0p_opt().is_some()
        }
        fn f32_0p_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::None
        }
        fn f32_p0<'this>(&'this self) -> f32 {
            self.f32_p0_opt().unwrap_or(0f32)
        }
        fn has_f32_p0<'this>(&'this self) -> bool {
            self.f32_p0_opt().is_some()
        }
        fn f32_p0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::None
        }
        fn f32_0p0<'this>(&'this self) -> f32 {
            self.f32_0p0_opt().unwrap_or(0f32)
        }
        fn has_f32_0p0<'this>(&'this self) -> bool {
            self.f32_0p0_opt().is_some()
        }
        fn f32_0p0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::None
        }
        fn f32_42<'this>(&'this self) -> f32 {
            self.f32_42_opt().unwrap_or(42f32)
        }
        fn has_f32_42<'this>(&'this self) -> bool {
            self.f32_42_opt().is_some()
        }
        fn f32_42_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::None
        }
        fn f32_m42<'this>(&'this self) -> f32 {
            self.f32_m42_opt().unwrap_or(-42f32)
        }
        fn has_f32_m42<'this>(&'this self) -> bool {
            self.f32_m42_opt().is_some()
        }
        fn f32_m42_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::None
        }
        fn f32_0p25<'this>(&'this self) -> f32 {
            self.f32_0p25_opt().unwrap_or(0.25f32)
        }
        fn has_f32_0p25<'this>(&'this self) -> bool {
            self.f32_0p25_opt().is_some()
        }
        fn f32_0p25_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::None
        }
        fn f32_1p5e2<'this>(&'this self) -> f32 {
            self.f32_1p5e2_opt().unwrap_or(150f32)
        }
        fn has_f32_1p5e2<'this>(&'this self) -> bool {
            self.f32_1p5e2_opt().is_some()
        }
        fn f32_1p5e2_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::None
        }
        fn f32_inf<'this>(&'this self) -> f32 {
            self.f32_inf_opt().unwrap_or(f32::INFINITY)
        }
        fn has_f32_inf<'this>(&'this self) -> bool {
            self.f32_inf_opt().is_some()
        }
        fn f32_inf_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::None
        }
        fn f32_minf<'this>(&'this self) -> f32 {
            self.f32_minf_opt().unwrap_or(f32::NEG_INFINITY)
        }
        fn has_f32_minf<'this>(&'this self) -> bool {
            self.f32_minf_opt().is_some()
        }
        fn f32_minf_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::None
        }
        fn f32_nan<'this>(&'this self) -> f32 {
            self.f32_nan_opt().unwrap_or(f32::NAN)
        }
        fn has_f32_nan<'this>(&'this self) -> bool {
            self.f32_nan_opt().is_some()
        }
        fn f32_nan_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::None
        }
        fn f32_mnan<'this>(&'this self) -> f32 {
            self.f32_mnan_opt().unwrap_or(f32::NAN)
        }
        fn has_f32_mnan<'this>(&'this self) -> bool {
            self.f32_mnan_opt().is_some()
        }
        fn f32_mnan_opt<'this>(&'this self) -> ::std::option::Option<f32> {
            ::std::option::Option::None
        }
        fn bool_default<'this>(&'this self) -> bool {
            self.bool_default_opt()
                .unwrap_or_else(::std::default::Default::default)
        }
        fn has_bool_default<'this>(&'this self) -> bool {
            self.bool_default_opt().is_some()
        }
        fn bool_default_opt<'this>(&'this self) -> ::std::option::Option<bool> {
            ::std::option::Option::None
        }
        fn bool_true<'this>(&'this self) -> bool {
            self.bool_true_opt().unwrap_or(true)
        }
        fn has_bool_true<'this>(&'this self) -> bool {
            self.bool_true_opt().is_some()
        }
        fn bool_true_opt<'this>(&'this self) -> ::std::option::Option<bool> {
            ::std::option::Option::None
        }
        fn bool_false<'this>(&'this self) -> bool {
            self.bool_false_opt().unwrap_or(false)
        }
        fn has_bool_false<'this>(&'this self) -> bool {
            self.bool_false_opt().is_some()
        }
        fn bool_false_opt<'this>(&'this self) -> ::std::option::Option<bool> {
            ::std::option::Option::None
        }
        fn string_default<'this>(&'this self) -> &'this str {
            self.string_default_opt()
                .unwrap_or_else(::std::default::Default::default)
        }
        fn has_string_default<'this>(&'this self) -> bool {
            self.string_default_opt().is_some()
        }
        fn string_default_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            ::std::option::Option::None
        }
        fn string_empty<'this>(&'this self) -> &'this str {
            self.string_empty_opt().unwrap_or("")
        }
        fn has_string_empty<'this>(&'this self) -> bool {
            self.string_empty_opt().is_some()
        }
        fn string_empty_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            ::std::option::Option::None
        }
        fn string_abc<'this>(&'this self) -> &'this str {
            self.string_abc_opt().unwrap_or("abc")
        }
        fn has_string_abc<'this>(&'this self) -> bool {
            self.string_abc_opt().is_some()
        }
        fn string_abc_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            ::std::option::Option::None
        }
        fn string_aiu<'this>(&'this self) -> &'this str {
            self.string_aiu_opt().unwrap_or("\u{3042}\u{3044}\u{3046}")
        }
        fn has_string_aiu<'this>(&'this self) -> bool {
            self.string_aiu_opt().is_some()
        }
        fn string_aiu_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            ::std::option::Option::None
        }
        fn string_backslash<'this>(&'this self) -> &'this str {
            self.string_backslash_opt().unwrap_or("\\")
        }
        fn has_string_backslash<'this>(&'this self) -> bool {
            self.string_backslash_opt().is_some()
        }
        fn string_backslash_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            ::std::option::Option::None
        }
        fn string_tab<'this>(&'this self) -> &'this str {
            self.string_tab_opt().unwrap_or("\t")
        }
        fn has_string_tab<'this>(&'this self) -> bool {
            self.string_tab_opt().is_some()
        }
        fn string_tab_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            ::std::option::Option::None
        }
        fn string_crlf<'this>(&'this self) -> &'this str {
            self.string_crlf_opt().unwrap_or("\r\n")
        }
        fn has_string_crlf<'this>(&'this self) -> bool {
            self.string_crlf_opt().is_some()
        }
        fn string_crlf_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
            ::std::option::Option::None
        }
        fn bytes_default<'this>(&'this self) -> &'this [u8] {
            self.bytes_default_opt()
                .unwrap_or_else(::std::default::Default::default)
        }
        fn has_bytes_default<'this>(&'this self) -> bool {
            self.bytes_default_opt().is_some()
        }
        fn bytes_default_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            ::std::option::Option::None
        }
        fn bytes_empty<'this>(&'this self) -> &'this [u8] {
            self.bytes_empty_opt().unwrap_or(b"")
        }
        fn has_bytes_empty<'this>(&'this self) -> bool {
            self.bytes_empty_opt().is_some()
        }
        fn bytes_empty_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            ::std::option::Option::None
        }
        fn bytes_abc<'this>(&'this self) -> &'this [u8] {
            self.bytes_abc_opt().unwrap_or(b"\x61\x62\x63")
        }
        fn has_bytes_abc<'this>(&'this self) -> bool {
            self.bytes_abc_opt().is_some()
        }
        fn bytes_abc_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            ::std::option::Option::None
        }
        fn bytes_aiu<'this>(&'this self) -> &'this [u8] {
            self.bytes_aiu_opt()
                .unwrap_or(b"\xe3\x81\x82\xe3\x81\x84\xe3\x81\x86")
        }
        fn has_bytes_aiu<'this>(&'this self) -> bool {
            self.bytes_aiu_opt().is_some()
        }
        fn bytes_aiu_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            ::std::option::Option::None
        }
        fn bytes_backslash<'this>(&'this self) -> &'this [u8] {
            self.bytes_backslash_opt().unwrap_or(b"\x5c")
        }
        fn has_bytes_backslash<'this>(&'this self) -> bool {
            self.bytes_backslash_opt().is_some()
        }
        fn bytes_backslash_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            ::std::option::Option::None
        }
        fn bytes_tab<'this>(&'this self) -> &'this [u8] {
            self.bytes_tab_opt().unwrap_or(b"\x09")
        }
        fn has_bytes_tab<'this>(&'this self) -> bool {
            self.bytes_tab_opt().is_some()
        }
        fn bytes_tab_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            ::std::option::Option::None
        }
        fn bytes_crlf<'this>(&'this self) -> &'this [u8] {
            self.bytes_crlf_opt().unwrap_or(b"\x0d\x0a")
        }
        fn has_bytes_crlf<'this>(&'this self) -> bool {
            self.bytes_crlf_opt().is_some()
        }
        fn bytes_crlf_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
            ::std::option::Option::None
        }
        fn enum_default<'this>(&'this self) -> self::_puroro_root::proto2_defaults::MyEnum {
            self.enum_default_opt()
                .unwrap_or_else(::std::default::Default::default)
        }
        fn has_enum_default<'this>(&'this self) -> bool {
            self.enum_default_opt().is_some()
        }
        fn enum_default_opt<'this>(
            &'this self,
        ) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
            ::std::option::Option::None
        }
        fn enum_one<'this>(&'this self) -> self::_puroro_root::proto2_defaults::MyEnum {
            self.enum_one_opt()
                .unwrap_or(self::_puroro_root::proto2_defaults::MyEnum::One)
        }
        fn has_enum_one<'this>(&'this self) -> bool {
            self.enum_one_opt().is_some()
        }
        fn enum_one_opt<'this>(
            &'this self,
        ) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
            ::std::option::Option::None
        }
        fn enum_fourty_two<'this>(&'this self) -> self::_puroro_root::proto2_defaults::MyEnum {
            self.enum_fourty_two_opt()
                .unwrap_or(self::_puroro_root::proto2_defaults::MyEnum::FourtyTwo)
        }
        fn has_enum_fourty_two<'this>(&'this self) -> bool {
            self.enum_fourty_two_opt().is_some()
        }
        fn enum_fourty_two_opt<'this>(
            &'this self,
        ) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
            ::std::option::Option::None
        }
    }

    macro_rules! msg_delegate {
        ($ty:ty) => {
            fn i32_default_opt<'this>(&'this self) -> ::std::option::Option<i32> {
                (**self).i32_default_opt()
            }
            fn i32_0_opt<'this>(&'this self) -> ::std::option::Option<i32> {
                (**self).i32_0_opt()
            }
            fn i32_42_opt<'this>(&'this self) -> ::std::option::Option<i32> {
                (**self).i32_42_opt()
            }
            fn i32_m42_opt<'this>(&'this self) -> ::std::option::Option<i32> {
                (**self).i32_m42_opt()
            }
            fn i32_2147483647_opt<'this>(&'this self) -> ::std::option::Option<i32> {
                (**self).i32_2147483647_opt()
            }
            fn i32_m2147483648_opt<'this>(&'this self) -> ::std::option::Option<i32> {
                (**self).i32_m2147483648_opt()
            }
            fn i32_0123_opt<'this>(&'this self) -> ::std::option::Option<i32> {
                (**self).i32_0123_opt()
            }
            fn i32_0x123_opt<'this>(&'this self) -> ::std::option::Option<i32> {
                (**self).i32_0x123_opt()
            }
            fn u32_default_opt<'this>(&'this self) -> ::std::option::Option<u32> {
                (**self).u32_default_opt()
            }
            fn u32_0_opt<'this>(&'this self) -> ::std::option::Option<u32> {
                (**self).u32_0_opt()
            }
            fn u32_42_opt<'this>(&'this self) -> ::std::option::Option<u32> {
                (**self).u32_42_opt()
            }
            fn u32_4294967295_opt<'this>(&'this self) -> ::std::option::Option<u32> {
                (**self).u32_4294967295_opt()
            }
            fn u32_0123_opt<'this>(&'this self) -> ::std::option::Option<u32> {
                (**self).u32_0123_opt()
            }
            fn u32_0x123_opt<'this>(&'this self) -> ::std::option::Option<u32> {
                (**self).u32_0x123_opt()
            }
            fn i64_default_opt<'this>(&'this self) -> ::std::option::Option<i64> {
                (**self).i64_default_opt()
            }
            fn i64_0_opt<'this>(&'this self) -> ::std::option::Option<i64> {
                (**self).i64_0_opt()
            }
            fn i64_42_opt<'this>(&'this self) -> ::std::option::Option<i64> {
                (**self).i64_42_opt()
            }
            fn i64_m42_opt<'this>(&'this self) -> ::std::option::Option<i64> {
                (**self).i64_m42_opt()
            }
            fn i64_9223372036854775807_opt<'this>(&'this self) -> ::std::option::Option<i64> {
                (**self).i64_9223372036854775807_opt()
            }
            fn i64_m9223372036854775808_opt<'this>(&'this self) -> ::std::option::Option<i64> {
                (**self).i64_m9223372036854775808_opt()
            }
            fn i64_0123_opt<'this>(&'this self) -> ::std::option::Option<i64> {
                (**self).i64_0123_opt()
            }
            fn i64_0x123_opt<'this>(&'this self) -> ::std::option::Option<i64> {
                (**self).i64_0x123_opt()
            }
            fn u64_default_opt<'this>(&'this self) -> ::std::option::Option<u64> {
                (**self).u64_default_opt()
            }
            fn u64_0_opt<'this>(&'this self) -> ::std::option::Option<u64> {
                (**self).u64_0_opt()
            }
            fn u64_42_opt<'this>(&'this self) -> ::std::option::Option<u64> {
                (**self).u64_42_opt()
            }
            fn u64_18446744073709551615_opt<'this>(&'this self) -> ::std::option::Option<u64> {
                (**self).u64_18446744073709551615_opt()
            }
            fn u64_0123_opt<'this>(&'this self) -> ::std::option::Option<u64> {
                (**self).u64_0123_opt()
            }
            fn u64_0x123_opt<'this>(&'this self) -> ::std::option::Option<u64> {
                (**self).u64_0x123_opt()
            }
            fn f32_default_opt<'this>(&'this self) -> ::std::option::Option<f32> {
                (**self).f32_default_opt()
            }
            fn f32_0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
                (**self).f32_0_opt()
            }
            fn f32_m0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
                (**self).f32_m0_opt()
            }
            fn f32_0p_opt<'this>(&'this self) -> ::std::option::Option<f32> {
                (**self).f32_0p_opt()
            }
            fn f32_p0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
                (**self).f32_p0_opt()
            }
            fn f32_0p0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
                (**self).f32_0p0_opt()
            }
            fn f32_42_opt<'this>(&'this self) -> ::std::option::Option<f32> {
                (**self).f32_42_opt()
            }
            fn f32_m42_opt<'this>(&'this self) -> ::std::option::Option<f32> {
                (**self).f32_m42_opt()
            }
            fn f32_0p25_opt<'this>(&'this self) -> ::std::option::Option<f32> {
                (**self).f32_0p25_opt()
            }
            fn f32_1p5e2_opt<'this>(&'this self) -> ::std::option::Option<f32> {
                (**self).f32_1p5e2_opt()
            }
            fn f32_inf_opt<'this>(&'this self) -> ::std::option::Option<f32> {
                (**self).f32_inf_opt()
            }
            fn f32_minf_opt<'this>(&'this self) -> ::std::option::Option<f32> {
                (**self).f32_minf_opt()
            }
            fn f32_nan_opt<'this>(&'this self) -> ::std::option::Option<f32> {
                (**self).f32_nan_opt()
            }
            fn f32_mnan_opt<'this>(&'this self) -> ::std::option::Option<f32> {
                (**self).f32_mnan_opt()
            }
            fn bool_default_opt<'this>(&'this self) -> ::std::option::Option<bool> {
                (**self).bool_default_opt()
            }
            fn bool_true_opt<'this>(&'this self) -> ::std::option::Option<bool> {
                (**self).bool_true_opt()
            }
            fn bool_false_opt<'this>(&'this self) -> ::std::option::Option<bool> {
                (**self).bool_false_opt()
            }
            fn string_default_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
                (**self).string_default_opt()
            }
            fn string_empty_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
                (**self).string_empty_opt()
            }
            fn string_abc_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
                (**self).string_abc_opt()
            }
            fn string_aiu_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
                (**self).string_aiu_opt()
            }
            fn string_backslash_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
                (**self).string_backslash_opt()
            }
            fn string_tab_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
                (**self).string_tab_opt()
            }
            fn string_crlf_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
                (**self).string_crlf_opt()
            }
            fn bytes_default_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
                (**self).bytes_default_opt()
            }
            fn bytes_empty_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
                (**self).bytes_empty_opt()
            }
            fn bytes_abc_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
                (**self).bytes_abc_opt()
            }
            fn bytes_aiu_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
                (**self).bytes_aiu_opt()
            }
            fn bytes_backslash_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
                (**self).bytes_backslash_opt()
            }
            fn bytes_tab_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
                (**self).bytes_tab_opt()
            }
            fn bytes_crlf_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
                (**self).bytes_crlf_opt()
            }
            fn enum_default_opt<'this>(
                &'this self,
            ) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
                (**self).enum_default_opt()
            }
            fn enum_one_opt<'this>(
                &'this self,
            ) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
                (**self).enum_one_opt()
            }
            fn enum_fourty_two_opt<'this>(
                &'this self,
            ) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
                (**self).enum_fourty_two_opt()
            }
        };
    }

    impl<T> MsgTrait for &'_ T
    where
        T: MsgTrait,
    {
        msg_delegate!(T);
    }

    impl<T> MsgTrait for &'_ mut T
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
}
#[derive(::std::fmt::Debug, ::std::clone::Clone, ::std::cmp::PartialEq)]
pub enum MyEnum {
    One,
    FourtyTwo,
}

impl ::puroro::Enum2 for MyEnum {}
impl ::std::convert::TryFrom<i32> for MyEnum {
    type Error = i32;
    fn try_from(value: i32) -> ::std::result::Result<Self, i32> {
        ::std::result::Result::Ok(match value {
            1 => MyEnum::One,
            42 => MyEnum::FourtyTwo,
            _ => Err(value)?,
        })
    }
}

impl ::std::convert::From<MyEnum> for i32 {
    fn from(value: MyEnum) -> i32 {
        match value {
            MyEnum::One => 1,
            MyEnum::FourtyTwo => 42,
        }
    }
}

impl ::std::default::Default for MyEnum {
    fn default() -> Self {
        MyEnum::One
    }
}
pub use _puroro_nested::*;
pub mod _puroro_nested {
    pub mod msg {
        mod _puroro_root {
            pub use super::super::super::_puroro_root::*;
        }
    }
}