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
pub struct Msg {
    i32_default: ::std::option::Option<i32>,
    i32_0: ::std::option::Option<i32>,
    i32_42: ::std::option::Option<i32>,
    i32_m42: ::std::option::Option<i32>,
    i32_2147483647: ::std::option::Option<i32>,
    i32_m2147483648: ::std::option::Option<i32>,
    i32_0123: ::std::option::Option<i32>,
    i32_0x123: ::std::option::Option<i32>,
    u32_default: ::std::option::Option<u32>,
    u32_0: ::std::option::Option<u32>,
    u32_42: ::std::option::Option<u32>,
    u32_4294967295: ::std::option::Option<u32>,
    u32_0123: ::std::option::Option<u32>,
    u32_0x123: ::std::option::Option<u32>,
    i64_default: ::std::option::Option<i64>,
    i64_0: ::std::option::Option<i64>,
    i64_42: ::std::option::Option<i64>,
    i64_m42: ::std::option::Option<i64>,
    i64_9223372036854775807: ::std::option::Option<i64>,
    i64_m9223372036854775808: ::std::option::Option<i64>,
    i64_0123: ::std::option::Option<i64>,
    i64_0x123: ::std::option::Option<i64>,
    u64_default: ::std::option::Option<u64>,
    u64_0: ::std::option::Option<u64>,
    u64_42: ::std::option::Option<u64>,
    u64_18446744073709551615: ::std::option::Option<u64>,
    u64_0123: ::std::option::Option<u64>,
    u64_0x123: ::std::option::Option<u64>,
    f32_default: ::std::option::Option<f32>,
    f32_0: ::std::option::Option<f32>,
    f32_m0: ::std::option::Option<f32>,
    f32_0p: ::std::option::Option<f32>,
    f32_p0: ::std::option::Option<f32>,
    f32_0p0: ::std::option::Option<f32>,
    f32_42: ::std::option::Option<f32>,
    f32_m42: ::std::option::Option<f32>,
    f32_0p25: ::std::option::Option<f32>,
    f32_1p5e2: ::std::option::Option<f32>,
    f32_inf: ::std::option::Option<f32>,
    f32_minf: ::std::option::Option<f32>,
    f32_nan: ::std::option::Option<f32>,
    f32_mnan: ::std::option::Option<f32>,
    bool_default: ::std::option::Option<bool>,
    bool_true: ::std::option::Option<bool>,
    bool_false: ::std::option::Option<bool>,
    string_default: ::std::option::Option<::std::string::String>,
    string_empty: ::std::option::Option<::std::string::String>,
    string_abc: ::std::option::Option<::std::string::String>,
    string_aiu: ::std::option::Option<::std::string::String>,
    string_backslash: ::std::option::Option<::std::string::String>,
    string_tab: ::std::option::Option<::std::string::String>,
    string_crlf: ::std::option::Option<::std::string::String>,
    bytes_default: ::std::option::Option<::std::vec::Vec<u8>>,
    bytes_empty: ::std::option::Option<::std::vec::Vec<u8>>,
    bytes_abc: ::std::option::Option<::std::vec::Vec<u8>>,
    bytes_aiu: ::std::option::Option<::std::vec::Vec<u8>>,
    bytes_backslash: ::std::option::Option<::std::vec::Vec<u8>>,
    bytes_tab: ::std::option::Option<::std::vec::Vec<u8>>,
    bytes_crlf: ::std::option::Option<::std::vec::Vec<u8>>,
    enum_default: ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum>,
    enum_one: ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum>,
    enum_fourty_two: ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum>,
}
impl ::puroro::Message<Msg> for Msg {}

impl Msg {
    pub fn new() -> Self {
        Self {
            i32_default: ::std::default::Default::default(),
            i32_0: ::std::default::Default::default(),
            i32_42: ::std::default::Default::default(),
            i32_m42: ::std::default::Default::default(),
            i32_2147483647: ::std::default::Default::default(),
            i32_m2147483648: ::std::default::Default::default(),
            i32_0123: ::std::default::Default::default(),
            i32_0x123: ::std::default::Default::default(),
            u32_default: ::std::default::Default::default(),
            u32_0: ::std::default::Default::default(),
            u32_42: ::std::default::Default::default(),
            u32_4294967295: ::std::default::Default::default(),
            u32_0123: ::std::default::Default::default(),
            u32_0x123: ::std::default::Default::default(),
            i64_default: ::std::default::Default::default(),
            i64_0: ::std::default::Default::default(),
            i64_42: ::std::default::Default::default(),
            i64_m42: ::std::default::Default::default(),
            i64_9223372036854775807: ::std::default::Default::default(),
            i64_m9223372036854775808: ::std::default::Default::default(),
            i64_0123: ::std::default::Default::default(),
            i64_0x123: ::std::default::Default::default(),
            u64_default: ::std::default::Default::default(),
            u64_0: ::std::default::Default::default(),
            u64_42: ::std::default::Default::default(),
            u64_18446744073709551615: ::std::default::Default::default(),
            u64_0123: ::std::default::Default::default(),
            u64_0x123: ::std::default::Default::default(),
            f32_default: ::std::default::Default::default(),
            f32_0: ::std::default::Default::default(),
            f32_m0: ::std::default::Default::default(),
            f32_0p: ::std::default::Default::default(),
            f32_p0: ::std::default::Default::default(),
            f32_0p0: ::std::default::Default::default(),
            f32_42: ::std::default::Default::default(),
            f32_m42: ::std::default::Default::default(),
            f32_0p25: ::std::default::Default::default(),
            f32_1p5e2: ::std::default::Default::default(),
            f32_inf: ::std::default::Default::default(),
            f32_minf: ::std::default::Default::default(),
            f32_nan: ::std::default::Default::default(),
            f32_mnan: ::std::default::Default::default(),
            bool_default: ::std::default::Default::default(),
            bool_true: ::std::default::Default::default(),
            bool_false: ::std::default::Default::default(),
            string_default: ::std::default::Default::default(),
            string_empty: ::std::default::Default::default(),
            string_abc: ::std::default::Default::default(),
            string_aiu: ::std::default::Default::default(),
            string_backslash: ::std::default::Default::default(),
            string_tab: ::std::default::Default::default(),
            string_crlf: ::std::default::Default::default(),
            bytes_default: ::std::default::Default::default(),
            bytes_empty: ::std::default::Default::default(),
            bytes_abc: ::std::default::Default::default(),
            bytes_aiu: ::std::default::Default::default(),
            bytes_backslash: ::std::default::Default::default(),
            bytes_tab: ::std::default::Default::default(),
            bytes_crlf: ::std::default::Default::default(),
            enum_default: ::std::default::Default::default(),
            enum_one: ::std::default::Default::default(),
            enum_fourty_two: ::std::default::Default::default(),
        }
    }
    pub fn i32_default_opt(&self) -> ::std::option::Option<i32> {
        self.i32_default.clone()
    }

    pub fn has_i32_default(&self) -> bool {
        Self::i32_default_opt(self).is_some()
    }

    pub fn i32_default(&self) -> i32 {
        self.i32_default_opt().unwrap_or(
            ::std::default::Default::default()
        )
    }
    pub fn i32_0_opt(&self) -> ::std::option::Option<i32> {
        self.i32_0.clone()
    }

    pub fn has_i32_0(&self) -> bool {
        Self::i32_0_opt(self).is_some()
    }

    pub fn i32_0(&self) -> i32 {
        self.i32_0_opt().unwrap_or(
            0
        )
    }
    pub fn i32_42_opt(&self) -> ::std::option::Option<i32> {
        self.i32_42.clone()
    }

    pub fn has_i32_42(&self) -> bool {
        Self::i32_42_opt(self).is_some()
    }

    pub fn i32_42(&self) -> i32 {
        self.i32_42_opt().unwrap_or(
            42
        )
    }
    pub fn i32_m42_opt(&self) -> ::std::option::Option<i32> {
        self.i32_m42.clone()
    }

    pub fn has_i32_m42(&self) -> bool {
        Self::i32_m42_opt(self).is_some()
    }

    pub fn i32_m42(&self) -> i32 {
        self.i32_m42_opt().unwrap_or(
            -42
        )
    }
    pub fn i32_2147483647_opt(&self) -> ::std::option::Option<i32> {
        self.i32_2147483647.clone()
    }

    pub fn has_i32_2147483647(&self) -> bool {
        Self::i32_2147483647_opt(self).is_some()
    }

    pub fn i32_2147483647(&self) -> i32 {
        self.i32_2147483647_opt().unwrap_or(
            2147483647
        )
    }
    pub fn i32_m2147483648_opt(&self) -> ::std::option::Option<i32> {
        self.i32_m2147483648.clone()
    }

    pub fn has_i32_m2147483648(&self) -> bool {
        Self::i32_m2147483648_opt(self).is_some()
    }

    pub fn i32_m2147483648(&self) -> i32 {
        self.i32_m2147483648_opt().unwrap_or(
            -2147483648
        )
    }
    pub fn i32_0123_opt(&self) -> ::std::option::Option<i32> {
        self.i32_0123.clone()
    }

    pub fn has_i32_0123(&self) -> bool {
        Self::i32_0123_opt(self).is_some()
    }

    pub fn i32_0123(&self) -> i32 {
        self.i32_0123_opt().unwrap_or(
            83
        )
    }
    pub fn i32_0x123_opt(&self) -> ::std::option::Option<i32> {
        self.i32_0x123.clone()
    }

    pub fn has_i32_0x123(&self) -> bool {
        Self::i32_0x123_opt(self).is_some()
    }

    pub fn i32_0x123(&self) -> i32 {
        self.i32_0x123_opt().unwrap_or(
            291
        )
    }
    pub fn u32_default_opt(&self) -> ::std::option::Option<u32> {
        self.u32_default.clone()
    }

    pub fn has_u32_default(&self) -> bool {
        Self::u32_default_opt(self).is_some()
    }

    pub fn u32_default(&self) -> u32 {
        self.u32_default_opt().unwrap_or(
            ::std::default::Default::default()
        )
    }
    pub fn u32_0_opt(&self) -> ::std::option::Option<u32> {
        self.u32_0.clone()
    }

    pub fn has_u32_0(&self) -> bool {
        Self::u32_0_opt(self).is_some()
    }

    pub fn u32_0(&self) -> u32 {
        self.u32_0_opt().unwrap_or(
            0
        )
    }
    pub fn u32_42_opt(&self) -> ::std::option::Option<u32> {
        self.u32_42.clone()
    }

    pub fn has_u32_42(&self) -> bool {
        Self::u32_42_opt(self).is_some()
    }

    pub fn u32_42(&self) -> u32 {
        self.u32_42_opt().unwrap_or(
            42
        )
    }
    pub fn u32_4294967295_opt(&self) -> ::std::option::Option<u32> {
        self.u32_4294967295.clone()
    }

    pub fn has_u32_4294967295(&self) -> bool {
        Self::u32_4294967295_opt(self).is_some()
    }

    pub fn u32_4294967295(&self) -> u32 {
        self.u32_4294967295_opt().unwrap_or(
            4294967295
        )
    }
    pub fn u32_0123_opt(&self) -> ::std::option::Option<u32> {
        self.u32_0123.clone()
    }

    pub fn has_u32_0123(&self) -> bool {
        Self::u32_0123_opt(self).is_some()
    }

    pub fn u32_0123(&self) -> u32 {
        self.u32_0123_opt().unwrap_or(
            83
        )
    }
    pub fn u32_0x123_opt(&self) -> ::std::option::Option<u32> {
        self.u32_0x123.clone()
    }

    pub fn has_u32_0x123(&self) -> bool {
        Self::u32_0x123_opt(self).is_some()
    }

    pub fn u32_0x123(&self) -> u32 {
        self.u32_0x123_opt().unwrap_or(
            291
        )
    }
    pub fn i64_default_opt(&self) -> ::std::option::Option<i64> {
        self.i64_default.clone()
    }

    pub fn has_i64_default(&self) -> bool {
        Self::i64_default_opt(self).is_some()
    }

    pub fn i64_default(&self) -> i64 {
        self.i64_default_opt().unwrap_or(
            ::std::default::Default::default()
        )
    }
    pub fn i64_0_opt(&self) -> ::std::option::Option<i64> {
        self.i64_0.clone()
    }

    pub fn has_i64_0(&self) -> bool {
        Self::i64_0_opt(self).is_some()
    }

    pub fn i64_0(&self) -> i64 {
        self.i64_0_opt().unwrap_or(
            0
        )
    }
    pub fn i64_42_opt(&self) -> ::std::option::Option<i64> {
        self.i64_42.clone()
    }

    pub fn has_i64_42(&self) -> bool {
        Self::i64_42_opt(self).is_some()
    }

    pub fn i64_42(&self) -> i64 {
        self.i64_42_opt().unwrap_or(
            42
        )
    }
    pub fn i64_m42_opt(&self) -> ::std::option::Option<i64> {
        self.i64_m42.clone()
    }

    pub fn has_i64_m42(&self) -> bool {
        Self::i64_m42_opt(self).is_some()
    }

    pub fn i64_m42(&self) -> i64 {
        self.i64_m42_opt().unwrap_or(
            -42
        )
    }
    pub fn i64_9223372036854775807_opt(&self) -> ::std::option::Option<i64> {
        self.i64_9223372036854775807.clone()
    }

    pub fn has_i64_9223372036854775807(&self) -> bool {
        Self::i64_9223372036854775807_opt(self).is_some()
    }

    pub fn i64_9223372036854775807(&self) -> i64 {
        self.i64_9223372036854775807_opt().unwrap_or(
            9223372036854775807
        )
    }
    pub fn i64_m9223372036854775808_opt(&self) -> ::std::option::Option<i64> {
        self.i64_m9223372036854775808.clone()
    }

    pub fn has_i64_m9223372036854775808(&self) -> bool {
        Self::i64_m9223372036854775808_opt(self).is_some()
    }

    pub fn i64_m9223372036854775808(&self) -> i64 {
        self.i64_m9223372036854775808_opt().unwrap_or(
            -9223372036854775808
        )
    }
    pub fn i64_0123_opt(&self) -> ::std::option::Option<i64> {
        self.i64_0123.clone()
    }

    pub fn has_i64_0123(&self) -> bool {
        Self::i64_0123_opt(self).is_some()
    }

    pub fn i64_0123(&self) -> i64 {
        self.i64_0123_opt().unwrap_or(
            83
        )
    }
    pub fn i64_0x123_opt(&self) -> ::std::option::Option<i64> {
        self.i64_0x123.clone()
    }

    pub fn has_i64_0x123(&self) -> bool {
        Self::i64_0x123_opt(self).is_some()
    }

    pub fn i64_0x123(&self) -> i64 {
        self.i64_0x123_opt().unwrap_or(
            291
        )
    }
    pub fn u64_default_opt(&self) -> ::std::option::Option<u64> {
        self.u64_default.clone()
    }

    pub fn has_u64_default(&self) -> bool {
        Self::u64_default_opt(self).is_some()
    }

    pub fn u64_default(&self) -> u64 {
        self.u64_default_opt().unwrap_or(
            ::std::default::Default::default()
        )
    }
    pub fn u64_0_opt(&self) -> ::std::option::Option<u64> {
        self.u64_0.clone()
    }

    pub fn has_u64_0(&self) -> bool {
        Self::u64_0_opt(self).is_some()
    }

    pub fn u64_0(&self) -> u64 {
        self.u64_0_opt().unwrap_or(
            0
        )
    }
    pub fn u64_42_opt(&self) -> ::std::option::Option<u64> {
        self.u64_42.clone()
    }

    pub fn has_u64_42(&self) -> bool {
        Self::u64_42_opt(self).is_some()
    }

    pub fn u64_42(&self) -> u64 {
        self.u64_42_opt().unwrap_or(
            42
        )
    }
    pub fn u64_18446744073709551615_opt(&self) -> ::std::option::Option<u64> {
        self.u64_18446744073709551615.clone()
    }

    pub fn has_u64_18446744073709551615(&self) -> bool {
        Self::u64_18446744073709551615_opt(self).is_some()
    }

    pub fn u64_18446744073709551615(&self) -> u64 {
        self.u64_18446744073709551615_opt().unwrap_or(
            18446744073709551615
        )
    }
    pub fn u64_0123_opt(&self) -> ::std::option::Option<u64> {
        self.u64_0123.clone()
    }

    pub fn has_u64_0123(&self) -> bool {
        Self::u64_0123_opt(self).is_some()
    }

    pub fn u64_0123(&self) -> u64 {
        self.u64_0123_opt().unwrap_or(
            83
        )
    }
    pub fn u64_0x123_opt(&self) -> ::std::option::Option<u64> {
        self.u64_0x123.clone()
    }

    pub fn has_u64_0x123(&self) -> bool {
        Self::u64_0x123_opt(self).is_some()
    }

    pub fn u64_0x123(&self) -> u64 {
        self.u64_0x123_opt().unwrap_or(
            291
        )
    }
    pub fn f32_default_opt(&self) -> ::std::option::Option<f32> {
        self.f32_default.clone()
    }

    pub fn has_f32_default(&self) -> bool {
        Self::f32_default_opt(self).is_some()
    }

    pub fn f32_default(&self) -> f32 {
        self.f32_default_opt().unwrap_or(
            ::std::default::Default::default()
        )
    }
    pub fn f32_0_opt(&self) -> ::std::option::Option<f32> {
        self.f32_0.clone()
    }

    pub fn has_f32_0(&self) -> bool {
        Self::f32_0_opt(self).is_some()
    }

    pub fn f32_0(&self) -> f32 {
        self.f32_0_opt().unwrap_or(
            0f32
        )
    }
    pub fn f32_m0_opt(&self) -> ::std::option::Option<f32> {
        self.f32_m0.clone()
    }

    pub fn has_f32_m0(&self) -> bool {
        Self::f32_m0_opt(self).is_some()
    }

    pub fn f32_m0(&self) -> f32 {
        self.f32_m0_opt().unwrap_or(
            -0f32
        )
    }
    pub fn f32_0p_opt(&self) -> ::std::option::Option<f32> {
        self.f32_0p.clone()
    }

    pub fn has_f32_0p(&self) -> bool {
        Self::f32_0p_opt(self).is_some()
    }

    pub fn f32_0p(&self) -> f32 {
        self.f32_0p_opt().unwrap_or(
            0f32
        )
    }
    pub fn f32_p0_opt(&self) -> ::std::option::Option<f32> {
        self.f32_p0.clone()
    }

    pub fn has_f32_p0(&self) -> bool {
        Self::f32_p0_opt(self).is_some()
    }

    pub fn f32_p0(&self) -> f32 {
        self.f32_p0_opt().unwrap_or(
            0f32
        )
    }
    pub fn f32_0p0_opt(&self) -> ::std::option::Option<f32> {
        self.f32_0p0.clone()
    }

    pub fn has_f32_0p0(&self) -> bool {
        Self::f32_0p0_opt(self).is_some()
    }

    pub fn f32_0p0(&self) -> f32 {
        self.f32_0p0_opt().unwrap_or(
            0f32
        )
    }
    pub fn f32_42_opt(&self) -> ::std::option::Option<f32> {
        self.f32_42.clone()
    }

    pub fn has_f32_42(&self) -> bool {
        Self::f32_42_opt(self).is_some()
    }

    pub fn f32_42(&self) -> f32 {
        self.f32_42_opt().unwrap_or(
            42f32
        )
    }
    pub fn f32_m42_opt(&self) -> ::std::option::Option<f32> {
        self.f32_m42.clone()
    }

    pub fn has_f32_m42(&self) -> bool {
        Self::f32_m42_opt(self).is_some()
    }

    pub fn f32_m42(&self) -> f32 {
        self.f32_m42_opt().unwrap_or(
            -42f32
        )
    }
    pub fn f32_0p25_opt(&self) -> ::std::option::Option<f32> {
        self.f32_0p25.clone()
    }

    pub fn has_f32_0p25(&self) -> bool {
        Self::f32_0p25_opt(self).is_some()
    }

    pub fn f32_0p25(&self) -> f32 {
        self.f32_0p25_opt().unwrap_or(
            0.25f32
        )
    }
    pub fn f32_1p5e2_opt(&self) -> ::std::option::Option<f32> {
        self.f32_1p5e2.clone()
    }

    pub fn has_f32_1p5e2(&self) -> bool {
        Self::f32_1p5e2_opt(self).is_some()
    }

    pub fn f32_1p5e2(&self) -> f32 {
        self.f32_1p5e2_opt().unwrap_or(
            150f32
        )
    }
    pub fn f32_inf_opt(&self) -> ::std::option::Option<f32> {
        self.f32_inf.clone()
    }

    pub fn has_f32_inf(&self) -> bool {
        Self::f32_inf_opt(self).is_some()
    }

    pub fn f32_inf(&self) -> f32 {
        self.f32_inf_opt().unwrap_or(
            f32::INFINITY
        )
    }
    pub fn f32_minf_opt(&self) -> ::std::option::Option<f32> {
        self.f32_minf.clone()
    }

    pub fn has_f32_minf(&self) -> bool {
        Self::f32_minf_opt(self).is_some()
    }

    pub fn f32_minf(&self) -> f32 {
        self.f32_minf_opt().unwrap_or(
            f32::NEG_INFINITY
        )
    }
    pub fn f32_nan_opt(&self) -> ::std::option::Option<f32> {
        self.f32_nan.clone()
    }

    pub fn has_f32_nan(&self) -> bool {
        Self::f32_nan_opt(self).is_some()
    }

    pub fn f32_nan(&self) -> f32 {
        self.f32_nan_opt().unwrap_or(
            f32::NAN
        )
    }
    pub fn f32_mnan_opt(&self) -> ::std::option::Option<f32> {
        self.f32_mnan.clone()
    }

    pub fn has_f32_mnan(&self) -> bool {
        Self::f32_mnan_opt(self).is_some()
    }

    pub fn f32_mnan(&self) -> f32 {
        self.f32_mnan_opt().unwrap_or(
            f32::NAN
        )
    }
    pub fn bool_default_opt(&self) -> ::std::option::Option<bool> {
        self.bool_default.clone()
    }

    pub fn has_bool_default(&self) -> bool {
        Self::bool_default_opt(self).is_some()
    }

    pub fn bool_default(&self) -> bool {
        self.bool_default_opt().unwrap_or(
            ::std::default::Default::default()
        )
    }
    pub fn bool_true_opt(&self) -> ::std::option::Option<bool> {
        self.bool_true.clone()
    }

    pub fn has_bool_true(&self) -> bool {
        Self::bool_true_opt(self).is_some()
    }

    pub fn bool_true(&self) -> bool {
        self.bool_true_opt().unwrap_or(
            true
        )
    }
    pub fn bool_false_opt(&self) -> ::std::option::Option<bool> {
        self.bool_false.clone()
    }

    pub fn has_bool_false(&self) -> bool {
        Self::bool_false_opt(self).is_some()
    }

    pub fn bool_false(&self) -> bool {
        self.bool_false_opt().unwrap_or(
            false
        )
    }
    pub fn string_default_opt(&self) -> ::std::option::Option<&'_ str> {
        if self.string_default.as_deref()
    }

    pub fn has_string_default(&self) -> bool {
        Self::string_default_opt(self).is_some()
    }

    pub fn string_default(&self) -> &'_ str {
        self.string_default_opt().unwrap_or(
            ::std::default::Default::default()
        )
    }
    pub fn string_empty_opt(&self) -> ::std::option::Option<&'_ str> {
        if self.string_empty.as_deref()
    }

    pub fn has_string_empty(&self) -> bool {
        Self::string_empty_opt(self).is_some()
    }

    pub fn string_empty(&self) -> &'_ str {
        self.string_empty_opt().unwrap_or(
            ""
        )
    }
    pub fn string_abc_opt(&self) -> ::std::option::Option<&'_ str> {
        if self.string_abc.as_deref()
    }

    pub fn has_string_abc(&self) -> bool {
        Self::string_abc_opt(self).is_some()
    }

    pub fn string_abc(&self) -> &'_ str {
        self.string_abc_opt().unwrap_or(
            "abc"
        )
    }
    pub fn string_aiu_opt(&self) -> ::std::option::Option<&'_ str> {
        if self.string_aiu.as_deref()
    }

    pub fn has_string_aiu(&self) -> bool {
        Self::string_aiu_opt(self).is_some()
    }

    pub fn string_aiu(&self) -> &'_ str {
        self.string_aiu_opt().unwrap_or(
            "\u{3042}\u{3044}\u{3046}"
        )
    }
    pub fn string_backslash_opt(&self) -> ::std::option::Option<&'_ str> {
        if self.string_backslash.as_deref()
    }

    pub fn has_string_backslash(&self) -> bool {
        Self::string_backslash_opt(self).is_some()
    }

    pub fn string_backslash(&self) -> &'_ str {
        self.string_backslash_opt().unwrap_or(
            "\\"
        )
    }
    pub fn string_tab_opt(&self) -> ::std::option::Option<&'_ str> {
        if self.string_tab.as_deref()
    }

    pub fn has_string_tab(&self) -> bool {
        Self::string_tab_opt(self).is_some()
    }

    pub fn string_tab(&self) -> &'_ str {
        self.string_tab_opt().unwrap_or(
            "\t"
        )
    }
    pub fn string_crlf_opt(&self) -> ::std::option::Option<&'_ str> {
        if self.string_crlf.as_deref()
    }

    pub fn has_string_crlf(&self) -> bool {
        Self::string_crlf_opt(self).is_some()
    }

    pub fn string_crlf(&self) -> &'_ str {
        self.string_crlf_opt().unwrap_or(
            "\r\n"
        )
    }
    pub fn bytes_default_opt(&self) -> ::std::option::Option<&'_ [u8]> {
        if self.bytes_default.as_deref()
    }

    pub fn has_bytes_default(&self) -> bool {
        Self::bytes_default_opt(self).is_some()
    }

    pub fn bytes_default(&self) -> &'_ [u8] {
        self.bytes_default_opt().unwrap_or(
            ::std::default::Default::default()
        )
    }
    pub fn bytes_empty_opt(&self) -> ::std::option::Option<&'_ [u8]> {
        if self.bytes_empty.as_deref()
    }

    pub fn has_bytes_empty(&self) -> bool {
        Self::bytes_empty_opt(self).is_some()
    }

    pub fn bytes_empty(&self) -> &'_ [u8] {
        self.bytes_empty_opt().unwrap_or(
            b""
        )
    }
    pub fn bytes_abc_opt(&self) -> ::std::option::Option<&'_ [u8]> {
        if self.bytes_abc.as_deref()
    }

    pub fn has_bytes_abc(&self) -> bool {
        Self::bytes_abc_opt(self).is_some()
    }

    pub fn bytes_abc(&self) -> &'_ [u8] {
        self.bytes_abc_opt().unwrap_or(
            b"\x61\x62\x63"
        )
    }
    pub fn bytes_aiu_opt(&self) -> ::std::option::Option<&'_ [u8]> {
        if self.bytes_aiu.as_deref()
    }

    pub fn has_bytes_aiu(&self) -> bool {
        Self::bytes_aiu_opt(self).is_some()
    }

    pub fn bytes_aiu(&self) -> &'_ [u8] {
        self.bytes_aiu_opt().unwrap_or(
            b"\xe3\x81\x82\xe3\x81\x84\xe3\x81\x86"
        )
    }
    pub fn bytes_backslash_opt(&self) -> ::std::option::Option<&'_ [u8]> {
        if self.bytes_backslash.as_deref()
    }

    pub fn has_bytes_backslash(&self) -> bool {
        Self::bytes_backslash_opt(self).is_some()
    }

    pub fn bytes_backslash(&self) -> &'_ [u8] {
        self.bytes_backslash_opt().unwrap_or(
            b"\x5c"
        )
    }
    pub fn bytes_tab_opt(&self) -> ::std::option::Option<&'_ [u8]> {
        if self.bytes_tab.as_deref()
    }

    pub fn has_bytes_tab(&self) -> bool {
        Self::bytes_tab_opt(self).is_some()
    }

    pub fn bytes_tab(&self) -> &'_ [u8] {
        self.bytes_tab_opt().unwrap_or(
            b"\x09"
        )
    }
    pub fn bytes_crlf_opt(&self) -> ::std::option::Option<&'_ [u8]> {
        if self.bytes_crlf.as_deref()
    }

    pub fn has_bytes_crlf(&self) -> bool {
        Self::bytes_crlf_opt(self).is_some()
    }

    pub fn bytes_crlf(&self) -> &'_ [u8] {
        self.bytes_crlf_opt().unwrap_or(
            b"\x0d\x0a"
        )
    }
    pub fn enum_default_opt(&self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
        self.enum_default.clone()
    }

    pub fn has_enum_default(&self) -> bool {
        Self::enum_default_opt(self).is_some()
    }

    pub fn enum_default(&self) -> self::_puroro_root::proto2_defaults::MyEnum {
        self.enum_default_opt().unwrap_or(
            ::std::default::Default::default()
        )
    }
    pub fn enum_one_opt(&self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
        self.enum_one.clone()
    }

    pub fn has_enum_one(&self) -> bool {
        Self::enum_one_opt(self).is_some()
    }

    pub fn enum_one(&self) -> self::_puroro_root::proto2_defaults::MyEnum {
        self.enum_one_opt().unwrap_or(
            self::_puroro_root::proto2_defaults::MyEnum::One
        )
    }
    pub fn enum_fourty_two_opt(&self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
        self.enum_fourty_two.clone()
    }

    pub fn has_enum_fourty_two(&self) -> bool {
        Self::enum_fourty_two_opt(self).is_some()
    }

    pub fn enum_fourty_two(&self) -> self::_puroro_root::proto2_defaults::MyEnum {
        self.enum_fourty_two_opt().unwrap_or(
            self::_puroro_root::proto2_defaults::MyEnum::FourtyTwo
        )
    }
    pub fn i32_default_mut(&mut self) -> &mut ::std::option::Option<i32> {
        &mut self.i32_default
    }
    pub fn i32_0_mut(&mut self) -> &mut ::std::option::Option<i32> {
        &mut self.i32_0
    }
    pub fn i32_42_mut(&mut self) -> &mut ::std::option::Option<i32> {
        &mut self.i32_42
    }
    pub fn i32_m42_mut(&mut self) -> &mut ::std::option::Option<i32> {
        &mut self.i32_m42
    }
    pub fn i32_2147483647_mut(&mut self) -> &mut ::std::option::Option<i32> {
        &mut self.i32_2147483647
    }
    pub fn i32_m2147483648_mut(&mut self) -> &mut ::std::option::Option<i32> {
        &mut self.i32_m2147483648
    }
    pub fn i32_0123_mut(&mut self) -> &mut ::std::option::Option<i32> {
        &mut self.i32_0123
    }
    pub fn i32_0x123_mut(&mut self) -> &mut ::std::option::Option<i32> {
        &mut self.i32_0x123
    }
    pub fn u32_default_mut(&mut self) -> &mut ::std::option::Option<u32> {
        &mut self.u32_default
    }
    pub fn u32_0_mut(&mut self) -> &mut ::std::option::Option<u32> {
        &mut self.u32_0
    }
    pub fn u32_42_mut(&mut self) -> &mut ::std::option::Option<u32> {
        &mut self.u32_42
    }
    pub fn u32_4294967295_mut(&mut self) -> &mut ::std::option::Option<u32> {
        &mut self.u32_4294967295
    }
    pub fn u32_0123_mut(&mut self) -> &mut ::std::option::Option<u32> {
        &mut self.u32_0123
    }
    pub fn u32_0x123_mut(&mut self) -> &mut ::std::option::Option<u32> {
        &mut self.u32_0x123
    }
    pub fn i64_default_mut(&mut self) -> &mut ::std::option::Option<i64> {
        &mut self.i64_default
    }
    pub fn i64_0_mut(&mut self) -> &mut ::std::option::Option<i64> {
        &mut self.i64_0
    }
    pub fn i64_42_mut(&mut self) -> &mut ::std::option::Option<i64> {
        &mut self.i64_42
    }
    pub fn i64_m42_mut(&mut self) -> &mut ::std::option::Option<i64> {
        &mut self.i64_m42
    }
    pub fn i64_9223372036854775807_mut(&mut self) -> &mut ::std::option::Option<i64> {
        &mut self.i64_9223372036854775807
    }
    pub fn i64_m9223372036854775808_mut(&mut self) -> &mut ::std::option::Option<i64> {
        &mut self.i64_m9223372036854775808
    }
    pub fn i64_0123_mut(&mut self) -> &mut ::std::option::Option<i64> {
        &mut self.i64_0123
    }
    pub fn i64_0x123_mut(&mut self) -> &mut ::std::option::Option<i64> {
        &mut self.i64_0x123
    }
    pub fn u64_default_mut(&mut self) -> &mut ::std::option::Option<u64> {
        &mut self.u64_default
    }
    pub fn u64_0_mut(&mut self) -> &mut ::std::option::Option<u64> {
        &mut self.u64_0
    }
    pub fn u64_42_mut(&mut self) -> &mut ::std::option::Option<u64> {
        &mut self.u64_42
    }
    pub fn u64_18446744073709551615_mut(&mut self) -> &mut ::std::option::Option<u64> {
        &mut self.u64_18446744073709551615
    }
    pub fn u64_0123_mut(&mut self) -> &mut ::std::option::Option<u64> {
        &mut self.u64_0123
    }
    pub fn u64_0x123_mut(&mut self) -> &mut ::std::option::Option<u64> {
        &mut self.u64_0x123
    }
    pub fn f32_default_mut(&mut self) -> &mut ::std::option::Option<f32> {
        &mut self.f32_default
    }
    pub fn f32_0_mut(&mut self) -> &mut ::std::option::Option<f32> {
        &mut self.f32_0
    }
    pub fn f32_m0_mut(&mut self) -> &mut ::std::option::Option<f32> {
        &mut self.f32_m0
    }
    pub fn f32_0p_mut(&mut self) -> &mut ::std::option::Option<f32> {
        &mut self.f32_0p
    }
    pub fn f32_p0_mut(&mut self) -> &mut ::std::option::Option<f32> {
        &mut self.f32_p0
    }
    pub fn f32_0p0_mut(&mut self) -> &mut ::std::option::Option<f32> {
        &mut self.f32_0p0
    }
    pub fn f32_42_mut(&mut self) -> &mut ::std::option::Option<f32> {
        &mut self.f32_42
    }
    pub fn f32_m42_mut(&mut self) -> &mut ::std::option::Option<f32> {
        &mut self.f32_m42
    }
    pub fn f32_0p25_mut(&mut self) -> &mut ::std::option::Option<f32> {
        &mut self.f32_0p25
    }
    pub fn f32_1p5e2_mut(&mut self) -> &mut ::std::option::Option<f32> {
        &mut self.f32_1p5e2
    }
    pub fn f32_inf_mut(&mut self) -> &mut ::std::option::Option<f32> {
        &mut self.f32_inf
    }
    pub fn f32_minf_mut(&mut self) -> &mut ::std::option::Option<f32> {
        &mut self.f32_minf
    }
    pub fn f32_nan_mut(&mut self) -> &mut ::std::option::Option<f32> {
        &mut self.f32_nan
    }
    pub fn f32_mnan_mut(&mut self) -> &mut ::std::option::Option<f32> {
        &mut self.f32_mnan
    }
    pub fn bool_default_mut(&mut self) -> &mut ::std::option::Option<bool> {
        &mut self.bool_default
    }
    pub fn bool_true_mut(&mut self) -> &mut ::std::option::Option<bool> {
        &mut self.bool_true
    }
    pub fn bool_false_mut(&mut self) -> &mut ::std::option::Option<bool> {
        &mut self.bool_false
    }
    pub fn string_default_mut(&mut self) -> &mut ::std::option::Option<::std::string::String> {
        &mut self.string_default
    }
    pub fn string_empty_mut(&mut self) -> &mut ::std::option::Option<::std::string::String> {
        &mut self.string_empty
    }
    pub fn string_abc_mut(&mut self) -> &mut ::std::option::Option<::std::string::String> {
        &mut self.string_abc
    }
    pub fn string_aiu_mut(&mut self) -> &mut ::std::option::Option<::std::string::String> {
        &mut self.string_aiu
    }
    pub fn string_backslash_mut(&mut self) -> &mut ::std::option::Option<::std::string::String> {
        &mut self.string_backslash
    }
    pub fn string_tab_mut(&mut self) -> &mut ::std::option::Option<::std::string::String> {
        &mut self.string_tab
    }
    pub fn string_crlf_mut(&mut self) -> &mut ::std::option::Option<::std::string::String> {
        &mut self.string_crlf
    }
    pub fn bytes_default_mut(&mut self) -> &mut ::std::option::Option<::std::vec::Vec<u8>> {
        &mut self.bytes_default
    }
    pub fn bytes_empty_mut(&mut self) -> &mut ::std::option::Option<::std::vec::Vec<u8>> {
        &mut self.bytes_empty
    }
    pub fn bytes_abc_mut(&mut self) -> &mut ::std::option::Option<::std::vec::Vec<u8>> {
        &mut self.bytes_abc
    }
    pub fn bytes_aiu_mut(&mut self) -> &mut ::std::option::Option<::std::vec::Vec<u8>> {
        &mut self.bytes_aiu
    }
    pub fn bytes_backslash_mut(&mut self) -> &mut ::std::option::Option<::std::vec::Vec<u8>> {
        &mut self.bytes_backslash
    }
    pub fn bytes_tab_mut(&mut self) -> &mut ::std::option::Option<::std::vec::Vec<u8>> {
        &mut self.bytes_tab
    }
    pub fn bytes_crlf_mut(&mut self) -> &mut ::std::option::Option<::std::vec::Vec<u8>> {
        &mut self.bytes_crlf
    }
    pub fn enum_default_mut(&mut self) -> &mut ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
        &mut self.enum_default
    }
    pub fn enum_one_mut(&mut self) -> &mut ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
        &mut self.enum_one
    }
    pub fn enum_fourty_two_mut(&mut self) -> &mut ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
        &mut self.enum_fourty_two
    }
}

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
fn enum_default_opt<'this>(&'this self) -> Option<self::_puroro_root::proto2_defaults::MyEnum> {
    Clone::clone(&self.enum_default)
}
fn enum_one_opt<'this>(&'this self) -> Option<self::_puroro_root::proto2_defaults::MyEnum> {
    Clone::clone(&self.enum_one)
}
fn enum_fourty_two_opt<'this>(&'this self) -> Option<self::_puroro_root::proto2_defaults::MyEnum> {
    Clone::clone(&self.enum_fourty_two)
}
}

impl ::puroro::MessageRepresentativeImpl for Msg {}

impl ::puroro::internal::de::DeserMessageFromBytesIter for Msg {
    fn deser_field<I>(
        &mut self,
        field_number: i32,
        data: ::puroro::internal::types::FieldData<&mut ::puroro::internal::de::from_iter::ScopedIter<I>>,
    ) -> ::puroro::Result<()>
    where
        I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>
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

impl ::puroro::internal::se::SerMessageToIoWrite for Msg
where
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_default_opt(self),
            1,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_0_opt(self),
            2,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_42_opt(self),
            3,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_m42_opt(self),
            4,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_2147483647_opt(self),
            5,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_m2147483648_opt(self),
            6,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_0123_opt(self),
            7,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_0x123_opt(self),
            8,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_default_opt(self),
            11,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_0_opt(self),
            12,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_42_opt(self),
            13,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_4294967295_opt(self),
            15,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_0123_opt(self),
            17,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_0x123_opt(self),
            18,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_default_opt(self),
            21,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_0_opt(self),
            22,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_42_opt(self),
            23,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_m42_opt(self),
            24,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_9223372036854775807_opt(self),
            25,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_m9223372036854775808_opt(self),
            26,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_0123_opt(self),
            27,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_0x123_opt(self),
            28,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_default_opt(self),
            31,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_0_opt(self),
            32,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_42_opt(self),
            33,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_18446744073709551615_opt(self),
            35,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_0123_opt(self),
            37,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_0x123_opt(self),
            38,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_default_opt(self),
            41,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_0_opt(self),
            42,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_m0_opt(self),
            43,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_0p_opt(self),
            44,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_p0_opt(self),
            45,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_0p0_opt(self),
            46,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_42_opt(self),
            47,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_m42_opt(self),
            48,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_0p25_opt(self),
            49,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_1p5e2_opt(self),
            50,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_inf_opt(self),
            51,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_minf_opt(self),
            52,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_nan_opt(self),
            53,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_mnan_opt(self),
            54,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bool
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bool_default_opt(self),
            61,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bool
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bool_true_opt(self),
            62,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bool
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bool_false_opt(self),
            63,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_default_opt(self),
            71,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_empty_opt(self),
            72,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_abc_opt(self),
            73,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_aiu_opt(self),
            74,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_backslash_opt(self),
            75,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_tab_opt(self),
            76,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_crlf_opt(self),
            77,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_default_opt(self),
            81,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_empty_opt(self),
            82,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_abc_opt(self),
            83,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_aiu_opt(self),
            84,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_backslash_opt(self),
            85,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_tab_opt(self),
            86,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_crlf_opt(self),
            87,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::enum_default_opt(self),
            91,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::enum_one_opt(self),
            92,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::enum_fourty_two_opt(self),
            93,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl ::std::default::Default for Msg {
    fn default() -> Self {
        Self::new()
    }
}

impl ::std::fmt::Debug for Msg 
where
    Self: super::_puroro_traits::MsgTrait
{
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        f.debug_struct("Msg")
            .field("i32_default", &<Self as super::_puroro_traits::MsgTrait>::i32_default_opt(self))
            .field("i32_0", &<Self as super::_puroro_traits::MsgTrait>::i32_0_opt(self))
            .field("i32_42", &<Self as super::_puroro_traits::MsgTrait>::i32_42_opt(self))
            .field("i32_m42", &<Self as super::_puroro_traits::MsgTrait>::i32_m42_opt(self))
            .field("i32_2147483647", &<Self as super::_puroro_traits::MsgTrait>::i32_2147483647_opt(self))
            .field("i32_m2147483648", &<Self as super::_puroro_traits::MsgTrait>::i32_m2147483648_opt(self))
            .field("i32_0123", &<Self as super::_puroro_traits::MsgTrait>::i32_0123_opt(self))
            .field("i32_0x123", &<Self as super::_puroro_traits::MsgTrait>::i32_0x123_opt(self))
            .field("u32_default", &<Self as super::_puroro_traits::MsgTrait>::u32_default_opt(self))
            .field("u32_0", &<Self as super::_puroro_traits::MsgTrait>::u32_0_opt(self))
            .field("u32_42", &<Self as super::_puroro_traits::MsgTrait>::u32_42_opt(self))
            .field("u32_4294967295", &<Self as super::_puroro_traits::MsgTrait>::u32_4294967295_opt(self))
            .field("u32_0123", &<Self as super::_puroro_traits::MsgTrait>::u32_0123_opt(self))
            .field("u32_0x123", &<Self as super::_puroro_traits::MsgTrait>::u32_0x123_opt(self))
            .field("i64_default", &<Self as super::_puroro_traits::MsgTrait>::i64_default_opt(self))
            .field("i64_0", &<Self as super::_puroro_traits::MsgTrait>::i64_0_opt(self))
            .field("i64_42", &<Self as super::_puroro_traits::MsgTrait>::i64_42_opt(self))
            .field("i64_m42", &<Self as super::_puroro_traits::MsgTrait>::i64_m42_opt(self))
            .field("i64_9223372036854775807", &<Self as super::_puroro_traits::MsgTrait>::i64_9223372036854775807_opt(self))
            .field("i64_m9223372036854775808", &<Self as super::_puroro_traits::MsgTrait>::i64_m9223372036854775808_opt(self))
            .field("i64_0123", &<Self as super::_puroro_traits::MsgTrait>::i64_0123_opt(self))
            .field("i64_0x123", &<Self as super::_puroro_traits::MsgTrait>::i64_0x123_opt(self))
            .field("u64_default", &<Self as super::_puroro_traits::MsgTrait>::u64_default_opt(self))
            .field("u64_0", &<Self as super::_puroro_traits::MsgTrait>::u64_0_opt(self))
            .field("u64_42", &<Self as super::_puroro_traits::MsgTrait>::u64_42_opt(self))
            .field("u64_18446744073709551615", &<Self as super::_puroro_traits::MsgTrait>::u64_18446744073709551615_opt(self))
            .field("u64_0123", &<Self as super::_puroro_traits::MsgTrait>::u64_0123_opt(self))
            .field("u64_0x123", &<Self as super::_puroro_traits::MsgTrait>::u64_0x123_opt(self))
            .field("f32_default", &<Self as super::_puroro_traits::MsgTrait>::f32_default_opt(self))
            .field("f32_0", &<Self as super::_puroro_traits::MsgTrait>::f32_0_opt(self))
            .field("f32_m0", &<Self as super::_puroro_traits::MsgTrait>::f32_m0_opt(self))
            .field("f32_0p", &<Self as super::_puroro_traits::MsgTrait>::f32_0p_opt(self))
            .field("f32_p0", &<Self as super::_puroro_traits::MsgTrait>::f32_p0_opt(self))
            .field("f32_0p0", &<Self as super::_puroro_traits::MsgTrait>::f32_0p0_opt(self))
            .field("f32_42", &<Self as super::_puroro_traits::MsgTrait>::f32_42_opt(self))
            .field("f32_m42", &<Self as super::_puroro_traits::MsgTrait>::f32_m42_opt(self))
            .field("f32_0p25", &<Self as super::_puroro_traits::MsgTrait>::f32_0p25_opt(self))
            .field("f32_1p5e2", &<Self as super::_puroro_traits::MsgTrait>::f32_1p5e2_opt(self))
            .field("f32_inf", &<Self as super::_puroro_traits::MsgTrait>::f32_inf_opt(self))
            .field("f32_minf", &<Self as super::_puroro_traits::MsgTrait>::f32_minf_opt(self))
            .field("f32_nan", &<Self as super::_puroro_traits::MsgTrait>::f32_nan_opt(self))
            .field("f32_mnan", &<Self as super::_puroro_traits::MsgTrait>::f32_mnan_opt(self))
            .field("bool_default", &<Self as super::_puroro_traits::MsgTrait>::bool_default_opt(self))
            .field("bool_true", &<Self as super::_puroro_traits::MsgTrait>::bool_true_opt(self))
            .field("bool_false", &<Self as super::_puroro_traits::MsgTrait>::bool_false_opt(self))
            .field("string_default", &<Self as super::_puroro_traits::MsgTrait>::string_default_opt(self))
            .field("string_empty", &<Self as super::_puroro_traits::MsgTrait>::string_empty_opt(self))
            .field("string_abc", &<Self as super::_puroro_traits::MsgTrait>::string_abc_opt(self))
            .field("string_aiu", &<Self as super::_puroro_traits::MsgTrait>::string_aiu_opt(self))
            .field("string_backslash", &<Self as super::_puroro_traits::MsgTrait>::string_backslash_opt(self))
            .field("string_tab", &<Self as super::_puroro_traits::MsgTrait>::string_tab_opt(self))
            .field("string_crlf", &<Self as super::_puroro_traits::MsgTrait>::string_crlf_opt(self))
            .field("bytes_default", &<Self as super::_puroro_traits::MsgTrait>::bytes_default_opt(self))
            .field("bytes_empty", &<Self as super::_puroro_traits::MsgTrait>::bytes_empty_opt(self))
            .field("bytes_abc", &<Self as super::_puroro_traits::MsgTrait>::bytes_abc_opt(self))
            .field("bytes_aiu", &<Self as super::_puroro_traits::MsgTrait>::bytes_aiu_opt(self))
            .field("bytes_backslash", &<Self as super::_puroro_traits::MsgTrait>::bytes_backslash_opt(self))
            .field("bytes_tab", &<Self as super::_puroro_traits::MsgTrait>::bytes_tab_opt(self))
            .field("bytes_crlf", &<Self as super::_puroro_traits::MsgTrait>::bytes_crlf_opt(self))
            .field("enum_default", &<Self as super::_puroro_traits::MsgTrait>::enum_default_opt(self))
            .field("enum_one", &<Self as super::_puroro_traits::MsgTrait>::enum_one_opt(self))
            .field("enum_fourty_two", &<Self as super::_puroro_traits::MsgTrait>::enum_fourty_two_opt(self))
            .finish()
    }
}

impl ::std::clone::Clone for Msg {
    fn clone(&self) -> Self {
        Self {
            i32_default: ::std::clone::Clone::clone(&self.i32_default),
            i32_0: ::std::clone::Clone::clone(&self.i32_0),
            i32_42: ::std::clone::Clone::clone(&self.i32_42),
            i32_m42: ::std::clone::Clone::clone(&self.i32_m42),
            i32_2147483647: ::std::clone::Clone::clone(&self.i32_2147483647),
            i32_m2147483648: ::std::clone::Clone::clone(&self.i32_m2147483648),
            i32_0123: ::std::clone::Clone::clone(&self.i32_0123),
            i32_0x123: ::std::clone::Clone::clone(&self.i32_0x123),
            u32_default: ::std::clone::Clone::clone(&self.u32_default),
            u32_0: ::std::clone::Clone::clone(&self.u32_0),
            u32_42: ::std::clone::Clone::clone(&self.u32_42),
            u32_4294967295: ::std::clone::Clone::clone(&self.u32_4294967295),
            u32_0123: ::std::clone::Clone::clone(&self.u32_0123),
            u32_0x123: ::std::clone::Clone::clone(&self.u32_0x123),
            i64_default: ::std::clone::Clone::clone(&self.i64_default),
            i64_0: ::std::clone::Clone::clone(&self.i64_0),
            i64_42: ::std::clone::Clone::clone(&self.i64_42),
            i64_m42: ::std::clone::Clone::clone(&self.i64_m42),
            i64_9223372036854775807: ::std::clone::Clone::clone(&self.i64_9223372036854775807),
            i64_m9223372036854775808: ::std::clone::Clone::clone(&self.i64_m9223372036854775808),
            i64_0123: ::std::clone::Clone::clone(&self.i64_0123),
            i64_0x123: ::std::clone::Clone::clone(&self.i64_0x123),
            u64_default: ::std::clone::Clone::clone(&self.u64_default),
            u64_0: ::std::clone::Clone::clone(&self.u64_0),
            u64_42: ::std::clone::Clone::clone(&self.u64_42),
            u64_18446744073709551615: ::std::clone::Clone::clone(&self.u64_18446744073709551615),
            u64_0123: ::std::clone::Clone::clone(&self.u64_0123),
            u64_0x123: ::std::clone::Clone::clone(&self.u64_0x123),
            f32_default: ::std::clone::Clone::clone(&self.f32_default),
            f32_0: ::std::clone::Clone::clone(&self.f32_0),
            f32_m0: ::std::clone::Clone::clone(&self.f32_m0),
            f32_0p: ::std::clone::Clone::clone(&self.f32_0p),
            f32_p0: ::std::clone::Clone::clone(&self.f32_p0),
            f32_0p0: ::std::clone::Clone::clone(&self.f32_0p0),
            f32_42: ::std::clone::Clone::clone(&self.f32_42),
            f32_m42: ::std::clone::Clone::clone(&self.f32_m42),
            f32_0p25: ::std::clone::Clone::clone(&self.f32_0p25),
            f32_1p5e2: ::std::clone::Clone::clone(&self.f32_1p5e2),
            f32_inf: ::std::clone::Clone::clone(&self.f32_inf),
            f32_minf: ::std::clone::Clone::clone(&self.f32_minf),
            f32_nan: ::std::clone::Clone::clone(&self.f32_nan),
            f32_mnan: ::std::clone::Clone::clone(&self.f32_mnan),
            bool_default: ::std::clone::Clone::clone(&self.bool_default),
            bool_true: ::std::clone::Clone::clone(&self.bool_true),
            bool_false: ::std::clone::Clone::clone(&self.bool_false),
            string_default: ::std::clone::Clone::clone(&self.string_default),
            string_empty: ::std::clone::Clone::clone(&self.string_empty),
            string_abc: ::std::clone::Clone::clone(&self.string_abc),
            string_aiu: ::std::clone::Clone::clone(&self.string_aiu),
            string_backslash: ::std::clone::Clone::clone(&self.string_backslash),
            string_tab: ::std::clone::Clone::clone(&self.string_tab),
            string_crlf: ::std::clone::Clone::clone(&self.string_crlf),
            bytes_default: ::std::clone::Clone::clone(&self.bytes_default),
            bytes_empty: ::std::clone::Clone::clone(&self.bytes_empty),
            bytes_abc: ::std::clone::Clone::clone(&self.bytes_abc),
            bytes_aiu: ::std::clone::Clone::clone(&self.bytes_aiu),
            bytes_backslash: ::std::clone::Clone::clone(&self.bytes_backslash),
            bytes_tab: ::std::clone::Clone::clone(&self.bytes_tab),
            bytes_crlf: ::std::clone::Clone::clone(&self.bytes_crlf),
            enum_default: ::std::clone::Clone::clone(&self.enum_default),
            enum_one: ::std::clone::Clone::clone(&self.enum_one),
            enum_fourty_two: ::std::clone::Clone::clone(&self.enum_fourty_two),
        }
    }
}

impl ::std::cmp::PartialEq for Msg {
    fn eq(&self, rhs: &Self) -> bool {
        self.i32_default == rhs.i32_default &&
        self.i32_0 == rhs.i32_0 &&
        self.i32_42 == rhs.i32_42 &&
        self.i32_m42 == rhs.i32_m42 &&
        self.i32_2147483647 == rhs.i32_2147483647 &&
        self.i32_m2147483648 == rhs.i32_m2147483648 &&
        self.i32_0123 == rhs.i32_0123 &&
        self.i32_0x123 == rhs.i32_0x123 &&
        self.u32_default == rhs.u32_default &&
        self.u32_0 == rhs.u32_0 &&
        self.u32_42 == rhs.u32_42 &&
        self.u32_4294967295 == rhs.u32_4294967295 &&
        self.u32_0123 == rhs.u32_0123 &&
        self.u32_0x123 == rhs.u32_0x123 &&
        self.i64_default == rhs.i64_default &&
        self.i64_0 == rhs.i64_0 &&
        self.i64_42 == rhs.i64_42 &&
        self.i64_m42 == rhs.i64_m42 &&
        self.i64_9223372036854775807 == rhs.i64_9223372036854775807 &&
        self.i64_m9223372036854775808 == rhs.i64_m9223372036854775808 &&
        self.i64_0123 == rhs.i64_0123 &&
        self.i64_0x123 == rhs.i64_0x123 &&
        self.u64_default == rhs.u64_default &&
        self.u64_0 == rhs.u64_0 &&
        self.u64_42 == rhs.u64_42 &&
        self.u64_18446744073709551615 == rhs.u64_18446744073709551615 &&
        self.u64_0123 == rhs.u64_0123 &&
        self.u64_0x123 == rhs.u64_0x123 &&
        self.f32_default == rhs.f32_default &&
        self.f32_0 == rhs.f32_0 &&
        self.f32_m0 == rhs.f32_m0 &&
        self.f32_0p == rhs.f32_0p &&
        self.f32_p0 == rhs.f32_p0 &&
        self.f32_0p0 == rhs.f32_0p0 &&
        self.f32_42 == rhs.f32_42 &&
        self.f32_m42 == rhs.f32_m42 &&
        self.f32_0p25 == rhs.f32_0p25 &&
        self.f32_1p5e2 == rhs.f32_1p5e2 &&
        self.f32_inf == rhs.f32_inf &&
        self.f32_minf == rhs.f32_minf &&
        self.f32_nan == rhs.f32_nan &&
        self.f32_mnan == rhs.f32_mnan &&
        self.bool_default == rhs.bool_default &&
        self.bool_true == rhs.bool_true &&
        self.bool_false == rhs.bool_false &&
        self.string_default == rhs.string_default &&
        self.string_empty == rhs.string_empty &&
        self.string_abc == rhs.string_abc &&
        self.string_aiu == rhs.string_aiu &&
        self.string_backslash == rhs.string_backslash &&
        self.string_tab == rhs.string_tab &&
        self.string_crlf == rhs.string_crlf &&
        self.bytes_default == rhs.bytes_default &&
        self.bytes_empty == rhs.bytes_empty &&
        self.bytes_abc == rhs.bytes_abc &&
        self.bytes_aiu == rhs.bytes_aiu &&
        self.bytes_backslash == rhs.bytes_backslash &&
        self.bytes_tab == rhs.bytes_tab &&
        self.bytes_crlf == rhs.bytes_crlf &&
        self.enum_default == rhs.enum_default &&
        self.enum_one == rhs.enum_one &&
        self.enum_fourty_two == rhs.enum_fourty_two &&
        true
    }
}
}

pub use _puroro_impls::*;
pub mod _puroro_impls {
    mod _puroro_root {
        pub use super::super::_puroro_root::*;
    }use super::_puroro_traits::*;

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField1<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub i32_default: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField1<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField1<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn i32_default_opt<'this>(&'this self) -> ::std::option::Option<i32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.i32_default))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField1<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_default_opt(self),
            1,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField1<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            i32_default: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField2<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub i32_0: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField2<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField2<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn i32_0_opt<'this>(&'this self) -> ::std::option::Option<i32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.i32_0))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField2<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_0_opt(self),
            2,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField2<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            i32_0: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField3<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub i32_42: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField3<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField3<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn i32_42_opt<'this>(&'this self) -> ::std::option::Option<i32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.i32_42))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField3<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_42_opt(self),
            3,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField3<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            i32_42: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField4<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub i32_m42: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField4<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField4<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn i32_m42_opt<'this>(&'this self) -> ::std::option::Option<i32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.i32_m42))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField4<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_m42_opt(self),
            4,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField4<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            i32_m42: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField5<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub i32_2147483647: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField5<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField5<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn i32_2147483647_opt<'this>(&'this self) -> ::std::option::Option<i32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.i32_2147483647))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField5<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_2147483647_opt(self),
            5,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField5<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            i32_2147483647: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField6<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub i32_m2147483648: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField6<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField6<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn i32_m2147483648_opt<'this>(&'this self) -> ::std::option::Option<i32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.i32_m2147483648))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField6<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_m2147483648_opt(self),
            6,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField6<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            i32_m2147483648: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField7<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub i32_0123: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField7<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField7<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn i32_0123_opt<'this>(&'this self) -> ::std::option::Option<i32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.i32_0123))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField7<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_0123_opt(self),
            7,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField7<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            i32_0123: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField8<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub i32_0x123: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField8<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField8<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn i32_0x123_opt<'this>(&'this self) -> ::std::option::Option<i32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.i32_0x123))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField8<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_0x123_opt(self),
            8,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField8<ScalarType>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            i32_0x123: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField11<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub u32_default: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField11<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField11<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn u32_default_opt<'this>(&'this self) -> ::std::option::Option<u32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.u32_default))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField11<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_default_opt(self),
            11,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField11<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            u32_default: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField12<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub u32_0: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField12<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField12<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn u32_0_opt<'this>(&'this self) -> ::std::option::Option<u32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.u32_0))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField12<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_0_opt(self),
            12,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField12<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            u32_0: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField13<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub u32_42: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField13<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField13<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn u32_42_opt<'this>(&'this self) -> ::std::option::Option<u32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.u32_42))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField13<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_42_opt(self),
            13,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField13<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            u32_42: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField15<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub u32_4294967295: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField15<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField15<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn u32_4294967295_opt<'this>(&'this self) -> ::std::option::Option<u32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.u32_4294967295))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField15<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_4294967295_opt(self),
            15,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField15<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            u32_4294967295: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField17<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub u32_0123: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField17<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField17<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn u32_0123_opt<'this>(&'this self) -> ::std::option::Option<u32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.u32_0123))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField17<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_0123_opt(self),
            17,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField17<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            u32_0123: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField18<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub u32_0x123: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField18<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField18<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn u32_0x123_opt<'this>(&'this self) -> ::std::option::Option<u32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.u32_0x123))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField18<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_0x123_opt(self),
            18,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField18<ScalarType>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            u32_0x123: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField21<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub i64_default: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField21<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField21<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn i64_default_opt<'this>(&'this self) -> ::std::option::Option<i64> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.i64_default))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField21<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_default_opt(self),
            21,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField21<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            i64_default: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField22<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub i64_0: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField22<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField22<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn i64_0_opt<'this>(&'this self) -> ::std::option::Option<i64> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.i64_0))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField22<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_0_opt(self),
            22,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField22<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            i64_0: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField23<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub i64_42: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField23<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField23<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn i64_42_opt<'this>(&'this self) -> ::std::option::Option<i64> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.i64_42))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField23<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_42_opt(self),
            23,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField23<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            i64_42: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField24<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub i64_m42: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField24<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField24<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn i64_m42_opt<'this>(&'this self) -> ::std::option::Option<i64> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.i64_m42))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField24<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_m42_opt(self),
            24,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField24<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            i64_m42: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField25<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub i64_9223372036854775807: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField25<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField25<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn i64_9223372036854775807_opt<'this>(&'this self) -> ::std::option::Option<i64> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.i64_9223372036854775807))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField25<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_9223372036854775807_opt(self),
            25,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField25<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            i64_9223372036854775807: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField26<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub i64_m9223372036854775808: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField26<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField26<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn i64_m9223372036854775808_opt<'this>(&'this self) -> ::std::option::Option<i64> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.i64_m9223372036854775808))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField26<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_m9223372036854775808_opt(self),
            26,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField26<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            i64_m9223372036854775808: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField27<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub i64_0123: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField27<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField27<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn i64_0123_opt<'this>(&'this self) -> ::std::option::Option<i64> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.i64_0123))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField27<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_0123_opt(self),
            27,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField27<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            i64_0123: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField28<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub i64_0x123: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField28<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField28<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn i64_0x123_opt<'this>(&'this self) -> ::std::option::Option<i64> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.i64_0x123))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField28<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_0x123_opt(self),
            28,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField28<ScalarType>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            i64_0x123: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField31<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub u64_default: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField31<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField31<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn u64_default_opt<'this>(&'this self) -> ::std::option::Option<u64> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.u64_default))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField31<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_default_opt(self),
            31,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField31<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            u64_default: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField32<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub u64_0: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField32<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField32<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn u64_0_opt<'this>(&'this self) -> ::std::option::Option<u64> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.u64_0))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField32<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_0_opt(self),
            32,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField32<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            u64_0: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField33<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub u64_42: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField33<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField33<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn u64_42_opt<'this>(&'this self) -> ::std::option::Option<u64> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.u64_42))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField33<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_42_opt(self),
            33,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField33<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            u64_42: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField35<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub u64_18446744073709551615: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField35<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField35<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn u64_18446744073709551615_opt<'this>(&'this self) -> ::std::option::Option<u64> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.u64_18446744073709551615))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField35<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_18446744073709551615_opt(self),
            35,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField35<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            u64_18446744073709551615: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField37<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub u64_0123: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField37<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField37<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn u64_0123_opt<'this>(&'this self) -> ::std::option::Option<u64> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.u64_0123))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField37<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_0123_opt(self),
            37,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField37<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            u64_0123: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField38<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub u64_0x123: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField38<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField38<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn u64_0x123_opt<'this>(&'this self) -> ::std::option::Option<u64> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.u64_0x123))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField38<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_0x123_opt(self),
            38,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField38<ScalarType>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            u64_0x123: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField41<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub f32_default: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField41<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField41<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn f32_default_opt<'this>(&'this self) -> ::std::option::Option<f32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.f32_default))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField41<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_default_opt(self),
            41,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField41<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            f32_default: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField42<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub f32_0: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField42<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField42<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn f32_0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.f32_0))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField42<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_0_opt(self),
            42,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField42<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            f32_0: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField43<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub f32_m0: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField43<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField43<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn f32_m0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.f32_m0))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField43<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_m0_opt(self),
            43,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField43<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            f32_m0: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField44<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub f32_0p: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField44<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField44<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn f32_0p_opt<'this>(&'this self) -> ::std::option::Option<f32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.f32_0p))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField44<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_0p_opt(self),
            44,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField44<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            f32_0p: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField45<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub f32_p0: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField45<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField45<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn f32_p0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.f32_p0))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField45<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_p0_opt(self),
            45,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField45<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            f32_p0: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField46<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub f32_0p0: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField46<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField46<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn f32_0p0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.f32_0p0))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField46<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_0p0_opt(self),
            46,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField46<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            f32_0p0: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField47<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub f32_42: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField47<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField47<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn f32_42_opt<'this>(&'this self) -> ::std::option::Option<f32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.f32_42))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField47<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_42_opt(self),
            47,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField47<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            f32_42: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField48<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub f32_m42: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField48<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField48<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn f32_m42_opt<'this>(&'this self) -> ::std::option::Option<f32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.f32_m42))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField48<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_m42_opt(self),
            48,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField48<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            f32_m42: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField49<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub f32_0p25: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField49<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField49<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn f32_0p25_opt<'this>(&'this self) -> ::std::option::Option<f32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.f32_0p25))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField49<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_0p25_opt(self),
            49,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField49<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            f32_0p25: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField50<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub f32_1p5e2: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField50<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField50<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn f32_1p5e2_opt<'this>(&'this self) -> ::std::option::Option<f32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.f32_1p5e2))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField50<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_1p5e2_opt(self),
            50,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField50<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            f32_1p5e2: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField51<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub f32_inf: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField51<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField51<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn f32_inf_opt<'this>(&'this self) -> ::std::option::Option<f32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.f32_inf))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField51<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_inf_opt(self),
            51,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField51<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            f32_inf: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField52<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub f32_minf: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField52<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField52<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn f32_minf_opt<'this>(&'this self) -> ::std::option::Option<f32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.f32_minf))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField52<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_minf_opt(self),
            52,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField52<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            f32_minf: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField53<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub f32_nan: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField53<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField53<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn f32_nan_opt<'this>(&'this self) -> ::std::option::Option<f32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.f32_nan))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField53<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_nan_opt(self),
            53,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField53<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            f32_nan: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField54<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub f32_mnan: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField54<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField54<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn f32_mnan_opt<'this>(&'this self) -> ::std::option::Option<f32> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.f32_mnan))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField54<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_mnan_opt(self),
            54,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField54<ScalarType>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            f32_mnan: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField61<ScalarType>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub bool_default: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField61<ScalarType>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField61<ScalarType>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn bool_default_opt<'this>(&'this self) -> ::std::option::Option<bool> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.bool_default))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField61<ScalarType>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bool
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bool_default_opt(self),
            61,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField61<ScalarType>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            bool_default: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField62<ScalarType>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub bool_true: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField62<ScalarType>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField62<ScalarType>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn bool_true_opt<'this>(&'this self) -> ::std::option::Option<bool> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.bool_true))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField62<ScalarType>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bool
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bool_true_opt(self),
            62,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField62<ScalarType>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            bool_true: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField63<ScalarType>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub bool_false: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField63<ScalarType>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField63<ScalarType>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn bool_false_opt<'this>(&'this self) -> ::std::option::Option<bool> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.bool_false))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField63<ScalarType>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bool
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bool_false_opt(self),
            63,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField63<ScalarType>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            bool_false: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField71<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub string_default: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField71<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField71<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn string_default_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
    ::std::option::Option::Some(self.string_default.as_ref())
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField71<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_default_opt(self),
            71,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField71<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
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

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub string_empty: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField72<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField72<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn string_empty_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
    ::std::option::Option::Some(self.string_empty.as_ref())
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField72<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_empty_opt(self),
            72,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField72<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
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

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub string_abc: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField73<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField73<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn string_abc_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
    ::std::option::Option::Some(self.string_abc.as_ref())
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField73<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_abc_opt(self),
            73,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField73<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            string_abc: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField74<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub string_aiu: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField74<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField74<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn string_aiu_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
    ::std::option::Option::Some(self.string_aiu.as_ref())
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField74<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_aiu_opt(self),
            74,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField74<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            string_aiu: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField75<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub string_backslash: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField75<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField75<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn string_backslash_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
    ::std::option::Option::Some(self.string_backslash.as_ref())
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField75<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_backslash_opt(self),
            75,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField75<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
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

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub string_tab: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField76<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField76<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn string_tab_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
    ::std::option::Option::Some(self.string_tab.as_ref())
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField76<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_tab_opt(self),
            76,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField76<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            string_tab: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField77<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub string_crlf: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField77<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField77<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn string_crlf_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
    ::std::option::Option::Some(self.string_crlf.as_ref())
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField77<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_crlf_opt(self),
            77,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField77<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            string_crlf: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField81<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub bytes_default: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField81<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField81<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn bytes_default_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
    ::std::option::Option::Some(self.bytes_default.as_ref())
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField81<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_default_opt(self),
            81,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField81<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
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

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub bytes_empty: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField82<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField82<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn bytes_empty_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
    ::std::option::Option::Some(self.bytes_empty.as_ref())
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField82<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_empty_opt(self),
            82,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField82<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            bytes_empty: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField83<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub bytes_abc: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField83<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField83<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn bytes_abc_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
    ::std::option::Option::Some(self.bytes_abc.as_ref())
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField83<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_abc_opt(self),
            83,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField83<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            bytes_abc: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField84<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub bytes_aiu: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField84<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField84<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn bytes_aiu_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
    ::std::option::Option::Some(self.bytes_aiu.as_ref())
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField84<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_aiu_opt(self),
            84,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField84<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            bytes_aiu: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField85<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub bytes_backslash: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField85<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField85<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn bytes_backslash_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
    ::std::option::Option::Some(self.bytes_backslash.as_ref())
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField85<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_backslash_opt(self),
            85,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField85<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
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

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub bytes_tab: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField86<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField86<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn bytes_tab_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
    ::std::option::Option::Some(self.bytes_tab.as_ref())
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField86<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_tab_opt(self),
            86,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField86<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            bytes_tab: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField87<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub bytes_crlf: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField87<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField87<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn bytes_crlf_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
    ::std::option::Option::Some(self.bytes_crlf.as_ref())
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField87<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_crlf_opt(self),
            87,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField87<ScalarType>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            bytes_crlf: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField91<ScalarType>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub enum_default: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField91<ScalarType>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField91<ScalarType>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn enum_default_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.enum_default))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField91<ScalarType>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::enum_default_opt(self),
            91,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField91<ScalarType>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            enum_default: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField92<ScalarType>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub enum_one: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField92<ScalarType>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField92<ScalarType>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn enum_one_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.enum_one))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField92<ScalarType>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::enum_one_opt(self),
            92,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField92<ScalarType>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            enum_one: value,
        }
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]

pub struct MsgSingleField93<ScalarType>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    pub enum_fourty_two: ScalarType,
}

impl<ScalarType> ::puroro::Message<super::Msg>
for MsgSingleField93<ScalarType>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{}

impl<ScalarType> super::_puroro_traits::MsgTrait
for MsgSingleField93<ScalarType>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{

fn enum_fourty_two_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
    ::std::option::Option::Some(
        ::std::convert::Into::into(::std::clone::Clone::clone(&self.enum_fourty_two))
    )
}
}


impl<ScalarType> ::puroro::internal::se::SerMessageToIoWrite
for MsgSingleField93<ScalarType>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::enum_fourty_two_opt(self),
            93,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}

impl<ScalarType> ::std::convert::From<ScalarType>
for MsgSingleField93<ScalarType>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
{
    fn from(value: ScalarType) -> Self {
        Self {
            enum_fourty_two: value,
        }
    }
}
pub struct MsgBumpalo<'bump> {
    _bump: &'bump ::puroro::bumpalo::Bump,
    _bitfield: ::puroro::bitvec::array::BitArray<
        ::puroro::bitvec::order::Lsb0,
        [u32; (62 + 31) / 32],
    >,
    i32_default: ::puroro::internal::Bare<i32>,
    i32_0: ::puroro::internal::Bare<i32>,
    i32_42: ::puroro::internal::Bare<i32>,
    i32_m42: ::puroro::internal::Bare<i32>,
    i32_2147483647: ::puroro::internal::Bare<i32>,
    i32_m2147483648: ::puroro::internal::Bare<i32>,
    i32_0123: ::puroro::internal::Bare<i32>,
    i32_0x123: ::puroro::internal::Bare<i32>,
    u32_default: ::puroro::internal::Bare<u32>,
    u32_0: ::puroro::internal::Bare<u32>,
    u32_42: ::puroro::internal::Bare<u32>,
    u32_4294967295: ::puroro::internal::Bare<u32>,
    u32_0123: ::puroro::internal::Bare<u32>,
    u32_0x123: ::puroro::internal::Bare<u32>,
    i64_default: ::puroro::internal::Bare<i64>,
    i64_0: ::puroro::internal::Bare<i64>,
    i64_42: ::puroro::internal::Bare<i64>,
    i64_m42: ::puroro::internal::Bare<i64>,
    i64_9223372036854775807: ::puroro::internal::Bare<i64>,
    i64_m9223372036854775808: ::puroro::internal::Bare<i64>,
    i64_0123: ::puroro::internal::Bare<i64>,
    i64_0x123: ::puroro::internal::Bare<i64>,
    u64_default: ::puroro::internal::Bare<u64>,
    u64_0: ::puroro::internal::Bare<u64>,
    u64_42: ::puroro::internal::Bare<u64>,
    u64_18446744073709551615: ::puroro::internal::Bare<u64>,
    u64_0123: ::puroro::internal::Bare<u64>,
    u64_0x123: ::puroro::internal::Bare<u64>,
    f32_default: ::puroro::internal::Bare<f32>,
    f32_0: ::puroro::internal::Bare<f32>,
    f32_m0: ::puroro::internal::Bare<f32>,
    f32_0p: ::puroro::internal::Bare<f32>,
    f32_p0: ::puroro::internal::Bare<f32>,
    f32_0p0: ::puroro::internal::Bare<f32>,
    f32_42: ::puroro::internal::Bare<f32>,
    f32_m42: ::puroro::internal::Bare<f32>,
    f32_0p25: ::puroro::internal::Bare<f32>,
    f32_1p5e2: ::puroro::internal::Bare<f32>,
    f32_inf: ::puroro::internal::Bare<f32>,
    f32_minf: ::puroro::internal::Bare<f32>,
    f32_nan: ::puroro::internal::Bare<f32>,
    f32_mnan: ::puroro::internal::Bare<f32>,
    bool_default: ::puroro::internal::Bare<bool>,
    bool_true: ::puroro::internal::Bare<bool>,
    bool_false: ::puroro::internal::Bare<bool>,
    string_default: ::puroro::internal::Bare<::puroro::internal::NoAllocBumpString>,
    string_empty: ::puroro::internal::Bare<::puroro::internal::NoAllocBumpString>,
    string_abc: ::puroro::internal::Bare<::puroro::internal::NoAllocBumpString>,
    string_aiu: ::puroro::internal::Bare<::puroro::internal::NoAllocBumpString>,
    string_backslash: ::puroro::internal::Bare<::puroro::internal::NoAllocBumpString>,
    string_tab: ::puroro::internal::Bare<::puroro::internal::NoAllocBumpString>,
    string_crlf: ::puroro::internal::Bare<::puroro::internal::NoAllocBumpString>,
    bytes_default: ::puroro::internal::Bare<::puroro::internal::NoAllocBumpVec<u8>>,
    bytes_empty: ::puroro::internal::Bare<::puroro::internal::NoAllocBumpVec<u8>>,
    bytes_abc: ::puroro::internal::Bare<::puroro::internal::NoAllocBumpVec<u8>>,
    bytes_aiu: ::puroro::internal::Bare<::puroro::internal::NoAllocBumpVec<u8>>,
    bytes_backslash: ::puroro::internal::Bare<::puroro::internal::NoAllocBumpVec<u8>>,
    bytes_tab: ::puroro::internal::Bare<::puroro::internal::NoAllocBumpVec<u8>>,
    bytes_crlf: ::puroro::internal::Bare<::puroro::internal::NoAllocBumpVec<u8>>,
    enum_default: ::puroro::internal::Bare<self::_puroro_root::proto2_defaults::MyEnum>,
    enum_one: ::puroro::internal::Bare<self::_puroro_root::proto2_defaults::MyEnum>,
    enum_fourty_two: ::puroro::internal::Bare<self::_puroro_root::proto2_defaults::MyEnum>,
}

pub type MsgBumpaloOwned = ::puroro::BumpaloOwned<MsgBumpalo<'static>>;
impl<'bump> MsgBumpalo<'bump> {
    pub fn new_in(bump: &'bump ::puroro::bumpalo::Bump) -> Self {
        #[allow(unused)]
        let bump_ref: &::puroro::bumpalo::Bump = unsafe {
            ::std::mem::transmute(
                ::std::ops::Deref::deref(&bump)
            )
        };

        Self {
            _bump: bump,
            _bitfield: ::std::default::Default::default(),
            i32_default: ::std::default::Default::default(),
            i32_0: ::std::default::Default::default(),
            i32_42: ::std::default::Default::default(),
            i32_m42: ::std::default::Default::default(),
            i32_2147483647: ::std::default::Default::default(),
            i32_m2147483648: ::std::default::Default::default(),
            i32_0123: ::std::default::Default::default(),
            i32_0x123: ::std::default::Default::default(),
            u32_default: ::std::default::Default::default(),
            u32_0: ::std::default::Default::default(),
            u32_42: ::std::default::Default::default(),
            u32_4294967295: ::std::default::Default::default(),
            u32_0123: ::std::default::Default::default(),
            u32_0x123: ::std::default::Default::default(),
            i64_default: ::std::default::Default::default(),
            i64_0: ::std::default::Default::default(),
            i64_42: ::std::default::Default::default(),
            i64_m42: ::std::default::Default::default(),
            i64_9223372036854775807: ::std::default::Default::default(),
            i64_m9223372036854775808: ::std::default::Default::default(),
            i64_0123: ::std::default::Default::default(),
            i64_0x123: ::std::default::Default::default(),
            u64_default: ::std::default::Default::default(),
            u64_0: ::std::default::Default::default(),
            u64_42: ::std::default::Default::default(),
            u64_18446744073709551615: ::std::default::Default::default(),
            u64_0123: ::std::default::Default::default(),
            u64_0x123: ::std::default::Default::default(),
            f32_default: ::std::default::Default::default(),
            f32_0: ::std::default::Default::default(),
            f32_m0: ::std::default::Default::default(),
            f32_0p: ::std::default::Default::default(),
            f32_p0: ::std::default::Default::default(),
            f32_0p0: ::std::default::Default::default(),
            f32_42: ::std::default::Default::default(),
            f32_m42: ::std::default::Default::default(),
            f32_0p25: ::std::default::Default::default(),
            f32_1p5e2: ::std::default::Default::default(),
            f32_inf: ::std::default::Default::default(),
            f32_minf: ::std::default::Default::default(),
            f32_nan: ::std::default::Default::default(),
            f32_mnan: ::std::default::Default::default(),
            bool_default: ::std::default::Default::default(),
            bool_true: ::std::default::Default::default(),
            bool_false: ::std::default::Default::default(),
            string_default: ::std::default::Default::default(),
            string_empty: ::std::default::Default::default(),
            string_abc: ::std::default::Default::default(),
            string_aiu: ::std::default::Default::default(),
            string_backslash: ::std::default::Default::default(),
            string_tab: ::std::default::Default::default(),
            string_crlf: ::std::default::Default::default(),
            bytes_default: ::std::default::Default::default(),
            bytes_empty: ::std::default::Default::default(),
            bytes_abc: ::std::default::Default::default(),
            bytes_aiu: ::std::default::Default::default(),
            bytes_backslash: ::std::default::Default::default(),
            bytes_tab: ::std::default::Default::default(),
            bytes_crlf: ::std::default::Default::default(),
            enum_default: ::std::default::Default::default(),
            enum_one: ::std::default::Default::default(),
            enum_fourty_two: ::std::default::Default::default(),
        }
    }
    pub fn i32_default_opt<'this>(&'this self) -> ::std::option::Option<i32> {
        if self._bitfield.get(0).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.i32_default.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn i32_default<'this>(&'this self) -> i32 {
        match self.i32_default_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                ::std::default::Default::default()
            }
        }
    }

    pub fn has_i32_default(&self) -> bool {
        self.i32_default_opt().is_some()
    }
    pub fn i32_0_opt<'this>(&'this self) -> ::std::option::Option<i32> {
        if self._bitfield.get(1).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.i32_0.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn i32_0<'this>(&'this self) -> i32 {
        match self.i32_0_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                0
            }
        }
    }

    pub fn has_i32_0(&self) -> bool {
        self.i32_0_opt().is_some()
    }
    pub fn i32_42_opt<'this>(&'this self) -> ::std::option::Option<i32> {
        if self._bitfield.get(2).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.i32_42.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn i32_42<'this>(&'this self) -> i32 {
        match self.i32_42_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                42
            }
        }
    }

    pub fn has_i32_42(&self) -> bool {
        self.i32_42_opt().is_some()
    }
    pub fn i32_m42_opt<'this>(&'this self) -> ::std::option::Option<i32> {
        if self._bitfield.get(3).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.i32_m42.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn i32_m42<'this>(&'this self) -> i32 {
        match self.i32_m42_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                -42
            }
        }
    }

    pub fn has_i32_m42(&self) -> bool {
        self.i32_m42_opt().is_some()
    }
    pub fn i32_2147483647_opt<'this>(&'this self) -> ::std::option::Option<i32> {
        if self._bitfield.get(4).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.i32_2147483647.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn i32_2147483647<'this>(&'this self) -> i32 {
        match self.i32_2147483647_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                2147483647
            }
        }
    }

    pub fn has_i32_2147483647(&self) -> bool {
        self.i32_2147483647_opt().is_some()
    }
    pub fn i32_m2147483648_opt<'this>(&'this self) -> ::std::option::Option<i32> {
        if self._bitfield.get(5).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.i32_m2147483648.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn i32_m2147483648<'this>(&'this self) -> i32 {
        match self.i32_m2147483648_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                -2147483648
            }
        }
    }

    pub fn has_i32_m2147483648(&self) -> bool {
        self.i32_m2147483648_opt().is_some()
    }
    pub fn i32_0123_opt<'this>(&'this self) -> ::std::option::Option<i32> {
        if self._bitfield.get(6).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.i32_0123.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn i32_0123<'this>(&'this self) -> i32 {
        match self.i32_0123_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                83
            }
        }
    }

    pub fn has_i32_0123(&self) -> bool {
        self.i32_0123_opt().is_some()
    }
    pub fn i32_0x123_opt<'this>(&'this self) -> ::std::option::Option<i32> {
        if self._bitfield.get(7).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.i32_0x123.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn i32_0x123<'this>(&'this self) -> i32 {
        match self.i32_0x123_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                291
            }
        }
    }

    pub fn has_i32_0x123(&self) -> bool {
        self.i32_0x123_opt().is_some()
    }
    pub fn u32_default_opt<'this>(&'this self) -> ::std::option::Option<u32> {
        if self._bitfield.get(8).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.u32_default.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn u32_default<'this>(&'this self) -> u32 {
        match self.u32_default_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                ::std::default::Default::default()
            }
        }
    }

    pub fn has_u32_default(&self) -> bool {
        self.u32_default_opt().is_some()
    }
    pub fn u32_0_opt<'this>(&'this self) -> ::std::option::Option<u32> {
        if self._bitfield.get(9).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.u32_0.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn u32_0<'this>(&'this self) -> u32 {
        match self.u32_0_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                0
            }
        }
    }

    pub fn has_u32_0(&self) -> bool {
        self.u32_0_opt().is_some()
    }
    pub fn u32_42_opt<'this>(&'this self) -> ::std::option::Option<u32> {
        if self._bitfield.get(10).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.u32_42.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn u32_42<'this>(&'this self) -> u32 {
        match self.u32_42_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                42
            }
        }
    }

    pub fn has_u32_42(&self) -> bool {
        self.u32_42_opt().is_some()
    }
    pub fn u32_4294967295_opt<'this>(&'this self) -> ::std::option::Option<u32> {
        if self._bitfield.get(11).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.u32_4294967295.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn u32_4294967295<'this>(&'this self) -> u32 {
        match self.u32_4294967295_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                4294967295
            }
        }
    }

    pub fn has_u32_4294967295(&self) -> bool {
        self.u32_4294967295_opt().is_some()
    }
    pub fn u32_0123_opt<'this>(&'this self) -> ::std::option::Option<u32> {
        if self._bitfield.get(12).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.u32_0123.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn u32_0123<'this>(&'this self) -> u32 {
        match self.u32_0123_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                83
            }
        }
    }

    pub fn has_u32_0123(&self) -> bool {
        self.u32_0123_opt().is_some()
    }
    pub fn u32_0x123_opt<'this>(&'this self) -> ::std::option::Option<u32> {
        if self._bitfield.get(13).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.u32_0x123.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn u32_0x123<'this>(&'this self) -> u32 {
        match self.u32_0x123_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                291
            }
        }
    }

    pub fn has_u32_0x123(&self) -> bool {
        self.u32_0x123_opt().is_some()
    }
    pub fn i64_default_opt<'this>(&'this self) -> ::std::option::Option<i64> {
        if self._bitfield.get(14).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.i64_default.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn i64_default<'this>(&'this self) -> i64 {
        match self.i64_default_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                ::std::default::Default::default()
            }
        }
    }

    pub fn has_i64_default(&self) -> bool {
        self.i64_default_opt().is_some()
    }
    pub fn i64_0_opt<'this>(&'this self) -> ::std::option::Option<i64> {
        if self._bitfield.get(15).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.i64_0.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn i64_0<'this>(&'this self) -> i64 {
        match self.i64_0_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                0
            }
        }
    }

    pub fn has_i64_0(&self) -> bool {
        self.i64_0_opt().is_some()
    }
    pub fn i64_42_opt<'this>(&'this self) -> ::std::option::Option<i64> {
        if self._bitfield.get(16).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.i64_42.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn i64_42<'this>(&'this self) -> i64 {
        match self.i64_42_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                42
            }
        }
    }

    pub fn has_i64_42(&self) -> bool {
        self.i64_42_opt().is_some()
    }
    pub fn i64_m42_opt<'this>(&'this self) -> ::std::option::Option<i64> {
        if self._bitfield.get(17).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.i64_m42.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn i64_m42<'this>(&'this self) -> i64 {
        match self.i64_m42_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                -42
            }
        }
    }

    pub fn has_i64_m42(&self) -> bool {
        self.i64_m42_opt().is_some()
    }
    pub fn i64_9223372036854775807_opt<'this>(&'this self) -> ::std::option::Option<i64> {
        if self._bitfield.get(18).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.i64_9223372036854775807.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn i64_9223372036854775807<'this>(&'this self) -> i64 {
        match self.i64_9223372036854775807_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                9223372036854775807
            }
        }
    }

    pub fn has_i64_9223372036854775807(&self) -> bool {
        self.i64_9223372036854775807_opt().is_some()
    }
    pub fn i64_m9223372036854775808_opt<'this>(&'this self) -> ::std::option::Option<i64> {
        if self._bitfield.get(19).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.i64_m9223372036854775808.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn i64_m9223372036854775808<'this>(&'this self) -> i64 {
        match self.i64_m9223372036854775808_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                -9223372036854775808
            }
        }
    }

    pub fn has_i64_m9223372036854775808(&self) -> bool {
        self.i64_m9223372036854775808_opt().is_some()
    }
    pub fn i64_0123_opt<'this>(&'this self) -> ::std::option::Option<i64> {
        if self._bitfield.get(20).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.i64_0123.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn i64_0123<'this>(&'this self) -> i64 {
        match self.i64_0123_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                83
            }
        }
    }

    pub fn has_i64_0123(&self) -> bool {
        self.i64_0123_opt().is_some()
    }
    pub fn i64_0x123_opt<'this>(&'this self) -> ::std::option::Option<i64> {
        if self._bitfield.get(21).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.i64_0x123.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn i64_0x123<'this>(&'this self) -> i64 {
        match self.i64_0x123_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                291
            }
        }
    }

    pub fn has_i64_0x123(&self) -> bool {
        self.i64_0x123_opt().is_some()
    }
    pub fn u64_default_opt<'this>(&'this self) -> ::std::option::Option<u64> {
        if self._bitfield.get(22).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.u64_default.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn u64_default<'this>(&'this self) -> u64 {
        match self.u64_default_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                ::std::default::Default::default()
            }
        }
    }

    pub fn has_u64_default(&self) -> bool {
        self.u64_default_opt().is_some()
    }
    pub fn u64_0_opt<'this>(&'this self) -> ::std::option::Option<u64> {
        if self._bitfield.get(23).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.u64_0.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn u64_0<'this>(&'this self) -> u64 {
        match self.u64_0_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                0
            }
        }
    }

    pub fn has_u64_0(&self) -> bool {
        self.u64_0_opt().is_some()
    }
    pub fn u64_42_opt<'this>(&'this self) -> ::std::option::Option<u64> {
        if self._bitfield.get(24).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.u64_42.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn u64_42<'this>(&'this self) -> u64 {
        match self.u64_42_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                42
            }
        }
    }

    pub fn has_u64_42(&self) -> bool {
        self.u64_42_opt().is_some()
    }
    pub fn u64_18446744073709551615_opt<'this>(&'this self) -> ::std::option::Option<u64> {
        if self._bitfield.get(25).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.u64_18446744073709551615.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn u64_18446744073709551615<'this>(&'this self) -> u64 {
        match self.u64_18446744073709551615_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                18446744073709551615
            }
        }
    }

    pub fn has_u64_18446744073709551615(&self) -> bool {
        self.u64_18446744073709551615_opt().is_some()
    }
    pub fn u64_0123_opt<'this>(&'this self) -> ::std::option::Option<u64> {
        if self._bitfield.get(26).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.u64_0123.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn u64_0123<'this>(&'this self) -> u64 {
        match self.u64_0123_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                83
            }
        }
    }

    pub fn has_u64_0123(&self) -> bool {
        self.u64_0123_opt().is_some()
    }
    pub fn u64_0x123_opt<'this>(&'this self) -> ::std::option::Option<u64> {
        if self._bitfield.get(27).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.u64_0x123.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn u64_0x123<'this>(&'this self) -> u64 {
        match self.u64_0x123_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                291
            }
        }
    }

    pub fn has_u64_0x123(&self) -> bool {
        self.u64_0x123_opt().is_some()
    }
    pub fn f32_default_opt<'this>(&'this self) -> ::std::option::Option<f32> {
        if self._bitfield.get(28).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.f32_default.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn f32_default<'this>(&'this self) -> f32 {
        match self.f32_default_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                ::std::default::Default::default()
            }
        }
    }

    pub fn has_f32_default(&self) -> bool {
        self.f32_default_opt().is_some()
    }
    pub fn f32_0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
        if self._bitfield.get(29).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.f32_0.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn f32_0<'this>(&'this self) -> f32 {
        match self.f32_0_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                0f32
            }
        }
    }

    pub fn has_f32_0(&self) -> bool {
        self.f32_0_opt().is_some()
    }
    pub fn f32_m0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
        if self._bitfield.get(30).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.f32_m0.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn f32_m0<'this>(&'this self) -> f32 {
        match self.f32_m0_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                -0f32
            }
        }
    }

    pub fn has_f32_m0(&self) -> bool {
        self.f32_m0_opt().is_some()
    }
    pub fn f32_0p_opt<'this>(&'this self) -> ::std::option::Option<f32> {
        if self._bitfield.get(31).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.f32_0p.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn f32_0p<'this>(&'this self) -> f32 {
        match self.f32_0p_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                0f32
            }
        }
    }

    pub fn has_f32_0p(&self) -> bool {
        self.f32_0p_opt().is_some()
    }
    pub fn f32_p0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
        if self._bitfield.get(32).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.f32_p0.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn f32_p0<'this>(&'this self) -> f32 {
        match self.f32_p0_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                0f32
            }
        }
    }

    pub fn has_f32_p0(&self) -> bool {
        self.f32_p0_opt().is_some()
    }
    pub fn f32_0p0_opt<'this>(&'this self) -> ::std::option::Option<f32> {
        if self._bitfield.get(33).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.f32_0p0.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn f32_0p0<'this>(&'this self) -> f32 {
        match self.f32_0p0_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                0f32
            }
        }
    }

    pub fn has_f32_0p0(&self) -> bool {
        self.f32_0p0_opt().is_some()
    }
    pub fn f32_42_opt<'this>(&'this self) -> ::std::option::Option<f32> {
        if self._bitfield.get(34).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.f32_42.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn f32_42<'this>(&'this self) -> f32 {
        match self.f32_42_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                42f32
            }
        }
    }

    pub fn has_f32_42(&self) -> bool {
        self.f32_42_opt().is_some()
    }
    pub fn f32_m42_opt<'this>(&'this self) -> ::std::option::Option<f32> {
        if self._bitfield.get(35).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.f32_m42.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn f32_m42<'this>(&'this self) -> f32 {
        match self.f32_m42_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                -42f32
            }
        }
    }

    pub fn has_f32_m42(&self) -> bool {
        self.f32_m42_opt().is_some()
    }
    pub fn f32_0p25_opt<'this>(&'this self) -> ::std::option::Option<f32> {
        if self._bitfield.get(36).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.f32_0p25.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn f32_0p25<'this>(&'this self) -> f32 {
        match self.f32_0p25_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                0.25f32
            }
        }
    }

    pub fn has_f32_0p25(&self) -> bool {
        self.f32_0p25_opt().is_some()
    }
    pub fn f32_1p5e2_opt<'this>(&'this self) -> ::std::option::Option<f32> {
        if self._bitfield.get(37).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.f32_1p5e2.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn f32_1p5e2<'this>(&'this self) -> f32 {
        match self.f32_1p5e2_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                150f32
            }
        }
    }

    pub fn has_f32_1p5e2(&self) -> bool {
        self.f32_1p5e2_opt().is_some()
    }
    pub fn f32_inf_opt<'this>(&'this self) -> ::std::option::Option<f32> {
        if self._bitfield.get(38).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.f32_inf.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn f32_inf<'this>(&'this self) -> f32 {
        match self.f32_inf_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                f32::INFINITY
            }
        }
    }

    pub fn has_f32_inf(&self) -> bool {
        self.f32_inf_opt().is_some()
    }
    pub fn f32_minf_opt<'this>(&'this self) -> ::std::option::Option<f32> {
        if self._bitfield.get(39).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.f32_minf.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn f32_minf<'this>(&'this self) -> f32 {
        match self.f32_minf_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                f32::NEG_INFINITY
            }
        }
    }

    pub fn has_f32_minf(&self) -> bool {
        self.f32_minf_opt().is_some()
    }
    pub fn f32_nan_opt<'this>(&'this self) -> ::std::option::Option<f32> {
        if self._bitfield.get(40).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.f32_nan.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn f32_nan<'this>(&'this self) -> f32 {
        match self.f32_nan_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                f32::NAN
            }
        }
    }

    pub fn has_f32_nan(&self) -> bool {
        self.f32_nan_opt().is_some()
    }
    pub fn f32_mnan_opt<'this>(&'this self) -> ::std::option::Option<f32> {
        if self._bitfield.get(41).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.f32_mnan.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn f32_mnan<'this>(&'this self) -> f32 {
        match self.f32_mnan_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                f32::NAN
            }
        }
    }

    pub fn has_f32_mnan(&self) -> bool {
        self.f32_mnan_opt().is_some()
    }
    pub fn bool_default_opt<'this>(&'this self) -> ::std::option::Option<bool> {
        if self._bitfield.get(42).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.bool_default.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn bool_default<'this>(&'this self) -> bool {
        match self.bool_default_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                ::std::default::Default::default()
            }
        }
    }

    pub fn has_bool_default(&self) -> bool {
        self.bool_default_opt().is_some()
    }
    pub fn bool_true_opt<'this>(&'this self) -> ::std::option::Option<bool> {
        if self._bitfield.get(43).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.bool_true.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn bool_true<'this>(&'this self) -> bool {
        match self.bool_true_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                true
            }
        }
    }

    pub fn has_bool_true(&self) -> bool {
        self.bool_true_opt().is_some()
    }
    pub fn bool_false_opt<'this>(&'this self) -> ::std::option::Option<bool> {
        if self._bitfield.get(44).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.bool_false.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn bool_false<'this>(&'this self) -> bool {
        match self.bool_false_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                false
            }
        }
    }

    pub fn has_bool_false(&self) -> bool {
        self.bool_false_opt().is_some()
    }
    pub fn string_default_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
        if self._bitfield.get(45).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                &self.string_default
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn string_default<'this>(&'this self) -> &'this str {
        match self.string_default_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                ::std::default::Default::default()
            }
        }
    }

    pub fn has_string_default(&self) -> bool {
        self.string_default_opt().is_some()
    }
    pub fn string_empty_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
        if self._bitfield.get(46).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                &self.string_empty
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn string_empty<'this>(&'this self) -> &'this str {
        match self.string_empty_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                ""
            }
        }
    }

    pub fn has_string_empty(&self) -> bool {
        self.string_empty_opt().is_some()
    }
    pub fn string_abc_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
        if self._bitfield.get(47).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                &self.string_abc
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn string_abc<'this>(&'this self) -> &'this str {
        match self.string_abc_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                "abc"
            }
        }
    }

    pub fn has_string_abc(&self) -> bool {
        self.string_abc_opt().is_some()
    }
    pub fn string_aiu_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
        if self._bitfield.get(48).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                &self.string_aiu
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn string_aiu<'this>(&'this self) -> &'this str {
        match self.string_aiu_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                "\u{3042}\u{3044}\u{3046}"
            }
        }
    }

    pub fn has_string_aiu(&self) -> bool {
        self.string_aiu_opt().is_some()
    }
    pub fn string_backslash_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
        if self._bitfield.get(49).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                &self.string_backslash
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn string_backslash<'this>(&'this self) -> &'this str {
        match self.string_backslash_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                "\\"
            }
        }
    }

    pub fn has_string_backslash(&self) -> bool {
        self.string_backslash_opt().is_some()
    }
    pub fn string_tab_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
        if self._bitfield.get(50).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                &self.string_tab
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn string_tab<'this>(&'this self) -> &'this str {
        match self.string_tab_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                "\t"
            }
        }
    }

    pub fn has_string_tab(&self) -> bool {
        self.string_tab_opt().is_some()
    }
    pub fn string_crlf_opt<'this>(&'this self) -> ::std::option::Option<&'this str> {
        if self._bitfield.get(51).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                &self.string_crlf
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn string_crlf<'this>(&'this self) -> &'this str {
        match self.string_crlf_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                "\r\n"
            }
        }
    }

    pub fn has_string_crlf(&self) -> bool {
        self.string_crlf_opt().is_some()
    }
    pub fn bytes_default_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
        if self._bitfield.get(52).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                &self.bytes_default
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn bytes_default<'this>(&'this self) -> &'this [u8] {
        match self.bytes_default_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                ::std::default::Default::default()
            }
        }
    }

    pub fn has_bytes_default(&self) -> bool {
        self.bytes_default_opt().is_some()
    }
    pub fn bytes_empty_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
        if self._bitfield.get(53).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                &self.bytes_empty
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn bytes_empty<'this>(&'this self) -> &'this [u8] {
        match self.bytes_empty_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                b""
            }
        }
    }

    pub fn has_bytes_empty(&self) -> bool {
        self.bytes_empty_opt().is_some()
    }
    pub fn bytes_abc_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
        if self._bitfield.get(54).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                &self.bytes_abc
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn bytes_abc<'this>(&'this self) -> &'this [u8] {
        match self.bytes_abc_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                b"\x61\x62\x63"
            }
        }
    }

    pub fn has_bytes_abc(&self) -> bool {
        self.bytes_abc_opt().is_some()
    }
    pub fn bytes_aiu_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
        if self._bitfield.get(55).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                &self.bytes_aiu
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn bytes_aiu<'this>(&'this self) -> &'this [u8] {
        match self.bytes_aiu_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                b"\xe3\x81\x82\xe3\x81\x84\xe3\x81\x86"
            }
        }
    }

    pub fn has_bytes_aiu(&self) -> bool {
        self.bytes_aiu_opt().is_some()
    }
    pub fn bytes_backslash_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
        if self._bitfield.get(56).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                &self.bytes_backslash
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn bytes_backslash<'this>(&'this self) -> &'this [u8] {
        match self.bytes_backslash_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                b"\x5c"
            }
        }
    }

    pub fn has_bytes_backslash(&self) -> bool {
        self.bytes_backslash_opt().is_some()
    }
    pub fn bytes_tab_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
        if self._bitfield.get(57).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                &self.bytes_tab
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn bytes_tab<'this>(&'this self) -> &'this [u8] {
        match self.bytes_tab_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                b"\x09"
            }
        }
    }

    pub fn has_bytes_tab(&self) -> bool {
        self.bytes_tab_opt().is_some()
    }
    pub fn bytes_crlf_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]> {
        if self._bitfield.get(58).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                &self.bytes_crlf
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn bytes_crlf<'this>(&'this self) -> &'this [u8] {
        match self.bytes_crlf_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                b"\x0d\x0a"
            }
        }
    }

    pub fn has_bytes_crlf(&self) -> bool {
        self.bytes_crlf_opt().is_some()
    }
    pub fn enum_default_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
        if self._bitfield.get(59).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.enum_default.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn enum_default<'this>(&'this self) -> self::_puroro_root::proto2_defaults::MyEnum {
        match self.enum_default_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                ::std::default::Default::default()
            }
        }
    }

    pub fn has_enum_default(&self) -> bool {
        self.enum_default_opt().is_some()
    }
    pub fn enum_one_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
        if self._bitfield.get(60).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.enum_one.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn enum_one<'this>(&'this self) -> self::_puroro_root::proto2_defaults::MyEnum {
        match self.enum_one_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                self::_puroro_root::proto2_defaults::MyEnum::One
            }
        }
    }

    pub fn has_enum_one(&self) -> bool {
        self.enum_one_opt().is_some()
    }
    pub fn enum_fourty_two_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
        if self._bitfield.get(61).map_or(false, |v| *v) {
            ::std::option::Option::Some(
                self.enum_fourty_two.inner()
            )
        } else {
            ::std::option::Option::None
        }
    }
    pub fn enum_fourty_two<'this>(&'this self) -> self::_puroro_root::proto2_defaults::MyEnum {
        match self.enum_fourty_two_opt() {
            ::std::option::Option::Some(x) => x,
            _ => {
                self::_puroro_root::proto2_defaults::MyEnum::FourtyTwo
            }
        }
    }

    pub fn has_enum_fourty_two(&self) -> bool {
        self.enum_fourty_two_opt().is_some()
    }
    pub fn clear_i32_default(&mut self) {
        self._bitfield.set(0, false);
    }
    pub fn i32_default_mut<'this>(&'this mut self) -> &'this mut i32 {
        if !self.has_i32_default() {
            self.i32_default = ::std::default::Default::default();
            self._bitfield.set(0, true);
        }
        &mut self.i32_default
    }
    pub fn clear_i32_0(&mut self) {
        self._bitfield.set(1, false);
    }
    pub fn i32_0_mut<'this>(&'this mut self) -> &'this mut i32 {
        if !self.has_i32_0() {
            self.i32_0 = ::std::default::Default::default();
            self._bitfield.set(1, true);
        }
        &mut self.i32_0
    }
    pub fn clear_i32_42(&mut self) {
        self._bitfield.set(2, false);
    }
    pub fn i32_42_mut<'this>(&'this mut self) -> &'this mut i32 {
        if !self.has_i32_42() {
            self.i32_42 = ::std::default::Default::default();
            self._bitfield.set(2, true);
        }
        &mut self.i32_42
    }
    pub fn clear_i32_m42(&mut self) {
        self._bitfield.set(3, false);
    }
    pub fn i32_m42_mut<'this>(&'this mut self) -> &'this mut i32 {
        if !self.has_i32_m42() {
            self.i32_m42 = ::std::default::Default::default();
            self._bitfield.set(3, true);
        }
        &mut self.i32_m42
    }
    pub fn clear_i32_2147483647(&mut self) {
        self._bitfield.set(4, false);
    }
    pub fn i32_2147483647_mut<'this>(&'this mut self) -> &'this mut i32 {
        if !self.has_i32_2147483647() {
            self.i32_2147483647 = ::std::default::Default::default();
            self._bitfield.set(4, true);
        }
        &mut self.i32_2147483647
    }
    pub fn clear_i32_m2147483648(&mut self) {
        self._bitfield.set(5, false);
    }
    pub fn i32_m2147483648_mut<'this>(&'this mut self) -> &'this mut i32 {
        if !self.has_i32_m2147483648() {
            self.i32_m2147483648 = ::std::default::Default::default();
            self._bitfield.set(5, true);
        }
        &mut self.i32_m2147483648
    }
    pub fn clear_i32_0123(&mut self) {
        self._bitfield.set(6, false);
    }
    pub fn i32_0123_mut<'this>(&'this mut self) -> &'this mut i32 {
        if !self.has_i32_0123() {
            self.i32_0123 = ::std::default::Default::default();
            self._bitfield.set(6, true);
        }
        &mut self.i32_0123
    }
    pub fn clear_i32_0x123(&mut self) {
        self._bitfield.set(7, false);
    }
    pub fn i32_0x123_mut<'this>(&'this mut self) -> &'this mut i32 {
        if !self.has_i32_0x123() {
            self.i32_0x123 = ::std::default::Default::default();
            self._bitfield.set(7, true);
        }
        &mut self.i32_0x123
    }
    pub fn clear_u32_default(&mut self) {
        self._bitfield.set(8, false);
    }
    pub fn u32_default_mut<'this>(&'this mut self) -> &'this mut u32 {
        if !self.has_u32_default() {
            self.u32_default = ::std::default::Default::default();
            self._bitfield.set(8, true);
        }
        &mut self.u32_default
    }
    pub fn clear_u32_0(&mut self) {
        self._bitfield.set(9, false);
    }
    pub fn u32_0_mut<'this>(&'this mut self) -> &'this mut u32 {
        if !self.has_u32_0() {
            self.u32_0 = ::std::default::Default::default();
            self._bitfield.set(9, true);
        }
        &mut self.u32_0
    }
    pub fn clear_u32_42(&mut self) {
        self._bitfield.set(10, false);
    }
    pub fn u32_42_mut<'this>(&'this mut self) -> &'this mut u32 {
        if !self.has_u32_42() {
            self.u32_42 = ::std::default::Default::default();
            self._bitfield.set(10, true);
        }
        &mut self.u32_42
    }
    pub fn clear_u32_4294967295(&mut self) {
        self._bitfield.set(11, false);
    }
    pub fn u32_4294967295_mut<'this>(&'this mut self) -> &'this mut u32 {
        if !self.has_u32_4294967295() {
            self.u32_4294967295 = ::std::default::Default::default();
            self._bitfield.set(11, true);
        }
        &mut self.u32_4294967295
    }
    pub fn clear_u32_0123(&mut self) {
        self._bitfield.set(12, false);
    }
    pub fn u32_0123_mut<'this>(&'this mut self) -> &'this mut u32 {
        if !self.has_u32_0123() {
            self.u32_0123 = ::std::default::Default::default();
            self._bitfield.set(12, true);
        }
        &mut self.u32_0123
    }
    pub fn clear_u32_0x123(&mut self) {
        self._bitfield.set(13, false);
    }
    pub fn u32_0x123_mut<'this>(&'this mut self) -> &'this mut u32 {
        if !self.has_u32_0x123() {
            self.u32_0x123 = ::std::default::Default::default();
            self._bitfield.set(13, true);
        }
        &mut self.u32_0x123
    }
    pub fn clear_i64_default(&mut self) {
        self._bitfield.set(14, false);
    }
    pub fn i64_default_mut<'this>(&'this mut self) -> &'this mut i64 {
        if !self.has_i64_default() {
            self.i64_default = ::std::default::Default::default();
            self._bitfield.set(14, true);
        }
        &mut self.i64_default
    }
    pub fn clear_i64_0(&mut self) {
        self._bitfield.set(15, false);
    }
    pub fn i64_0_mut<'this>(&'this mut self) -> &'this mut i64 {
        if !self.has_i64_0() {
            self.i64_0 = ::std::default::Default::default();
            self._bitfield.set(15, true);
        }
        &mut self.i64_0
    }
    pub fn clear_i64_42(&mut self) {
        self._bitfield.set(16, false);
    }
    pub fn i64_42_mut<'this>(&'this mut self) -> &'this mut i64 {
        if !self.has_i64_42() {
            self.i64_42 = ::std::default::Default::default();
            self._bitfield.set(16, true);
        }
        &mut self.i64_42
    }
    pub fn clear_i64_m42(&mut self) {
        self._bitfield.set(17, false);
    }
    pub fn i64_m42_mut<'this>(&'this mut self) -> &'this mut i64 {
        if !self.has_i64_m42() {
            self.i64_m42 = ::std::default::Default::default();
            self._bitfield.set(17, true);
        }
        &mut self.i64_m42
    }
    pub fn clear_i64_9223372036854775807(&mut self) {
        self._bitfield.set(18, false);
    }
    pub fn i64_9223372036854775807_mut<'this>(&'this mut self) -> &'this mut i64 {
        if !self.has_i64_9223372036854775807() {
            self.i64_9223372036854775807 = ::std::default::Default::default();
            self._bitfield.set(18, true);
        }
        &mut self.i64_9223372036854775807
    }
    pub fn clear_i64_m9223372036854775808(&mut self) {
        self._bitfield.set(19, false);
    }
    pub fn i64_m9223372036854775808_mut<'this>(&'this mut self) -> &'this mut i64 {
        if !self.has_i64_m9223372036854775808() {
            self.i64_m9223372036854775808 = ::std::default::Default::default();
            self._bitfield.set(19, true);
        }
        &mut self.i64_m9223372036854775808
    }
    pub fn clear_i64_0123(&mut self) {
        self._bitfield.set(20, false);
    }
    pub fn i64_0123_mut<'this>(&'this mut self) -> &'this mut i64 {
        if !self.has_i64_0123() {
            self.i64_0123 = ::std::default::Default::default();
            self._bitfield.set(20, true);
        }
        &mut self.i64_0123
    }
    pub fn clear_i64_0x123(&mut self) {
        self._bitfield.set(21, false);
    }
    pub fn i64_0x123_mut<'this>(&'this mut self) -> &'this mut i64 {
        if !self.has_i64_0x123() {
            self.i64_0x123 = ::std::default::Default::default();
            self._bitfield.set(21, true);
        }
        &mut self.i64_0x123
    }
    pub fn clear_u64_default(&mut self) {
        self._bitfield.set(22, false);
    }
    pub fn u64_default_mut<'this>(&'this mut self) -> &'this mut u64 {
        if !self.has_u64_default() {
            self.u64_default = ::std::default::Default::default();
            self._bitfield.set(22, true);
        }
        &mut self.u64_default
    }
    pub fn clear_u64_0(&mut self) {
        self._bitfield.set(23, false);
    }
    pub fn u64_0_mut<'this>(&'this mut self) -> &'this mut u64 {
        if !self.has_u64_0() {
            self.u64_0 = ::std::default::Default::default();
            self._bitfield.set(23, true);
        }
        &mut self.u64_0
    }
    pub fn clear_u64_42(&mut self) {
        self._bitfield.set(24, false);
    }
    pub fn u64_42_mut<'this>(&'this mut self) -> &'this mut u64 {
        if !self.has_u64_42() {
            self.u64_42 = ::std::default::Default::default();
            self._bitfield.set(24, true);
        }
        &mut self.u64_42
    }
    pub fn clear_u64_18446744073709551615(&mut self) {
        self._bitfield.set(25, false);
    }
    pub fn u64_18446744073709551615_mut<'this>(&'this mut self) -> &'this mut u64 {
        if !self.has_u64_18446744073709551615() {
            self.u64_18446744073709551615 = ::std::default::Default::default();
            self._bitfield.set(25, true);
        }
        &mut self.u64_18446744073709551615
    }
    pub fn clear_u64_0123(&mut self) {
        self._bitfield.set(26, false);
    }
    pub fn u64_0123_mut<'this>(&'this mut self) -> &'this mut u64 {
        if !self.has_u64_0123() {
            self.u64_0123 = ::std::default::Default::default();
            self._bitfield.set(26, true);
        }
        &mut self.u64_0123
    }
    pub fn clear_u64_0x123(&mut self) {
        self._bitfield.set(27, false);
    }
    pub fn u64_0x123_mut<'this>(&'this mut self) -> &'this mut u64 {
        if !self.has_u64_0x123() {
            self.u64_0x123 = ::std::default::Default::default();
            self._bitfield.set(27, true);
        }
        &mut self.u64_0x123
    }
    pub fn clear_f32_default(&mut self) {
        self._bitfield.set(28, false);
    }
    pub fn f32_default_mut<'this>(&'this mut self) -> &'this mut f32 {
        if !self.has_f32_default() {
            self.f32_default = ::std::default::Default::default();
            self._bitfield.set(28, true);
        }
        &mut self.f32_default
    }
    pub fn clear_f32_0(&mut self) {
        self._bitfield.set(29, false);
    }
    pub fn f32_0_mut<'this>(&'this mut self) -> &'this mut f32 {
        if !self.has_f32_0() {
            self.f32_0 = ::std::default::Default::default();
            self._bitfield.set(29, true);
        }
        &mut self.f32_0
    }
    pub fn clear_f32_m0(&mut self) {
        self._bitfield.set(30, false);
    }
    pub fn f32_m0_mut<'this>(&'this mut self) -> &'this mut f32 {
        if !self.has_f32_m0() {
            self.f32_m0 = ::std::default::Default::default();
            self._bitfield.set(30, true);
        }
        &mut self.f32_m0
    }
    pub fn clear_f32_0p(&mut self) {
        self._bitfield.set(31, false);
    }
    pub fn f32_0p_mut<'this>(&'this mut self) -> &'this mut f32 {
        if !self.has_f32_0p() {
            self.f32_0p = ::std::default::Default::default();
            self._bitfield.set(31, true);
        }
        &mut self.f32_0p
    }
    pub fn clear_f32_p0(&mut self) {
        self._bitfield.set(32, false);
    }
    pub fn f32_p0_mut<'this>(&'this mut self) -> &'this mut f32 {
        if !self.has_f32_p0() {
            self.f32_p0 = ::std::default::Default::default();
            self._bitfield.set(32, true);
        }
        &mut self.f32_p0
    }
    pub fn clear_f32_0p0(&mut self) {
        self._bitfield.set(33, false);
    }
    pub fn f32_0p0_mut<'this>(&'this mut self) -> &'this mut f32 {
        if !self.has_f32_0p0() {
            self.f32_0p0 = ::std::default::Default::default();
            self._bitfield.set(33, true);
        }
        &mut self.f32_0p0
    }
    pub fn clear_f32_42(&mut self) {
        self._bitfield.set(34, false);
    }
    pub fn f32_42_mut<'this>(&'this mut self) -> &'this mut f32 {
        if !self.has_f32_42() {
            self.f32_42 = ::std::default::Default::default();
            self._bitfield.set(34, true);
        }
        &mut self.f32_42
    }
    pub fn clear_f32_m42(&mut self) {
        self._bitfield.set(35, false);
    }
    pub fn f32_m42_mut<'this>(&'this mut self) -> &'this mut f32 {
        if !self.has_f32_m42() {
            self.f32_m42 = ::std::default::Default::default();
            self._bitfield.set(35, true);
        }
        &mut self.f32_m42
    }
    pub fn clear_f32_0p25(&mut self) {
        self._bitfield.set(36, false);
    }
    pub fn f32_0p25_mut<'this>(&'this mut self) -> &'this mut f32 {
        if !self.has_f32_0p25() {
            self.f32_0p25 = ::std::default::Default::default();
            self._bitfield.set(36, true);
        }
        &mut self.f32_0p25
    }
    pub fn clear_f32_1p5e2(&mut self) {
        self._bitfield.set(37, false);
    }
    pub fn f32_1p5e2_mut<'this>(&'this mut self) -> &'this mut f32 {
        if !self.has_f32_1p5e2() {
            self.f32_1p5e2 = ::std::default::Default::default();
            self._bitfield.set(37, true);
        }
        &mut self.f32_1p5e2
    }
    pub fn clear_f32_inf(&mut self) {
        self._bitfield.set(38, false);
    }
    pub fn f32_inf_mut<'this>(&'this mut self) -> &'this mut f32 {
        if !self.has_f32_inf() {
            self.f32_inf = ::std::default::Default::default();
            self._bitfield.set(38, true);
        }
        &mut self.f32_inf
    }
    pub fn clear_f32_minf(&mut self) {
        self._bitfield.set(39, false);
    }
    pub fn f32_minf_mut<'this>(&'this mut self) -> &'this mut f32 {
        if !self.has_f32_minf() {
            self.f32_minf = ::std::default::Default::default();
            self._bitfield.set(39, true);
        }
        &mut self.f32_minf
    }
    pub fn clear_f32_nan(&mut self) {
        self._bitfield.set(40, false);
    }
    pub fn f32_nan_mut<'this>(&'this mut self) -> &'this mut f32 {
        if !self.has_f32_nan() {
            self.f32_nan = ::std::default::Default::default();
            self._bitfield.set(40, true);
        }
        &mut self.f32_nan
    }
    pub fn clear_f32_mnan(&mut self) {
        self._bitfield.set(41, false);
    }
    pub fn f32_mnan_mut<'this>(&'this mut self) -> &'this mut f32 {
        if !self.has_f32_mnan() {
            self.f32_mnan = ::std::default::Default::default();
            self._bitfield.set(41, true);
        }
        &mut self.f32_mnan
    }
    pub fn clear_bool_default(&mut self) {
        self._bitfield.set(42, false);
    }
    pub fn bool_default_mut<'this>(&'this mut self) -> &'this mut bool {
        if !self.has_bool_default() {
            self.bool_default = ::std::default::Default::default();
            self._bitfield.set(42, true);
        }
        &mut self.bool_default
    }
    pub fn clear_bool_true(&mut self) {
        self._bitfield.set(43, false);
    }
    pub fn bool_true_mut<'this>(&'this mut self) -> &'this mut bool {
        if !self.has_bool_true() {
            self.bool_true = ::std::default::Default::default();
            self._bitfield.set(43, true);
        }
        &mut self.bool_true
    }
    pub fn clear_bool_false(&mut self) {
        self._bitfield.set(44, false);
    }
    pub fn bool_false_mut<'this>(&'this mut self) -> &'this mut bool {
        if !self.has_bool_false() {
            self.bool_false = ::std::default::Default::default();
            self._bitfield.set(44, true);
        }
        &mut self.bool_false
    }
    pub fn clear_string_default(&mut self) {
        self._bitfield.set(45, false);
    }
    pub fn string_default_mut<'this>(&'this mut self) -> ::puroro::internal::RefMutBumpString<'bump, 'this> {
        if !self.has_string_default() {
            self.string_default = ::std::default::Default::default();
            self._bitfield.set(45, true);
        }
        unsafe { self.string_default.as_mut_string_in(self._bump) }
    }
    pub fn clear_string_empty(&mut self) {
        self._bitfield.set(46, false);
    }
    pub fn string_empty_mut<'this>(&'this mut self) -> ::puroro::internal::RefMutBumpString<'bump, 'this> {
        if !self.has_string_empty() {
            self.string_empty = ::std::default::Default::default();
            self._bitfield.set(46, true);
        }
        unsafe { self.string_empty.as_mut_string_in(self._bump) }
    }
    pub fn clear_string_abc(&mut self) {
        self._bitfield.set(47, false);
    }
    pub fn string_abc_mut<'this>(&'this mut self) -> ::puroro::internal::RefMutBumpString<'bump, 'this> {
        if !self.has_string_abc() {
            self.string_abc = ::std::default::Default::default();
            self._bitfield.set(47, true);
        }
        unsafe { self.string_abc.as_mut_string_in(self._bump) }
    }
    pub fn clear_string_aiu(&mut self) {
        self._bitfield.set(48, false);
    }
    pub fn string_aiu_mut<'this>(&'this mut self) -> ::puroro::internal::RefMutBumpString<'bump, 'this> {
        if !self.has_string_aiu() {
            self.string_aiu = ::std::default::Default::default();
            self._bitfield.set(48, true);
        }
        unsafe { self.string_aiu.as_mut_string_in(self._bump) }
    }
    pub fn clear_string_backslash(&mut self) {
        self._bitfield.set(49, false);
    }
    pub fn string_backslash_mut<'this>(&'this mut self) -> ::puroro::internal::RefMutBumpString<'bump, 'this> {
        if !self.has_string_backslash() {
            self.string_backslash = ::std::default::Default::default();
            self._bitfield.set(49, true);
        }
        unsafe { self.string_backslash.as_mut_string_in(self._bump) }
    }
    pub fn clear_string_tab(&mut self) {
        self._bitfield.set(50, false);
    }
    pub fn string_tab_mut<'this>(&'this mut self) -> ::puroro::internal::RefMutBumpString<'bump, 'this> {
        if !self.has_string_tab() {
            self.string_tab = ::std::default::Default::default();
            self._bitfield.set(50, true);
        }
        unsafe { self.string_tab.as_mut_string_in(self._bump) }
    }
    pub fn clear_string_crlf(&mut self) {
        self._bitfield.set(51, false);
    }
    pub fn string_crlf_mut<'this>(&'this mut self) -> ::puroro::internal::RefMutBumpString<'bump, 'this> {
        if !self.has_string_crlf() {
            self.string_crlf = ::std::default::Default::default();
            self._bitfield.set(51, true);
        }
        unsafe { self.string_crlf.as_mut_string_in(self._bump) }
    }
    pub fn clear_bytes_default(&mut self) {
        self._bitfield.set(52, false);
    }
    pub fn bytes_default_mut<'this>(&'this mut self) -> ::puroro::internal::RefMutBumpVec<'bump, 'this, u8> {
        if !self.has_bytes_default() {
            self.bytes_default = ::std::default::Default::default();
            self._bitfield.set(52, true);
        }
        unsafe { self.bytes_default.as_mut_vec_in(self._bump) }
    }
    pub fn clear_bytes_empty(&mut self) {
        self._bitfield.set(53, false);
    }
    pub fn bytes_empty_mut<'this>(&'this mut self) -> ::puroro::internal::RefMutBumpVec<'bump, 'this, u8> {
        if !self.has_bytes_empty() {
            self.bytes_empty = ::std::default::Default::default();
            self._bitfield.set(53, true);
        }
        unsafe { self.bytes_empty.as_mut_vec_in(self._bump) }
    }
    pub fn clear_bytes_abc(&mut self) {
        self._bitfield.set(54, false);
    }
    pub fn bytes_abc_mut<'this>(&'this mut self) -> ::puroro::internal::RefMutBumpVec<'bump, 'this, u8> {
        if !self.has_bytes_abc() {
            self.bytes_abc = ::std::default::Default::default();
            self._bitfield.set(54, true);
        }
        unsafe { self.bytes_abc.as_mut_vec_in(self._bump) }
    }
    pub fn clear_bytes_aiu(&mut self) {
        self._bitfield.set(55, false);
    }
    pub fn bytes_aiu_mut<'this>(&'this mut self) -> ::puroro::internal::RefMutBumpVec<'bump, 'this, u8> {
        if !self.has_bytes_aiu() {
            self.bytes_aiu = ::std::default::Default::default();
            self._bitfield.set(55, true);
        }
        unsafe { self.bytes_aiu.as_mut_vec_in(self._bump) }
    }
    pub fn clear_bytes_backslash(&mut self) {
        self._bitfield.set(56, false);
    }
    pub fn bytes_backslash_mut<'this>(&'this mut self) -> ::puroro::internal::RefMutBumpVec<'bump, 'this, u8> {
        if !self.has_bytes_backslash() {
            self.bytes_backslash = ::std::default::Default::default();
            self._bitfield.set(56, true);
        }
        unsafe { self.bytes_backslash.as_mut_vec_in(self._bump) }
    }
    pub fn clear_bytes_tab(&mut self) {
        self._bitfield.set(57, false);
    }
    pub fn bytes_tab_mut<'this>(&'this mut self) -> ::puroro::internal::RefMutBumpVec<'bump, 'this, u8> {
        if !self.has_bytes_tab() {
            self.bytes_tab = ::std::default::Default::default();
            self._bitfield.set(57, true);
        }
        unsafe { self.bytes_tab.as_mut_vec_in(self._bump) }
    }
    pub fn clear_bytes_crlf(&mut self) {
        self._bitfield.set(58, false);
    }
    pub fn bytes_crlf_mut<'this>(&'this mut self) -> ::puroro::internal::RefMutBumpVec<'bump, 'this, u8> {
        if !self.has_bytes_crlf() {
            self.bytes_crlf = ::std::default::Default::default();
            self._bitfield.set(58, true);
        }
        unsafe { self.bytes_crlf.as_mut_vec_in(self._bump) }
    }
    pub fn clear_enum_default(&mut self) {
        self._bitfield.set(59, false);
    }
    pub fn enum_default_mut<'this>(&'this mut self) -> &'this mut self::_puroro_root::proto2_defaults::MyEnum {
        if !self.has_enum_default() {
            self.enum_default = ::std::default::Default::default();
            self._bitfield.set(59, true);
        }
        &mut self.enum_default
    }
    pub fn clear_enum_one(&mut self) {
        self._bitfield.set(60, false);
    }
    pub fn enum_one_mut<'this>(&'this mut self) -> &'this mut self::_puroro_root::proto2_defaults::MyEnum {
        if !self.has_enum_one() {
            self.enum_one = ::std::default::Default::default();
            self._bitfield.set(60, true);
        }
        &mut self.enum_one
    }
    pub fn clear_enum_fourty_two(&mut self) {
        self._bitfield.set(61, false);
    }
    pub fn enum_fourty_two_mut<'this>(&'this mut self) -> &'this mut self::_puroro_root::proto2_defaults::MyEnum {
        if !self.has_enum_fourty_two() {
            self.enum_fourty_two = ::std::default::Default::default();
            self._bitfield.set(61, true);
        }
        &mut self.enum_fourty_two
    }
}
impl<'bump> ::puroro::Message<super::_puroro_simple_impl::Msg> for MsgBumpalo<'bump> {}

impl<'bump> ::puroro::BumpaloMessage<'bump> for MsgBumpalo<'bump> {
    fn new_in(bump: &'bump ::puroro::bumpalo::Bump) -> Self {
        Self::new_in(bump)
    }
}

impl<'bump> ::puroro::internal::BumpDefault<'bump> for MsgBumpalo<'bump> {
    fn default_in(bump: &'bump ::puroro::bumpalo::Bump) -> Self {
        Self::new_in(bump)
    }
}

impl<'bump> super::_puroro_traits::MsgTrait for MsgBumpalo<'bump> {
fn i32_default_opt<'this>(&'this self) -> Option<i32> {
    <Self>::i32_default_opt(self)
}
fn i32_0_opt<'this>(&'this self) -> Option<i32> {
    <Self>::i32_0_opt(self)
}
fn i32_42_opt<'this>(&'this self) -> Option<i32> {
    <Self>::i32_42_opt(self)
}
fn i32_m42_opt<'this>(&'this self) -> Option<i32> {
    <Self>::i32_m42_opt(self)
}
fn i32_2147483647_opt<'this>(&'this self) -> Option<i32> {
    <Self>::i32_2147483647_opt(self)
}
fn i32_m2147483648_opt<'this>(&'this self) -> Option<i32> {
    <Self>::i32_m2147483648_opt(self)
}
fn i32_0123_opt<'this>(&'this self) -> Option<i32> {
    <Self>::i32_0123_opt(self)
}
fn i32_0x123_opt<'this>(&'this self) -> Option<i32> {
    <Self>::i32_0x123_opt(self)
}
fn u32_default_opt<'this>(&'this self) -> Option<u32> {
    <Self>::u32_default_opt(self)
}
fn u32_0_opt<'this>(&'this self) -> Option<u32> {
    <Self>::u32_0_opt(self)
}
fn u32_42_opt<'this>(&'this self) -> Option<u32> {
    <Self>::u32_42_opt(self)
}
fn u32_4294967295_opt<'this>(&'this self) -> Option<u32> {
    <Self>::u32_4294967295_opt(self)
}
fn u32_0123_opt<'this>(&'this self) -> Option<u32> {
    <Self>::u32_0123_opt(self)
}
fn u32_0x123_opt<'this>(&'this self) -> Option<u32> {
    <Self>::u32_0x123_opt(self)
}
fn i64_default_opt<'this>(&'this self) -> Option<i64> {
    <Self>::i64_default_opt(self)
}
fn i64_0_opt<'this>(&'this self) -> Option<i64> {
    <Self>::i64_0_opt(self)
}
fn i64_42_opt<'this>(&'this self) -> Option<i64> {
    <Self>::i64_42_opt(self)
}
fn i64_m42_opt<'this>(&'this self) -> Option<i64> {
    <Self>::i64_m42_opt(self)
}
fn i64_9223372036854775807_opt<'this>(&'this self) -> Option<i64> {
    <Self>::i64_9223372036854775807_opt(self)
}
fn i64_m9223372036854775808_opt<'this>(&'this self) -> Option<i64> {
    <Self>::i64_m9223372036854775808_opt(self)
}
fn i64_0123_opt<'this>(&'this self) -> Option<i64> {
    <Self>::i64_0123_opt(self)
}
fn i64_0x123_opt<'this>(&'this self) -> Option<i64> {
    <Self>::i64_0x123_opt(self)
}
fn u64_default_opt<'this>(&'this self) -> Option<u64> {
    <Self>::u64_default_opt(self)
}
fn u64_0_opt<'this>(&'this self) -> Option<u64> {
    <Self>::u64_0_opt(self)
}
fn u64_42_opt<'this>(&'this self) -> Option<u64> {
    <Self>::u64_42_opt(self)
}
fn u64_18446744073709551615_opt<'this>(&'this self) -> Option<u64> {
    <Self>::u64_18446744073709551615_opt(self)
}
fn u64_0123_opt<'this>(&'this self) -> Option<u64> {
    <Self>::u64_0123_opt(self)
}
fn u64_0x123_opt<'this>(&'this self) -> Option<u64> {
    <Self>::u64_0x123_opt(self)
}
fn f32_default_opt<'this>(&'this self) -> Option<f32> {
    <Self>::f32_default_opt(self)
}
fn f32_0_opt<'this>(&'this self) -> Option<f32> {
    <Self>::f32_0_opt(self)
}
fn f32_m0_opt<'this>(&'this self) -> Option<f32> {
    <Self>::f32_m0_opt(self)
}
fn f32_0p_opt<'this>(&'this self) -> Option<f32> {
    <Self>::f32_0p_opt(self)
}
fn f32_p0_opt<'this>(&'this self) -> Option<f32> {
    <Self>::f32_p0_opt(self)
}
fn f32_0p0_opt<'this>(&'this self) -> Option<f32> {
    <Self>::f32_0p0_opt(self)
}
fn f32_42_opt<'this>(&'this self) -> Option<f32> {
    <Self>::f32_42_opt(self)
}
fn f32_m42_opt<'this>(&'this self) -> Option<f32> {
    <Self>::f32_m42_opt(self)
}
fn f32_0p25_opt<'this>(&'this self) -> Option<f32> {
    <Self>::f32_0p25_opt(self)
}
fn f32_1p5e2_opt<'this>(&'this self) -> Option<f32> {
    <Self>::f32_1p5e2_opt(self)
}
fn f32_inf_opt<'this>(&'this self) -> Option<f32> {
    <Self>::f32_inf_opt(self)
}
fn f32_minf_opt<'this>(&'this self) -> Option<f32> {
    <Self>::f32_minf_opt(self)
}
fn f32_nan_opt<'this>(&'this self) -> Option<f32> {
    <Self>::f32_nan_opt(self)
}
fn f32_mnan_opt<'this>(&'this self) -> Option<f32> {
    <Self>::f32_mnan_opt(self)
}
fn bool_default_opt<'this>(&'this self) -> Option<bool> {
    <Self>::bool_default_opt(self)
}
fn bool_true_opt<'this>(&'this self) -> Option<bool> {
    <Self>::bool_true_opt(self)
}
fn bool_false_opt<'this>(&'this self) -> Option<bool> {
    <Self>::bool_false_opt(self)
}
fn string_default_opt<'this>(&'this self) -> Option<&'this str> {
    <Self>::string_default_opt(self)
}
fn string_empty_opt<'this>(&'this self) -> Option<&'this str> {
    <Self>::string_empty_opt(self)
}
fn string_abc_opt<'this>(&'this self) -> Option<&'this str> {
    <Self>::string_abc_opt(self)
}
fn string_aiu_opt<'this>(&'this self) -> Option<&'this str> {
    <Self>::string_aiu_opt(self)
}
fn string_backslash_opt<'this>(&'this self) -> Option<&'this str> {
    <Self>::string_backslash_opt(self)
}
fn string_tab_opt<'this>(&'this self) -> Option<&'this str> {
    <Self>::string_tab_opt(self)
}
fn string_crlf_opt<'this>(&'this self) -> Option<&'this str> {
    <Self>::string_crlf_opt(self)
}
fn bytes_default_opt<'this>(&'this self) -> Option<&'this [u8]> {
    <Self>::bytes_default_opt(self)
}
fn bytes_empty_opt<'this>(&'this self) -> Option<&'this [u8]> {
    <Self>::bytes_empty_opt(self)
}
fn bytes_abc_opt<'this>(&'this self) -> Option<&'this [u8]> {
    <Self>::bytes_abc_opt(self)
}
fn bytes_aiu_opt<'this>(&'this self) -> Option<&'this [u8]> {
    <Self>::bytes_aiu_opt(self)
}
fn bytes_backslash_opt<'this>(&'this self) -> Option<&'this [u8]> {
    <Self>::bytes_backslash_opt(self)
}
fn bytes_tab_opt<'this>(&'this self) -> Option<&'this [u8]> {
    <Self>::bytes_tab_opt(self)
}
fn bytes_crlf_opt<'this>(&'this self) -> Option<&'this [u8]> {
    <Self>::bytes_crlf_opt(self)
}
fn enum_default_opt<'this>(&'this self) -> Option<self::_puroro_root::proto2_defaults::MyEnum> {
    <Self>::enum_default_opt(self)
}
fn enum_one_opt<'this>(&'this self) -> Option<self::_puroro_root::proto2_defaults::MyEnum> {
    <Self>::enum_one_opt(self)
}
fn enum_fourty_two_opt<'this>(&'this self) -> Option<self::_puroro_root::proto2_defaults::MyEnum> {
    <Self>::enum_fourty_two_opt(self)
}
}

impl<'bump> ::puroro::internal::de::DeserMessageFromBytesIter for MsgBumpalo<'bump> {
    fn deser_field<'this, I>(
        &'this mut self,
        field_number: i32,
        data: ::puroro::internal::types::FieldData<&mut ::puroro::internal::de::from_iter::ScopedIter<I>>,
    ) -> ::puroro::Result<()>
    where
        I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>
    {
        use ::puroro::internal::impls::bumpalo::de::DeserFieldFromBytesIter;
        match field_number {
            1 => {
                self._bitfield.set(0, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Int32
                >::deser_field(&mut self.i32_default, data, self._bump)
            }
            2 => {
                self._bitfield.set(1, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Int32
                >::deser_field(&mut self.i32_0, data, self._bump)
            }
            3 => {
                self._bitfield.set(2, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Int32
                >::deser_field(&mut self.i32_42, data, self._bump)
            }
            4 => {
                self._bitfield.set(3, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Int32
                >::deser_field(&mut self.i32_m42, data, self._bump)
            }
            5 => {
                self._bitfield.set(4, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Int32
                >::deser_field(&mut self.i32_2147483647, data, self._bump)
            }
            6 => {
                self._bitfield.set(5, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Int32
                >::deser_field(&mut self.i32_m2147483648, data, self._bump)
            }
            7 => {
                self._bitfield.set(6, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Int32
                >::deser_field(&mut self.i32_0123, data, self._bump)
            }
            8 => {
                self._bitfield.set(7, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Int32
                >::deser_field(&mut self.i32_0x123, data, self._bump)
            }
            11 => {
                self._bitfield.set(8, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::UInt32
                >::deser_field(&mut self.u32_default, data, self._bump)
            }
            12 => {
                self._bitfield.set(9, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::UInt32
                >::deser_field(&mut self.u32_0, data, self._bump)
            }
            13 => {
                self._bitfield.set(10, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::UInt32
                >::deser_field(&mut self.u32_42, data, self._bump)
            }
            15 => {
                self._bitfield.set(11, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::UInt32
                >::deser_field(&mut self.u32_4294967295, data, self._bump)
            }
            17 => {
                self._bitfield.set(12, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::UInt32
                >::deser_field(&mut self.u32_0123, data, self._bump)
            }
            18 => {
                self._bitfield.set(13, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::UInt32
                >::deser_field(&mut self.u32_0x123, data, self._bump)
            }
            21 => {
                self._bitfield.set(14, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Int64
                >::deser_field(&mut self.i64_default, data, self._bump)
            }
            22 => {
                self._bitfield.set(15, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Int64
                >::deser_field(&mut self.i64_0, data, self._bump)
            }
            23 => {
                self._bitfield.set(16, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Int64
                >::deser_field(&mut self.i64_42, data, self._bump)
            }
            24 => {
                self._bitfield.set(17, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Int64
                >::deser_field(&mut self.i64_m42, data, self._bump)
            }
            25 => {
                self._bitfield.set(18, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Int64
                >::deser_field(&mut self.i64_9223372036854775807, data, self._bump)
            }
            26 => {
                self._bitfield.set(19, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Int64
                >::deser_field(&mut self.i64_m9223372036854775808, data, self._bump)
            }
            27 => {
                self._bitfield.set(20, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Int64
                >::deser_field(&mut self.i64_0123, data, self._bump)
            }
            28 => {
                self._bitfield.set(21, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Int64
                >::deser_field(&mut self.i64_0x123, data, self._bump)
            }
            31 => {
                self._bitfield.set(22, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::UInt64
                >::deser_field(&mut self.u64_default, data, self._bump)
            }
            32 => {
                self._bitfield.set(23, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::UInt64
                >::deser_field(&mut self.u64_0, data, self._bump)
            }
            33 => {
                self._bitfield.set(24, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::UInt64
                >::deser_field(&mut self.u64_42, data, self._bump)
            }
            35 => {
                self._bitfield.set(25, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::UInt64
                >::deser_field(&mut self.u64_18446744073709551615, data, self._bump)
            }
            37 => {
                self._bitfield.set(26, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::UInt64
                >::deser_field(&mut self.u64_0123, data, self._bump)
            }
            38 => {
                self._bitfield.set(27, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::UInt64
                >::deser_field(&mut self.u64_0x123, data, self._bump)
            }
            41 => {
                self._bitfield.set(28, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Float
                >::deser_field(&mut self.f32_default, data, self._bump)
            }
            42 => {
                self._bitfield.set(29, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Float
                >::deser_field(&mut self.f32_0, data, self._bump)
            }
            43 => {
                self._bitfield.set(30, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Float
                >::deser_field(&mut self.f32_m0, data, self._bump)
            }
            44 => {
                self._bitfield.set(31, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Float
                >::deser_field(&mut self.f32_0p, data, self._bump)
            }
            45 => {
                self._bitfield.set(32, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Float
                >::deser_field(&mut self.f32_p0, data, self._bump)
            }
            46 => {
                self._bitfield.set(33, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Float
                >::deser_field(&mut self.f32_0p0, data, self._bump)
            }
            47 => {
                self._bitfield.set(34, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Float
                >::deser_field(&mut self.f32_42, data, self._bump)
            }
            48 => {
                self._bitfield.set(35, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Float
                >::deser_field(&mut self.f32_m42, data, self._bump)
            }
            49 => {
                self._bitfield.set(36, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Float
                >::deser_field(&mut self.f32_0p25, data, self._bump)
            }
            50 => {
                self._bitfield.set(37, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Float
                >::deser_field(&mut self.f32_1p5e2, data, self._bump)
            }
            51 => {
                self._bitfield.set(38, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Float
                >::deser_field(&mut self.f32_inf, data, self._bump)
            }
            52 => {
                self._bitfield.set(39, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Float
                >::deser_field(&mut self.f32_minf, data, self._bump)
            }
            53 => {
                self._bitfield.set(40, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Float
                >::deser_field(&mut self.f32_nan, data, self._bump)
            }
            54 => {
                self._bitfield.set(41, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Float
                >::deser_field(&mut self.f32_mnan, data, self._bump)
            }
            61 => {
                self._bitfield.set(42, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Bool
                >::deser_field(&mut self.bool_default, data, self._bump)
            }
            62 => {
                self._bitfield.set(43, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Bool
                >::deser_field(&mut self.bool_true, data, self._bump)
            }
            63 => {
                self._bitfield.set(44, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Bool
                >::deser_field(&mut self.bool_false, data, self._bump)
            }
            71 => {
                self._bitfield.set(45, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::String
                >::deser_field(&mut self.string_default, data, self._bump)
            }
            72 => {
                self._bitfield.set(46, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::String
                >::deser_field(&mut self.string_empty, data, self._bump)
            }
            73 => {
                self._bitfield.set(47, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::String
                >::deser_field(&mut self.string_abc, data, self._bump)
            }
            74 => {
                self._bitfield.set(48, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::String
                >::deser_field(&mut self.string_aiu, data, self._bump)
            }
            75 => {
                self._bitfield.set(49, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::String
                >::deser_field(&mut self.string_backslash, data, self._bump)
            }
            76 => {
                self._bitfield.set(50, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::String
                >::deser_field(&mut self.string_tab, data, self._bump)
            }
            77 => {
                self._bitfield.set(51, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::String
                >::deser_field(&mut self.string_crlf, data, self._bump)
            }
            81 => {
                self._bitfield.set(52, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Bytes
                >::deser_field(&mut self.bytes_default, data, self._bump)
            }
            82 => {
                self._bitfield.set(53, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Bytes
                >::deser_field(&mut self.bytes_empty, data, self._bump)
            }
            83 => {
                self._bitfield.set(54, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Bytes
                >::deser_field(&mut self.bytes_abc, data, self._bump)
            }
            84 => {
                self._bitfield.set(55, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Bytes
                >::deser_field(&mut self.bytes_aiu, data, self._bump)
            }
            85 => {
                self._bitfield.set(56, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Bytes
                >::deser_field(&mut self.bytes_backslash, data, self._bump)
            }
            86 => {
                self._bitfield.set(57, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Bytes
                >::deser_field(&mut self.bytes_tab, data, self._bump)
            }
            87 => {
                self._bitfield.set(58, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Bytes
                >::deser_field(&mut self.bytes_crlf, data, self._bump)
            }
            91 => {
                self._bitfield.set(59, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>
                >::deser_field(&mut self.enum_default, data, self._bump)
            }
            92 => {
                self._bitfield.set(60, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>
                >::deser_field(&mut self.enum_one, data, self._bump)
            }
            93 => {
                self._bitfield.set(61, true);
                DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional, ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>
                >::deser_field(&mut self.enum_fourty_two, data, self._bump)
            }

            _ => unimplemented!("TODO: This case should be handled properly..."),
        }
    }
}

impl<'bump> ::puroro::internal::se::SerMessageToIoWrite for MsgBumpalo<'bump>
where
    Self: super::_puroro_traits::MsgTrait,
{
    fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
    where
        W: ::std::io::Write,
    {
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_default_opt(self),
            1,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_0_opt(self),
            2,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_42_opt(self),
            3,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_m42_opt(self),
            4,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_2147483647_opt(self),
            5,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_m2147483648_opt(self),
            6,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_0123_opt(self),
            7,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i32_0x123_opt(self),
            8,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_default_opt(self),
            11,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_0_opt(self),
            12,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_42_opt(self),
            13,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_4294967295_opt(self),
            15,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_0123_opt(self),
            17,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt32
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u32_0x123_opt(self),
            18,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_default_opt(self),
            21,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_0_opt(self),
            22,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_42_opt(self),
            23,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_m42_opt(self),
            24,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_9223372036854775807_opt(self),
            25,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_m9223372036854775808_opt(self),
            26,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_0123_opt(self),
            27,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Int64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::i64_0x123_opt(self),
            28,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_default_opt(self),
            31,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_0_opt(self),
            32,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_42_opt(self),
            33,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_18446744073709551615_opt(self),
            35,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_0123_opt(self),
            37,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::UInt64
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::u64_0x123_opt(self),
            38,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_default_opt(self),
            41,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_0_opt(self),
            42,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_m0_opt(self),
            43,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_0p_opt(self),
            44,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_p0_opt(self),
            45,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_0p0_opt(self),
            46,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_42_opt(self),
            47,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_m42_opt(self),
            48,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_0p25_opt(self),
            49,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_1p5e2_opt(self),
            50,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_inf_opt(self),
            51,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_minf_opt(self),
            52,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_nan_opt(self),
            53,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Float
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::f32_mnan_opt(self),
            54,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bool
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bool_default_opt(self),
            61,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bool
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bool_true_opt(self),
            62,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bool
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bool_false_opt(self),
            63,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_default_opt(self),
            71,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_empty_opt(self),
            72,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_abc_opt(self),
            73,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_aiu_opt(self),
            74,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_backslash_opt(self),
            75,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_tab_opt(self),
            76,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::String
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::string_crlf_opt(self),
            77,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_default_opt(self),
            81,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_empty_opt(self),
            82,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_abc_opt(self),
            83,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_aiu_opt(self),
            84,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_backslash_opt(self),
            85,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_tab_opt(self),
            86,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Bytes
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::bytes_crlf_opt(self),
            87,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::enum_default_opt(self),
            91,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::enum_one_opt(self),
            92,
            out
        )?;
        ::puroro::internal::se::SerFieldToIoWrite::<
            ::puroro::tags::Optional, ::puroro::tags::Enum2<self::_puroro_root::proto2_defaults::MyEnum>
        >::ser_field(
            <Self as super::_puroro_traits::MsgTrait>::enum_fourty_two_opt(self),
            93,
            out
        )?;
        ::std::result::Result::Ok(())
    }
}pub struct MsgBuilder<T>(T);

impl<T> MsgBuilder<T>
where
    T: MsgTrait
{

    pub fn append_i32_default<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField1<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField1 { i32_default: value}))
    }

    pub fn append_i32_0<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField2<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField2 { i32_0: value}))
    }

    pub fn append_i32_42<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField3<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField3 { i32_42: value}))
    }

    pub fn append_i32_m42<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField4<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField4 { i32_m42: value}))
    }

    pub fn append_i32_2147483647<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField5<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField5 { i32_2147483647: value}))
    }

    pub fn append_i32_m2147483648<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField6<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField6 { i32_m2147483648: value}))
    }

    pub fn append_i32_0123<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField7<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField7 { i32_0123: value}))
    }

    pub fn append_i32_0x123<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField8<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<i32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField8 { i32_0x123: value}))
    }

    pub fn append_u32_default<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField11<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField11 { u32_default: value}))
    }

    pub fn append_u32_0<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField12<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField12 { u32_0: value}))
    }

    pub fn append_u32_42<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField13<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField13 { u32_42: value}))
    }

    pub fn append_u32_4294967295<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField15<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField15 { u32_4294967295: value}))
    }

    pub fn append_u32_0123<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField17<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField17 { u32_0123: value}))
    }

    pub fn append_u32_0x123<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField18<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<u32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField18 { u32_0x123: value}))
    }

    pub fn append_i64_default<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField21<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField21 { i64_default: value}))
    }

    pub fn append_i64_0<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField22<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField22 { i64_0: value}))
    }

    pub fn append_i64_42<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField23<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField23 { i64_42: value}))
    }

    pub fn append_i64_m42<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField24<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField24 { i64_m42: value}))
    }

    pub fn append_i64_9223372036854775807<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField25<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField25 { i64_9223372036854775807: value}))
    }

    pub fn append_i64_m9223372036854775808<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField26<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField26 { i64_m9223372036854775808: value}))
    }

    pub fn append_i64_0123<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField27<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField27 { i64_0123: value}))
    }

    pub fn append_i64_0x123<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField28<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<i64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField28 { i64_0x123: value}))
    }

    pub fn append_u64_default<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField31<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField31 { u64_default: value}))
    }

    pub fn append_u64_0<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField32<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField32 { u64_0: value}))
    }

    pub fn append_u64_42<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField33<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField33 { u64_42: value}))
    }

    pub fn append_u64_18446744073709551615<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField35<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField35 { u64_18446744073709551615: value}))
    }

    pub fn append_u64_0123<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField37<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField37 { u64_0123: value}))
    }

    pub fn append_u64_0x123<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField38<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<u64>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField38 { u64_0x123: value}))
    }

    pub fn append_f32_default<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField41<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField41 { f32_default: value}))
    }

    pub fn append_f32_0<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField42<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField42 { f32_0: value}))
    }

    pub fn append_f32_m0<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField43<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField43 { f32_m0: value}))
    }

    pub fn append_f32_0p<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField44<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField44 { f32_0p: value}))
    }

    pub fn append_f32_p0<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField45<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField45 { f32_p0: value}))
    }

    pub fn append_f32_0p0<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField46<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField46 { f32_0p0: value}))
    }

    pub fn append_f32_42<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField47<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField47 { f32_42: value}))
    }

    pub fn append_f32_m42<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField48<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField48 { f32_m42: value}))
    }

    pub fn append_f32_0p25<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField49<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField49 { f32_0p25: value}))
    }

    pub fn append_f32_1p5e2<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField50<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField50 { f32_1p5e2: value}))
    }

    pub fn append_f32_inf<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField51<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField51 { f32_inf: value}))
    }

    pub fn append_f32_minf<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField52<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField52 { f32_minf: value}))
    }

    pub fn append_f32_nan<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField53<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField53 { f32_nan: value}))
    }

    pub fn append_f32_mnan<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField54<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<f32>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField54 { f32_mnan: value}))
    }

    pub fn append_bool_default<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField61<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField61 { bool_default: value}))
    }

    pub fn append_bool_true<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField62<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField62 { bool_true: value}))
    }

    pub fn append_bool_false<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField63<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<bool>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField63 { bool_false: value}))
    }

    pub fn append_string_default<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField71<ScalarType>)>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField71 { string_default: value}))
    }

    pub fn append_string_empty<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField72<ScalarType>)>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField72 { string_empty: value}))
    }

    pub fn append_string_abc<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField73<ScalarType>)>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField73 { string_abc: value}))
    }

    pub fn append_string_aiu<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField74<ScalarType>)>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField74 { string_aiu: value}))
    }

    pub fn append_string_backslash<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField75<ScalarType>)>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField75 { string_backslash: value}))
    }

    pub fn append_string_tab<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField76<ScalarType>)>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField76 { string_tab: value}))
    }

    pub fn append_string_crlf<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField77<ScalarType>)>
where

ScalarType:
    ::std::convert::AsRef<str>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField77 { string_crlf: value}))
    }

    pub fn append_bytes_default<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField81<ScalarType>)>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField81 { bytes_default: value}))
    }

    pub fn append_bytes_empty<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField82<ScalarType>)>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField82 { bytes_empty: value}))
    }

    pub fn append_bytes_abc<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField83<ScalarType>)>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField83 { bytes_abc: value}))
    }

    pub fn append_bytes_aiu<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField84<ScalarType>)>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField84 { bytes_aiu: value}))
    }

    pub fn append_bytes_backslash<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField85<ScalarType>)>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField85 { bytes_backslash: value}))
    }

    pub fn append_bytes_tab<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField86<ScalarType>)>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField86 { bytes_tab: value}))
    }

    pub fn append_bytes_crlf<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField87<ScalarType>)>
where

ScalarType:
    ::std::convert::AsRef<[u8]>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField87 { bytes_crlf: value}))
    }

    pub fn append_enum_default<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField91<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField91 { enum_default: value}))
    }

    pub fn append_enum_one<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField92<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField92 { enum_one: value}))
    }

    pub fn append_enum_fourty_two<ScalarType>(self, value: ScalarType)
        -> MsgBuilder<(T, MsgSingleField93<ScalarType>)>
where

ScalarType:
    ::std::convert::Into<self::_puroro_root::proto2_defaults::MyEnum>
    + ::std::clone::Clone + ::std::cmp::PartialEq + ::std::fmt::Debug,
    {
        MsgBuilder((self.0, MsgSingleField93 { enum_fourty_two: value}))
    }

    pub fn build(self) -> T {
        self.0
    }
}

impl MsgBuilder<()>
{
    pub fn new() -> Self { Self(()) }
}
}
pub use _puroro_traits::*;
pub mod _puroro_traits {
    mod _puroro_root {
        pub use super::super::_puroro_root::*;
    }
    
    pub trait MsgTrait {
        fn i32_default<'this>(&'this self) -> i32 {
            self.i32_default_opt().unwrap_or_else(::std::default::Default::default)
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
            self.u32_default_opt().unwrap_or_else(::std::default::Default::default)
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
            self.i64_default_opt().unwrap_or_else(::std::default::Default::default)
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
            self.i64_9223372036854775807_opt().unwrap_or(9223372036854775807)
        }
        fn has_i64_9223372036854775807<'this>(&'this self) -> bool {
            self.i64_9223372036854775807_opt().is_some()
        }
        fn i64_9223372036854775807_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            ::std::option::Option::None
        }
        fn i64_m9223372036854775808<'this>(&'this self) -> i64 {
            self.i64_m9223372036854775808_opt().unwrap_or(-9223372036854775808)
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
            self.u64_default_opt().unwrap_or_else(::std::default::Default::default)
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
            self.u64_18446744073709551615_opt().unwrap_or(18446744073709551615)
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
            self.f32_default_opt().unwrap_or_else(::std::default::Default::default)
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
            self.bool_default_opt().unwrap_or_else(::std::default::Default::default)
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
            self.string_default_opt().unwrap_or_else(::std::default::Default::default)
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
            self.bytes_default_opt().unwrap_or_else(::std::default::Default::default)
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
            self.bytes_aiu_opt().unwrap_or(b"\xe3\x81\x82\xe3\x81\x84\xe3\x81\x86")
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
            self.enum_default_opt().unwrap_or_else(::std::default::Default::default)
        }
        fn has_enum_default<'this>(&'this self) -> bool {
            self.enum_default_opt().is_some()
        }
        fn enum_default_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
            ::std::option::Option::None
        }
        fn enum_one<'this>(&'this self) -> self::_puroro_root::proto2_defaults::MyEnum {
            self.enum_one_opt().unwrap_or(self::_puroro_root::proto2_defaults::MyEnum::One)
        }
        fn has_enum_one<'this>(&'this self) -> bool {
            self.enum_one_opt().is_some()
        }
        fn enum_one_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
            ::std::option::Option::None
        }
        fn enum_fourty_two<'this>(&'this self) -> self::_puroro_root::proto2_defaults::MyEnum {
            self.enum_fourty_two_opt().unwrap_or(self::_puroro_root::proto2_defaults::MyEnum::FourtyTwo)
        }
        fn has_enum_fourty_two<'this>(&'this self) -> bool {
            self.enum_fourty_two_opt().is_some()
        }
        fn enum_fourty_two_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
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
            fn enum_default_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
                (**self).enum_default_opt()
            }
            fn enum_one_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
                (**self).enum_one_opt()
            }
            fn enum_fourty_two_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
                (**self).enum_fourty_two_opt()
            }
        };
    }
    
    impl<T> MsgTrait for &'_ T
    where
        T: MsgTrait
    {
        msg_delegate!(T);
    }
    
    impl<T> MsgTrait for &'_ mut T
    where
        T: MsgTrait
    {
        msg_delegate!(T);
    }
    
    impl<T> MsgTrait for ::std::boxed::Box<T>
    where
        T: MsgTrait
    {
        msg_delegate!(T);
    }
    
    impl<'bump, T> MsgTrait for ::puroro::bumpalo::boxed::Box<'bump, T>
    where
        T: MsgTrait
    {
        msg_delegate!(T);
    }
    
    impl<T> MsgTrait for ::puroro::BumpaloOwned<T>
    where
        T: MsgTrait
    {
        msg_delegate!(T);
    }impl MsgTrait for () {
    }impl<T, U> MsgTrait for (T, U)
    where
        T: MsgTrait,
        U: MsgTrait,
    {
        fn i32_default_opt<'this>(&'this self) -> Option<i32>
        {
            <U as MsgTrait>::i32_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i32_default_opt(&self.0))
        }
        fn i32_0_opt<'this>(&'this self) -> Option<i32>
        {
            <U as MsgTrait>::i32_0_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i32_0_opt(&self.0))
        }
        fn i32_42_opt<'this>(&'this self) -> Option<i32>
        {
            <U as MsgTrait>::i32_42_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i32_42_opt(&self.0))
        }
        fn i32_m42_opt<'this>(&'this self) -> Option<i32>
        {
            <U as MsgTrait>::i32_m42_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i32_m42_opt(&self.0))
        }
        fn i32_2147483647_opt<'this>(&'this self) -> Option<i32>
        {
            <U as MsgTrait>::i32_2147483647_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i32_2147483647_opt(&self.0))
        }
        fn i32_m2147483648_opt<'this>(&'this self) -> Option<i32>
        {
            <U as MsgTrait>::i32_m2147483648_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i32_m2147483648_opt(&self.0))
        }
        fn i32_0123_opt<'this>(&'this self) -> Option<i32>
        {
            <U as MsgTrait>::i32_0123_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i32_0123_opt(&self.0))
        }
        fn i32_0x123_opt<'this>(&'this self) -> Option<i32>
        {
            <U as MsgTrait>::i32_0x123_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i32_0x123_opt(&self.0))
        }
        fn u32_default_opt<'this>(&'this self) -> Option<u32>
        {
            <U as MsgTrait>::u32_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u32_default_opt(&self.0))
        }
        fn u32_0_opt<'this>(&'this self) -> Option<u32>
        {
            <U as MsgTrait>::u32_0_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u32_0_opt(&self.0))
        }
        fn u32_42_opt<'this>(&'this self) -> Option<u32>
        {
            <U as MsgTrait>::u32_42_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u32_42_opt(&self.0))
        }
        fn u32_4294967295_opt<'this>(&'this self) -> Option<u32>
        {
            <U as MsgTrait>::u32_4294967295_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u32_4294967295_opt(&self.0))
        }
        fn u32_0123_opt<'this>(&'this self) -> Option<u32>
        {
            <U as MsgTrait>::u32_0123_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u32_0123_opt(&self.0))
        }
        fn u32_0x123_opt<'this>(&'this self) -> Option<u32>
        {
            <U as MsgTrait>::u32_0x123_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u32_0x123_opt(&self.0))
        }
        fn i64_default_opt<'this>(&'this self) -> Option<i64>
        {
            <U as MsgTrait>::i64_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i64_default_opt(&self.0))
        }
        fn i64_0_opt<'this>(&'this self) -> Option<i64>
        {
            <U as MsgTrait>::i64_0_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i64_0_opt(&self.0))
        }
        fn i64_42_opt<'this>(&'this self) -> Option<i64>
        {
            <U as MsgTrait>::i64_42_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i64_42_opt(&self.0))
        }
        fn i64_m42_opt<'this>(&'this self) -> Option<i64>
        {
            <U as MsgTrait>::i64_m42_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i64_m42_opt(&self.0))
        }
        fn i64_9223372036854775807_opt<'this>(&'this self) -> Option<i64>
        {
            <U as MsgTrait>::i64_9223372036854775807_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i64_9223372036854775807_opt(&self.0))
        }
        fn i64_m9223372036854775808_opt<'this>(&'this self) -> Option<i64>
        {
            <U as MsgTrait>::i64_m9223372036854775808_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i64_m9223372036854775808_opt(&self.0))
        }
        fn i64_0123_opt<'this>(&'this self) -> Option<i64>
        {
            <U as MsgTrait>::i64_0123_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i64_0123_opt(&self.0))
        }
        fn i64_0x123_opt<'this>(&'this self) -> Option<i64>
        {
            <U as MsgTrait>::i64_0x123_opt(&self.1)
                .or_else(|| <T as MsgTrait>::i64_0x123_opt(&self.0))
        }
        fn u64_default_opt<'this>(&'this self) -> Option<u64>
        {
            <U as MsgTrait>::u64_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u64_default_opt(&self.0))
        }
        fn u64_0_opt<'this>(&'this self) -> Option<u64>
        {
            <U as MsgTrait>::u64_0_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u64_0_opt(&self.0))
        }
        fn u64_42_opt<'this>(&'this self) -> Option<u64>
        {
            <U as MsgTrait>::u64_42_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u64_42_opt(&self.0))
        }
        fn u64_18446744073709551615_opt<'this>(&'this self) -> Option<u64>
        {
            <U as MsgTrait>::u64_18446744073709551615_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u64_18446744073709551615_opt(&self.0))
        }
        fn u64_0123_opt<'this>(&'this self) -> Option<u64>
        {
            <U as MsgTrait>::u64_0123_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u64_0123_opt(&self.0))
        }
        fn u64_0x123_opt<'this>(&'this self) -> Option<u64>
        {
            <U as MsgTrait>::u64_0x123_opt(&self.1)
                .or_else(|| <T as MsgTrait>::u64_0x123_opt(&self.0))
        }
        fn f32_default_opt<'this>(&'this self) -> Option<f32>
        {
            <U as MsgTrait>::f32_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_default_opt(&self.0))
        }
        fn f32_0_opt<'this>(&'this self) -> Option<f32>
        {
            <U as MsgTrait>::f32_0_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_0_opt(&self.0))
        }
        fn f32_m0_opt<'this>(&'this self) -> Option<f32>
        {
            <U as MsgTrait>::f32_m0_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_m0_opt(&self.0))
        }
        fn f32_0p_opt<'this>(&'this self) -> Option<f32>
        {
            <U as MsgTrait>::f32_0p_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_0p_opt(&self.0))
        }
        fn f32_p0_opt<'this>(&'this self) -> Option<f32>
        {
            <U as MsgTrait>::f32_p0_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_p0_opt(&self.0))
        }
        fn f32_0p0_opt<'this>(&'this self) -> Option<f32>
        {
            <U as MsgTrait>::f32_0p0_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_0p0_opt(&self.0))
        }
        fn f32_42_opt<'this>(&'this self) -> Option<f32>
        {
            <U as MsgTrait>::f32_42_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_42_opt(&self.0))
        }
        fn f32_m42_opt<'this>(&'this self) -> Option<f32>
        {
            <U as MsgTrait>::f32_m42_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_m42_opt(&self.0))
        }
        fn f32_0p25_opt<'this>(&'this self) -> Option<f32>
        {
            <U as MsgTrait>::f32_0p25_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_0p25_opt(&self.0))
        }
        fn f32_1p5e2_opt<'this>(&'this self) -> Option<f32>
        {
            <U as MsgTrait>::f32_1p5e2_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_1p5e2_opt(&self.0))
        }
        fn f32_inf_opt<'this>(&'this self) -> Option<f32>
        {
            <U as MsgTrait>::f32_inf_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_inf_opt(&self.0))
        }
        fn f32_minf_opt<'this>(&'this self) -> Option<f32>
        {
            <U as MsgTrait>::f32_minf_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_minf_opt(&self.0))
        }
        fn f32_nan_opt<'this>(&'this self) -> Option<f32>
        {
            <U as MsgTrait>::f32_nan_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_nan_opt(&self.0))
        }
        fn f32_mnan_opt<'this>(&'this self) -> Option<f32>
        {
            <U as MsgTrait>::f32_mnan_opt(&self.1)
                .or_else(|| <T as MsgTrait>::f32_mnan_opt(&self.0))
        }
        fn bool_default_opt<'this>(&'this self) -> Option<bool>
        {
            <U as MsgTrait>::bool_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bool_default_opt(&self.0))
        }
        fn bool_true_opt<'this>(&'this self) -> Option<bool>
        {
            <U as MsgTrait>::bool_true_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bool_true_opt(&self.0))
        }
        fn bool_false_opt<'this>(&'this self) -> Option<bool>
        {
            <U as MsgTrait>::bool_false_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bool_false_opt(&self.0))
        }
        fn string_default_opt<'this>(&'this self) -> Option<&'this str>
        {
            <U as MsgTrait>::string_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::string_default_opt(&self.0))
        }
        fn string_empty_opt<'this>(&'this self) -> Option<&'this str>
        {
            <U as MsgTrait>::string_empty_opt(&self.1)
                .or_else(|| <T as MsgTrait>::string_empty_opt(&self.0))
        }
        fn string_abc_opt<'this>(&'this self) -> Option<&'this str>
        {
            <U as MsgTrait>::string_abc_opt(&self.1)
                .or_else(|| <T as MsgTrait>::string_abc_opt(&self.0))
        }
        fn string_aiu_opt<'this>(&'this self) -> Option<&'this str>
        {
            <U as MsgTrait>::string_aiu_opt(&self.1)
                .or_else(|| <T as MsgTrait>::string_aiu_opt(&self.0))
        }
        fn string_backslash_opt<'this>(&'this self) -> Option<&'this str>
        {
            <U as MsgTrait>::string_backslash_opt(&self.1)
                .or_else(|| <T as MsgTrait>::string_backslash_opt(&self.0))
        }
        fn string_tab_opt<'this>(&'this self) -> Option<&'this str>
        {
            <U as MsgTrait>::string_tab_opt(&self.1)
                .or_else(|| <T as MsgTrait>::string_tab_opt(&self.0))
        }
        fn string_crlf_opt<'this>(&'this self) -> Option<&'this str>
        {
            <U as MsgTrait>::string_crlf_opt(&self.1)
                .or_else(|| <T as MsgTrait>::string_crlf_opt(&self.0))
        }
        fn bytes_default_opt<'this>(&'this self) -> Option<&'this [u8]>
        {
            <U as MsgTrait>::bytes_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bytes_default_opt(&self.0))
        }
        fn bytes_empty_opt<'this>(&'this self) -> Option<&'this [u8]>
        {
            <U as MsgTrait>::bytes_empty_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bytes_empty_opt(&self.0))
        }
        fn bytes_abc_opt<'this>(&'this self) -> Option<&'this [u8]>
        {
            <U as MsgTrait>::bytes_abc_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bytes_abc_opt(&self.0))
        }
        fn bytes_aiu_opt<'this>(&'this self) -> Option<&'this [u8]>
        {
            <U as MsgTrait>::bytes_aiu_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bytes_aiu_opt(&self.0))
        }
        fn bytes_backslash_opt<'this>(&'this self) -> Option<&'this [u8]>
        {
            <U as MsgTrait>::bytes_backslash_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bytes_backslash_opt(&self.0))
        }
        fn bytes_tab_opt<'this>(&'this self) -> Option<&'this [u8]>
        {
            <U as MsgTrait>::bytes_tab_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bytes_tab_opt(&self.0))
        }
        fn bytes_crlf_opt<'this>(&'this self) -> Option<&'this [u8]>
        {
            <U as MsgTrait>::bytes_crlf_opt(&self.1)
                .or_else(|| <T as MsgTrait>::bytes_crlf_opt(&self.0))
        }
        fn enum_default_opt<'this>(&'this self) -> Option<self::_puroro_root::proto2_defaults::MyEnum>
        {
            <U as MsgTrait>::enum_default_opt(&self.1)
                .or_else(|| <T as MsgTrait>::enum_default_opt(&self.0))
        }
        fn enum_one_opt<'this>(&'this self) -> Option<self::_puroro_root::proto2_defaults::MyEnum>
        {
            <U as MsgTrait>::enum_one_opt(&self.1)
                .or_else(|| <T as MsgTrait>::enum_one_opt(&self.0))
        }
        fn enum_fourty_two_opt<'this>(&'this self) -> Option<self::_puroro_root::proto2_defaults::MyEnum>
        {
            <U as MsgTrait>::enum_fourty_two_opt(&self.1)
                .or_else(|| <T as MsgTrait>::enum_fourty_two_opt(&self.0))
        }
    }impl<T, U> MsgTrait for ::puroro::Either<T, U>
    where
        T: MsgTrait,
        U: MsgTrait,
    {
        fn i32_default_opt<'this>(&'this self) -> ::std::option::Option<i32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_default_opt(t),
                |u| <U as MsgTrait>::i32_default_opt(u),
            )
        }
        fn i32_0_opt<'this>(&'this self) -> ::std::option::Option<i32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_0_opt(t),
                |u| <U as MsgTrait>::i32_0_opt(u),
            )
        }
        fn i32_42_opt<'this>(&'this self) -> ::std::option::Option<i32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_42_opt(t),
                |u| <U as MsgTrait>::i32_42_opt(u),
            )
        }
        fn i32_m42_opt<'this>(&'this self) -> ::std::option::Option<i32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_m42_opt(t),
                |u| <U as MsgTrait>::i32_m42_opt(u),
            )
        }
        fn i32_2147483647_opt<'this>(&'this self) -> ::std::option::Option<i32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_2147483647_opt(t),
                |u| <U as MsgTrait>::i32_2147483647_opt(u),
            )
        }
        fn i32_m2147483648_opt<'this>(&'this self) -> ::std::option::Option<i32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_m2147483648_opt(t),
                |u| <U as MsgTrait>::i32_m2147483648_opt(u),
            )
        }
        fn i32_0123_opt<'this>(&'this self) -> ::std::option::Option<i32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_0123_opt(t),
                |u| <U as MsgTrait>::i32_0123_opt(u),
            )
        }
        fn i32_0x123_opt<'this>(&'this self) -> ::std::option::Option<i32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::i32_0x123_opt(t),
                |u| <U as MsgTrait>::i32_0x123_opt(u),
            )
        }
        fn u32_default_opt<'this>(&'this self) -> ::std::option::Option<u32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::u32_default_opt(t),
                |u| <U as MsgTrait>::u32_default_opt(u),
            )
        }
        fn u32_0_opt<'this>(&'this self) -> ::std::option::Option<u32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::u32_0_opt(t),
                |u| <U as MsgTrait>::u32_0_opt(u),
            )
        }
        fn u32_42_opt<'this>(&'this self) -> ::std::option::Option<u32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::u32_42_opt(t),
                |u| <U as MsgTrait>::u32_42_opt(u),
            )
        }
        fn u32_4294967295_opt<'this>(&'this self) -> ::std::option::Option<u32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::u32_4294967295_opt(t),
                |u| <U as MsgTrait>::u32_4294967295_opt(u),
            )
        }
        fn u32_0123_opt<'this>(&'this self) -> ::std::option::Option<u32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::u32_0123_opt(t),
                |u| <U as MsgTrait>::u32_0123_opt(u),
            )
        }
        fn u32_0x123_opt<'this>(&'this self) -> ::std::option::Option<u32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::u32_0x123_opt(t),
                |u| <U as MsgTrait>::u32_0x123_opt(u),
            )
        }
        fn i64_default_opt<'this>(&'this self) -> ::std::option::Option<i64>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_default_opt(t),
                |u| <U as MsgTrait>::i64_default_opt(u),
            )
        }
        fn i64_0_opt<'this>(&'this self) -> ::std::option::Option<i64>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_0_opt(t),
                |u| <U as MsgTrait>::i64_0_opt(u),
            )
        }
        fn i64_42_opt<'this>(&'this self) -> ::std::option::Option<i64>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_42_opt(t),
                |u| <U as MsgTrait>::i64_42_opt(u),
            )
        }
        fn i64_m42_opt<'this>(&'this self) -> ::std::option::Option<i64>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_m42_opt(t),
                |u| <U as MsgTrait>::i64_m42_opt(u),
            )
        }
        fn i64_9223372036854775807_opt<'this>(&'this self) -> ::std::option::Option<i64>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_9223372036854775807_opt(t),
                |u| <U as MsgTrait>::i64_9223372036854775807_opt(u),
            )
        }
        fn i64_m9223372036854775808_opt<'this>(&'this self) -> ::std::option::Option<i64>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_m9223372036854775808_opt(t),
                |u| <U as MsgTrait>::i64_m9223372036854775808_opt(u),
            )
        }
        fn i64_0123_opt<'this>(&'this self) -> ::std::option::Option<i64>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_0123_opt(t),
                |u| <U as MsgTrait>::i64_0123_opt(u),
            )
        }
        fn i64_0x123_opt<'this>(&'this self) -> ::std::option::Option<i64>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::i64_0x123_opt(t),
                |u| <U as MsgTrait>::i64_0x123_opt(u),
            )
        }
        fn u64_default_opt<'this>(&'this self) -> ::std::option::Option<u64>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::u64_default_opt(t),
                |u| <U as MsgTrait>::u64_default_opt(u),
            )
        }
        fn u64_0_opt<'this>(&'this self) -> ::std::option::Option<u64>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::u64_0_opt(t),
                |u| <U as MsgTrait>::u64_0_opt(u),
            )
        }
        fn u64_42_opt<'this>(&'this self) -> ::std::option::Option<u64>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::u64_42_opt(t),
                |u| <U as MsgTrait>::u64_42_opt(u),
            )
        }
        fn u64_18446744073709551615_opt<'this>(&'this self) -> ::std::option::Option<u64>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::u64_18446744073709551615_opt(t),
                |u| <U as MsgTrait>::u64_18446744073709551615_opt(u),
            )
        }
        fn u64_0123_opt<'this>(&'this self) -> ::std::option::Option<u64>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::u64_0123_opt(t),
                |u| <U as MsgTrait>::u64_0123_opt(u),
            )
        }
        fn u64_0x123_opt<'this>(&'this self) -> ::std::option::Option<u64>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::u64_0x123_opt(t),
                |u| <U as MsgTrait>::u64_0x123_opt(u),
            )
        }
        fn f32_default_opt<'this>(&'this self) -> ::std::option::Option<f32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_default_opt(t),
                |u| <U as MsgTrait>::f32_default_opt(u),
            )
        }
        fn f32_0_opt<'this>(&'this self) -> ::std::option::Option<f32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_0_opt(t),
                |u| <U as MsgTrait>::f32_0_opt(u),
            )
        }
        fn f32_m0_opt<'this>(&'this self) -> ::std::option::Option<f32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_m0_opt(t),
                |u| <U as MsgTrait>::f32_m0_opt(u),
            )
        }
        fn f32_0p_opt<'this>(&'this self) -> ::std::option::Option<f32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_0p_opt(t),
                |u| <U as MsgTrait>::f32_0p_opt(u),
            )
        }
        fn f32_p0_opt<'this>(&'this self) -> ::std::option::Option<f32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_p0_opt(t),
                |u| <U as MsgTrait>::f32_p0_opt(u),
            )
        }
        fn f32_0p0_opt<'this>(&'this self) -> ::std::option::Option<f32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_0p0_opt(t),
                |u| <U as MsgTrait>::f32_0p0_opt(u),
            )
        }
        fn f32_42_opt<'this>(&'this self) -> ::std::option::Option<f32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_42_opt(t),
                |u| <U as MsgTrait>::f32_42_opt(u),
            )
        }
        fn f32_m42_opt<'this>(&'this self) -> ::std::option::Option<f32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_m42_opt(t),
                |u| <U as MsgTrait>::f32_m42_opt(u),
            )
        }
        fn f32_0p25_opt<'this>(&'this self) -> ::std::option::Option<f32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_0p25_opt(t),
                |u| <U as MsgTrait>::f32_0p25_opt(u),
            )
        }
        fn f32_1p5e2_opt<'this>(&'this self) -> ::std::option::Option<f32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_1p5e2_opt(t),
                |u| <U as MsgTrait>::f32_1p5e2_opt(u),
            )
        }
        fn f32_inf_opt<'this>(&'this self) -> ::std::option::Option<f32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_inf_opt(t),
                |u| <U as MsgTrait>::f32_inf_opt(u),
            )
        }
        fn f32_minf_opt<'this>(&'this self) -> ::std::option::Option<f32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_minf_opt(t),
                |u| <U as MsgTrait>::f32_minf_opt(u),
            )
        }
        fn f32_nan_opt<'this>(&'this self) -> ::std::option::Option<f32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_nan_opt(t),
                |u| <U as MsgTrait>::f32_nan_opt(u),
            )
        }
        fn f32_mnan_opt<'this>(&'this self) -> ::std::option::Option<f32>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::f32_mnan_opt(t),
                |u| <U as MsgTrait>::f32_mnan_opt(u),
            )
        }
        fn bool_default_opt<'this>(&'this self) -> ::std::option::Option<bool>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::bool_default_opt(t),
                |u| <U as MsgTrait>::bool_default_opt(u),
            )
        }
        fn bool_true_opt<'this>(&'this self) -> ::std::option::Option<bool>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::bool_true_opt(t),
                |u| <U as MsgTrait>::bool_true_opt(u),
            )
        }
        fn bool_false_opt<'this>(&'this self) -> ::std::option::Option<bool>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::bool_false_opt(t),
                |u| <U as MsgTrait>::bool_false_opt(u),
            )
        }
        fn string_default_opt<'this>(&'this self) -> ::std::option::Option<&'this str>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::string_default_opt(t),
                |u| <U as MsgTrait>::string_default_opt(u),
            )
        }
        fn string_empty_opt<'this>(&'this self) -> ::std::option::Option<&'this str>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::string_empty_opt(t),
                |u| <U as MsgTrait>::string_empty_opt(u),
            )
        }
        fn string_abc_opt<'this>(&'this self) -> ::std::option::Option<&'this str>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::string_abc_opt(t),
                |u| <U as MsgTrait>::string_abc_opt(u),
            )
        }
        fn string_aiu_opt<'this>(&'this self) -> ::std::option::Option<&'this str>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::string_aiu_opt(t),
                |u| <U as MsgTrait>::string_aiu_opt(u),
            )
        }
        fn string_backslash_opt<'this>(&'this self) -> ::std::option::Option<&'this str>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::string_backslash_opt(t),
                |u| <U as MsgTrait>::string_backslash_opt(u),
            )
        }
        fn string_tab_opt<'this>(&'this self) -> ::std::option::Option<&'this str>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::string_tab_opt(t),
                |u| <U as MsgTrait>::string_tab_opt(u),
            )
        }
        fn string_crlf_opt<'this>(&'this self) -> ::std::option::Option<&'this str>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::string_crlf_opt(t),
                |u| <U as MsgTrait>::string_crlf_opt(u),
            )
        }
        fn bytes_default_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::bytes_default_opt(t),
                |u| <U as MsgTrait>::bytes_default_opt(u),
            )
        }
        fn bytes_empty_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::bytes_empty_opt(t),
                |u| <U as MsgTrait>::bytes_empty_opt(u),
            )
        }
        fn bytes_abc_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::bytes_abc_opt(t),
                |u| <U as MsgTrait>::bytes_abc_opt(u),
            )
        }
        fn bytes_aiu_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::bytes_aiu_opt(t),
                |u| <U as MsgTrait>::bytes_aiu_opt(u),
            )
        }
        fn bytes_backslash_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::bytes_backslash_opt(t),
                |u| <U as MsgTrait>::bytes_backslash_opt(u),
            )
        }
        fn bytes_tab_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::bytes_tab_opt(t),
                |u| <U as MsgTrait>::bytes_tab_opt(u),
            )
        }
        fn bytes_crlf_opt<'this>(&'this self) -> ::std::option::Option<&'this [u8]>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::bytes_crlf_opt(t),
                |u| <U as MsgTrait>::bytes_crlf_opt(u),
            )
        }
        fn enum_default_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::enum_default_opt(t),
                |u| <U as MsgTrait>::enum_default_opt(u),
            )
        }
        fn enum_one_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::enum_one_opt(t),
                |u| <U as MsgTrait>::enum_one_opt(u),
            )
        }
        fn enum_fourty_two_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum>
        {
            self.as_ref().either(
                |t| <T as MsgTrait>::enum_fourty_two_opt(t),
                |u| <U as MsgTrait>::enum_fourty_two_opt(u),
            )
        }
    }impl<T> MsgTrait for ::std::option::Option<T>
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
            self.as_ref().and_then(|msg| msg.i64_9223372036854775807_opt())
        }
        fn i64_m9223372036854775808_opt<'this>(&'this self) -> ::std::option::Option<i64> {
            self.as_ref().and_then(|msg| msg.i64_m9223372036854775808_opt())
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
            self.as_ref().and_then(|msg| msg.u64_18446744073709551615_opt())
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
        fn enum_default_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
            self.as_ref().and_then(|msg| msg.enum_default_opt())
        }
        fn enum_one_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
            self.as_ref().and_then(|msg| msg.enum_one_opt())
        }
        fn enum_fourty_two_opt<'this>(&'this self) -> ::std::option::Option<self::_puroro_root::proto2_defaults::MyEnum> {
            self.as_ref().and_then(|msg| msg.enum_fourty_two_opt())
        }
    }
}
#[derive(::std::fmt::Debug, ::std::clone::Clone, ::std::marker::Copy, ::std::cmp::PartialEq)]
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

impl<'bump> ::puroro::internal::BumpDefault<'bump> for MyEnum {
    fn default_in(_: &'bump ::puroro::bumpalo::Bump) -> Self {
        ::std::default::Default::default()
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