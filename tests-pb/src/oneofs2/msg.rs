// A generated source code by puroro library
// package .oneofs2.Msg

pub mod _puroro_root {
    pub use super::super::_puroro_root::*;
}

pub mod _puroro {
    pub use ::puroro::*;
}

pub union GroupOne {
    _none: (),
    g1_int32: ::std::mem::ManuallyDrop<
        self::_puroro::internal::oneof_field_type::NumericalField<i32, self::_puroro::tags::Int32>,
    >,
    g1_string: ::std::mem::ManuallyDrop<self::_puroro::internal::oneof_field_type::StringField>,
}
#[repr(u32)]
#[derive(Debug, Clone)]
pub enum GroupOneCase {
    G1Int32,
    G1String,
}
#[repr(u32)]
#[derive(Debug, Clone)]
pub enum GroupOneCaseRef<'a> {
    G1Int32(i32),
    G1String(&'a str),
}

impl GroupOne {
    pub(crate) fn g1_int32_opt<B: self::_puroro::bitvec::BitSlice>(
        &self,
        bits: &B,
    ) -> ::std::option::Option<i32> {
        use self::_puroro::internal::oneof_field_type::OneofFieldType;
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::option::Option::{None, Some};

        let case_opt = self::GroupOneCase::from_bitslice(bits);
        if let Some(self::GroupOneCase::G1Int32) = case_opt {
            let item = unsafe { &self.g1_int32 };
            Some(item.get_field())
        } else {
            None
        }
    }
    pub(crate) fn g1_string_opt<B: self::_puroro::bitvec::BitSlice>(
        &self,
        bits: &B,
    ) -> ::std::option::Option<&str> {
        use self::_puroro::internal::oneof_field_type::OneofFieldType;
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::option::Option::{None, Some};

        let case_opt = self::GroupOneCase::from_bitslice(bits);
        if let Some(self::GroupOneCase::G1String) = case_opt {
            let item = unsafe { &self.g1_string };
            Some(item.get_field())
        } else {
            None
        }
    }
}

impl self::_puroro::internal::oneof_type::OneofUnion for GroupOne {
    type CaseRef<'a> = self::GroupOneCaseRef<'a>
        where Self: 'a;

    fn case_ref<B: self::_puroro::bitvec::BitSlice>(
        &self,
        bits: &B,
    ) -> ::std::option::Option<Self::CaseRef<'_>> {
        use self::_puroro::internal::oneof_type::{OneofCase, OneofCaseRef};
        let case_opt = <_puroro_root::oneofs2::msg::GroupOneCase as OneofCase>::from_bitslice(bits);
        case_opt.map(|case| OneofCaseRef::from_union_and_case(self, case))
    }

    fn clear<B: self::_puroro::bitvec::BitSlice>(&mut self, bits: &mut B) {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::mem::ManuallyDrop;
        #[allow(unused)]
        use ::std::option::Option::Some;

        match self::GroupOneCase::from_bitslice(bits) {
            Some(self::GroupOneCase::G1Int32) => {
                unsafe { ManuallyDrop::take(&mut self.g1_int32) };
            }
            Some(self::GroupOneCase::G1String) => {
                unsafe { ManuallyDrop::take(&mut self.g1_string) };
            }
            _ => (),
        }
        bits.set_range(0..2, 2);
    }

    fn clone<B: self::_puroro::bitvec::BitSlice>(&self, bits: &B) -> Self {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::clone::Clone;
        #[allow(unused)]
        use ::std::option::Option::Some;

        match self::GroupOneCase::from_bitslice(bits) {
            Some(GroupOneCase::G1Int32) => Self {
                g1_int32: Clone::clone(unsafe { &self.g1_int32 }),
            },
            Some(GroupOneCase::G1String) => Self {
                g1_string: Clone::clone(unsafe { &self.g1_string }),
            },
            _ => Self { _none: () },
        }
    }
}

impl ::std::default::Default for GroupOne {
    fn default() -> Self {
        Self { _none: () }
    }
}

impl self::_puroro::internal::oneof_type::OneofCase for GroupOneCase {
    const BITFIELD_BEGIN: usize = 0;
    const BITFIELD_END: usize = 2;
    fn from_u32(x: u32) -> Option<Self> {
        #[allow(unused)]
        use ::std::option::Option::{None, Some};
        match x {
            0 => Some(self::GroupOneCase::G1Int32),
            1 => Some(self::GroupOneCase::G1String),
            _ => None,
        }
    }
}

impl<'a> self::_puroro::internal::oneof_type::OneofCaseRef<'a> for GroupOneCaseRef<'a> {
    type Case = self::GroupOneCase;
    type Union = self::GroupOne;
    fn from_union_and_case(u: &'a Self::Union, case: Self::Case) -> Self {
        use self::_puroro::internal::oneof_field_type::OneofFieldType;
        match case {
            self::GroupOneCase::G1Int32 => {
                self::GroupOneCaseRef::G1Int32(unsafe { &u.g1_int32 }.get_field())
            }
            self::GroupOneCase::G1String => {
                self::GroupOneCaseRef::G1String(unsafe { &u.g1_string }.get_field())
            }
        }
    }
}

pub union GroupTwo {
    _none: (),
    g2_f32: ::std::mem::ManuallyDrop<
        self::_puroro::internal::oneof_field_type::NumericalField<f32, self::_puroro::tags::Float>,
    >,
    g2_string: ::std::mem::ManuallyDrop<self::_puroro::internal::oneof_field_type::StringField>,
    g2_submsg: ::std::mem::ManuallyDrop<
        self::_puroro::internal::oneof_field_type::HeapMessageField<_puroro_root::oneofs2::Submsg>,
    >,
}
#[repr(u32)]
#[derive(Debug, Clone)]
pub enum GroupTwoCase {
    G2F32,
    G2String,
    G2Submsg,
}
#[repr(u32)]
#[derive(Debug, Clone)]
pub enum GroupTwoCaseRef<'a> {
    G2F32(f32),
    G2String(&'a str),
    G2Submsg(&'a _puroro_root::oneofs2::Submsg),
}

impl GroupTwo {
    pub(crate) fn g2_f32_opt<B: self::_puroro::bitvec::BitSlice>(
        &self,
        bits: &B,
    ) -> ::std::option::Option<f32> {
        use self::_puroro::internal::oneof_field_type::OneofFieldType;
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::option::Option::{None, Some};

        let case_opt = self::GroupTwoCase::from_bitslice(bits);
        if let Some(self::GroupTwoCase::G2F32) = case_opt {
            let item = unsafe { &self.g2_f32 };
            Some(item.get_field())
        } else {
            None
        }
    }
    pub(crate) fn g2_string_opt<B: self::_puroro::bitvec::BitSlice>(
        &self,
        bits: &B,
    ) -> ::std::option::Option<&str> {
        use self::_puroro::internal::oneof_field_type::OneofFieldType;
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::option::Option::{None, Some};

        let case_opt = self::GroupTwoCase::from_bitslice(bits);
        if let Some(self::GroupTwoCase::G2String) = case_opt {
            let item = unsafe { &self.g2_string };
            Some(item.get_field())
        } else {
            None
        }
    }
    pub(crate) fn g2_submsg_opt<B: self::_puroro::bitvec::BitSlice>(
        &self,
        bits: &B,
    ) -> ::std::option::Option<&_puroro_root::oneofs2::Submsg> {
        use self::_puroro::internal::oneof_field_type::OneofFieldType;
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::option::Option::{None, Some};

        let case_opt = self::GroupTwoCase::from_bitslice(bits);
        if let Some(self::GroupTwoCase::G2Submsg) = case_opt {
            let item = unsafe { &self.g2_submsg };
            Some(item.get_field())
        } else {
            None
        }
    }
}

impl self::_puroro::internal::oneof_type::OneofUnion for GroupTwo {
    type CaseRef<'a> = self::GroupTwoCaseRef<'a>
        where Self: 'a;

    fn case_ref<B: self::_puroro::bitvec::BitSlice>(
        &self,
        bits: &B,
    ) -> ::std::option::Option<Self::CaseRef<'_>> {
        use self::_puroro::internal::oneof_type::{OneofCase, OneofCaseRef};
        let case_opt = <_puroro_root::oneofs2::msg::GroupTwoCase as OneofCase>::from_bitslice(bits);
        case_opt.map(|case| OneofCaseRef::from_union_and_case(self, case))
    }

    fn clear<B: self::_puroro::bitvec::BitSlice>(&mut self, bits: &mut B) {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::mem::ManuallyDrop;
        #[allow(unused)]
        use ::std::option::Option::Some;

        match self::GroupTwoCase::from_bitslice(bits) {
            Some(self::GroupTwoCase::G2F32) => {
                unsafe { ManuallyDrop::take(&mut self.g2_f32) };
            }
            Some(self::GroupTwoCase::G2String) => {
                unsafe { ManuallyDrop::take(&mut self.g2_string) };
            }
            Some(self::GroupTwoCase::G2Submsg) => {
                unsafe { ManuallyDrop::take(&mut self.g2_submsg) };
            }
            _ => (),
        }
        bits.set_range(2..4, 3);
    }

    fn clone<B: self::_puroro::bitvec::BitSlice>(&self, bits: &B) -> Self {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::clone::Clone;
        #[allow(unused)]
        use ::std::option::Option::Some;

        match self::GroupTwoCase::from_bitslice(bits) {
            Some(GroupTwoCase::G2F32) => Self {
                g2_f32: Clone::clone(unsafe { &self.g2_f32 }),
            },
            Some(GroupTwoCase::G2String) => Self {
                g2_string: Clone::clone(unsafe { &self.g2_string }),
            },
            Some(GroupTwoCase::G2Submsg) => Self {
                g2_submsg: Clone::clone(unsafe { &self.g2_submsg }),
            },
            _ => Self { _none: () },
        }
    }
}

impl ::std::default::Default for GroupTwo {
    fn default() -> Self {
        Self { _none: () }
    }
}

impl self::_puroro::internal::oneof_type::OneofCase for GroupTwoCase {
    const BITFIELD_BEGIN: usize = 2;
    const BITFIELD_END: usize = 4;
    fn from_u32(x: u32) -> Option<Self> {
        #[allow(unused)]
        use ::std::option::Option::{None, Some};
        match x {
            0 => Some(self::GroupTwoCase::G2F32),
            1 => Some(self::GroupTwoCase::G2String),
            2 => Some(self::GroupTwoCase::G2Submsg),
            _ => None,
        }
    }
}

impl<'a> self::_puroro::internal::oneof_type::OneofCaseRef<'a> for GroupTwoCaseRef<'a> {
    type Case = self::GroupTwoCase;
    type Union = self::GroupTwo;
    fn from_union_and_case(u: &'a Self::Union, case: Self::Case) -> Self {
        use self::_puroro::internal::oneof_field_type::OneofFieldType;
        match case {
            self::GroupTwoCase::G2F32 => {
                self::GroupTwoCaseRef::G2F32(unsafe { &u.g2_f32 }.get_field())
            }
            self::GroupTwoCase::G2String => {
                self::GroupTwoCaseRef::G2String(unsafe { &u.g2_string }.get_field())
            }
            self::GroupTwoCase::G2Submsg => {
                self::GroupTwoCaseRef::G2Submsg(unsafe { &u.g2_submsg }.get_field())
            }
        }
    }
}

pub union GroupThree {
    _none: (),
    g3_int32: ::std::mem::ManuallyDrop<
        self::_puroro::internal::oneof_field_type::NumericalField<i32, self::_puroro::tags::Int32>,
    >,
}
#[repr(u32)]
#[derive(Debug, Clone)]
pub enum GroupThreeCase {
    G3Int32,
}
#[repr(u32)]
#[derive(Debug, Clone)]
pub enum GroupThreeCaseRef {
    G3Int32(i32),
}

impl GroupThree {
    pub(crate) fn g3_int32_opt<B: self::_puroro::bitvec::BitSlice>(
        &self,
        bits: &B,
    ) -> ::std::option::Option<i32> {
        use self::_puroro::internal::oneof_field_type::OneofFieldType;
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::option::Option::{None, Some};

        let case_opt = self::GroupThreeCase::from_bitslice(bits);
        if let Some(self::GroupThreeCase::G3Int32) = case_opt {
            let item = unsafe { &self.g3_int32 };
            Some(item.get_field())
        } else {
            None
        }
    }
}

impl self::_puroro::internal::oneof_type::OneofUnion for GroupThree {
    type CaseRef<'a> = self::GroupThreeCaseRef
        where Self: 'a;

    fn case_ref<B: self::_puroro::bitvec::BitSlice>(
        &self,
        bits: &B,
    ) -> ::std::option::Option<Self::CaseRef<'_>> {
        use self::_puroro::internal::oneof_type::{OneofCase, OneofCaseRef};
        let case_opt =
            <_puroro_root::oneofs2::msg::GroupThreeCase as OneofCase>::from_bitslice(bits);
        case_opt.map(|case| OneofCaseRef::from_union_and_case(self, case))
    }

    fn clear<B: self::_puroro::bitvec::BitSlice>(&mut self, bits: &mut B) {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::mem::ManuallyDrop;
        #[allow(unused)]
        use ::std::option::Option::Some;

        match self::GroupThreeCase::from_bitslice(bits) {
            Some(self::GroupThreeCase::G3Int32) => {
                unsafe { ManuallyDrop::take(&mut self.g3_int32) };
            }
            _ => (),
        }
        bits.set_range(4..5, 1);
    }

    fn clone<B: self::_puroro::bitvec::BitSlice>(&self, bits: &B) -> Self {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::clone::Clone;
        #[allow(unused)]
        use ::std::option::Option::Some;

        match self::GroupThreeCase::from_bitslice(bits) {
            Some(GroupThreeCase::G3Int32) => Self {
                g3_int32: Clone::clone(unsafe { &self.g3_int32 }),
            },
            _ => Self { _none: () },
        }
    }
}

impl ::std::default::Default for GroupThree {
    fn default() -> Self {
        Self { _none: () }
    }
}

impl self::_puroro::internal::oneof_type::OneofCase for GroupThreeCase {
    const BITFIELD_BEGIN: usize = 4;
    const BITFIELD_END: usize = 5;
    fn from_u32(x: u32) -> Option<Self> {
        #[allow(unused)]
        use ::std::option::Option::{None, Some};
        match x {
            0 => Some(self::GroupThreeCase::G3Int32),
            _ => None,
        }
    }
}

impl<'a> self::_puroro::internal::oneof_type::OneofCaseRef<'a> for GroupThreeCaseRef {
    type Case = self::GroupThreeCase;
    type Union = self::GroupThree;
    fn from_union_and_case(u: &'a Self::Union, case: Self::Case) -> Self {
        use self::_puroro::internal::oneof_field_type::OneofFieldType;
        match case {
            self::GroupThreeCase::G3Int32 => {
                self::GroupThreeCaseRef::G3Int32(unsafe { &u.g3_int32 }.get_field())
            }
        }
    }
}
