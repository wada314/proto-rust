// A generated source code by puroro library
// package oneofs3

pub mod _puroro_root {
    pub use super::super::_puroro_root::*;
}

pub mod _puroro {
    pub use ::puroro::*;
}

#[derive(Default)]
pub struct Msg {
    // oneof GroupOne
    group_one: _puroro_root::oneofs3::msg::GroupOne,
    // oneof GroupTwo
    group_two: _puroro_root::oneofs3::msg::GroupTwo,
    // oneof GroupThree
    group_three: _puroro_root::oneofs3::msg::GroupThree,

    _bitfield: self::_puroro::bitvec::BitArray<1>,
}

impl Msg {
    pub fn group_one(
        &self,
    ) -> ::std::option::Option<_puroro_root::oneofs3::msg::GroupOneCaseRef<'_>> {
        use self::_puroro::internal::oneof_type::OneofUnion;
        <_puroro_root::oneofs3::msg::GroupOne as OneofUnion>::case_ref(
            &self.group_one,
            &self._bitfield,
        )
    }

    pub fn clear_group_one(&mut self) {
        use self::_puroro::internal::oneof_type::OneofUnion;
        <_puroro_root::oneofs3::msg::GroupOne as OneofUnion>::clear(
            &mut self.group_one,
            &mut self._bitfield,
        );
    }
    pub fn g1_int32(&self) -> i32 {
        self.group_one.g1_int32(&self._bitfield)
    }

    pub fn g1_int32_opt(&self) -> ::std::option::Option<i32> {
        self.group_one.g1_int32_opt(&self._bitfield)
    }

    pub fn g1_int32_mut(&mut self) -> &mut i32 {
        self.group_one.g1_int32_mut(&mut self._bitfield)
    }

    pub fn has_g1_int32(&self) -> bool {
        self.g1_int32_opt().is_some()
    }

    pub fn clear_g1_int32(&mut self) {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::option::Option::Some;
        match <_puroro_root::oneofs3::msg::GroupOneCase as OneofCase>::from_bitslice(
            &self._bitfield,
        ) {
            Some(_puroro_root::oneofs3::msg::GroupOneCase::G1Int32) => {
                self.clear_group_one();
            }
            _ => (),
        }
    }
    pub fn g1_string(&self) -> &str {
        self.group_one.g1_string(&self._bitfield)
    }

    pub fn g1_string_opt(&self) -> ::std::option::Option<&str> {
        self.group_one.g1_string_opt(&self._bitfield)
    }

    pub fn g1_string_mut(&mut self) -> &mut ::std::string::String {
        self.group_one.g1_string_mut(&mut self._bitfield)
    }

    pub fn has_g1_string(&self) -> bool {
        self.g1_string_opt().is_some()
    }

    pub fn clear_g1_string(&mut self) {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::option::Option::Some;
        match <_puroro_root::oneofs3::msg::GroupOneCase as OneofCase>::from_bitslice(
            &self._bitfield,
        ) {
            Some(_puroro_root::oneofs3::msg::GroupOneCase::G1String) => {
                self.clear_group_one();
            }
            _ => (),
        }
    }
    pub fn group_two(
        &self,
    ) -> ::std::option::Option<_puroro_root::oneofs3::msg::GroupTwoCaseRef<'_>> {
        use self::_puroro::internal::oneof_type::OneofUnion;
        <_puroro_root::oneofs3::msg::GroupTwo as OneofUnion>::case_ref(
            &self.group_two,
            &self._bitfield,
        )
    }

    pub fn clear_group_two(&mut self) {
        use self::_puroro::internal::oneof_type::OneofUnion;
        <_puroro_root::oneofs3::msg::GroupTwo as OneofUnion>::clear(
            &mut self.group_two,
            &mut self._bitfield,
        );
    }
    pub fn g2_f32(&self) -> f32 {
        self.group_two.g2_f32(&self._bitfield)
    }

    pub fn g2_f32_opt(&self) -> ::std::option::Option<f32> {
        self.group_two.g2_f32_opt(&self._bitfield)
    }

    pub fn g2_f32_mut(&mut self) -> &mut f32 {
        self.group_two.g2_f32_mut(&mut self._bitfield)
    }

    pub fn has_g2_f32(&self) -> bool {
        self.g2_f32_opt().is_some()
    }

    pub fn clear_g2_f32(&mut self) {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::option::Option::Some;
        match <_puroro_root::oneofs3::msg::GroupTwoCase as OneofCase>::from_bitslice(
            &self._bitfield,
        ) {
            Some(_puroro_root::oneofs3::msg::GroupTwoCase::G2F32) => {
                self.clear_group_two();
            }
            _ => (),
        }
    }
    pub fn g2_string(&self) -> &str {
        self.group_two.g2_string(&self._bitfield)
    }

    pub fn g2_string_opt(&self) -> ::std::option::Option<&str> {
        self.group_two.g2_string_opt(&self._bitfield)
    }

    pub fn g2_string_mut(&mut self) -> &mut ::std::string::String {
        self.group_two.g2_string_mut(&mut self._bitfield)
    }

    pub fn has_g2_string(&self) -> bool {
        self.g2_string_opt().is_some()
    }

    pub fn clear_g2_string(&mut self) {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::option::Option::Some;
        match <_puroro_root::oneofs3::msg::GroupTwoCase as OneofCase>::from_bitslice(
            &self._bitfield,
        ) {
            Some(_puroro_root::oneofs3::msg::GroupTwoCase::G2String) => {
                self.clear_group_two();
            }
            _ => (),
        }
    }
    pub fn g2_submsg(&self) -> ::std::option::Option<&_puroro_root::oneofs3::Submsg> {
        self.group_two.g2_submsg(&self._bitfield)
    }

    pub fn g2_submsg_opt(&self) -> ::std::option::Option<&_puroro_root::oneofs3::Submsg> {
        self.group_two.g2_submsg_opt(&self._bitfield)
    }

    pub fn g2_submsg_mut(&mut self) -> &mut _puroro_root::oneofs3::Submsg {
        self.group_two.g2_submsg_mut(&mut self._bitfield)
    }

    pub fn has_g2_submsg(&self) -> bool {
        self.g2_submsg_opt().is_some()
    }

    pub fn clear_g2_submsg(&mut self) {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::option::Option::Some;
        match <_puroro_root::oneofs3::msg::GroupTwoCase as OneofCase>::from_bitslice(
            &self._bitfield,
        ) {
            Some(_puroro_root::oneofs3::msg::GroupTwoCase::G2Submsg) => {
                self.clear_group_two();
            }
            _ => (),
        }
    }
    pub fn group_three(
        &self,
    ) -> ::std::option::Option<_puroro_root::oneofs3::msg::GroupThreeCaseRef> {
        use self::_puroro::internal::oneof_type::OneofUnion;
        <_puroro_root::oneofs3::msg::GroupThree as OneofUnion>::case_ref(
            &self.group_three,
            &self._bitfield,
        )
    }

    pub fn clear_group_three(&mut self) {
        use self::_puroro::internal::oneof_type::OneofUnion;
        <_puroro_root::oneofs3::msg::GroupThree as OneofUnion>::clear(
            &mut self.group_three,
            &mut self._bitfield,
        );
    }
    pub fn g3_int32(&self) -> i32 {
        self.group_three.g3_int32(&self._bitfield)
    }

    pub fn g3_int32_opt(&self) -> ::std::option::Option<i32> {
        self.group_three.g3_int32_opt(&self._bitfield)
    }

    pub fn g3_int32_mut(&mut self) -> &mut i32 {
        self.group_three.g3_int32_mut(&mut self._bitfield)
    }

    pub fn has_g3_int32(&self) -> bool {
        self.g3_int32_opt().is_some()
    }

    pub fn clear_g3_int32(&mut self) {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofCase;
        #[allow(unused)]
        use ::std::option::Option::Some;
        match <_puroro_root::oneofs3::msg::GroupThreeCase as OneofCase>::from_bitslice(
            &self._bitfield,
        ) {
            Some(_puroro_root::oneofs3::msg::GroupThreeCase::G3Int32) => {
                self.clear_group_three();
            }
            _ => (),
        }
    }
}

impl self::_puroro::Message for Msg {
    fn from_bytes_iter<I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>>(
        iter: I,
    ) -> self::_puroro::Result<Self> {
        #[allow(unused)]
        use ::std::result::Result::Ok;
        let mut msg: Self = ::std::default::Default::default();
        msg.merge_from_bytes_iter(iter)?;
        Ok(msg)
    }

    fn merge_from_bytes_iter<I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>>(
        &mut self,
        mut iter: I,
    ) -> self::_puroro::Result<()> {
        #[allow(unused)]
        use self::_puroro::internal::field_type::FieldType;
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofUnion;
        #[allow(unused)]
        use ::std::option::Option::Some;
        #[allow(unused)]
        use ::std::result::Result::Ok;
        while let Some((number, field_data)) =
            self::_puroro::internal::ser::FieldData::from_bytes_iter(iter.by_ref())?
        {
            match number {
                1 => <_puroro_root::oneofs3::msg::GroupOne as OneofUnion>::deser_from_iter(
                    &mut self.group_one,
                    &mut self._bitfield,
                    field_data,
                    _puroro_root::oneofs3::msg::GroupOneCase::G1Int32,
                )?,
                2 => <_puroro_root::oneofs3::msg::GroupOne as OneofUnion>::deser_from_iter(
                    &mut self.group_one,
                    &mut self._bitfield,
                    field_data,
                    _puroro_root::oneofs3::msg::GroupOneCase::G1String,
                )?,
                3 => <_puroro_root::oneofs3::msg::GroupTwo as OneofUnion>::deser_from_iter(
                    &mut self.group_two,
                    &mut self._bitfield,
                    field_data,
                    _puroro_root::oneofs3::msg::GroupTwoCase::G2F32,
                )?,
                4 => <_puroro_root::oneofs3::msg::GroupTwo as OneofUnion>::deser_from_iter(
                    &mut self.group_two,
                    &mut self._bitfield,
                    field_data,
                    _puroro_root::oneofs3::msg::GroupTwoCase::G2String,
                )?,
                5 => <_puroro_root::oneofs3::msg::GroupTwo as OneofUnion>::deser_from_iter(
                    &mut self.group_two,
                    &mut self._bitfield,
                    field_data,
                    _puroro_root::oneofs3::msg::GroupTwoCase::G2Submsg,
                )?,
                6 => <_puroro_root::oneofs3::msg::GroupThree as OneofUnion>::deser_from_iter(
                    &mut self.group_three,
                    &mut self._bitfield,
                    field_data,
                    _puroro_root::oneofs3::msg::GroupThreeCase::G3Int32,
                )?,
                _ => todo!(), // Unknown field...
            }
        }
        Ok(())
    }

    fn to_bytes<W: ::std::io::Write>(
        &self,
        #[allow(unused)] out: &mut W,
    ) -> self::_puroro::Result<()> {
        #[allow(unused)]
        use self::_puroro::internal::field_type::FieldType;
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofUnion;
        #[allow(unused)]
        use ::std::result::Result::Ok;
        <_puroro_root::oneofs3::msg::GroupOne as OneofUnion>::ser_to_write(
            &self.group_one,
            &self._bitfield,
            out,
        )?;
        <_puroro_root::oneofs3::msg::GroupTwo as OneofUnion>::ser_to_write(
            &self.group_two,
            &self._bitfield,
            out,
        )?;
        <_puroro_root::oneofs3::msg::GroupThree as OneofUnion>::ser_to_write(
            &self.group_three,
            &self._bitfield,
            out,
        )?;

        Ok(())
    }
}

impl ::std::clone::Clone for Msg {
    fn clone(&self) -> Self {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofUnion;
        #[allow(unused)]
        use ::std::clone::Clone;
        Self {
            group_one: <_puroro_root::oneofs3::msg::GroupOne as OneofUnion>::clone(
                &self.group_one,
                &self._bitfield,
            ),
            group_two: <_puroro_root::oneofs3::msg::GroupTwo as OneofUnion>::clone(
                &self.group_two,
                &self._bitfield,
            ),
            group_three: <_puroro_root::oneofs3::msg::GroupThree as OneofUnion>::clone(
                &self.group_three,
                &self._bitfield,
            ),

            _bitfield: Clone::clone(&self._bitfield),
        }
    }
}

impl ::std::fmt::Debug for Msg {
    fn fmt(
        &self,
        fmt: &mut ::std::fmt::Formatter<'_>,
    ) -> ::std::result::Result<(), ::std::fmt::Error> {
        fmt.debug_struct("Msg").finish()
    }
}

impl ::std::cmp::PartialEq for Msg {
    fn eq(&self, rhs: &Self) -> bool {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofUnion;

        true && <_puroro_root::oneofs3::msg::GroupOne as OneofUnion>::case_ref(
            &self.group_one,
            &self._bitfield,
        ) == <_puroro_root::oneofs3::msg::GroupOne as OneofUnion>::case_ref(
            &rhs.group_one,
            &rhs._bitfield,
        ) && <_puroro_root::oneofs3::msg::GroupTwo as OneofUnion>::case_ref(
            &self.group_two,
            &self._bitfield,
        ) == <_puroro_root::oneofs3::msg::GroupTwo as OneofUnion>::case_ref(
            &rhs.group_two,
            &rhs._bitfield,
        ) && <_puroro_root::oneofs3::msg::GroupThree as OneofUnion>::case_ref(
            &self.group_three,
            &self._bitfield,
        ) == <_puroro_root::oneofs3::msg::GroupThree as OneofUnion>::case_ref(
            &rhs.group_three,
            &rhs._bitfield,
        )
    }
}

impl ::std::ops::Drop for Msg {
    fn drop(&mut self) {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofUnion;
        <_puroro_root::oneofs3::msg::GroupOne as OneofUnion>::clear(
            &mut self.group_one,
            &mut self._bitfield,
        );
        <_puroro_root::oneofs3::msg::GroupTwo as OneofUnion>::clear(
            &mut self.group_two,
            &mut self._bitfield,
        );
        <_puroro_root::oneofs3::msg::GroupThree as OneofUnion>::clear(
            &mut self.group_three,
            &mut self._bitfield,
        );
    }
}

#[derive(Default)]
pub struct Submsg {
    // Singular, Variant(Int32)
    i32_unlabeled: self::_puroro::internal::field_type::SingularNumericalField<
        i32,
        self::_puroro::tags::Int32,
    >,

    _bitfield: self::_puroro::bitvec::BitArray<0>,
}

impl Submsg {
    // Singular, Variant(Int32)
    pub fn i32_unlabeled(&self) -> i32 {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField::<i32, self::_puroro::tags::Int32> as NonRepeatedFieldType>::get_field(
            &self.i32_unlabeled, &self._bitfield, ::std::default::Default::default,
        )
    }
    pub fn i32_unlabeled_opt(&self) -> ::std::option::Option<i32> {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField::<i32, self::_puroro::tags::Int32> as NonRepeatedFieldType>::get_field_opt(
            &self.i32_unlabeled, &self._bitfield,
        )
    }
    pub fn has_i32_unlabeled(&self) -> bool {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField::<i32, self::_puroro::tags::Int32> as NonRepeatedFieldType>::get_field_opt(
            &self.i32_unlabeled, &self._bitfield,
        ).is_some()
    }
    pub fn i32_unlabeled_mut(&mut self) -> &mut i32 {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField::<i32, self::_puroro::tags::Int32> as NonRepeatedFieldType>::mut_field(
            &mut self.i32_unlabeled, &mut self._bitfield, ::std::default::Default::default,
        )
    }
    pub fn clear_i32_unlabeled(&mut self) {
        use self::_puroro::internal::field_type::NonRepeatedFieldType;
        <self::_puroro::internal::field_type::SingularNumericalField::<i32, self::_puroro::tags::Int32> as NonRepeatedFieldType>::clear(
            &mut self.i32_unlabeled, &mut self._bitfield,
        )
    }
}

impl self::_puroro::Message for Submsg {
    fn from_bytes_iter<I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>>(
        iter: I,
    ) -> self::_puroro::Result<Self> {
        #[allow(unused)]
        use ::std::result::Result::Ok;
        let mut msg: Self = ::std::default::Default::default();
        msg.merge_from_bytes_iter(iter)?;
        Ok(msg)
    }

    fn merge_from_bytes_iter<I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>>(
        &mut self,
        mut iter: I,
    ) -> self::_puroro::Result<()> {
        #[allow(unused)]
        use self::_puroro::internal::field_type::FieldType;
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofUnion;
        #[allow(unused)]
        use ::std::option::Option::Some;
        #[allow(unused)]
        use ::std::result::Result::Ok;
        while let Some((number, field_data)) =
            self::_puroro::internal::ser::FieldData::from_bytes_iter(iter.by_ref())?
        {
            match number {
                1 => <self::_puroro::internal::field_type::SingularNumericalField<
                    i32,
                    self::_puroro::tags::Int32,
                > as FieldType>::deser_from_iter(
                    &mut self.i32_unlabeled,
                    &mut self._bitfield,
                    field_data,
                )?,
                _ => todo!(), // Unknown field...
            }
        }
        Ok(())
    }

    fn to_bytes<W: ::std::io::Write>(
        &self,
        #[allow(unused)] out: &mut W,
    ) -> self::_puroro::Result<()> {
        #[allow(unused)]
        use self::_puroro::internal::field_type::FieldType;
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofUnion;
        #[allow(unused)]
        use ::std::result::Result::Ok;
        <self::_puroro::internal::field_type::SingularNumericalField<
            i32,
            self::_puroro::tags::Int32,
        > as FieldType>::ser_to_write(&self.i32_unlabeled, &self._bitfield, 1, out)?;

        Ok(())
    }
}

impl ::std::clone::Clone for Submsg {
    fn clone(&self) -> Self {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofUnion;
        #[allow(unused)]
        use ::std::clone::Clone;
        Self {
            i32_unlabeled: Clone::clone(&self.i32_unlabeled),

            _bitfield: Clone::clone(&self._bitfield),
        }
    }
}

impl ::std::fmt::Debug for Submsg {
    fn fmt(
        &self,
        fmt: &mut ::std::fmt::Formatter<'_>,
    ) -> ::std::result::Result<(), ::std::fmt::Error> {
        fmt.debug_struct("Submsg")
            .field("i32_unlabeled", &self.i32_unlabeled())
            .finish()
    }
}

impl ::std::cmp::PartialEq for Submsg {
    fn eq(&self, rhs: &Self) -> bool {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofUnion;

        true && self.i32_unlabeled_opt() == rhs.i32_unlabeled_opt()
    }
}

impl ::std::ops::Drop for Submsg {
    fn drop(&mut self) {
        #[allow(unused)]
        use self::_puroro::internal::oneof_type::OneofUnion;
    }
}
pub mod msg;
