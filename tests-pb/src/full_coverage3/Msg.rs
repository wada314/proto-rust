// A generated source code by puroro library
// package full_coverage3.Msg
pub mod _submsg;

pub mod _puroro_root {
    pub use super::super::_puroro_root::*;
}

pub mod _puroro {
    pub use ::puroro::*;
}

#[derive(Default, Clone)]
pub struct Submsg {
    // Singular, Variant(Int32)
    i32_unlabeled:
        self::_puroro::internal::field_types::SingularVariantField<i32, self::_puroro::tags::Int32>,
    // Singular, Variant(Int32)
    i32_optional:
        self::_puroro::internal::field_types::SingularVariantField<i32, self::_puroro::tags::Int32>,
    // Singular, Variant(Int64)
    i64_unlabeled:
        self::_puroro::internal::field_types::SingularVariantField<i64, self::_puroro::tags::Int64>,

    _bitfield: self::_puroro::bitvec::BitArray<0>,
}

impl Submsg {
    // Singular, Variant(Int32)
    pub fn i32_unlabeled(&self) -> i32 {
        <self::_puroro::internal::field_types::SingularVariantField<i32, self::_puroro::tags::Int32> as self::_puroro::internal::field_types::FieldType>::get_field(
            &self.i32_unlabeled, &self._bitfield,
        )
    }
    // Singular, Variant(Int32)
    pub fn i32_optional(&self) -> i32 {
        <self::_puroro::internal::field_types::SingularVariantField<i32, self::_puroro::tags::Int32> as self::_puroro::internal::field_types::FieldType>::get_field(
            &self.i32_optional, &self._bitfield,
        )
    }
    // Singular, Variant(Int64)
    pub fn i64_unlabeled(&self) -> i64 {
        <self::_puroro::internal::field_types::SingularVariantField<i64, self::_puroro::tags::Int64> as self::_puroro::internal::field_types::FieldType>::get_field(
            &self.i64_unlabeled, &self._bitfield,
        )
    }
}

impl self::_puroro::Message for Submsg {
    fn from_bytes_iter<I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>>(
        iter: I,
    ) -> self::_puroro::Result<Self> {
        let mut msg: Self = ::std::default::Default::default();
        let mut peekable = iter.peekable();
        while peekable.peek().is_some() {
            let (number, field_data) =
                self::_puroro::internal::ser::FieldData::from_bytes_iter(peekable.by_ref())?;
            match number {
                1 => <self::_puroro::internal::field_types::SingularVariantField<
                    i32,
                    self::_puroro::tags::Int32,
                > as self::_puroro::internal::field_types::FieldType>::deser_from_iter(
                    &mut msg.i32_unlabeled,
                    &mut msg._bitfield,
                    field_data,
                )?,
                2 => <self::_puroro::internal::field_types::SingularVariantField<
                    i32,
                    self::_puroro::tags::Int32,
                > as self::_puroro::internal::field_types::FieldType>::deser_from_iter(
                    &mut msg.i32_optional,
                    &mut msg._bitfield,
                    field_data,
                )?,
                101 => <self::_puroro::internal::field_types::SingularVariantField<
                    i64,
                    self::_puroro::tags::Int64,
                > as self::_puroro::internal::field_types::FieldType>::deser_from_iter(
                    &mut msg.i64_unlabeled,
                    &mut msg._bitfield,
                    field_data,
                )?,
                _ => todo!(),
            }
        }
        Ok(msg)
    }
}

pub mod _submsg {

    mod _puroro {
        pub use super::super::_puroro::*;
    }
    mod _puroro_root {
        pub use super::super::_puroro_root::*;
    }
}