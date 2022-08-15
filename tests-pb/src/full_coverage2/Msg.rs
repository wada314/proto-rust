// A generated source code by puroro library
// package full_coverage2.Msg
pub mod _submsg;

pub mod _puroro_root {
    pub use super::super::_puroro_root::*;
}

pub mod _puroro {
    pub use ::puroro::*;
}

#[derive(Default, Clone)]
pub struct Submsg {
    // Optional, Variant(Int32)
    i32_required: self::_puroro::internal::field_types::OptionalVariantField<
        i32,
        self::_puroro::tags::Int32,
        0,
    >,
    // Optional, Variant(Int64)
    i64_required: self::_puroro::internal::field_types::OptionalVariantField<
        i64,
        self::_puroro::tags::Int64,
        1,
    >,

    _bitfield: self::_puroro::bitvec::BitArray<1>,
}

impl Submsg {
    // Optional, Variant(Int32)
    pub fn i32_required(&self) -> i32 {
        <self::_puroro::internal::field_types::OptionalVariantField<
            i32,
            self::_puroro::tags::Int32,
            0,
        > as self::_puroro::internal::field_types::FieldType>::get_field(
            &self.i32_required,
            &self._bitfield,
        )
    }
    // Optional, Variant(Int64)
    pub fn i64_required(&self) -> i64 {
        <self::_puroro::internal::field_types::OptionalVariantField<
            i64,
            self::_puroro::tags::Int64,
            1,
        > as self::_puroro::internal::field_types::FieldType>::get_field(
            &self.i64_required,
            &self._bitfield,
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
                1 => <self::_puroro::internal::field_types::OptionalVariantField<
                    i32,
                    self::_puroro::tags::Int32,
                    0,
                > as self::_puroro::internal::field_types::FieldType>::deser_from_iter(
                    &mut msg.i32_required,
                    &mut msg._bitfield,
                    field_data,
                )?,
                101 => <self::_puroro::internal::field_types::OptionalVariantField<
                    i64,
                    self::_puroro::tags::Int64,
                    1,
                > as self::_puroro::internal::field_types::FieldType>::deser_from_iter(
                    &mut msg.i64_required,
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
