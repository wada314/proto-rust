use std::convert::TryInto;

use crate::de::DoDefaultCheck;
use crate::se::to_io_write::write_field_number_and_wire_type;
use crate::se::{SerEnumToIoWrite, SerFieldToIoWrite, SerInternalDataToIoWrite, SerMsgToIoWrite};
use crate::{
    EnumTypeGen, ErrorKind, FieldTypeGen, MsgTypeGen, Result, SimpleImpl, StructInternalTypeGen,
};
use ::puroro::fixed_bits::{Bits32TypeTag, Bits64TypeTag};
use ::puroro::tags;
use ::puroro::types::WireType;
use ::puroro::variant::{Variant, VariantTypeTag};
use ::puroro::{GetImpl, SerToIoWrite};

use super::{LabelWrappedLdType, LabelWrappedMessageType, LabelWrappedType};

// Non-repeated, variant
type NonRepeatedVariant<X, V, _1, _2> = (tags::NonRepeated<_1, _2>, (X, tags::wire::Variant<V>));
type VariantNativeType<X, V> =
    <(X, tags::wire::Variant<V>) as tags::NumericalFieldTypeTag>::NativeType;
impl<X, V, _1, _2> SerFieldToIoWrite<X, tags::NonRepeated<_1, _2>, tags::wire::Variant<V>>
    for SimpleImpl
where
    (X, tags::NonRepeated<_1, _2>): DoDefaultCheck,
    (X, tags::wire::Variant<V>): tags::NumericalFieldTypeTag + VariantTypeTag,
    VariantNativeType<X, V>: LabelWrappedType<tags::NonRepeated<_1, _2>> + Clone,
    Self: FieldTypeGen<X, tags::NonRepeated<_1, _2>, tags::wire::Variant<V>>,
{
    fn ser_to_io_write<W>(
        field: &<Self as FieldTypeGen<X, tags::NonRepeated<_1, _2>, tags::wire::Variant<V>>>::Type,
        field_number: i32,
        out: &mut W,
        _internal_data: &<Self as StructInternalTypeGen>::Type,
    ) -> Result<()>
    where
        W: std::io::Write,
    {
        let do_default_check = <(X, tags::NonRepeated<_1, _2>) as DoDefaultCheck>::VALUE;
        if let Some(value) =
            <VariantNativeType<X, V> as LabelWrappedType<tags::NonRepeated<_1, _2>>>::iter(field)
                .next()
        {
            let variant = Variant::from_native::<(X, tags::wire::Variant<V>)>(value.clone())?;
            if !do_default_check || !variant.is_zero() {
                write_field_number_and_wire_type(out, field_number, WireType::Variant)?;
                variant.encode_bytes(out)?;
            }
        }
        Ok(())
    }
}

// Repeated, variant
type RepeatedVariant<X, V> = (tags::Repeated, (X, tags::wire::Variant<V>));
impl<X, V> SerFieldToIoWrite<X, tags::Repeated, tags::wire::Variant<V>> for SimpleImpl
where
    (X, tags::wire::Variant<V>): tags::NumericalFieldTypeTag + VariantTypeTag,
    VariantNativeType<X, V>: LabelWrappedType<tags::Repeated> + Clone,
    Self: FieldTypeGen<X, tags::Repeated, tags::wire::Variant<V>>,
{
    fn ser_to_io_write<W>(
        field: &<Self as FieldTypeGen<X, tags::Repeated, tags::wire::Variant<V>>>::Type,
        field_number: i32,
        out: &mut W,
        _internal_data: &<Self as StructInternalTypeGen>::Type,
    ) -> Result<()>
    where
        W: std::io::Write,
    {
        let mut iter =
            <VariantNativeType<X, V> as LabelWrappedType<tags::Repeated>>::iter(field).peekable();
        if iter.peek().is_some() {
            let mut buffer: Vec<u8> = Vec::new();
            for val in iter {
                let variant = Variant::from_native::<(X, tags::wire::Variant<V>)>(val.clone())?;
                variant.encode_bytes(&mut buffer)?;
            }
            let total_len: i32 = buffer
                .len()
                .try_into()
                .map_err(|_| ErrorKind::TooLongToSerialize)?;

            write_field_number_and_wire_type(out, field_number, WireType::LengthDelimited)?;
            Variant::from_i32(total_len)?.encode_bytes(out)?;
            out.write_all(&buffer)?;
        }
        Ok(())
    }
}

// Bits32
type Bits32NativeType<X, V> =
    <(X, tags::wire::Bits32<V>) as tags::NumericalFieldTypeTag>::NativeType;
type Bits32FieldTag<L, X, V> = (L, (X, tags::wire::Bits32<V>));
impl<L, X, V> SerFieldToIoWrite<X, L, tags::wire::Bits32<V>> for SimpleImpl
where
    (X, L): DoDefaultCheck,
    (X, tags::wire::Bits32<V>): tags::NumericalFieldTypeTag + Bits32TypeTag,
    Bits32NativeType<X, V>: LabelWrappedType<L> + Clone,
    Self: FieldTypeGen<
        X,
        L,
        tags::wire::Bits32<V>,
        Type = <Bits32NativeType<X, V> as LabelWrappedType<L>>::Type,
    >,
{
    fn ser_to_io_write<W>(
        field: &<Self as FieldTypeGen<X, L, tags::wire::Bits32<V>>>::Type,
        field_number: i32,
        out: &mut W,
        _internal_data: &<Self as StructInternalTypeGen>::Type,
    ) -> Result<()>
    where
        W: std::io::Write,
    {
        let do_default_check = <(X, L) as DoDefaultCheck>::VALUE;
        for item in <Bits32NativeType<X, V> as LabelWrappedType<L>>::iter(field) {
            if do_default_check
                && item.clone()
                    == <(X, tags::wire::Bits32<V>) as tags::NumericalFieldTypeTag>::default()
            {
                continue;
            }
            write_field_number_and_wire_type(out, field_number, WireType::Bits32)?;
            let bytes = <(X, tags::wire::Bits32<V>) as Bits32TypeTag>::into_array(item.clone());
            out.write_all(&bytes)?;
        }
        Ok(())
    }
}

// Bits64
type Bits64NativeType<X, V> =
    <(X, tags::wire::Bits64<V>) as tags::NumericalFieldTypeTag>::NativeType;
type Bits64FieldTag<L, X, V> = (L, (X, tags::wire::Bits64<V>));
impl<L, X, V> SerFieldToIoWrite<X, L, tags::wire::Bits64<V>> for SimpleImpl
where
    (X, L): DoDefaultCheck,
    (X, tags::wire::Bits64<V>): tags::NumericalFieldTypeTag + Bits64TypeTag,
    Bits64NativeType<X, V>: LabelWrappedType<L> + Clone,
    Self: FieldTypeGen<
        X,
        L,
        tags::wire::Bits64<V>,
        Type = <Bits64NativeType<X, V> as LabelWrappedType<L>>::Type,
    >,
{
    fn ser_to_io_write<W>(
        field: &<Self as FieldTypeGen<X, L, tags::wire::Bits64<V>>>::Type,
        field_number: i32,
        out: &mut W,
        _internal_data: &<Self as StructInternalTypeGen>::Type,
    ) -> Result<()>
    where
        W: std::io::Write,
    {
        let do_default_check = <(X, L) as DoDefaultCheck>::VALUE;
        for item in <Bits64NativeType<X, V> as LabelWrappedType<L>>::iter(field) {
            if do_default_check
                && item.clone()
                    == <(X, tags::wire::Bits64<V>) as tags::NumericalFieldTypeTag>::default()
            {
                continue;
            }
            write_field_number_and_wire_type(out, field_number, WireType::Bits64)?;
            let bytes = <(X, tags::wire::Bits64<V>) as Bits64TypeTag>::into_array(item.clone());
            out.write_all(&bytes)?;
        }
        Ok(())
    }
}

// Bytes
impl<L, X> SerFieldToIoWrite<X, L, tags::Bytes> for SimpleImpl
where
    (X, L): DoDefaultCheck,
    [u8]: LabelWrappedLdType<L, X>,
    Self: FieldTypeGen<X, L, tags::Bytes>,
{
    fn ser_to_io_write<W>(
        field: &<Self as FieldTypeGen<X, L, tags::Bytes>>::Type,
        field_number: i32,
        out: &mut W,
        _internal_data: &<Self as StructInternalTypeGen>::Type,
    ) -> Result<()>
    where
        W: std::io::Write,
    {
        let do_default_check = <(X, L) as DoDefaultCheck>::VALUE;
        for item in <[u8] as LabelWrappedLdType<L, X>>::iter(field) {
            if do_default_check && item.is_empty() {
                continue;
            }
            write_field_number_and_wire_type(out, field_number, WireType::LengthDelimited)?;
            let length: i32 = item
                .len()
                .try_into()
                .map_err(|_| ErrorKind::TooLongToSerialize)?;
            Variant::from_i32(length)?.encode_bytes(out)?;
            out.write_all(item)?;
        }
        Ok(())
    }
}

// Strings
impl<L, X> SerFieldToIoWrite<X, L, tags::String> for SimpleImpl
where
    (X, L): DoDefaultCheck,
    str: LabelWrappedLdType<L, X>,
    Self: FieldTypeGen<X, L, tags::String, Type = <str as LabelWrappedLdType<L, X>>::Type>,
{
    fn ser_to_io_write<W>(
        field: &<Self as FieldTypeGen<X, L, tags::String>>::Type,
        field_number: i32,
        out: &mut W,
        _internal_data: &<Self as StructInternalTypeGen>::Type,
    ) -> Result<()>
    where
        W: std::io::Write,
    {
        let do_default_check = <(X, L) as DoDefaultCheck>::VALUE;
        for item in <str as LabelWrappedLdType<L, X>>::iter(field) {
            if do_default_check && item.is_empty() {
                continue;
            }
            write_field_number_and_wire_type(out, field_number, WireType::LengthDelimited)?;
            let length: i32 = item
                .len()
                .try_into()
                .map_err(|_| ErrorKind::TooLongToSerialize)?;
            Variant::from_i32(length)?.encode_bytes(out)?;
            out.write_all(item.as_bytes())?;
        }
        Ok(())
    }
}

// Message
type MessageFieldTag<L, X, M> = (L, (X, tags::Message<M>));
impl<L, X> SerMsgToIoWrite<X, L> for SimpleImpl
where
    Self: MsgTypeGen<X, L>,
{
    fn ser_to_io_write<W, M>(
        field: &<Self as MsgTypeGen<X, L>>::MsgType<M>,
        field_number: i32,
        out: &mut W,
        _internal_data: &<Self as StructInternalTypeGen>::Type,
    ) -> Result<()>
    where
        W: std::io::Write,
    {
        use std::ops::Deref as _;
        for boxed in <M as LabelWrappedMessageType<L>>::iter(field) {
            write_field_number_and_wire_type(out, field_number, WireType::LengthDelimited)?;
            let mut buffer: Vec<u8> = Vec::new();
            <M as SerToIoWrite>::ser(boxed.deref(), &mut buffer)?;
            let length: i32 = buffer
                .len()
                .try_into()
                .map_err(|_| ErrorKind::TooLongToSerialize)?;
            Variant::from_i32(length)?.encode_bytes(out)?;
            out.write_all(&buffer)?;
        }
        Ok(())
    }
}

impl SerInternalDataToIoWrite for SimpleImpl {
    fn ser_to_io_write<W>(
        _out: &mut W,
        _internal_data: &<Self as StructInternalTypeGen>::Type,
    ) -> Result<()>
    where
        W: std::io::Write,
    {
        Ok(())
    }
}
