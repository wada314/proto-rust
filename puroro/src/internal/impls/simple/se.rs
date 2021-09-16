use crate::fixed_bits::{Bits32TypeTag, Bits64TypeTag};
use crate::internal::se::to_io_write::write_field_number_and_wire_type;
use crate::types::WireType;
use crate::variant::Variant;
use crate::variant::VariantTypeTag;
use crate::SerToIoWrite;
use crate::{tags, Result};
use ::std::borrow::Cow;
use ::std::convert::TryInto;
use ::std::io::Write;
use ::std::marker::PhantomData;
use ::std::ops::Deref;

use super::VecOrOptionOrBare;

struct NullWrite(usize);
impl Write for NullWrite {
    fn write(&mut self, buf: &[u8]) -> ::std::io::Result<usize> {
        if let Some(new_size) = usize::checked_add(self.0, buf.len()) {
            self.0 = new_size;
            Ok(buf.len())
        } else {
            Err(::std::io::Error::new(
                ::std::io::ErrorKind::Unsupported,
                "Too long to serialize",
            ))
        }
    }
    fn flush(&mut self) -> ::std::io::Result<()> {
        Ok(())
    }
}
impl NullWrite {
    fn new() -> Self {
        Self(0usize)
    }
    fn len(&self) -> usize {
        self.0
    }
}

// ser to Write methods

pub struct SerFieldToIoWrite<L, V>(PhantomData<(L, V)>);

impl<V, _1, _2, _3> SerFieldToIoWrite<tags::LabelNonRepeated<_1, _2, _3>, tags::wire::Variant<V>>
where
    tags::LabelNonRepeated<_1, _2, _3>: tags::FieldLabelTag,
    tags::wire::Variant<V>: VariantTypeTag,
{
    pub fn ser_field<FieldType, W>(field: &FieldType, number: i32, out: &mut W) -> Result<()>
    where
        FieldType:
            VecOrOptionOrBare<<tags::wire::Variant<V> as tags::NumericalTypeTag>::NativeType>,
        W: Write,
    {
        use tags::FieldLabelTag as _;
        for item in field.iter() {
            if !tags::LabelNonRepeated::<_1, _2, _3>::DO_DEFAULT_CHECK
                || item.clone() != Default::default()
            {
                write_field_number_and_wire_type(out, number, WireType::Variant)?;
                Variant::from_native::<tags::wire::Variant<V>>(item.clone())?.encode_bytes(out)?;
            }
        }
        Ok(())
    }
}

impl<V> SerFieldToIoWrite<tags::Repeated, tags::wire::Variant<V>>
where
    tags::wire::Variant<V>: VariantTypeTag,
{
    pub fn ser_field<FieldType, W>(field: &FieldType, number: i32, out: &mut W) -> Result<()>
    where
        FieldType:
            VecOrOptionOrBare<<tags::wire::Variant<V> as tags::NumericalTypeTag>::NativeType>,
        W: Write,
    {
        let len = {
            let mut null_out = NullWrite::new();
            for item in field.iter() {
                Variant::from_native::<tags::wire::Variant<V>>(item.clone())?
                    .encode_bytes(&mut null_out)?;
            }
            null_out.len()
        };
        if len == 0 {
            return Ok(());
        }
        let len_i32 = len
            .try_into()
            .map_err(|_| crate::ErrorKind::TooLongToSerialize)?;
        write_field_number_and_wire_type(out, number, WireType::LengthDelimited)?;
        Variant::from_i32(len_i32)?.encode_bytes(out)?;
        for item in field.iter() {
            Variant::from_native::<tags::wire::Variant<V>>(item.clone())?.encode_bytes(out)?;
        }
        Ok(())
    }
}

impl<L, V> SerFieldToIoWrite<L, tags::wire::Bits32<V>>
where
    L: tags::FieldLabelTag,
    tags::wire::Bits32<V>: Bits32TypeTag,
{
    pub fn ser_field<FieldType, W>(field: &FieldType, number: i32, out: &mut W) -> Result<()>
    where
        FieldType: VecOrOptionOrBare<<tags::wire::Bits32<V> as tags::NumericalTypeTag>::NativeType>,
        W: Write,
    {
        for item in field.iter() {
            if !L::DO_DEFAULT_CHECK || item.clone() != Default::default() {
                write_field_number_and_wire_type(out, number, WireType::Bits32)?;
                out.write(&tags::wire::Bits32::<V>::into_array(item.clone()))?;
            }
        }
        Ok(())
    }
}

impl<L, V> SerFieldToIoWrite<L, tags::wire::Bits64<V>>
where
    L: tags::FieldLabelTag,
    tags::wire::Bits64<V>: Bits64TypeTag,
{
    pub fn ser_field<FieldType, W>(field: &FieldType, number: i32, out: &mut W) -> Result<()>
    where
        FieldType: VecOrOptionOrBare<<tags::wire::Bits64<V> as tags::NumericalTypeTag>::NativeType>,
        W: Write,
    {
        for item in field.iter() {
            if !L::DO_DEFAULT_CHECK || item.clone() != Default::default() {
                write_field_number_and_wire_type(out, number, WireType::Bits64)?;
                out.write(&tags::wire::Bits64::<V>::into_array(item.clone()))?;
            }
        }
        Ok(())
    }
}

impl<L> SerFieldToIoWrite<L, tags::Bytes>
where
    L: tags::FieldLabelTag,
{
    pub fn ser_field<FieldType, W>(field: &FieldType, number: i32, out: &mut W) -> Result<()>
    where
        FieldType: VecOrOptionOrBare<Cow<'static, [u8]>>,
        W: Write,
    {
        for item in field.iter() {
            if !L::DO_DEFAULT_CHECK || !item.is_empty() {
                write_field_number_and_wire_type(out, number, WireType::LengthDelimited)?;
                let len_i32: i32 = item
                    .len()
                    .try_into()
                    .map_err(|_| crate::ErrorKind::TooLongToSerialize)?;
                Variant::from_i32(len_i32)?.encode_bytes(out)?;
                out.write(&item)?;
            }
        }
        Ok(())
    }
}

impl<L> SerFieldToIoWrite<L, tags::String>
where
    L: tags::FieldLabelTag,
{
    pub fn ser_field<FieldType, W>(field: &FieldType, number: i32, out: &mut W) -> Result<()>
    where
        FieldType: VecOrOptionOrBare<Cow<'static, str>>,
        W: Write,
    {
        for item in field.iter() {
            if !L::DO_DEFAULT_CHECK || !item.is_empty() {
                write_field_number_and_wire_type(out, number, WireType::LengthDelimited)?;
                let len_i32: i32 = item
                    .len()
                    .try_into()
                    .map_err(|_| crate::ErrorKind::TooLongToSerialize)?;
                Variant::from_i32(len_i32)?.encode_bytes(out)?;
                out.write(item.as_bytes())?;
            }
        }
        Ok(())
    }
}

impl<M, _1, _2, _3> SerFieldToIoWrite<tags::LabelNonRepeated<_1, _2, _3>, tags::Message<M>>
where
    M: SerToIoWrite,
{
    pub fn ser_field<FieldType, W>(field: &FieldType, number: i32, out: &mut W) -> Result<()>
    where
        FieldType: VecOrOptionOrBare<Box<M>>,
        W: Write,
    {
        for boxed in field.iter() {
            let len = {
                let mut null_out = NullWrite::new();
                <M as SerToIoWrite>::ser(boxed.deref(), &mut null_out)?;
                null_out.len()
            };
            let len_i32: i32 = len
                .try_into()
                .map_err(|_| crate::ErrorKind::TooLongToSerialize)?;
            write_field_number_and_wire_type(out, number, WireType::LengthDelimited)?;
            Variant::from_i32(len_i32)?.encode_bytes(out)?;
            <M as SerToIoWrite>::ser(boxed.deref(), out)?;
        }
        Ok(())
    }
}

impl<M> SerFieldToIoWrite<tags::Repeated, tags::Message<M>>
where
    M: SerToIoWrite,
{
    pub fn ser_field<W>(field: &Vec<M>, number: i32, out: &mut W) -> Result<()>
    where
        W: Write,
    {
        for item in field {
            let len = {
                let mut null_out = NullWrite::new();
                <M as SerToIoWrite>::ser(item, &mut null_out)?;
                null_out.len()
            };
            let len_i32: i32 = len
                .try_into()
                .map_err(|_| crate::ErrorKind::TooLongToSerialize)?;
            write_field_number_and_wire_type(out, number, WireType::LengthDelimited)?;
            Variant::from_i32(len_i32)?.encode_bytes(out)?;
            <M as SerToIoWrite>::ser(item, out)?;
        }
        Ok(())
    }
}