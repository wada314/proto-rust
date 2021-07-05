use super::{LabelWrappedLDType, LabelWrappedType, SimpleImpl};
use puroro::de::from_iter::Variants;
use puroro::variant;
use puroro::DeserFromBytesIter;
use puroro::{tags, DeserFieldFromBytesIter, Result};
use puroro::{ErrorKind, FieldData, FieldTypeGen};

// deser from iterator

// deser from iterator, into variant type fields
impl<L, V, X> DeserFieldFromBytesIter<(L, (X, tags::wire::Variant<V>))> for SimpleImpl
where
    // The type tag has corresponding Rust numerical type,
    (X, tags::wire::Variant<V>): tags::NumericalFieldTypeTag + variant::VariantTypeTag,
    // ..and the type above can be wrapped by Option<> or Vec<> according to
    // the label (this is always true),
    <(X, tags::wire::Variant<V>) as tags::NumericalFieldTypeTag>::NativeType: LabelWrappedType<L>,
    // ..and the Rust type generated by FieldTypeGen is equal to the type above.
    Self: FieldTypeGen<(L, (X, tags::wire::Variant<V>)), Type =
        <<(X, tags::wire::Variant<V>) as tags::NumericalFieldTypeTag>::NativeType as LabelWrappedType<L>>::Type>
{
    fn deser_from_scoped_bytes_iter<I>(
        field: &mut <Self as FieldTypeGen<(L, (X, tags::wire::Variant<V>))>>::Type,
        data: FieldData<&mut puroro::de::from_iter::ScopedIter<I>>,
    ) -> Result<()>
    where
        I: Iterator<Item = std::io::Result<u8>>,
    {
        match data {
            FieldData::Variant(variant) => {
                // todo: proto3 default value check
                let native = variant.to_native::<(X, tags::wire::Variant<V>)>()?;
                *LabelWrappedType::<L>::get_or_insert_with(
                    field,
                    <(X, tags::wire::Variant<V>) as tags::NumericalFieldTypeTag>::default
                ) = native;
            },
            FieldData::LengthDelimited(iter) => {
                // todo: proto3 default value check
                let variants_iter = Variants::new(iter);
                let values_iter = variants_iter.map(|rv| rv.and_then(|v| {
                    v.to_native::<(X, tags::wire::Variant<V>)>()
                }));
                LabelWrappedType::<L>::extend(field, values_iter)?;
            },
            FieldData::Bits32(_) |
            FieldData::Bits64(_) => Err(ErrorKind::UnexpectedWireType)?,
        };
        Ok(())
    }
}

// Bits32 / Bits64
impl<L, V, X, _1> DeserFieldFromBytesIter<(L, (X, tags::wire::Bits32Or64<V, _1>))> for SimpleImpl
where
    // The type tag has corresponding Rust numerical type,
    (X, tags::wire::Bits32Or64<V, _1>): tags::NumericalFieldTypeTag + variant::VariantTypeTag,
    // ..and the type above can be wrapped by Option<> or Vec<> according to
    // the label (this is always true),
    <(X, tags::wire::Bits32Or64<V, _1>) as tags::NumericalFieldTypeTag>::NativeType: LabelWrappedType<L>,
    // ..and the Rust type generated by FieldTypeGen is equal to the type above.
    Self: FieldTypeGen<(L, (X, tags::wire::Bits32Or64<V, _1>)), Type =
        <<(X, tags::wire::Bits32Or64<V, _1>) as tags::NumericalFieldTypeTag>::NativeType as LabelWrappedType<L>>::Type>
{
    fn deser_from_scoped_bytes_iter<I>(
        field: &mut <Self as FieldTypeGen<(L, (X, tags::wire::Bits32Or64<V, _1>))>>::Type,
        data: FieldData<&mut puroro::de::from_iter::ScopedIter<I>>,
    ) -> Result<()>
    where
        I: Iterator<Item = std::io::Result<u8>>,
    {
        match data {
            FieldData::Variant(variant) => {
                // todo: proto3 default value check
                let native = variant.to_native::<(X, tags::wire::Bits32Or64<V, _1>)>()?;
                *LabelWrappedType::<L>::get_or_insert_with(
                    field,
                    <(X, tags::wire::Bits32Or64<V, _1>) as tags::NumericalFieldTypeTag>::default
                ) = native;
            },
            _ => Err(ErrorKind::UnexpectedWireType)?,
        };
        Ok(())
    }
}

// String
impl<L, X> DeserFieldFromBytesIter<(L, (X, tags::String))> for SimpleImpl
where
    str: LabelWrappedLDType<L, X>,
    Self: FieldTypeGen<(L, (X, tags::String)), Type = <str as LabelWrappedLDType<L, X>>::Type>,
{
    fn deser_from_scoped_bytes_iter<I>(
        field: &mut <Self as FieldTypeGen<(L, (X, tags::String))>>::Type,
        data: FieldData<&mut puroro::de::from_iter::ScopedIter<I>>,
    ) -> Result<()>
    where
        I: Iterator<Item = std::io::Result<u8>>,
    {
        match data {
            FieldData::LengthDelimited(iter) => {
                // TODO: do proto3 default value check
                let string = String::from_utf8(iter.collect::<::std::io::Result<Vec<_>>>()?)
                    .map_err(|e| ErrorKind::InvalidUtf8(e))?;
                *<str as LabelWrappedLDType<L, X>>::get_or_insert_default(field) = string;
            }
            _ => Err(ErrorKind::UnexpectedWireType)?,
        }
        Ok(())
    }
}

// Bytes
impl<L, X> DeserFieldFromBytesIter<(L, (X, tags::Bytes))> for SimpleImpl
where
    [u8]: LabelWrappedLDType<L, X>,
    Self: FieldTypeGen<(L, (X, tags::Bytes)), Type = <[u8] as LabelWrappedLDType<L, X>>::Type>,
{
    fn deser_from_scoped_bytes_iter<I>(
        field: &mut <Self as FieldTypeGen<(L, (X, tags::Bytes))>>::Type,
        data: FieldData<&mut puroro::de::from_iter::ScopedIter<I>>,
    ) -> Result<()>
    where
        I: Iterator<Item = std::io::Result<u8>>,
    {
        match data {
            FieldData::LengthDelimited(iter) => {
                // TODO: do proto3 default value check
                let bytes = iter.collect::<::std::io::Result<Vec<_>>>()?;
                *<[u8] as LabelWrappedLDType<L, X>>::get_or_insert_default(field) = bytes;
            }
            _ => Err(ErrorKind::UnexpectedWireType)?,
        }
        Ok(())
    }
}

// Message
impl<X, M, _1, _2> DeserFieldFromBytesIter<(tags::NonRepeated<_1, _2>, (X, tags::Message<M>))>
    for SimpleImpl
where
    M: DeserFromBytesIter,
{
    fn deser_from_scoped_bytes_iter<I>(
        field: &mut <Self as FieldTypeGen<(tags::NonRepeated<_1, _2>, (X, tags::Message<M>))>>::Type,
        data: FieldData<&mut puroro::de::from_iter::ScopedIter<I>>,
    ) -> Result<()>
    where
        I: Iterator<Item = std::io::Result<u8>>,
    {
        match data {
            FieldData::LengthDelimited(iter) => {
                todo!()
            }
            _ => Err(ErrorKind::UnexpectedWireType)?,
        }
    }
}
