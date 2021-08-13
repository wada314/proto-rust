use crate::de::from_iter::{ScopedIter, Variants};
use crate::de::DeserFieldsFromBytesIter;
use crate::se::to_io_write::write_field_number_and_wire_type;
use ::puroro::fixed_bits::{Bits32TypeTag, Bits64TypeTag};
use ::puroro::types::FieldData;
use ::puroro::types::WireType;
use ::puroro::variant::Variant;
use ::puroro::variant::VariantTypeTag;
use ::puroro::{tags, RepeatedField, Result};
use ::puroro::{ErrorKind, Message, SerToIoWrite};
use ::std::borrow::Borrow;
use ::std::borrow::Cow;
use ::std::convert::TryInto;
use ::std::io::Write;
use ::std::marker::PhantomData;
use ::std::ops::{Deref, DerefMut};

pub struct VecWrapper<'msg, T>(&'msg Vec<T>);

impl<'msg, T> VecWrapper<'msg, T> {
    pub fn new(vec: &'msg Vec<T>) -> Self {
        Self(vec)
    }
}

impl<'msg, T: Clone> IntoIterator for VecWrapper<'msg, T> {
    type Item = T;
    type IntoIter = std::iter::Cloned<std::slice::Iter<'msg, T>>;

    fn into_iter(self) -> Self::IntoIter {
        <[T]>::iter(&self.0).cloned()
    }
}
impl<'msg, T: Clone> RepeatedField<'msg, T> for VecWrapper<'msg, T> {}

pub struct VecCowWrapper<'msg, B: ?Sized + ToOwned>(&'msg Vec<B::Owned>);

impl<'msg, B: ?Sized + ToOwned> VecCowWrapper<'msg, B> {
    pub fn new(vec: &'msg Vec<B::Owned>) -> Self {
        Self(vec)
    }
}
impl<'msg, B: 'msg + ?Sized + ToOwned> IntoIterator for VecCowWrapper<'msg, B> {
    type Item = Cow<'msg, B>;
    type IntoIter = CowIter<'msg, B, std::slice::Iter<'msg, B::Owned>>;

    fn into_iter(self) -> Self::IntoIter {
        CowIter(<[B::Owned]>::iter(self.0), PhantomData)
    }
}
pub struct CowIter<'msg, B, Iter>(Iter, PhantomData<B>)
where
    B: 'msg + ?Sized + ToOwned,
    Iter: Iterator<Item = &'msg B::Owned>;
impl<'msg, B, Iter> Iterator for CowIter<'msg, B, Iter>
where
    B: 'msg + ?Sized + ToOwned,
    Iter: Iterator<Item = &'msg B::Owned>,
{
    type Item = Cow<'msg, B>;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|x| Cow::Borrowed(x.borrow()))
    }
}
impl<'msg, B> RepeatedField<'msg, Cow<'msg, B>> for VecCowWrapper<'msg, B> where
    B: 'msg + ?Sized + ToOwned
{
}

pub trait VecOrOptionOrBare<T> {
    fn push(&mut self, val: T);
    type Iter<'a>: Iterator<Item = &'a T>
    where
        T: 'a;
    fn iter(&self) -> Self::Iter<'_>;
}
impl<T> VecOrOptionOrBare<T> for Option<T> {
    fn push(&mut self, val: T) {
        *self = Some(val);
    }
    type Iter<'a>
    where
        T: 'a,
    = ::std::option::Iter<'a, T>;
    fn iter(&self) -> Self::Iter<'_> {
        Option::iter(self)
    }
}
impl<T> VecOrOptionOrBare<T> for Vec<T> {
    fn push(&mut self, val: T) {
        self.push(val);
    }
    type Iter<'a>
    where
        T: 'a,
    = ::std::slice::Iter<'a, T>;
    fn iter(&self) -> <Self as VecOrOptionOrBare<T>>::Iter<'_> {
        <[T]>::iter(self)
    }
}
impl<T> VecOrOptionOrBare<T> for T {
    fn push(&mut self, val: T) {
        *self = val;
    }
    type Iter<'a>
    where
        T: 'a,
    = ::std::iter::Once<&'a T>;
    fn iter(&self) -> Self::Iter<'_> {
        ::std::iter::once(self)
    }
}

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

// deser from iter methods

pub struct DeserFieldFromBytesIter<L, V>(PhantomData<(L, V)>);

impl<L, V> DeserFieldFromBytesIter<L, tags::wire::Variant<V>>
where
    L: tags::FieldLabelTag,
    tags::wire::Variant<V>: VariantTypeTag,
{
    pub fn deser_field<FieldType, I>(
        field: &mut FieldType,
        input: FieldData<&mut ScopedIter<I>>,
    ) -> Result<()>
    where
        FieldType:
            VecOrOptionOrBare<<tags::wire::Variant<V> as tags::NumericalTypeTag>::NativeType>,
        I: Iterator<Item = ::std::io::Result<u8>>,
    {
        match input {
            FieldData::Variant(v) => {
                let native_value = v.to_native::<tags::wire::Variant<V>>()?;
                if !L::DO_DEFAULT_CHECK || native_value != Default::default() {
                    field.push(native_value);
                }
            }
            FieldData::LengthDelimited(iter) => {
                let variants = Variants::new(iter);
                let values =
                    variants.map(|rv| rv.and_then(|v| v.to_native::<tags::wire::Variant<V>>()));
                for rvalue in values {
                    let native_value = rvalue?;
                    if !L::DO_DEFAULT_CHECK || native_value != Default::default() {
                        field.push(native_value);
                    }
                }
            }
            _ => Err(ErrorKind::UnexpectedWireType)?,
        }
        Ok(())
    }
}

impl<L, V> DeserFieldFromBytesIter<L, tags::wire::Bits32<V>>
where
    L: tags::FieldLabelTag,
    tags::wire::Bits32<V>: Bits32TypeTag,
{
    pub fn deser_field<FieldType, I>(
        field: &mut FieldType,
        input: FieldData<&mut ScopedIter<I>>,
    ) -> Result<()>
    where
        FieldType: VecOrOptionOrBare<<tags::wire::Bits32<V> as tags::NumericalTypeTag>::NativeType>,
        I: Iterator<Item = ::std::io::Result<u8>>,
    {
        if let FieldData::Bits32(bytes) = input {
            let native_value = tags::wire::Bits32::<V>::from_array(bytes);
            if !L::DO_DEFAULT_CHECK || native_value != Default::default() {
                field.push(native_value);
            }
        } else {
            Err(ErrorKind::UnexpectedWireType)?;
        }
        Ok(())
    }
}

impl<L, V> DeserFieldFromBytesIter<L, tags::wire::Bits64<V>>
where
    L: tags::FieldLabelTag,
    tags::wire::Bits64<V>: Bits64TypeTag,
{
    pub fn deser_field<FieldType, I>(
        field: &mut FieldType,
        input: FieldData<&mut ScopedIter<I>>,
    ) -> Result<()>
    where
        FieldType: VecOrOptionOrBare<<tags::wire::Bits64<V> as tags::NumericalTypeTag>::NativeType>,
        I: Iterator<Item = ::std::io::Result<u8>>,
    {
        if let FieldData::Bits64(bytes) = input {
            let native_value = tags::wire::Bits64::<V>::from_array(bytes);
            if !L::DO_DEFAULT_CHECK || native_value != Default::default() {
                field.push(native_value);
            }
        } else {
            Err(ErrorKind::UnexpectedWireType)?;
        }
        Ok(())
    }
}

impl<L> DeserFieldFromBytesIter<L, tags::String>
where
    L: tags::FieldLabelTag,
{
    pub fn deser_field<FieldType, I>(
        field: &mut FieldType,
        input: FieldData<&mut ScopedIter<I>>,
    ) -> Result<()>
    where
        FieldType: VecOrOptionOrBare<String>,
        I: Iterator<Item = ::std::io::Result<u8>>,
    {
        if let FieldData::LengthDelimited(iter) = input {
            let string = String::from_utf8(iter.collect::<::std::io::Result<Vec<_>>>()?)
                .map_err(|e| ErrorKind::InvalidUtf8(e))?;
            if !L::DO_DEFAULT_CHECK || !string.is_empty() {
                field.push(string);
            }
        } else {
            Err(ErrorKind::UnexpectedWireType)?;
        }
        Ok(())
    }
}

impl<L> DeserFieldFromBytesIter<L, tags::Bytes>
where
    L: tags::FieldLabelTag,
{
    pub fn deser_field<FieldType, I>(
        field: &mut FieldType,
        input: FieldData<&mut ScopedIter<I>>,
    ) -> Result<()>
    where
        FieldType: VecOrOptionOrBare<Vec<u8>>,
        I: Iterator<Item = ::std::io::Result<u8>>,
    {
        if let FieldData::LengthDelimited(iter) = input {
            let bytes = iter.collect::<::std::io::Result<Vec<_>>>()?;
            if !L::DO_DEFAULT_CHECK || !bytes.is_empty() {
                field.push(bytes);
            }
        } else {
            Err(ErrorKind::UnexpectedWireType)?;
        }
        Ok(())
    }
}

impl<M, _1, _2> DeserFieldFromBytesIter<tags::NonRepeated<_1, _2>, tags::Message<M>>
where
    M: Message + DeserFieldsFromBytesIter + Default,
{
    pub fn deser_field<I>(
        field: &mut Option<Box<M>>,
        input: FieldData<&mut ScopedIter<I>>,
    ) -> Result<()>
    where
        I: Iterator<Item = ::std::io::Result<u8>>,
    {
        if let FieldData::LengthDelimited(mut iter) = input {
            let msg = field.get_or_insert_with(Default::default);
            crate::de::from_iter::deser_from_scoped_iter(msg.deref_mut(), &mut iter)?;
        } else {
            Err(ErrorKind::UnexpectedWireType)?;
        }
        Ok(())
    }
}

impl<M> DeserFieldFromBytesIter<tags::Repeated, tags::Message<M>>
where
    M: Message + DeserFieldsFromBytesIter + Default,
{
    pub fn deser_field<I>(field: &mut Vec<M>, input: FieldData<&mut ScopedIter<I>>) -> Result<()>
    where
        I: Iterator<Item = ::std::io::Result<u8>>,
    {
        if let FieldData::LengthDelimited(mut iter) = input {
            field.push(Default::default());
            let msg = field.last_mut().unwrap();
            crate::de::from_iter::deser_from_scoped_iter(msg, &mut iter)?;
        } else {
            Err(ErrorKind::UnexpectedWireType)?;
        }
        Ok(())
    }
}

// ser to Write methods

pub struct SerFieldToIoWrite<L, V>(PhantomData<(L, V)>);

impl<V, _1, _2> SerFieldToIoWrite<tags::NonRepeated<_1, _2>, tags::wire::Variant<V>>
where
    tags::NonRepeated<_1, _2>: tags::FieldLabelTag,
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
            if !tags::NonRepeated::<_1, _2>::DO_DEFAULT_CHECK || item.clone() != Default::default()
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
            .map_err(|_| ::puroro::ErrorKind::TooLongToSerialize)?;
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
        FieldType: VecOrOptionOrBare<Vec<u8>>,
        W: Write,
    {
        for item in field.iter() {
            if !L::DO_DEFAULT_CHECK || !item.is_empty() {
                write_field_number_and_wire_type(out, number, WireType::LengthDelimited)?;
                let len_i32: i32 = item
                    .len()
                    .try_into()
                    .map_err(|_| ::puroro::ErrorKind::TooLongToSerialize)?;
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
        FieldType: VecOrOptionOrBare<String>,
        W: Write,
    {
        for item in field.iter() {
            if !L::DO_DEFAULT_CHECK || !item.is_empty() {
                write_field_number_and_wire_type(out, number, WireType::LengthDelimited)?;
                let len_i32: i32 = item
                    .len()
                    .try_into()
                    .map_err(|_| ::puroro::ErrorKind::TooLongToSerialize)?;
                Variant::from_i32(len_i32)?.encode_bytes(out)?;
                out.write(item.as_bytes())?;
            }
        }
        Ok(())
    }
}

impl<M, _1, _2> SerFieldToIoWrite<tags::NonRepeated<_1, _2>, tags::Message<M>>
where
    M: SerToIoWrite,
{
    pub fn ser_field<W>(field: &Option<Box<M>>, number: i32, out: &mut W) -> Result<()>
    where
        W: Write,
    {
        if let Some(boxed) = field {
            let len = {
                let mut null_out = NullWrite::new();
                <M as SerToIoWrite>::ser(boxed.deref(), &mut null_out)?;
                null_out.len()
            };
            let len_i32: i32 = len
                .try_into()
                .map_err(|_| ::puroro::ErrorKind::TooLongToSerialize)?;
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
                .map_err(|_| ::puroro::ErrorKind::TooLongToSerialize)?;
            write_field_number_and_wire_type(out, number, WireType::LengthDelimited)?;
            Variant::from_i32(len_i32)?.encode_bytes(out)?;
            <M as SerToIoWrite>::ser(item, out)?;
        }
        Ok(())
    }
}
