use ::num_traits::FromPrimitive;
use std::io::Result as IoResult;

use super::*;

pub(crate) struct DeserializerImpl<I>
where
    I: Iterator<Item = IoResult<u8>>,
{
    indexed_iter: IndexedIterator<I>,
}
impl<I> DeserializerImpl<I>
where
    I: Iterator<Item = IoResult<u8>>,
{
    pub(crate) fn new(iter: I) -> Self {
        Self {
            indexed_iter: IndexedIterator::new(iter),
        }
    }
}
impl<I> Deserializer for DeserializerImpl<I>
where
    I: Iterator<Item = IoResult<u8>>,
{
    fn deserialize<H: Handler>(mut self, handler: H) -> Result<H::Target> {
        LengthDelimitedDeserializerImpl::new(&mut self.indexed_iter, None)
            .deserialize_as_message(handler)
    }
}

pub(crate) struct LengthDelimitedDeserializerImpl<'a, I>
where
    I: Iterator<Item = IoResult<u8>>,
{
    indexed_iter: &'a mut IndexedIterator<I>,
    bytes_len: Option<usize>,
}
impl<'a, I> LengthDelimitedDeserializerImpl<'a, I>
where
    I: Iterator<Item = IoResult<u8>>,
{
    pub(crate) fn new(indexed_iter: &'a mut IndexedIterator<I>, bytes_len: Option<usize>) -> Self {
        Self {
            indexed_iter,
            bytes_len,
        }
    }
    fn make_sub_deserializer<'b>(
        &'b mut self,
        new_length: usize,
    ) -> LengthDelimitedDeserializerImpl<'b, I>
    where
        'a: 'b,
    {
        LengthDelimitedDeserializerImpl {
            indexed_iter: self.indexed_iter,
            bytes_len: Some(new_length),
        }
    }

    // May expectedly fail if reached to the eof
    fn try_get_wire_type_and_field_number(&mut self) -> Result<(WireType, usize)> {
        let mut peekable = self.indexed_iter.by_ref().peekable();
        if let None = peekable.peek() {
            // Found EOF at first byte. Successfull failure.
            return Err(DeserializeError::ExpectedInputTermination);
        }
        let key = Variant::from_bytes(&mut peekable)?.to_usize()?;
        Ok((WireType::from_usize(key & 0x07).unwrap(), (key >> 3)))
    }
}

impl<'a, I> LengthDelimitedDeserializer for LengthDelimitedDeserializerImpl<'a, I>
where
    I: Iterator<Item = IoResult<u8>>,
{
    fn deserialize_as_message<H: Handler>(mut self, mut handler: H) -> Result<H::Target> {
        let start_pos = self.indexed_iter.index();
        loop {
            // Check message length if possible
            if let Some(message_length) = self.bytes_len {
                if start_pos + message_length >= self.indexed_iter.index() {
                    break;
                }
            }

            // get field number, wire type
            let (wire_type, field_number) = match self.try_get_wire_type_and_field_number() {
                Ok(x) => x,
                Err(DeserializeError::ExpectedInputTermination) => {
                    break;
                } // This is ok. finish This message deserialization.
                Err(e) => {
                    return Err(e);
                }
            };

            match wire_type {
                WireType::Variant => {
                    let variant = Variant::from_bytes(&mut self.indexed_iter)?;
                    handler.deserialized_variant(field_number, variant)?;
                }
                WireType::LengthDelimited => {
                    let field_length = Variant::from_bytes(&mut self.indexed_iter)?.to_usize()?;
                    let deserializer_for_inner = self.make_sub_deserializer(field_length);
                    handler.deserialize_length_delimited_field(
                        deserializer_for_inner,
                        field_number,
                        field_length,
                    )?;
                }
                _ => {
                    todo!()
                }
            }
        }

        handler.finish()
    }

    fn deserialize_as_string<H>(self, handler: H) -> Result<()>
    where
        H: RepeatedFieldHandler<char>,
    {
        let start_pos = self.indexed_iter.index();
        if let Some(length) = self.bytes_len {
            let iter = CharsIterator::new(self.indexed_iter.by_ref().take(length));
            handler.handle(iter)?;
        } else {
            let iter = CharsIterator::new(self.indexed_iter.by_ref());
            handler.handle(iter)?;
        }
        let end_pos = self.indexed_iter.index();
        if let Some(length) = self.bytes_len {
            if end_pos - start_pos == length {
                Ok(())
            } else {
                Err(DeserializeError::InvalidFieldLength)
            }
        } else {
            Ok(())
        }
    }

    fn deserialize_as_bytes<H>(self, handler: H) -> Result<()>
    where
        H: RepeatedFieldHandler<u8>,
    {
        let start_pos = self.indexed_iter.index();
        if let Some(length) = self.bytes_len {
            let iter = self
                .indexed_iter
                .by_ref()
                .take(length)
                .map(|r| r.map_err(|e| e.into()));
            handler.handle(iter)?;
        } else {
            let iter = self.indexed_iter.by_ref().map(|r| r.map_err(|e| e.into()));
            handler.handle(iter)?;
        }
        let end_pos = self.indexed_iter.index();
        if let Some(length) = self.bytes_len {
            if end_pos - start_pos == length {
                Ok(())
            } else {
                Err(DeserializeError::InvalidFieldLength)
            }
        } else {
            Ok(())
        }
    }
    fn deserialize_as_variants<H>(self, handler: H) -> Result<()>
    where
        H: RepeatedFieldHandler<Variant>,
    {
        let start_pos = self.indexed_iter.index();
        if let Some(length) = self.bytes_len {
            let iter = VariantsIterator::new(self.indexed_iter.by_ref().take(length));
            handler.handle(iter)?;
        } else {
            let iter = VariantsIterator::new(self.indexed_iter.by_ref());
            handler.handle(iter)?;
        }
        let end_pos = self.indexed_iter.index();
        if let Some(length) = self.bytes_len {
            if end_pos - start_pos == length {
                Ok(())
            } else {
                Err(DeserializeError::InvalidFieldLength)
            }
        } else {
            Ok(())
        }
    }
}

pub struct CharsIterator<T: Iterator<Item = IoResult<u8>>> {
    iter: ::utf8_decode::UnsafeDecoder<T>,
}
impl<T: Iterator<Item = IoResult<u8>>> CharsIterator<T> {
    pub fn new(iter: T) -> Self {
        Self {
            iter: ::utf8_decode::UnsafeDecoder::new(iter),
        }
    }
}
impl<T: Iterator<Item = IoResult<u8>>> Iterator for CharsIterator<T> {
    type Item = Result<char>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|r| r.map_err(|e| e.into()))
    }
}

pub struct VariantsIterator<I: Iterator<Item = IoResult<u8>>> {
    iter: I,
}
impl<I: Iterator<Item = IoResult<u8>>> VariantsIterator<I> {
    pub fn new(iter: I) -> Self {
        Self { iter }
    }
}
impl<I: Iterator<Item = IoResult<u8>>> Iterator for VariantsIterator<I> {
    type Item = Result<Variant>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut peekable = self.iter.peekable();
        if let None = peekable.peek() {
            return None;
        }
        Some(Variant::from_bytes(&mut peekable))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn do_parse_test_variant() {
        // https://developers.google.com/protocol-buffers/docs/encoding#simple
        // message Test1 {
        //   optional int32 a = 1;
        // }
        // a = 150
        let input: &[u8] = &[0x08, 0x96, 0x01];
        #[derive(Default, PartialEq)]
        struct Test1 {
            a: i32,
        }
        impl Handler for Test1 {
            type Target = Self;
            fn finish(self) -> Result<Self::Target> {
                Ok(self)
            }
            fn deserialized_variant(
                &mut self,
                field_number: usize,
                variant: Variant,
            ) -> Result<()> {
                assert_eq!(1, field_number);
                self.a = variant.to_i32()?;
                Ok(())
            }
        }

        let handler = Test1::default();
        let deserializer = DeserializerImpl::<_>::new(input.bytes());
        let result = deserializer.deserialize(handler);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().a, 150);
    }

    #[test]
    fn do_parse_test_string() {
        // https://developers.google.com/protocol-buffers/docs/encoding#strings
        // message Test2 {
        //   optional string b = 2;
        // }
        // b = "testing"
        let input: &[u8] = &[0x12, 0x07, 0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67];
        #[derive(Default, PartialEq)]
        struct Test2 {
            b: String,
        }
        impl Handler for Test2 {
            type Target = Self;
            fn finish(self) -> Result<Self::Target> {
                Ok(self)
            }
            fn deserialize_length_delimited_field<D: LengthDelimitedDeserializer>(
                &mut self,
                deserializer: D,
                field_number: usize,
                _length: usize,
            ) -> Result<()> {
                assert_eq!(field_number, 2);
                deserializer.deserialize_as_string(|s| {
                    self.b = s;
                    Ok(())
                })?;
                Ok(())
            }
        }

        let handler = Test2::default();
        let deserializer = DeserializerImpl::<_>::new(input.bytes());
        let result = deserializer.deserialize(handler);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().b, "testing");
    }
}
