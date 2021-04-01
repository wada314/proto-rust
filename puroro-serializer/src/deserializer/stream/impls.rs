use ::either::Either;
use ::num_traits::FromPrimitive;
use std::io::Result as IoResult;

use super::iters::{BytesIterator, CharsIterator, VariantsIterator};
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
    fn deserialize<H: MessageHandler>(mut self, handler: H) -> Result<H::Target> {
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
    sub_deserializer_expected_finish_pos: Option<usize>,
}
impl<'a, I> LengthDelimitedDeserializerImpl<'a, I>
where
    I: Iterator<Item = IoResult<u8>>,
{
    pub(crate) fn new(indexed_iter: &'a mut IndexedIterator<I>, bytes_len: Option<usize>) -> Self {
        Self {
            indexed_iter,
            bytes_len,
            #[cfg(debug_assertions)]
            sub_deserializer_expected_finish_pos: None,
        }
    }
    fn make_sub_deserializer<'b>(
        &'b mut self,
        new_length: usize,
    ) -> LengthDelimitedDeserializerImpl<'b, I>
    where
        'a: 'b,
    {
        assert!(
            self.sub_deserializer_expected_finish_pos.is_none(),
             "The previous field is not preccessed yet. i.e. The iterator is still in the previous field."
        );
        self.sub_deserializer_expected_finish_pos = Some(new_length + self.indexed_iter.index());
        LengthDelimitedDeserializerImpl {
            indexed_iter: self.indexed_iter,
            bytes_len: Some(new_length),
            #[cfg(debug_assertions)]
            sub_deserializer_expected_finish_pos: None,
        }
    }

    // May expectedly fail if reached to the eof
    fn try_get_wire_type_and_field_number(&mut self) -> Result<Option<(WireType, usize)>> {
        let mut peekable = self.indexed_iter.by_ref().peekable();
        if let None = peekable.peek() {
            // Found EOF at first byte. Successfull failure.
            return Ok(None);
        }
        let key = Variant::decode_bytes(&mut peekable)?.to_usize()?;
        Ok(Some((
            WireType::from_usize(key & 0x07).ok_or(PuroroError::InvalidWireType)?,
            (key >> 3),
        )))
    }

    fn eat_one_byte(&mut self) -> Result<u8> {
        self.indexed_iter
            .next()
            .ok_or(PuroroError::UnexpectedInputTermination)
            .and_then(|r| r.map_err(|e| e.into()))
    }
}

impl<'a, I> Iterator for LengthDelimitedDeserializerImpl<'a, I>
where
    I: Iterator<Item = IoResult<u8>>,
{
    type Item = <I as Iterator>::Item;
    #[cfg(debug_assertions)]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(expected_pos) = self.sub_deserializer_expected_finish_pos.take() {
            assert_eq!(
                expected_pos,
                self.indexed_iter.index(),
                concat!(
                    "The previous field is not finished yet! ",
                    "Since this deserializer uses an Iterator as input, ",
                    "you need to make sure the previous field has read the ",
                    "all its contents from the input Iterator."
                )
            );
        }
        self.indexed_iter.next()
    }
    #[cfg(not(debug_assertions))]
    fn next(&mut self) -> Option<Self::Item> {
        self.indexed_iter.next()
    }
}

impl<'a, I> LengthDelimitedDeserializer<'a> for LengthDelimitedDeserializerImpl<'a, I>
where
    I: Iterator<Item = IoResult<u8>>,
{
    fn deserialize_as_message<H: MessageHandler>(mut self, mut handler: H) -> Result<H::Target> {
        let start_pos = self.indexed_iter.index();
        loop {
            // Check message length if possible
            if let Some(message_length) = self.bytes_len {
                if start_pos + message_length <= self.indexed_iter.index() {
                    break;
                }
            }

            // get field number, wire type
            let (wire_type, field_number) = match self.try_get_wire_type_and_field_number() {
                Ok(Some(x)) => x,
                Ok(None) => {
                    break;
                } // This is ok. finish This message deserialization.
                Err(e) => {
                    return Err(e);
                }
            };

            match wire_type {
                WireType::Variant => {
                    let variant = Variant::decode_bytes(&mut self.indexed_iter)?;
                    handler.deserialized_variant(field_number, variant)?;
                }
                WireType::LengthDelimited => {
                    let field_length = Variant::decode_bytes(&mut self.indexed_iter)?.to_usize()?;
                    let deserializer_for_inner = self.make_sub_deserializer(field_length);
                    handler
                        .deserialize_length_delimited_field(deserializer_for_inner, field_number)?;
                }
                WireType::Bytes32 => {
                    let v0 = self.eat_one_byte()?;
                    let v1 = self.eat_one_byte()?;
                    let v2 = self.eat_one_byte()?;
                    let v3 = self.eat_one_byte()?;
                    handler.deserialized_32bits(field_number, [v0, v1, v2, v3])?;
                }
                WireType::Bytes64 => {
                    let v0 = self.eat_one_byte()?;
                    let v1 = self.eat_one_byte()?;
                    let v2 = self.eat_one_byte()?;
                    let v3 = self.eat_one_byte()?;
                    let v4 = self.eat_one_byte()?;
                    let v5 = self.eat_one_byte()?;
                    let v6 = self.eat_one_byte()?;
                    let v7 = self.eat_one_byte()?;
                    handler.deserialized_64bits(field_number, [v0, v1, v2, v3, v4, v5, v6, v7])?;
                }
                _ => {
                    unimplemented!("WIP for group support");
                }
            }
        }

        handler.finish()
    }

    type BytesIterator = BytesIterator<Self>;
    fn deserialize_as_bytes(self) -> Self::BytesIterator {
        BytesIterator::new(self)
    }

    type CharsIterator = CharsIterator<Self>;
    fn deserialize_as_chars(self) -> Self::CharsIterator {
        CharsIterator::new(self)
    }

    type VariantsIterator = VariantsIterator<Self>;
    fn deserialize_as_variants(self) -> Self::VariantsIterator {
        VariantsIterator::new(self)
    }

    fn leave_as_unknown(self) -> Result<DelayedLengthDelimitedDeserializer> {
        Ok(DelayedLengthDelimitedDeserializer::new(
            self.indexed_iter
                .collect::<IoResult<Vec<_>>>()
                .map_err(|e| PuroroError::from(e))?,
        ))
    }
}

pub(crate) struct IndexedIterator<I> {
    index: usize,
    iter: I,
}
impl<I> Iterator for IndexedIterator<I>
where
    I: Iterator,
{
    type Item = <I as Iterator>::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.index += 1;
        self.iter.next()
    }
}
impl<I> IndexedIterator<I> {
    pub(crate) fn new(iter: I) -> Self {
        IndexedIterator { index: 0, iter }
    }
    fn index(&self) -> usize {
        self.index
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deserialize_samples_test1() {
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
        impl MessageHandler for Test1 {
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
    fn deserialize_samples_test2() {
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
        impl MessageHandler for Test2 {
            type Target = Self;
            fn finish(self) -> Result<Self::Target> {
                Ok(self)
            }
            fn deserialize_length_delimited_field<'a, D: LengthDelimitedDeserializer<'a>>(
                &mut self,
                deserializer: D,
                field_number: usize,
            ) -> Result<()> {
                assert_eq!(field_number, 2);
                self.b = deserializer
                    .deserialize_as_chars()
                    .collect::<Result<String>>()?;
                Ok(())
            }
        }

        let handler = Test2::default();
        let deserializer = DeserializerImpl::<_>::new(input.bytes());
        let result = deserializer.deserialize(handler);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().b, "testing");
    }

    #[test]
    fn deserialize_samples_test3() {
        // https://developers.google.com/protocol-buffers/docs/encoding#embedded
        // message Test1 {
        //   optional int32 a = 1;
        // }
        // message Test3 {
        //   optional Test1 c = 3;
        // }
        // a = 150
        let input: &[u8] = &[0x1a, 0x03, 0x08, 0x96, 0x01];
        #[derive(Default, PartialEq)]
        struct Test1 {
            a: i32,
        }
        #[derive(Default, PartialEq)]
        struct Test3 {
            c: Test1,
        }

        impl MessageHandler for Test1 {
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
        impl MessageHandler for Test3 {
            type Target = Self;
            fn finish(self) -> Result<Self::Target> {
                Ok(self)
            }
            fn deserialize_length_delimited_field<'a, D: LengthDelimitedDeserializer<'a>>(
                &mut self,
                deserializer: D,
                field_number: usize,
            ) -> Result<()> {
                assert_eq!(3, field_number);
                self.c = deserializer.deserialize_as_message(Test1::default())?;
                Ok(())
            }
        }

        let handler = Test3::default();
        let deserializer = DeserializerImpl::<_>::new(input.bytes());
        let result = deserializer.deserialize(handler);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().c.a, 150);
    }

    #[test]
    fn deserialize_samples_test4() {
        // https://developers.google.com/protocol-buffers/docs/encoding#packed
        // message Test4 {
        //   repeated int32 d = 4 [packed=true];
        // }
        // d = [3, 270, 86942]
        let input: &[u8] = &[0x22, 0x06, 0x03, 0x8E, 0x02, 0x9E, 0xA7, 0x05];
        #[derive(Default, PartialEq)]
        struct Test4 {
            d: Vec<i32>,
        }
        impl MessageHandler for Test4 {
            type Target = Self;
            fn finish(self) -> Result<Self::Target> {
                Ok(self)
            }
            fn deserialize_length_delimited_field<'a, D: LengthDelimitedDeserializer<'a>>(
                &mut self,
                deserializer: D,
                field_number: usize,
            ) -> Result<()> {
                assert_eq!(4, field_number);
                self.d = deserializer
                    .deserialize_as_variants()
                    .map(|r| r.and_then(|v| v.to_i32()))
                    .collect::<Result<Vec<_>>>()?;
                Ok(())
            }
        }

        let handler = Test4::default();
        let deserializer = DeserializerImpl::<_>::new(input.bytes());
        let result = deserializer.deserialize(handler);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().d, [3, 270, 86942]);
    }
}
