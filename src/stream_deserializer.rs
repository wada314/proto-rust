use ::itertools::Itertools;
use std::convert::TryFrom;
use std::io::{Error as IoError, Result as IoResult};
use std::marker::PhantomData;
use std::num::TryFromIntError;

#[derive(::thiserror::Error, Debug)]
pub(crate) enum DeserializeError {
    #[error("The input binary has terminated in irregular position.")]
    UnexpectedInputTermination,
    #[error("A variant integer type has too large or too small value.")]
    IntegerOverflow(#[from] std::num::TryFromIntError),
    #[error("A variant integer type is longer than 10 bytes.")]
    TooLargeVariant,
    #[error("Unexpected field type. e.g. Expected int32, but found a Message field")]
    UnexpectedFieldType,
    #[error("The bytestream iterator returned an error: {0}")]
    IteratorError(#[from] IoError),
}
type Result<T> = std::result::Result<T, DeserializeError>;

#[derive(Debug)]
struct Variant(u64);
impl Variant {
    pub(crate) fn from_bytes<T>(bytes: &mut T) -> Result<Self>
    where
        T: Iterator<Item = IoResult<u8>>,
    {
        let mut x = 0u64;
        for i in 0..9 {
            match bytes.next() {
                Some(maybe_byte) => {
                    let byte = maybe_byte?;
                    x |= ((byte & 0x7F) as u64) << (i * 7);
                    if byte < 0x80 {
                        return Ok(Variant(x));
                    }
                }
                None => {
                    return Err(DeserializeError::UnexpectedInputTermination);
                }
            }
        }
        // i == 9, so now checking a last MSBit.
        match bytes.next() {
            Some(maybe_byte) => {
                let byte = maybe_byte?;
                x |= ((byte & 0x01) as u64) << 63;
                if byte & 0xFE != 0 {
                    return Err(DeserializeError::TooLargeVariant);
                } else {
                    return Ok(Variant(x));
                }
            }
            None => {
                return Err(DeserializeError::UnexpectedInputTermination);
            }
        }
    }

    pub(crate) fn to_u32(&self) -> Result<u32> {
        Ok(u32::try_from(self.0)?)
    }
    pub(crate) fn to_u64(&self) -> Result<u64> {
        Ok(self.0)
    }
}

struct ParseState<I>
where
    I: Iterator<Item = IoResult<u8>>,
{
    iter: I,
}

impl<I> ParseState<I>
where
    I: Iterator<Item = IoResult<u8>>,
{
    fn try_parse_message<T, H: ParseEventHandler<I>>(&self, handler: &mut H) -> Result<T> {
        todo!()
    }

    fn try_parse_as_packed_variants<T: ParseEventHandler<I>>(&self, handler: &T) -> Result<()> {
        todo!()
    }
}

trait ParseEventHandler<I>
where
    I: Iterator<Item = IoResult<u8>>,
{
    fn start_parse_message(&mut self, state: ParseState<I>);

    fn met_variant_field(&mut self, field_number: usize, value: &Variant) -> Result<()>;
    fn met_binary_field(&mut self, field_number: usize, state: ParseState<I>) -> Result<()>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::ErrorKind;
    const IO_ERROR1: IoError = IoError::new(ErrorKind::InvalidData, "");
    const IO_ERROR2: IoError = IoError::new(ErrorKind::NotConnected, "");

    fn into_iter<'a>(slice: &'a [u8]) -> impl Iterator<Item = IoResult<u8>> + 'a {
        slice.iter().copied().map(|x| Ok(x))
    }
    fn collect_iter<I: Iterator<Item = IoResult<u8>>>(iter: I) -> Vec<u8> {
        iter.map(|r| r.unwrap()).collect::<Vec<_>>()
    }

    #[test]
    fn test_variant_from_bytes() {
        fn expect_ok(input: &[u8], expected_value: u64, expected_remaining: &[u8]) {
            let mut iter = into_iter(input);
            let result = Variant::from_bytes(&mut iter);
            assert!(result.is_ok());
            let variant = result.unwrap();
            assert_eq!(variant.0, expected_value);
            assert_eq!(collect_iter(iter), expected_remaining);
        }
        fn get_err(input: Vec<IoResult<u8>>) -> DeserializeError {
            let mut iter = input.into_iter();
            let result = Variant::from_bytes(&mut iter);
            assert!(result.is_err());
            result.unwrap_err()
        }
        expect_ok(&[0x00], 0, &[]);
        expect_ok(&[0x00, 0x80, 0x81], 0, &[0x80, 0x81]);
        expect_ok(&[0x80, 0x40], 0b1000000_0000000, &[]);
        expect_ok(
            &[0x80, 0x80, 0x80, 0x40],
            0b1000000_0000000_0000000_0000000,
            &[],
        );
        assert!(matches!(
            get_err(vec![Ok(0x00)]),
            DeserializeError::UnexpectedInputTermination
        ));
        assert!(matches!(
            get_err(vec![Err(IO_ERROR1)]),
            DeserializeError::IteratorError(_)
        ));
    }

    #[test]
    fn test_variant_unsigned() {
        fn get_u32(input: &[u8]) -> Result<u32> {
            let mut iter = into_iter(input);
            let v = Variant::from_bytes(&mut iter)?;
            assert_eq!(collect_iter(iter), Vec::<u8>::new());
            v.to_u32()
        }
        assert_eq!(get_u32(&[0x00]).unwrap(), 0);
        assert_eq!(get_u32(&[0x01]).unwrap(), 1);
        assert_eq!(get_u32(&[0x7F]).unwrap(), 0x7F);
        assert_eq!(get_u32(&[0x80, 0x01]).unwrap(), 0x80);
        assert_eq!(
            get_u32(&[0xFF, 0xFF, 0xFF, 0xFF, 0x0F]).unwrap(),
            0xFFFFFFFF
        );
        assert!(matches!(
            get_u32(&[0xFF, 0xFF, 0xFF, 0xFF, 0x1F]).unwrap_err(),
            DeserializeError::IntegerOverflow(_)
        ));
        assert!(matches!(
            get_u32(&[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F]).unwrap_err(),
            DeserializeError::IntegerOverflow(_)
        ));
    }
}
