use ::itertools::Itertools;
use ::num_traits::{One, PrimInt, Zero};
use std::ops::BitOrAssign;

trait Unsigned: PrimInt + Zero + One + BitOrAssign {
    fn from_u8(from: u8) -> Self;
}
impl Unsigned for u32 {
    fn from_u8(from: u8) -> Self {
        from as u32
    }
}
impl Unsigned for u64 {
    fn from_u8(from: u8) -> Self {
        from as u64
    }
}

#[derive(::thiserror::Error, Debug, PartialEq)]
pub(crate) enum ParseError {
    #[error("A value of an integer type has too large or too small value.")]
    IntegerOverflow,
    #[error("Unexpected field type. e.g. Expected int32, but found a Message field")]
    UnexpectedFieldType,
}
type Result<T> = std::result::Result<T, ParseError>;

#[derive(::thiserror::Error, Debug, PartialEq)]
pub(crate) enum LexerError {
    #[error("The input binary has terminated in irregular position.")]
    UnexpectedInputTermination,
}
type LexResult<T> = std::result::Result<T, LexerError>;

#[derive(Debug)]
struct Variant<'a, I>(I)
where
    I: Iterator<Item = &'a u8>;
impl<'a, I> Variant<'a, I>
where
    I: Iterator<Item = &'a u8> + Clone,
{
    pub(crate) fn from_bytes(mut bytes: I) -> Result<(Self, I)> {}
}

impl<'a, I> Variant<'a, I> {
    fn to_unsigned<T: Unsigned>(&self) -> Result<T> {
        debug_assert!(self.0.len() >= 1);
        let mut value: T = T::zero();
        let bits: usize = std::mem::size_of::<T>() * 8;
        if self.0.len() > (bits + 6) / 7 {
            return Err(ParseError::IntegerOverflow);
        }
        for i in 0..(self.0.len() - 1) {
            value |= T::from_u8(0x7f & self.0[i]) << (i * 7);
        }
        // last byte for this int size.
        let i = self.0.len() - 1;
        let remaining_bits = (bits - i * 7).min(7);
        debug_assert!(remaining_bits <= 7);
        let remaining_bits_mask = ((1u32 << remaining_bits) - 1) as u8;
        if (self.0[i] & !remaining_bits_mask) != 0 {
            return Err(ParseError::IntegerOverflow);
        }
        value |= T::from_u8(self.0[i]) << (i * 7);
        Ok(value)
    }
    pub(crate) fn to_u32(&self) -> Result<u32> {
        self.to_unsigned::<u32>()
    }
    pub(crate) fn to_u64(&self) -> Result<u64> {
        self.to_unsigned::<u64>()
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        self.0.len()
    }
}

#[derive(Clone, Debug)]
struct ParseState<'a> {
    cur: &'a [u8],
}

impl<'a> ParseState<'a> {
    fn try_parse_message<T, H: ParseEventHandler>(&self, handler: &mut H) -> Result<T> {
        todo!()
    }

    fn try_parse_as_packed_variants<T: ParseEventHandler>(&self, handler: &T) -> Result<()> {
        todo!()
    }
}

trait ParseEventHandler {
    fn start_parse_message<T>(&mut self, state: ParseState);

    fn met_variant_field(&mut self, field_number: usize, value: &Variant) -> Result<()>;
    fn met_binary_field(&mut self, field_number: usize, state: ParseState) -> Result<()>;
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_variant_from_bytes() {
        fn expect_ok(input: &[u8], expected_len: usize, expected_remaining: &[u8]) {
            let result = Variant::from_bytes(input);
            assert!(result.is_ok());
            let (variant, remaining) = result.unwrap();
            assert_eq!(variant.len(), expected_len);
            assert_eq!(remaining, expected_remaining);
        }
        fn expect_err(input: &[u8], expected_err: ParseError) {
            let result = Variant::from_bytes(input);
            assert!(result.is_err());
            assert_eq!(result.unwrap_err(), expected_err);
        }
        expect_ok(&[0x00], 1, &[]);
        expect_ok(&[0x00, 0x80, 0x81], 1, &[0x80, 0x81]);
        expect_ok(&[0x80, 0x40], 2, &[]);
        expect_ok(&[0x80, 0x00, 0x00, 0x40], 4, &[]);
        expect_err(&[0x80], ParseError::UnexpectedInputTermination);
    }

    #[test]
    fn test_variant_unsigned() {
        fn get_u32(input: &[u8]) -> Result<u32> {
            let (v, _) = Variant::from_bytes(input)?;
            v.to_u32()
        }
        assert_eq!(get_u32(&[0x00]), Ok(0));
        assert_eq!(get_u32(&[0x01]), Ok(1));
        assert_eq!(get_u32(&[0x7F]), Ok(0x7F));
        assert_eq!(get_u32(&[0x80, 0x01]), Ok(0x80));
        assert_eq!(get_u32(&[0xFF, 0xFF, 0xFF, 0xFF, 0x0F]), Ok(0xFFFFFFFF));
        assert_eq!(
            get_u32(&[0xFF, 0xFF, 0xFF, 0xFF, 0x1F]),
            Err(ParseError::IntegerOverflow)
        );
        assert_eq!(
            get_u32(&[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F]),
            Err(ParseError::IntegerOverflow)
        );
    }
}
