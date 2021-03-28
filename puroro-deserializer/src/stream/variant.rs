use super::{PuroroError, Result};
use std::convert::TryFrom;
use std::io::Result as IoResult;

#[derive(Debug, Default, Clone)]
pub struct Variant([u8; 8]);
impl Variant {
    pub fn from_bytes<I>(bytes: &mut I) -> Result<Self>
    where
        I: Iterator<Item = IoResult<u8>>,
    {
        let mut x = 0u64;
        for i in 0..9 {
            match bytes.next() {
                Some(maybe_byte) => {
                    let byte = maybe_byte?;
                    x |= ((byte & 0x7F) as u64) << (i * 7);
                    if byte < 0x80 {
                        return Ok(Variant(x.to_ne_bytes()));
                    }
                }
                None => {
                    return Err(PuroroError::UnexpectedInputTermination);
                }
            }
        }
        // i == 9, so now checking a last MSBit.
        match bytes.next() {
            Some(maybe_byte) => {
                let byte = maybe_byte?;
                x |= ((byte & 0x01) as u64) << 63;
                if byte & 0xFE != 0 {
                    return Err(PuroroError::TooLargeVariant);
                } else {
                    return Ok(Variant(x.to_ne_bytes()));
                }
            }
            None => {
                return Err(PuroroError::UnexpectedInputTermination);
            }
        }
    }
    fn to_sint(&self) -> Result<i64> {
        // decode zigzag encoding for sint32 and sint64.
        let x = self.to_i64()?;
        Ok((x ^ (0 - (x & 1))) >> 1)
    }

    pub fn to_u32(&self) -> Result<u32> {
        Ok(u32::try_from(u64::from_ne_bytes(self.0))?)
    }
    pub fn to_u64(&self) -> Result<u64> {
        Ok(u64::from_ne_bytes(self.0))
    }
    pub fn to_usize(&self) -> Result<usize> {
        Ok(usize::try_from(u64::from_ne_bytes(self.0))?)
    }
    pub fn to_i32(&self) -> Result<i32> {
        Ok(i32::try_from(i64::from_ne_bytes(self.0))?)
    }
    pub fn to_i64(&self) -> Result<i64> {
        Ok(i64::from_ne_bytes(self.0))
    }
    pub fn to_si32(&self) -> Result<i32> {
        Ok(i32::try_from(self.to_sint()?)?)
    }
    pub fn to_si64(&self) -> Result<i64> {
        Ok(self.to_sint()?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Error as IoError, ErrorKind, Read};

    fn collect_iter<I: Iterator<Item = IoResult<u8>>>(iter: I) -> Vec<u8> {
        iter.map(|r| r.unwrap()).collect::<Vec<_>>()
    }

    #[test]
    fn test_variant_from_bytes() {
        let io_error1 = IoError::new(ErrorKind::InvalidData, "");

        fn expect_ok(input: &[u8], expected_value: u64, expected_remaining: &[u8]) {
            let mut iter = input.bytes();
            let result = Variant::from_bytes(&mut iter);
            assert!(result.is_ok());
            let variant = result.unwrap();
            assert_eq!(variant.0, expected_value.to_ne_bytes());
            assert_eq!(collect_iter(iter), expected_remaining);
        }
        fn get_err(input: Vec<IoResult<u8>>) -> PuroroError {
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
            get_err(vec![Ok(0x80)]),
            PuroroError::UnexpectedInputTermination
        ));
        assert!(matches!(
            get_err(vec![Err(io_error1)]),
            PuroroError::IteratorError(_)
        ));
    }

    #[test]
    fn test_variant_unsigned() {
        fn get_u32(input: &[u8]) -> Result<u32> {
            let mut iter = input.bytes();
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
            PuroroError::IntegerOverflow(_)
        ));
        assert!(matches!(
            get_u32(&[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F]).unwrap_err(),
            PuroroError::IntegerOverflow(_)
        ));
    }

    #[test]
    fn test_variant_signed_zigzag() {
        fn get_si32(input: &[u8]) -> Result<i32> {
            let mut iter = input.bytes();
            let v = Variant::from_bytes(&mut iter)?;
            assert_eq!(collect_iter(iter), Vec::<u8>::new());
            v.to_si32()
        }
        assert_eq!(get_si32(&[0x00]).unwrap(), 0);
        assert_eq!(get_si32(&[0x01]).unwrap(), -1);
        assert_eq!(get_si32(&[0x02]).unwrap(), 1);
        assert_eq!(get_si32(&[0x7F]).unwrap(), -0x40);
        assert_eq!(get_si32(&[0x80, 0x01]).unwrap(), 0x40);
        assert_eq!(
            get_si32(&[0xFF, 0xFF, 0xFF, 0xFF, 0x0F]).unwrap(),
            -0x80000000
        );
        assert!(matches!(
            get_si32(&[0xFF, 0xFF, 0xFF, 0xFF, 0x1F]).unwrap_err(),
            PuroroError::IntegerOverflow(_)
        ));
        assert!(matches!(
            get_si32(&[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F]).unwrap_err(),
            PuroroError::IntegerOverflow(_)
        ));
    }
}
