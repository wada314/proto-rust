use crate::types::*;
use std::io::Read;

mod delayed;
mod impls;
mod iters;

pub use crate::variant::Variant;
pub use ::puroro::{PuroroError, Result};
pub use ::puroro::{RepeatedFieldCollector, RepeatedFieldHandler};

pub use delayed::DelayedLengthDelimitedDeserializer;

pub trait Deserializer {
    fn deserialize<H: MessageHandler>(self, handler: H) -> Result<H::Target>;
}
pub fn deserializer_from_read<R: Read>(read: R) -> impl Deserializer {
    impls::DeserializerImpl::<std::io::Bytes<R>>::new(read.bytes())
}
pub fn deserializer_from_bytes<I: Iterator<Item = std::io::Result<u8>>>(
    iter: I,
) -> impl Deserializer {
    impls::DeserializerImpl::<I>::new(iter)
}

pub trait LengthDelimitedDeserializer: Sized {
    fn deserialize_as_message<H: MessageHandler>(
        self,
        handler: H,
    ) -> Result<<H as MessageHandler>::Target>;

    type BytesIterator: Iterator<Item = Result<u8>>;
    fn deserialize_as_bytes(self) -> Self::BytesIterator;

    type CharsIterator: Iterator<Item = Result<char>>;
    fn deserialize_as_chars(self) -> Self::CharsIterator;

    type VariantsIterator: Iterator<Item = Result<Variant>>;
    fn deserialize_as_variants(self) -> Self::VariantsIterator;

    // Delay the deserializing
    fn leave_as_unknown(self) -> Result<DelayedLengthDelimitedDeserializer>;
}

#[derive(Debug, Clone)]
pub enum Field<T> {
    Variant(Variant),
    LengthDelimited(T),
    Bytes32([u8; 4]),
    Bytes64([u8; 8]),
}

pub trait MessageHandler {
    type Target;
    fn finish(self) -> Result<Self::Target>;

    fn met_field<T: LengthDelimitedDeserializer>(
        &mut self,
        field: Field<T>,
        field_number: usize,
    ) -> Result<()>;
}
