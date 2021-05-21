use std::marker::PhantomData;

use crate::deser::LdSlice;
use crate::tags;
use crate::types::{FieldData, SliceViewField};
use crate::variant::VariantTypeTag;
use crate::InternalDataForSliceViewStruct;
use crate::{ErrorKind, Result, ResultHelper};
use ::itertools::{Either, Itertools};
use ::puroro::RepeatedField;

pub trait FieldDataIntoIter<'p> {
    type Item;
    type Iter: 'p + Iterator<Item = Result<Self::Item>>;
    fn into<'slice: 'p>(field_data: FieldData<LdSlice<'slice>>) -> Result<Self::Iter>;
}
impl<'p> FieldDataIntoIter<'p> for tags::Int32 {
    type Item = i32;
    type Iter = impl 'p + Iterator<Item = Result<Self::Item>>;
    fn into<'slice: 'p>(field_data: FieldData<LdSlice<'slice>>) -> Result<Self::Iter> {
        Ok(match field_data {
            FieldData::Variant(variant) => {
                Either::Left(std::iter::once(variant.to_native::<Self>()))
            }
            FieldData::LengthDelimited(ld_slice) => Either::Right(
                ld_slice
                    .variants()
                    .map_ok(|variant| variant.to_native::<Self>())
                    .map(|rrval| rrval.flatten()),
            ),
            _ => Err(ErrorKind::UnexpectedWireType)?,
        }
        .into_iter())
    }
}

#[derive(Debug, Clone)]
pub struct RepeatedSliceViewField<'slice, 'p, TypeTag>
where
    TypeTag: FieldDataIntoIter<'p>,
{
    field: &'p Option<SliceViewField<'slice>>,
    field_number: usize,
    internal_data: &'p InternalDataForSliceViewStruct<'slice, 'p>,
    phantom: PhantomData<TypeTag>,
}

impl<'slice, 'p, TypeTag> RepeatedSliceViewField<'slice, 'p, TypeTag>
where
    TypeTag: FieldDataIntoIter<'p>,
{
    fn iter_impl(&'p self) -> impl 'p + Iterator<Item = <TypeTag as FieldDataIntoIter>::Item> {
        self.internal_data
            .field_data_iter(self.field_number, self.field)
            .map_ok(|field| -> Result<_> { <TypeTag as FieldDataIntoIter>::into(field) })
            .map(|rrval| rrval.flatten())
            .flatten_ok()
            .map(|rrval| rrval.flatten())
            .map(|result| result.unwrap())
    }
}

impl<'slice, 'p, T, TypeTag> RepeatedField<'p, T> for RepeatedSliceViewField<'slice, 'p, TypeTag>
where
    T: 'p,
    TypeTag: FieldDataIntoIter<'p, Item = T>,
{
    fn for_each<F>(&'p self, f: F)
    where
        F: FnMut(T),
    {
        self.iter_impl().for_each(f)
    }
    fn boxed_iter(&'p self) -> Box<dyn 'p + Iterator<Item = T>> {
        Box::new(self.iter_impl())
    }

    type Iter = impl Iterator<Item = T>;
    fn iter(&'p self) -> Self::Iter {
        self.iter_impl()
    }
}
