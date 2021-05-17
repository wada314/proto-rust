use crate::deser::LdSlice;
use crate::types::{FieldData, SliceViewField};
use crate::{ErrorKind, Result};
use ::either_n::Either4;
use itertools::{Either, Itertools};
use puroro::InternalData;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct InternalDataForNormalStruct {
    unknown_fields: Option<HashMap<usize, FieldData<Vec<u8>>>>,
}
impl InternalDataForNormalStruct {
    pub fn new() -> Self {
        Self {
            unknown_fields: None,
        }
    }
}
impl<'bump> InternalData<'bump> for InternalDataForNormalStruct {
    #[cfg(feature = "puroro-bumpalo")]
    fn bumpalo(&self) -> &'bump bumpalo::Bump {
        panic!("The Bumpalo data field is only available for a Bumpalo struct!")
    }
}

#[cfg(feature = "puroro-bumpalo")]
#[derive(Debug, Clone)]
pub struct InternalDataForBumpaloStruct<'bump> {
    // No hashmap implementation in bumpalo...
    unknown_fields: Option<
        ::bumpalo::collections::Vec<
            'bump,
            (usize, FieldData<::bumpalo::collections::Vec<'bump, u8>>),
        >,
    >,
    bump: &'bump ::bumpalo::Bump,
}

#[cfg(feature = "puroro-bumpalo")]
impl<'bump> InternalDataForBumpaloStruct<'bump> {
    pub fn new_with_bumpalo(bump: &'bump ::bumpalo::Bump) -> Self {
        Self {
            unknown_fields: None,
            bump,
        }
    }
}
impl<'bump> InternalData<'bump> for InternalDataForBumpaloStruct<'bump> {
    /// Note that the returned bumpalo lifetime is not `'bump' but `'_`.
    /// This is because I don't want to introduce the lifetime parameter
    /// `'b` into the trait's definition. The lifetime `'_` might be shorter
    /// than `'b`, but I believe it's not a problem.
    fn bumpalo(&self) -> &'bump bumpalo::Bump {
        self.bump
    }
}

#[derive(Debug, Clone)]
pub struct InternalDataForSliceViewStruct<'slice, 'p> {
    source_ld_slices: SourceLdSlices<'slice, 'p>,
}
#[derive(Debug, Clone)]
pub enum SourceLdSlices<'slice, 'p> {
    SingleLdSlice(LdSlice<'slice>),
    MaybeMultipleLdSlices {
        field_in_parent: Option<&'p SliceViewField<'slice>>,
        field_number_in_parent: usize,
        parent_internal_data: &'p InternalDataForSliceViewStruct<'slice, 'p>,
    },
}

impl<'slice, 'p> InternalDataForSliceViewStruct<'slice, 'p> {
    pub fn new(slice: &'slice [u8]) -> Self {
        Self {
            source_ld_slices: SourceLdSlices::SingleLdSlice(LdSlice::new(slice)),
        }
    }

    pub fn new_with_parent(
        parent_field: &'p Option<SliceViewField<'slice>>,
        field_number_in_parent: usize,
        parent_internal_data: &'p InternalDataForSliceViewStruct<'slice, 'p>,
    ) -> Self {
        Self {
            source_ld_slices: SourceLdSlices::MaybeMultipleLdSlices {
                field_in_parent: parent_field.as_ref(),
                field_number_in_parent,
                parent_internal_data,
            },
        }
    }

    pub fn ld_slices(&'p self) -> impl 'p + Iterator<Item = Result<LdSlice<'slice>>> {
        SourceLdSlicesIter::<'slice, 'p>::new(&self.source_ld_slices, None)
    }

    pub fn field_data_iter(
        &'p self,
        field_number: usize,
        field: &'p Option<SliceViewField<'slice>>,
    ) -> impl 'p + Iterator<Item = Result<FieldData<LdSlice<'slice>>>> {
        SourceLdSlicesIter::<'slice, 'p>::new(&self.source_ld_slices, None)
    }
}

struct SourceLdSlicesIter<'slice, 'p> {
    container: &'p SourceLdSlices<'slice, 'p>,
    prev_ld_slice: Option<LdSlice<'slice>>,
}

impl<'slice, 'p> Iterator for SourceLdSlicesIter<'slice, 'p> {
    type Item = Result<LdSlice<'slice>>;
    fn next(&mut self) -> Option<Self::Item> {
        self.try_next().transpose()
    }
}

impl<'slice, 'p> SourceLdSlicesIter<'slice, 'p> {
    fn new(
        container: &'p SourceLdSlices<'slice, 'p>,
        prev_ld_slice: Option<LdSlice<'slice>>,
    ) -> Self {
        Self {
            container,
            prev_ld_slice,
        }
    }

    fn try_next(&mut self) -> Result<Option<LdSlice<'slice>>> {
        let result = match self.container.clone() {
            SourceLdSlices::SingleLdSlice(slice) => match &self.prev_ld_slice {
                &Some(prev_ld_slice) => {
                    debug_assert_eq!(prev_ld_slice, slice);
                    Ok(None)
                }
                &None => Ok(Some(slice)),
            },
            SourceLdSlices::MaybeMultipleLdSlices {
                field_in_parent,
                field_number_in_parent,
                parent_internal_data,
            } => {
                // WRONG. before getting parent_internal_data.ld_slices(), we need to check if
                // the field_in_parent is singular slice or multiple slices. We need to go to parent_internal_data
                // only in the latter case.
                let ld_slices_iter = parent_internal_data
                    .ld_slices()
                    .map_ok(|ld_slice| ld_slice.fields())
                    .flatten_ok()
                    // ↓ i.e. Result<Result<T, E>, E>::flatten() => Result<T, E>, which is not in stable std yet.
                    .map(|rrfield| rrfield.and_then(|x| x))
                    .filter_map_ok(|field| -> Option<Result<_>> {
                        if field.number == field_number_in_parent {
                            if let FieldData::LengthDelimited(ld_slice) = field.data {
                                Some(Ok(ld_slice))
                            } else {
                                Some(Err(ErrorKind::UnexpectedWireType.into()))
                            }
                        } else {
                            None
                        }
                    })
                    .map(|rrfield| rrfield.and_then(|x| x));
                match self.prev_ld_slice.clone() {
                    Some(prev_ld_slice) => {
                        // Skip until we see the prev_ld_slice value, and then get the next value.
                        ld_slices_iter
                            .skip_while(|rld_slice| {
                                rld_slice.map_or(true, |rd_slice| rd_slice != prev_ld_slice)
                            })
                            .nth(1)
                    }
                    None => ld_slices_iter.next(),
                }
                .transpose()
            }
        };
        self.prev_ld_slice = result.or(self.prev_ld_slice);
        result
    }
}

impl<'bump, 'slice, 'p> InternalData<'bump> for InternalDataForSliceViewStruct<'slice, 'p> {
    fn bumpalo(&self) -> &'bump bumpalo::Bump {
        panic!("The Bumpalo data field is only available for a Bumpalo struct!")
    }
}
