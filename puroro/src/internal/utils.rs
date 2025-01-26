// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{ErrorKind, Result};
use ::cached_pair::{EitherOrBoth, Pair};
use ::once_list2::OnceList;
use ::std::alloc::Allocator;
use ::std::iter;

#[derive(Clone)]
pub struct OnceList1<T, A: Allocator>(T, OnceList<T, A>);
impl<T, A: Allocator> OnceList1<T, A> {
    pub fn new_in(first: T, alloc: A) -> Self {
        Self(first, OnceList::new_in(alloc))
    }
    pub fn first(&self) -> &T {
        &self.0
    }
    pub fn last(&self) -> &T {
        match self.1.last() {
            Some(last) => last,
            None => self.first(),
        }
    }
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        iter::once(&self.0).chain(self.1.iter())
    }
    pub fn allocator(&self) -> &A {
        self.1.allocator()
    }
}
impl<T, A: Allocator + Clone> OnceList1<T, A> {
    pub fn push(&self, value: T) -> &T {
        self.1.push(value)
    }
}

impl<T: ::std::fmt::Debug, A: Allocator> ::std::fmt::Debug for OnceList1<T, A> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        f.debug_list()
            .entry(&self.0)
            .entries(self.1.iter())
            .finish()
    }
}

pub(crate) struct WithAllocator<T, A>(pub(crate) T, pub(crate) A);

pub(crate) trait PairWithOnceList1Ext<L, R, A> {
    fn try_get_or_insert_into_right<'a, T, F>(&'a self, to_right: F, alloc: A) -> Result<&'a T>
    where
        L: 'a,
        R: 'a,
        &'a R: TryInto<&'a T>,
        WithAllocator<&'a R, A>: TryInto<L>,
        ErrorKind: From<<WithAllocator<&'a R, A> as TryInto<L>>::Error>,
        T: Into<R>,
        F: FnOnce(&L) -> Result<T>;
    fn try_get_mut_or_insert_into_right<'a, T, F>(
        &'a mut self,
        to_right: F,
        alloc: A,
    ) -> Result<&'a mut T>
    where
        L: 'a,
        R: 'a,
        &'a R: TryInto<&'a T>,
        WithAllocator<&'a R, A>: TryInto<L>,
        ErrorKind: From<<WithAllocator<&'a R, A> as TryInto<L>>::Error>,
        T: Into<R>,
        F: FnOnce(&L) -> Result<T>;
}

impl<L, R, A> PairWithOnceList1Ext<L, R, A> for Pair<L, OnceList1<R, A>>
where
    A: Allocator + Clone,
{
    fn try_get_or_insert_into_right<'a, T, F>(&'a self, to_right: F, alloc: A) -> Result<&'a T>
    where
        L: 'a,
        R: 'a,
        &'a R: TryInto<&'a T>,
        WithAllocator<&'a R, A>: TryInto<L>,
        ErrorKind: From<<WithAllocator<&'a R, A> as TryInto<L>>::Error>,
        T: Into<R>,
        F: FnOnce(&L) -> Result<T>,
    {
        // First try to find in existing list if available
        if let Some(list) = self.right_opt() {
            if let Some(item) = list.iter().find_map(|x| x.try_into().ok()) {
                return Ok(item);
            }
        }

        // The value not exists. To create the new right value, we need to get the left value.
        let left = self.try_left_with(|right_list| {
            WithAllocator(right_list.first(), alloc.clone()).try_into()
        })?;

        // Create the new right value. Store it as mut Optional for the following steps.
        let mut value_opt = Some(to_right(left)?);

        // Get the right list. If the list not exists, create it.
        // We need to initialize the list with the value.
        let list =
            self.right_with(|_| OnceList1::new_in(value_opt.take().unwrap().into(), alloc.clone()));

        // Push the new value into the list. This step is not necessary if we already added the value in the previous steps.
        if let Some(value) = value_opt {
            list.push(value.into());
        }

        Ok(unsafe { list.last().try_into().unwrap_unchecked() })
    }

    fn try_get_mut_or_insert_into_right<'a, T, F>(
        &'a mut self,
        to_right: F,
        alloc: A,
    ) -> Result<&'a mut T>
    where
        L: 'a,
        R: 'a,
        &'a R: TryInto<&'a T>,
        WithAllocator<&'a R, A>: TryInto<L>,
        ErrorKind: From<<WithAllocator<&'a R, A> as TryInto<L>>::Error>,
        T: Into<R>,
        F: FnOnce(&L) -> Result<T>,
    {
        // kore muzui
        Ok(todo!())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ::std::alloc::Global;

    #[derive(::derive_more::TryInto, ::derive_more::From, PartialEq, Debug, Clone)]
    #[try_into(owned, ref)]
    enum Int32Compatible {
        String(String),
        Array([u8; 4]),
    }

    impl TryFrom<WithAllocator<&Int32Compatible, Global>> for i32 {
        type Error = ErrorKind;

        fn try_from(value: WithAllocator<&Int32Compatible, Global>) -> Result<Self> {
            match value.0 {
                Int32Compatible::String(s) => s
                    .parse()
                    .map_err(|_| "Invalid number format".to_string().into()),
                Int32Compatible::Array(a) => Ok(i32::from_le_bytes(*a)),
            }
        }
    }

    impl From<i32> for Int32Compatible {
        fn from(value: i32) -> Self {
            Int32Compatible::Array(value.to_le_bytes())
        }
    }

    #[test]
    fn test_once_list1_basic() {
        let list = OnceList1::new_in(1, Global);
        assert_eq!(*list.first(), 1);

        let items: Vec<_> = list.iter().copied().collect();
        assert_eq!(items, vec![1]);
    }

    #[test]
    fn test_once_list1_push() {
        let list = OnceList1::new_in(1, Global);
        list.push(2);
        list.push(3);

        let items: Vec<_> = list.iter().copied().collect();
        assert_eq!(items, vec![1, 2, 3]);
    }

    #[test]
    fn test_once_list1_debug() {
        let list = OnceList1::new_in(1, Global);
        list.push(2);

        assert_eq!(format!("{:?}", list), "[1, 2]");
    }

    #[test]
    fn test_pair_with_once_list1_ext_find_existing() -> Result<()> {
        let list = OnceList1::new_in(Int32Compatible::String("42".to_string()), Global);
        list.push(Int32Compatible::Array(123i32.to_le_bytes()));
        let pair: Pair<i32, _> = Pair::from_right(list);

        let result: &String = pair.try_get_or_insert_into_right(|n| Ok(n.to_string()), Global)?;
        assert_eq!(*result, "42".to_string());
        Ok(())
    }

    #[test]
    fn test_pair_with_once_list1_ext_create_list_from_left() -> Result<()> {
        let pair: Pair<i32, _> = Pair::from_left(42);

        let result: &String = pair.try_get_or_insert_into_right(|n| Ok(n.to_string()), Global)?;
        assert_eq!(*result, "42".to_string());
        Ok(())
    }

    #[test]
    fn test_pair_with_once_list1_ext_push_new_value() -> Result<()> {
        let list = OnceList1::new_in(Int32Compatible::Array(42i32.to_le_bytes()), Global);
        let pair: Pair<i32, _> = Pair::from_right(list);

        let result: &String = pair.try_get_or_insert_into_right(|n| Ok(n.to_string()), Global)?;
        assert_eq!(*result, "42".to_string());
        Ok(())
    }

    #[test]
    fn test_pair_with_once_list1_ext_both_sides_present_but_no_string() -> Result<()> {
        let list = OnceList1::new_in(Int32Compatible::Array(42i32.to_le_bytes()), Global);
        let pair: Pair<i32, _> = Pair::from_right(list);
        let _ = pair.left_with(|_| 42);

        let result: &String = pair.try_get_or_insert_into_right(|n| Ok(n.to_string()), Global)?;
        assert_eq!(*result, "42".to_string());
        Ok(())
    }
}
