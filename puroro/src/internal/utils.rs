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

pub trait PairWithOnceList1Ext2<L, R, A> {
    fn try_get_or_insert_into_right2<'a, T, F>(&'a self, to_right: F, alloc: A) -> Result<&'a T>
    where
        L: 'a,
        R: 'a,
        &'a R: TryInto<&'a T> + TryInto<L>,
        ErrorKind: From<<&'a R as TryInto<L>>::Error>,
        T: Into<R>,
        F: FnOnce(&L) -> Result<T>;
}

impl<L, R, A> PairWithOnceList1Ext2<L, R, A> for Pair<L, OnceList1<R, A>>
where
    A: Allocator + Clone,
{
    fn try_get_or_insert_into_right2<'a, T, F>(&'a self, to_right: F, alloc: A) -> Result<&'a T>
    where
        L: 'a,
        R: 'a,
        &'a R: TryInto<&'a T> + TryInto<L>,
        ErrorKind: From<<&'a R as TryInto<L>>::Error>,
        T: Into<R>,
        F: FnOnce(&L) -> Result<T>,
    {
        // First try to find in existing list if available
        if let Some(list) = self.right_opt() {
            if let Some(item) = list.iter().find_map(|x| x.try_into().ok()) {
                return Ok(item);
            }

            // List exists but value not found, create new value and push it
            let value = match self.as_ref() {
                EitherOrBoth::Both(left, _) | EitherOrBoth::Left(left) => to_right(left)?,
                EitherOrBoth::Right(_) => {
                    let left = list.first().try_into()?;
                    to_right(&left)?
                }
            };
            let right_item = list.push(value.into());
            return Ok(unsafe { right_item.try_into().unwrap_unchecked() });
        }

        // List doesn't exist, create new list with the value
        let value = match self.as_ref() {
            EitherOrBoth::Both(left, _) | EitherOrBoth::Left(left) => to_right(left)?,
            EitherOrBoth::Right(list) => {
                let left = list.first().try_into()?;
                to_right(&left)?
            }
        };

        let list_ref = self.right_with(|_| OnceList1::new_in(value.into(), alloc));
        Ok(unsafe { list_ref.first().try_into().unwrap_unchecked() })
    }
}

pub trait PairWithOnceList1Ext<L, T, A> {
    fn try_get_or_insert_into_right<
        F: Fn(&T) -> bool,
        G: FnOnce(&L) -> Result<T>,
        H: FnOnce(&T) -> Result<L>,
    >(
        &self,
        pred: F,
        to_right: G,
        to_left: H,
        alloc: &A,
    ) -> Result<&T>;
}
impl<L, T, A: Allocator + Clone> PairWithOnceList1Ext<L, T, A> for Pair<L, OnceList1<T, A>> {
    fn try_get_or_insert_into_right<
        F: Fn(&T) -> bool,
        G: FnOnce(&L) -> Result<T>,
        H: FnOnce(&T) -> Result<L>,
    >(
        &self,
        pred: F,
        to_right: G,
        to_left: H,
        alloc: &A,
    ) -> Result<&T> {
        // First try to find in existing list if available
        if let Some(list) = self.right_opt() {
            if let Some(item) = list.iter().find(|x| pred(*x)) {
                return Ok(item);
            }

            // List exists but value not found, create new value and push it
            let value = match self.as_ref() {
                EitherOrBoth::Both(left, _) | EitherOrBoth::Left(left) => to_right(left)?,
                EitherOrBoth::Right(_) => {
                    let left = to_left(list.first())?;
                    to_right(&left)?
                }
            };
            return Ok(list.push(value));
        }

        // List doesn't exist, create new list with the value
        let value = match self.as_ref() {
            EitherOrBoth::Both(left, _) | EitherOrBoth::Left(left) => to_right(left)?,
            EitherOrBoth::Right(list) => {
                let left = to_left(list.first())?;
                to_right(&left)?
            }
        };

        let list_ref = self.right_with(|_| OnceList1::new_in(value, A::clone(&alloc)));
        Ok(list_ref.first())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::alloc::Global;

    #[derive(Debug, PartialEq, Clone)]
    enum RadixStr {
        Decimal(String),
        Octal(String),
        Hex(String),
    }

    impl RadixStr {
        fn parse(&self) -> Option<i32> {
            match self {
                RadixStr::Decimal(s) => s.parse().ok(),
                RadixStr::Octal(s) => s
                    .strip_prefix('0')
                    .and_then(|s| i32::from_str_radix(s, 8).ok()),
                RadixStr::Hex(s) => s
                    .strip_prefix("0x")
                    .and_then(|s| i32::from_str_radix(s, 16).ok()),
            }
        }
    }

    impl TryFrom<&RadixStr> for RadixStr {
        type Error = ErrorKind;

        fn try_from(value: &RadixStr) -> Result<Self> {
            Ok(value.clone())
        }
    }

    #[derive(::derive_more::TryInto, ::derive_more::From, PartialEq, Debug, Clone)]
    #[try_into(owned, ref)]
    enum Int32Compatible {
        String(String),
        Array([u8; 4]),
    }

    impl TryFrom<&Int32Compatible> for i32 {
        type Error = ErrorKind;

        fn try_from(value: &Int32Compatible) -> Result<Self> {
            match value {
                Int32Compatible::String(s) => s
                    .parse()
                    .map_err(|_| "Invalid number format".to_string().into()),
                Int32Compatible::Array(a) => Ok(i32::from_le_bytes(*a)),
            }
        }
    }

    impl<'a> TryFrom<&'a Int32Compatible> for &'a i32 {
        type Error = ErrorKind;

        fn try_from(value: &'a Int32Compatible) -> Result<Self> {
            static mut CACHED: Option<(Int32Compatible, i32)> = None;

            unsafe {
                if let Some((ref cached_input, ref cached_output)) = CACHED {
                    if cached_input == value {
                        return Ok(cached_output);
                    }
                }

                let result = i32::try_from(value)?;
                CACHED = Some((value.clone(), result));
                if let Some((_, ref output)) = CACHED {
                    Ok(output)
                } else {
                    unreachable!()
                }
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
        let list = OnceList1::new_in(RadixStr::Hex("0x2a".to_string()), Global);
        list.push(RadixStr::Octal("052".to_string()));
        let pair = Pair::from_right(list);

        let result = pair.try_get_or_insert_into_right(
            |r: &RadixStr| matches!(r, RadixStr::Octal(_)),
            |n: &i32| Ok(RadixStr::Octal(format!("0{:o}", n))),
            |r: &RadixStr| {
                r.parse()
                    .ok_or_else(|| "Invalid number format".to_string().into())
            },
            &Global,
        )?;
        assert_eq!(result, &RadixStr::Octal("052".to_string()));
        Ok(())
    }

    #[test]
    fn test_pair_with_once_list1_ext_push_list_value_from_left() -> Result<()> {
        let pair = Pair::from_left(42);
        let _ =
            pair.right_with(|i| OnceList1::new_in(RadixStr::Hex(format!("0x{:x}", *i)), Global));

        let result = pair.try_get_or_insert_into_right(
            |r: &RadixStr| matches!(r, RadixStr::Decimal(_)),
            |n: &i32| Ok(RadixStr::Decimal(n.to_string())),
            |r: &RadixStr| {
                r.parse()
                    .ok_or_else(|| "Invalid number format".to_string().into())
            },
            &Global,
        )?;
        assert_eq!(result, &RadixStr::Decimal("42".to_string()));
        Ok(())
    }

    #[test]
    fn test_pair_with_once_list1_ext_push_list_value_from_right() -> Result<()> {
        let list = OnceList1::new_in(RadixStr::Hex("0x2a".to_string()), Global);
        let pair = Pair::from_right(list);

        let result = pair.try_get_or_insert_into_right(
            |r: &RadixStr| matches!(r, RadixStr::Decimal(_)),
            |n: &i32| Ok(RadixStr::Decimal(n.to_string())),
            |r: &RadixStr| {
                r.parse()
                    .ok_or_else(|| "Invalid number format".to_string().into())
            },
            &Global,
        )?;
        assert_eq!(result, &RadixStr::Decimal("42".to_string()));
        Ok(())
    }

    #[test]
    fn test_pair_with_once_list1_ext_create_list_from_left() -> Result<()> {
        let pair = Pair::from_left(42);

        let result = pair.try_get_or_insert_into_right(
            |r: &RadixStr| matches!(r, RadixStr::Decimal(_)),
            |n: &i32| Ok(RadixStr::Decimal(n.to_string())),
            |r: &RadixStr| {
                r.parse()
                    .ok_or_else(|| "Invalid number format".to_string().into())
            },
            &Global,
        )?;
        assert_eq!(result, &RadixStr::Decimal("42".to_string()));
        Ok(())
    }

    #[test]
    fn test_pair_with_once_list1_ext2_find_existing() -> Result<()> {
        let list = OnceList1::new_in(Int32Compatible::String("42".to_string()), Global);
        list.push(Int32Compatible::Array(123i32.to_le_bytes()));
        let pair: Pair<i32, _> = Pair::from_right(list);

        let result: &String = pair.try_get_or_insert_into_right2(|n| Ok(n.to_string()), Global)?;
        assert_eq!(*result, "42".to_string());
        Ok(())
    }

}
