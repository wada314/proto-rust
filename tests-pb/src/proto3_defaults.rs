// A generated source code by puroro library
// package proto3_defaults

pub mod _puroro_root {
    pub use super::super::_puroro_root::*;
}

pub use _puroro_impls::MsgSimple as Msg;
pub use _puroro_impls::SubmsgSimple as Submsg;
pub mod _puroro_impls {
    mod _puroro_root {
        pub use super::super::_puroro_root::*;
    }
    #[derive(
        ::std::clone::Clone, ::std::default::Default, ::std::cmp::PartialEq, ::std::fmt::Debug,
    )]
    pub struct MsgSimple {
        pub i32_unlabeled: i32,
        pub i32_optional: ::std::option::Option<i32>,
        pub i32_repeated: ::std::vec::Vec<i32>,
        pub f32_unlabeled: f32,
        pub string_unlabeled: ::std::string::String,
        pub submsg_unlabeled: ::std::option::Option<
            ::std::boxed::Box<self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgSimple>,
        >,
    }
    impl ::puroro::Message for MsgSimple {}

    impl super::_puroro_traits::MsgTrait for MsgSimple {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            ::std::clone::Clone::clone(&self.i32_unlabeled)
        }
        fn i32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::clone::Clone::clone(&self.i32_optional)
        }
        type Field3RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, i32>>;

        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            self.i32_repeated.iter().cloned()
        }
        fn f32_unlabeled<'this>(&'this self) -> f32 {
            ::std::clone::Clone::clone(&self.f32_unlabeled)
        }
        type Field5StringType<'this> = &'this str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field5StringType<'this> {
            &self.string_unlabeled
        }
        type Field6MessageType<'this> =
            &'this self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgSimple;
        fn submsg_unlabeled<'this>(
            &'this self,
        ) -> ::std::option::Option<Self::Field6MessageType<'this>> {
            self.submsg_unlabeled.as_ref().map(|v| v.as_ref())
        }
    }

    impl ::puroro::DeserFromBytesIter for MsgSimple {
        fn deser<I>(&mut self, iter: I) -> ::puroro::Result<()>
        where
            I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>,
        {
            ::puroro_internal::de::from_iter::deser_from_iter(self, iter)
        }
    }

    impl ::puroro_internal::de::DeserFieldsFromBytesIter for MsgSimple {
        fn deser_field<I>(
            &mut self,
            field_number: i32,
            data: ::puroro::types::FieldData<&mut ::puroro_internal::de::from_iter::ScopedIter<I>>,
        ) -> ::puroro::Result<()>
        where
            I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>,
        {
            match field_number {
                1 => ::puroro_internal::impls::simple::de::DeserFieldFromBytesIter::<
                    ::puroro::tags::Unlabeled,
                    ::puroro::tags::Int32,
                >::deser_field(&mut self.i32_unlabeled, data),
                2 => ::puroro_internal::impls::simple::de::DeserFieldFromBytesIter::<
                    ::puroro::tags::Optional,
                    ::puroro::tags::Int32,
                >::deser_field(&mut self.i32_optional, data),
                3 => ::puroro_internal::impls::simple::de::DeserFieldFromBytesIter::<
                    ::puroro::tags::Repeated,
                    ::puroro::tags::Int32,
                >::deser_field(&mut self.i32_repeated, data),
                4 => ::puroro_internal::impls::simple::de::DeserFieldFromBytesIter::<
                    ::puroro::tags::Unlabeled,
                    ::puroro::tags::Float,
                >::deser_field(&mut self.f32_unlabeled, data),
                5 => ::puroro_internal::impls::simple::de::DeserFieldFromBytesIter::<
                    ::puroro::tags::Unlabeled,
                    ::puroro::tags::String,
                >::deser_field(&mut self.string_unlabeled, data),
                6 => ::puroro_internal::impls::simple::de::DeserFieldFromBytesIter::<
                    ::puroro::tags::Unlabeled,
                    ::puroro::tags::Message<
                        self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgSimple,
                    >,
                >::deser_field(&mut self.submsg_unlabeled, data),

                _ => unimplemented!("TODO: This case should be handled properly..."),
            }
        }
    }

    impl ::puroro::SerToIoWrite for MsgSimple {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            ::puroro_internal::impls::simple::se::SerFieldToIoWrite::<
                ::puroro::tags::Unlabeled,
                ::puroro::tags::Int32,
            >::ser_field(&self.i32_unlabeled, 1, out)?;
            ::puroro_internal::impls::simple::se::SerFieldToIoWrite::<
                ::puroro::tags::Optional,
                ::puroro::tags::Int32,
            >::ser_field(&self.i32_optional, 2, out)?;
            ::puroro_internal::impls::simple::se::SerFieldToIoWrite::<
                ::puroro::tags::Repeated,
                ::puroro::tags::Int32,
            >::ser_field(&self.i32_repeated, 3, out)?;
            ::puroro_internal::impls::simple::se::SerFieldToIoWrite::<
                ::puroro::tags::Unlabeled,
                ::puroro::tags::Float,
            >::ser_field(&self.f32_unlabeled, 4, out)?;
            ::puroro_internal::impls::simple::se::SerFieldToIoWrite::<
                ::puroro::tags::Unlabeled,
                ::puroro::tags::String,
            >::ser_field(&self.string_unlabeled, 5, out)?;
            ::puroro_internal::impls::simple::se::SerFieldToIoWrite::<
                ::puroro::tags::Unlabeled,
                ::puroro::tags::Message<
                    self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgSimple,
                >,
            >::ser_field(&self.submsg_unlabeled, 6, out)?;
            ::std::result::Result::Ok(())
        }
    }
    #[derive(
        ::std::clone::Clone, ::std::default::Default, ::std::cmp::PartialEq, ::std::fmt::Debug,
    )]
    pub struct MsgEmpty;

    impl ::puroro::Message for MsgEmpty {}

    impl super::_puroro_traits::MsgTrait for MsgEmpty {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            ::std::default::Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro_internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro_internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f32_unlabeled<'this>(&'this self) -> f32 {
            ::std::default::Default::default()
        }
        type Field5StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field5StringType<'this> {
            ""
        }
        type Field6MessageType<'this> =
            self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgEmpty;
    }

    impl ::puroro::SerToIoWrite for MsgEmpty {
        fn ser<W>(&self, _out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            ::std::result::Result::Ok(())
        }
    }
    impl<T, U> super::_puroro_traits::MsgTrait for (T, U)
    where
        T: super::_puroro_traits::MsgTrait,
        U: super::_puroro_traits::MsgTrait,
    {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            let left = <T as super::_puroro_traits::MsgTrait>::i32_unlabeled(&self.0);
            if left != ::std::default::Default::default() {
                left
            } else {
                <U as super::_puroro_traits::MsgTrait>::i32_unlabeled(&self.1)
            }
        }
        fn i32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
            todo!()
        }
        type Field3RepeatedType<'this> = ::puroro_internal::impls::merged::MergedRepeatedField<
            <T as super::_puroro_traits::MsgTrait>::Field3RepeatedType<'this>,
            <U as super::_puroro_traits::MsgTrait>::Field3RepeatedType<'this>,
        >;

        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro_internal::impls::merged::MergedRepeatedField::new(
                <T as super::_puroro_traits::MsgTrait>::i32_repeated(&self.0),
                <U as super::_puroro_traits::MsgTrait>::i32_repeated(&self.1),
            )
        }
        fn f32_unlabeled<'this>(&'this self) -> f32 {
            let left = <T as super::_puroro_traits::MsgTrait>::f32_unlabeled(&self.0);
            if left != ::std::default::Default::default() {
                left
            } else {
                <U as super::_puroro_traits::MsgTrait>::f32_unlabeled(&self.1)
            }
        }
        type Field5StringType<'this> = ::puroro::Either<
            <T as super::_puroro_traits::MsgTrait>::Field5StringType<'this>,
            <U as super::_puroro_traits::MsgTrait>::Field5StringType<'this>,
        >;
        fn string_unlabeled<'this>(&'this self) -> Self::Field5StringType<'this> {
            todo!()
        }
        type Field6MessageType<'this> = ::puroro::Either<
            ::puroro::Either<
                <T as super::_puroro_traits::MsgTrait>::Field6MessageType<'this>,
                <U as super::_puroro_traits::MsgTrait>::Field6MessageType<'this>,
            >,
            (
                <T as super::_puroro_traits::MsgTrait>::Field6MessageType<'this>,
                <U as super::_puroro_traits::MsgTrait>::Field6MessageType<'this>,
            ),
        >;
        fn submsg_unlabeled<'this>(
            &'this self,
        ) -> ::std::option::Option<Self::Field6MessageType<'this>> {
            match (
                <T as super::_puroro_traits::MsgTrait>::submsg_unlabeled(&self.0),
                <U as super::_puroro_traits::MsgTrait>::submsg_unlabeled(&self.1),
            ) {
                (None, None) => None,
                (Some(t), None) => Some(::puroro::Either::Left(::puroro::Either::Left(t))),
                (None, Some(u)) => Some(::puroro::Either::Left(::puroro::Either::Right(u))),
                (Some(t), Some(u)) => Some(::puroro::Either::Right((t, u))),
            }
        }
    }
    impl<T, U> super::_puroro_traits::MsgTrait for ::puroro::Either<T, U>
    where
        T: super::_puroro_traits::MsgTrait,
        U: super::_puroro_traits::MsgTrait,
    {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            self.as_ref().either(
                |t| <T as super::_puroro_traits::MsgTrait>::i32_unlabeled(t),
                |u| <U as super::_puroro_traits::MsgTrait>::i32_unlabeled(u),
            )
        }
        fn i32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
            self.as_ref().either(
                |t| <T as super::_puroro_traits::MsgTrait>::i32_optional(t),
                |u| <U as super::_puroro_traits::MsgTrait>::i32_optional(u),
            )
        }
        type Field3RepeatedType<'this> = ::puroro_internal::impls::either::EitherRepeatedField<
            <T as super::_puroro_traits::MsgTrait>::Field3RepeatedType<'this>,
            <U as super::_puroro_traits::MsgTrait>::Field3RepeatedType<'this>,
        >;

        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro_internal::impls::either::EitherRepeatedField::new(
                self.as_ref()
                    .map_left(|t| <T as super::_puroro_traits::MsgTrait>::i32_repeated(t))
                    .map_right(|u| <U as super::_puroro_traits::MsgTrait>::i32_repeated(u)),
            )
        }
        fn f32_unlabeled<'this>(&'this self) -> f32 {
            self.as_ref().either(
                |t| <T as super::_puroro_traits::MsgTrait>::f32_unlabeled(t),
                |u| <U as super::_puroro_traits::MsgTrait>::f32_unlabeled(u),
            )
        }
        type Field5StringType<'this> = ::puroro::Either<
            <T as super::_puroro_traits::MsgTrait>::Field5StringType<'this>,
            <U as super::_puroro_traits::MsgTrait>::Field5StringType<'this>,
        >;
        fn string_unlabeled<'this>(&'this self) -> Self::Field5StringType<'this> {
            self.as_ref().either(
                |t| {
                    ::puroro::Either::Left(
                        <T as super::_puroro_traits::MsgTrait>::string_unlabeled(t),
                    )
                },
                |u| {
                    ::puroro::Either::Right(
                        <U as super::_puroro_traits::MsgTrait>::string_unlabeled(u),
                    )
                },
            )
        }
        type Field6MessageType<'this> = ::puroro::Either<
            <T as super::_puroro_traits::MsgTrait>::Field6MessageType<'this>,
            <U as super::_puroro_traits::MsgTrait>::Field6MessageType<'this>,
        >;
        fn submsg_unlabeled<'this>(
            &'this self,
        ) -> ::std::option::Option<Self::Field6MessageType<'this>> {
            self.as_ref().either(
                |t| {
                    <T as super::_puroro_traits::MsgTrait>::submsg_unlabeled(t)
                        .map(|t| ::puroro::Either::Left(t))
                },
                |u| {
                    <U as super::_puroro_traits::MsgTrait>::submsg_unlabeled(u)
                        .map(|u| ::puroro::Either::Right(u))
                },
            )
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField1 {
        i32_unlabeled: i32,
    }

    impl ::puroro::Message for MsgSimpleField1 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField1 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            ::std::clone::Clone::clone(&self.i32_unlabeled)
        }
        type Field3RepeatedType<'this> = ::puroro_internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro_internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f32_unlabeled<'this>(&'this self) -> f32 {
            ::std::default::Default::default()
        }
        type Field5StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field5StringType<'this> {
            ""
        }
        type Field6MessageType<'this> =
            self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgEmpty;
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField2 {
        i32_optional: ::std::option::Option<i32>,
    }

    impl ::puroro::Message for MsgSimpleField2 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField2 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            ::std::default::Default::default()
        }
        fn i32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::clone::Clone::clone(&self.i32_optional)
        }
        type Field3RepeatedType<'this> = ::puroro_internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro_internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f32_unlabeled<'this>(&'this self) -> f32 {
            ::std::default::Default::default()
        }
        type Field5StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field5StringType<'this> {
            ""
        }
        type Field6MessageType<'this> =
            self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgEmpty;
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField3 {
        i32_repeated: ::std::vec::Vec<i32>,
    }

    impl ::puroro::Message for MsgSimpleField3 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField3 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            ::std::default::Default::default()
        }
        type Field3RepeatedType<'this> = ::std::iter::Cloned<::std::slice::Iter<'this, i32>>;

        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            self.i32_repeated.iter().cloned()
        }
        fn f32_unlabeled<'this>(&'this self) -> f32 {
            ::std::default::Default::default()
        }
        type Field5StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field5StringType<'this> {
            ""
        }
        type Field6MessageType<'this> =
            self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgEmpty;
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField4 {
        f32_unlabeled: f32,
    }

    impl ::puroro::Message for MsgSimpleField4 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField4 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            ::std::default::Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro_internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro_internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f32_unlabeled<'this>(&'this self) -> f32 {
            ::std::clone::Clone::clone(&self.f32_unlabeled)
        }
        type Field5StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field5StringType<'this> {
            ""
        }
        type Field6MessageType<'this> =
            self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgEmpty;
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField5 {
        string_unlabeled: ::std::string::String,
    }

    impl ::puroro::Message for MsgSimpleField5 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField5 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            ::std::default::Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro_internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro_internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f32_unlabeled<'this>(&'this self) -> f32 {
            ::std::default::Default::default()
        }
        type Field5StringType<'this> = &'this str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field5StringType<'this> {
            &self.string_unlabeled
        }
        type Field6MessageType<'this> =
            self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgEmpty;
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct MsgSimpleField6 {
        submsg_unlabeled: ::std::option::Option<
            ::std::boxed::Box<self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgSimple>,
        >,
    }

    impl ::puroro::Message for MsgSimpleField6 {}

    impl super::_puroro_traits::MsgTrait for MsgSimpleField6 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            ::std::default::Default::default()
        }
        type Field3RepeatedType<'this> = ::puroro_internal::impls::empty::EmptyRepeatedField<i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            ::puroro_internal::impls::empty::EmptyRepeatedField::new()
        }
        fn f32_unlabeled<'this>(&'this self) -> f32 {
            ::std::default::Default::default()
        }
        type Field5StringType<'this> = &'static str;
        fn string_unlabeled<'this>(&'this self) -> Self::Field5StringType<'this> {
            ""
        }
        type Field6MessageType<'this> =
            &'this self::_puroro_root::proto3_defaults::_puroro_impls::SubmsgSimple;
        fn submsg_unlabeled<'this>(
            &'this self,
        ) -> ::std::option::Option<Self::Field6MessageType<'this>> {
            self.submsg_unlabeled.as_ref().map(|v| v.as_ref())
        }
    }
    #[derive(
        ::std::clone::Clone, ::std::default::Default, ::std::cmp::PartialEq, ::std::fmt::Debug,
    )]
    pub struct SubmsgSimple {
        pub i32_unlabeled: i32,
    }
    impl ::puroro::Message for SubmsgSimple {}

    impl super::_puroro_traits::SubmsgTrait for SubmsgSimple {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            ::std::clone::Clone::clone(&self.i32_unlabeled)
        }
    }

    impl ::puroro::DeserFromBytesIter for SubmsgSimple {
        fn deser<I>(&mut self, iter: I) -> ::puroro::Result<()>
        where
            I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>,
        {
            ::puroro_internal::de::from_iter::deser_from_iter(self, iter)
        }
    }

    impl ::puroro_internal::de::DeserFieldsFromBytesIter for SubmsgSimple {
        fn deser_field<I>(
            &mut self,
            field_number: i32,
            data: ::puroro::types::FieldData<&mut ::puroro_internal::de::from_iter::ScopedIter<I>>,
        ) -> ::puroro::Result<()>
        where
            I: ::std::iter::Iterator<Item = ::std::io::Result<u8>>,
        {
            match field_number {
                1 => ::puroro_internal::impls::simple::de::DeserFieldFromBytesIter::<
                    ::puroro::tags::Unlabeled,
                    ::puroro::tags::Int32,
                >::deser_field(&mut self.i32_unlabeled, data),

                _ => unimplemented!("TODO: This case should be handled properly..."),
            }
        }
    }

    impl ::puroro::SerToIoWrite for SubmsgSimple {
        fn ser<W>(&self, out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            ::puroro_internal::impls::simple::se::SerFieldToIoWrite::<
                ::puroro::tags::Unlabeled,
                ::puroro::tags::Int32,
            >::ser_field(&self.i32_unlabeled, 1, out)?;
            ::std::result::Result::Ok(())
        }
    }
    #[derive(
        ::std::clone::Clone, ::std::default::Default, ::std::cmp::PartialEq, ::std::fmt::Debug,
    )]
    pub struct SubmsgEmpty;

    impl ::puroro::Message for SubmsgEmpty {}

    impl super::_puroro_traits::SubmsgTrait for SubmsgEmpty {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            ::std::default::Default::default()
        }
    }

    impl ::puroro::SerToIoWrite for SubmsgEmpty {
        fn ser<W>(&self, _out: &mut W) -> ::puroro::Result<()>
        where
            W: ::std::io::Write,
        {
            ::std::result::Result::Ok(())
        }
    }
    impl<T, U> super::_puroro_traits::SubmsgTrait for (T, U)
    where
        T: super::_puroro_traits::SubmsgTrait,
        U: super::_puroro_traits::SubmsgTrait,
    {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            let left = <T as super::_puroro_traits::SubmsgTrait>::i32_unlabeled(&self.0);
            if left != ::std::default::Default::default() {
                left
            } else {
                <U as super::_puroro_traits::SubmsgTrait>::i32_unlabeled(&self.1)
            }
        }
    }
    impl<T, U> super::_puroro_traits::SubmsgTrait for ::puroro::Either<T, U>
    where
        T: super::_puroro_traits::SubmsgTrait,
        U: super::_puroro_traits::SubmsgTrait,
    {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            self.as_ref().either(
                |t| <T as super::_puroro_traits::SubmsgTrait>::i32_unlabeled(t),
                |u| <U as super::_puroro_traits::SubmsgTrait>::i32_unlabeled(u),
            )
        }
    }

    #[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
    struct SubmsgSimpleField1 {
        i32_unlabeled: i32,
    }

    impl ::puroro::Message for SubmsgSimpleField1 {}

    impl super::_puroro_traits::SubmsgTrait for SubmsgSimpleField1 {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            ::std::clone::Clone::clone(&self.i32_unlabeled)
        }
    }
}
pub use _puroro_traits::*;
pub mod _puroro_traits {
    mod _puroro_root {
        pub use super::super::_puroro_root::*;
    }

    pub trait MsgTrait {
        fn i32_unlabeled<'this>(&'this self) -> i32;
        fn i32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
            ::std::default::Default::default()
        }
        type Field3RepeatedType<'this>: ::puroro::RepeatedField<'this>
            + ::std::iter::IntoIterator<Item = i32>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this>;
        fn f32_unlabeled<'this>(&'this self) -> f32;
        type Field5StringType<'this>: ::std::ops::Deref<Target = str>;
        fn string_unlabeled<'this>(&'this self) -> Self::Field5StringType<'this>;
        type Field6MessageType<'this>: self::_puroro_root::proto3_defaults::_puroro_traits::SubmsgTrait;
        fn submsg_unlabeled<'this>(
            &'this self,
        ) -> ::std::option::Option<Self::Field6MessageType<'this>> {
            ::std::default::Default::default()
        }
    }

    impl<T> MsgTrait for &'_ T
    where
        T: MsgTrait,
    {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            (**self).i32_unlabeled()
        }
        fn i32_optional<'this>(&'this self) -> ::std::option::Option<i32> {
            (**self).i32_optional()
        }
        type Field3RepeatedType<'this> = T::Field3RepeatedType<'this>;
        fn i32_repeated<'this>(&'this self) -> Self::Field3RepeatedType<'this> {
            (**self).i32_repeated()
        }
        fn f32_unlabeled<'this>(&'this self) -> f32 {
            (**self).f32_unlabeled()
        }
        type Field5StringType<'this> = T::Field5StringType<'this>;
        fn string_unlabeled<'this>(&'this self) -> Self::Field5StringType<'this> {
            (**self).string_unlabeled()
        }
        type Field6MessageType<'this> = T::Field6MessageType<'this>;
        fn submsg_unlabeled<'this>(
            &'this self,
        ) -> ::std::option::Option<Self::Field6MessageType<'this>> {
            (**self).submsg_unlabeled()
        }
    }
    pub trait SubmsgTrait {
        fn i32_unlabeled<'this>(&'this self) -> i32;
    }

    impl<T> SubmsgTrait for &'_ T
    where
        T: SubmsgTrait,
    {
        fn i32_unlabeled<'this>(&'this self) -> i32 {
            (**self).i32_unlabeled()
        }
    }
}
pub use _puroro_nested::*;
pub mod _puroro_nested {
    pub mod msg {
        mod _puroro_root {
            pub use super::super::super::_puroro_root::*;
        }
    }
    pub mod submsg {
        mod _puroro_root {
            pub use super::super::super::_puroro_root::*;
        }
    }
}
