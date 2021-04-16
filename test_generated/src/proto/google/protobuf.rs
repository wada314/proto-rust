#![allow(unused_variables)]
#![allow(unused_imports)]

#[derive(Debug, Clone)]
pub struct GeneratedCodeInfo {
    pub annotation: ::std::vec::Vec<super::super::google::protobuf::generated_code_info::Annotation>,
}
impl ::std::default::Default for GeneratedCodeInfo {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            annotation: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut GeneratedCodeInfo {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    let msg = self.annotation.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for GeneratedCodeInfo {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <GeneratedCodeInfo as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for GeneratedCodeInfo {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        for msg in self.annotation.iter_for_ser() {
            serializer.serialize_message_twice(1, msg)?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for GeneratedCodeInfo {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait GeneratedCodeInfoTrait {
    fn for_each_annotation<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::generated_code_info::Annotation);
    fn annotation_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::generated_code_info::Annotation>>;
}
impl GeneratedCodeInfoTrait for GeneratedCodeInfo {
    fn for_each_annotation<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::generated_code_info::Annotation) {
        for item in &self.annotation {
            (f)(item);
        }
    }
    fn annotation_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::generated_code_info::Annotation>> {
        ::std::boxed::Box::new(self.annotation.iter())
    }
}
pub mod generated_code_info {
#[derive(Debug, Clone)]
pub struct Annotation {
    pub path: ::std::vec::Vec<i32>,
    pub source_file: ::std::string::String,
    pub begin: i32,
    pub end: i32,
}
impl ::std::default::Default for Annotation {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            path: ::std::default::Default::default(),
            source_file: ::std::default::Default::default(),
            begin: ::std::default::Default::default(),
            end: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut Annotation {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => {
                    *self.path.push_and_get_mut() = variant.to_native::<::puroro::tags::Int32>()?;
                }
                2 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                3 => {
                    *self.begin.push_and_get_mut() = variant.to_native::<::puroro::tags::Int32>()?;
                }
                4 => {
                    *self.end.push_and_get_mut() = variant.to_native::<::puroro::tags::Int32>()?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Int32>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.path, first, iter);
                }
                2 => {
                    *self.source_file.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                3 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Int32>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.begin, first, iter);
                }
                4 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Int32>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.end, first, iter);
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 2 | 3 | 4 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 2 | 3 | 4 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for Annotation {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <Annotation as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for Annotation {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        serializer.serialize_variants_twice::<::puroro::tags::Int32, _>(
            1, 
            self.path.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        for string in self.source_file.iter_for_ser() {
            serializer.serialize_bytes_twice(2, string.bytes().map(|b| Ok(b)))?;
        }
        serializer.serialize_variants_twice::<::puroro::tags::Int32, _>(
            3, 
            self.begin.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Int32, _>(
            4, 
            self.end.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        Ok(())
    }
}
impl ::puroro::Serializable for Annotation {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait AnnotationTrait {
    fn for_each_path<F>(&self, f: F)
    where
        F: FnMut(i32);
    fn path_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=i32>>;
    fn source_file(&self) -> &str;
    fn begin(&self) -> i32;
    fn end(&self) -> i32;
}
impl AnnotationTrait for Annotation {
    fn for_each_path<F>(&self, f: F)
    where
        F: FnMut(i32) {
        for item in &self.path {
            (f)(item);
        }
    }
    fn path_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=i32>> {
        ::std::boxed::Box::new(self.path.iter().cloned())
    }
    fn source_file(&self) -> &str {
        &self.source_file
    }
    fn begin(&self) -> i32 {
        &self.begin
    }
    fn end(&self) -> i32 {
        &self.end
    }
}
} // mod generated_code_info
#[derive(Debug, Clone)]
pub struct SourceCodeInfo {
    pub location: ::std::vec::Vec<super::super::google::protobuf::source_code_info::Location>,
}
impl ::std::default::Default for SourceCodeInfo {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            location: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut SourceCodeInfo {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    let msg = self.location.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for SourceCodeInfo {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <SourceCodeInfo as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for SourceCodeInfo {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        for msg in self.location.iter_for_ser() {
            serializer.serialize_message_twice(1, msg)?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for SourceCodeInfo {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait SourceCodeInfoTrait {
    fn for_each_location<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::source_code_info::Location);
    fn location_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::source_code_info::Location>>;
}
impl SourceCodeInfoTrait for SourceCodeInfo {
    fn for_each_location<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::source_code_info::Location) {
        for item in &self.location {
            (f)(item);
        }
    }
    fn location_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::source_code_info::Location>> {
        ::std::boxed::Box::new(self.location.iter())
    }
}
pub mod source_code_info {
#[derive(Debug, Clone)]
pub struct Location {
    pub path: ::std::vec::Vec<i32>,
    pub span: ::std::vec::Vec<i32>,
    pub leading_comments: ::std::string::String,
    pub trailing_comments: ::std::string::String,
    pub leading_detached_comments: ::std::vec::Vec<::std::string::String>,
}
impl ::std::default::Default for Location {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            path: ::std::default::Default::default(),
            span: ::std::default::Default::default(),
            leading_comments: ::std::default::Default::default(),
            trailing_comments: ::std::default::Default::default(),
            leading_detached_comments: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut Location {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => {
                    *self.path.push_and_get_mut() = variant.to_native::<::puroro::tags::Int32>()?;
                }
                2 => {
                    *self.span.push_and_get_mut() = variant.to_native::<::puroro::tags::Int32>()?;
                }
                3 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                4 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                6 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Int32>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.path, first, iter);
                }
                2 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Int32>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.span, first, iter);
                }
                3 => {
                    *self.leading_comments.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                4 => {
                    *self.trailing_comments.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                6 => {
                    *self.leading_detached_comments.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 2 | 3 | 4 | 6 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 2 | 3 | 4 | 6 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for Location {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <Location as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for Location {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        serializer.serialize_variants_twice::<::puroro::tags::Int32, _>(
            1, 
            self.path.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Int32, _>(
            2, 
            self.span.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        for string in self.leading_comments.iter_for_ser() {
            serializer.serialize_bytes_twice(3, string.bytes().map(|b| Ok(b)))?;
        }
        for string in self.trailing_comments.iter_for_ser() {
            serializer.serialize_bytes_twice(4, string.bytes().map(|b| Ok(b)))?;
        }
        for string in self.leading_detached_comments.iter_for_ser() {
            serializer.serialize_bytes_twice(6, string.bytes().map(|b| Ok(b)))?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for Location {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait LocationTrait {
    fn for_each_path<F>(&self, f: F)
    where
        F: FnMut(i32);
    fn path_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=i32>>;
    fn for_each_span<F>(&self, f: F)
    where
        F: FnMut(i32);
    fn span_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=i32>>;
    fn leading_comments(&self) -> &str;
    fn trailing_comments(&self) -> &str;
    fn for_each_leading_detached_comments<F>(&self, f: F)
    where
        F: FnMut(&str);
    fn leading_detached_comments_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&str>>;
}
impl LocationTrait for Location {
    fn for_each_path<F>(&self, f: F)
    where
        F: FnMut(i32) {
        for item in &self.path {
            (f)(item);
        }
    }
    fn path_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=i32>> {
        ::std::boxed::Box::new(self.path.iter().cloned())
    }
    fn for_each_span<F>(&self, f: F)
    where
        F: FnMut(i32) {
        for item in &self.span {
            (f)(item);
        }
    }
    fn span_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=i32>> {
        ::std::boxed::Box::new(self.span.iter().cloned())
    }
    fn leading_comments(&self) -> &str {
        &self.leading_comments
    }
    fn trailing_comments(&self) -> &str {
        &self.trailing_comments
    }
    fn for_each_leading_detached_comments<F>(&self, f: F)
    where
        F: FnMut(&str) {
        for item in &self.leading_detached_comments {
            (f)(item);
        }
    }
    fn leading_detached_comments_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&str>> {
        ::std::boxed::Box::new(self.leading_detached_comments.iter().cloned())
    }
}
} // mod source_code_info
#[derive(Debug, Clone)]
pub struct UninterpretedOption {
    pub name: ::std::vec::Vec<super::super::google::protobuf::uninterpreted_option::NamePart>,
    pub identifier_value: ::std::string::String,
    pub positive_int_value: u64,
    pub negative_int_value: i64,
    pub double_value: f64,
    pub string_value: ::std::vec::Vec<u8>,
    pub aggregate_value: ::std::string::String,
}
impl ::std::default::Default for UninterpretedOption {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            name: ::std::default::Default::default(),
            identifier_value: ::std::default::Default::default(),
            positive_int_value: ::std::default::Default::default(),
            negative_int_value: ::std::default::Default::default(),
            double_value: ::std::default::Default::default(),
            string_value: ::std::default::Default::default(),
            aggregate_value: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut UninterpretedOption {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                2 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                3 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                4 => {
                    *self.positive_int_value.push_and_get_mut() = variant.to_native::<::puroro::tags::UInt64>()?;
                }
                5 => {
                    *self.negative_int_value.push_and_get_mut() = variant.to_native::<::puroro::tags::Int64>()?;
                }
                6 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                7 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                8 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                2 => {
                    let msg = self.name.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                3 => {
                    *self.identifier_value.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                4 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::UInt64>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.positive_int_value, first, iter);
                }
                5 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Int64>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.negative_int_value, first, iter);
                }
                6 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                7 => {
                    *self.string_value.push_and_get_mut()
                        = ldd.deserialize_as_bytes().collect::<::puroro::Result<_>>()?;
                }
                8 => {
                    *self.aggregate_value.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                2 | 3 | 4 | 5 | 6 | 7 | 8 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                6 => {
                    *self.double_value.push_and_get_mut() = f64::from_le_bytes(bytes);
                }
                2 | 3 | 4 | 5 | 7 | 8 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for UninterpretedOption {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <UninterpretedOption as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for UninterpretedOption {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        for msg in self.name.iter_for_ser() {
            serializer.serialize_message_twice(2, msg)?;
        }
        for string in self.identifier_value.iter_for_ser() {
            serializer.serialize_bytes_twice(3, string.bytes().map(|b| Ok(b)))?;
        }
        serializer.serialize_variants_twice::<::puroro::tags::UInt64, _>(
            4, 
            self.positive_int_value.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Int64, _>(
            5, 
            self.negative_int_value.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        for item in self.double_value.iter_for_ser() {
            serializer.serialize_fixed_bits(6, item.to_le_bytes())?;
        }
        for bytes in self.string_value.iter_for_ser() {
            serializer.serialize_bytes_twice(7, bytes.iter().map(|b| Ok(*b)))?;
        }
        for string in self.aggregate_value.iter_for_ser() {
            serializer.serialize_bytes_twice(8, string.bytes().map(|b| Ok(b)))?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for UninterpretedOption {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait UninterpretedOptionTrait {
    fn for_each_name<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::uninterpreted_option::NamePart);
    fn name_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::uninterpreted_option::NamePart>>;
    fn identifier_value(&self) -> &str;
    fn positive_int_value(&self) -> u64;
    fn negative_int_value(&self) -> i64;
    fn double_value(&self) -> f64;
    fn string_value(&self) -> &[u8];
    fn aggregate_value(&self) -> &str;
}
impl UninterpretedOptionTrait for UninterpretedOption {
    fn for_each_name<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::uninterpreted_option::NamePart) {
        for item in &self.name {
            (f)(item);
        }
    }
    fn name_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::uninterpreted_option::NamePart>> {
        ::std::boxed::Box::new(self.name.iter())
    }
    fn identifier_value(&self) -> &str {
        &self.identifier_value
    }
    fn positive_int_value(&self) -> u64 {
        &self.positive_int_value
    }
    fn negative_int_value(&self) -> i64 {
        &self.negative_int_value
    }
    fn double_value(&self) -> f64 {
        &self.double_value
    }
    fn string_value(&self) -> &[u8] {
        &self.string_value
    }
    fn aggregate_value(&self) -> &str {
        &self.aggregate_value
    }
}
pub mod uninterpreted_option {
#[derive(Debug, Clone)]
pub struct NamePart {
    pub name_part: ::std::string::String,
    pub is_extension: bool,
}
impl ::std::default::Default for NamePart {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            name_part: ::std::default::Default::default(),
            is_extension: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut NamePart {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                2 => {
                    *self.is_extension.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    *self.name_part.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                2 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.is_extension, first, iter);
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 2 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 2 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for NamePart {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <NamePart as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for NamePart {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        for string in self.name_part.iter_for_ser() {
            serializer.serialize_bytes_twice(1, string.bytes().map(|b| Ok(b)))?;
        }
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            2, 
            self.is_extension.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        Ok(())
    }
}
impl ::puroro::Serializable for NamePart {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait NamePartTrait {
    fn name_part(&self) -> &str;
    fn is_extension(&self) -> bool;
}
impl NamePartTrait for NamePart {
    fn name_part(&self) -> &str {
        &self.name_part
    }
    fn is_extension(&self) -> bool {
        &self.is_extension
    }
}
} // mod uninterpreted_option
#[derive(Debug, Clone)]
pub struct MethodOptions {
    pub deprecated: bool,
    pub idempotency_level: ::std::result::Result<super::super::google::protobuf::method_options::IdempotencyLevel, i32>,
    pub uninterpreted_option: ::std::vec::Vec<super::super::google::protobuf::UninterpretedOption>,
}
impl ::std::default::Default for MethodOptions {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            deprecated: ::std::default::Default::default(),
            idempotency_level: 0i32.try_into(),
            uninterpreted_option: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut MethodOptions {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                33 => {
                    *self.deprecated.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                34 => {
                    *self.idempotency_level.push_and_get_mut() = variant.to_native::<::puroro::tags::Enum<super::super::google::protobuf::method_options::IdempotencyLevel>>()?;
                }
                999 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                33 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.deprecated, first, iter);
                }
                34 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Enum<super::super::google::protobuf::method_options::IdempotencyLevel>>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.idempotency_level, first, iter);
                }
                999 => {
                    let msg = self.uninterpreted_option.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                33 | 34 | 999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                33 | 34 | 999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for MethodOptions {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <MethodOptions as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for MethodOptions {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            33, 
            self.deprecated.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Enum<super::super::google::protobuf::method_options::IdempotencyLevel>, _>(
            34, 
            self.idempotency_level.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        for msg in self.uninterpreted_option.iter_for_ser() {
            serializer.serialize_message_twice(999, msg)?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for MethodOptions {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait MethodOptionsTrait {
    fn deprecated(&self) -> bool;
    fn idempotency_level(&self) -> ::std::result::Result<super::super::google::protobuf::method_options::IdempotencyLevel, i32>;
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption);
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>>;
}
impl MethodOptionsTrait for MethodOptions {
    fn deprecated(&self) -> bool {
        &self.deprecated
    }
    fn idempotency_level(&self) -> ::std::result::Result<super::super::google::protobuf::method_options::IdempotencyLevel, i32> {
        &self.idempotency_level
    }
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption) {
        for item in &self.uninterpreted_option {
            (f)(item);
        }
    }
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>> {
        ::std::boxed::Box::new(self.uninterpreted_option.iter())
    }
}
pub mod method_options {
#[derive(Debug, Clone)]
pub enum IdempotencyLevel {
    IdempotencyUnknown = 0,
    NoSideEffects = 1,
    Idempotent = 2,
}
impl ::std::convert::TryFrom<i32> for IdempotencyLevel {
    type Error = i32;
    fn try_from(val: i32) -> ::std::result::Result<Self, i32> {
        match val {
            0 => Ok(Self::IdempotencyUnknown),
            1 => Ok(Self::NoSideEffects),
            2 => Ok(Self::Idempotent),
            x => Err(x),
        }
    }
}
impl ::std::convert::Into<i32> for IdempotencyLevel {
    fn into(self) -> i32 {
        self as i32
    }
}
} // mod method_options
#[derive(Debug, Clone)]
pub struct ServiceOptions {
    pub deprecated: bool,
    pub uninterpreted_option: ::std::vec::Vec<super::super::google::protobuf::UninterpretedOption>,
}
impl ::std::default::Default for ServiceOptions {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            deprecated: ::std::default::Default::default(),
            uninterpreted_option: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut ServiceOptions {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                33 => {
                    *self.deprecated.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                999 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                33 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.deprecated, first, iter);
                }
                999 => {
                    let msg = self.uninterpreted_option.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                33 | 999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                33 | 999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for ServiceOptions {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <ServiceOptions as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for ServiceOptions {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            33, 
            self.deprecated.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        for msg in self.uninterpreted_option.iter_for_ser() {
            serializer.serialize_message_twice(999, msg)?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for ServiceOptions {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait ServiceOptionsTrait {
    fn deprecated(&self) -> bool;
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption);
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>>;
}
impl ServiceOptionsTrait for ServiceOptions {
    fn deprecated(&self) -> bool {
        &self.deprecated
    }
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption) {
        for item in &self.uninterpreted_option {
            (f)(item);
        }
    }
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>> {
        ::std::boxed::Box::new(self.uninterpreted_option.iter())
    }
}
#[derive(Debug, Clone)]
pub struct EnumValueOptions {
    pub deprecated: bool,
    pub uninterpreted_option: ::std::vec::Vec<super::super::google::protobuf::UninterpretedOption>,
}
impl ::std::default::Default for EnumValueOptions {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            deprecated: ::std::default::Default::default(),
            uninterpreted_option: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut EnumValueOptions {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => {
                    *self.deprecated.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                999 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.deprecated, first, iter);
                }
                999 => {
                    let msg = self.uninterpreted_option.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for EnumValueOptions {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <EnumValueOptions as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for EnumValueOptions {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            1, 
            self.deprecated.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        for msg in self.uninterpreted_option.iter_for_ser() {
            serializer.serialize_message_twice(999, msg)?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for EnumValueOptions {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait EnumValueOptionsTrait {
    fn deprecated(&self) -> bool;
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption);
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>>;
}
impl EnumValueOptionsTrait for EnumValueOptions {
    fn deprecated(&self) -> bool {
        &self.deprecated
    }
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption) {
        for item in &self.uninterpreted_option {
            (f)(item);
        }
    }
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>> {
        ::std::boxed::Box::new(self.uninterpreted_option.iter())
    }
}
#[derive(Debug, Clone)]
pub struct EnumOptions {
    pub allow_alias: bool,
    pub deprecated: bool,
    pub uninterpreted_option: ::std::vec::Vec<super::super::google::protobuf::UninterpretedOption>,
}
impl ::std::default::Default for EnumOptions {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            allow_alias: ::std::default::Default::default(),
            deprecated: ::std::default::Default::default(),
            uninterpreted_option: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut EnumOptions {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                2 => {
                    *self.allow_alias.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                3 => {
                    *self.deprecated.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                999 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                2 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.allow_alias, first, iter);
                }
                3 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.deprecated, first, iter);
                }
                999 => {
                    let msg = self.uninterpreted_option.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                2 | 3 | 999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                2 | 3 | 999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for EnumOptions {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <EnumOptions as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for EnumOptions {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            2, 
            self.allow_alias.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            3, 
            self.deprecated.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        for msg in self.uninterpreted_option.iter_for_ser() {
            serializer.serialize_message_twice(999, msg)?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for EnumOptions {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait EnumOptionsTrait {
    fn allow_alias(&self) -> bool;
    fn deprecated(&self) -> bool;
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption);
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>>;
}
impl EnumOptionsTrait for EnumOptions {
    fn allow_alias(&self) -> bool {
        &self.allow_alias
    }
    fn deprecated(&self) -> bool {
        &self.deprecated
    }
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption) {
        for item in &self.uninterpreted_option {
            (f)(item);
        }
    }
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>> {
        ::std::boxed::Box::new(self.uninterpreted_option.iter())
    }
}
#[derive(Debug, Clone)]
pub struct OneofOptions {
    pub uninterpreted_option: ::std::vec::Vec<super::super::google::protobuf::UninterpretedOption>,
}
impl ::std::default::Default for OneofOptions {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            uninterpreted_option: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut OneofOptions {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                999 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                999 => {
                    let msg = self.uninterpreted_option.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for OneofOptions {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <OneofOptions as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for OneofOptions {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        for msg in self.uninterpreted_option.iter_for_ser() {
            serializer.serialize_message_twice(999, msg)?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for OneofOptions {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait OneofOptionsTrait {
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption);
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>>;
}
impl OneofOptionsTrait for OneofOptions {
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption) {
        for item in &self.uninterpreted_option {
            (f)(item);
        }
    }
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>> {
        ::std::boxed::Box::new(self.uninterpreted_option.iter())
    }
}
#[derive(Debug, Clone)]
pub struct FieldOptions {
    pub ctype: ::std::result::Result<super::super::google::protobuf::field_options::Ctype, i32>,
    pub packed: bool,
    pub jstype: ::std::result::Result<super::super::google::protobuf::field_options::Jstype, i32>,
    pub lazy: bool,
    pub deprecated: bool,
    pub weak: bool,
    pub uninterpreted_option: ::std::vec::Vec<super::super::google::protobuf::UninterpretedOption>,
}
impl ::std::default::Default for FieldOptions {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            ctype: 0i32.try_into(),
            packed: ::std::default::Default::default(),
            jstype: 0i32.try_into(),
            lazy: ::std::default::Default::default(),
            deprecated: ::std::default::Default::default(),
            weak: ::std::default::Default::default(),
            uninterpreted_option: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut FieldOptions {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => {
                    *self.ctype.push_and_get_mut() = variant.to_native::<::puroro::tags::Enum<super::super::google::protobuf::field_options::Ctype>>()?;
                }
                2 => {
                    *self.packed.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                6 => {
                    *self.jstype.push_and_get_mut() = variant.to_native::<::puroro::tags::Enum<super::super::google::protobuf::field_options::Jstype>>()?;
                }
                5 => {
                    *self.lazy.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                3 => {
                    *self.deprecated.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                10 => {
                    *self.weak.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                999 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Enum<super::super::google::protobuf::field_options::Ctype>>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.ctype, first, iter);
                }
                2 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.packed, first, iter);
                }
                6 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Enum<super::super::google::protobuf::field_options::Jstype>>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.jstype, first, iter);
                }
                5 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.lazy, first, iter);
                }
                3 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.deprecated, first, iter);
                }
                10 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.weak, first, iter);
                }
                999 => {
                    let msg = self.uninterpreted_option.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 2 | 6 | 5 | 3 | 10 | 999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 2 | 6 | 5 | 3 | 10 | 999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for FieldOptions {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <FieldOptions as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for FieldOptions {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        serializer.serialize_variants_twice::<::puroro::tags::Enum<super::super::google::protobuf::field_options::Ctype>, _>(
            1, 
            self.ctype.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            2, 
            self.packed.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Enum<super::super::google::protobuf::field_options::Jstype>, _>(
            6, 
            self.jstype.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            5, 
            self.lazy.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            3, 
            self.deprecated.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            10, 
            self.weak.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        for msg in self.uninterpreted_option.iter_for_ser() {
            serializer.serialize_message_twice(999, msg)?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for FieldOptions {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait FieldOptionsTrait {
    fn ctype(&self) -> ::std::result::Result<super::super::google::protobuf::field_options::Ctype, i32>;
    fn packed(&self) -> bool;
    fn jstype(&self) -> ::std::result::Result<super::super::google::protobuf::field_options::Jstype, i32>;
    fn lazy(&self) -> bool;
    fn deprecated(&self) -> bool;
    fn weak(&self) -> bool;
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption);
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>>;
}
impl FieldOptionsTrait for FieldOptions {
    fn ctype(&self) -> ::std::result::Result<super::super::google::protobuf::field_options::Ctype, i32> {
        &self.ctype
    }
    fn packed(&self) -> bool {
        &self.packed
    }
    fn jstype(&self) -> ::std::result::Result<super::super::google::protobuf::field_options::Jstype, i32> {
        &self.jstype
    }
    fn lazy(&self) -> bool {
        &self.lazy
    }
    fn deprecated(&self) -> bool {
        &self.deprecated
    }
    fn weak(&self) -> bool {
        &self.weak
    }
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption) {
        for item in &self.uninterpreted_option {
            (f)(item);
        }
    }
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>> {
        ::std::boxed::Box::new(self.uninterpreted_option.iter())
    }
}
pub mod field_options {
#[derive(Debug, Clone)]
pub enum Jstype {
    JsNormal = 0,
    JsString = 1,
    JsNumber = 2,
}
impl ::std::convert::TryFrom<i32> for Jstype {
    type Error = i32;
    fn try_from(val: i32) -> ::std::result::Result<Self, i32> {
        match val {
            0 => Ok(Self::JsNormal),
            1 => Ok(Self::JsString),
            2 => Ok(Self::JsNumber),
            x => Err(x),
        }
    }
}
impl ::std::convert::Into<i32> for Jstype {
    fn into(self) -> i32 {
        self as i32
    }
}
#[derive(Debug, Clone)]
pub enum Ctype {
    String = 0,
    Cord = 1,
    StringPiece = 2,
}
impl ::std::convert::TryFrom<i32> for Ctype {
    type Error = i32;
    fn try_from(val: i32) -> ::std::result::Result<Self, i32> {
        match val {
            0 => Ok(Self::String),
            1 => Ok(Self::Cord),
            2 => Ok(Self::StringPiece),
            x => Err(x),
        }
    }
}
impl ::std::convert::Into<i32> for Ctype {
    fn into(self) -> i32 {
        self as i32
    }
}
} // mod field_options
#[derive(Debug, Clone)]
pub struct MessageOptions {
    pub message_set_wire_format: bool,
    pub no_standard_descriptor_accessor: bool,
    pub deprecated: bool,
    pub map_entry: bool,
    pub uninterpreted_option: ::std::vec::Vec<super::super::google::protobuf::UninterpretedOption>,
}
impl ::std::default::Default for MessageOptions {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            message_set_wire_format: ::std::default::Default::default(),
            no_standard_descriptor_accessor: ::std::default::Default::default(),
            deprecated: ::std::default::Default::default(),
            map_entry: ::std::default::Default::default(),
            uninterpreted_option: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut MessageOptions {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => {
                    *self.message_set_wire_format.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                2 => {
                    *self.no_standard_descriptor_accessor.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                3 => {
                    *self.deprecated.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                7 => {
                    *self.map_entry.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                999 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.message_set_wire_format, first, iter);
                }
                2 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.no_standard_descriptor_accessor, first, iter);
                }
                3 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.deprecated, first, iter);
                }
                7 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.map_entry, first, iter);
                }
                999 => {
                    let msg = self.uninterpreted_option.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 2 | 3 | 7 | 999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 2 | 3 | 7 | 999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for MessageOptions {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <MessageOptions as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for MessageOptions {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            1, 
            self.message_set_wire_format.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            2, 
            self.no_standard_descriptor_accessor.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            3, 
            self.deprecated.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            7, 
            self.map_entry.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        for msg in self.uninterpreted_option.iter_for_ser() {
            serializer.serialize_message_twice(999, msg)?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for MessageOptions {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait MessageOptionsTrait {
    fn message_set_wire_format(&self) -> bool;
    fn no_standard_descriptor_accessor(&self) -> bool;
    fn deprecated(&self) -> bool;
    fn map_entry(&self) -> bool;
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption);
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>>;
}
impl MessageOptionsTrait for MessageOptions {
    fn message_set_wire_format(&self) -> bool {
        &self.message_set_wire_format
    }
    fn no_standard_descriptor_accessor(&self) -> bool {
        &self.no_standard_descriptor_accessor
    }
    fn deprecated(&self) -> bool {
        &self.deprecated
    }
    fn map_entry(&self) -> bool {
        &self.map_entry
    }
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption) {
        for item in &self.uninterpreted_option {
            (f)(item);
        }
    }
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>> {
        ::std::boxed::Box::new(self.uninterpreted_option.iter())
    }
}
#[derive(Debug, Clone)]
pub struct FileOptions {
    pub java_package: ::std::string::String,
    pub java_outer_classname: ::std::string::String,
    pub java_multiple_files: bool,
    pub java_generate_equals_and_hash: bool,
    pub java_string_check_utf8: bool,
    pub optimize_for: ::std::result::Result<super::super::google::protobuf::file_options::OptimizeMode, i32>,
    pub go_package: ::std::string::String,
    pub cc_generic_services: bool,
    pub java_generic_services: bool,
    pub py_generic_services: bool,
    pub php_generic_services: bool,
    pub deprecated: bool,
    pub cc_enable_arenas: bool,
    pub objc_class_prefix: ::std::string::String,
    pub csharp_namespace: ::std::string::String,
    pub swift_prefix: ::std::string::String,
    pub php_class_prefix: ::std::string::String,
    pub php_namespace: ::std::string::String,
    pub php_metadata_namespace: ::std::string::String,
    pub ruby_package: ::std::string::String,
    pub uninterpreted_option: ::std::vec::Vec<super::super::google::protobuf::UninterpretedOption>,
}
impl ::std::default::Default for FileOptions {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            java_package: ::std::default::Default::default(),
            java_outer_classname: ::std::default::Default::default(),
            java_multiple_files: ::std::default::Default::default(),
            java_generate_equals_and_hash: ::std::default::Default::default(),
            java_string_check_utf8: ::std::default::Default::default(),
            optimize_for: 0i32.try_into(),
            go_package: ::std::default::Default::default(),
            cc_generic_services: ::std::default::Default::default(),
            java_generic_services: ::std::default::Default::default(),
            py_generic_services: ::std::default::Default::default(),
            php_generic_services: ::std::default::Default::default(),
            deprecated: ::std::default::Default::default(),
            cc_enable_arenas: ::std::default::Default::default(),
            objc_class_prefix: ::std::default::Default::default(),
            csharp_namespace: ::std::default::Default::default(),
            swift_prefix: ::std::default::Default::default(),
            php_class_prefix: ::std::default::Default::default(),
            php_namespace: ::std::default::Default::default(),
            php_metadata_namespace: ::std::default::Default::default(),
            ruby_package: ::std::default::Default::default(),
            uninterpreted_option: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut FileOptions {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                8 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                10 => {
                    *self.java_multiple_files.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                20 => {
                    *self.java_generate_equals_and_hash.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                27 => {
                    *self.java_string_check_utf8.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                9 => {
                    *self.optimize_for.push_and_get_mut() = variant.to_native::<::puroro::tags::Enum<super::super::google::protobuf::file_options::OptimizeMode>>()?;
                }
                11 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                16 => {
                    *self.cc_generic_services.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                17 => {
                    *self.java_generic_services.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                18 => {
                    *self.py_generic_services.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                42 => {
                    *self.php_generic_services.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                23 => {
                    *self.deprecated.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                31 => {
                    *self.cc_enable_arenas.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                36 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                37 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                39 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                40 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                41 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                44 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                45 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                999 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    *self.java_package.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                8 => {
                    *self.java_outer_classname.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                10 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.java_multiple_files, first, iter);
                }
                20 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.java_generate_equals_and_hash, first, iter);
                }
                27 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.java_string_check_utf8, first, iter);
                }
                9 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Enum<super::super::google::protobuf::file_options::OptimizeMode>>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.optimize_for, first, iter);
                }
                11 => {
                    *self.go_package.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                16 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.cc_generic_services, first, iter);
                }
                17 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.java_generic_services, first, iter);
                }
                18 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.py_generic_services, first, iter);
                }
                42 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.php_generic_services, first, iter);
                }
                23 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.deprecated, first, iter);
                }
                31 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.cc_enable_arenas, first, iter);
                }
                36 => {
                    *self.objc_class_prefix.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                37 => {
                    *self.csharp_namespace.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                39 => {
                    *self.swift_prefix.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                40 => {
                    *self.php_class_prefix.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                41 => {
                    *self.php_namespace.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                44 => {
                    *self.php_metadata_namespace.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                45 => {
                    *self.ruby_package.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                999 => {
                    let msg = self.uninterpreted_option.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 8 | 10 | 20 | 27 | 9 | 11 | 16 | 17 | 18 | 42 | 23 | 31 | 36 | 37 | 39 | 40 | 41 | 44 | 45 | 999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 8 | 10 | 20 | 27 | 9 | 11 | 16 | 17 | 18 | 42 | 23 | 31 | 36 | 37 | 39 | 40 | 41 | 44 | 45 | 999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for FileOptions {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <FileOptions as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for FileOptions {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        for string in self.java_package.iter_for_ser() {
            serializer.serialize_bytes_twice(1, string.bytes().map(|b| Ok(b)))?;
        }
        for string in self.java_outer_classname.iter_for_ser() {
            serializer.serialize_bytes_twice(8, string.bytes().map(|b| Ok(b)))?;
        }
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            10, 
            self.java_multiple_files.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            20, 
            self.java_generate_equals_and_hash.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            27, 
            self.java_string_check_utf8.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Enum<super::super::google::protobuf::file_options::OptimizeMode>, _>(
            9, 
            self.optimize_for.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        for string in self.go_package.iter_for_ser() {
            serializer.serialize_bytes_twice(11, string.bytes().map(|b| Ok(b)))?;
        }
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            16, 
            self.cc_generic_services.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            17, 
            self.java_generic_services.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            18, 
            self.py_generic_services.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            42, 
            self.php_generic_services.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            23, 
            self.deprecated.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            31, 
            self.cc_enable_arenas.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        for string in self.objc_class_prefix.iter_for_ser() {
            serializer.serialize_bytes_twice(36, string.bytes().map(|b| Ok(b)))?;
        }
        for string in self.csharp_namespace.iter_for_ser() {
            serializer.serialize_bytes_twice(37, string.bytes().map(|b| Ok(b)))?;
        }
        for string in self.swift_prefix.iter_for_ser() {
            serializer.serialize_bytes_twice(39, string.bytes().map(|b| Ok(b)))?;
        }
        for string in self.php_class_prefix.iter_for_ser() {
            serializer.serialize_bytes_twice(40, string.bytes().map(|b| Ok(b)))?;
        }
        for string in self.php_namespace.iter_for_ser() {
            serializer.serialize_bytes_twice(41, string.bytes().map(|b| Ok(b)))?;
        }
        for string in self.php_metadata_namespace.iter_for_ser() {
            serializer.serialize_bytes_twice(44, string.bytes().map(|b| Ok(b)))?;
        }
        for string in self.ruby_package.iter_for_ser() {
            serializer.serialize_bytes_twice(45, string.bytes().map(|b| Ok(b)))?;
        }
        for msg in self.uninterpreted_option.iter_for_ser() {
            serializer.serialize_message_twice(999, msg)?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for FileOptions {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait FileOptionsTrait {
    fn java_package(&self) -> &str;
    fn java_outer_classname(&self) -> &str;
    fn java_multiple_files(&self) -> bool;
    fn java_generate_equals_and_hash(&self) -> bool;
    fn java_string_check_utf8(&self) -> bool;
    fn optimize_for(&self) -> ::std::result::Result<super::super::google::protobuf::file_options::OptimizeMode, i32>;
    fn go_package(&self) -> &str;
    fn cc_generic_services(&self) -> bool;
    fn java_generic_services(&self) -> bool;
    fn py_generic_services(&self) -> bool;
    fn php_generic_services(&self) -> bool;
    fn deprecated(&self) -> bool;
    fn cc_enable_arenas(&self) -> bool;
    fn objc_class_prefix(&self) -> &str;
    fn csharp_namespace(&self) -> &str;
    fn swift_prefix(&self) -> &str;
    fn php_class_prefix(&self) -> &str;
    fn php_namespace(&self) -> &str;
    fn php_metadata_namespace(&self) -> &str;
    fn ruby_package(&self) -> &str;
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption);
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>>;
}
impl FileOptionsTrait for FileOptions {
    fn java_package(&self) -> &str {
        &self.java_package
    }
    fn java_outer_classname(&self) -> &str {
        &self.java_outer_classname
    }
    fn java_multiple_files(&self) -> bool {
        &self.java_multiple_files
    }
    fn java_generate_equals_and_hash(&self) -> bool {
        &self.java_generate_equals_and_hash
    }
    fn java_string_check_utf8(&self) -> bool {
        &self.java_string_check_utf8
    }
    fn optimize_for(&self) -> ::std::result::Result<super::super::google::protobuf::file_options::OptimizeMode, i32> {
        &self.optimize_for
    }
    fn go_package(&self) -> &str {
        &self.go_package
    }
    fn cc_generic_services(&self) -> bool {
        &self.cc_generic_services
    }
    fn java_generic_services(&self) -> bool {
        &self.java_generic_services
    }
    fn py_generic_services(&self) -> bool {
        &self.py_generic_services
    }
    fn php_generic_services(&self) -> bool {
        &self.php_generic_services
    }
    fn deprecated(&self) -> bool {
        &self.deprecated
    }
    fn cc_enable_arenas(&self) -> bool {
        &self.cc_enable_arenas
    }
    fn objc_class_prefix(&self) -> &str {
        &self.objc_class_prefix
    }
    fn csharp_namespace(&self) -> &str {
        &self.csharp_namespace
    }
    fn swift_prefix(&self) -> &str {
        &self.swift_prefix
    }
    fn php_class_prefix(&self) -> &str {
        &self.php_class_prefix
    }
    fn php_namespace(&self) -> &str {
        &self.php_namespace
    }
    fn php_metadata_namespace(&self) -> &str {
        &self.php_metadata_namespace
    }
    fn ruby_package(&self) -> &str {
        &self.ruby_package
    }
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption) {
        for item in &self.uninterpreted_option {
            (f)(item);
        }
    }
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>> {
        ::std::boxed::Box::new(self.uninterpreted_option.iter())
    }
}
pub mod file_options {
#[derive(Debug, Clone)]
pub enum OptimizeMode {
    Speed = 1,
    CodeSize = 2,
    LiteRuntime = 3,
}
impl ::std::convert::TryFrom<i32> for OptimizeMode {
    type Error = i32;
    fn try_from(val: i32) -> ::std::result::Result<Self, i32> {
        match val {
            1 => Ok(Self::Speed),
            2 => Ok(Self::CodeSize),
            3 => Ok(Self::LiteRuntime),
            x => Err(x),
        }
    }
}
impl ::std::convert::Into<i32> for OptimizeMode {
    fn into(self) -> i32 {
        self as i32
    }
}
} // mod file_options
#[derive(Debug, Clone)]
pub struct MethodDescriptorProto {
    pub name: ::std::string::String,
    pub input_type: ::std::string::String,
    pub output_type: ::std::string::String,
    pub options: ::std::option::Option<::std::boxed::Box<super::super::google::protobuf::MethodOptions>>,
    pub client_streaming: bool,
    pub server_streaming: bool,
}
impl ::std::default::Default for MethodDescriptorProto {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            name: ::std::default::Default::default(),
            input_type: ::std::default::Default::default(),
            output_type: ::std::default::Default::default(),
            options: ::std::default::Default::default(),
            client_streaming: ::std::default::Default::default(),
            server_streaming: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut MethodDescriptorProto {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                2 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                3 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                4 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                5 => {
                    *self.client_streaming.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                6 => {
                    *self.server_streaming.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    *self.name.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                2 => {
                    *self.input_type.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                3 => {
                    *self.output_type.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                4 => {
                    let msg = self.options.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                5 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.client_streaming, first, iter);
                }
                6 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.server_streaming, first, iter);
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 2 | 3 | 4 | 5 | 6 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 2 | 3 | 4 | 5 | 6 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for MethodDescriptorProto {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <MethodDescriptorProto as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for MethodDescriptorProto {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        for string in self.name.iter_for_ser() {
            serializer.serialize_bytes_twice(1, string.bytes().map(|b| Ok(b)))?;
        }
        for string in self.input_type.iter_for_ser() {
            serializer.serialize_bytes_twice(2, string.bytes().map(|b| Ok(b)))?;
        }
        for string in self.output_type.iter_for_ser() {
            serializer.serialize_bytes_twice(3, string.bytes().map(|b| Ok(b)))?;
        }
        for msg in self.options.iter_for_ser() {
            serializer.serialize_message_twice(4, msg)?;
        }
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            5, 
            self.client_streaming.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            6, 
            self.server_streaming.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        Ok(())
    }
}
impl ::puroro::Serializable for MethodDescriptorProto {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait MethodDescriptorProtoTrait {
    fn name(&self) -> &str;
    fn input_type(&self) -> &str;
    fn output_type(&self) -> &str;
    fn options(&self) -> ::std::option::Option<&super::super::google::protobuf::MethodOptions>;
    fn client_streaming(&self) -> bool;
    fn server_streaming(&self) -> bool;
}
impl MethodDescriptorProtoTrait for MethodDescriptorProto {
    fn name(&self) -> &str {
        &self.name
    }
    fn input_type(&self) -> &str {
        &self.input_type
    }
    fn output_type(&self) -> &str {
        &self.output_type
    }
    fn options(&self) -> ::std::option::Option<&super::super::google::protobuf::MethodOptions> {
        self.options.as_ref()
    }
    fn client_streaming(&self) -> bool {
        &self.client_streaming
    }
    fn server_streaming(&self) -> bool {
        &self.server_streaming
    }
}
#[derive(Debug, Clone)]
pub struct ServiceDescriptorProto {
    pub name: ::std::string::String,
    pub method: ::std::vec::Vec<super::super::google::protobuf::MethodDescriptorProto>,
    pub options: ::std::option::Option<::std::boxed::Box<super::super::google::protobuf::ServiceOptions>>,
}
impl ::std::default::Default for ServiceDescriptorProto {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            name: ::std::default::Default::default(),
            method: ::std::default::Default::default(),
            options: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut ServiceDescriptorProto {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                2 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                3 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    *self.name.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                2 => {
                    let msg = self.method.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                3 => {
                    let msg = self.options.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 2 | 3 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 2 | 3 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for ServiceDescriptorProto {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <ServiceDescriptorProto as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for ServiceDescriptorProto {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        for string in self.name.iter_for_ser() {
            serializer.serialize_bytes_twice(1, string.bytes().map(|b| Ok(b)))?;
        }
        for msg in self.method.iter_for_ser() {
            serializer.serialize_message_twice(2, msg)?;
        }
        for msg in self.options.iter_for_ser() {
            serializer.serialize_message_twice(3, msg)?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for ServiceDescriptorProto {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait ServiceDescriptorProtoTrait {
    fn name(&self) -> &str;
    fn for_each_method<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::MethodDescriptorProto);
    fn method_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::MethodDescriptorProto>>;
    fn options(&self) -> ::std::option::Option<&super::super::google::protobuf::ServiceOptions>;
}
impl ServiceDescriptorProtoTrait for ServiceDescriptorProto {
    fn name(&self) -> &str {
        &self.name
    }
    fn for_each_method<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::MethodDescriptorProto) {
        for item in &self.method {
            (f)(item);
        }
    }
    fn method_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::MethodDescriptorProto>> {
        ::std::boxed::Box::new(self.method.iter())
    }
    fn options(&self) -> ::std::option::Option<&super::super::google::protobuf::ServiceOptions> {
        self.options.as_ref()
    }
}
#[derive(Debug, Clone)]
pub struct EnumValueDescriptorProto {
    pub name: ::std::string::String,
    pub number: i32,
    pub options: ::std::option::Option<::std::boxed::Box<super::super::google::protobuf::EnumValueOptions>>,
}
impl ::std::default::Default for EnumValueDescriptorProto {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            name: ::std::default::Default::default(),
            number: ::std::default::Default::default(),
            options: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut EnumValueDescriptorProto {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                2 => {
                    *self.number.push_and_get_mut() = variant.to_native::<::puroro::tags::Int32>()?;
                }
                3 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    *self.name.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                2 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Int32>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.number, first, iter);
                }
                3 => {
                    let msg = self.options.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 2 | 3 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 2 | 3 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for EnumValueDescriptorProto {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <EnumValueDescriptorProto as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for EnumValueDescriptorProto {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        for string in self.name.iter_for_ser() {
            serializer.serialize_bytes_twice(1, string.bytes().map(|b| Ok(b)))?;
        }
        serializer.serialize_variants_twice::<::puroro::tags::Int32, _>(
            2, 
            self.number.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        for msg in self.options.iter_for_ser() {
            serializer.serialize_message_twice(3, msg)?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for EnumValueDescriptorProto {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait EnumValueDescriptorProtoTrait {
    fn name(&self) -> &str;
    fn number(&self) -> i32;
    fn options(&self) -> ::std::option::Option<&super::super::google::protobuf::EnumValueOptions>;
}
impl EnumValueDescriptorProtoTrait for EnumValueDescriptorProto {
    fn name(&self) -> &str {
        &self.name
    }
    fn number(&self) -> i32 {
        &self.number
    }
    fn options(&self) -> ::std::option::Option<&super::super::google::protobuf::EnumValueOptions> {
        self.options.as_ref()
    }
}
#[derive(Debug, Clone)]
pub struct EnumDescriptorProto {
    pub name: ::std::string::String,
    pub value: ::std::vec::Vec<super::super::google::protobuf::EnumValueDescriptorProto>,
    pub options: ::std::option::Option<::std::boxed::Box<super::super::google::protobuf::EnumOptions>>,
    pub reserved_range: ::std::vec::Vec<super::super::google::protobuf::enum_descriptor_proto::EnumReservedRange>,
    pub reserved_name: ::std::vec::Vec<::std::string::String>,
}
impl ::std::default::Default for EnumDescriptorProto {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            name: ::std::default::Default::default(),
            value: ::std::default::Default::default(),
            options: ::std::default::Default::default(),
            reserved_range: ::std::default::Default::default(),
            reserved_name: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut EnumDescriptorProto {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                2 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                3 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                4 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                5 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    *self.name.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                2 => {
                    let msg = self.value.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                3 => {
                    let msg = self.options.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                4 => {
                    let msg = self.reserved_range.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                5 => {
                    *self.reserved_name.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 2 | 3 | 4 | 5 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 2 | 3 | 4 | 5 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for EnumDescriptorProto {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <EnumDescriptorProto as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for EnumDescriptorProto {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        for string in self.name.iter_for_ser() {
            serializer.serialize_bytes_twice(1, string.bytes().map(|b| Ok(b)))?;
        }
        for msg in self.value.iter_for_ser() {
            serializer.serialize_message_twice(2, msg)?;
        }
        for msg in self.options.iter_for_ser() {
            serializer.serialize_message_twice(3, msg)?;
        }
        for msg in self.reserved_range.iter_for_ser() {
            serializer.serialize_message_twice(4, msg)?;
        }
        for string in self.reserved_name.iter_for_ser() {
            serializer.serialize_bytes_twice(5, string.bytes().map(|b| Ok(b)))?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for EnumDescriptorProto {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait EnumDescriptorProtoTrait {
    fn name(&self) -> &str;
    fn for_each_value<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::EnumValueDescriptorProto);
    fn value_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::EnumValueDescriptorProto>>;
    fn options(&self) -> ::std::option::Option<&super::super::google::protobuf::EnumOptions>;
    fn for_each_reserved_range<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::enum_descriptor_proto::EnumReservedRange);
    fn reserved_range_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::enum_descriptor_proto::EnumReservedRange>>;
    fn for_each_reserved_name<F>(&self, f: F)
    where
        F: FnMut(&str);
    fn reserved_name_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&str>>;
}
impl EnumDescriptorProtoTrait for EnumDescriptorProto {
    fn name(&self) -> &str {
        &self.name
    }
    fn for_each_value<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::EnumValueDescriptorProto) {
        for item in &self.value {
            (f)(item);
        }
    }
    fn value_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::EnumValueDescriptorProto>> {
        ::std::boxed::Box::new(self.value.iter())
    }
    fn options(&self) -> ::std::option::Option<&super::super::google::protobuf::EnumOptions> {
        self.options.as_ref()
    }
    fn for_each_reserved_range<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::enum_descriptor_proto::EnumReservedRange) {
        for item in &self.reserved_range {
            (f)(item);
        }
    }
    fn reserved_range_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::enum_descriptor_proto::EnumReservedRange>> {
        ::std::boxed::Box::new(self.reserved_range.iter())
    }
    fn for_each_reserved_name<F>(&self, f: F)
    where
        F: FnMut(&str) {
        for item in &self.reserved_name {
            (f)(item);
        }
    }
    fn reserved_name_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&str>> {
        ::std::boxed::Box::new(self.reserved_name.iter().cloned())
    }
}
pub mod enum_descriptor_proto {
#[derive(Debug, Clone)]
pub struct EnumReservedRange {
    pub start: i32,
    pub end: i32,
}
impl ::std::default::Default for EnumReservedRange {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            start: ::std::default::Default::default(),
            end: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut EnumReservedRange {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => {
                    *self.start.push_and_get_mut() = variant.to_native::<::puroro::tags::Int32>()?;
                }
                2 => {
                    *self.end.push_and_get_mut() = variant.to_native::<::puroro::tags::Int32>()?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Int32>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.start, first, iter);
                }
                2 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Int32>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.end, first, iter);
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 2 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 2 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for EnumReservedRange {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <EnumReservedRange as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for EnumReservedRange {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        serializer.serialize_variants_twice::<::puroro::tags::Int32, _>(
            1, 
            self.start.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Int32, _>(
            2, 
            self.end.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        Ok(())
    }
}
impl ::puroro::Serializable for EnumReservedRange {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait EnumReservedRangeTrait {
    fn start(&self) -> i32;
    fn end(&self) -> i32;
}
impl EnumReservedRangeTrait for EnumReservedRange {
    fn start(&self) -> i32 {
        &self.start
    }
    fn end(&self) -> i32 {
        &self.end
    }
}
} // mod enum_descriptor_proto
#[derive(Debug, Clone)]
pub struct OneofDescriptorProto {
    pub name: ::std::string::String,
    pub options: ::std::option::Option<::std::boxed::Box<super::super::google::protobuf::OneofOptions>>,
}
impl ::std::default::Default for OneofDescriptorProto {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            name: ::std::default::Default::default(),
            options: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut OneofDescriptorProto {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                2 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    *self.name.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                2 => {
                    let msg = self.options.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 2 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 2 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for OneofDescriptorProto {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <OneofDescriptorProto as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for OneofDescriptorProto {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        for string in self.name.iter_for_ser() {
            serializer.serialize_bytes_twice(1, string.bytes().map(|b| Ok(b)))?;
        }
        for msg in self.options.iter_for_ser() {
            serializer.serialize_message_twice(2, msg)?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for OneofDescriptorProto {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait OneofDescriptorProtoTrait {
    fn name(&self) -> &str;
    fn options(&self) -> ::std::option::Option<&super::super::google::protobuf::OneofOptions>;
}
impl OneofDescriptorProtoTrait for OneofDescriptorProto {
    fn name(&self) -> &str {
        &self.name
    }
    fn options(&self) -> ::std::option::Option<&super::super::google::protobuf::OneofOptions> {
        self.options.as_ref()
    }
}
#[derive(Debug, Clone)]
pub struct FieldDescriptorProto {
    pub name: ::std::string::String,
    pub number: i32,
    pub label: ::std::result::Result<super::super::google::protobuf::field_descriptor_proto::Label, i32>,
    pub type_: ::std::result::Result<super::super::google::protobuf::field_descriptor_proto::Type, i32>,
    pub type_name: ::std::string::String,
    pub extendee: ::std::string::String,
    pub default_value: ::std::string::String,
    pub oneof_index: i32,
    pub json_name: ::std::string::String,
    pub options: ::std::option::Option<::std::boxed::Box<super::super::google::protobuf::FieldOptions>>,
    pub proto3_optional: bool,
}
impl ::std::default::Default for FieldDescriptorProto {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            name: ::std::default::Default::default(),
            number: ::std::default::Default::default(),
            label: 0i32.try_into(),
            type_: 0i32.try_into(),
            type_name: ::std::default::Default::default(),
            extendee: ::std::default::Default::default(),
            default_value: ::std::default::Default::default(),
            oneof_index: ::std::default::Default::default(),
            json_name: ::std::default::Default::default(),
            options: ::std::default::Default::default(),
            proto3_optional: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut FieldDescriptorProto {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                3 => {
                    *self.number.push_and_get_mut() = variant.to_native::<::puroro::tags::Int32>()?;
                }
                4 => {
                    *self.label.push_and_get_mut() = variant.to_native::<::puroro::tags::Enum<super::super::google::protobuf::field_descriptor_proto::Label>>()?;
                }
                5 => {
                    *self.type_.push_and_get_mut() = variant.to_native::<::puroro::tags::Enum<super::super::google::protobuf::field_descriptor_proto::Type>>()?;
                }
                6 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                2 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                7 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                9 => {
                    *self.oneof_index.push_and_get_mut() = variant.to_native::<::puroro::tags::Int32>()?;
                }
                10 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                8 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                17 => {
                    *self.proto3_optional.push_and_get_mut() = variant.to_native::<::puroro::tags::Bool>()?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    *self.name.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                3 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Int32>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.number, first, iter);
                }
                4 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Enum<super::super::google::protobuf::field_descriptor_proto::Label>>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.label, first, iter);
                }
                5 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Enum<super::super::google::protobuf::field_descriptor_proto::Type>>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.type_, first, iter);
                }
                6 => {
                    *self.type_name.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                2 => {
                    *self.extendee.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                7 => {
                    *self.default_value.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                9 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Int32>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.oneof_index, first, iter);
                }
                10 => {
                    *self.json_name.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                8 => {
                    let msg = self.options.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                17 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Bool>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.proto3_optional, first, iter);
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 3 | 4 | 5 | 6 | 2 | 7 | 9 | 10 | 8 | 17 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 3 | 4 | 5 | 6 | 2 | 7 | 9 | 10 | 8 | 17 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for FieldDescriptorProto {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <FieldDescriptorProto as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for FieldDescriptorProto {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        for string in self.name.iter_for_ser() {
            serializer.serialize_bytes_twice(1, string.bytes().map(|b| Ok(b)))?;
        }
        serializer.serialize_variants_twice::<::puroro::tags::Int32, _>(
            3, 
            self.number.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Enum<super::super::google::protobuf::field_descriptor_proto::Label>, _>(
            4, 
            self.label.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Enum<super::super::google::protobuf::field_descriptor_proto::Type>, _>(
            5, 
            self.type_.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        for string in self.type_name.iter_for_ser() {
            serializer.serialize_bytes_twice(6, string.bytes().map(|b| Ok(b)))?;
        }
        for string in self.extendee.iter_for_ser() {
            serializer.serialize_bytes_twice(2, string.bytes().map(|b| Ok(b)))?;
        }
        for string in self.default_value.iter_for_ser() {
            serializer.serialize_bytes_twice(7, string.bytes().map(|b| Ok(b)))?;
        }
        serializer.serialize_variants_twice::<::puroro::tags::Int32, _>(
            9, 
            self.oneof_index.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        for string in self.json_name.iter_for_ser() {
            serializer.serialize_bytes_twice(10, string.bytes().map(|b| Ok(b)))?;
        }
        for msg in self.options.iter_for_ser() {
            serializer.serialize_message_twice(8, msg)?;
        }
        serializer.serialize_variants_twice::<::puroro::tags::Bool, _>(
            17, 
            self.proto3_optional.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        Ok(())
    }
}
impl ::puroro::Serializable for FieldDescriptorProto {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait FieldDescriptorProtoTrait {
    fn name(&self) -> &str;
    fn number(&self) -> i32;
    fn label(&self) -> ::std::result::Result<super::super::google::protobuf::field_descriptor_proto::Label, i32>;
    fn type_(&self) -> ::std::result::Result<super::super::google::protobuf::field_descriptor_proto::Type, i32>;
    fn type_name(&self) -> &str;
    fn extendee(&self) -> &str;
    fn default_value(&self) -> &str;
    fn oneof_index(&self) -> i32;
    fn json_name(&self) -> &str;
    fn options(&self) -> ::std::option::Option<&super::super::google::protobuf::FieldOptions>;
    fn proto3_optional(&self) -> bool;
}
impl FieldDescriptorProtoTrait for FieldDescriptorProto {
    fn name(&self) -> &str {
        &self.name
    }
    fn number(&self) -> i32 {
        &self.number
    }
    fn label(&self) -> ::std::result::Result<super::super::google::protobuf::field_descriptor_proto::Label, i32> {
        &self.label
    }
    fn type_(&self) -> ::std::result::Result<super::super::google::protobuf::field_descriptor_proto::Type, i32> {
        &self.type_
    }
    fn type_name(&self) -> &str {
        &self.type_name
    }
    fn extendee(&self) -> &str {
        &self.extendee
    }
    fn default_value(&self) -> &str {
        &self.default_value
    }
    fn oneof_index(&self) -> i32 {
        &self.oneof_index
    }
    fn json_name(&self) -> &str {
        &self.json_name
    }
    fn options(&self) -> ::std::option::Option<&super::super::google::protobuf::FieldOptions> {
        self.options.as_ref()
    }
    fn proto3_optional(&self) -> bool {
        &self.proto3_optional
    }
}
pub mod field_descriptor_proto {
#[derive(Debug, Clone)]
pub enum Label {
    LabelOptional = 1,
    LabelRequired = 2,
    LabelRepeated = 3,
}
impl ::std::convert::TryFrom<i32> for Label {
    type Error = i32;
    fn try_from(val: i32) -> ::std::result::Result<Self, i32> {
        match val {
            1 => Ok(Self::LabelOptional),
            2 => Ok(Self::LabelRequired),
            3 => Ok(Self::LabelRepeated),
            x => Err(x),
        }
    }
}
impl ::std::convert::Into<i32> for Label {
    fn into(self) -> i32 {
        self as i32
    }
}
#[derive(Debug, Clone)]
pub enum Type {
    TypeDouble = 1,
    TypeFloat = 2,
    TypeInt64 = 3,
    TypeUint64 = 4,
    TypeInt32 = 5,
    TypeFixed64 = 6,
    TypeFixed32 = 7,
    TypeBool = 8,
    TypeString = 9,
    TypeGroup = 10,
    TypeMessage = 11,
    TypeBytes = 12,
    TypeUint32 = 13,
    TypeEnum = 14,
    TypeSfixed32 = 15,
    TypeSfixed64 = 16,
    TypeSint32 = 17,
    TypeSint64 = 18,
}
impl ::std::convert::TryFrom<i32> for Type {
    type Error = i32;
    fn try_from(val: i32) -> ::std::result::Result<Self, i32> {
        match val {
            1 => Ok(Self::TypeDouble),
            2 => Ok(Self::TypeFloat),
            3 => Ok(Self::TypeInt64),
            4 => Ok(Self::TypeUint64),
            5 => Ok(Self::TypeInt32),
            6 => Ok(Self::TypeFixed64),
            7 => Ok(Self::TypeFixed32),
            8 => Ok(Self::TypeBool),
            9 => Ok(Self::TypeString),
            10 => Ok(Self::TypeGroup),
            11 => Ok(Self::TypeMessage),
            12 => Ok(Self::TypeBytes),
            13 => Ok(Self::TypeUint32),
            14 => Ok(Self::TypeEnum),
            15 => Ok(Self::TypeSfixed32),
            16 => Ok(Self::TypeSfixed64),
            17 => Ok(Self::TypeSint32),
            18 => Ok(Self::TypeSint64),
            x => Err(x),
        }
    }
}
impl ::std::convert::Into<i32> for Type {
    fn into(self) -> i32 {
        self as i32
    }
}
} // mod field_descriptor_proto
#[derive(Debug, Clone)]
pub struct ExtensionRangeOptions {
    pub uninterpreted_option: ::std::vec::Vec<super::super::google::protobuf::UninterpretedOption>,
}
impl ::std::default::Default for ExtensionRangeOptions {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            uninterpreted_option: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut ExtensionRangeOptions {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                999 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                999 => {
                    let msg = self.uninterpreted_option.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                999 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for ExtensionRangeOptions {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <ExtensionRangeOptions as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for ExtensionRangeOptions {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        for msg in self.uninterpreted_option.iter_for_ser() {
            serializer.serialize_message_twice(999, msg)?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for ExtensionRangeOptions {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait ExtensionRangeOptionsTrait {
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption);
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>>;
}
impl ExtensionRangeOptionsTrait for ExtensionRangeOptions {
    fn for_each_uninterpreted_option<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::UninterpretedOption) {
        for item in &self.uninterpreted_option {
            (f)(item);
        }
    }
    fn uninterpreted_option_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::UninterpretedOption>> {
        ::std::boxed::Box::new(self.uninterpreted_option.iter())
    }
}
#[derive(Debug, Clone)]
pub struct DescriptorProto {
    pub name: ::std::string::String,
    pub field: ::std::vec::Vec<super::super::google::protobuf::FieldDescriptorProto>,
    pub extension: ::std::vec::Vec<super::super::google::protobuf::FieldDescriptorProto>,
    pub nested_type: ::std::vec::Vec<super::super::google::protobuf::DescriptorProto>,
    pub enum_type: ::std::vec::Vec<super::super::google::protobuf::EnumDescriptorProto>,
    pub extension_range: ::std::vec::Vec<super::super::google::protobuf::descriptor_proto::ExtensionRange>,
    pub oneof_decl: ::std::vec::Vec<super::super::google::protobuf::OneofDescriptorProto>,
    pub options: ::std::option::Option<::std::boxed::Box<super::super::google::protobuf::MessageOptions>>,
    pub reserved_range: ::std::vec::Vec<super::super::google::protobuf::descriptor_proto::ReservedRange>,
    pub reserved_name: ::std::vec::Vec<::std::string::String>,
}
impl ::std::default::Default for DescriptorProto {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            name: ::std::default::Default::default(),
            field: ::std::default::Default::default(),
            extension: ::std::default::Default::default(),
            nested_type: ::std::default::Default::default(),
            enum_type: ::std::default::Default::default(),
            extension_range: ::std::default::Default::default(),
            oneof_decl: ::std::default::Default::default(),
            options: ::std::default::Default::default(),
            reserved_range: ::std::default::Default::default(),
            reserved_name: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut DescriptorProto {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                2 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                6 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                3 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                4 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                5 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                8 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                7 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                9 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                10 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    *self.name.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                2 => {
                    let msg = self.field.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                6 => {
                    let msg = self.extension.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                3 => {
                    let msg = self.nested_type.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                4 => {
                    let msg = self.enum_type.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                5 => {
                    let msg = self.extension_range.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                8 => {
                    let msg = self.oneof_decl.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                7 => {
                    let msg = self.options.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                9 => {
                    let msg = self.reserved_range.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                10 => {
                    *self.reserved_name.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 2 | 6 | 3 | 4 | 5 | 8 | 7 | 9 | 10 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 2 | 6 | 3 | 4 | 5 | 8 | 7 | 9 | 10 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for DescriptorProto {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <DescriptorProto as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for DescriptorProto {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        for string in self.name.iter_for_ser() {
            serializer.serialize_bytes_twice(1, string.bytes().map(|b| Ok(b)))?;
        }
        for msg in self.field.iter_for_ser() {
            serializer.serialize_message_twice(2, msg)?;
        }
        for msg in self.extension.iter_for_ser() {
            serializer.serialize_message_twice(6, msg)?;
        }
        for msg in self.nested_type.iter_for_ser() {
            serializer.serialize_message_twice(3, msg)?;
        }
        for msg in self.enum_type.iter_for_ser() {
            serializer.serialize_message_twice(4, msg)?;
        }
        for msg in self.extension_range.iter_for_ser() {
            serializer.serialize_message_twice(5, msg)?;
        }
        for msg in self.oneof_decl.iter_for_ser() {
            serializer.serialize_message_twice(8, msg)?;
        }
        for msg in self.options.iter_for_ser() {
            serializer.serialize_message_twice(7, msg)?;
        }
        for msg in self.reserved_range.iter_for_ser() {
            serializer.serialize_message_twice(9, msg)?;
        }
        for string in self.reserved_name.iter_for_ser() {
            serializer.serialize_bytes_twice(10, string.bytes().map(|b| Ok(b)))?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for DescriptorProto {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait DescriptorProtoTrait {
    fn name(&self) -> &str;
    fn for_each_field<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::FieldDescriptorProto);
    fn field_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::FieldDescriptorProto>>;
    fn for_each_extension<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::FieldDescriptorProto);
    fn extension_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::FieldDescriptorProto>>;
    fn for_each_nested_type<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::DescriptorProto);
    fn nested_type_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::DescriptorProto>>;
    fn for_each_enum_type<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::EnumDescriptorProto);
    fn enum_type_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::EnumDescriptorProto>>;
    fn for_each_extension_range<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::descriptor_proto::ExtensionRange);
    fn extension_range_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::descriptor_proto::ExtensionRange>>;
    fn for_each_oneof_decl<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::OneofDescriptorProto);
    fn oneof_decl_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::OneofDescriptorProto>>;
    fn options(&self) -> ::std::option::Option<&super::super::google::protobuf::MessageOptions>;
    fn for_each_reserved_range<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::descriptor_proto::ReservedRange);
    fn reserved_range_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::descriptor_proto::ReservedRange>>;
    fn for_each_reserved_name<F>(&self, f: F)
    where
        F: FnMut(&str);
    fn reserved_name_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&str>>;
}
impl DescriptorProtoTrait for DescriptorProto {
    fn name(&self) -> &str {
        &self.name
    }
    fn for_each_field<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::FieldDescriptorProto) {
        for item in &self.field {
            (f)(item);
        }
    }
    fn field_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::FieldDescriptorProto>> {
        ::std::boxed::Box::new(self.field.iter())
    }
    fn for_each_extension<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::FieldDescriptorProto) {
        for item in &self.extension {
            (f)(item);
        }
    }
    fn extension_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::FieldDescriptorProto>> {
        ::std::boxed::Box::new(self.extension.iter())
    }
    fn for_each_nested_type<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::DescriptorProto) {
        for item in &self.nested_type {
            (f)(item);
        }
    }
    fn nested_type_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::DescriptorProto>> {
        ::std::boxed::Box::new(self.nested_type.iter())
    }
    fn for_each_enum_type<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::EnumDescriptorProto) {
        for item in &self.enum_type {
            (f)(item);
        }
    }
    fn enum_type_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::EnumDescriptorProto>> {
        ::std::boxed::Box::new(self.enum_type.iter())
    }
    fn for_each_extension_range<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::descriptor_proto::ExtensionRange) {
        for item in &self.extension_range {
            (f)(item);
        }
    }
    fn extension_range_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::descriptor_proto::ExtensionRange>> {
        ::std::boxed::Box::new(self.extension_range.iter())
    }
    fn for_each_oneof_decl<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::OneofDescriptorProto) {
        for item in &self.oneof_decl {
            (f)(item);
        }
    }
    fn oneof_decl_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::OneofDescriptorProto>> {
        ::std::boxed::Box::new(self.oneof_decl.iter())
    }
    fn options(&self) -> ::std::option::Option<&super::super::google::protobuf::MessageOptions> {
        self.options.as_ref()
    }
    fn for_each_reserved_range<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::descriptor_proto::ReservedRange) {
        for item in &self.reserved_range {
            (f)(item);
        }
    }
    fn reserved_range_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::descriptor_proto::ReservedRange>> {
        ::std::boxed::Box::new(self.reserved_range.iter())
    }
    fn for_each_reserved_name<F>(&self, f: F)
    where
        F: FnMut(&str) {
        for item in &self.reserved_name {
            (f)(item);
        }
    }
    fn reserved_name_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&str>> {
        ::std::boxed::Box::new(self.reserved_name.iter().cloned())
    }
}
pub mod descriptor_proto {
#[derive(Debug, Clone)]
pub struct ReservedRange {
    pub start: i32,
    pub end: i32,
}
impl ::std::default::Default for ReservedRange {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            start: ::std::default::Default::default(),
            end: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut ReservedRange {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => {
                    *self.start.push_and_get_mut() = variant.to_native::<::puroro::tags::Int32>()?;
                }
                2 => {
                    *self.end.push_and_get_mut() = variant.to_native::<::puroro::tags::Int32>()?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Int32>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.start, first, iter);
                }
                2 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Int32>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.end, first, iter);
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 2 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 2 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for ReservedRange {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <ReservedRange as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for ReservedRange {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        serializer.serialize_variants_twice::<::puroro::tags::Int32, _>(
            1, 
            self.start.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Int32, _>(
            2, 
            self.end.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        Ok(())
    }
}
impl ::puroro::Serializable for ReservedRange {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait ReservedRangeTrait {
    fn start(&self) -> i32;
    fn end(&self) -> i32;
}
impl ReservedRangeTrait for ReservedRange {
    fn start(&self) -> i32 {
        &self.start
    }
    fn end(&self) -> i32 {
        &self.end
    }
}
#[derive(Debug, Clone)]
pub struct ExtensionRange {
    pub start: i32,
    pub end: i32,
    pub options: ::std::option::Option<::std::boxed::Box<super::super::super::google::protobuf::ExtensionRangeOptions>>,
}
impl ::std::default::Default for ExtensionRange {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            start: ::std::default::Default::default(),
            end: ::std::default::Default::default(),
            options: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut ExtensionRange {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => {
                    *self.start.push_and_get_mut() = variant.to_native::<::puroro::tags::Int32>()?;
                }
                2 => {
                    *self.end.push_and_get_mut() = variant.to_native::<::puroro::tags::Int32>()?;
                }
                3 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Int32>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.start, first, iter);
                }
                2 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Int32>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.end, first, iter);
                }
                3 => {
                    let msg = self.options.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 2 | 3 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 2 | 3 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for ExtensionRange {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <ExtensionRange as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for ExtensionRange {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        serializer.serialize_variants_twice::<::puroro::tags::Int32, _>(
            1, 
            self.start.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Int32, _>(
            2, 
            self.end.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        for msg in self.options.iter_for_ser() {
            serializer.serialize_message_twice(3, msg)?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for ExtensionRange {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait ExtensionRangeTrait {
    fn start(&self) -> i32;
    fn end(&self) -> i32;
    fn options(&self) -> ::std::option::Option<&super::super::super::google::protobuf::ExtensionRangeOptions>;
}
impl ExtensionRangeTrait for ExtensionRange {
    fn start(&self) -> i32 {
        &self.start
    }
    fn end(&self) -> i32 {
        &self.end
    }
    fn options(&self) -> ::std::option::Option<&super::super::super::google::protobuf::ExtensionRangeOptions> {
        self.options.as_ref()
    }
}
} // mod descriptor_proto
#[derive(Debug, Clone)]
pub struct FileDescriptorProto {
    pub name: ::std::string::String,
    pub package: ::std::string::String,
    pub dependency: ::std::vec::Vec<::std::string::String>,
    pub public_dependency: ::std::vec::Vec<i32>,
    pub weak_dependency: ::std::vec::Vec<i32>,
    pub message_type: ::std::vec::Vec<super::super::google::protobuf::DescriptorProto>,
    pub enum_type: ::std::vec::Vec<super::super::google::protobuf::EnumDescriptorProto>,
    pub service: ::std::vec::Vec<super::super::google::protobuf::ServiceDescriptorProto>,
    pub extension: ::std::vec::Vec<super::super::google::protobuf::FieldDescriptorProto>,
    pub options: ::std::option::Option<::std::boxed::Box<super::super::google::protobuf::FileOptions>>,
    pub source_code_info: ::std::option::Option<::std::boxed::Box<super::super::google::protobuf::SourceCodeInfo>>,
    pub syntax: ::std::string::String,
}
impl ::std::default::Default for FileDescriptorProto {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            name: ::std::default::Default::default(),
            package: ::std::default::Default::default(),
            dependency: ::std::default::Default::default(),
            public_dependency: ::std::default::Default::default(),
            weak_dependency: ::std::default::Default::default(),
            message_type: ::std::default::Default::default(),
            enum_type: ::std::default::Default::default(),
            service: ::std::default::Default::default(),
            extension: ::std::default::Default::default(),
            options: ::std::default::Default::default(),
            source_code_info: ::std::default::Default::default(),
            syntax: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut FileDescriptorProto {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                2 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                3 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                10 => {
                    *self.public_dependency.push_and_get_mut() = variant.to_native::<::puroro::tags::Int32>()?;
                }
                11 => {
                    *self.weak_dependency.push_and_get_mut() = variant.to_native::<::puroro::tags::Int32>()?;
                }
                4 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                5 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                6 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                7 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                8 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                9 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                12 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    *self.name.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                2 => {
                    *self.package.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                3 => {
                    *self.dependency.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                10 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Int32>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.public_dependency, first, iter);
                }
                11 => {
                    let values = ldd.deserialize_as_variants().map(|rv| {
                        rv.and_then(|variant| variant.to_native::<::puroro::tags::Int32>())
                    }).collect::<::puroro::Result<::std::vec::Vec<_>>>()?;
                    let mut iter = values.into_iter();
                    let first = iter.next().ok_or(::puroro::PuroroError::ZeroLengthPackedField)?;
                    MaybeRepeatedVariantField::extend(&mut self.weak_dependency, first, iter);
                }
                4 => {
                    let msg = self.message_type.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                5 => {
                    let msg = self.enum_type.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                6 => {
                    let msg = self.service.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                7 => {
                    let msg = self.extension.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                8 => {
                    let msg = self.options.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                9 => {
                    let msg = self.source_code_info.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                12 => {
                    *self.syntax.push_and_get_mut()
                        = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 | 2 | 3 | 10 | 11 | 4 | 5 | 6 | 7 | 8 | 9 | 12 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 | 2 | 3 | 10 | 11 | 4 | 5 | 6 | 7 | 8 | 9 | 12 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for FileDescriptorProto {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <FileDescriptorProto as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for FileDescriptorProto {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        for string in self.name.iter_for_ser() {
            serializer.serialize_bytes_twice(1, string.bytes().map(|b| Ok(b)))?;
        }
        for string in self.package.iter_for_ser() {
            serializer.serialize_bytes_twice(2, string.bytes().map(|b| Ok(b)))?;
        }
        for string in self.dependency.iter_for_ser() {
            serializer.serialize_bytes_twice(3, string.bytes().map(|b| Ok(b)))?;
        }
        serializer.serialize_variants_twice::<::puroro::tags::Int32, _>(
            10, 
            self.public_dependency.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        serializer.serialize_variants_twice::<::puroro::tags::Int32, _>(
            11, 
            self.weak_dependency.iter_for_ser()
                .cloned()
                .map(|v| Ok(v)))?;
        for msg in self.message_type.iter_for_ser() {
            serializer.serialize_message_twice(4, msg)?;
        }
        for msg in self.enum_type.iter_for_ser() {
            serializer.serialize_message_twice(5, msg)?;
        }
        for msg in self.service.iter_for_ser() {
            serializer.serialize_message_twice(6, msg)?;
        }
        for msg in self.extension.iter_for_ser() {
            serializer.serialize_message_twice(7, msg)?;
        }
        for msg in self.options.iter_for_ser() {
            serializer.serialize_message_twice(8, msg)?;
        }
        for msg in self.source_code_info.iter_for_ser() {
            serializer.serialize_message_twice(9, msg)?;
        }
        for string in self.syntax.iter_for_ser() {
            serializer.serialize_bytes_twice(12, string.bytes().map(|b| Ok(b)))?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for FileDescriptorProto {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait FileDescriptorProtoTrait {
    fn name(&self) -> &str;
    fn package(&self) -> &str;
    fn for_each_dependency<F>(&self, f: F)
    where
        F: FnMut(&str);
    fn dependency_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&str>>;
    fn for_each_public_dependency<F>(&self, f: F)
    where
        F: FnMut(i32);
    fn public_dependency_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=i32>>;
    fn for_each_weak_dependency<F>(&self, f: F)
    where
        F: FnMut(i32);
    fn weak_dependency_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=i32>>;
    fn for_each_message_type<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::DescriptorProto);
    fn message_type_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::DescriptorProto>>;
    fn for_each_enum_type<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::EnumDescriptorProto);
    fn enum_type_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::EnumDescriptorProto>>;
    fn for_each_service<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::ServiceDescriptorProto);
    fn service_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::ServiceDescriptorProto>>;
    fn for_each_extension<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::FieldDescriptorProto);
    fn extension_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::FieldDescriptorProto>>;
    fn options(&self) -> ::std::option::Option<&super::super::google::protobuf::FileOptions>;
    fn source_code_info(&self) -> ::std::option::Option<&super::super::google::protobuf::SourceCodeInfo>;
    fn syntax(&self) -> &str;
}
impl FileDescriptorProtoTrait for FileDescriptorProto {
    fn name(&self) -> &str {
        &self.name
    }
    fn package(&self) -> &str {
        &self.package
    }
    fn for_each_dependency<F>(&self, f: F)
    where
        F: FnMut(&str) {
        for item in &self.dependency {
            (f)(item);
        }
    }
    fn dependency_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&str>> {
        ::std::boxed::Box::new(self.dependency.iter().cloned())
    }
    fn for_each_public_dependency<F>(&self, f: F)
    where
        F: FnMut(i32) {
        for item in &self.public_dependency {
            (f)(item);
        }
    }
    fn public_dependency_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=i32>> {
        ::std::boxed::Box::new(self.public_dependency.iter().cloned())
    }
    fn for_each_weak_dependency<F>(&self, f: F)
    where
        F: FnMut(i32) {
        for item in &self.weak_dependency {
            (f)(item);
        }
    }
    fn weak_dependency_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=i32>> {
        ::std::boxed::Box::new(self.weak_dependency.iter().cloned())
    }
    fn for_each_message_type<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::DescriptorProto) {
        for item in &self.message_type {
            (f)(item);
        }
    }
    fn message_type_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::DescriptorProto>> {
        ::std::boxed::Box::new(self.message_type.iter())
    }
    fn for_each_enum_type<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::EnumDescriptorProto) {
        for item in &self.enum_type {
            (f)(item);
        }
    }
    fn enum_type_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::EnumDescriptorProto>> {
        ::std::boxed::Box::new(self.enum_type.iter())
    }
    fn for_each_service<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::ServiceDescriptorProto) {
        for item in &self.service {
            (f)(item);
        }
    }
    fn service_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::ServiceDescriptorProto>> {
        ::std::boxed::Box::new(self.service.iter())
    }
    fn for_each_extension<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::FieldDescriptorProto) {
        for item in &self.extension {
            (f)(item);
        }
    }
    fn extension_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::FieldDescriptorProto>> {
        ::std::boxed::Box::new(self.extension.iter())
    }
    fn options(&self) -> ::std::option::Option<&super::super::google::protobuf::FileOptions> {
        self.options.as_ref()
    }
    fn source_code_info(&self) -> ::std::option::Option<&super::super::google::protobuf::SourceCodeInfo> {
        self.source_code_info.as_ref()
    }
    fn syntax(&self) -> &str {
        &self.syntax
    }
}
#[derive(Debug, Clone)]
pub struct FileDescriptorSet {
    pub file: ::std::vec::Vec<super::super::google::protobuf::FileDescriptorProto>,
}
impl ::std::default::Default for FileDescriptorSet {
    fn default() -> Self {
        use ::std::convert::TryInto;
        Self {
            file: ::std::default::Default::default(),
        }
    }
}
impl<'a> ::puroro::deserializer::stream::MessageDeserializeEventHandler for &'a mut FileDescriptorSet {
    type Target = ();
    fn finish(self) -> ::puroro::Result<Self::Target> {
        Ok(())
    }
    fn met_field<T: ::puroro::deserializer::stream::LengthDelimitedDeserializer>(
        &mut self,
        field: ::puroro::deserializer::stream::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {
        use ::puroro::helpers::MaybeRepeatedField;
        use ::puroro::helpers::MaybeRepeatedVariantField;
        match field {
            ::puroro::deserializer::stream::Field::Variant(variant) => match field_number {
                1 => Err(::puroro::PuroroError::UnexpectedWireType)?,
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::LengthDelimited(ldd) => match field_number {
                1 => {
                    let msg = self.file.push_and_get_mut();
                    ldd.deserialize_as_message(msg)?;
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits32(bytes) => match field_number {
                1 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
            ::puroro::deserializer::stream::Field::Bits64(bytes) => match field_number {
                1 => {
                    Err(::puroro::PuroroError::UnexpectedWireType)?
                }
                _ => Err(::puroro::PuroroError::UnexpectedFieldId)?,
            }
        }
        Ok(())
    }
}
impl ::puroro::Deserializable for FileDescriptorSet {
    fn from_bytes<I: Iterator<Item = ::std::io::Result<u8>>>(iter: I) -> ::puroro::Result<Self> {
        use ::puroro::deserializer::stream::Deserializer;
        let deserializer = ::puroro::deserializer::stream::deserializer_from_bytes(iter);
        let mut msg = <FileDescriptorSet as ::std::default::Default>::default();
        deserializer.deserialize(&mut msg)?;
        Ok(msg)
    }
}
impl ::puroro::serializer::Serializable for FileDescriptorSet {
    fn serialize<T: ::puroro::serializer::MessageSerializer>(
        &self, serializer: &mut T) -> ::puroro::Result<()>
    {
        use ::puroro::helpers::MaybeRepeatedField;
        for msg in self.file.iter_for_ser() {
            serializer.serialize_message_twice(1, msg)?;
        }
        Ok(())
    }
}
impl ::puroro::Serializable for FileDescriptorSet {
    fn serialize<W: std::io::Write>(&self, write: &mut W) -> ::puroro::Result<()> {
        let mut serializer = ::puroro::serializer::default_serializer(write);
        <Self as ::puroro::serializer::Serializable>::serialize(self, &mut serializer)
    }
}
pub trait FileDescriptorSetTrait {
    fn for_each_file<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::FileDescriptorProto);
    fn file_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::FileDescriptorProto>>;
}
impl FileDescriptorSetTrait for FileDescriptorSet {
    fn for_each_file<F>(&self, f: F)
    where
        F: FnMut(&super::super::google::protobuf::FileDescriptorProto) {
        for item in &self.file {
            (f)(item);
        }
    }
    fn file_boxed_iter(&self)
        -> ::std::boxed::Box<dyn '_ + Iterator<Item=&super::super::google::protobuf::FileDescriptorProto>> {
        ::std::boxed::Box::new(self.file.iter())
    }
}

pub mod compiler;
