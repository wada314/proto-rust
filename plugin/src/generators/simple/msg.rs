use super::*;

// Too long! lol
const DESER_MOD: &'static str = "::puroro_serializer::deserializer::stream";

pub(crate) fn handle_msg<'p, W: Write>(
    output: &mut Indentor<W>,
    context: &Context<'p>,
    msg: &'p DescriptorProto,
) -> Result<()> {
    write_body(output, context, msg)?;
    write_default(output, context, msg)?;
    write_deser_stream_handler(output, context, msg)?;
    Ok(())
}

// struct body
fn write_body<'p, W: Write>(
    output: &mut Indentor<W>,
    context: &Context<'p>,
    msg: &'p DescriptorProto,
) -> Result<()> {
    let native_type_name = to_type_name(&msg.name);
    (
        format!("pub struct {name} {{\n", name = native_type_name),
        indent((iter(msg.field.iter().map(|field| {
            let field_native_type = gen_field_type(field, context)?;
            Ok(format!(
                "{name}: {type_},\n",
                name = to_var_name(&field.name),
                type_ = field_native_type
            ))
        })),)),
        "}}\n",
    )
        .write_into(output)
}

// impl Default
// Because enum is Result<enum, i32>, we need a special treatment for it.
fn write_default<'p, W: Write>(
    output: &mut Indentor<W>,
    context: &Context<'p>,
    msg: &'p DescriptorProto,
) -> Result<()> {
    let native_type_name = to_type_name(&msg.name);
    (
        format!(
            "\
impl ::std::default::Default for {name} {{
    fn default() -> Self {{
        Self {{\n",
            name = native_type_name
        ),
        indent_n(
            3,
            (iter(msg.field.iter().map(|field| {
                let native_field_name = to_var_name(&field.name);
                let is_repeated = is_field_repeated(field);
                let is_enum = is_field_enum(field, context);

                match (is_repeated, is_enum) {
                    (false, true) => Ok(format!(
                        "{name}: 0i32.try_into(),\n",
                        name = native_field_name
                    )),
                    (_, _) => Ok(format!(
                        "{name}: ::std::default::Default::default(),\n",
                        name = native_field_name
                    )),
                }
            })),),
        ),
        "        \
        }}
    }}
}}\n",
    )
        .write_into(output)
}

fn write_deser_stream_handler<'p, W: Write>(
    output: &mut Indentor<W>,
    context: &Context<'p>,
    msg: &'p DescriptorProto,
) -> Result<()> {
    let native_type_name = to_type_name(&msg.name);
    (
        format!(
            "\
impl {d}::MessageDeserializeEventHandler for {name} {{
    type Target = Self;
    fn finish(self) -> ::puroro::Result<Self::Target> {{
        Ok(self)
    }}
    fn met_field<T: {d}::LengthDelimitedDeserializer>(
        &mut self,
        field: {d}::Field<T>,
        field_number: usize,
    ) -> ::puroro::Result<()> {{
        match field {{\n",
            d = DESER_MOD,
            name = native_type_name
        ),
        indent_n(
            3,
            (
                func(|output| write_deser_stream_handler_variant_arm(output, context, msg)),
                func(|output| write_deser_stream_handler_ld_arm(output, context, msg)),
                func(|output| write_deser_stream_handler_bitsxx_arm(32, output, context, msg)),
                func(|output| write_deser_stream_handler_bitsxx_arm(64, output, context, msg)),
                "_ => Err(::puroro::PuroroError::UnexpectedFieldType)?,\n",
            ),
        ),
        "        \
        }}
        Ok(())
    }}
}}\n",
    )
        .write_into(output)
}

fn write_deser_stream_handler_variant_arm<'p, W: Write>(
    output: &mut Indentor<W>,
    context: &Context<'p>,
    msg: &'p DescriptorProto,
) -> Result<()> {
    (
        format!(
            "{d}::Field::Variant(variant) => match field_number {{\n",
            d = DESER_MOD
        ),
        indent((
            iter(msg.field.iter().map(|field| {
                Ok(match variant_field_type_tag(field) {
                    None => {
                        // This is not a variant field, so the output's match-case should fail.
                        format!(
                            "{number} => Err(::puroro::PuroroError::UnexpectedWireType)?,\n",
                            number = field.number
                        )
                    }
                    Some(tag_type) => {
                        let is_enum = is_field_enum(field, context);
                        let is_repeated = is_field_repeated(field);
                        let maybe_try_into = if is_enum { ".try_into()" } else { "" };
                        if is_repeated {
                            format!(
                                "\
{number} => {{
    self.{name}.push(variant.to_native::<{tag}>()?{maybe_try_into});
}}\n",
                                number = field.number,
                                name = to_var_name(&field.name),
                                tag = tag_type,
                                maybe_try_into = maybe_try_into,
                            )
                        } else {
                            format!(
                                "\
{number} => {{
    self.{name} = variant.to_native::<{tag}>()?{maybe_try_into};
}}\n",
                                number = field.number,
                                name = to_var_name(&field.name),
                                tag = tag_type,
                                maybe_try_into = maybe_try_into,
                            )
                        }
                    }
                })
            })),
            "_ => todo!(\"Unknown field number\"),\n",
        )),
        "}}\n",
    )
        .write_into(output)
}

fn write_deser_stream_handler_ld_arm<'p, W: Write>(
    output: &mut Indentor<W>,
    context: &Context<'p>,
    msg: &'p DescriptorProto,
) -> Result<()> {
    (
        format!(
            "{d}::Field::LengthDelimited(ldd) => match field_number {{\n",
            d = DESER_MOD
        ),
        indent((
            iter(msg.field.iter().map(|field| {
                let native_field_name = to_var_name(&field.name);
                let is_repeated = is_field_repeated(field);
                Ok(
                    if let Some(TypeOfIdent::Message) = context.type_of_ident(&field.type_name) {
                        // Message
                        let field_native_type = gen_field_type(field, context)?;
                        if is_repeated {
                            format!(
                                "\
{number} => {{
    self.{name}.push(ldd.deserialize_as_message(
        <{native_type} as ::std::default::Default>::default())?
    );
}}\n",
                                number = field.number,
                                name = native_field_name,
                                native_type = field_native_type,
                            )
                        } else {
                            format!(
                                "\
{number} => {{
    let msg = self.{name}.get_or_insert_with(<{native_type} as ::std::default::Default>::default);
    self.{name} = Some(ldd.deserialize_as_message(msg)?);
}}\n",
                                number = field.number,
                                name = native_field_name,
                                native_type = field_native_type,
                            )
                        }
                    } else if let Some(tag_type) = variant_field_type_tag(field) {
                        // packed variant
                        if is_repeated {
                            format!(
                                "\
{number} => {{
    self.{name}.append(&mut ldd.deserialize_as_variants().map(|rv| {{
        rv.and_then(|variant| variant.to_native::<{tag}>())
    }}).collect::<::puroro::Result<::std::vec::Vec<_>>>()?);
}}\n",
                                number = field.number,
                                name = native_field_name,
                                tag = tag_type,
                            )
                        } else {
                            // a packed variant is coming for singular field...??
                            // It's soooo weird but I'm not sure if that is illegal...
                            format!(
                                "\
{number} => {{
    self.{name} = ldd.deserialize_as_variants()
        .last()
        .unwrap_or(::puroro::PuroroError::ZeroLengthPackedField)
        .and_then(|variant| variant.to_native::<{tag}>())?;
}}\n",
                                number = field.number,
                                name = native_field_name,
                                tag = tag_type,
                            )
                        }
                    } else {
                        match field.type_ {
                            Ok(FieldDescriptorProto_Type::TYPE_STRING) => {
                                // string
                                if is_repeated {
                                    format!(
                                        "\
{number} => {{
    self.{name}.push(ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?);
}}\n",
                                        number = field.number,
                                        name = native_field_name,
                                    )
                                } else {
                                    format!(
                                        "\
{number} => {{
    self.{name} = ldd.deserialize_as_chars().collect::<::puroro::Result<_>>()?;
}}\n",
                                        number = field.number,
                                        name = native_field_name,
                                    )
                                }
                            }
                            Ok(FieldDescriptorProto_Type::TYPE_BYTES) => {
                                // bytes
                                if is_repeated {
                                    format!(
                                        "\
{number} => {{
    self.{name}.push(ldd.deserialize_as_bytes().collect::<::puroro::Result<_>>()?);
}}\n",
                                        number = field.number,
                                        name = native_field_name,
                                    )
                                } else {
                                    format!(
                                        "\
{number} => {{
    self.{name} = ldd.deserialize_as_bytes().collect::<::puroro::Result<_>>()?;
}}\n",
                                        number = field.number,
                                        name = native_field_name,
                                    )
                                }
                            }
                            _ => {
                                // else
                                format!(
                                "{number} => Err(::puroro::PuroroError::UnexpectedWireType)?,\n",
                                number = field.number
                            )
                            }
                        }
                    },
                )
            })),
            "_ => todo!(\"Unknown filed number\"),\n",
        )),
        "}}\n",
    )
        .write_into(output)
}

fn write_deser_stream_handler_bitsxx_arm<'p, W: Write>(
    bits: usize,
    output: &mut Indentor<W>,
    context: &Context<'p>,
    msg: &'p DescriptorProto,
) -> Result<()> {
    (
        format!(
            "{d}::Field::Bits{bits}(bytes) => match field_number {{\n",
            bits = bits,
            d = DESER_MOD
        ),
        indent((
            iter(msg.field.iter().map(|field| {
                let opt_native_type = if bits == 32 {
                    bits32_field_native_type(field)
                } else {
                    bits64_field_native_type(field)
                };
                Ok(if let Some(native_type) = opt_native_type {
                    let native_field_name = to_var_name(&field.name);
                    if is_field_repeated(field) {
                        format!(
                            "\
{number} => {{
    self.{name}.push({type_}::from_le_bytes(bytes));
}}\n",
                            number = field.number,
                            name = native_field_name,
                            type_ = native_type
                        )
                    } else {
                        format!(
                            "\
{number} => {{
    self.{name} = {type_}::from_le_bytes(bytes);
}}\n",
                            number = field.number,
                            name = native_field_name,
                            type_ = native_type
                        )
                    }
                } else {
                    format!(
                        "{number} => Err(::puroro::PuroroError::UnexpectedWireType)?,\n",
                        number = field.number
                    )
                })
            })),
            "_ => todo!(\"Unknown filed number\"),\n",
        )),
        "}}\n",
    )
        .write_into(output)
}

fn variant_field_type_tag(field: &FieldDescriptorProto) -> Option<&'static str> {
    if let Ok(t) = field.type_ {
        match t {
            FieldDescriptorProto_Type::TYPE_INT64 => Some("::puroro::tags::Int64"),
            FieldDescriptorProto_Type::TYPE_SINT64 => Some("::puroro::tags::SInt64"),
            FieldDescriptorProto_Type::TYPE_UINT64 => Some("::puroro::tags::UInt64"),
            FieldDescriptorProto_Type::TYPE_INT32 => Some("::puroro::tags::Int32"),
            FieldDescriptorProto_Type::TYPE_SINT32 => Some("::puroro::tags::SInt32"),
            FieldDescriptorProto_Type::TYPE_ENUM => Some("::puroro::tags::Int32"),
            FieldDescriptorProto_Type::TYPE_BOOL => Some("::puroro::tags::Bool"),
            FieldDescriptorProto_Type::TYPE_UINT32 => Some("::puroro::tags::UInt32"),
            _ => None,
        }
    } else {
        None
    }
}

fn bits32_field_native_type(field: &FieldDescriptorProto) -> Option<&'static str> {
    if let Ok(t) = field.type_ {
        match t {
            FieldDescriptorProto_Type::TYPE_FLOAT => Some("f32"),
            FieldDescriptorProto_Type::TYPE_FIXED32 => Some("u32"),
            FieldDescriptorProto_Type::TYPE_SFIXED32 => Some("i32"),
            _ => None,
        }
    } else {
        None
    }
}

fn bits64_field_native_type(field: &FieldDescriptorProto) -> Option<&'static str> {
    if let Ok(t) = field.type_ {
        match t {
            FieldDescriptorProto_Type::TYPE_DOUBLE => Some("f64"),
            FieldDescriptorProto_Type::TYPE_FIXED64 => Some("u64"),
            FieldDescriptorProto_Type::TYPE_SFIXED64 => Some("i64"),
            _ => None,
        }
    } else {
        None
    }
}
