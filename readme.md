# puroro, protocol buffer implementation for rust

## TODOs
- proto2
    - Groups, at least correctly ignore it (where's document!?)
    - default
    - extensions
- proto2 & 3
    - Maps
    - OneOfs
    - Anys, and other well-known types
    - Unit tests
    - Document!!
    - Mutable interface
    - Keep unknown fields
    - Deserializer from a slice
    - Required field checker
    - Other implementations
        - SliceRef -- A viewer over a `&[u8]` slice
        - Append -- A thin wrapper over other impls, just overriding few fields using `with_myfield()` method
    - Naming of the other implementations. Consider using a type generator class
    - Support the `allocator_api`. Waiting for the `String` support
    - RPCs / services

## subcrates

- puroro -- The crate that the library user need to import
- puroro-internal -- The crate that the generated code need to import
- puroro-plugin -- A protoc compiler plugin

## Sample command
Keep in mind that protoc command not work properly with Windows path separator "\\". Use "/" instead.
```
$ protoc <protofile-path> --plugin=protoc-gen-rust=./target/debug/puroro-plugin.exe --rust_out=<output-dir> --proto_path=<protofile-dir>
```