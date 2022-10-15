# puroro, a protocol buffer implementation for Rust

A yet another protocol buffer compiler implementation for Rust language.
This project is licensed under Apache 2.0 license.

This is not an officially supported Google product.

See [puroro/src/lib.rs](https://docs.rs/puroro/) for more documents.

## important notes

This library is under development and it is very possible to make breaking changes.

Currently this library only supports Rust nightly channel.

# How to compile your .pb files to .rs files

First, let's create a crate for your .proto files (and the generated .rs files).
Actually it is not required to create a separated crate for the proto files,
though I recommend to make it to avoid any unexpected problems.

```shell
$ cargo new my-examples --lib
$ cd my-examples

# Create your .proto files under this directory
$ mkdir protos

# Edit your .proto files
$ emacs-vim-nano-or-whatever ./protos/yourproto.proto
```

As an example, let's make a simple proto file `test1.proto`:

```protobuf
syntax = "proto3";
package library;
message Book {
    string title = 1;
    uint32 num_pages = 2;
}
```

Note that the file names does not make any effect in the generated codes.
Only the package name (in this case, `package library;`) makes the effect
to the generated code's module name (or file name).

Then edit the `Cargo.toml` to add the dependency to `puroro` library crates:

```toml
[dependencies]
puroro = "*"

[build-dependencies]
puroro-plugin = "*"
```

As a last step, create a file `build.rs` under the crate root directory.
Check [our sample build.rs](./tests-pb/build.rs) and just copy and paste.

Once you have finished these steps, the directory should be like this:

    + my-examples/
        ├ src/
        │   └ (empty)
        ├ protos/
        │   └ test1.proto
        ├ cargo.toml
        ├ build.rs
        ├ (some other generated files)

Then run `cargo build` command. If it successfully runs, then the generated
`.rs` files will be generated under `src/` directory and you can use it from
your own crate. Congraturations!

# subcrates
- puroro -- The crate that the library user need to import
- puroro-plugin -- A protoc compiler plugin
- tests -- Test cases
- tests-pb -- Compiling .pb files used by tests crate
- protobuf -- A git submodule of Google's official protobuf repository
- puroro-protobuf-compiled -- Compiled .rs files in protobuf crate so that puroro-plugin crate can use it
    - update-plugin-protos.bat -- A batch file to generate the compiled .rs files

# TODOs
- proto2
    - [ ] Groups, at least correctly ignore it
    - [x] Enums (In proto2 we need to refuse the unknown value)
    - [ ] default value (something like `optional int32 foo = 1; [default=10]`)
    - [ ] extensions
- proto2 & 3
    - [ ] Maps
    - [x] OneOfs
        - [x] Type definitions
        - [x] serialize / deserialize
    - [ ] Anys, and other well-known types
    - [ ] Enum allow-alias option
    - [ ] More more more unit tests
    - [ ] More more more more documents
    - [ ] Print comments in the generated files
    - [ ] Reflections
        - [ ] Get message metadata (descriptors)
    - [ ] Nightly / stable features
        - [ ] Support stable (not using nightly features)
    - [ ] Message traits
        - [ ] Mutable interface trait
        - [ ] (More) Repeated field interface trait
        - [ ] Map interface trait
    - [ ] Keep unknown fields
    - [ ] Deserializer from a slice
    - [ ] Serializer performance improvement
    - [ ] Custom deserializer (?)
    - [ ] Required field checker
    - [ ] Other implementations
        - [ ] Bumpalo -- Use Bumpalo for `Vec` and `String` allocation
        - [ ] SliceView -- A viewer over a `&[u8]` slice, without allocating any extra memories
        - [ ] Empty(Unit) -- `()`, which only returns default values
        - [ ] Merged -- `(T, U)`
        - [ ] Either -- `::either::Either<T, U>`
        - [ ] Option -- `Option<T>`
    - [ ] Support the `allocator_api`. Waiting for the `String` support
    - [ ] RPCs / services
    - [ ] Deserializer vulnerbility: Need to limit the recursion depth
    - [ ] Get multiple fields mutable references at once
