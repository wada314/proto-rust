// A generated source code by puroro library
// package library

pub mod _puroro_root {
    pub use super::super::_puroro_root::*;
}

pub mod _puroro {
    pub use ::puroro::*;
}

pub struct Book<T>(T);

impl<T: self::_puroro::GenericMessage> Book<T> {
    pub fn title(&self) -> () {
        todo!()
    }

    pub fn num_pages(&self) -> () {
        todo!()
    }
}

pub struct BookOwned {
    _bitfield: self::_puroro::bitvec::array::BitArray<[u32; 4], self::_puroro::bitvec::order::Lsb0>,
}

pub mod book {

    mod _puroro {
        pub use super::super::_puroro::*;
    }
    mod _puroro_root {
        pub use super::super::_puroro_root::*;
    }

    pub mod _field_descriptors {
        mod _puroro {
            pub use super::super::_puroro::*;
        }
        mod _puroro_root {
            pub use super::super::_puroro_root::*;
        }
        pub struct Title;
        impl self::_puroro::FieldDescriptorType for Title {}
        pub struct NumPages;
        impl self::_puroro::FieldDescriptorType for NumPages {}
    }
    pub use _field_descriptors::*;
}
