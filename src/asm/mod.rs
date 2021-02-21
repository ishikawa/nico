pub mod allocator;
pub mod emitter;
pub mod wasm;
use crate::sem::Type;
pub use allocator::Allocator;
pub use emitter::AsmBuilder;
use std::cell::RefCell;
use std::rc::Rc;

/// The enum *Storage* represents names in WASM module.
/// For example, function parameters, local variables and global variables.
#[derive(Debug, PartialEq)]
pub enum Storage {
    Parameter {
        name: String,
        r#type: Rc<RefCell<Type>>,
    },
    LocalVariable {
        name: String,
        r#type: Rc<RefCell<Type>>,
    },
}

/// String literal's portion of the module's memory that is allocated at compile time.
///
/// ```ignore
///     +----------------------------+---------------------+
///     | length (u32 little endian) | UTF-8 byte sequence |
///     +----------------------------+---------------------+
/// ```
///
#[derive(Debug, PartialEq)]
pub struct ConstantString {
    content: String,
    // the largest amount of memory possible with 32-bit pointers,
    // which is what WebAssembly currently supports
    offset: u32,
    header: [u8; 4],
}

#[allow(clippy::len_without_is_empty)]
impl ConstantString {
    pub fn from_str(content: &str, offset: u32) -> Self {
        let bytes = content.as_bytes();

        // Write length at head
        if bytes.len() > u32::MAX as usize {
            panic!("string literal is too long. max = {}", u32::MAX);
        }
        let header = (bytes.len() as i32).to_le_bytes();

        Self {
            content: content.to_string(),
            header,
            offset,
        }
    }

    /// Returns memory offset.
    ///
    /// ## Examples
    ///
    /// ```
    /// # use nico::asm::ConstantString;
    /// let s = ConstantString::from_str("", 0);
    /// assert_eq!(s.offset(), 0)
    /// ```
    pub fn offset(&self) -> u32 {
        self.offset
    }

    pub fn len(&self) -> u32 {
        self.offset + (self.content.len() + self.header.len()) as u32
    }

    pub fn bytes(&self) -> std::iter::Chain<std::slice::Iter<u8>, std::slice::Iter<u8>> {
        self.header.iter().chain(self.content.as_bytes().iter())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_string() {
        let s = ConstantString::from_str("", 0);
        assert_eq!(s.offset(), 0);

        let bytes = s.bytes().copied().collect::<Vec<_>>();
        assert_eq!(bytes, [0, 0, 0, 0]);
    }
    #[test]
    fn some_string() {
        let s = ConstantString::from_str("123", 0);
        assert_eq!(s.offset(), 0);

        let bytes = s.bytes().copied().collect::<Vec<_>>();
        assert_eq!(bytes, [0x3, 0, 0, 0, '1' as u8, '2' as u8, '3' as u8]);
    }
}
