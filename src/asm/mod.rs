//! ## Memory Layout
//!
//! ```ignore
//!    +-------+-----+-------------------+---------------+----------+
//!    |       | ... | Caller's FP (i32) | Constant Pool | Heap ... |
//!    o-------o-----o-------------------o---------------o----------+
//!    |       |     |                   |               |          
//! index 0   SP    FP              Stack Offset     Heap Offset
//! ```
//!
//! ### Global Context Registers
//!
//! Global variables that are shared by multiple execution contexts.
//!
//! - **Stack Pointer (SP)** - Stack pointer. End of stack.
//! - **Stack Offset** - Start index of the virtual stack segment. The virtual stack extends in
//!   the negative direction. If the access is out of range, it will be trapped in the host environment.
//! - **Heap Offset** - Start index of the heap segment. The heap extends in the positive direction.
//!   If the access is out of range, it will be trapped in the host environment.
//!
//! ### Execution Context Registers
//!
//! Run-time context allocated in global variables. We should be able to switch between multiple
//! execution contexts by saving them somewhere.
//!
//! - **Frame Pointer (FP)** - The frame pointer of the current function.
//!
//! ### Virtual Stack Segment
//!
//! Unlike WebAssembly's value stack, it is placed in a contiguous memory area and a frame is
//! allocated for each function call.
//!
//! - When the closure is introduced, we will secure not only the FP of the caller,
//!   but also the FP of the function where a closure is defined.
//! - Can it be laid out well so that variables that are not referenced by the closure can be discarded?
//!
//! ### Constant Pool
//!
//! This is the area of the object whose size is determined at compile time and survives throughout
//! the execution of the program, starting at Stack Offset and extending in the positive direction to Heap Offset.
//!
//! ### Heap
//!
//! A memory area for dynamically allocated objects. How to manage the memory is still under consideration.

pub mod allocator;
pub mod emitter;
pub mod wasm;
use crate::sem::Type;
pub use allocator::Allocator;
pub use emitter::AsmBuilder;
use std::cell::RefCell;
use std::rc::Rc;

/// Memory alignment
const ALIGNMENT: wasm::Size = wasm::SIZE_BYTES;

#[inline]
pub fn align(n: wasm::Size) -> wasm::Size {
    let m = n / ALIGNMENT;
    let a = ALIGNMENT * m;

    if a < n {
        ALIGNMENT * (m + 1)
    } else {
        a
    }
}

/// The struct *LocalStorage* represents name and type for
// local variables and function parameters.
#[derive(Debug, PartialEq)]
pub struct LocalStorage {
    name: String,
    r#type: Rc<RefCell<Type>>,
}

/// String literal allocation in constant pool that is allocated at compile time.
///
/// ```ignore
///     +----------------------------+----------------------------+---------------------+
///     |                        Reference                        |       Object        |
///     +----------------------------+----------------------------+---------------------+
///     |  index (u32 little endian) | length (u32 little endian) | UTF-8 byte sequence |
///     +----------------------------+----------------------------+---------------------+
/// ```
/// - `index` is absolute index in the memory. It points to the beginning of UTF-8 bytes.
/// - `length` is the number of UTF-8 bytes only.
///
#[derive(Debug, PartialEq)]
pub struct ConstantString {
    content: String,
    // the largest amount of memory possible with 32-bit pointers,
    // which is what WebAssembly currently supports
    offset: wasm::Size,
}

#[allow(clippy::len_without_is_empty)]
impl ConstantString {
    pub fn from_str(content: &str, offset: wasm::Size) -> Self {
        Self {
            content: content.to_string(),
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

    /// Returns the number of bytes of reference and UTF-8 bytes
    /// including memory alignment.
    pub fn memory_size(&self) -> wasm::Size {
        align(
            wasm::SIZE_BYTES +                           // offset
            wasm::SIZE_BYTES +                           // length
            self.content.as_bytes().len() as wasm::Size, // UTF-8 bytes
        )
        //(self.content.len() + self.header.len()) as u32
    }

    pub fn bytes(&self, base: wasm::Size) -> Vec<u8> {
        let bytes = self.content.as_bytes();
        let offset = (base + self.offset + wasm::SIZE_BYTES + wasm::SIZE_BYTES).to_le_bytes();
        let length = (bytes.len() as wasm::Size).to_le_bytes();

        offset
            .iter()
            .chain(length.iter())
            .chain(bytes.iter())
            .copied()
            .collect::<Vec<_>>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_string() {
        let s = ConstantString::from_str("", 0);
        assert_eq!(s.offset(), 0);
        assert_eq!(s.memory_size(), 8);
        assert_eq!(s.bytes(0), [0x8, 0, 0, 0, 0, 0, 0, 0]);
    }
    #[test]
    fn some_string() {
        let s = ConstantString::from_str("123", 0);
        assert_eq!(s.offset(), 0);
        assert_eq!(s.memory_size(), 12);
        assert_eq!(
            s.bytes(1),
            [0x9, 0, 0, 0, 0x3, 0, 0, 0, '1' as u8, '2' as u8, '3' as u8]
        );
    }
}
