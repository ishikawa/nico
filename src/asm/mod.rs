//! ## Memory Layout
//!
//! ```ignore
//!    +-------+-------------+------------+--------------+---------------+----------+
//!    |  ...  | Dynamic (1) | Static (2) | FP (3) (i32) | Constant Pool | Heap ... |
//!    o-------o-------------o------------+--------------o---------------o----------+
//!    |       |             |                           |               |          
//! index 0   SP            FP                      Stack Base       Heap Base
//! ```
//! Since WebAssemby's Memory Instruction cannot take negative values for offsets, the address
//! calculation should be designed so that it can be calculated by adding positive values.
//!
//! - (1) Dynamically allocated memory on the stack.
//! - (2) Statically allocated memory on the stack. The size of this area is known at compile time.
//! - (3) Caller's FP = Load(FP + sizeof(Static))
//!       Caller's SP = FP + sizeof(Static) + sizeof(FP)
//!
//! ### Global Context Registers
//!
//! Global variables that are shared by multiple execution contexts.
//!
//! - **Stack Pointer (SP)** - Stack pointer. End of stack.
//! - **Stack Base** - Start index of the virtual stack segment. The virtual stack extends in
//!   the negative direction. If the access is out of range, it will be trapped in the host environment.
//! - **Heap Base** - Start index of the heap segment. The heap extends in the positive direction.
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
//! the execution of the program, starting at Stack Base and extending in the positive direction to Heap Base.
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
fn align(n: wasm::Size) -> wasm::Size {
    let m = n / ALIGNMENT;
    let a = ALIGNMENT * m;

    if a < n {
        ALIGNMENT * (m + 1)
    } else {
        a
    }
}

fn wasm_type(ty: &Rc<RefCell<Type>>) -> Option<wasm::Type> {
    let wty = match *ty.borrow() {
        Type::Int32 => Some(wasm::Type::I32),
        Type::Boolean => Some(wasm::Type::I32),
        Type::String => Some(wasm::Type::I32),
        Type::Void => None,
        Type::Array(_) => Some(wasm::Type::I32),
        Type::TypeVariable { .. } => {
            panic!(
                "Type variable `{}` can't be resolved to WASM type.",
                ty.borrow()
            )
        }
        Type::Function { .. } => panic!(
            "Function type `{}` can't be resolved to WASM type.",
            ty.borrow()
        ),
    };
    wty
}

#[derive(Debug, Default)]
pub struct StackFrame {
    sizes: Vec<wasm::Size>,
}

impl StackFrame {
    /// Reserve memory in "Static" on the stack.
    pub fn reserve(&mut self, size: wasm::Size) {
        self.sizes.push(size);
    }

    /// Returns the total size of "Static" on  the stack.
    pub fn static_size(&self) -> wasm::Size {
        align(self.sizes.iter().sum())
    }
}

/// The struct *LocalStorage* represents name and type for local variables and
/// function parameters.
/// This struct can be cloned because the name of storage will be unchagend
/// after fixed.
#[derive(Debug, PartialEq, Clone)]
pub struct LocalStorage {
    name: String,
    r#type: Rc<RefCell<Type>>,
}

impl LocalStorage {
    pub fn shared<S: AsRef<str>>(name: S, r#type: &Rc<RefCell<Type>>) -> Rc<Self> {
        Rc::new(Self {
            name: name.as_ref().to_string(),
            r#type: Rc::clone(&r#type),
        })
    }
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
/// - `index` is **absolute index in the memory**. It points to the beginning of UTF-8 bytes.
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
