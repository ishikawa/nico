//! ## Memory Layout
//!
//! ```ignore
//!    +-------+-------------+------------+--------------+---------------+----------+
//!    |  ...  | Dynamic (1) | Static (2) | FP (3) (i32) | Constant Pool | Heap ... |
//!    o-------o-------------o------------+--------------o---------------o----------+
//!    |       |             |                           |               |          
//! index 0   SP            FP                      Stack Base       Heap Base
//! ```
//! Since WebAssembly's Memory Instruction cannot take negative values for offsets, the address
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
use crate::util::naming::PrefixNaming;
pub use allocator::Allocator;
pub use emitter::AsmBuilder;
use std::cell::RefCell;
use std::convert::TryFrom;
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
        Type::Struct { .. } => Some(wasm::Type::I32),
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
/// This struct can be cloned because the name of storage will be unchanged.
#[derive(Debug, PartialEq)]
pub enum Storage {
    LocalVariable(LocalVariable),
    Function(Function),
}

#[derive(Debug, PartialEq, Clone)]
pub struct LocalVariable {
    name: String,
    r#type: wasm::Type,
}

#[derive(Debug, PartialEq)]
pub struct Function {
    name: String,
    function_type: Rc<RefCell<Type>>,
}

impl Storage {
    pub fn function<S: Into<String>>(name: S, r#type: &Rc<RefCell<Type>>) -> Self {
        if let Type::Function { .. } = *r#type.borrow() {
            Self::Function(Function {
                name: name.into(),
                function_type: Rc::clone(r#type),
            })
        } else {
            panic!("Can't create Storage::Function with {}", r#type.borrow());
        }
    }

    pub fn local_variable<S: Into<String>>(name: S, r#type: &Rc<RefCell<Type>>) -> Self {
        Self::LocalVariable(LocalVariable {
            name: name.into(),
            r#type: wasm_type(r#type).unwrap(),
        })
    }

    pub fn unwrap_function(&self) -> &Function {
        match self {
            Storage::Function(fun) => fun,
            _ => panic!("storage must be a function"),
        }
    }

    pub fn unwrap_local_variable(&self) -> &LocalVariable {
        match self {
            Storage::LocalVariable(var) => var,
            _ => panic!("storage must be a local variable"),
        }
    }
}

/// This structure allocates required local/temporary variables within a WASM function frame.
/// It manages the scope and allocates the minimum number of local variables required in
/// a function frame.
#[derive(Debug)]
pub struct LocalVariables {
    i32_naming: PrefixNaming,

    // Free - temporary variables not used in active scopes, but reserved for a function.
    free: Vec<Rc<Storage>>,

    // Used - used temporary variables stack. The top of stack is the current scope. They will be
    //        reclaimed when a scope terminated, and moved to free list.
    used: Vec<Vec<Rc<Storage>>>,
}

impl LocalVariables {
    // To avoid collision with other variables, specify special prefix (e.g. ".")
    //     $.i32.0, $.i32.1, ...
    pub fn new(prefix: &str) -> Self {
        Self {
            i32_naming: PrefixNaming::new(&format!("{}i32.", prefix)),
            free: vec![],
            used: vec![],
        }
    }

    pub fn variables(&self) -> &Vec<Rc<Storage>> {
        &self.free
    }

    pub fn push_scope(&mut self) {
        self.used.push(vec![]);
    }

    pub fn pop_scope(&mut self) {
        if let Some(used) = self.used.pop() {
            for var in used {
                self.free.push(var);
            }
        }
    }

    pub fn reserve(&mut self, ty: &Rc<RefCell<Type>>) -> Rc<Storage> {
        let wasm_type = wasm_type(ty);

        if let Some(wasm::Type::I32) = wasm_type {
            self.reserve_i32()
        } else {
            panic!("unsupported type {}", ty.borrow());
        }
    }

    pub fn reserve_i32(&mut self) -> Rc<Storage> {
        let used_scope = self.used.last_mut().expect("empty scope stack");
        let index = self
            .free
            .iter()
            .map(|x| x.unwrap_local_variable())
            .position(|x| x.r#type == wasm::Type::I32);

        let var = if let Some(index) = index {
            self.free.swap_remove(index)
        } else {
            let name = self.i32_naming.next();
            Rc::new(Storage::LocalVariable(LocalVariable {
                name,
                r#type: wasm::Type::I32,
            }))
        };

        used_scope.push(Rc::clone(&var));
        var
    }

    pub fn reserve_name_i32(&mut self) -> String {
        let var = self.reserve_i32();
        var.unwrap_local_variable().name.clone()
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
        let len = self.content.as_bytes().len();
        align(
            wasm::SIZE_BYTES +                  // offset
            wasm::SIZE_BYTES +                  // length
            wasm::Size::try_from(len).unwrap(), // UTF-8 bytes
        )
    }

    pub fn bytes(&self, base: wasm::Size) -> Vec<u8> {
        let bytes = self.content.as_bytes();
        let offset = (base + self.offset + wasm::SIZE_BYTES + wasm::SIZE_BYTES).to_le_bytes();
        let length = (wasm::Size::try_from(bytes.len()).unwrap()).to_le_bytes();

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
    use std::collections::HashSet;

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

    #[test]
    fn local_variables_empty() {
        let mut locals = LocalVariables::new(".");

        locals.push_scope();
        locals.pop_scope();

        assert!(locals.variables().is_empty());
    }

    #[test]
    fn local_variables() {
        let mut locals = LocalVariables::new(".");

        {
            locals.push_scope();

            let var1 = locals.reserve_i32();
            let var2 = locals.reserve_i32();

            assert_ne!(
                var1.unwrap_local_variable().name,
                var2.unwrap_local_variable().name
            );

            locals.pop_scope();
        }

        {
            locals.push_scope();

            let var3 = locals.reserve_i32();
            let var4 = locals.reserve_i32();

            assert_ne!(
                var3.unwrap_local_variable().name,
                var4.unwrap_local_variable().name
            );

            {
                locals.push_scope();
                locals.reserve_i32();
                locals.pop_scope();
            }

            locals.pop_scope();
        }

        let vars = locals.variables();
        let mut names = HashSet::new();

        for var in vars {
            let name = var.unwrap_local_variable().name.clone();

            assert!(!names.contains(&name));

            names.insert(name);
        }

        assert_eq!(vars.len(), 3);
    }
}
