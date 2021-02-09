use parser::Definition;

use super::parser;

pub enum Type {
    Int32,
    String,
}

pub struct Binding {
    name: String,
    r#type: Type,
}

pub struct Scope {
    bindings: Vec<Binding>,
}

pub struct Function {
    name: String,           // The name of a function in .nico file
    reference_name: String, // The name of a function in .wat file (flat namespace)
    params: Vec<Binding>,
}
