#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    Int32,
    Boolean,
    String,
    Function {
        params: Vec<Type>,
        return_type: Box<Type>,
    },
    TypeVariable {
        name: String,
        instance: Option<Box<Type>>,
    },
}

pub struct Binding {
    pub name: String,
    pub r#type: Type,
}
