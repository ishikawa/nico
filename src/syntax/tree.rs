use crate::sem;
use crate::tokenizer::Token;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug)]
pub struct Source {
    pub tokens: Vec<Rc<Token>>,
}

pub struct ModuleNode {
    pub nodes: Vec<TopLevel>,
}

#[derive(Debug)]
pub enum TopLevel {
    Struct(StructNode),
    Function(FunctionNode),
    Statement(StatementNode),
}

/// Types
/// -----
/// ```ignore
/// definition  := struct
/// struct      := "struct" name "{" fields "}"
/// fields      := field | fields ","
/// field       := name ":" type
/// type        := name
/// name        := IDENT
/// ```
#[derive(Debug)]
pub struct StructNode {
    pub name: String,
    pub fields: Vec<TypeFieldNode>,
    // ["struct", <Identifier>, "{", ...fields, "}"]
    pub source: Source,
}

#[derive(Debug)]
pub struct TypeFieldNode {
    pub name: String,
    pub type_annotation: TypeAnnotationNode,
    // [<Identifier>, ":", ...type_annotation]
    pub source: Source,
}

#[derive(Debug)]
pub struct TypeAnnotationNode {
    pub name: String,
    pub r#type: Option<Rc<RefCell<sem::Type>>>,
    // [<Identifier>]
    pub source: Source,
}

#[derive(Debug)]
pub struct FunctionNode {
    pub name: String,
    pub params: Vec<ParamNode>,
    pub body: Vec<StatementNode>,
    // ["fun", <Identifier>, "(", ...params, ")", ...body, "end"]
    pub source: Source,
}

#[derive(Debug)]
pub struct ParamNode {
    pub expr: Vec<ExprNode>,
    // ["fun", <Identifier>, "(", ...params, ")", ...body, "end"]
    pub source: Source,
}

#[derive(Debug)]
pub struct StatementNode {
    pub name: String,
    // [<Identifier>, "(", ...params, ")", ...body, "end"]
    pub source: Source,
}

#[derive(Debug)]
pub struct ExprNode {
    pub kind: ExprKind,
    pub r#type: Rc<RefCell<sem::Type>>,
    pub source: Source,
}

#[derive(Debug)]
pub enum ExprKind {
    Integer(i32),
    Add(
        Box<ExprNode>,
        Box<ExprNode>,
        Option<Rc<RefCell<sem::Binding>>>,
    ),
}
