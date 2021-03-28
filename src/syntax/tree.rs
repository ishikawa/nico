use crate::sem;
use crate::tokenizer::Token;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug)]
pub enum SyntaxToken {
    Interpreted(Rc<Token>),
    Missing(Rc<Token>),
    Skipped(Rc<Token>),
}

#[derive(Debug)]
pub struct Code {
    pub tokens: Vec<SyntaxToken>,
}

impl Code {
    pub fn with_token(token: Token) -> Self {
        Self {
            tokens: vec![SyntaxToken::Interpreted(Rc::new(token))],
        }
    }
}

pub struct ModuleNode {
    pub children: Vec<TopLevel>,
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
///
/// tokens: ["struct", <Identifier>, "{", ...fields, "}"]
#[derive(Debug)]
pub struct StructNode {
    pub name: String,
    pub fields: Vec<TypeFieldNode>,
    pub code: Code,
}

#[derive(Debug)]
/// tokens: [<Identifier>, ":", ...type_annotation]
pub struct TypeFieldNode {
    pub name: String,
    pub type_annotation: TypeAnnotationNode,
    pub code: Code,
}

#[derive(Debug)]
/// tokens: [<Identifier>]
pub struct TypeAnnotationNode {
    pub name: String,
    pub r#type: Option<Rc<RefCell<sem::Type>>>,
    pub code: Code,
}

#[derive(Debug)]
/// tokens: ["fun", <Identifier>, "(", ...params, ")", ...body, "end"]
pub struct FunctionNode {
    pub name: String,
    pub params: Vec<ParamNode>,
    pub body: Vec<StatementNode>,
    pub code: Code,
}

#[derive(Debug)]
/// tokens: [<Identifier>]
pub struct ParamNode {
    pub name: String,
    pub code: Code,
}

#[derive(Debug)]
/// tokens: [...expr]
pub struct StatementNode {
    pub expr: ExprNode,
}

#[derive(Debug)]
pub struct ExprNode {
    pub kind: Expr,
    pub r#type: Rc<RefCell<sem::Type>>,
    pub code: Code,
}

#[derive(Debug)]
pub enum Expr {
    Integer(i32),
}

// --- tokens
impl StatementNode {
    pub fn tokens(&self) -> Box<dyn Iterator<Item = &'_ SyntaxToken> + '_> {
        self.expr.tokens()
    }
}

impl ExprNode {
    pub fn tokens(&self) -> Box<dyn Iterator<Item = &'_ SyntaxToken> + '_> {
        match self.kind {
            Expr::Integer(_) => Box::new(self.code.tokens.iter()),
        }
    }
}
