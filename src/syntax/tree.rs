use crate::sem;
use crate::tokenizer::Token;
use std::rc::Rc;
use std::{cell::RefCell, slice};

#[derive(Debug)]
pub enum SyntaxToken {
    Interpreted(Rc<Token>),
    Missing(Rc<Token>),
    Skipped(Rc<Token>),
    Child,
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

    // Binary Op
    // tokens: [...lhs, <operator>, ...rhs]
    Add(
        Box<ExprNode>,
        Box<ExprNode>,
        Option<Rc<RefCell<sem::Binding>>>,
    ),
}

// --- tokens
impl StatementNode {
    pub fn tokens(&self) -> SyntaxTokens<'_> {
        self.expr.tokens()
    }
}

impl ExprNode {
    pub fn tokens(&self) -> SyntaxTokens<'_> {
        match self.kind {
            Expr::Integer(_) => SyntaxTokens::new(self.code.tokens.iter(), vec![]),
            Expr::Add(ref lhs, ref rhs, ..) => {
                SyntaxTokens::new(self.code.tokens.iter(), vec![lhs.tokens(), rhs.tokens()])
            }
        }
    }
}

pub struct SyntaxTokens<'a> {
    iterator: slice::Iter<'a, SyntaxToken>,
    children: Vec<SyntaxTokens<'a>>,
    in_child: bool,
}

impl<'a> SyntaxTokens<'a> {
    pub fn new(iterator: slice::Iter<'a, SyntaxToken>, children: Vec<SyntaxTokens<'a>>) -> Self {
        Self {
            iterator,
            children,
            in_child: false,
        }
    }
}

impl<'a> Iterator for SyntaxTokens<'a> {
    type Item = &'a SyntaxToken;

    fn next(&mut self) -> Option<Self::Item> {
        if self.in_child {
            if self.children.is_empty() {
                panic!("children  overflow");
            }

            let token = self.children[0].next();

            if token.is_none() {
                self.children.remove(0);
                self.in_child = false;
            } else {
                return token;
            }
        }

        let next = self.iterator.next();

        if let Some(SyntaxToken::Child) = next {
            self.in_child = true;
            return self.next();
        }

        next
    }
}
