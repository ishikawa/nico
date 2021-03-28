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

type SyntaxTokenIterator<'a> = Box<dyn Iterator<Item = &'a SyntaxToken> + 'a>;

// --- tokens
impl StatementNode {
    pub fn tokens(&self) -> SyntaxTokenIterator<'_> {
        self.expr.tokens()
    }
}

impl ExprNode {
    pub fn tokens(&self) -> SyntaxTokenIterator<'_> {
        match self.kind {
            Expr::Integer(_) => Box::new(self.code.tokens.iter()),
            Expr::Add(ref lhs, ref rhs, ..) => Box::new(SyntaxTokens::new(
                self.code.tokens.iter(),
                vec![lhs.tokens(), rhs.tokens()],
            )),
        }
    }
}

pub struct SyntaxTokens<'a> {
    iterator: slice::Iter<'a, SyntaxToken>,
    children: Vec<SyntaxTokenIterator<'a>>,
    child_iterator: Option<SyntaxTokenIterator<'a>>,
    child_index: usize,
}

impl<'a> SyntaxTokens<'a> {
    pub fn new(
        iterator: slice::Iter<'a, SyntaxToken>,
        children: Vec<SyntaxTokenIterator<'a>>,
    ) -> Self {
        Self {
            iterator,
            children,
            child_iterator: None,
            child_index: 0,
        }
    }
}

impl<'a> Iterator for SyntaxTokens<'a> {
    type Item = &'a SyntaxToken;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(ref mut child_iterator) = self.child_iterator {
            let token = child_iterator.next();

            if token.is_none() {
                self.child_iterator = None;
            } else {
                return token;
            }
        }

        let next = self.iterator.next();

        if let Some(SyntaxToken::Child) = next {
            if self.child_index >= self.children.len() {
                panic!("children vec overflow: {}", self.children.len());
            }

            let mut it = self.children.remove(self.child_index);
            let token = it.next();

            self.child_iterator.replace(it);
            return token;
        }

        next
    }
}
