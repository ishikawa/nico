use crate::sem;
use crate::tokenizer::Token;
use std::rc::Rc;
use std::{cell::RefCell, slice};

#[derive(Debug)]
pub enum SyntaxToken {
    Interpreted(Rc<Token>),
    Missing(Rc<Token>),
    /// A skipped token with the description of an expected node.
    Skipped {
        token: Rc<Token>,
        expected: String,
    },
    Child,
}

impl SyntaxToken {
    pub fn interpreted(token: Token) -> Self {
        Self::Interpreted(Rc::new(token))
    }

    pub fn missing(token: Token) -> Self {
        Self::Missing(Rc::new(token))
    }

    pub fn skipped<S: Into<String>>(token: Token, expected: S) -> Self {
        Self::Skipped {
            token: Rc::new(token),
            expected: expected.into(),
        }
    }
}

#[derive(Debug)]
pub struct ModuleNode {
    pub children: Vec<TopLevel>,
}

#[derive(Debug)]
pub enum TopLevel {
    Struct(StructNode),
    Function(FunctionNode),
    Statement(StatementNode),
    Unknown(Token),
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
    pub tokens: Vec<SyntaxToken>,
}

#[derive(Debug)]
/// tokens: [<Identifier>, ":", ...type_annotation]
pub struct TypeFieldNode {
    pub name: String,
    pub type_annotation: TypeAnnotationNode,
    pub tokens: Vec<SyntaxToken>,
}

#[derive(Debug)]
/// tokens: [<Identifier>]
pub struct TypeAnnotationNode {
    pub name: String,
    pub r#type: Option<Rc<RefCell<sem::Type>>>,
    pub tokens: Vec<SyntaxToken>,
}

#[derive(Debug)]
/// tokens: ["fun", <Identifier>, "(", ...params, ")", ...body, "end"]
pub struct FunctionNode {
    pub name: String,
    pub params: Vec<ParamNode>,
    pub body: Vec<StatementNode>,
    pub tokens: Vec<SyntaxToken>,
}

#[derive(Debug)]
/// tokens: [<Identifier>]
pub struct ParamNode {
    pub name: String,
    pub tokens: Vec<SyntaxToken>,
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
    pub tokens: Vec<SyntaxToken>,
}

#[derive(Debug)]
pub enum Expr {
    Integer(i32),
    Identifier(String),
    String(Option<String>),
    Subscript {
        operand: Box<ExprNode>,
        index: Option<Box<ExprNode>>,
    },

    // Binary Op
    // tokens: [...lhs, <operator>, ...rhs]
    Add(
        Box<ExprNode>,
        Option<Box<ExprNode>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ),
    Sub(
        Box<ExprNode>,
        Option<Box<ExprNode>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ),
    Rem(
        Box<ExprNode>,
        Option<Box<ExprNode>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ),
    Mul(
        Box<ExprNode>,
        Option<Box<ExprNode>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ),
    Div(
        Box<ExprNode>,
        Option<Box<ExprNode>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ),

    // Relational operator
    Lt(
        Box<ExprNode>,
        Option<Box<ExprNode>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ), // Less Than
    Gt(
        Box<ExprNode>,
        Option<Box<ExprNode>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ), // Greater Than
    Le(
        Box<ExprNode>,
        Option<Box<ExprNode>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ), // Less than Equal
    Ge(
        Box<ExprNode>,
        Option<Box<ExprNode>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ), // Greater than Equal
    Eq(
        Box<ExprNode>,
        Option<Box<ExprNode>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ), // Equal
    Ne(
        Box<ExprNode>,
        Option<Box<ExprNode>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ), // Not Equal

    // Unary operator
    Minus(Option<Box<ExprNode>>, Option<Rc<RefCell<sem::Binding>>>),
    Plus(Option<Box<ExprNode>>, Option<Rc<RefCell<sem::Binding>>>),
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
            Expr::Integer(_) | Expr::Identifier(_) | Expr::String(_) => {
                SyntaxTokens::new(self.tokens.iter(), vec![])
            }
            Expr::Subscript {
                operand: ref lhs,
                index: ref rhs,
            }
            | Expr::Add(ref lhs, ref rhs, ..)
            | Expr::Sub(ref lhs, ref rhs, ..)
            | Expr::Rem(ref lhs, ref rhs, ..)
            | Expr::Mul(ref lhs, ref rhs, ..)
            | Expr::Div(ref lhs, ref rhs, ..)
            | Expr::Eq(ref lhs, ref rhs, ..)
            | Expr::Ne(ref lhs, ref rhs, ..)
            | Expr::Le(ref lhs, ref rhs, ..)
            | Expr::Ge(ref lhs, ref rhs, ..)
            | Expr::Lt(ref lhs, ref rhs, ..)
            | Expr::Gt(ref lhs, ref rhs, ..) => {
                let mut children = vec![lhs.tokens()];

                if let Some(rhs) = rhs {
                    children.push(rhs.tokens())
                }

                SyntaxTokens::new(self.tokens.iter(), children)
            }
            Expr::Plus(ref operand, ..) | Expr::Minus(ref operand, ..) => {
                let mut children = vec![];

                if let Some(operand) = operand {
                    children.push(operand.tokens())
                }

                SyntaxTokens::new(self.tokens.iter(), children)
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
