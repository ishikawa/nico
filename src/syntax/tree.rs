use crate::tokenizer::Token;
use crate::{sem, tokenizer::SyntaxToken};
use std::rc::Rc;
use std::{cell::RefCell, slice};

#[derive(Debug)]
pub struct Program {
    pub body: Vec<TopLevelKind>,
}

#[derive(Debug)]
pub enum TopLevelKind {
    StructDefinition(StructDefinition),
    FunctionDefinition(FunctionDefinition),
    Statement(Statement),
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
pub struct StructDefinition {
    pub name: String,
    pub fields: Vec<TypeField>,
    pub tokens: Vec<SyntaxToken>,
}

#[derive(Debug)]
/// tokens: [<Identifier>, ":", ...type_annotation]
pub struct TypeField {
    pub name: String,
    pub type_annotation: TypeAnnotation,
    pub tokens: Vec<SyntaxToken>,
}

#[derive(Debug)]
/// tokens: [<Identifier>]
pub struct TypeAnnotation {
    pub name: String,
    pub r#type: Option<Rc<RefCell<sem::Type>>>,
    pub tokens: Vec<SyntaxToken>,
}

#[derive(Debug)]
/// tokens: ["fun", <Identifier>, "(", ...params, ")", ...body, "end"]
pub struct FunctionDefinition {
    pub name: String,
    pub params: Vec<FunctionParameter>,
    pub body: Vec<Statement>,
    pub tokens: Vec<SyntaxToken>,
}

#[derive(Debug)]
pub struct FunctionParameter {
    pub name: String,
    pub tokens: Vec<SyntaxToken>,
}

#[derive(Debug)]
pub struct Statement {
    pub expression: Expression,
}

#[derive(Debug)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub r#type: Rc<RefCell<sem::Type>>,
    pub tokens: Vec<SyntaxToken>,
}

#[derive(Debug)]
pub enum ExpressionKind {
    Integer(i32),
    Identifier(String),
    String(Option<String>),
    Subscript {
        operand: Box<Expression>,
        index: Option<Box<Expression>>,
    },

    // Binary Op
    // tokens: [...lhs, <operator>, ...rhs]
    Add(
        Box<Expression>,
        Option<Box<Expression>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ),
    Sub(
        Box<Expression>,
        Option<Box<Expression>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ),
    Rem(
        Box<Expression>,
        Option<Box<Expression>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ),
    Mul(
        Box<Expression>,
        Option<Box<Expression>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ),
    Div(
        Box<Expression>,
        Option<Box<Expression>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ),

    // Relational operator
    Lt(
        Box<Expression>,
        Option<Box<Expression>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ), // Less Than
    Gt(
        Box<Expression>,
        Option<Box<Expression>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ), // Greater Than
    Le(
        Box<Expression>,
        Option<Box<Expression>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ), // Less than Equal
    Ge(
        Box<Expression>,
        Option<Box<Expression>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ), // Greater than Equal
    Eq(
        Box<Expression>,
        Option<Box<Expression>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ), // Equal
    Ne(
        Box<Expression>,
        Option<Box<Expression>>,
        Option<Rc<RefCell<sem::Binding>>>,
    ), // Not Equal

    // Unary operator
    Minus(Option<Box<Expression>>, Option<Rc<RefCell<sem::Binding>>>),
    Plus(Option<Box<Expression>>, Option<Rc<RefCell<sem::Binding>>>),
}

// --- tokens
impl Statement {
    pub fn tokens(&self) -> SyntaxTokens<'_> {
        self.expression.tokens()
    }
}

impl Expression {
    pub fn tokens(&self) -> SyntaxTokens<'_> {
        match self.kind {
            ExpressionKind::Integer(_)
            | ExpressionKind::Identifier(_)
            | ExpressionKind::String(_) => SyntaxTokens::new(self.tokens.iter(), vec![]),
            ExpressionKind::Subscript {
                operand: ref lhs,
                index: ref rhs,
            }
            | ExpressionKind::Add(ref lhs, ref rhs, ..)
            | ExpressionKind::Sub(ref lhs, ref rhs, ..)
            | ExpressionKind::Rem(ref lhs, ref rhs, ..)
            | ExpressionKind::Mul(ref lhs, ref rhs, ..)
            | ExpressionKind::Div(ref lhs, ref rhs, ..)
            | ExpressionKind::Eq(ref lhs, ref rhs, ..)
            | ExpressionKind::Ne(ref lhs, ref rhs, ..)
            | ExpressionKind::Le(ref lhs, ref rhs, ..)
            | ExpressionKind::Ge(ref lhs, ref rhs, ..)
            | ExpressionKind::Lt(ref lhs, ref rhs, ..)
            | ExpressionKind::Gt(ref lhs, ref rhs, ..) => {
                let mut children = vec![lhs.tokens()];

                if let Some(rhs) = rhs {
                    children.push(rhs.tokens())
                }

                SyntaxTokens::new(self.tokens.iter(), children)
            }
            ExpressionKind::Plus(ref operand, ..) | ExpressionKind::Minus(ref operand, ..) => {
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
