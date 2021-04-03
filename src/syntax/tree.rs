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

impl Expression {
    pub fn unwrap_identifier(&self) -> &Identifier {
        if let ExpressionKind::Identifier(ref expr) = self.kind {
            expr
        } else {
            panic!("Expected identifier");
        }
    }

    pub fn unwrap_subscript_expression(&self) -> &SubscriptExpression {
        if let ExpressionKind::SubscriptExpression(ref expr) = self.kind {
            expr
        } else {
            panic!("Expected subscript expression");
        }
    }

    pub fn unwrap_binary_expression(&self) -> &BinaryExpression {
        if let ExpressionKind::BinaryExpression(ref expr) = self.kind {
            expr
        } else {
            panic!("Expected binary expression");
        }
    }

    pub fn unwrap_unary_expression(&self) -> &UnaryExpression {
        if let ExpressionKind::UnaryExpression(ref expr) = self.kind {
            expr
        } else {
            panic!("Expected unary expression");
        }
    }
}

#[derive(Debug)]
pub struct IntegerLiteral(pub i32);

#[derive(Debug)]
pub struct StringLiteral(pub Option<String>);

#[derive(Debug)]
pub struct Identifier(pub String);

#[derive(Debug)]
pub struct SubscriptExpression {
    pub operand: Box<Expression>,
    pub index: Option<Box<Expression>>,
}

#[derive(Debug)]
pub struct BinaryExpression {
    pub operator: BinaryOperator,
    pub lhs: Box<Expression>,
    pub rhs: Option<Box<Expression>>,
}

#[derive(Debug)]
pub struct UnaryExpression {
    pub operator: UnaryOperator,
    pub operand: Option<Box<Expression>>,
}

#[derive(Debug, Copy, Clone)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Lt,
    Gt,
    Le,
    Ge,
    Eq,
    Ne,
}

#[derive(Debug, Copy, Clone)]
pub enum UnaryOperator {
    Minus,
    Plus,
}

#[derive(Debug)]
pub enum ExpressionKind {
    IntegerLiteral(IntegerLiteral),
    StringLiteral(StringLiteral),
    Identifier(Identifier),
    SubscriptExpression(SubscriptExpression),
    BinaryExpression(BinaryExpression),
    UnaryExpression(UnaryExpression),
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
            ExpressionKind::IntegerLiteral(_)
            | ExpressionKind::Identifier(_)
            | ExpressionKind::StringLiteral(_) => SyntaxTokens::new(self.tokens.iter(), vec![]),
            ExpressionKind::SubscriptExpression(SubscriptExpression {
                operand: ref lhs,
                index: ref rhs,
            })
            | ExpressionKind::BinaryExpression(BinaryExpression {
                ref lhs, ref rhs, ..
            }) => {
                let mut children = vec![lhs.tokens()];

                if let Some(rhs) = rhs {
                    children.push(rhs.tokens())
                }

                SyntaxTokens::new(self.tokens.iter(), children)
            }
            ExpressionKind::UnaryExpression(UnaryExpression { ref operand, .. }) => {
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
