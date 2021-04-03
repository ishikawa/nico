use super::{SyntaxToken, Token, TokenKind};
use crate::sem;
use std::cell::RefCell;
use std::rc::Rc;
use std::slice;

// Token
#[derive(Debug)]
pub enum SyntaxTokenItem {
    Token(SyntaxToken),
    Child,
}

impl SyntaxTokenItem {
    pub fn interpreted(token: Token) -> Self {
        Self::Token(SyntaxToken::Interpreted(token))
    }

    pub fn missing(token: Token) -> Self {
        Self::Token(SyntaxToken::Missing(token))
    }

    pub fn skipped<S: Into<String>>(token: Token, expected: S) -> Self {
        Self::Token(SyntaxToken::Skipped {
            token,
            expected: expected.into(),
        })
    }
}

#[derive(Debug, Default)]
pub struct TokensBuilder {
    tokens: Vec<SyntaxTokenItem>,
}

impl TokensBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn interpret(&mut self, token: Token) -> &mut Self {
        self.tokens
            .push(SyntaxTokenItem::Token(SyntaxToken::Interpreted(token)));
        self
    }

    pub fn missing(&mut self, token: Token) -> &mut Self {
        self.tokens
            .push(SyntaxTokenItem::Token(SyntaxToken::Missing(token)));
        self
    }

    pub fn skip<S: Into<String>>(&mut self, token: Token, expected: S) -> &mut Self {
        self.tokens
            .push(SyntaxTokenItem::Token(SyntaxToken::Skipped {
                token,
                expected: expected.into(),
            }));
        self
    }
}

// Node
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
#[derive(Debug)]
pub struct StructDefinition {
    pub name: String,
    pub fields: Vec<TypeField>,
    pub tokens: Vec<SyntaxTokenItem>,
}

#[derive(Debug)]
pub struct TypeField {
    pub name: String,
    pub type_annotation: TypeAnnotation,
    pub tokens: Vec<SyntaxTokenItem>,
}

#[derive(Debug)]
pub struct TypeAnnotation {
    pub name: String,
    pub r#type: Option<Rc<RefCell<sem::Type>>>,
    pub tokens: Vec<SyntaxTokenItem>,
}

#[derive(Debug)]
pub struct FunctionDefinition {
    pub name: Option<String>,
    pub params: Vec<FunctionParameter>,
    pub body: Vec<Statement>,
    pub tokens: Vec<SyntaxTokenItem>,
}

#[derive(Debug)]
pub struct FunctionParameter {
    pub name: String,
    pub tokens: Vec<SyntaxTokenItem>,
}

#[derive(Debug)]
pub struct Statement {
    pub expression: Expression,
}

#[derive(Debug)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub r#type: Rc<RefCell<sem::Type>>,
    pub tokens: Vec<SyntaxTokenItem>,
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
pub struct BinaryExpression {
    pub operator: BinaryOperator,
    pub lhs: Box<Expression>,
    pub rhs: Option<Box<Expression>>,
}

#[derive(Debug)]
pub struct SubscriptExpression {
    pub callee: Box<Expression>,
    pub arguments: Vec<Expression>,
}

#[derive(Debug)]
pub struct CallExpression {
    pub callee: Box<Expression>,
    pub arguments: Vec<Expression>,
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
    BinaryExpression(BinaryExpression),
    UnaryExpression(UnaryExpression),
    SubscriptExpression(SubscriptExpression),
    CallExpression(CallExpression),
}

// --- tokens
impl Statement {
    pub fn tokens(&self) -> SyntaxTokens<'_> {
        self.expression.tokens()
    }
}

impl Expression {
    pub fn children(&self) -> Vec<&Expression> {
        let mut children = vec![];

        match &self.kind {
            ExpressionKind::IntegerLiteral(_)
            | ExpressionKind::Identifier(_)
            | ExpressionKind::StringLiteral(_) => {}
            ExpressionKind::BinaryExpression(BinaryExpression { lhs, rhs, .. }) => {
                children.push(&**lhs);

                if let Some(rhs) = rhs {
                    children.push(&**rhs)
                }
            }
            ExpressionKind::UnaryExpression(UnaryExpression { operand, .. }) => {
                if let Some(operand) = operand {
                    children.push(&**operand)
                }
            }
            ExpressionKind::SubscriptExpression(SubscriptExpression { callee, arguments })
            | ExpressionKind::CallExpression(CallExpression { callee, arguments }) => {
                children.push(&**callee);

                for arg in arguments {
                    children.push(arg)
                }
            }
        };

        children
    }

    pub fn tokens(&self) -> SyntaxTokens<'_> {
        let children = self.children().iter().map(|x| x.tokens()).collect();
        SyntaxTokens::new(self.tokens.iter(), children)
    }
}

pub struct SyntaxTokens<'a> {
    iterator: slice::Iter<'a, SyntaxTokenItem>,
    children: Vec<SyntaxTokens<'a>>,
    in_child: bool,
}

impl<'a> SyntaxTokens<'a> {
    pub fn new(
        iterator: slice::Iter<'a, SyntaxTokenItem>,
        children: Vec<SyntaxTokens<'a>>,
    ) -> Self {
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

        match self.iterator.next() {
            None => None,
            Some(SyntaxTokenItem::Child) => {
                self.in_child = true;
                self.next()
            }
            Some(SyntaxTokenItem::Token(ref t)) => Some(t),
        }
    }
}
