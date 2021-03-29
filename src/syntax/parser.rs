use super::errors::{ParseError, ParseErrorKind};
use super::tree::*;
use crate::sem;
use crate::tokenizer::{TokenKind, Tokenizer};
use crate::util::naming::PrefixNaming;
use crate::util::wrap;
use std::cell::RefCell;
use std::rc::Rc;

const DEBUG: bool = false;

#[derive(Debug)]
pub struct Parser<'a> {
    /// The filename, uri of a source code.
    source: String,
    tokenizer: Tokenizer<'a>,
    naming: PrefixNaming,
}

impl<'a> Parser<'a> {
    pub fn new<S: Into<String>>(tokenizer: Tokenizer<'a>, source: S) -> Self {
        Self {
            tokenizer,
            source: source.into(),
            naming: PrefixNaming::new("?"),
        }
    }
}

impl Parser<'_> {
    pub fn parse_string<S: AsRef<str>>(src: S) -> Result<ModuleNode, ParseError> {
        let tokenizer = Tokenizer::from_string(&src);
        let mut parser = Parser::new(tokenizer, "-");

        parser.parse()
    }

    pub fn parse(&mut self) -> Result<ModuleNode, ParseError> {
        let mut children = vec![];

        loop {
            // Type declaration
            if let Some(node) = self.parse_struct_definition()? {
                children.push(TopLevel::Struct(node));
            }
            // Function
            else if let Some(node) = self.parse_function()? {
                children.push(TopLevel::Function(node));
            }
            // Body for main function
            else if let Some(node) = self.parse_stmt()? {
                children.push(TopLevel::Statement(node));
            }
            // No top level constructs can be consumed. It may be at the end of input or
            // parse error.
            else {
                let token = self.tokenizer.peek()?;

                match &token.kind {
                    TokenKind::Eos => break,
                    kind => {
                        return Err(ParseError {
                            position: token.range.start,
                            kind: ParseErrorKind::SyntaxError(format!(
                                "Unrecognized token: {}",
                                kind
                            )),
                        });
                    }
                }
            }
        }

        Ok(ModuleNode { children })
    }

    #[allow(clippy::unnecessary_wraps)]
    fn parse_struct_definition(&mut self) -> Result<Option<StructNode>, ParseError> {
        self.debug_trace("parse_struct_definition");
        Ok(None)
    }

    #[allow(clippy::unnecessary_wraps)]
    fn parse_function(&mut self) -> Result<Option<FunctionNode>, ParseError> {
        self.debug_trace("parse_function");
        Ok(None)
    }

    fn parse_stmt(&mut self) -> Result<Option<StatementNode>, ParseError> {
        self.debug_trace("parse_stmt");

        match self.tokenizer.peek_kind()? {
            TokenKind::Let => {
                self.tokenizer.next_token()?;
            }
            _ => return self.parse_stmt_expr(),
        };

        // TODO: Variable binding
        Ok(None)
    }

    fn parse_stmt_expr(&mut self) -> Result<Option<StatementNode>, ParseError> {
        self.debug_trace("parse_stmt_expr");

        if let Some(expr) = self.parse_expr()? {
            Ok(Some(StatementNode { expr }))
        } else {
            Ok(None)
        }
    }

    fn parse_expr(&mut self) -> Result<Option<ExprNode>, ParseError> {
        self.debug_trace("parse_expr");
        self.parse_rel_op1()
    }

    fn parse_rel_op1(&mut self) -> Result<Option<ExprNode>, ParseError> {
        self.debug_trace("parse_rel_op1");
        self.parse_rel_op2()
    }

    fn parse_rel_op2(&mut self) -> Result<Option<ExprNode>, ParseError> {
        self.debug_trace("parse_rel_op2");
        self.parse_binary_op1()
    }

    fn parse_binary_op1(&mut self) -> Result<Option<ExprNode>, ParseError> {
        self.debug_trace("parse_binary_op1");

        let lhs = self.parse_binary_op2()?;
        let mut lhs = if let Some(lhs) = lhs {
            lhs
        } else {
            return Ok(None);
        };

        loop {
            let builder = match self.tokenizer.peek_kind() {
                Ok(TokenKind::Char('+')) => Expr::Add,
                Ok(TokenKind::Char('-')) => Expr::Sub,
                Ok(TokenKind::Char('%')) => Expr::Rem,
                _ => break,
            };

            // A newline character terminates node construction.
            if self.tokenizer.is_newline_seen() {
                break;
            }

            let op_token = self.tokenizer.next_token()?;

            let rhs = self.parse_binary_op2()?.ok_or_else(|| {
                ParseError::syntax_error(self.tokenizer.current_position(), "Expected RHS")
            })?;

            // node
            let kind = builder(Box::new(lhs), Box::new(rhs), None);
            let code = Code::new(vec![
                SyntaxToken::Child,
                SyntaxToken::Interpreted(Rc::new(op_token)),
                SyntaxToken::Child,
            ]);
            let r#type = self.new_type_var();

            lhs = ExprNode { kind, code, r#type };
        }

        Ok(Some(lhs))
    }

    fn parse_binary_op2(&mut self) -> Result<Option<ExprNode>, ParseError> {
        self.debug_trace("parse_binary_op2");
        self.parse_unary_op()
    }

    fn parse_unary_op(&mut self) -> Result<Option<ExprNode>, ParseError> {
        self.debug_trace("parse_unary_op");
        self.parse_access()
    }

    fn parse_access(&mut self) -> Result<Option<ExprNode>, ParseError> {
        self.debug_trace("parse_access");
        self.parse_primary()
    }

    fn parse_primary(&mut self) -> Result<Option<ExprNode>, ParseError> {
        self.debug_trace("parse_primary");

        let token = self.tokenizer.peek()?;

        match &token.kind {
            TokenKind::Eos => Ok(None),
            TokenKind::Integer(i) => {
                let kind = Expr::Integer(*i);
                let token = self.tokenizer.next_token()?;
                let code = Code::with_token(token);
                let r#type = wrap(sem::Type::Int32);

                Ok(Some(ExprNode { kind, code, r#type }))
            }
            token_kind => {
                return Err(ParseError::syntax_error(
                    token.range.start,
                    format!("Unexpected token {}", token_kind),
                ));
            }
        }
    }

    // --- Helpers

    /// Returns a new type variable.
    fn new_type_var(&mut self) -> Rc<RefCell<sem::Type>> {
        let name = self.naming.next();
        wrap(sem::Type::new_type_var(&name))
    }

    fn debug_trace(&self, name: &str) {
        if DEBUG {
            eprintln!("[{}] position: {}", name, self.tokenizer.current_position());
        }
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::*;
    use crate::{
        syntax::{Expr, StatementNode, TopLevel},
        tokenizer::Token,
    };
    use assert_matches::assert_matches;

    #[test]
    fn number_integer() {
        let module = Parser::parse_string("42").unwrap();
        assert!(!module.children.is_empty());

        let stmt = unwrap_statement(&module.children[0]);
        assert_matches!(stmt.expr.kind, Expr::Integer(42));

        let tokens = stmt.tokens().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 1);

        let token = unwrap_interpreted_token(tokens[0]);
        assert_matches!(token.kind, TokenKind::Integer(i) => {
            assert_eq!(i, 42);
        });
    }

    #[test]
    fn add_integer() {
        let module = Parser::parse_string("1+2").unwrap();
        assert!(!module.children.is_empty());

        let stmt = unwrap_statement(&module.children[0]);
        assert_matches!(&stmt.expr.kind, Expr::Add(lhs, rhs, ..) => {
            assert_matches!(lhs.kind, Expr::Integer(1));
            assert_matches!(rhs.kind, Expr::Integer(2));
        });

        let tokens = stmt.tokens().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 3);

        let token = unwrap_interpreted_token(tokens[0]);
        assert_matches!(token.kind, TokenKind::Integer(1));

        let token = unwrap_interpreted_token(tokens[1]);
        assert_matches!(token.kind, TokenKind::Char('+'));

        let token = unwrap_interpreted_token(tokens[2]);
        assert_matches!(token.kind, TokenKind::Integer(2));
    }

    // --- helpers

    fn unwrap_statement(node: &TopLevel) -> &StatementNode {
        if let TopLevel::Statement(node) = node {
            node
        } else {
            panic!()
        }
    }

    fn unwrap_interpreted_token(token: &SyntaxToken) -> Rc<Token> {
        if let SyntaxToken::Interpreted(token) = token {
            Rc::clone(token)
        } else {
            panic!()
        }
    }
}
