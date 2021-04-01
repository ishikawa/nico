use super::errors::ParseError;
use super::tree::*;
use crate::sem::{self, Binding};
use crate::tokenizer::{TokenKind, Tokenizer};
use crate::util::naming::PrefixNaming;
use crate::util::wrap;
use std::cell::RefCell;
use std::rc::Rc;

const DEBUG: bool = false;

pub type ParseResult = Result<Option<ExprNode>, ParseError>;

type BinaryOpBuilder =
    fn(Box<ExprNode>, Option<Box<ExprNode>>, Option<Rc<RefCell<Binding>>>) -> Expr;

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

impl<'a> Parser<'a> {
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
                let token = self.tokenizer.peek();

                match &token.kind {
                    TokenKind::Eos => break,
                    _ => {
                        let token = self.tokenizer.next_token();
                        children.push(TopLevel::Unknown(token));
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

        match self.tokenizer.peek_kind() {
            TokenKind::Let => {
                self.tokenizer.next_token();
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

    fn parse_expr(&mut self) -> ParseResult {
        self.debug_trace("parse_expr");
        self.parse_rel_op1()
    }

    fn parse_rel_op1(&mut self) -> ParseResult {
        self.debug_trace("parse_rel_op1");
        self._parse_binary_op(
            Parser::parse_rel_op2,
            &[(TokenKind::Eq, Expr::Eq), (TokenKind::Ne, Expr::Ne)],
        )
    }

    fn parse_rel_op2(&mut self) -> ParseResult {
        self.debug_trace("parse_rel_op2");
        self._parse_binary_op(
            Parser::parse_binary_op1,
            &[
                (TokenKind::Le, Expr::Le),
                (TokenKind::Ge, Expr::Ge),
                (TokenKind::Char('<'), Expr::Lt),
                (TokenKind::Char('>'), Expr::Gt),
            ],
        )
    }

    fn parse_binary_op1(&mut self) -> ParseResult {
        self.debug_trace("parse_binary_op1");
        self._parse_binary_op(
            Parser::parse_binary_op2,
            &[
                (TokenKind::Char('+'), Expr::Add),
                (TokenKind::Char('-'), Expr::Sub),
                (TokenKind::Char('%'), Expr::Rem),
            ],
        )
    }

    fn parse_binary_op2(&mut self) -> ParseResult {
        self.debug_trace("parse_binary_op2");
        self._parse_binary_op(
            Parser::parse_unary_op,
            &[
                (TokenKind::Char('*'), Expr::Mul),
                (TokenKind::Char('/'), Expr::Div),
            ],
        )
    }

    fn parse_unary_op(&mut self) -> ParseResult {
        self.debug_trace("parse_unary_op");

        let builder = match self.tokenizer.peek_kind() {
            TokenKind::Char('+') => Expr::Plus,
            TokenKind::Char('-') => Expr::Minus,
            _ => return self.parse_access(),
        };

        // unary operators are right associative.
        let op_token = self.tokenizer.next_token();
        let mut tokens = vec![SyntaxToken::Interpreted(Rc::new(op_token))];
        let mut operand = None;

        loop {
            match self.parse_unary_op()? {
                None => {
                    // If we couldn't parse the right hand expression, retry
                    // parsing after consuming a token as skipped.
                    let t = self.tokenizer.next_token();
                    tokens.push(SyntaxToken::skipped(t, "expression"));

                    if self.tokenizer.is_at_end() {
                        break;
                    }
                }
                Some(node) => {
                    operand = Some(node);
                    tokens.push(SyntaxToken::Child);
                    break;
                }
            }
        }

        // node
        let kind = builder(operand.map(Box::new), None);
        let r#type = self.new_type_var();
        let code = Code::new(tokens);

        Ok(Some(ExprNode { kind, code, r#type }))
    }

    fn parse_access(&mut self) -> ParseResult {
        self.debug_trace("parse_access");

        let operand = self.parse_primary();
        let mut operand = if let Some(operand) = operand {
            operand
        } else {
            return Ok(None);
        };

        loop {
            // To distinguish `x\n[...]` and `x[...]`, we have to capture
            // `tokenizer.is_newline_seen()`, so try to advance tokenizer.
            self.tokenizer.peek();

            if self.tokenizer.is_newline_seen() {
                break;
            }

            let token = self.tokenizer.peek();

            match token.kind {
                TokenKind::Char('[') => {
                    let open_token = self.tokenizer.next_token();
                    let mut index_node;
                    let mut tokens = vec![
                        SyntaxToken::Child,
                        SyntaxToken::Interpreted(Rc::new(open_token)),
                    ];
                    let mut closed = false;

                    loop {
                        index_node = self.parse_expr()?.map(Box::new);

                        if index_node.is_some() {
                            tokens.push(SyntaxToken::Child);
                            break;
                        } else {
                            // If we couldn't parse the subscript expression, retry
                            // parsing after consuming a token as skipped.
                            let t = self.tokenizer.next_token();

                            if let TokenKind::Char(']') = t.kind {
                                closed = true;
                            }

                            tokens.push(SyntaxToken::skipped(t, "expression"));

                            if self.tokenizer.is_at_end() || closed {
                                break;
                            }
                        }
                    }

                    // Read "]" if needed.
                    if !closed {
                        if let TokenKind::Char(']') = self.tokenizer.peek_kind() {
                            let t = self.tokenizer.next_token();
                            tokens.push(SyntaxToken::Interpreted(Rc::new(t)));
                        } else {
                            let missed = self.tokenizer.build_token(TokenKind::Char(']'), "]");
                            tokens.push(SyntaxToken::Missing(Rc::new(missed)))
                        }
                    }

                    // node
                    let kind = Expr::Subscript {
                        operand: Box::new(operand),
                        index: index_node,
                    };
                    let r#type = self.new_type_var();
                    let code = Code::new(tokens);

                    operand = ExprNode { kind, code, r#type };
                }
                _ => break,
            }
        }

        Ok(Some(operand))
    }

    fn parse_primary(&mut self) -> Option<ExprNode> {
        self.debug_trace("parse_primary");

        let token = self.tokenizer.peek();
        let node = match token.kind {
            TokenKind::Integer(_) => self.read_integer(),
            TokenKind::Identifier(_) => self.read_identifier(),
            TokenKind::StringStart => self.read_string(),
            _ => return None,
        };

        Some(node)
    }

    // --- Generic implementations
    fn read_integer(&mut self) -> ExprNode {
        let token = self.tokenizer.next_token();

        if let TokenKind::Integer(i) = token.kind {
            let kind = Expr::Integer(i);
            let code = Code::with_token(token);
            let r#type = wrap(sem::Type::Int32);

            ExprNode { kind, code, r#type }
        } else {
            unreachable!()
        }
    }

    fn read_identifier(&mut self) -> ExprNode {
        let token = self.tokenizer.next_token();

        if let TokenKind::Identifier(ref id) = token.kind {
            let kind = Expr::Identifier(id.clone());
            let code = Code::with_token(token);
            let r#type = self.new_type_var();

            ExprNode { kind, code, r#type }
        } else {
            unreachable!()
        }
    }

    fn read_string(&mut self) -> ExprNode {
        let start_token = self.tokenizer.next_token(); // StringStart
        let mut tokens = vec![SyntaxToken::Interpreted(Rc::new(start_token))];
        let mut string = String::new();
        let mut has_error = false;

        loop {
            let token = self.tokenizer.next_token();

            match token.kind {
                TokenKind::StringContent(ref s) => {
                    if !has_error {
                        string.push_str(s);
                    }
                    tokens.push(SyntaxToken::Interpreted(Rc::new(token)));
                }
                TokenKind::StringEnd => {
                    tokens.push(SyntaxToken::Interpreted(Rc::new(token)));
                    break;
                }
                TokenKind::UnrecognizedEscapeSequence(_) => {
                    tokens.push(SyntaxToken::skipped(token, "ESCAPE SEQUENCE"));
                    has_error = true;
                }
                _ => {
                    let missed = self.tokenizer.build_token(TokenKind::StringEnd, "\"");
                    tokens.push(SyntaxToken::Missing(Rc::new(missed)));
                    has_error = true;
                    break;
                }
            }
        }

        let kind = if has_error {
            Expr::String(None)
        } else {
            Expr::String(Some(string))
        };
        let code = Code::new(tokens);
        let r#type = wrap(sem::Type::String);

        ExprNode { kind, code, r#type }
    }

    fn _parse_binary_op(
        &mut self,
        next_parser: fn(&mut Parser<'a>) -> ParseResult,
        operators: &[(TokenKind, BinaryOpBuilder)],
    ) -> ParseResult {
        let lhs = next_parser(self)?;
        let mut lhs = if let Some(lhs) = lhs {
            lhs
        } else {
            return Ok(None);
        };

        loop {
            let kind = self.tokenizer.peek_kind();
            let builder = operators
                .iter()
                .find(|(op, _)| op == kind)
                .map(|(_, builder)| builder);

            let builder = if let Some(builder) = builder {
                builder
            } else {
                break;
            };

            // A newline character terminates node construction.
            if self.tokenizer.is_newline_seen() {
                break;
            }

            let op_token = self.tokenizer.next_token();
            let mut rhs;
            let mut tokens = vec![
                SyntaxToken::Child,
                SyntaxToken::Interpreted(Rc::new(op_token)),
            ];

            loop {
                rhs = next_parser(self)?.map(Box::new);

                if rhs.is_some() {
                    tokens.push(SyntaxToken::Child);
                    break;
                } else {
                    // If we couldn't parse the right hand expression, retry
                    // parsing after consuming a token as skipped.
                    let t = self.tokenizer.next_token();
                    tokens.push(SyntaxToken::skipped(t, "expression"));

                    if self.tokenizer.is_at_end() {
                        break;
                    }
                }
            }

            // node
            let kind = builder(Box::new(lhs), rhs, None);
            let r#type = self.new_type_var();
            let code = Code::new(tokens);

            lhs = ExprNode { kind, code, r#type };
        }

        Ok(Some(lhs))
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
        assert_eq!(module.children.len(), 1);

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
        assert_eq!(module.children.len(), 1);

        let stmt = unwrap_statement(&module.children[0]);
        assert_matches!(&stmt.expr.kind, Expr::Add(lhs, Some(rhs), ..) => {
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

    #[test]
    fn add_integer_missing_node() {
        let module = Parser::parse_string("1+").unwrap();
        assert!(!module.children.is_empty());
        assert_eq!(module.children.len(), 1);

        let stmt = unwrap_statement(&module.children[0]);
        assert_matches!(&stmt.expr.kind, Expr::Add(lhs, None, ..) => {
            assert_matches!(lhs.kind, Expr::Integer(1));
        });

        let tokens = stmt.tokens().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 3);

        let token = unwrap_interpreted_token(tokens[0]);
        assert_matches!(token.kind, TokenKind::Integer(1));

        let token = unwrap_interpreted_token(tokens[1]);
        assert_matches!(token.kind, TokenKind::Char('+'));

        let (token, expected) = unwrap_skipped_token(tokens[2]);
        assert_eq!(token.kind, TokenKind::Eos);
        assert_eq!(expected, "expression");
    }

    #[test]
    fn add_integer_skipped_tokens() {
        let module = Parser::parse_string("1 + % ? 2").unwrap();
        assert!(!module.children.is_empty());
        assert_eq!(module.children.len(), 1);

        let stmt = unwrap_statement(&module.children[0]);
        assert_matches!(&stmt.expr.kind, Expr::Add(lhs, Some(rhs), ..) => {
            assert_matches!(lhs.kind, Expr::Integer(1));
            assert_matches!(rhs.kind, Expr::Integer(2));
        });

        let tokens = stmt.tokens().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 5);

        let token = unwrap_interpreted_token(tokens[0]);
        assert_matches!(token.kind, TokenKind::Integer(1));

        let token = unwrap_interpreted_token(tokens[1]);
        assert_matches!(token.kind, TokenKind::Char('+'));

        let (token, expected) = unwrap_skipped_token(tokens[2]);
        assert_eq!(token.kind, TokenKind::Char('%'));
        assert_eq!(expected, "expression");

        let (token, expected) = unwrap_skipped_token(tokens[3]);
        assert_eq!(token.kind, TokenKind::Char('?'));
        assert_eq!(expected, "expression");

        let token = unwrap_interpreted_token(tokens[4]);
        assert_matches!(token.kind, TokenKind::Integer(2));
    }

    #[test]
    fn unary_op() {
        let module = Parser::parse_string("-1").unwrap();
        assert!(!module.children.is_empty());
        assert_eq!(module.children.len(), 1);

        let stmt = unwrap_statement(&module.children[0]);
        assert_matches!(&stmt.expr.kind, Expr::Minus(Some(operand), ..) => {
            assert_matches!(operand.kind, Expr::Integer(1));
        });

        let tokens = stmt.tokens().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 2);

        let token = unwrap_interpreted_token(tokens[0]);
        assert_matches!(token.kind, TokenKind::Char('-'));

        let token = unwrap_interpreted_token(tokens[1]);
        assert_matches!(token.kind, TokenKind::Integer(1));
    }

    #[test]
    fn unary_op_nested() {
        let module = Parser::parse_string("-+1").unwrap();
        assert!(!module.children.is_empty());
        assert_eq!(module.children.len(), 1);

        let stmt = unwrap_statement(&module.children[0]);
        assert_matches!(&stmt.expr.kind, Expr::Minus(Some(operand), ..) => {
            assert_matches!(&operand.kind, Expr::Plus(Some(operand), ..) => {
                assert_matches!(operand.kind, Expr::Integer(1));
            });
        });

        let tokens = stmt.tokens().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 3);

        let token = unwrap_interpreted_token(tokens[0]);
        assert_matches!(token.kind, TokenKind::Char('-'));

        let token = unwrap_interpreted_token(tokens[1]);
        assert_matches!(token.kind, TokenKind::Char('+'));

        let token = unwrap_interpreted_token(tokens[2]);
        assert_matches!(token.kind, TokenKind::Integer(1));
    }

    #[test]
    fn subscript_index() {
        let module = Parser::parse_string("a[0]").unwrap();
        assert!(!module.children.is_empty());
        assert_eq!(module.children.len(), 1);

        let stmt = unwrap_statement(&module.children[0]);
        assert_matches!(&stmt.expr.kind, Expr::Subscript{ operand, index: Some(index) } => {
            assert_matches!(&operand.kind, Expr::Identifier(id) => {
                assert_eq!(id, "a");
            });
            assert_matches!(&index.kind, Expr::Integer(0));
        });

        let tokens = stmt.tokens().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 4);

        let token = unwrap_interpreted_token(tokens[0]);
        assert_matches!(&token.kind, TokenKind::Identifier(id) => {
            assert_eq!(id, "a");
        });

        let token = unwrap_interpreted_token(tokens[1]);
        assert_matches!(token.kind, TokenKind::Char('['));

        let token = unwrap_interpreted_token(tokens[2]);
        assert_matches!(token.kind, TokenKind::Integer(0));

        let token = unwrap_interpreted_token(tokens[3]);
        assert_matches!(token.kind, TokenKind::Char(']'));
    }

    #[test]
    fn subscript_skip_close() {
        let module = Parser::parse_string("a[]").unwrap();
        assert!(!module.children.is_empty());
        assert_eq!(module.children.len(), 1);

        let stmt = unwrap_statement(&module.children[0]);
        assert_matches!(&stmt.expr.kind, Expr::Subscript{ operand, index: None } => {
            assert_matches!(&operand.kind, Expr::Identifier(id) => {
                assert_eq!(id, "a");
            });
        });

        let tokens = stmt.tokens().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 3);

        let token = unwrap_interpreted_token(tokens[0]);
        assert_matches!(&token.kind, TokenKind::Identifier(id) => {
            assert_eq!(id, "a");
        });

        let token = unwrap_interpreted_token(tokens[1]);
        assert_matches!(token.kind, TokenKind::Char('['));

        let (token, expected) = unwrap_skipped_token(tokens[2]);
        assert_eq!(expected, "expression");
        assert_matches!(token.kind, TokenKind::Char(']'));
    }

    #[test]
    fn subscript_not_closed() {
        let module = Parser::parse_string("a[1\nb").unwrap();
        assert_eq!(module.children.len(), 2);

        // subscript
        let stmt = unwrap_statement(&module.children[0]);
        assert_matches!(&stmt.expr.kind, Expr::Subscript{ operand, index: Some(index) } => {
            assert_matches!(&operand.kind, Expr::Identifier(id) => {
                assert_eq!(id, "a");
            });
            assert_matches!(&index.kind, Expr::Integer(1));
        });

        let tokens = stmt.tokens().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 4);

        let token = unwrap_missing_token(tokens[3]);
        assert_matches!(token.kind, TokenKind::Char(']'));
    }

    // --- helpers

    fn unwrap_statement(node: &TopLevel) -> &StatementNode {
        if let TopLevel::Statement(node) = node {
            node
        } else {
            panic!("expected statement")
        }
    }

    fn unwrap_interpreted_token(token: &SyntaxToken) -> Rc<Token> {
        if let SyntaxToken::Interpreted(token) = token {
            Rc::clone(token)
        } else {
            panic!("expected interpreted token")
        }
    }

    fn unwrap_missing_token(token: &SyntaxToken) -> Rc<Token> {
        if let SyntaxToken::Missing(token) = token {
            Rc::clone(token)
        } else {
            panic!("expected missing token")
        }
    }

    fn unwrap_skipped_token(token: &SyntaxToken) -> (Rc<Token>, String) {
        if let SyntaxToken::Skipped { token, expected } = token {
            (Rc::clone(token), expected.clone())
        } else {
            panic!("expected skipped token")
        }
    }
}
