use super::errors::ParseError;
use super::tree::*;
use super::{TokenKind, Tokenizer};
use crate::sem;
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

impl<'a> Parser<'a> {
    pub fn parse_string<S: AsRef<str>>(src: S) -> Result<Program, ParseError> {
        let tokenizer = Tokenizer::from_string(&src);
        let mut parser = Parser::new(tokenizer, "-");

        parser.parse()
    }

    pub fn parse(&mut self) -> Result<Program, ParseError> {
        let mut body = vec![];

        loop {
            // Type declaration
            if let Some(node) = self.parse_struct_definition()? {
                body.push(TopLevelKind::StructDefinition(node));
            }
            // Function
            else if let Some(node) = self.parse_function()? {
                body.push(TopLevelKind::FunctionDefinition(node));
            }
            // Body for main function
            else if let Some(node) = self.parse_stmt()? {
                body.push(TopLevelKind::Statement(node));
            }
            // No top level constructs can be consumed. It may be at the end of input or
            // parse error.
            else {
                let token = self.tokenizer.peek();

                match &token.kind {
                    TokenKind::Eos => break,
                    _ => {
                        let token = self.tokenizer.next_token();
                        body.push(TopLevelKind::Unknown(token));
                    }
                }
            }
        }

        Ok(Program { body })
    }

    #[allow(clippy::unnecessary_wraps)]
    fn parse_struct_definition(&mut self) -> Result<Option<StructDefinition>, ParseError> {
        self.debug_trace("parse_struct_definition");
        Ok(None)
    }

    #[allow(clippy::unnecessary_wraps)]
    fn parse_function(&mut self) -> Result<Option<FunctionDefinition>, ParseError> {
        self.debug_trace("parse_function");

        let mut tokens = SyntaxTokensBuffer::new();

        // TODO: In L(1) parser, if the `fun` keyword is not followed by an `export` keyword,
        // the `export` keyword cannot be push backed, so we shouldn't stop reading export here.
        let export = self.match_token(TokenKind::Export);

        if export {
            tokens.interpret(self.tokenizer.next_token());
        }

        // fun
        if !self.match_token(TokenKind::Fun) {
            return Ok(None);
        }

        tokens.interpret(self.tokenizer.next_token());

        // name
        let mut function_name = None;

        loop {
            match self.tokenizer.peek_kind() {
                TokenKind::Identifier(name) => {
                    // Okay, it's a function name.
                    function_name = Some(name.clone());
                    tokens.interpret(self.tokenizer.next_token());
                    break;
                }
                TokenKind::Char('(') | TokenKind::Eos => {
                    // Umm, maybe user forgot/omitted a function name?
                    // I'm sorry, but this language is not JavaScript.
                    tokens.missing(
                        self.tokenizer
                            .build_missing(TokenKind::Identifier("".to_string()), "function name"),
                    );
                    break;
                }
                _ => {
                    // Continue until read identifier or over.
                    tokens.skip(self.tokenizer.next_token(), "function name");
                }
            }
        }

        // parameters - begin
        let mut parameters = vec![];
        let mut param_read = false;

        loop {
            match self.tokenizer.peek_kind() {
                TokenKind::Char('(') => {
                    // Beginning of parameters.
                    tokens.interpret(self.tokenizer.next_token());
                    break;
                }
                TokenKind::Char(')') | TokenKind::Eos => {
                    // Umm, maybe user forgot opening paren.
                    //
                    //     fun foo # (
                    //     )
                    tokens.missing(self.tokenizer.build_missing(TokenKind::Char('('), "("));
                    break;
                }
                _ => {
                    if let Some(param) = self.parse_function_parameter()? {
                        // Maybe user forgot opening paren before a param.
                        //     fun foo # (
                        //         a, ...
                        //     )
                        parameters.push(param);

                        tokens.missing(self.tokenizer.build_missing(TokenKind::Char('('), "("));
                        tokens.child();

                        param_read = true;
                        break;
                    } else {
                        // Continue until read an open paren.
                        tokens.skip(self.tokenizer.next_token(), "(");
                    }
                }
            }
        }

        Ok(None)
    }

    #[allow(clippy::unnecessary_wraps)]
    fn parse_function_parameter(&mut self) -> Result<Option<FunctionParameter>, ParseError> {
        if let TokenKind::Identifier(name) = self.tokenizer.peek_kind() {
            let name = name.clone();
            let tokens = SyntaxTokensBuffer::with_interpreted(self.tokenizer.next_token());

            Ok(Some(FunctionParameter { name, tokens }))
        } else {
            Ok(None)
        }
    }

    fn parse_stmt(&mut self) -> Result<Option<Statement>, ParseError> {
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

    fn parse_stmt_expr(&mut self) -> Result<Option<Statement>, ParseError> {
        self.debug_trace("parse_stmt_expr");

        if let Some(expression) = self.parse_expr()? {
            Ok(Some(Statement { expression }))
        } else {
            Ok(None)
        }
    }

    fn parse_expr(&mut self) -> Result<Option<Expression>, ParseError> {
        self.debug_trace("parse_expr");
        self.parse_rel_op1()
    }

    fn parse_rel_op1(&mut self) -> Result<Option<Expression>, ParseError> {
        self.debug_trace("parse_rel_op1");
        self._parse_binary_op(
            Parser::parse_rel_op2,
            &[
                (TokenKind::Eq, BinaryOperator::Eq),
                (TokenKind::Ne, BinaryOperator::Ne),
            ],
        )
    }

    fn parse_rel_op2(&mut self) -> Result<Option<Expression>, ParseError> {
        self.debug_trace("parse_rel_op2");
        self._parse_binary_op(
            Parser::parse_binary_op1,
            &[
                (TokenKind::Le, BinaryOperator::Le),
                (TokenKind::Ge, BinaryOperator::Ge),
                (TokenKind::Char('<'), BinaryOperator::Lt),
                (TokenKind::Char('>'), BinaryOperator::Gt),
            ],
        )
    }

    fn parse_binary_op1(&mut self) -> Result<Option<Expression>, ParseError> {
        self.debug_trace("parse_binary_op1");
        self._parse_binary_op(
            Parser::parse_binary_op2,
            &[
                (TokenKind::Char('+'), BinaryOperator::Add),
                (TokenKind::Char('-'), BinaryOperator::Sub),
                (TokenKind::Char('%'), BinaryOperator::Rem),
            ],
        )
    }

    fn parse_binary_op2(&mut self) -> Result<Option<Expression>, ParseError> {
        self.debug_trace("parse_binary_op2");
        self._parse_binary_op(
            Parser::parse_unary_op,
            &[
                (TokenKind::Char('*'), BinaryOperator::Mul),
                (TokenKind::Char('/'), BinaryOperator::Div),
            ],
        )
    }

    fn parse_unary_op(&mut self) -> Result<Option<Expression>, ParseError> {
        self.debug_trace("parse_unary_op");

        let operator = match self.tokenizer.peek_kind() {
            TokenKind::Char('+') => UnaryOperator::Plus,
            TokenKind::Char('-') => UnaryOperator::Minus,
            _ => return self.parse_access(),
        };

        // unary operators are right associative.
        let mut tokens = SyntaxTokensBuffer::with_interpreted(self.tokenizer.next_token());
        let mut operand = None;

        loop {
            if let Some(node) = self.parse_unary_op()? {
                operand = Some(node);
                tokens.child();
                break;
            } else {
                // If we couldn't parse the right hand expression, retry
                // parsing after consuming a token as skipped.
                tokens.skip(self.tokenizer.next_token(), "expression");

                if self.tokenizer.is_at_end() {
                    break;
                }
            }
        }

        // node
        let expr = UnaryExpression {
            operand: operand.map(Box::new),
            operator,
        };

        Ok(Some(Expression {
            kind: ExpressionKind::UnaryExpression(expr),
            r#type: self.new_type_var(),
            tokens,
        }))
    }

    fn parse_access(&mut self) -> Result<Option<Expression>, ParseError> {
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
                    let mut tokens = SyntaxTokensBuffer::with_child();
                    let arguments = self.read_arguments(']', &mut tokens)?;

                    let expr = SubscriptExpression {
                        callee: Box::new(operand),
                        arguments,
                    };

                    operand = Expression {
                        kind: ExpressionKind::SubscriptExpression(expr),
                        r#type: self.new_type_var(),
                        tokens,
                    };
                }
                TokenKind::Char('(') => {
                    let mut tokens = SyntaxTokensBuffer::with_child();
                    let arguments = self.read_arguments(')', &mut tokens)?;

                    let expr = CallExpression {
                        callee: Box::new(operand),
                        arguments,
                    };

                    operand = Expression {
                        kind: ExpressionKind::CallExpression(expr),
                        r#type: self.new_type_var(),
                        tokens,
                    };
                }
                _ => break,
            }
        }

        Ok(Some(operand))
    }

    fn parse_primary(&mut self) -> Option<Expression> {
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
    fn read_integer(&mut self) -> Expression {
        let token = self.tokenizer.next_token();

        if let TokenKind::Integer(i) = token.kind {
            let literal = IntegerLiteral(i);
            let tokens = SyntaxTokensBuffer::with_interpreted(token);

            Expression {
                kind: ExpressionKind::IntegerLiteral(literal),
                r#type: wrap(sem::Type::Int32),
                tokens,
            }
        } else {
            unreachable!()
        }
    }

    fn read_identifier(&mut self) -> Expression {
        let token = self.tokenizer.next_token();

        if let TokenKind::Identifier(ref id) = token.kind {
            let id = Identifier(id.clone());
            let tokens = SyntaxTokensBuffer::with_interpreted(token);

            Expression {
                kind: ExpressionKind::Identifier(id),
                r#type: self.new_type_var(),
                tokens,
            }
        } else {
            unreachable!()
        }
    }

    fn read_string(&mut self) -> Expression {
        let start_token = self.tokenizer.next_token(); // StringStart
        let mut tokens = SyntaxTokensBuffer::with_interpreted(start_token);
        let mut string = String::new();
        let mut has_error = false;

        loop {
            let token = self.tokenizer.next_token();

            match token.kind {
                TokenKind::StringContent(ref s) => {
                    if !has_error {
                        string.push_str(s);
                    }
                    tokens.interpret(token);
                }
                TokenKind::StringEnd => {
                    tokens.interpret(token);
                    break;
                }
                TokenKind::UnrecognizedEscapeSequence(_) => {
                    tokens.skip(token, "ESCAPE SEQUENCE");
                    has_error = true;
                }
                _ => {
                    let missed = self.tokenizer.build_missing(TokenKind::StringEnd, "\"");
                    tokens.missing(missed);
                    has_error = true;
                    break;
                }
            }
        }

        let literal = if has_error {
            StringLiteral(None)
        } else {
            StringLiteral(Some(string))
        };

        Expression {
            kind: ExpressionKind::StringLiteral(literal),
            r#type: wrap(sem::Type::String),
            tokens,
        }
    }

    fn read_arguments(
        &mut self,
        close_char: char,
        tokens: &mut SyntaxTokensBuffer,
    ) -> Result<Vec<Expression>, ParseError> {
        tokens.interpret(self.tokenizer.next_token());

        let mut arguments = vec![];
        let mut argument_read = true;

        loop {
            if argument_read {
                let argument = self.parse_expr()?;

                if let Some(argument) = argument {
                    argument_read = true;
                    arguments.push(argument);
                    tokens.child();
                } else {
                    argument_read = false;
                }
            }

            match self.tokenizer.peek_kind() {
                TokenKind::Char(c) if *c == close_char => {
                    // arguments closed
                    tokens.interpret(self.tokenizer.next_token());
                    break;
                }
                TokenKind::Char(',') => {
                    let t = self.tokenizer.next_token();

                    if !argument_read {
                        // Missing argument, so skip token.
                        tokens.skip(t, "expression");
                        argument_read = true;
                    } else {
                        tokens.interpret(t);
                    }
                }
                _ => {
                    // Premature EOF or unknown token.
                    tokens.missing(self.tokenizer.build_missing(TokenKind::Char(']'), "]"));
                    break;
                }
            }
        }

        Ok(arguments)
    }

    fn _parse_binary_op(
        &mut self,
        next_parser: fn(&mut Parser<'a>) -> Result<Option<Expression>, ParseError>,
        operators: &[(TokenKind, BinaryOperator)],
    ) -> Result<Option<Expression>, ParseError> {
        let lhs = next_parser(self)?;
        let mut lhs = if let Some(lhs) = lhs {
            lhs
        } else {
            return Ok(None);
        };

        loop {
            let kind = self.tokenizer.peek_kind();
            let operator = operators
                .iter()
                .find(|(op, _)| op == kind)
                .map(|(_, operator)| operator);

            if operator.is_none() {
                break;
            }

            let operator = *operator.unwrap();

            // A newline character terminates node construction.
            if self.tokenizer.is_newline_seen() {
                break;
            }

            let op_token = self.tokenizer.next_token();
            let mut rhs;
            let mut tokens = SyntaxTokensBuffer::new();

            tokens.child().interpret(op_token);

            loop {
                rhs = next_parser(self)?.map(Box::new);

                if rhs.is_some() {
                    tokens.child();
                    break;
                } else {
                    // If we couldn't parse the right hand expression, retry
                    // parsing after consuming a token as skipped.
                    let t = self.tokenizer.next_token();
                    tokens.skip(t, "expression");

                    if self.tokenizer.is_at_end() {
                        break;
                    }
                }
            }

            // node
            let expr = BinaryExpression {
                lhs: Box::new(lhs),
                rhs,
                operator,
            };

            lhs = Expression {
                kind: ExpressionKind::BinaryExpression(expr),
                tokens,
                r#type: self.new_type_var(),
            };
        }

        Ok(Some(lhs))
    }

    // --- Helpers
    fn match_token(&mut self, kind: TokenKind) -> bool {
        *self.tokenizer.peek_kind() == kind
    }

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
    use super::*;
    use crate::syntax::{ExpressionKind, Statement, SyntaxToken, Token, TopLevelKind};
    use assert_matches::assert_matches;

    #[test]
    fn number_integer() {
        let module = Parser::parse_string("42").unwrap();
        assert!(!module.body.is_empty());
        assert_eq!(module.body.len(), 1);

        let stmt = unwrap_statement(&module.body[0]);
        assert_matches!(
            stmt.expression.kind,
            ExpressionKind::IntegerLiteral(IntegerLiteral(42))
        );

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
        assert!(!module.body.is_empty());
        assert_eq!(module.body.len(), 1);

        let stmt = unwrap_statement(&module.body[0]);
        let expr = stmt.expression.unwrap_binary_expression();

        assert_matches!(expr, BinaryExpression { operator: BinaryOperator::Add, lhs, rhs: Some(rhs) } => {
            assert_matches!(lhs.kind, ExpressionKind::IntegerLiteral(IntegerLiteral(1)));
            assert_matches!(rhs.kind, ExpressionKind::IntegerLiteral(IntegerLiteral(2)));
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
        assert!(!module.body.is_empty());
        assert_eq!(module.body.len(), 1);

        let stmt = unwrap_statement(&module.body[0]);
        let expr = stmt.expression.unwrap_binary_expression();

        assert_matches!(expr, BinaryExpression { operator: BinaryOperator::Add, lhs, rhs: None } => {
            assert_matches!(lhs.kind, ExpressionKind::IntegerLiteral(IntegerLiteral(1)));
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
        assert!(!module.body.is_empty());
        assert_eq!(module.body.len(), 1);

        let stmt = unwrap_statement(&module.body[0]);
        let expr = stmt.expression.unwrap_binary_expression();

        assert_matches!(expr, BinaryExpression { operator: BinaryOperator::Add, lhs, rhs: Some(rhs) } => {
            assert_matches!(lhs.kind, ExpressionKind::IntegerLiteral(IntegerLiteral(1)));
            assert_matches!(rhs.kind, ExpressionKind::IntegerLiteral(IntegerLiteral(2)));
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
        assert!(!module.body.is_empty());
        assert_eq!(module.body.len(), 1);

        let stmt = unwrap_statement(&module.body[0]);
        let expr = stmt.expression.unwrap_unary_expression();

        assert_matches!(expr, UnaryExpression { operator: UnaryOperator::Minus, operand: Some(operand) } => {
            assert_matches!(operand.kind, ExpressionKind::IntegerLiteral(IntegerLiteral(1)));
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
        assert!(!module.body.is_empty());
        assert_eq!(module.body.len(), 1);

        let stmt = unwrap_statement(&module.body[0]);
        let expr = stmt.expression.unwrap_unary_expression();

        assert_matches!(expr, UnaryExpression { operator: UnaryOperator::Minus, operand: Some(operand) } => {
            let operand = operand.unwrap_unary_expression();

            assert_matches!(operand, UnaryExpression { operator: UnaryOperator::Plus, operand: Some(operand) } => {
                assert_matches!(operand.kind, ExpressionKind::IntegerLiteral(IntegerLiteral(1)));
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
        assert!(!module.body.is_empty());
        assert_eq!(module.body.len(), 1);

        let stmt = unwrap_statement(&module.body[0]);
        let expr = stmt.expression.unwrap_subscript_expression();

        assert_matches!(expr, SubscriptExpression{ callee, arguments } => {
            let id = callee.unwrap_identifier();
            assert_matches!(id, Identifier(id) => {
                assert_eq!(id, "a");
            });
            assert_eq!(arguments.len(), 1);
            assert_matches!(arguments[0].kind, ExpressionKind::IntegerLiteral(IntegerLiteral(0)));
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
    fn subscript_empty() {
        let module = Parser::parse_string("a[]").unwrap();
        assert!(!module.body.is_empty());
        assert_eq!(module.body.len(), 1);

        let stmt = unwrap_statement(&module.body[0]);
        let expr = stmt.expression.unwrap_subscript_expression();

        assert_matches!(expr, SubscriptExpression{ callee, arguments } => {
            let id = callee.unwrap_identifier();
            assert_matches!(id, Identifier(id) => {
                assert_eq!(id, "a");
            });
            assert_eq!(arguments.len(), 0);
        });

        let tokens = stmt.tokens().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 3);

        let token = unwrap_interpreted_token(tokens[0]);
        assert_matches!(&token.kind, TokenKind::Identifier(id) => {
            assert_eq!(id, "a");
        });

        let token = unwrap_interpreted_token(tokens[1]);
        assert_matches!(token.kind, TokenKind::Char('['));

        let token = unwrap_interpreted_token(tokens[2]);
        assert_matches!(token.kind, TokenKind::Char(']'));
    }

    #[test]
    fn subscript_not_closed() {
        let module = Parser::parse_string("a[1\nb").unwrap();
        assert_eq!(module.body.len(), 2);

        // subscript
        let stmt = unwrap_statement(&module.body[0]);
        let expr = stmt.expression.unwrap_subscript_expression();

        assert_matches!(expr, SubscriptExpression{ callee, arguments } => {
            let id = callee.unwrap_identifier();
            assert_matches!(id, Identifier(id) => {
                assert_eq!(id, "a");
            });
            assert_eq!(arguments.len(), 1);
            assert_matches!(arguments[0].kind, ExpressionKind::IntegerLiteral(IntegerLiteral(1)));
        });

        let tokens = stmt.tokens().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 4);

        let token = unwrap_missing_token(tokens[3]);
        assert_matches!(token.kind, TokenKind::Char(']'));
    }

    // --- helpers

    fn unwrap_statement(node: &TopLevelKind) -> &Statement {
        if let TopLevelKind::Statement(node) = node {
            node
        } else {
            panic!("expected statement")
        }
    }

    fn unwrap_interpreted_token(token: &SyntaxToken) -> &Token {
        if let SyntaxToken::Interpreted(token) = token {
            token
        } else {
            panic!("expected interpreted token")
        }
    }

    fn unwrap_missing_token(token: &SyntaxToken) -> &Token {
        if let SyntaxToken::Missing(token) = token {
            token
        } else {
            panic!("expected missing token")
        }
    }

    fn unwrap_skipped_token(token: &SyntaxToken) -> (&Token, String) {
        if let SyntaxToken::Skipped { token, expected } = token {
            (token, expected.clone())
        } else {
            panic!("expected skipped token")
        }
    }
}
