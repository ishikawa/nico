use super::*;
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
    pub fn parse_string<S: AsRef<str>>(src: S) -> Node {
        let tokenizer = Tokenizer::from_string(&src);
        let mut parser = Parser::new(tokenizer, "-");

        parser.parse()
    }

    pub fn parse(&mut self) -> Node {
        let mut body = vec![];
        let mut code = Code::new();

        loop {
            // Type declaration
            if let Some(node) = self.parse_struct_definition() {
                code.node(&node);
                body.push(node);
            }
            // Function
            else if let Some(node) = self.parse_function() {
                code.node(&node);
                body.push(node);
            }
            // Body for main function
            else if let Some(node) = self.parse_stmt() {
                code.node(&node);
                body.push(node);
            }
            // No top level constructs can be consumed. It may be at the end of input or
            // parse error.
            else {
                let token = self.tokenizer.peek();

                match &token.kind {
                    TokenKind::Eos => break,
                    _ => {
                        let token = self.tokenizer.next_token();
                        code.skip(token, MissingTokenKind::TopLevel);
                    }
                }
            }
        }

        Node::new(NodeKind::Program(Program::new(body)), code)
    }

    fn parse_struct_definition(&mut self) -> Option<Rc<Node>> {
        self.debug_trace("parse_struct_definition");
        None
    }

    fn parse_function(&mut self) -> Option<Rc<Node>> {
        self.debug_trace("parse_function");

        let mut code = Code::new();

        // TODO: In L(1) parser, if the `fun` keyword is not followed by an `export` keyword,
        // the `export` keyword cannot be push backed, so we shouldn't stop reading export here.
        let export = self.match_token(TokenKind::Export);

        if export {
            code.interpret(self.tokenizer.next_token());
        }

        // fun
        if !self.match_token(TokenKind::Fun) {
            return None;
        }

        code.interpret(self.tokenizer.next_token());

        // name
        let mut function_name = None;

        loop {
            match self.tokenizer.peek_kind() {
                TokenKind::Identifier(_) => {
                    // Okay, it's a function name.
                    let name = self.parse_name().unwrap();

                    code.node(&name);
                    function_name = Some(name);

                    break;
                }
                TokenKind::Char('(') | TokenKind::Eos => {
                    // Umm, maybe user forgot/omitted a function name?
                    // I'm sorry, but this language is not JavaScript.
                    code.missing(
                        self.tokenizer.current_insertion_range(),
                        MissingTokenKind::FunctionName,
                    );
                    break;
                }
                _ => {
                    // Continue until read identifier or over.
                    code.skip(self.tokenizer.next_token(), MissingTokenKind::FunctionName);
                }
            }
        }

        // parameters
        let parameters =
            self._parse_elements('(', ')', &mut code, Parser::parse_function_parameter);

        // body
        let body = Rc::new(self._read_block(&[TokenKind::End]));

        code.node(&body);
        code.interpret(self.tokenizer.next_token()); // end

        Some(Rc::new(Node::new(
            NodeKind::FunctionDefinition(FunctionDefinition::new(function_name, parameters, body)),
            code,
        )))
    }

    fn parse_function_parameter(&mut self) -> Option<Rc<Node>> {
        if let Some(name) = self.parse_name() {
            let code = Code::with_node(&name);
            let node = Node::new(
                NodeKind::FunctionParameter(FunctionParameter::new(name)),
                code,
            );

            Some(Rc::new(node))
        } else {
            None
        }
    }

    fn parse_name(&mut self) -> Option<Rc<Node>> {
        if let TokenKind::Identifier(name) = self.tokenizer.peek_kind() {
            let name = name.clone();
            let code = Code::with_interpreted(self.tokenizer.next_token());
            let node = Node::new(NodeKind::Identifier(Identifier::new(name)), code);

            Some(Rc::new(node))
        } else {
            None
        }
    }

    fn parse_stmt(&mut self) -> Option<Rc<Node>> {
        self.debug_trace("parse_stmt");

        match self.tokenizer.peek_kind() {
            TokenKind::Let => {
                self.tokenizer.next_token();
            }
            _ => return self.parse_stmt_expr(),
        };

        // TODO: Variable binding
        None
    }

    fn parse_stmt_expr(&mut self) -> Option<Rc<Node>> {
        self.debug_trace("parse_stmt_expr");

        if let Some(expr) = self.parse_expr() {
            let code = Code::with_node(&expr);

            Some(Rc::new(Node::new(
                NodeKind::Statement(Statement::new(expr)),
                code,
            )))
        } else {
            None
        }
    }

    fn parse_expr(&mut self) -> Option<Rc<Node>> {
        self.debug_trace("parse_expr");
        self.parse_rel_op1()
    }

    fn parse_rel_op1(&mut self) -> Option<Rc<Node>> {
        self.debug_trace("parse_rel_op1");
        self._parse_binary_op(
            Parser::parse_rel_op2,
            &[
                (TokenKind::Eq, BinaryOperator::Eq),
                (TokenKind::Ne, BinaryOperator::Ne),
            ],
        )
    }

    fn parse_rel_op2(&mut self) -> Option<Rc<Node>> {
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

    fn parse_binary_op1(&mut self) -> Option<Rc<Node>> {
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

    fn parse_binary_op2(&mut self) -> Option<Rc<Node>> {
        self.debug_trace("parse_binary_op2");
        self._parse_binary_op(
            Parser::parse_unary_op,
            &[
                (TokenKind::Char('*'), BinaryOperator::Mul),
                (TokenKind::Char('/'), BinaryOperator::Div),
            ],
        )
    }

    fn parse_unary_op(&mut self) -> Option<Rc<Node>> {
        self.debug_trace("parse_unary_op");

        let operator = match self.tokenizer.peek_kind() {
            TokenKind::Char('+') => UnaryOperator::Plus,
            TokenKind::Char('-') => UnaryOperator::Minus,
            _ => return self.parse_access(),
        };

        // unary operators are right associative.
        let mut code = Code::with_interpreted(self.tokenizer.next_token());
        let mut operand = None;

        loop {
            if let Some(node) = self.parse_unary_op() {
                code.node(&node);
                operand = Some(node);
                break;
            } else {
                // If we couldn't parse the right hand expression, retry
                // parsing after consuming a token as skipped.
                code.skip(self.tokenizer.next_token(), MissingTokenKind::Expression);

                if self.tokenizer.is_at_end() {
                    break;
                }
            }
        }

        // node
        let expr = UnaryExpression { operand, operator };
        let kind = ExpressionKind::UnaryExpression(expr);

        Some(Rc::new(Node::new(
            NodeKind::Expression(Expression::new(kind, self.new_type_var())),
            code,
        )))
    }

    fn parse_access(&mut self) -> Option<Rc<Node>> {
        self.debug_trace("parse_access");

        let mut operand = self.parse_primary()?;

        loop {
            let mut code = Code::with_node(&operand);

            // To distinguish `x\n[...]` and `x[...]`, we have to capture
            // `tokenizer.is_newline_seen()`, so try to advance tokenizer.
            self.tokenizer.peek();

            if self.tokenizer.is_newline_seen() {
                break;
            }

            let token = self.tokenizer.peek();

            match token.kind {
                TokenKind::Char('[') => {
                    let arguments = self._parse_elements('[', ']', &mut code, Parser::parse_expr);
                    let expr = SubscriptExpression::new(operand, arguments);

                    operand = Rc::new(Node::new(
                        NodeKind::Expression(Expression::new(
                            ExpressionKind::SubscriptExpression(expr),
                            self.new_type_var(),
                        )),
                        code,
                    ));
                }
                TokenKind::Char('(') => {
                    let arguments = self._parse_elements('(', ')', &mut code, Parser::parse_expr);

                    let expr = CallExpression::new(operand, arguments);

                    operand = Rc::new(Node::new(
                        NodeKind::Expression(Expression::new(
                            ExpressionKind::CallExpression(expr),
                            self.new_type_var(),
                        )),
                        code,
                    ));
                }
                _ => break,
            }
        }

        Some(operand)
    }

    fn parse_primary(&mut self) -> Option<Rc<Node>> {
        self.debug_trace("parse_primary");

        let token = self.tokenizer.peek();
        let node = match token.kind {
            TokenKind::Integer(_) => self.read_integer(),
            TokenKind::Identifier(_) => self.read_identifier(),
            TokenKind::StringStart => self.read_string(),
            TokenKind::Char('(') => self.read_paren(),
            TokenKind::Char('[') => self.read_array(),
            TokenKind::If => self.read_if_expression(),
            _ => return None,
        };

        Some(Rc::new(node))
    }

    fn read_integer(&mut self) -> Node {
        let token = self.tokenizer.next_token();

        if let TokenKind::Integer(i) = token.kind {
            let literal = IntegerLiteral(i);
            let code = Code::with_interpreted(token);

            Node::new(
                NodeKind::Expression(Expression::new(
                    ExpressionKind::IntegerLiteral(literal),
                    wrap(sem::Type::Int32),
                )),
                code,
            )
        } else {
            unreachable!()
        }
    }

    fn read_identifier(&mut self) -> Node {
        let token = self.tokenizer.next_token();

        if let TokenKind::Identifier(ref id) = token.kind {
            let id = Identifier::new(id.clone());
            let code = Code::with_interpreted(token);

            Node::new(
                NodeKind::Expression(Expression::new(
                    ExpressionKind::VariableExpression(id),
                    self.new_type_var(),
                )),
                code,
            )
        } else {
            unreachable!()
        }
    }

    fn read_string(&mut self) -> Node {
        let start_token = self.tokenizer.next_token(); // StringStart
        let mut code = Code::with_interpreted(start_token);
        let mut string = String::new();
        let mut has_error = false;

        loop {
            match self.tokenizer.peek_kind() {
                TokenKind::StringContent(s) => {
                    if !has_error {
                        string.push_str(s);
                    }
                    code.interpret(self.tokenizer.next_token());
                }
                TokenKind::StringEscapeSequence(c) => {
                    if !has_error {
                        string.push(*c);
                    }
                    code.interpret(self.tokenizer.next_token());
                }
                TokenKind::StringEnd => {
                    code.interpret(self.tokenizer.next_token());
                    break;
                }
                TokenKind::StringUnrecognizedEscapeSequence(_) => {
                    code.skip(
                        self.tokenizer.next_token(),
                        MissingTokenKind::EscapeSequence,
                    );
                    has_error = true;
                }
                _ => {
                    code.missing(
                        self.tokenizer.current_insertion_range(),
                        MissingTokenKind::StringEnd,
                    );
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

        Node::new(
            NodeKind::Expression(Expression::new(
                ExpressionKind::StringLiteral(literal),
                wrap(sem::Type::String),
            )),
            code,
        )
    }

    fn read_paren(&mut self) -> Node {
        let mut code = Code::with_interpreted(self.tokenizer.next_token()); // "("
        let node = self.parse_expr();

        if let Some(ref node) = node {
            code.node(node);
        }

        loop {
            match self.tokenizer.peek_kind() {
                TokenKind::Char(')') => {
                    code.interpret(self.tokenizer.next_token());
                    break;
                }
                TokenKind::Eos | TokenKind::Char('\n') => {
                    code.missing(
                        self.tokenizer.current_insertion_range(),
                        MissingTokenKind::Char(')'),
                    );
                    break;
                }
                _ => {
                    code.skip(self.tokenizer.next_token(), MissingTokenKind::Char(')'));
                }
            }
        }

        if let Some(ref node) = node {
            let expr = node.expression().unwrap();

            // Because parentheses which groups an expression is not part of
            // AST, we have to incorporate it into another node.
            Node::new(
                NodeKind::Expression(Expression::new(
                    ExpressionKind::Expression(Rc::clone(&node)),
                    Rc::clone(&expr.r#type),
                )),
                code,
            )
        } else {
            Node::new(NodeKind::Unit, code)
        }
    }

    fn read_array(&mut self) -> Node {
        let mut code = Code::new();
        let elements = self._parse_elements('[', ']', &mut code, Parser::parse_expr);

        let expr = ArrayExpression::new(elements);

        Node::new(
            NodeKind::Expression(Expression::new(
                ExpressionKind::ArrayExpression(expr),
                self.new_type_var(),
            )),
            code,
        )
    }

    fn read_if_expression(&mut self) -> Node {
        let mut code = Code::with_interpreted(self.tokenizer.next_token()); // "if"
        let condition = self.parse_expr();

        if let Some(ref node) = condition {
            code.node(node);
        } else {
            // missed condition expression
            code.missing(
                self.tokenizer.current_insertion_range(),
                MissingTokenKind::Expression,
            );
        }

        // body
        let then_body = Rc::new(self._read_block(&[TokenKind::End, TokenKind::Else]));
        let has_else = *self.tokenizer.peek_kind() == TokenKind::Else;

        code.node(&then_body);
        code.interpret(self.tokenizer.next_token()); // "else" or "end"

        let else_body = if has_else {
            let else_body = Rc::new(self._read_block(&[TokenKind::End]));

            code.node(&else_body);
            code.interpret(self.tokenizer.next_token()); //  "end"

            Some(else_body)
        } else {
            None
        };

        let expr = IfExpression::new(condition, then_body, else_body);

        Node::new(
            NodeKind::Expression(Expression::new(
                ExpressionKind::IfExpression(expr),
                self.new_type_var(),
            )),
            code,
        )
    }

    /// Reads statements until it meets a token listed in `stop_tokens`.
    /// But this function doesn't consume a stop token itself, consuming
    /// a stop token is caller's responsibility.
    fn _read_block(&mut self, stop_tokens: &[TokenKind]) -> Node {
        let mut code = Code::new();

        // body
        let mut body = vec![];

        loop {
            if let Some(stmt) = self.parse_stmt() {
                code.node(&stmt);
                body.push(stmt);
            }

            match self.tokenizer.peek_kind() {
                TokenKind::Eos => {
                    // Maybe user forgot `end`.
                    // I'm sorry, but this language is like Ruby not Python.
                    code.missing(
                        self.tokenizer.current_insertion_range(),
                        MissingTokenKind::End,
                    );
                    break;
                }
                token => {
                    if stop_tokens.contains(token) {
                        // Okay, it's done. don't consume a token.
                        break;
                    }

                    // Continue until read identifier or over.
                    code.skip(self.tokenizer.next_token(), MissingTokenKind::End);
                }
            }
        }

        Node::new(NodeKind::Block(Block::new(body)), code)
    }

    /// Read comma-separated elements from the start character token specified by `open_char` to
    /// the end character token or EOF specified by `close_char`.
    fn _parse_elements(
        &mut self,
        open_char: char,
        close_char: char,
        code: &mut Code,
        element_parser: fn(&mut Parser<'a>) -> Option<Rc<Node>>,
    ) -> Vec<Rc<Node>> {
        let mut arguments = vec![];
        let mut consumed = false; // An argument already read.

        // Read an opening token
        loop {
            match self.tokenizer.peek_kind() {
                TokenKind::Char(c) if *c == open_char => {
                    // Beginning of arguments.
                    code.interpret(self.tokenizer.next_token());
                    break;
                }
                TokenKind::Eos => {
                    // Oh, is it over?
                    code.missing(
                        self.tokenizer.current_insertion_range(),
                        MissingTokenKind::Char(open_char),
                    );
                    break;
                }
                TokenKind::Char(c) if *c == close_char => {
                    // Umm, maybe user forgot opening token.
                    //
                    //     # (
                    //     )
                    code.missing(
                        self.tokenizer.current_insertion_range(),
                        MissingTokenKind::Char(open_char),
                    );
                    break;
                }
                _ => {
                    if let Some(expr) = element_parser(self) {
                        // Maybe user forgot opening token before a param.
                        //     # (
                        //         a ...
                        //     )
                        arguments.push(Rc::clone(&expr));
                        consumed = true;

                        code.missing(
                            self.tokenizer.current_insertion_range(),
                            MissingTokenKind::Char(open_char),
                        );
                        code.node(&expr);
                        break;
                    } else {
                        // Continue until read an opening token.
                        code.skip(
                            self.tokenizer.next_token(),
                            MissingTokenKind::Char(open_char),
                        );
                    }
                }
            }
        }

        loop {
            if !consumed {
                let argument = element_parser(self);

                if let Some(argument) = argument {
                    consumed = true;
                    arguments.push(Rc::clone(&argument));
                    code.node(&argument);
                } else {
                    consumed = false;
                }
            }

            match self.tokenizer.peek_kind() {
                TokenKind::Char(c) if *c == close_char => {
                    // arguments closed
                    code.interpret(self.tokenizer.next_token());
                    break;
                }
                TokenKind::Char(',') => {
                    let t = self.tokenizer.next_token();

                    if !consumed {
                        // missing argument, so skip token.
                        code.skip(t, MissingTokenKind::Expression);
                    } else {
                        code.interpret(t);
                    }

                    // clear the flag before iterating the next.
                    consumed = false;
                }
                _ => {
                    // Premature EOF or unknown token.
                    code.missing(
                        self.tokenizer.current_insertion_range(),
                        MissingTokenKind::Char(close_char),
                    );
                    break;
                }
            }
        }

        arguments
    }

    fn _parse_binary_op(
        &mut self,
        next_parser: fn(&mut Parser<'a>) -> Option<Rc<Node>>,
        operators: &[(TokenKind, BinaryOperator)],
    ) -> Option<Rc<Node>> {
        let mut lhs = next_parser(self)?;

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
            let mut code = Code::new();

            code.node(&lhs).interpret(op_token);

            loop {
                rhs = next_parser(self);

                if let Some(ref rhs) = rhs {
                    code.node(rhs);
                    break;
                } else {
                    // If we couldn't parse the right hand expression, retry
                    // parsing after consuming a token as skipped.
                    let t = self.tokenizer.next_token();
                    code.skip(t, MissingTokenKind::Expression);

                    if self.tokenizer.is_at_end() {
                        break;
                    }
                }
            }

            // node
            let expr = BinaryExpression { lhs, rhs, operator };

            lhs = Rc::new(Node::new(
                NodeKind::Expression(Expression::new(
                    ExpressionKind::BinaryExpression(expr),
                    self.new_type_var(),
                )),
                code,
            ));
        }

        Some(lhs)
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
    use crate::syntax::{EffectiveRange, ExpressionKind, SyntaxToken, Token};
    use assert_matches::assert_matches;

    #[test]
    fn number_integer() {
        let stmt = parse_statement("42");
        let stmt = stmt.statement().unwrap();

        assert_matches!(
            stmt.expression().kind,
            ExpressionKind::IntegerLiteral(IntegerLiteral(42))
        );

        let code = stmt.expression.code().collect::<Vec<_>>();
        assert_eq!(code.len(), 1);

        let token = unwrap_interpreted_token(code[0]);
        assert_matches!(token.kind, TokenKind::Integer(i) => {
            assert_eq!(i, 42);
        });
    }

    #[test]
    fn incomplete_string() {
        for src in vec!["\"Fizz\\\"", "\"Fizz\\\"\n"] {
            let stmt = parse_statement(src);
            let stmt = stmt.statement().unwrap();
            let expr = stmt.expression();

            assert_matches!(expr.kind, ExpressionKind::StringLiteral(..));

            let tokens = stmt.expression.code().collect::<Vec<_>>();
            assert_eq!(tokens.len(), 4);

            let token = unwrap_interpreted_token(tokens[0]);
            assert_matches!(token.kind, TokenKind::StringStart);

            let token = unwrap_interpreted_token(tokens[1]);
            assert_matches!(&token.kind, TokenKind::StringContent(s) => {
                assert_eq!(s, "Fizz")
            });

            let token = unwrap_interpreted_token(tokens[2]);
            assert_matches!(token.kind, TokenKind::StringEscapeSequence(c) => {
                assert_eq!(c, '\"')
            });

            let (_, item) = unwrap_missing_token(tokens[3]);
            assert_eq!(item, MissingTokenKind::StringEnd);
        }
    }

    #[test]
    fn incomplete_string_in_paren() {
        for src in vec!["(\"Fizz\\\")", "(\"Fizz\\\")\n"] {
            let stmt = parse_statement(src);
            let stmt = stmt.statement().unwrap();
            let expr = stmt.expression();

            assert_matches!(expr.kind, ExpressionKind::Expression(ref expr) => {
                assert_matches!(expr.expression().unwrap().kind, ExpressionKind::StringLiteral(..));
            });

            let tokens = stmt.expression.code().collect::<Vec<_>>();
            assert_eq!(tokens.len(), 3);

            let token = unwrap_interpreted_token(tokens[0]);
            assert_matches!(token.kind, TokenKind::Char('('));

            let node = unwrap_node(tokens[1]);
            assert_matches!(node.kind(), NodeKind::Expression(..));

            let (_, item) = unwrap_missing_token(tokens[2]);
            assert_eq!(item, MissingTokenKind::Char(')'));
        }
    }

    #[test]
    fn add_integer() {
        let stmt = parse_statement("1+2");
        let stmt = stmt.statement().unwrap();
        let expr = stmt.expression().binary_expression().unwrap();

        assert_matches!(expr, BinaryExpression { operator: BinaryOperator::Add, lhs, rhs: Some(rhs) } => {
            assert_matches!(lhs.expression().unwrap().kind, ExpressionKind::IntegerLiteral(IntegerLiteral(1)));
            assert_matches!(rhs.expression().unwrap().kind, ExpressionKind::IntegerLiteral(IntegerLiteral(2)));
        });

        let tokens = stmt.expression.code().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 3);

        let node = unwrap_node(tokens[0]);
        assert!(node.is_expression());

        let token = unwrap_interpreted_token(tokens[1]);
        assert_matches!(token.kind, TokenKind::Char('+'));

        let node = unwrap_node(tokens[2]);
        assert!(node.is_expression());
    }

    #[test]
    fn add_integer_missing_node() {
        let stmt = parse_statement("1+");
        let stmt = stmt.statement().unwrap();
        let expr = stmt.expression().binary_expression().unwrap();

        assert_matches!(expr, BinaryExpression { operator: BinaryOperator::Add, lhs, rhs: None } => {
            assert_matches!(lhs.expression().unwrap().kind, ExpressionKind::IntegerLiteral(IntegerLiteral(1)));
        });

        let tokens = stmt.expression.code().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 3);

        let node = unwrap_node(tokens[0]);
        assert!(node.is_expression());

        let token = unwrap_interpreted_token(tokens[1]);
        assert_matches!(token.kind, TokenKind::Char('+'));

        let (token, expected) = unwrap_skipped_token(tokens[2]);
        assert_eq!(token.kind, TokenKind::Eos);
        assert_eq!(expected, MissingTokenKind::Expression);
    }

    #[test]
    fn add_integer_skipped_tokens() {
        let stmt = parse_statement("1 + % ? 2");
        let stmt = stmt.statement().unwrap();
        let expr = stmt.expression().binary_expression().unwrap();

        assert_matches!(expr, BinaryExpression { operator: BinaryOperator::Add, lhs, rhs: Some(rhs) } => {
            assert_matches!(lhs.expression().unwrap().kind, ExpressionKind::IntegerLiteral(IntegerLiteral(1)));
            assert_matches!(rhs.expression().unwrap().kind, ExpressionKind::IntegerLiteral(IntegerLiteral(2)));
        });

        let tokens = stmt.expression.code().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 5);

        let node = unwrap_node(tokens[0]);
        assert!(node.is_expression());

        let token = unwrap_interpreted_token(tokens[1]);
        assert_matches!(token.kind, TokenKind::Char('+'));

        let (token, expected) = unwrap_skipped_token(tokens[2]);
        assert_eq!(token.kind, TokenKind::Char('%'));
        assert_eq!(expected, MissingTokenKind::Expression);

        let (token, expected) = unwrap_skipped_token(tokens[3]);
        assert_eq!(token.kind, TokenKind::Char('?'));
        assert_eq!(expected, MissingTokenKind::Expression);

        let node = unwrap_node(tokens[4]);
        assert!(node.is_expression());
    }

    #[test]
    fn unary_op() {
        let stmt = parse_statement("-1");
        let stmt = stmt.statement().unwrap();
        let expr = stmt.expression().unary_expression().unwrap();

        assert_matches!(expr, UnaryExpression { operator: UnaryOperator::Minus, operand: Some(operand) } => {
            assert_matches!(operand.expression().unwrap().kind, ExpressionKind::IntegerLiteral(IntegerLiteral(1)));
        });

        let tokens = stmt.expression.code().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 2);

        let token = unwrap_interpreted_token(tokens[0]);
        assert_matches!(token.kind, TokenKind::Char('-'));

        let node = unwrap_node(tokens[1]);
        assert!(node.is_expression());
    }

    #[test]
    fn unary_op_nested() {
        let stmt = parse_statement("-+1");
        let stmt = stmt.statement().unwrap();
        let expr = stmt.expression().unary_expression().unwrap();

        assert_matches!(expr, UnaryExpression { operator: UnaryOperator::Minus, operand: Some(operand) } => {
            let operand = operand.unary_expression().unwrap();

            assert_matches!(operand, UnaryExpression { operator: UnaryOperator::Plus, operand: Some(operand) } => {
                assert_matches!(operand.expression().unwrap().kind, ExpressionKind::IntegerLiteral(IntegerLiteral(1)));
            });
        });

        let tokens = stmt.expression.code().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 2);

        let token = unwrap_interpreted_token(tokens[0]);
        assert_matches!(token.kind, TokenKind::Char('-'));

        let node = unwrap_node(tokens[1]);
        assert!(node.is_expression());
    }

    #[test]
    fn subscript_index() {
        let stmt = parse_statement("a[0]");
        let stmt = stmt.statement().unwrap();
        let expr = stmt.expression().subscript_expression().unwrap();

        assert_matches!(expr, SubscriptExpression{ .. } => {
            let id = expr.callee().variable_expression();
            assert!(id.is_some());

            let id = id.unwrap();
            assert_eq!(id.to_string(), "a");

            let arguments = expr.arguments().collect::<Vec<_>>();
            assert_eq!(arguments.len(), 1);
            assert_matches!(arguments[0].kind, ExpressionKind::IntegerLiteral(IntegerLiteral(0)));
        });

        let tokens = stmt.expression.code().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 4);

        let node = unwrap_node(tokens[0]);
        assert!(node.is_expression());

        let token = unwrap_interpreted_token(tokens[1]);
        assert_matches!(token.kind, TokenKind::Char('['));

        let node = unwrap_node(tokens[2]);
        assert!(node.is_expression());

        let token = unwrap_interpreted_token(tokens[3]);
        assert_matches!(token.kind, TokenKind::Char(']'));
    }

    #[test]
    fn subscript_empty() {
        let stmt = parse_statement("a[]");
        let stmt = stmt.statement().unwrap();
        let expr = stmt.expression().subscript_expression().unwrap();

        assert_matches!(expr, SubscriptExpression{ .. } => {
            let id = expr.callee().variable_expression();
            assert!(id.is_some());

            let id = id.unwrap();
            assert_eq!(id.to_string(), "a");

            let arguments = expr.arguments().collect::<Vec<_>>();
            assert_eq!(arguments.len(), 0);
        });

        let tokens = stmt.expression.code().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 3);

        let node = unwrap_node(tokens[0]);
        assert!(node.is_expression());

        let token = unwrap_interpreted_token(tokens[1]);
        assert_matches!(token.kind, TokenKind::Char('['));

        let token = unwrap_interpreted_token(tokens[2]);
        assert_matches!(token.kind, TokenKind::Char(']'));
    }

    #[test]
    fn subscript_not_closed() {
        let stmt = parse_statement("a[1\nb");
        let stmt = stmt.statement().unwrap();
        let expr = stmt.expression().subscript_expression().unwrap();

        assert_matches!(expr, SubscriptExpression{ .. } => {
            let id = expr.callee().variable_expression();
            assert!(id.is_some());

            let id = id.unwrap();
            assert_eq!(id.to_string(), "a");

            let arguments = expr.arguments().collect::<Vec<_>>();
            assert_eq!(arguments.len(), 1);
            assert_matches!(arguments[0].kind, ExpressionKind::IntegerLiteral(IntegerLiteral(1)));
        });

        let tokens = stmt.expression.code().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 4);

        let (range, item) = unwrap_missing_token(tokens[3]);
        assert_eq!(item, MissingTokenKind::Char(']'));
        assert_eq!(range.start.line, 0);
        assert_eq!(range.start.character, 2);
        assert_eq!(range.length, 1);
    }

    #[test]
    fn subscript_incomplete_string() {
        for src in vec!["a[\"", "a[\"\n"] {
            let stmt = parse_statement(src);
            let stmt = stmt.statement().unwrap();
            let expr = stmt.expression().subscript_expression().unwrap();

            assert_matches!(expr, SubscriptExpression{ .. } => {
                let arguments = expr.arguments().collect::<Vec<_>>();
                assert_eq!(arguments.len(), 1);
                assert_matches!(arguments[0].kind, ExpressionKind::StringLiteral(..));
            });

            let tokens = stmt.expression.code().collect::<Vec<_>>();
            assert_eq!(tokens.len(), 4);

            let (range, item) = unwrap_missing_token(tokens[3]);
            assert_eq!(item, MissingTokenKind::Char(']'));
            assert_eq!(range.start.line, 0);
            assert_eq!(range.start.character, 2);
            assert_eq!(range.length, 1);
        }
    }

    #[test]
    fn array_empty() {
        let stmt = parse_statement("[]");
        let stmt = stmt.statement().unwrap();
        let expr = stmt.expression().array_expression().unwrap();

        assert_matches!(expr, ArrayExpression{ .. } => {
            let elements = expr.elements().collect::<Vec<_>>();
            assert_eq!(elements.len(), 0);
        });

        let tokens = stmt.expression.code().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 2);

        let token = unwrap_interpreted_token(tokens[0]);
        assert_matches!(token.kind, TokenKind::Char('['));

        let token = unwrap_interpreted_token(tokens[1]);
        assert_matches!(token.kind, TokenKind::Char(']'));
    }

    #[test]
    fn array_one_element_and_trailing_comma() {
        let stmt = parse_statement("[1,]");
        let stmt = stmt.statement().unwrap();
        let expr = stmt.expression().array_expression().unwrap();

        assert_matches!(expr, ArrayExpression{ .. } => {
            let elements = expr.elements().collect::<Vec<_>>();
            assert_eq!(elements.len(), 1);

            assert_eq!(elements.len(), 1);
            assert_matches!(elements[0].kind, ExpressionKind::IntegerLiteral(IntegerLiteral(1)));
        });

        let tokens = stmt.expression.code().collect::<Vec<_>>();
        assert_eq!(tokens.len(), 4);

        let token = unwrap_interpreted_token(tokens[0]);
        assert_matches!(token.kind, TokenKind::Char('['));

        let node = unwrap_node(tokens[1]);
        assert!(node.is_expression());

        let token = unwrap_interpreted_token(tokens[2]);
        assert_matches!(token.kind, TokenKind::Char(','));

        let token = unwrap_interpreted_token(tokens[3]);
        assert_matches!(token.kind, TokenKind::Char(']'));
    }

    // --- helpers

    fn parse_statement(src: &str) -> Rc<Node> {
        let module = Parser::parse_string(src);
        let module = module.program().unwrap();

        assert!(!module.body.is_empty());
        Rc::clone(&module.body[0])
    }

    fn unwrap_node(kind: &CodeKind) -> &Node {
        if let CodeKind::Node(node) = kind {
            return node;
        }

        panic!("expected child node");
    }

    fn unwrap_interpreted_token(kind: &CodeKind) -> &Token {
        if let CodeKind::SyntaxToken(token) = kind {
            if let SyntaxToken::Interpreted(token) = token {
                return token;
            }
        }

        panic!("expected interpreted token");
    }

    fn unwrap_missing_token(kind: &CodeKind) -> (EffectiveRange, MissingTokenKind) {
        if let CodeKind::SyntaxToken(token) = kind {
            if let SyntaxToken::Missing { range, item } = token {
                return (range.clone(), item.clone());
            }
        }

        panic!("expected missing token");
    }

    fn unwrap_skipped_token(kind: &CodeKind) -> (&Token, MissingTokenKind) {
        if let CodeKind::SyntaxToken(token) = kind {
            if let SyntaxToken::Skipped { token, expected } = token {
                return (token, *expected);
            }
        }

        panic!("expected missing token");
    }
}
