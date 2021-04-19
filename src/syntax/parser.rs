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

    fn parse_unary_op(&mut self) -> Option<Expression> {
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
        let expr = UnaryExpression::new(operator, operand);
        let kind = ExpressionKind::UnaryExpression(expr);

        Some(Expression::new(kind, code, self.new_type_var()))
    }

    fn parse_access(&mut self) -> Option<Expression> {
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

                    operand = Expression::new(
                        ExpressionKind::SubscriptExpression(expr),
                        code,
                        self.new_type_var(),
                    );
                }
                TokenKind::Char('(') => {
                    let arguments = self._parse_elements('(', ')', &mut code, Parser::parse_expr);

                    let expr = CallExpression::new(operand, arguments);

                    operand = Expression::new(
                        ExpressionKind::CallExpression(expr),
                        code,
                        self.new_type_var(),
                    );
                }
                _ => break,
            }
        }

        Some(operand)
    }

    fn parse_primary(&mut self) -> Option<Expression> {
        self.debug_trace("parse_primary");

        let token = self.tokenizer.peek();
        let node = match token.kind {
            TokenKind::Integer(_) => self.read_integer(false),
            TokenKind::Identifier(_) => self.read_identifier(false),
            TokenKind::StringStart => self.read_string(false),
            TokenKind::Char('(') => self.read_paren(),
            TokenKind::Char('[') => self.read_array(),
            TokenKind::If => self.read_if_expression(),
            TokenKind::Case => self.read_case_expression(),
            _ => return None,
        };

        Some(Rc::new(node))
    }

    fn parse_pattern(&mut self) -> Option<Rc<Node>> {
        self.debug_trace("parse_pattern");

        let token = self.tokenizer.peek();
        let node = match token.kind {
            TokenKind::Integer(_) => self.read_integer(true),
            TokenKind::Identifier(_) => self.read_identifier(true),
            TokenKind::StringStart => self.read_string(true),
            TokenKind::Char('[') => self.read_array_pattern(),
            _ => return None,
        };

        Some(Rc::new(node))
    }

    fn read_integer(&mut self, as_pattern: bool) -> Node {
        let token = self.tokenizer.next_token();

        if let TokenKind::Integer(i) = token.kind {
            let literal = IntegerLiteral::new(i);
            let code = Code::with_interpreted(token);
            let kind = if as_pattern {
                NodeKind::Pattern(Pattern::new(PatternKind::IntegerPattern(literal)))
            } else {
                NodeKind::Expression(Expression::new(
                    ExpressionKind::IntegerLiteral(literal),
                    wrap(sem::Type::Int32),
                ))
            };

            Node::new(kind, code)
        } else {
            unreachable!()
        }
    }

    fn read_identifier(&mut self, as_pattern: bool) -> Node {
        let token = self.tokenizer.next_token();

        if let TokenKind::Identifier(ref id) = token.kind {
            let id = Identifier::new(id.clone());
            let code = Code::with_interpreted(token);
            let kind = if as_pattern {
                NodeKind::Pattern(Pattern::new(PatternKind::VariablePattern(id)))
            } else {
                NodeKind::Expression(Expression::new(
                    ExpressionKind::VariableExpression(id),
                    self.new_type_var(),
                ))
            };

            Node::new(kind, code)
        } else {
            unreachable!()
        }
    }

    fn read_string(&mut self, as_pattern: bool) -> Node {
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
            StringLiteral::new(None)
        } else {
            StringLiteral::new(Some(string))
        };

        let kind = if as_pattern {
            NodeKind::Pattern(Pattern::new(PatternKind::StringPattern(literal)))
        } else {
            NodeKind::Expression(Expression::new(
                ExpressionKind::StringLiteral(literal),
                wrap(sem::Type::String),
            ))
        };

        Node::new(kind, code)
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
                    Rc::clone(expr.r#type()),
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

    fn read_array_pattern(&mut self) -> Node {
        let mut code = Code::new();
        let elements = self._parse_elements('[', ']', &mut code, Parser::parse_pattern);

        let expr = ArrayPattern::new(elements);

        Node::new(
            NodeKind::Pattern(Pattern::new(PatternKind::ArrayPattern(expr))),
            code,
        )
    }

    fn read_if_expression(&mut self) -> Node {
        let mut code = Code::with_interpreted(self.tokenizer.next_token()); // "if"
        let condition =
            self._parse_optional_item(&mut code, Parser::parse_expr, MissingTokenKind::Expression);

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

    fn read_case_expression(&mut self) -> Node {
        // case ...
        let mut code = Code::with_interpreted(self.tokenizer.next_token()); // "case"
        let head =
            self._parse_optional_item(&mut code, Parser::parse_expr, MissingTokenKind::Expression);

        // arms
        let mut arms = vec![];
        let mut else_body = None;

        loop {
            match self.tokenizer.peek_kind() {
                TokenKind::When => {
                    // when
                    code.interpret(self.tokenizer.next_token());

                    // To avoid syntactic ambiguity, no newline can be placed after `when` keyword.
                    self.tokenizer.peek();
                    let pattern = if self.tokenizer.is_newline_seen() {
                        code.missing(
                            self.tokenizer.current_insertion_range(),
                            MissingTokenKind::Pattern,
                        );
                        None
                    } else {
                        self._parse_optional_item(
                            &mut code,
                            Parser::parse_pattern,
                            MissingTokenKind::Pattern,
                        )
                    };

                    // guard
                    let mut guard = None;

                    if *self.tokenizer.peek_kind() == TokenKind::If {
                        code.interpret(self.tokenizer.next_token());
                        guard = self._parse_optional_item(
                            &mut code,
                            Parser::parse_expr,
                            MissingTokenKind::Expression,
                        );
                    }

                    let then_body = Rc::new(self._read_block(&[
                        TokenKind::When,
                        TokenKind::Else,
                        TokenKind::End,
                    ]));
                    code.node(&then_body);
                    arms.push(CaseArm::new(pattern, guard, then_body))
                }
                TokenKind::Else => {
                    code.interpret(self.tokenizer.next_token());

                    let block = Rc::new(self._read_block(&[TokenKind::End]));
                    code.node(&block);

                    else_body = Some(block);
                }
                TokenKind::End => {
                    code.interpret(self.tokenizer.next_token());
                    break;
                }
                TokenKind::Eos => {
                    // Premature EOS
                    code.missing(
                        self.tokenizer.current_insertion_range(),
                        MissingTokenKind::End,
                    );
                    break;
                }
                _ => {
                    code.skip(self.tokenizer.next_token(), MissingTokenKind::End);
                }
            }
        }

        let expr = CaseExpression::new(head, arms, else_body);

        Node::new(
            NodeKind::Expression(Expression::new(
                ExpressionKind::CaseExpression(expr),
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

        // A separator must be appear before block
        self.tokenizer.peek();
        let mut newline_seen = self.tokenizer.is_newline_seen();
        let mut insertion_range = self.tokenizer.current_insertion_range();

        loop {
            let mut stmt_seen = false;

            if let Some(stmt) = self.parse_stmt() {
                stmt_seen = true;

                if !newline_seen {
                    code.missing(insertion_range, MissingTokenKind::Separator);
                }

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
                        // Okay, it's done. don't consume a stop token.
                        break;
                    }

                    newline_seen = self.tokenizer.is_newline_seen();
                    insertion_range = self.tokenizer.current_insertion_range();

                    // `parse_stmt()` should consume at least one token.
                    // However, in case `parse_stmt()` have not been able to consume a single token,
                    // we have to skip the current token.
                    if !stmt_seen {
                        code.skip(self.tokenizer.next_token(), MissingTokenKind::Statement);
                    }
                }
            }
        }

        Node::new(NodeKind::Block(Block::new(body)), code)
    }

    fn _parse_optional_item(
        &mut self,
        code: &mut Code,
        node_parser: fn(&mut Parser<'a>) -> Option<Rc<Node>>,
        missing_token: MissingTokenKind,
    ) -> Option<Rc<Node>> {
        let node = node_parser(self);

        if let Some(ref node) = node {
            code.node(node);
        } else {
            code.missing(self.tokenizer.current_insertion_range(), missing_token);
        }

        node
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
            let expr = BinaryExpression::new(operator, lhs, rhs);

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
            stmt.expression().kind(),
            ExpressionKind::IntegerLiteral(i) => {
                assert_eq!(i.value(), 42);
            }
        );

        let mut code = stmt.expression.code();
        assert_eq!(code.len(), 1);

        let token = next_interpreted_token(&mut code);
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

            assert_matches!(expr.kind(), ExpressionKind::StringLiteral(..));

            let mut tokens = stmt.expression.code();
            assert_eq!(tokens.len(), 4);

            let token = next_interpreted_token(&mut tokens);
            assert_matches!(token.kind, TokenKind::StringStart);

            let token = next_interpreted_token(&mut tokens);
            assert_matches!(&token.kind, TokenKind::StringContent(s) => {
                assert_eq!(s, "Fizz")
            });

            let token = next_interpreted_token(&mut tokens);
            assert_matches!(token.kind, TokenKind::StringEscapeSequence(c) => {
                assert_eq!(c, '\"')
            });

            let (_, item) = next_missing_token(&mut tokens);
            assert_eq!(item, MissingTokenKind::StringEnd);
        }
    }

    #[test]
    fn incomplete_string_in_paren() {
        for src in vec!["(\"Fizz\\\")", "(\"Fizz\\\")\n"] {
            let stmt = parse_statement(src);
            let stmt = stmt.statement().unwrap();
            let expr = stmt.expression();

            assert_matches!(expr.kind(), ExpressionKind::Expression(expr) => {
                assert_matches!(expr.expression().unwrap().kind(), ExpressionKind::StringLiteral(..));
            });

            let mut tokens = stmt.expression.code();
            assert_eq!(tokens.len(), 3);

            let token = next_interpreted_token(&mut tokens);
            assert_matches!(token.kind, TokenKind::Char('('));

            let node = next_node(&mut tokens);
            assert_matches!(node.kind(), NodeKind::Expression(..));

            let (_, item) = next_missing_token(&mut tokens);
            assert_eq!(item, MissingTokenKind::Char(')'));
        }
    }

    #[test]
    fn add_integer() {
        let stmt = parse_statement("1+2");
        let stmt = stmt.statement().unwrap();
        let expr = stmt.expression().binary_expression().unwrap();

        assert_eq!(expr.operator, BinaryOperator::Add);
        assert_matches!(expr.lhs().kind(), ExpressionKind::IntegerLiteral(i) => {
            assert_eq!(i.value(), 1);
        });
        assert_matches!(expr.rhs().unwrap().kind(), ExpressionKind::IntegerLiteral(i) => {
            assert_eq!(i.value(), 2);
        });

        let mut tokens = stmt.expression.code();
        assert_eq!(tokens.len(), 3);

        let node = next_node(&mut tokens);
        assert!(node.is_expression());

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('+'));

        let node = next_node(&mut tokens);
        assert!(node.is_expression());
    }

    #[test]
    fn add_integer_missing_node() {
        let stmt = parse_statement("1+");
        let stmt = stmt.statement().unwrap();
        let expr = stmt.expression().binary_expression().unwrap();

        assert_eq!(expr.operator, BinaryOperator::Add);
        assert_matches!(expr.lhs().kind(), ExpressionKind::IntegerLiteral(i) => {
            assert_eq!(i.value(), 1);
        });
        assert!(expr.rhs().is_none());

        let mut tokens = stmt.expression.code();
        assert_eq!(tokens.len(), 3);

        let node = next_node(&mut tokens);
        assert!(node.is_expression());

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('+'));

        let (token, expected) = next_skipped_token(&mut tokens);
        assert_eq!(token.kind, TokenKind::Eos);
        assert_eq!(expected, MissingTokenKind::Expression);
    }

    #[test]
    fn add_integer_skipped_tokens() {
        let stmt = parse_statement("1 + % ? 2");
        let stmt = stmt.statement().unwrap();
        let expr = stmt.expression().binary_expression().unwrap();

        assert_eq!(expr.operator, BinaryOperator::Add);
        assert_matches!(expr.lhs().kind(), ExpressionKind::IntegerLiteral(i) => {
            assert_eq!(i.value(), 1);
        });
        assert_matches!(expr.rhs().unwrap().kind(), ExpressionKind::IntegerLiteral(i) => {
            assert_eq!(i.value(), 2);
        });

        let mut tokens = stmt.expression.code();
        assert_eq!(tokens.len(), 5);

        let node = next_node(&mut tokens);
        assert!(node.is_expression());

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('+'));

        let (token, expected) = next_skipped_token(&mut tokens);
        assert_eq!(token.kind, TokenKind::Char('%'));
        assert_eq!(expected, MissingTokenKind::Expression);

        let (token, expected) = next_skipped_token(&mut tokens);
        assert_eq!(token.kind, TokenKind::Char('?'));
        assert_eq!(expected, MissingTokenKind::Expression);

        let node = next_node(&mut tokens);
        assert!(node.is_expression());
    }

    #[test]
    fn unary_op() {
        let stmt = parse_statement("-1");
        let stmt = stmt.statement().unwrap();
        let expr = stmt.expression().unary_expression().unwrap();

        assert_eq!(expr.operator, UnaryOperator::Minus);
        assert_matches!(expr.operand().unwrap().kind(), ExpressionKind::IntegerLiteral(i) => {
            assert_eq!(i.value(), 1);
        });

        let mut tokens = stmt.expression.code();
        assert_eq!(tokens.len(), 2);

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('-'));

        let node = next_node(&mut tokens);
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
                assert_matches!(operand.expression().unwrap().kind(), ExpressionKind::IntegerLiteral(i) => {
                    assert_eq!(i.value(), 1);
                });
            });
        });

        let mut tokens = stmt.expression.code();
        assert_eq!(tokens.len(), 2);

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('-'));

        let node = next_node(&mut tokens);
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
            assert_matches!(arguments[0].kind(), ExpressionKind::IntegerLiteral(i) => {
                assert_eq!(i.value(), 0);
            });
        });

        let mut tokens = stmt.expression.code();
        assert_eq!(tokens.len(), 4);

        let node = next_node(&mut tokens);
        assert!(node.is_expression());

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('['));

        let node = next_node(&mut tokens);
        assert!(node.is_expression());

        let token = next_interpreted_token(&mut tokens);
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

        let mut tokens = stmt.expression.code();
        assert_eq!(tokens.len(), 3);

        let node = next_node(&mut tokens);
        assert!(node.is_expression());

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('['));

        let token = next_interpreted_token(&mut tokens);
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
            assert_matches!(arguments[0].kind(), ExpressionKind::IntegerLiteral(i) => {
                assert_eq!(i.value(), 1);
            });
        });

        let mut tokens = stmt.expression.code();
        assert_eq!(tokens.len(), 4);

        tokens.next();
        tokens.next();
        tokens.next();

        let (range, item) = next_missing_token(&mut tokens);
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
                assert_matches!(arguments[0].kind(), ExpressionKind::StringLiteral(..));
            });

            let mut tokens = stmt.expression.code();
            assert_eq!(tokens.len(), 4);

            tokens.next();
            tokens.next();
            tokens.next();

            let (range, item) = next_missing_token(&mut tokens);
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

        let mut tokens = stmt.expression.code();
        assert_eq!(tokens.len(), 2);

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('['));

        let token = next_interpreted_token(&mut tokens);
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
            assert_matches!(elements[0].kind(), ExpressionKind::IntegerLiteral(i) => {
                assert_eq!(i.value(), 1);
            });
        });

        let mut tokens = stmt.expression.code();
        assert_eq!(tokens.len(), 4);

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('['));

        let node = next_node(&mut tokens);
        assert!(node.is_expression());

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char(','));

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char(']'));
    }

    // If expression
    #[test]
    fn if_expression() {
        let stmt = parse_statement(
            "if x > 0
                10
            else
                20
            end",
        );
        let stmt = stmt.statement().unwrap();
        let expr = stmt.expression().if_expression().unwrap();

        assert_matches!(expr, IfExpression { condition, then_body, else_body } => {
            let condition = condition.as_ref().unwrap().expression().unwrap();

            assert_matches!(condition.kind(), ExpressionKind::BinaryExpression(..));
            assert!(then_body.block().is_some());
            assert!(else_body.is_some());
            assert!(else_body.as_ref().unwrap().block().is_some());
        });
    }

    #[test]
    fn if_expression_missing_condition() {
        let stmt = parse_statement("if\nend");
        let stmt = stmt.statement().unwrap();
        let expr = stmt.expression().if_expression().unwrap();

        assert_matches!(expr, IfExpression { condition, then_body, else_body } => {
            assert!(condition.is_none());
            assert!(else_body.is_none());

            let then_body = then_body.block().unwrap();
            let stmts = then_body.statements();
            assert!(stmts.is_empty());
        });
    }

    #[test]
    fn if_expression_missing_newline() {
        let stmt = parse_statement("if b x end");
        let stmt = stmt.statement().unwrap();

        assert!(stmt.expression().if_expression().is_some());

        // tokens
        let mut tokens = stmt.expression.code();
        assert_eq!(tokens.len(), 4);

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::If);

        let node = next_node(&mut tokens);
        assert!(node.is_expression());

        let node = next_node(&mut tokens);
        assert!(node.is_block());

        {
            let mut tokens = node.code();

            assert_eq!(tokens.len(), 2);

            let (range, item) = next_missing_token(&mut tokens);
            assert_eq!(item, MissingTokenKind::Separator);
            assert_eq!(range.start.line, 0);
            assert_eq!(range.start.character, 5);
            assert_eq!(range.end.line, 0);
            assert_eq!(range.end.character, 6);

            let node = next_node(&mut tokens);
            assert!(node.is_statement());
        }

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::End);
    }

    // If expression
    #[test]
    fn case_expression() {
        let stmt = parse_statement(
            "
            case x
            when 123
                1
            when \"string\"
                2
            when y
                3
            when [1, x]
                4
            when x if x > 10
                5
            else
                6
            end",
        );
        let stmt = stmt.statement().unwrap();
        let expr = stmt.expression().case_expression().unwrap();

        assert_matches!(expr, CaseExpression { head, arms, else_body } => {
            assert!(head.is_some());
            assert!(!arms.is_empty());

            // when 123
            assert!(arms[0].pattern.is_some());
            assert!(arms[0].guard.is_none());
            assert_matches!(arms[0].pattern().unwrap().kind, PatternKind::IntegerPattern(..));

            // when \"string\"
            assert!(arms[1].pattern.is_some());
            assert!(arms[1].guard.is_none());
            assert_matches!(arms[1].pattern().unwrap().kind, PatternKind::StringPattern(..));

            // when y
            assert!(arms[2].pattern.is_some());
            assert!(arms[2].guard.is_none());
            assert_matches!(arms[2].pattern().unwrap().kind, PatternKind::VariablePattern(..));

            // when [1, x]
            assert!(arms[3].pattern.is_some());
            assert!(arms[3].guard.is_none());
            assert_matches!(arms[3].pattern().unwrap().kind, PatternKind::ArrayPattern(..));

            // when x if x > 10
            assert!(arms[4].pattern.is_some());
            assert!(arms[4].guard.is_some());
            assert_matches!(arms[4].pattern().unwrap().kind, PatternKind::VariablePattern(..));

            assert!(else_body.is_some());
        });
    }

    // --- helpers

    fn parse_statement(src: &str) -> Rc<Node> {
        let module = Parser::parse_string(src);
        let module = module.program().unwrap();

        assert!(!module.body.is_empty());
        Rc::clone(&module.body[0])
    }

    fn next_node<'a>(tokens: &'a mut CodeKinds) -> &'a Node {
        unwrap_node(tokens.next().unwrap())
    }

    fn next_interpreted_token<'a>(tokens: &'a mut CodeKinds) -> &'a Token {
        unwrap_interpreted_token(tokens.next().unwrap())
    }

    fn next_missing_token(tokens: &mut CodeKinds) -> (EffectiveRange, MissingTokenKind) {
        unwrap_missing_token(tokens.next().unwrap())
    }

    fn next_skipped_token<'a>(tokens: &'a mut CodeKinds) -> (&'a Token, MissingTokenKind) {
        unwrap_skipped_token(tokens.next().unwrap())
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
