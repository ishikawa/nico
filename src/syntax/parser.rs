use super::*;
use crate::util::wrap;
use crate::{sem, syntax::binding};

const DEBUG: bool = false;

pub struct Parser<'a> {
    tokenizer: Tokenizer<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(tokenizer: Tokenizer<'a>) -> Self {
        Self { tokenizer }
    }
}

impl<'a> Parser<'a> {
    pub fn parse_string<S: 'a + AsRef<str>>(src: S) -> AST {
        let tokenizer = Tokenizer::from_string(&src);
        let mut parser = Parser::new(tokenizer);

        parser.parse()
    }

    pub fn parse(&mut self) -> AST {
        let mut body = vec![];
        let mut code = Code::new();
        let mut arena = NodeArena::new();

        loop {
            // Type declaration
            if let Some(node) = self.parse_struct_definition(&mut arena) {
                code.node(node);
                body.push(node);
            }
            // Function
            else if let Some(node) = self.parse_function(&mut arena) {
                code.node(node);
                body.push(node);
            }
            // Body for main function
            else if let Some(node) = self.parse_stmt(&mut arena) {
                code.node(node);
                body.push(node);
            }
            // No top level constructs can be consumed. It may be at the end of input or
            // parse error.
            else {
                let token = self.tokenizer.peek();

                match &token.kind {
                    TokenKind::Eos => {
                        // To handle whitespace and comments at the end of a document
                        code.interpret(self.tokenizer.next_token());
                        break;
                    }
                    _ => {
                        let token = self.tokenizer.next_token();
                        code.skip(token, MissingTokenKind::TopLevel);
                    }
                }
            }
        }

        let program = Program::new(body, code);
        let node = arena.alloc(NodeKind::Program(program));
        let mut tree = AST::new(arena, node);

        binding::bind(&mut tree);

        tree
    }

    fn parse_struct_definition(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        self.debug_trace("parse_struct_definition");

        let mut code = Code::new();

        // struct
        code.interpret(self.expect_token(TokenKind::Struct)?);

        // name
        let mut struct_name = None;

        loop {
            match self.tokenizer.peek_kind() {
                TokenKind::Identifier(_) => {
                    let name = self.parse_name(arena).unwrap();

                    code.node(name);
                    struct_name = Some(name);

                    break;
                }
                TokenKind::Char('{') | TokenKind::Eos => {
                    code.missing(
                        self.tokenizer.current_insertion_range(),
                        MissingTokenKind::StructName,
                    );
                    break;
                }
                _ => {
                    // Continue until read identifier.
                    code.skip(self.tokenizer.next_token(), MissingTokenKind::StructName);
                }
            }
        }

        // fields
        let fields = self._parse_elements(arena, '{', '}', &mut code, Parser::parse_type_field);

        let definition = StructDefinition::new(struct_name, fields, code);

        Some(arena.alloc(NodeKind::StructDefinition(definition)))
    }

    fn parse_function(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        self.debug_trace("parse_function");

        let mut code = Code::new();

        // TODO: In L(1) parser, if the `fun` keyword is not followed by an `export` keyword,
        // the `export` keyword cannot be push backed, so we shouldn't stop reading export here.
        let export = self.match_token(TokenKind::Export);

        if export {
            code.interpret(self.tokenizer.next_token());
        }

        // fun
        code.interpret(self.expect_token(TokenKind::Fun)?);

        // name
        let mut function_name = None;

        loop {
            match self.tokenizer.peek_kind() {
                TokenKind::Identifier(_) => {
                    // Okay, it's a function name.
                    let name = self.parse_name(arena).unwrap();

                    code.node(name);
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
            self._parse_elements(arena, '(', ')', &mut code, Parser::parse_function_parameter);

        // body
        let body = self._read_block(arena, &[TokenKind::End]);

        code.node(body);
        code.interpret(self.tokenizer.next_token()); // end

        let definition = FunctionDefinition::new(function_name, parameters, body, code);
        Some(arena.alloc(NodeKind::FunctionDefinition(definition)))
    }

    fn parse_function_parameter(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        if let Some(name) = self.parse_name(arena) {
            let code = Code::with_node(name);
            Some(
                arena.alloc(NodeKind::FunctionParameter(FunctionParameter::new(
                    name, code,
                ))),
            )
        } else {
            None
        }
    }

    fn parse_type_field(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        // To prevent reading too many unnecessary tokens,
        // we should not skip tokens here.
        let mut code = Code::new();

        let name = self.parse_name(arena);

        if let Some(name) = name {
            code.node(name);
        } else {
            code.missing(
                self.tokenizer.current_insertion_range(),
                MissingTokenKind::FieldName,
            );
        }

        code.interpret(self.expect_token(TokenKind::Char(':'))?);

        let annotation = self.parse_type_annotation(arena);

        if let Some(annotation) = annotation {
            code.node(annotation);
        } else {
            code.missing(
                self.tokenizer.current_insertion_range(),
                MissingTokenKind::TypeAnnotation,
            );
        }

        let field = TypeField::new(name, annotation, code);
        Some(arena.alloc(NodeKind::TypeField(field)))
    }

    fn parse_value_field(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        let name = self.parse_name(arena)?;
        let mut code = Code::with_node(name);

        // value can be omitted for struct literal.
        let field = if let Some(separator) = self.expect_token(TokenKind::Char(':')) {
            code.interpret(separator);

            let value = self.parse_expr(arena);

            if let Some(value) = value {
                code.node(value);
            } else {
                code.missing(
                    self.tokenizer.current_insertion_range(),
                    MissingTokenKind::Expression,
                );
            }

            ValueField::new(name, value, code)
        } else {
            ValueField::new(name, None, code)
        };

        Some(arena.alloc(NodeKind::ValueField(field)))
    }

    fn parse_value_field_pattern(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        let name = self.parse_name(arena)?;
        let mut code = Code::with_node(name);

        // value can be omitted for struct literal.
        let field = if let Some(separator) = self.expect_token(TokenKind::Char(':')) {
            code.interpret(separator);

            let value = self.parse_pattern(arena);

            if let Some(value) = value {
                code.node(value);
            } else {
                code.missing(
                    self.tokenizer.current_insertion_range(),
                    MissingTokenKind::Pattern,
                );
            }

            ValueFieldPattern::new(name, value, code)
        } else {
            ValueFieldPattern::new(name, None, code)
        };

        Some(arena.alloc(NodeKind::ValueFieldPattern(field)))
    }

    fn parse_name(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        if let TokenKind::Identifier(name) = self.tokenizer.peek_kind() {
            let name = name.clone();
            let code = Code::with_interpreted(self.tokenizer.next_token());
            let id = arena.alloc(NodeKind::Identifier(Identifier::new(name, code)));

            Some(id)
        } else {
            None
        }
    }

    fn parse_type_annotation(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        let code = Code::with_interpreted(self.expect_token(TokenKind::I32)?);

        let ty = TypeAnnotation::new(wrap(sem::Type::Int32), code);
        Some(arena.alloc(NodeKind::TypeAnnotation(ty)))
    }

    fn parse_stmt(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        self.debug_trace("parse_stmt");

        match self.tokenizer.peek_kind() {
            TokenKind::Let => self.parse_variable_declaration_stmt(arena),
            _ => self.parse_stmt_expr(arena),
        }
    }

    fn parse_variable_declaration(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        self.debug_trace("parse_variable_declaration");

        let mut code = Code::with_interpreted(self.tokenizer.next_token()); // let
        let mut pattern = None;
        let mut init = None;

        if let Some(pat) = self.parse_pattern(arena) {
            code.node(pat);
            pattern = Some(pat);
        } else {
            code.missing(
                self.tokenizer.current_insertion_range(),
                MissingTokenKind::Pattern,
            );
        }

        code.interpret(self.expect_token(TokenKind::Char('='))?);

        if let Some(expr) = self.parse_expr(arena) {
            code.node(expr);
            init = Some(expr);
        } else {
            code.missing(
                self.tokenizer.current_insertion_range(),
                MissingTokenKind::Expression,
            );
        }

        let decl = VariableDeclaration::new(pattern, init, code);
        Some(arena.alloc(NodeKind::VariableDeclaration(decl)))
    }

    fn parse_variable_declaration_stmt(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        self.debug_trace("parse_variable_declaration_stmt");

        let decl = self.parse_variable_declaration(arena)?;
        let code = Code::with_node(decl);
        let stmt = Statement::new(StatementKind::VariableDeclaration(decl), code);

        Some(arena.alloc(NodeKind::Statement(stmt)))
    }

    fn parse_stmt_expr(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        self.debug_trace("parse_stmt_expr");

        let expr = self.parse_expr(arena)?;
        let code = Code::with_node(expr);
        let stmt = Statement::new(StatementKind::Expression(expr), code);

        Some(arena.alloc(NodeKind::Statement(stmt)))
    }

    fn parse_expr(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        self.debug_trace("parse_expr");
        self.parse_rel_op1(arena)
    }

    fn parse_rel_op1(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        self.debug_trace("parse_rel_op1");
        self._parse_binary_op(
            arena,
            Parser::parse_rel_op2,
            &[
                (TokenKind::Eq, BinaryOperator::Eq),
                (TokenKind::Ne, BinaryOperator::Ne),
            ],
        )
    }

    fn parse_rel_op2(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        self.debug_trace("parse_rel_op2");
        self._parse_binary_op(
            arena,
            Parser::parse_binary_op1,
            &[
                (TokenKind::Le, BinaryOperator::Le),
                (TokenKind::Ge, BinaryOperator::Ge),
                (TokenKind::Char('<'), BinaryOperator::Lt),
                (TokenKind::Char('>'), BinaryOperator::Gt),
            ],
        )
    }

    fn parse_binary_op1(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        self.debug_trace("parse_binary_op1");
        self._parse_binary_op(
            arena,
            Parser::parse_binary_op2,
            &[
                (TokenKind::Char('+'), BinaryOperator::Add),
                (TokenKind::Char('-'), BinaryOperator::Sub),
                (TokenKind::Char('%'), BinaryOperator::Rem),
            ],
        )
    }

    fn parse_binary_op2(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        self.debug_trace("parse_binary_op2");
        self._parse_binary_op(
            arena,
            Parser::parse_unary_op,
            &[
                (TokenKind::Char('*'), BinaryOperator::Mul),
                (TokenKind::Char('/'), BinaryOperator::Div),
            ],
        )
    }

    fn parse_unary_op(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        self.debug_trace("parse_unary_op");

        let operator = match self.tokenizer.peek_kind() {
            TokenKind::Char('+') => UnaryOperator::Plus,
            TokenKind::Char('-') => UnaryOperator::Minus,
            _ => return self.parse_access(arena),
        };

        // unary operators are right associative.
        let mut code = Code::with_interpreted(self.tokenizer.next_token());
        let mut operand = None;

        loop {
            if let Some(node) = self.parse_unary_op(arena) {
                code.node(node);
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
        let expr = Expression::new(kind, code);

        Some(arena.alloc(NodeKind::Expression(expr)))
    }

    fn parse_access(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        self.debug_trace("parse_access");

        let mut operand = self.parse_primary(arena)?;

        loop {
            let mut code = Code::with_node(operand);

            // To distinguish `x\n[...]` and `x[...]`, we have to capture
            // `tokenizer.is_newline_seen()`, so try to advance tokenizer.
            self.tokenizer.peek();

            if self.tokenizer.is_newline_seen() {
                break;
            }

            let token = self.tokenizer.peek();

            let kind = match token.kind {
                TokenKind::Char('[') => {
                    let arguments =
                        self._parse_elements(arena, '[', ']', &mut code, Parser::parse_expr);

                    ExpressionKind::SubscriptExpression(SubscriptExpression::new(
                        operand, arguments,
                    ))
                }
                TokenKind::Char('(') => {
                    let arguments =
                        self._parse_elements(arena, '(', ')', &mut code, Parser::parse_expr);

                    ExpressionKind::CallExpression(CallExpression::new(operand, arguments))
                }
                TokenKind::Char('.') => {
                    code.interpret(self.tokenizer.next_token());

                    let field = self.parse_name(arena);

                    if let Some(field) = field {
                        code.node(field);
                    } else {
                        code.missing(
                            self.tokenizer.current_insertion_range(),
                            MissingTokenKind::FieldName,
                        );
                    }

                    ExpressionKind::MemberExpression(MemberExpression::new(operand, field))
                }
                _ => break,
            };

            operand = arena.alloc(NodeKind::Expression(Expression::new(kind, code)));
        }

        Some(operand)
    }

    fn parse_primary(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        self.debug_trace("parse_primary");

        let token = self.tokenizer.peek();
        let node = match token.kind {
            TokenKind::Integer(_) => self.read_integer(arena),
            TokenKind::Identifier(_) => self.read_identifier(arena),
            TokenKind::StringStart => self.read_string(arena),
            TokenKind::Char('(') => self.read_paren(arena),
            TokenKind::Char('[') => self.read_array(arena),
            TokenKind::If => self.read_if_expression(arena),
            TokenKind::Case => self.read_case_expression(arena),
            _ => return None,
        };

        Some(arena.alloc(NodeKind::Expression(node)))
    }

    fn parse_pattern(&mut self, arena: &mut NodeArena) -> Option<NodeId> {
        self.debug_trace("parse_pattern");

        let token = self.tokenizer.peek();
        let pattern = match token.kind {
            TokenKind::Integer(_) => self.read_integer_pattern(arena),
            TokenKind::Identifier(_) => self.read_identifier_pattern(arena),
            TokenKind::StringStart => self.read_string_pattern(arena),
            TokenKind::Char('[') => self.read_array_pattern(arena),
            TokenKind::Rest => self.read_rest_pattern(arena),
            _ => return None,
        };

        Some(arena.alloc(NodeKind::Pattern(pattern)))
    }

    fn _read_integer(&mut self, arena: &mut NodeArena) -> (i32, Code) {
        let token = self.tokenizer.next_token();

        if let TokenKind::Integer(i) = token.kind {
            let code = Code::with_interpreted(token);

            (i, code)
        } else {
            unreachable!()
        }
    }

    fn read_integer(&mut self, arena: &mut NodeArena) -> Expression {
        let (literal, code) = self._read_integer(arena);
        Expression::new(ExpressionKind::IntegerLiteral(literal), code)
    }

    fn read_integer_pattern(&mut self, arena: &mut NodeArena) -> Pattern {
        let (literal, code) = self._read_integer(arena);

        Pattern::new(PatternKind::IntegerPattern(literal), code)
    }

    fn read_identifier(&mut self, arena: &mut NodeArena) -> Expression {
        let id = self.parse_name(arena).unwrap();
        let mut code = Code::with_node(id);

        let kind = if *self.tokenizer.peek_kind() == TokenKind::Char('{') {
            let fields =
                self._parse_elements(arena, '{', '}', &mut code, Parser::parse_value_field);

            ExpressionKind::StructLiteral(StructLiteral::new(id, fields))
        } else {
            ExpressionKind::VariableExpression(id)
        };

        Expression::new(kind, code)
    }

    fn read_identifier_pattern(&mut self, arena: &mut NodeArena) -> Pattern {
        let id = self.parse_name(arena).unwrap();
        let mut code = Code::with_node(id);

        let kind = if *self.tokenizer.peek_kind() == TokenKind::Char('{') {
            let fields = self._parse_elements(
                arena,
                '{',
                '}',
                &mut code,
                Parser::parse_value_field_pattern,
            );

            PatternKind::StructPattern(StructPattern::new(id, fields))
        } else {
            PatternKind::VariablePattern(id)
        };

        Pattern::new(kind, code)
    }

    fn _read_string(&mut self, arena: &mut NodeArena) -> (Option<String>, Code) {
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

        let literal = if has_error { None } else { Some(string) };

        (literal, code)
    }

    fn read_string(&mut self, arena: &mut NodeArena) -> Expression {
        let (string, code) = self._read_string(arena);

        Expression::new(ExpressionKind::StringLiteral(string), code)
    }

    fn read_string_pattern(&mut self, arena: &mut NodeArena) -> Pattern {
        let (string, code) = self._read_string(arena);
        Pattern::new(PatternKind::StringPattern(string), code)
    }

    fn read_paren(&mut self, arena: &mut NodeArena) -> Expression {
        let mut code = Code::with_interpreted(self.tokenizer.next_token()); // "("
        let node = self.parse_expr(arena);

        if let Some(node) = node {
            code.node(node);
        } else {
            code.missing(
                self.tokenizer.current_insertion_range(),
                MissingTokenKind::Expression,
            );
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

        // Because parentheses which groups an expression is not part of
        // AST, we have to incorporate it into another node.
        if let Some(expr) = node {
            Expression::new(ExpressionKind::Expression(Some(expr)), code)
        } else {
            Expression::new(ExpressionKind::Expression(None), code)
        }
    }

    fn read_array(&mut self, arena: &mut NodeArena) -> Expression {
        let mut code = Code::new();
        let elements = self._parse_elements(arena, '[', ']', &mut code, Parser::parse_expr);

        let expr = ArrayExpression::new(elements);

        Expression::new(ExpressionKind::ArrayExpression(expr), code)
    }

    fn read_array_pattern(&mut self, arena: &mut NodeArena) -> Pattern {
        let mut code = Code::new();
        let elements = self._parse_elements(arena, '[', ']', &mut code, Parser::parse_pattern);

        Pattern::new(PatternKind::ArrayPattern(ArrayPattern::new(elements)), code)
    }

    fn read_rest_pattern(&mut self, arena: &mut NodeArena) -> Pattern {
        let mut code = Code::with_interpreted(self.tokenizer.next_token()); // "..."
        let name = self.parse_name(arena);

        if let Some(node) = name {
            code.node(node);
        }

        Pattern::new(PatternKind::RestPattern(RestPattern::new(name)), code)
    }

    fn read_if_expression(&mut self, arena: &mut NodeArena) -> Expression {
        let mut code = Code::with_interpreted(self.tokenizer.next_token()); // "if"
        let condition = self._parse_optional_item(
            arena,
            &mut code,
            Parser::parse_expr,
            MissingTokenKind::Expression,
        );

        // body
        let then_body = self._read_block(arena, &[TokenKind::End, TokenKind::Else]);
        let has_else = *self.tokenizer.peek_kind() == TokenKind::Else;

        code.node(then_body);
        code.interpret(self.tokenizer.next_token()); // "else" or "end"

        let else_body = if has_else {
            let else_body = self._read_block(arena, &[TokenKind::End]);

            code.node(else_body);
            code.interpret(self.tokenizer.next_token()); //  "end"

            Some(else_body)
        } else {
            None
        };

        let expr = IfExpression::new(condition, then_body, else_body);

        Expression::new(ExpressionKind::IfExpression(expr), code)
    }

    fn read_case_expression(&mut self, arena: &mut NodeArena) -> Expression {
        // case ...
        let mut code = Code::with_interpreted(self.tokenizer.next_token()); // "case"
        let head = self._parse_optional_item(
            arena,
            &mut code,
            Parser::parse_expr,
            MissingTokenKind::Expression,
        );

        // arms
        let mut arms = vec![];
        let mut else_body = None;

        loop {
            match self.tokenizer.peek_kind() {
                TokenKind::When => {
                    let arm = self._read_case_arm(arena);

                    code.node(arm);
                    arms.push(arm);
                }
                TokenKind::Else => {
                    code.interpret(self.tokenizer.next_token());

                    let block = self._read_block(arena, &[TokenKind::End]);
                    code.node(block);

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

        Expression::new(ExpressionKind::CaseExpression(expr), code)
    }

    fn _read_case_arm(&mut self, arena: &mut NodeArena) -> NodeId {
        let mut code = Code::new();

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
                arena,
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
                arena,
                &mut code,
                Parser::parse_expr,
                MissingTokenKind::Expression,
            );
        }

        let then_body =
            self._read_block(arena, &[TokenKind::When, TokenKind::Else, TokenKind::End]);
        code.node(then_body);

        let arm = CaseArm::new(pattern, guard, then_body, code);
        arena.alloc(NodeKind::CaseArm(arm))
    }

    /// Reads statements until it meets a token listed in `stop_tokens`.
    /// But this function doesn't consume a stop token itself, consuming
    /// a stop token is caller's responsibility.
    fn _read_block(&mut self, arena: &mut NodeArena, stop_tokens: &[TokenKind]) -> NodeId {
        let mut code = Code::new();

        // body
        let mut body = vec![];

        // A separator must be appear before block
        self.tokenizer.peek();
        let mut newline_seen = self.tokenizer.is_newline_seen();
        let mut insertion_range = self.tokenizer.current_insertion_range();

        loop {
            let mut stmt_seen = false;

            if let Some(stmt) = self.parse_stmt(arena) {
                stmt_seen = true;

                if !newline_seen {
                    code.missing(insertion_range, MissingTokenKind::Separator);
                }

                code.node(stmt);
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

                    // `parse_stmt(arena)` should consume at least one token.
                    // However, in case `parse_stmt(arena)` have not been able to consume a single token,
                    // we have to skip the current token.
                    if !stmt_seen {
                        code.skip(self.tokenizer.next_token(), MissingTokenKind::Statement);
                    }
                }
            }
        }

        arena.alloc(NodeKind::Block(Block::new(body, code)))
    }

    fn _parse_optional_item(
        &mut self,
        arena: &mut NodeArena,
        code: &mut Code,
        node_parser: fn(&mut Parser<'a>, &mut NodeArena) -> Option<NodeId>,
        missing_token: MissingTokenKind,
    ) -> Option<NodeId> {
        let node = node_parser(self, arena);

        if let Some(node) = node {
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
        arena: &mut NodeArena,
        open_char: char,
        close_char: char,
        code: &mut Code,
        element_parser: fn(&mut Parser<'a>, &mut NodeArena) -> Option<NodeId>,
    ) -> Vec<NodeId> {
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
                    if let Some(expr) = element_parser(self, arena) {
                        // Maybe user forgot opening token before a param.
                        //     # (
                        //         a ...
                        //     )
                        arguments.push(expr);
                        consumed = true;

                        code.missing(
                            self.tokenizer.current_insertion_range(),
                            MissingTokenKind::Char(open_char),
                        );

                        code.node(expr);
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
                let argument = element_parser(self, arena);

                if let Some(argument) = argument {
                    consumed = true;
                    arguments.push(argument);
                    code.node(argument);
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
        arena: &mut NodeArena,
        next_parser: fn(&mut Parser<'a>, &mut NodeArena) -> Option<NodeId>,
        operators: &[(TokenKind, BinaryOperator)],
    ) -> Option<NodeId> {
        let mut lhs = next_parser(self, arena)?;

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

            code.node(lhs).interpret(op_token);

            loop {
                rhs = next_parser(self, arena);

                if let Some(rhs) = rhs {
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
            let expr = Expression::new(ExpressionKind::BinaryExpression(expr), code);

            lhs = arena.alloc(NodeKind::Expression(expr));
        }

        Some(lhs)
    }

    // --- Helpers
    fn match_token(&mut self, kind: TokenKind) -> bool {
        *self.tokenizer.peek_kind() == kind
    }

    fn expect_token(&mut self, kind: TokenKind) -> Option<Token> {
        if self.match_token(kind) {
            Some(self.tokenizer.next_token())
        } else {
            None
        }
    }

    fn debug_trace(&self, name: &str) {
        if DEBUG {
            eprintln!("[{}] position: {}", name, self.tokenizer.current_position());
        }
    }
}

#[cfg(test)]
mod tests {
    use std::slice;

    use super::*;
    use crate::syntax::{EffectiveRange, ExpressionKind, SyntaxToken, Token};
    use assert_matches::assert_matches;

    #[test]
    fn number_integer() {
        let tree = Parser::parse_string("42");
        let stmt = get_statement(&tree);

        assert_matches!(
            stmt.expression(&tree).unwrap().kind(),
            ExpressionKind::IntegerLiteral(42)
        );

        let mut code = stmt.expression(&tree).unwrap().code();
        assert_eq!(code.len(), 1);

        let token = next_interpreted_token(&mut code);
        assert_matches!(token.kind, TokenKind::Integer(42));
    }

    #[test]
    fn incomplete_string() {
        for src in vec!["\"Fizz\\\"", "\"Fizz\\\"\n"] {
            let tree = Parser::parse_string(src);
            let stmt = get_statement(&tree);
            let expr = stmt.expression(&tree).unwrap();

            assert_matches!(expr.kind(), ExpressionKind::StringLiteral(..));

            let mut tokens = stmt.expression(&tree).unwrap().code();
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
            let tree = Parser::parse_string(src);
            let stmt = get_statement(&tree);
            let expr = stmt.expression(&tree).unwrap();

            assert_matches!(expr.kind(), ExpressionKind::Expression(Some(node_id)) => {
                let expr = tree.get(*node_id).unwrap().expression().unwrap();
                assert_matches!(expr.kind(), ExpressionKind::StringLiteral(..));
            });

            let mut tokens = stmt.expression(&tree).unwrap().code();
            assert_eq!(tokens.len(), 3);

            let token = next_interpreted_token(&mut tokens);
            assert_matches!(token.kind, TokenKind::Char('('));

            let node = next_node(&tree, &mut tokens);
            assert_matches!(node, NodeKind::Expression(..));

            let (_, item) = next_missing_token(&mut tokens);
            assert_eq!(item, MissingTokenKind::Char(')'));
        }
    }

    #[test]
    fn add_integer() {
        let tree = Parser::parse_string("1+2");
        let stmt = get_statement(&tree);
        let expr = stmt.expression(&tree).unwrap().binary_expression().unwrap();

        assert_eq!(expr.operator, BinaryOperator::Add);
        assert_matches!(expr.lhs(&tree).kind(), ExpressionKind::IntegerLiteral(1));
        assert_matches!(
            expr.rhs(&tree).unwrap().kind(),
            ExpressionKind::IntegerLiteral(2)
        );

        let mut tokens = stmt.expression(&tree).unwrap().code();
        assert_eq!(tokens.len(), 3);

        let node = next_node(&tree, &mut tokens);
        assert!(node.is_expression());

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('+'));

        let node = next_node(&tree, &mut tokens);
        assert!(node.is_expression());
    }

    #[test]
    fn add_integer_missing_node() {
        let tree = Parser::parse_string("1+");
        let stmt = get_statement(&tree);
        let expr = stmt.expression(&tree).unwrap().binary_expression().unwrap();

        assert_eq!(expr.operator, BinaryOperator::Add);
        assert_matches!(expr.lhs(&tree).kind(), ExpressionKind::IntegerLiteral(1));
        assert!(expr.rhs(&tree).is_none());

        let mut tokens = stmt.expression(&tree).unwrap().code();
        assert_eq!(tokens.len(), 3);

        let node = next_node(&tree, &mut tokens);
        assert!(node.is_expression());

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('+'));

        let (token, expected) = next_skipped_token(&mut tokens);
        assert_eq!(token.kind, TokenKind::Eos);
        assert_eq!(expected, MissingTokenKind::Expression);
    }

    #[test]
    fn add_integer_skipped_tokens() {
        let tree = Parser::parse_string("1 + % ? 2");
        let stmt = get_statement(&tree);
        let expr = stmt.expression(&tree).unwrap().binary_expression().unwrap();

        assert_eq!(expr.operator, BinaryOperator::Add);
        assert_matches!(expr.lhs(&tree).kind(), ExpressionKind::IntegerLiteral(1));
        assert_matches!(
            expr.rhs(&tree).unwrap().kind(),
            ExpressionKind::IntegerLiteral(2)
        );

        let mut tokens = stmt.expression(&tree).unwrap().code();
        assert_eq!(tokens.len(), 5);

        let node = next_node(&tree, &mut tokens);
        assert!(node.is_expression());

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('+'));

        let (token, expected) = next_skipped_token(&mut tokens);
        assert_eq!(token.kind, TokenKind::Char('%'));
        assert_eq!(expected, MissingTokenKind::Expression);

        let (token, expected) = next_skipped_token(&mut tokens);
        assert_eq!(token.kind, TokenKind::Char('?'));
        assert_eq!(expected, MissingTokenKind::Expression);

        let node = next_node(&tree, &mut tokens);
        assert!(node.is_expression());
    }

    #[test]
    fn unary_op() {
        let tree = Parser::parse_string("-1");
        let stmt = get_statement(&tree);
        let expr = stmt.expression(&tree).unwrap().unary_expression().unwrap();

        assert_eq!(expr.operator, UnaryOperator::Minus);
        assert_matches!(
            expr.operand(&tree).unwrap().kind(),
            ExpressionKind::IntegerLiteral(1)
        );

        let mut tokens = stmt.expression(&tree).unwrap().code();
        assert_eq!(tokens.len(), 2);

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('-'));

        let node = next_node(&tree, &mut tokens);
        assert!(node.is_expression());
    }

    #[test]
    fn unary_op_nested() {
        let tree = Parser::parse_string("-+1");
        let stmt = get_statement(&tree);
        let expr = stmt.expression(&tree).unwrap().unary_expression().unwrap();

        assert_eq!(expr.operator, UnaryOperator::Minus);

        let operand = expr.operand(&tree).unwrap();
        let operand = operand.unary_expression().unwrap();

        assert_eq!(operand.operator, UnaryOperator::Plus);

        let operand = operand.operand(&tree).unwrap();
        assert_matches!(operand.kind(), ExpressionKind::IntegerLiteral(1));

        let mut tokens = stmt.expression(&tree).unwrap().code();
        assert_eq!(tokens.len(), 2);

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('-'));

        let node = next_node(&tree, &mut tokens);
        assert!(node.is_expression());
    }

    #[test]
    fn subscript_index() {
        let tree = Parser::parse_string("a[0]");
        let stmt = get_statement(&tree);
        let expr = stmt
            .expression(&tree)
            .unwrap()
            .subscript_expression()
            .unwrap();

        assert_matches!(expr, SubscriptExpression{ .. } => {
            let id = expr.callee(&tree).variable_expression(&tree);
            assert!(id.is_some());

            let id = id.unwrap();
            assert_eq!(id.to_string(), "a");

            let arguments = expr.arguments(&tree).collect::<Vec<_>>();
            assert_eq!(arguments.len(), 1);
            assert_matches!(arguments[0].kind(), ExpressionKind::IntegerLiteral(0));
        });

        let mut tokens = stmt.expression(&tree).unwrap().code();
        assert_eq!(tokens.len(), 4);

        let node = next_node(&tree, &mut tokens);
        assert!(node.is_expression());

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('['));

        let node = next_node(&tree, &mut tokens);
        assert!(node.is_expression());

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char(']'));
    }

    #[test]
    fn subscript_empty() {
        let tree = Parser::parse_string("a[]");
        let stmt = get_statement(&tree);
        let expr = stmt
            .expression(&tree)
            .unwrap()
            .subscript_expression()
            .unwrap();

        assert_matches!(expr, SubscriptExpression{ .. } => {
            let id = expr.callee(&tree).variable_expression(&tree);
            assert!(id.is_some());

            let id = id.unwrap();
            assert_eq!(id.to_string(), "a");

            let arguments = expr.arguments(&tree).collect::<Vec<_>>();
            assert_eq!(arguments.len(), 0);
        });

        let mut tokens = stmt.expression(&tree).unwrap().code();
        assert_eq!(tokens.len(), 3);

        let node = next_node(&tree, &mut tokens);
        assert!(node.is_expression());

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('['));

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char(']'));
    }

    #[test]
    fn subscript_not_closed() {
        let tree = Parser::parse_string("a[1\nb");
        let stmt = get_statement(&tree);
        let expr = stmt
            .expression(&tree)
            .unwrap()
            .subscript_expression()
            .unwrap();

        assert_matches!(expr, SubscriptExpression{ .. } => {
            let id = expr.callee(&tree).variable_expression(&tree);
            assert!(id.is_some());

            let id = id.unwrap();
            assert_eq!(id.to_string(), "a");

            let arguments = expr.arguments(&tree).collect::<Vec<_>>();
            assert_eq!(arguments.len(), 1);
            assert_matches!(arguments[0].kind(), ExpressionKind::IntegerLiteral(1));
        });

        let mut tokens = stmt.expression(&tree).unwrap().code();
        assert_eq!(tokens.len(), 4);

        tokens.next();
        tokens.next();
        tokens.next();

        let (range, item) = next_missing_token(&mut tokens);
        assert_eq!(item, MissingTokenKind::Char(']'));
        assert_eq!(range.start.line, 0);
        assert_eq!(range.start.character, 2);
    }

    #[test]
    fn subscript_incomplete_string() {
        for src in vec!["a[\"", "a[\"\n"] {
            let tree = Parser::parse_string(src);
            let stmt = get_statement(&tree);
            let expr = stmt
                .expression(&tree)
                .unwrap()
                .subscript_expression()
                .unwrap();

            assert_matches!(expr, SubscriptExpression{ .. } => {
                let arguments = expr.arguments(&tree).collect::<Vec<_>>();
                assert_eq!(arguments.len(), 1);
                assert_matches!(arguments[0].kind(), ExpressionKind::StringLiteral(..));
            });

            let mut tokens = stmt.expression(&tree).unwrap().code();
            assert_eq!(tokens.len(), 4);

            tokens.next();
            tokens.next();
            tokens.next();

            let (range, item) = next_missing_token(&mut tokens);
            assert_eq!(item, MissingTokenKind::Char(']'));
            assert_eq!(range.start.line, 0);
            assert_eq!(range.start.character, 2);
        }
    }

    #[test]
    fn array_empty() {
        let tree = Parser::parse_string("[]");
        let stmt = get_statement(&tree);
        let expr = stmt.expression(&tree).unwrap().array_expression().unwrap();

        assert_matches!(expr, ArrayExpression{ .. } => {
            let elements = expr.elements(&tree).collect::<Vec<_>>();
            assert_eq!(elements.len(), 0);
        });

        let mut tokens = stmt.expression(&tree).unwrap().code();
        assert_eq!(tokens.len(), 2);

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('['));

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char(']'));
    }

    #[test]
    fn array_one_element_and_trailing_comma() {
        let tree = Parser::parse_string("[1,]");
        let stmt = get_statement(&tree);
        let expr = stmt.expression(&tree).unwrap().array_expression().unwrap();

        assert_matches!(expr, ArrayExpression{ .. } => {
            let elements = expr.elements(&tree).collect::<Vec<_>>();
            assert_eq!(elements.len(), 1);

            assert_eq!(elements.len(), 1);
            assert_matches!(elements[0].kind(), ExpressionKind::IntegerLiteral(1));
        });

        let mut tokens = stmt.expression(&tree).unwrap().code();
        assert_eq!(tokens.len(), 4);

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('['));

        let node = next_node(&tree, &mut tokens);
        assert!(node.is_expression());

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char(','));

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char(']'));
    }

    // If expression
    #[test]
    fn if_expression() {
        let tree = Parser::parse_string(
            "if x > 0
                10
            else
                20
            end",
        );
        let stmt = get_statement(&tree);
        let expr = stmt.expression(&tree).unwrap().if_expression().unwrap();

        let condition = expr.condition(&tree).unwrap();
        assert_matches!(condition.kind(), ExpressionKind::BinaryExpression(..));

        let else_body = expr.else_body(&tree);
        assert!(else_body.is_some());
    }

    #[test]
    fn if_expression_missing_condition() {
        let tree = Parser::parse_string("if\nend");
        let stmt = get_statement(&tree);
        let expr = stmt.expression(&tree).unwrap().if_expression().unwrap();

        assert_matches!(expr, IfExpression { condition, then_body, else_body } => {
            assert!(condition.is_none());
            assert!(else_body.is_none());

            let block = expr.then_body(&tree);
            let stmts = block.statements(&tree);
            assert_eq!(stmts.len(), 0);
        });
    }

    #[test]
    fn if_expression_missing_newline() {
        let tree = Parser::parse_string("if b x end");
        let stmt = get_statement(&tree);

        assert!(stmt.expression(&tree).unwrap().if_expression().is_some());

        // tokens
        let mut tokens = stmt.expression(&tree).unwrap().code();
        assert_eq!(tokens.len(), 4);

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::If);

        let node = next_node(&tree, &mut tokens);
        assert!(node.is_expression());

        let node = next_node(&tree, &mut tokens);
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

            let node = next_node(&tree, &mut tokens);
            assert!(node.is_statement());
        }

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::End);
    }

    // If expression
    #[test]
    fn case_expression() {
        let tree = Parser::parse_string(
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
        let stmt = get_statement(&tree);
        let expr = stmt.expression(&tree).unwrap().case_expression().unwrap();

        assert!(expr.head(&tree).is_some());

        let mut arms = expr.arms(&tree);

        assert!(!arms.is_empty());

        // when 123
        let arm = arms.next().unwrap();

        assert!(arm.pattern(&tree).is_some());
        assert!(arm.guard(&tree).is_none());
        assert_matches!(
            arm.pattern(&tree).unwrap().kind(),
            PatternKind::IntegerPattern(..)
        );

        // when \"string\"
        let arm = arms.next().unwrap();

        assert!(arm.pattern(&tree).is_some());
        assert!(arm.guard(&tree).is_none());
        assert_matches!(
            arm.pattern(&tree).unwrap().kind(),
            PatternKind::StringPattern(..)
        );

        // when y
        let arm = arms.next().unwrap();

        assert!(arm.pattern(&tree).is_some());
        assert!(arm.guard(&tree).is_none());
        assert_matches!(
            arm.pattern(&tree).unwrap().kind(),
            PatternKind::VariablePattern(..)
        );

        // when [1, x]
        let arm = arms.next().unwrap();

        assert!(arm.pattern(&tree).is_some());
        assert!(arm.guard(&tree).is_none());
        assert_matches!(
            arm.pattern(&tree).unwrap().kind(),
            PatternKind::ArrayPattern(..)
        );

        // when x if x > 10
        let arm = arms.next().unwrap();

        assert!(arm.pattern(&tree).is_some());
        assert!(arm.guard(&tree).is_some());
        assert_matches!(
            arm.pattern(&tree).unwrap().kind(),
            PatternKind::VariablePattern(..)
        );

        assert!(expr.else_body(&tree).is_some());
    }

    // --- helpers

    fn get_statement(tree: &AST) -> &Statement {
        let program = tree.program();

        assert!(!program.body.is_empty());
        tree.get(program.body[0]).unwrap().statement().unwrap()
    }

    fn next_node<'a>(tree: &'a AST, tokens: &'a mut slice::Iter<CodeKind>) -> &'a NodeKind {
        unwrap_node(tree, tokens.next().unwrap())
    }

    fn next_interpreted_token<'a>(tokens: &'a mut slice::Iter<CodeKind>) -> &'a Token {
        unwrap_interpreted_token(tokens.next().unwrap())
    }

    fn next_missing_token(
        tokens: &mut slice::Iter<CodeKind>,
    ) -> (EffectiveRange, MissingTokenKind) {
        unwrap_missing_token(tokens.next().unwrap())
    }

    fn next_skipped_token<'a>(
        tokens: &'a mut slice::Iter<CodeKind>,
    ) -> (&'a Token, MissingTokenKind) {
        unwrap_skipped_token(tokens.next().unwrap())
    }

    fn unwrap_node<'a>(tree: &'a AST, kind: &'a CodeKind) -> &'a NodeKind {
        if let CodeKind::Node(node_id) = kind {
            return tree.get(*node_id).unwrap();
        }

        panic!("expected child node");
    }

    fn unwrap_interpreted_token<'a>(kind: &'a CodeKind) -> &'a Token {
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

    fn unwrap_skipped_token<'a>(kind: &'a CodeKind) -> (&Token, MissingTokenKind) {
        if let CodeKind::SyntaxToken(token) = kind {
            if let SyntaxToken::Skipped { token, expected } = token {
                return (token, *expected);
            }
        }

        panic!("expected missing token");
    }
}
