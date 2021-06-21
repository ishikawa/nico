use super::*;
use crate::arena::{BumpaloArena, BumpaloString};
use crate::semantic;
use crate::util::naming::PrefixNaming;

const DEBUG: bool = false;

#[derive(Debug)]
pub struct Parser<'a, 't> {
    /// The filename, uri of a source code.
    source_name: BumpaloString<'a>,
    tokenizer: Tokenizer<'t>,
    naming: PrefixNaming,
}

impl<'a, 't> Parser<'a, 't> {
    pub fn new<S: AsRef<str>>(
        arena: &'a BumpaloArena,
        tokenizer: Tokenizer<'t>,
        source_name: S,
    ) -> Self {
        Self {
            tokenizer,
            source_name: BumpaloString::from_str_in(source_name.as_ref(), arena),
            naming: PrefixNaming::new("?"),
        }
    }

    pub fn source_name(&self) -> &str {
        self.source_name.as_str()
    }

    pub fn parse_string<S: AsRef<str> + ?Sized>(
        arena: &'a BumpaloArena,
        src: &S,
    ) -> &'a Program<'a> {
        let tokenizer = Tokenizer::from_string(src);
        let mut parser = Parser::new(arena, tokenizer, "-");

        parser.parse(arena)
    }

    pub fn parse(&mut self, arena: &'a BumpaloArena) -> &'a Program<'a> {
        let mut body = vec![];
        let mut code = CodeBuilder::new();

        loop {
            if let Some(node) = self.parse_top_level(arena) {
                code.node(NodeKind::TopLevel(node));
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

        let program = arena.alloc(Program::new(arena, body, code.build(arena)));

        semantic::analyze(arena, program);

        program
    }

    fn parse_top_level(&mut self, arena: &'a BumpaloArena) -> Option<&'a TopLevel<'a>> {
        self.debug_trace("parse_top_level");

        let mut code = CodeBuilder::new();

        // Type declaration
        let kind = if let Some(node) = self.parse_struct_definition(arena) {
            code.node(NodeKind::StructDefinition(node));
            TopLevelKind::StructDefinition(node)
        }
        // Function
        else if let Some(node) = self.parse_function(arena) {
            code.node(NodeKind::FunctionDefinition(node));
            TopLevelKind::FunctionDefinition(node)
        }
        // Body for main function
        else if let Some(node) = self.parse_stmt(arena) {
            code.node(NodeKind::Statement(node));
            TopLevelKind::Statement(node)
        }
        // none
        else {
            return None;
        };

        Some(arena.alloc(TopLevel::new(kind, code.build(arena))))
    }

    fn parse_struct_definition(
        &mut self,
        arena: &'a BumpaloArena,
    ) -> Option<&'a StructDefinition<'a>> {
        self.debug_trace("parse_struct_definition");

        let mut code = CodeBuilder::new();

        // struct
        code.interpret(self.expect_token(TokenKind::Struct)?);

        // name
        let mut struct_name = None;

        loop {
            match self.tokenizer.peek_kind() {
                TokenKind::Identifier(_) => {
                    let name = self.parse_name(arena).unwrap();

                    code.node(NodeKind::Identifier(name));
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
        let fields = self._parse_elements(
            arena,
            '{',
            '}',
            &mut code,
            Parser::parse_type_field,
            NodeKind::TypeField,
        );

        let definition = arena.alloc(StructDefinition::new(
            arena,
            struct_name,
            fields,
            code.build(arena),
        ));
        Some(definition)
    }

    fn parse_function(&mut self, arena: &'a BumpaloArena) -> Option<&'a FunctionDefinition<'a>> {
        self.debug_trace("parse_function");

        let mut code = CodeBuilder::new();

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

                    code.node(NodeKind::Identifier(name));
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
        let parameters = self._parse_elements(
            arena,
            '(',
            ')',
            &mut code,
            Parser::parse_function_parameter,
            NodeKind::FunctionParameter,
        );

        // return type
        let mut return_type_annotation = None;

        if let Some(token) = self.expect_token(TokenKind::RightArrow) {
            code.interpret(token);

            return_type_annotation = self.parse_type_annotation(arena);
        }

        // To reduce ambiguity, a function signature must by followed by a newline.
        self.tokenizer.peek();

        if !self.tokenizer.is_newline_seen() {
            code.missing(
                self.tokenizer.current_insertion_range(),
                MissingTokenKind::LineSeparator,
            );
        }

        // body
        let body = self._read_block(arena, &[TokenKind::End]);

        code.node(NodeKind::Block(body));
        code.interpret(self.tokenizer.next_token()); // end

        Some(arena.alloc(FunctionDefinition::new(
            arena,
            function_name,
            parameters,
            return_type_annotation,
            body,
            code.build(arena),
        )))
    }

    fn parse_function_parameter(
        &mut self,
        arena: &'a BumpaloArena,
    ) -> Option<&'a FunctionParameter<'a>> {
        let name = self.parse_name(arena)?;

        let mut code = CodeBuilder::new();
        let mut type_annotation = None;

        code.node(NodeKind::Identifier(name));

        if let Some(token) = self.expect_token(TokenKind::Char(':')) {
            code.interpret(token);
            type_annotation = self.parse_type_annotation(arena);
        }

        if let Some(ref annotation) = type_annotation {
            code.node(NodeKind::TypeAnnotation(annotation));
        } else {
            code.missing(
                self.tokenizer.current_insertion_range(),
                MissingTokenKind::TypeAnnotation,
            );
        }

        let param = FunctionParameter::new(arena, name, type_annotation, code.build(arena));
        Some(arena.alloc(param))
    }

    fn parse_type_field(&mut self, arena: &'a BumpaloArena) -> Option<&'a TypeField<'a>> {
        // To prevent reading too many unnecessary tokens,
        // we should not skip tokens here.
        let mut code = CodeBuilder::new();

        let name = self.parse_name(arena);

        if let Some(ref name) = name {
            code.node(NodeKind::Identifier(name));
        } else {
            code.missing(
                self.tokenizer.current_insertion_range(),
                MissingTokenKind::FieldName,
            );
        }

        code.interpret(self.expect_token(TokenKind::Char(':'))?);

        let annotation = self.parse_type_annotation(arena);

        if let Some(ref annotation) = annotation {
            code.node(NodeKind::TypeAnnotation(annotation));
        } else {
            code.missing(
                self.tokenizer.current_insertion_range(),
                MissingTokenKind::TypeAnnotation,
            );
        }

        let field = TypeField::new(name, annotation, code.build(arena));
        Some(arena.alloc(field))
    }

    fn parse_struct_field(&mut self, arena: &'a BumpaloArena) -> Option<&'a ValueField<'a>> {
        let name = self.parse_name(arena)?;

        let mut code = CodeBuilder::new();
        code.node(NodeKind::Identifier(name));

        // value can be omitted for struct literal.
        let field = if let Some(separator) = self.expect_token(TokenKind::Char(':')) {
            code.interpret(separator);

            let value = self.parse_expr(arena);

            if let Some(ref value) = value {
                code.node(NodeKind::Expression(value));
            } else {
                code.missing(
                    self.tokenizer.current_insertion_range(),
                    MissingTokenKind::Expression,
                );
            }

            ValueField::new(arena, name, value, code.build(arena))
        } else {
            ValueField::new(arena, name, None, code.build(arena))
        };

        Some(arena.alloc(field))
    }

    fn parse_struct_field_pattern(
        &mut self,
        arena: &'a BumpaloArena,
    ) -> Option<&'a ValueFieldPattern<'a>> {
        let name = self.parse_name(arena)?;

        let mut code = CodeBuilder::new();
        code.node(NodeKind::Identifier(name));

        // value can be omitted for struct literal.
        let field = if let Some(separator) = self.expect_token(TokenKind::Char(':')) {
            code.interpret(separator);

            let value = self.parse_pattern(arena);

            if let Some(ref value) = value {
                code.node(NodeKind::Pattern(value));
            } else {
                code.missing(
                    self.tokenizer.current_insertion_range(),
                    MissingTokenKind::Pattern,
                );
            }

            ValueFieldPattern::new(arena, name, value, code.build(arena))
        } else {
            ValueFieldPattern::new(arena, name, None, code.build(arena))
        };

        Some(arena.alloc(field))
    }

    fn parse_name(&mut self, arena: &'a BumpaloArena) -> Option<&'a Identifier<'a>> {
        if let TokenKind::Identifier(name) = self.tokenizer.peek_kind() {
            let name = name.clone();
            let token = self.tokenizer.next_token();

            Some(arena.alloc(Identifier::new(arena, name, token)))
        } else {
            None
        }
    }

    fn parse_type_annotation(&mut self, arena: &'a BumpaloArena) -> Option<&'a TypeAnnotation<'a>> {
        let mut code = CodeBuilder::new();

        let mut kind = match self.tokenizer.peek_kind() {
            TokenKind::I32 => {
                let token = self.tokenizer.next_token();
                code.interpret(token);
                TypeAnnotationKind::Int32
            }
            TokenKind::Identifier(_) => {
                let name = self.parse_name(arena)?;
                code.node(NodeKind::Identifier(name));
                TypeAnnotationKind::Identifier(name)
            }
            _ => return None,
        };

        // Array
        while let Some(open_bracket) = self.expect_token(TokenKind::Char('[')) {
            code.interpret(open_bracket);

            if let Some(close_bracket) = self.expect_token(TokenKind::Char(']')) {
                code.interpret(close_bracket);
            } else {
                code.missing(
                    self.tokenizer.current_insertion_range(),
                    MissingTokenKind::Char(']'),
                );
            }

            // Regardless of reading a close bracket, we can infer the type is array :-)
            kind = TypeAnnotationKind::ArrayType(arena.alloc(kind));
        }

        let ty = TypeAnnotation::new(arena, kind, code.build(arena));
        Some(arena.alloc(ty))
    }

    fn parse_stmt(&mut self, arena: &'a BumpaloArena) -> Option<&'a Statement<'a>> {
        self.debug_trace("parse_stmt");

        match self.tokenizer.peek_kind() {
            TokenKind::Let => self.parse_variable_declaration_stmt(arena),
            _ => self.parse_stmt_expr(arena),
        }
    }

    fn parse_variable_declaration(
        &mut self,
        arena: &'a BumpaloArena,
    ) -> Option<&'a VariableDeclaration<'a>> {
        self.debug_trace("parse_variable_declaration");

        let mut code = CodeBuilder::new();
        code.interpret(self.tokenizer.next_token()); // Let

        let mut pattern = None;
        let mut init = None;

        if let Some(pat) = self.parse_pattern(arena) {
            code.node(NodeKind::Pattern(pat));
            pattern = Some(pat);
        } else {
            code.missing(
                self.tokenizer.current_insertion_range(),
                MissingTokenKind::Pattern,
            );
        }

        code.interpret(self.expect_token(TokenKind::Char('='))?);

        if let Some(expr) = self.parse_expr(arena) {
            code.node(NodeKind::Expression(expr));
            init = Some(expr);
        } else {
            code.missing(
                self.tokenizer.current_insertion_range(),
                MissingTokenKind::Expression,
            );
        }

        let decl = VariableDeclaration::new(pattern, init, code.build(arena));

        Some(arena.alloc(decl))
    }

    fn parse_variable_declaration_stmt(
        &mut self,
        arena: &'a BumpaloArena,
    ) -> Option<&'a Statement<'a>> {
        self.debug_trace("parse_variable_declaration_stmt");

        let decl = self.parse_variable_declaration(arena)?;
        Some(arena.alloc(Statement::new(StatementKind::VariableDeclaration(decl))))
    }

    fn parse_stmt_expr(&mut self, arena: &'a BumpaloArena) -> Option<&'a Statement<'a>> {
        self.debug_trace("parse_stmt_expr");

        let expr = self.parse_expr(arena)?;
        Some(arena.alloc(Statement::new(StatementKind::Expression(expr))))
    }

    fn parse_expr(&mut self, arena: &'a BumpaloArena) -> Option<&'a Expression<'a>> {
        self.debug_trace("parse_expr");
        self.parse_rel_op1(arena)
    }

    fn parse_rel_op1(&mut self, arena: &'a BumpaloArena) -> Option<&'a Expression<'a>> {
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

    fn parse_rel_op2(&mut self, arena: &'a BumpaloArena) -> Option<&'a Expression<'a>> {
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

    fn parse_binary_op1(&mut self, arena: &'a BumpaloArena) -> Option<&'a Expression<'a>> {
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

    fn parse_binary_op2(&mut self, arena: &'a BumpaloArena) -> Option<&'a Expression<'a>> {
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

    fn parse_unary_op(&mut self, arena: &'a BumpaloArena) -> Option<&'a Expression<'a>> {
        self.debug_trace("parse_unary_op");

        let operator = match self.tokenizer.peek_kind() {
            TokenKind::Char('+') => UnaryOperator::Plus,
            TokenKind::Char('-') => UnaryOperator::Minus,
            _ => return self.parse_access(arena),
        };

        // unary operators are right associative.
        let mut code = CodeBuilder::new();
        code.interpret(self.tokenizer.next_token());

        let mut operand = None;

        loop {
            if let Some(node) = self.parse_unary_op(arena) {
                code.node(NodeKind::Expression(node));
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
        let expr = arena.alloc(UnaryExpression::new(
            arena,
            operator,
            operand,
            code.build(arena),
        ));

        Some(arena.alloc(Expression::new(ExpressionKind::UnaryExpression(expr))))
    }

    fn parse_access(&mut self, arena: &'a BumpaloArena) -> Option<&'a Expression<'a>> {
        self.debug_trace("parse_access");

        let mut operand = self.parse_primary(arena)?;

        loop {
            let mut code = CodeBuilder::new();
            code.node(NodeKind::Expression(operand));

            // To distinguish `x\n[...]` and `x[...]`, we have to capture
            // `tokenizer.is_newline_seen()`, so try to advance tokenizer.
            self.tokenizer.peek();

            if self.tokenizer.is_newline_seen() {
                break;
            }

            let token = self.tokenizer.peek();

            let kind = match token.kind {
                TokenKind::Char('[') => {
                    let arguments = self._parse_elements(
                        arena,
                        '[',
                        ']',
                        &mut code,
                        Parser::parse_expr,
                        NodeKind::Expression,
                    );

                    let node = arena.alloc(SubscriptExpression::new(
                        arena,
                        operand,
                        arguments,
                        code.build(arena),
                    ));
                    ExpressionKind::SubscriptExpression(node)
                }
                TokenKind::Char('(') => {
                    let arguments = self._parse_elements(
                        arena,
                        '(',
                        ')',
                        &mut code,
                        Parser::parse_expr,
                        NodeKind::Expression,
                    );

                    let node = arena.alloc(CallExpression::new(
                        arena,
                        operand,
                        arguments,
                        code.build(arena),
                    ));
                    ExpressionKind::CallExpression(node)
                }
                TokenKind::Char('.') => {
                    code.interpret(self.tokenizer.next_token());

                    let field = self.parse_name(arena);

                    if let Some(ref field) = field {
                        code.node(NodeKind::Identifier(field));
                    } else {
                        code.missing(
                            self.tokenizer.current_insertion_range(),
                            MissingTokenKind::FieldName,
                        );
                    }

                    let node = arena.alloc(MemberExpression::new(
                        arena,
                        operand,
                        field,
                        code.build(arena),
                    ));
                    ExpressionKind::MemberExpression(node)
                }
                _ => break,
            };

            operand = arena.alloc(Expression::new(kind));
        }

        Some(operand)
    }

    fn parse_primary(&mut self, arena: &'a BumpaloArena) -> Option<&'a Expression<'a>> {
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

        Some(node)
    }

    fn parse_pattern(&mut self, arena: &'a BumpaloArena) -> Option<&'a Pattern<'a>> {
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

        Some(pattern)
    }

    fn _read_integer(&mut self, arena: &'a BumpaloArena) -> &'a IntegerLiteral<'a> {
        let token = self.tokenizer.next_token();

        if let TokenKind::Integer(i) = token.kind {
            arena.alloc(IntegerLiteral::new(arena, i, token))
        } else {
            unreachable!()
        }
    }

    fn read_integer(&mut self, arena: &'a BumpaloArena) -> &'a Expression<'a> {
        let literal = self._read_integer(arena);

        arena.alloc(Expression::new(ExpressionKind::IntegerLiteral(literal)))
    }

    fn read_integer_pattern(&mut self, arena: &'a BumpaloArena) -> &'a Pattern<'a> {
        let literal = self._read_integer(arena);

        arena.alloc(Pattern::new(PatternKind::IntegerPattern(literal)))
    }

    fn read_identifier(&mut self, arena: &'a BumpaloArena) -> &'a Expression<'a> {
        let id = self.parse_name(arena).unwrap();

        let expr = if *self.tokenizer.peek_kind() == TokenKind::Char('{') {
            let mut code = CodeBuilder::new();
            code.node(NodeKind::Identifier(id));

            let fields = self._parse_elements(
                arena,
                '{',
                '}',
                &mut code,
                Parser::parse_struct_field,
                NodeKind::ValueField,
            );

            let literal = arena.alloc(StructLiteral::new(arena, id, fields, code.build(arena)));
            Expression::new(ExpressionKind::StructLiteral(literal))
        } else {
            let expr = arena.alloc(VariableExpression::new(arena, id));
            Expression::new(ExpressionKind::VariableExpression(expr))
        };

        arena.alloc(expr)
    }

    fn read_identifier_pattern(&mut self, arena: &'a BumpaloArena) -> &'a Pattern<'a> {
        let id = self.parse_name(arena).unwrap();

        let kind = if *self.tokenizer.peek_kind() == TokenKind::Char('{') {
            let mut code = CodeBuilder::new();
            code.node(NodeKind::Identifier(id));

            let fields = self._parse_elements(
                arena,
                '{',
                '}',
                &mut code,
                Parser::parse_struct_field_pattern,
                NodeKind::ValueFieldPattern,
            );

            let pattern = arena.alloc(StructPattern::new(arena, id, fields, code.build(arena)));
            PatternKind::StructPattern(pattern)
        } else {
            let pattern = arena.alloc(VariablePattern::new(arena, id));
            PatternKind::VariablePattern(pattern)
        };

        arena.alloc(Pattern::new(kind))
    }

    fn _read_string(&mut self, arena: &'a BumpaloArena) -> &'a StringLiteral<'a> {
        let start_token = self.tokenizer.next_token(); // StringStart

        let mut code = CodeBuilder::new();
        code.interpret(start_token);

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

        let value = if has_error { None } else { Some(string) };

        arena.alloc(StringLiteral::new(arena, value, code.build(arena)))
    }

    fn read_string(&mut self, arena: &'a BumpaloArena) -> &'a Expression<'a> {
        let string = self._read_string(arena);

        arena.alloc(Expression::new(ExpressionKind::StringLiteral(string)))
    }

    fn read_string_pattern(&mut self, arena: &'a BumpaloArena) -> &'a Pattern<'a> {
        let string = self._read_string(arena);
        arena.alloc(Pattern::new(PatternKind::StringPattern(string)))
    }

    fn read_paren(&mut self, arena: &'a BumpaloArena) -> &'a Expression<'a> {
        let expr = self.read_grouped_expression(arena);

        arena.alloc(Expression::new(ExpressionKind::GroupedExpression(expr)))
    }

    fn read_grouped_expression(&mut self, arena: &'a BumpaloArena) -> &'a GroupedExpression<'a> {
        let mut code = CodeBuilder::new();
        code.interpret(self.tokenizer.next_token()); // "("

        let node = self.parse_expr(arena);

        if let Some(ref node) = node {
            code.node(NodeKind::Expression(node));
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
        arena.alloc(GroupedExpression::new(arena, node, code.build(arena)))
    }

    fn read_array(&mut self, arena: &'a BumpaloArena) -> &'a Expression<'a> {
        let mut code = CodeBuilder::new();
        let elements = self._parse_elements(
            arena,
            '[',
            ']',
            &mut code,
            Parser::parse_expr,
            NodeKind::Expression,
        );

        let expr = arena.alloc(ArrayExpression::new(arena, elements, code.build(arena)));

        arena.alloc(Expression::new(ExpressionKind::ArrayExpression(expr)))
    }

    fn read_array_pattern(&mut self, arena: &'a BumpaloArena) -> &'a Pattern<'a> {
        let mut code = CodeBuilder::new();
        let elements = self._parse_elements(
            arena,
            '[',
            ']',
            &mut code,
            Parser::parse_pattern,
            NodeKind::Pattern,
        );

        let pattern = arena.alloc(ArrayPattern::new(arena, elements, code.build(arena)));

        arena.alloc(Pattern::new(PatternKind::ArrayPattern(pattern)))
    }

    fn read_rest_pattern(&mut self, arena: &'a BumpaloArena) -> &'a Pattern<'a> {
        let mut code = CodeBuilder::new();
        code.interpret(self.tokenizer.next_token()); // "..."

        let name = self.parse_name(arena);

        let variable_pattern = if let Some(node) = name {
            let variable_pattern: &VariablePattern<'_> =
                arena.alloc(VariablePattern::new(arena, node));

            code.node(NodeKind::VariablePattern(variable_pattern));
            Some(variable_pattern)
        } else {
            None
        };

        let pattern = arena.alloc(RestPattern::new(arena, variable_pattern, code.build(arena)));

        arena.alloc(Pattern::new(PatternKind::RestPattern(pattern)))
    }

    fn read_if_expression(&mut self, arena: &'a BumpaloArena) -> &'a Expression<'a> {
        let mut code = CodeBuilder::new();
        code.interpret(self.tokenizer.next_token()); // "if"

        let condition = self._parse_optional_item(
            arena,
            &mut code,
            Parser::parse_expr,
            NodeKind::Expression,
            MissingTokenKind::Expression,
        );

        // body
        let then_body = self._read_block(arena, &[TokenKind::End, TokenKind::Else]);
        let has_else = *self.tokenizer.peek_kind() == TokenKind::Else;

        code.node(NodeKind::Block(then_body));
        code.interpret(self.tokenizer.next_token()); // "else" or "end"

        let else_body = if has_else {
            let else_body = self._read_block(arena, &[TokenKind::End]);

            code.node(NodeKind::Block(else_body));
            code.interpret(self.tokenizer.next_token()); //  "end"

            Some(else_body)
        } else {
            None
        };

        let expr = arena.alloc(IfExpression::new(
            arena,
            condition,
            then_body,
            else_body,
            code.build(arena),
        ));

        arena.alloc(Expression::new(ExpressionKind::IfExpression(expr)))
    }

    fn read_case_expression(&mut self, arena: &'a BumpaloArena) -> &'a Expression<'a> {
        // case ...
        let mut code = CodeBuilder::new();
        code.interpret(self.tokenizer.next_token()); // "case"

        let head = self._parse_optional_item(
            arena,
            &mut code,
            Parser::parse_expr,
            NodeKind::Expression,
            MissingTokenKind::Expression,
        );

        // arms
        let mut arms = vec![];
        let mut else_body = None;

        loop {
            match self.tokenizer.peek_kind() {
                TokenKind::When => {
                    let arm = self.read_case_arm(arena);

                    code.node(NodeKind::CaseArm(arm));
                    arms.push(arm);
                }
                TokenKind::Else => {
                    code.interpret(self.tokenizer.next_token());

                    let block = self._read_block(arena, &[TokenKind::End]);
                    code.node(NodeKind::Block(block));

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

        let expr = arena.alloc(CaseExpression::new(
            arena,
            head,
            arms,
            else_body,
            code.build(arena),
        ));

        arena.alloc(Expression::new(ExpressionKind::CaseExpression(expr)))
    }

    fn read_case_arm(&mut self, arena: &'a BumpaloArena) -> &'a CaseArm<'a> {
        let mut code = CodeBuilder::new();

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
                NodeKind::Pattern,
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
                NodeKind::Expression,
                MissingTokenKind::Expression,
            );
        }

        let then_body =
            self._read_block(arena, &[TokenKind::When, TokenKind::Else, TokenKind::End]);
        code.node(NodeKind::Block(then_body));

        arena.alloc(CaseArm::new(
            arena,
            pattern,
            guard,
            then_body,
            code.build(arena),
        ))
    }

    /// Reads statements until it meets a token listed in `stop_tokens`.
    /// But this function doesn't consume a stop token itself, consuming
    /// a stop token is caller's responsibility.
    fn _read_block(&mut self, arena: &'a BumpaloArena, stop_tokens: &[TokenKind]) -> &'a Block<'a> {
        let mut code = CodeBuilder::new();

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

                code.node(NodeKind::Statement(stmt));
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

        arena.alloc(Block::new(arena, body, code.build(arena)))
    }

    fn _parse_optional_item<T>(
        &mut self,
        arena: &'a BumpaloArena,
        code: &mut CodeBuilder<'a>,
        node_parser: fn(&mut Parser<'a, 't>, &'a BumpaloArena) -> Option<&'a T>,
        kind_builder: fn(&'a T) -> NodeKind<'a>,
        missing_token: MissingTokenKind,
    ) -> Option<&'a T> {
        let node = node_parser(self, arena);

        if let Some(ref node) = node {
            code.node(kind_builder(node));
        } else {
            code.missing(self.tokenizer.current_insertion_range(), missing_token);
        }

        node
    }

    /// Read comma-separated elements from the start character token specified by `open_char` to
    /// the end character token or EOF specified by `close_char`.
    fn _parse_elements<T>(
        &mut self,
        arena: &'a BumpaloArena,
        open_char: char,
        close_char: char,
        code: &mut CodeBuilder<'a>,
        element_parser: fn(&mut Parser<'a, 't>, &'a BumpaloArena) -> Option<&'a T>,
        kind_builder: fn(&'a T) -> NodeKind<'a>,
    ) -> Vec<&'a T> {
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

                        code.node(kind_builder(expr));
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
                    code.node(kind_builder(argument));
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
        arena: &'a BumpaloArena,
        next_parser: fn(&mut Parser<'a, 't>, &'a BumpaloArena) -> Option<&'a Expression<'a>>,
        operators: &[(TokenKind, BinaryOperator)],
    ) -> Option<&'a Expression<'a>> {
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
            let mut code = CodeBuilder::new();

            code.node(NodeKind::Expression(lhs)).interpret(op_token);

            loop {
                rhs = next_parser(self, arena);

                if let Some(ref rhs) = rhs {
                    code.node(NodeKind::Expression(rhs));
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
            let expr = arena.alloc(BinaryExpression::new(
                arena,
                operator,
                lhs,
                rhs,
                code.build(arena),
            ));

            lhs = arena.alloc(Expression::new(ExpressionKind::BinaryExpression(expr)));
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
    use super::*;
    use crate::arena::BumpaloArena;
    use crate::syntax::{EffectiveRange, ExpressionKind, SyntaxToken, Token};
    use assert_matches::assert_matches;

    #[test]
    fn number_integer() {
        let arena = BumpaloArena::new();
        let stmt = parse_statement(&arena, "42");

        assert_matches!(
            stmt.expression().unwrap().kind(),
            ExpressionKind::IntegerLiteral(n) => {
                assert_eq!(n.value(), 42);
            }
        );

        let mut code = stmt.expression().unwrap().integer_literal().unwrap().code();
        assert_eq!(code.len(), 1);

        let token = next_interpreted_token(&mut code);
        assert_matches!(token.kind, TokenKind::Integer(42));
    }

    #[test]
    fn incomplete_string() {
        let arena = BumpaloArena::new();
        for src in vec!["\"Fizz\\\"", "\"Fizz\\\"\n"] {
            let stmt = parse_statement(&arena, src);
            let expr = stmt.expression().unwrap();

            assert_matches!(expr.kind(), ExpressionKind::StringLiteral(..));

            let mut tokens = stmt.expression().unwrap().string_literal().unwrap().code();
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
        let arena = BumpaloArena::new();
        for src in vec!["(\"Fizz\\\")", "(\"Fizz\\\")\n"] {
            let stmt = parse_statement(&arena, src);
            let expr = stmt.expression().unwrap();

            assert_matches!(expr.kind(), ExpressionKind::GroupedExpression(expr) => {
                assert_matches!(expr.expression(), Some(expr) => {
                    assert_matches!(expr.kind(), ExpressionKind::StringLiteral(..));
                });

                let mut tokens = expr.code();

                assert_eq!(tokens.len(), 3);

                let token = next_interpreted_token(&mut tokens);
                assert_matches!(token.kind, TokenKind::Char('('));

                let node = next_node(&mut tokens);
                assert_matches!(node, NodeKind::Expression(..));

                let (_, item) = next_missing_token(&mut tokens);
                assert_eq!(item, MissingTokenKind::Char(')'));
            });
        }
    }

    #[test]
    fn add_integer() {
        let arena = BumpaloArena::new();
        let stmt = parse_statement(&arena, "1+2");
        let expr = stmt.expression().unwrap().binary_expression().unwrap();

        assert_eq!(expr.operator(), BinaryOperator::Add);
        assert_matches!(
            expr.lhs().kind(),
            ExpressionKind::IntegerLiteral(n) => {
                assert_eq!(n.value(), 1);
            }
        );
        assert_matches!(
            expr.rhs().unwrap().kind(),
            ExpressionKind::IntegerLiteral(n) => {
                assert_eq!(n.value(), 2);
            }
        );

        let mut tokens = stmt
            .expression()
            .unwrap()
            .binary_expression()
            .unwrap()
            .code();
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
        let arena = BumpaloArena::new();
        let stmt = parse_statement(&arena, "1+");
        let expr = stmt.expression().unwrap().binary_expression().unwrap();

        assert_eq!(expr.operator(), BinaryOperator::Add);
        assert_matches!(
            expr.lhs().kind(),
            ExpressionKind::IntegerLiteral(n) => {
                assert_eq!(n.value(), 1);
            }
        );
        assert!(expr.rhs().is_none());

        let mut tokens = stmt
            .expression()
            .unwrap()
            .binary_expression()
            .unwrap()
            .code();
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
        let arena = BumpaloArena::new();
        let stmt = parse_statement(&arena, "1 + % ? 2");
        let expr = stmt.expression().unwrap().binary_expression().unwrap();

        assert_eq!(expr.operator(), BinaryOperator::Add);
        assert_matches!(
            expr.lhs().kind(),
            ExpressionKind::IntegerLiteral(n) => {
                assert_eq!(n.value(), 1);
            }
        );
        assert_matches!(
            expr.rhs().unwrap().kind(),
            ExpressionKind::IntegerLiteral(n) => {
                assert_eq!(n.value(), 2);
            }
        );

        let mut tokens = stmt
            .expression()
            .unwrap()
            .binary_expression()
            .unwrap()
            .code();

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
        let arena = BumpaloArena::new();
        let stmt = parse_statement(&arena, "-1");
        let expr = stmt.expression().unwrap().unary_expression().unwrap();

        assert_eq!(expr.operator(), UnaryOperator::Minus);
        assert_matches!(
            expr.operand().unwrap().kind(),
            ExpressionKind::IntegerLiteral(n) => {
                assert_eq!(n.value(), 1);
            }
        );

        let mut tokens = stmt
            .expression()
            .unwrap()
            .unary_expression()
            .unwrap()
            .code();
        assert_eq!(tokens.len(), 2);

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('-'));

        let node = next_node(&mut tokens);
        assert!(node.is_expression());
    }

    #[test]
    fn unary_op_nested() {
        let arena = BumpaloArena::new();
        let stmt = parse_statement(&arena, "-+1");
        let expr = stmt.expression().unwrap().unary_expression().unwrap();

        assert_matches!(expr, UnaryExpression { .. } => {
            assert_eq!(expr.operator(), UnaryOperator::Minus);

            let operand = expr.operand().unwrap().unary_expression().unwrap();

            assert_matches!(operand, UnaryExpression { .. } => {
                assert_eq!(operand.operator(), UnaryOperator::Plus);

                assert_matches!(
                    operand.operand().unwrap().kind(),
                    ExpressionKind::IntegerLiteral(n) => {
                        assert_eq!(n.value(), 1);
                    }
                );
            });
        });

        let mut tokens = stmt
            .expression()
            .unwrap()
            .unary_expression()
            .unwrap()
            .code();
        assert_eq!(tokens.len(), 2);

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('-'));

        let node = next_node(&mut tokens);
        assert!(node.is_expression());
    }

    #[test]
    fn subscript_index() {
        let arena = BumpaloArena::new();
        let stmt = parse_statement(&arena, "a[0]");
        let expr = stmt.expression().unwrap().subscript_expression().unwrap();

        assert_matches!(expr, SubscriptExpression{ .. } => {
            let id = expr.callee().variable_expression();
            assert!(id.is_some());

            let id = id.unwrap();
            assert_eq!(id.name(), "a");

            let arguments = expr.arguments().collect::<Vec<_>>();
            assert_eq!(arguments.len(), 1);
            assert_matches!(
                arguments[0].kind(),
                ExpressionKind::IntegerLiteral(n) => {
                    assert_eq!(n.value(), 0);
                }
            );
        });

        let mut tokens = stmt
            .expression()
            .unwrap()
            .subscript_expression()
            .unwrap()
            .code();
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
        let arena = BumpaloArena::new();
        let stmt = parse_statement(&arena, "a[]");
        let expr = stmt.expression().unwrap().subscript_expression().unwrap();

        assert_matches!(expr, SubscriptExpression{ .. } => {
            let id = expr.callee().variable_expression();
            assert!(id.is_some());

            let id = id.unwrap();
            assert_eq!(id.name(), "a");

            let arguments = expr.arguments().collect::<Vec<_>>();
            assert_eq!(arguments.len(), 0);
        });

        let mut tokens = stmt
            .expression()
            .unwrap()
            .subscript_expression()
            .unwrap()
            .code();
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
        let arena = BumpaloArena::new();
        let stmt = parse_statement(&arena, "a[1\nb");
        let expr = stmt.expression().unwrap().subscript_expression().unwrap();

        assert_matches!(expr, SubscriptExpression{ .. } => {
            let id = expr.callee().variable_expression();
            assert!(id.is_some());

            let id = id.unwrap();
            assert_eq!(id.name(), "a");

            let arguments = expr.arguments().collect::<Vec<_>>();
            assert_eq!(arguments.len(), 1);
            assert_matches!(
                arguments[0].kind(),
                ExpressionKind::IntegerLiteral(n) => {
                    assert_eq!(n.value(), 1);
                }
            );
        });

        let mut tokens = stmt
            .expression()
            .unwrap()
            .subscript_expression()
            .unwrap()
            .code();

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
        let arena = BumpaloArena::new();
        for src in vec!["a[\"", "a[\"\n"] {
            let stmt = parse_statement(&arena, src);
            let expr = stmt.expression().unwrap().subscript_expression().unwrap();

            assert_matches!(expr, SubscriptExpression{ .. } => {
                let arguments = expr.arguments().collect::<Vec<_>>();
                assert_eq!(arguments.len(), 1);
                assert_matches!(arguments[0].kind(), ExpressionKind::StringLiteral(..));
            });

            let mut tokens = stmt
                .expression()
                .unwrap()
                .subscript_expression()
                .unwrap()
                .code();
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
        let arena = BumpaloArena::new();
        let stmt = parse_statement(&arena, "[]");
        let expr = stmt.expression().unwrap().array_expression().unwrap();

        assert_matches!(expr, ArrayExpression{ .. } => {
            let elements = expr.elements().collect::<Vec<_>>();
            assert_eq!(elements.len(), 0);
        });

        let mut tokens = stmt
            .expression()
            .unwrap()
            .array_expression()
            .unwrap()
            .code();
        assert_eq!(tokens.len(), 2);

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('['));

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char(']'));
    }

    #[test]
    fn array_one_element_and_trailing_comma() {
        let arena = BumpaloArena::new();
        let stmt = parse_statement(&arena, "[1,]");
        let expr = stmt.expression().unwrap().array_expression().unwrap();

        assert_matches!(expr, ArrayExpression{ .. } => {
            let elements = expr.elements().collect::<Vec<_>>();
            assert_eq!(elements.len(), 1);

            assert_eq!(elements.len(), 1);
            assert_matches!(
                elements[0].kind(),
                ExpressionKind::IntegerLiteral(n) => {
                    assert_eq!(n.value(), 1);
                }
            );
        });

        let mut tokens = stmt
            .expression()
            .unwrap()
            .array_expression()
            .unwrap()
            .code();
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
        let arena = BumpaloArena::new();
        let stmt = parse_statement(
            &arena,
            "if x > 0
                10
            else
                20
            end",
        );
        let expr = stmt.expression().unwrap().if_expression().unwrap();

        assert_matches!(expr, IfExpression { .. } => {
            let condition = expr.condition();
            let else_body = expr.else_body();

            let condition = condition.as_ref().unwrap();

            assert_matches!(condition.kind(), ExpressionKind::BinaryExpression(..));
            assert!(else_body.is_some());
        });
    }

    #[test]
    fn if_expression_missing_condition() {
        let arena = BumpaloArena::new();
        let stmt = parse_statement(&arena, "if\nend");
        let expr = stmt.expression().unwrap().if_expression().unwrap();

        assert_matches!(expr, IfExpression { .. } => {
            let condition = expr.condition();
            let then_body = expr.then_body();
            let else_body = expr.else_body();

            assert!(condition.is_none());
            assert!(else_body.is_none());

            let stmts = then_body.statements();
            assert_eq!(stmts.len(), 0);
        });
    }

    #[test]
    fn if_expression_missing_newline() {
        let arena = BumpaloArena::new();
        let stmt = parse_statement(&arena, "if b x end");

        assert!(stmt.expression().unwrap().if_expression().is_some());

        // tokens
        let mut tokens = stmt.expression().unwrap().if_expression().unwrap().code();
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

    #[test]
    fn case_expression() {
        let arena = BumpaloArena::new();
        let stmt = parse_statement(
            &arena,
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
        let expr = stmt.expression().unwrap().case_expression().unwrap();

        assert_matches!(expr, CaseExpression { .. } => {
            let head = expr.head();
            let arms: Vec<_> = expr.arms().collect();
            let else_body = expr.else_body();

            assert!(head.is_some());
            assert!(!arms.is_empty());

            // when 123
            assert!(arms[0].pattern().is_some());
            assert!(arms[0].guard().is_none());
            assert_matches!(arms[0].pattern().unwrap().kind(), PatternKind::IntegerPattern(..));

            // when \"string\"
            assert!(arms[1].pattern().is_some());
            assert!(arms[1].guard().is_none());
            assert_matches!(arms[1].pattern().unwrap().kind(), PatternKind::StringPattern(..));

            // when y
            assert!(arms[2].pattern().is_some());
            assert!(arms[2].guard().is_none());
            assert_matches!(arms[2].pattern().unwrap().kind(), PatternKind::VariablePattern(..));

            // when [1, x]
            assert!(arms[3].pattern().is_some());
            assert!(arms[3].guard().is_none());
            assert_matches!(arms[3].pattern().unwrap().kind(), PatternKind::ArrayPattern(..));

            // when x if x > 10
            assert!(arms[4].pattern().is_some());
            assert!(arms[4].guard().is_some());
            assert_matches!(arms[4].pattern().unwrap().kind(), PatternKind::VariablePattern(..));

            assert!(else_body.is_some());
        });
    }

    // --- helpers

    fn parse_statement<'a>(arena: &'a BumpaloArena, src: &'a str) -> &'a Statement<'a> {
        let module = Parser::parse_string(arena, src);

        assert_ne!(module.body().len(), 0);
        module.body().next().unwrap().statement().unwrap()
    }

    fn next_node<'a, 'b>(tokens: &'a mut CodeKindIter<'_, 'b>) -> &'a NodeKind<'b> {
        unwrap_node(tokens.next().unwrap())
    }

    fn next_interpreted_token<'a>(tokens: &'a mut CodeKindIter<'_, '_>) -> &'a Token {
        unwrap_interpreted_token(tokens.next().unwrap())
    }

    fn next_missing_token(tokens: &mut CodeKindIter<'_, '_>) -> (EffectiveRange, MissingTokenKind) {
        unwrap_missing_token(tokens.next().unwrap())
    }

    fn next_skipped_token<'a>(
        tokens: &'a mut CodeKindIter<'_, '_>,
    ) -> (&'a Token, MissingTokenKind) {
        unwrap_skipped_token(tokens.next().unwrap())
    }

    fn unwrap_node<'a, 'b>(kind: &'a CodeKind<'b>) -> &'a NodeKind<'b> {
        if let CodeKind::Node(node) = kind {
            return node;
        }

        panic!("expected child node");
    }

    fn unwrap_interpreted_token<'a>(kind: &'a CodeKind<'_>) -> &'a Token {
        if let CodeKind::SyntaxToken(token) = kind {
            if let SyntaxToken::Interpreted(token) = token {
                return token;
            }
        }

        panic!("expected interpreted token");
    }

    fn unwrap_missing_token(kind: &CodeKind<'_>) -> (EffectiveRange, MissingTokenKind) {
        if let CodeKind::SyntaxToken(token) = kind {
            if let SyntaxToken::Missing { range, item } = token {
                return (range.clone(), item.clone());
            }
        }

        panic!("expected missing token");
    }

    fn unwrap_skipped_token<'a>(kind: &'a CodeKind<'_>) -> (&'a Token, MissingTokenKind) {
        if let CodeKind::SyntaxToken(token) = kind {
            if let SyntaxToken::Skipped { token, expected } = token {
                return (token, *expected);
            }
        }

        panic!("expected missing token");
    }
}
