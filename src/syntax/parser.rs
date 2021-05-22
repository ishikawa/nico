use super::*;
use crate::util::naming::PrefixNaming;
use crate::util::wrap;
use crate::{sem, syntax::binding};
use bumpalo::collections::String as BumpaloString;

const DEBUG: bool = false;

#[derive(Debug)]
pub struct Parser<'a> {
    /// The filename, uri of a source code.
    source_name: BumpaloString<'a>,
    tokenizer: Tokenizer<'a>,
    naming: PrefixNaming,
}

impl<'a> Parser<'a> {
    pub fn new<S: AsRef<str>>(tree: &'a Ast, tokenizer: Tokenizer<'a>, source_name: S) -> Self {
        Self {
            tokenizer,
            source_name: BumpaloString::from_str_in(source_name.as_ref(), tree.arena()),
            naming: PrefixNaming::new("?"),
        }
    }

    pub fn source_name(&self) -> &str {
        self.source_name.as_str()
    }
}

impl<'a> Parser<'a> {
    pub fn parse_string<S: AsRef<str> + 'a>(tree: &'a Ast, src: S) -> &'a Program<'a> {
        let tokenizer = Tokenizer::from_string(src);
        let mut parser = Parser::new(tree, tokenizer, "-");

        parser.parse(tree)
    }

    pub fn parse(&mut self, tree: &'a Ast) -> &'a Program<'a> {
        let mut body = vec![];
        let mut code = Code::new(tree);

        loop {
            // Type declaration
            if let Some(node) = self.parse_struct_definition(tree) {
                code.node(NodeKind::StructDefinition(node));
                body.push(TopLevelKind::StructDefinition(node));
            }
            // Function
            else if let Some(node) = self.parse_function(tree) {
                code.node(NodeKind::FunctionDefinition(node));
                body.push(TopLevelKind::FunctionDefinition(node));
            }
            // Body for main function
            else if let Some(node) = self.parse_stmt(tree) {
                code.node(NodeKind::Statement(node));
                body.push(TopLevelKind::Statement(node));
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

        let program = tree.alloc(Program::new(tree, body, code));

        binding::bind(program);

        program
    }

    fn parse_struct_definition(&mut self, tree: &'a Ast) -> Option<&'a StructDefinition<'a>> {
        self.debug_trace("parse_struct_definition");

        let mut code = Code::new(tree);

        // struct
        code.interpret(self.expect_token(TokenKind::Struct)?);

        // name
        let mut struct_name = None;

        loop {
            match self.tokenizer.peek_kind() {
                TokenKind::Identifier(_) => {
                    let name = self.parse_name(tree).unwrap();

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
            tree,
            '{',
            '}',
            &mut code,
            Parser::parse_type_field,
            NodeKind::TypeField,
        );

        let definition = tree.alloc(StructDefinition::new(tree, struct_name, fields, code));
        Some(definition)
    }

    fn parse_function(&mut self, tree: &'a Ast) -> Option<&'a FunctionDefinition<'a>> {
        self.debug_trace("parse_function");

        let mut code = Code::new(tree);

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
                    let name = self.parse_name(tree).unwrap();

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
            tree,
            '(',
            ')',
            &mut code,
            Parser::parse_function_parameter,
            NodeKind::FunctionParameter,
        );

        // body
        let body = self._read_block(tree, &[TokenKind::End]);

        code.node(NodeKind::Block(body));
        code.interpret(self.tokenizer.next_token()); // end

        Some(tree.alloc(FunctionDefinition::new(
            tree,
            function_name,
            parameters,
            body,
            code,
        )))
    }

    fn parse_function_parameter(&mut self, tree: &'a Ast) -> Option<&'a FunctionParameter<'a>> {
        if let Some(name) = self.parse_name(tree) {
            let code = Code::with_node(tree, NodeKind::Identifier(name));
            Some(tree.alloc(FunctionParameter::new(name, code)))
        } else {
            None
        }
    }

    fn parse_type_field(&mut self, tree: &'a Ast) -> Option<&'a TypeField<'a>> {
        // To prevent reading too many unnecessary tokens,
        // we should not skip tokens here.
        let mut code = Code::new(tree);

        let name = self.parse_name(tree);

        if let Some(ref name) = name {
            code.node(NodeKind::Identifier(name));
        } else {
            code.missing(
                self.tokenizer.current_insertion_range(),
                MissingTokenKind::FieldName,
            );
        }

        code.interpret(self.expect_token(TokenKind::Char(':'))?);

        let annotation = self.parse_type_annotation(tree);

        if let Some(ref annotation) = annotation {
            code.node(NodeKind::TypeAnnotation(annotation));
        } else {
            code.missing(
                self.tokenizer.current_insertion_range(),
                MissingTokenKind::TypeAnnotation,
            );
        }

        let field = TypeField::new(name, annotation, code);

        Some(tree.alloc(field))
    }

    fn parse_struct_field(&mut self, tree: &'a Ast) -> Option<&'a ValueField<'a>> {
        let name = self.parse_name(tree)?;
        let mut code = Code::with_node(tree, NodeKind::Identifier(name));

        // value can be omitted for struct literal.
        let field = if let Some(separator) = self.expect_token(TokenKind::Char(':')) {
            code.interpret(separator);

            let value = self.parse_expr(tree);

            if let Some(ref value) = value {
                code.node(NodeKind::Expression(value));
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

        Some(tree.alloc(field))
    }

    fn parse_struct_field_pattern(&mut self, tree: &'a Ast) -> Option<&'a ValueFieldPattern<'a>> {
        let name = self.parse_name(tree)?;
        let mut code = Code::with_node(tree, NodeKind::Identifier(name));

        // value can be omitted for struct literal.
        let field = if let Some(separator) = self.expect_token(TokenKind::Char(':')) {
            code.interpret(separator);

            let value = self.parse_pattern(tree);

            if let Some(ref value) = value {
                code.node(NodeKind::Pattern(value));
            } else {
                code.missing(
                    self.tokenizer.current_insertion_range(),
                    MissingTokenKind::Pattern,
                );
            }

            ValueFieldPattern::new(tree, name, value, code)
        } else {
            ValueFieldPattern::new(tree, name, None, code)
        };

        Some(tree.alloc(field))
    }

    fn parse_name(&mut self, tree: &'a Ast) -> Option<&'a Identifier<'a>> {
        if let TokenKind::Identifier(name) = self.tokenizer.peek_kind() {
            let name = name.clone();
            let code = Code::with_interpreted(tree, self.tokenizer.next_token());

            Some(tree.alloc(Identifier::new(tree, name, code)))
        } else {
            None
        }
    }

    fn parse_type_annotation(&mut self, tree: &'a Ast) -> Option<&'a TypeAnnotation<'a>> {
        let code = Code::with_interpreted(tree, self.expect_token(TokenKind::I32)?);

        let ty = TypeAnnotation::new(wrap(sem::Type::Int32), code);
        Some(tree.alloc(ty))
    }

    fn parse_stmt(&mut self, tree: &'a Ast) -> Option<&'a Statement<'a>> {
        self.debug_trace("parse_stmt");

        match self.tokenizer.peek_kind() {
            TokenKind::Let => self.parse_variable_declaration_stmt(tree),
            _ => self.parse_stmt_expr(tree),
        }
    }

    fn parse_variable_declaration(&mut self, tree: &'a Ast) -> Option<&'a VariableDeclaration<'a>> {
        self.debug_trace("parse_variable_declaration");

        let mut code = Code::with_interpreted(tree, self.tokenizer.next_token()); // let
        let mut pattern = None;
        let mut init = None;

        if let Some(pat) = self.parse_pattern(tree) {
            code.node(NodeKind::Pattern(pat));
            pattern = Some(pat);
        } else {
            code.missing(
                self.tokenizer.current_insertion_range(),
                MissingTokenKind::Pattern,
            );
        }

        code.interpret(self.expect_token(TokenKind::Char('='))?);

        if let Some(expr) = self.parse_expr(tree) {
            code.node(NodeKind::Expression(expr));
            init = Some(expr);
        } else {
            code.missing(
                self.tokenizer.current_insertion_range(),
                MissingTokenKind::Expression,
            );
        }

        let decl = VariableDeclaration::new(pattern, init, code);

        Some(tree.alloc(decl))
    }

    fn parse_variable_declaration_stmt(&mut self, tree: &'a Ast) -> Option<&'a Statement<'a>> {
        self.debug_trace("parse_variable_declaration_stmt");

        let decl = self.parse_variable_declaration(tree)?;
        let code = Code::with_node(tree, NodeKind::VariableDeclaration(decl));

        Some(tree.alloc(Statement::new(
            StatementKind::VariableDeclaration(decl),
            code,
        )))
    }

    fn parse_stmt_expr(&mut self, tree: &'a Ast) -> Option<&'a Statement<'a>> {
        self.debug_trace("parse_stmt_expr");

        let expr = self.parse_expr(tree)?;
        let code = Code::with_node(tree, NodeKind::Expression(expr));

        Some(tree.alloc(Statement::new(StatementKind::Expression(expr), code)))
    }

    fn parse_expr(&mut self, tree: &'a Ast) -> Option<&'a Expression<'a>> {
        self.debug_trace("parse_expr");
        self.parse_rel_op1(tree)
    }

    fn parse_rel_op1(&mut self, tree: &'a Ast) -> Option<&'a Expression<'a>> {
        self.debug_trace("parse_rel_op1");
        self._parse_binary_op(
            tree,
            Parser::parse_rel_op2,
            &[
                (TokenKind::Eq, BinaryOperator::Eq),
                (TokenKind::Ne, BinaryOperator::Ne),
            ],
        )
    }

    fn parse_rel_op2(&mut self, tree: &'a Ast) -> Option<&'a Expression<'a>> {
        self.debug_trace("parse_rel_op2");
        self._parse_binary_op(
            tree,
            Parser::parse_binary_op1,
            &[
                (TokenKind::Le, BinaryOperator::Le),
                (TokenKind::Ge, BinaryOperator::Ge),
                (TokenKind::Char('<'), BinaryOperator::Lt),
                (TokenKind::Char('>'), BinaryOperator::Gt),
            ],
        )
    }

    fn parse_binary_op1(&mut self, tree: &'a Ast) -> Option<&'a Expression<'a>> {
        self.debug_trace("parse_binary_op1");
        self._parse_binary_op(
            tree,
            Parser::parse_binary_op2,
            &[
                (TokenKind::Char('+'), BinaryOperator::Add),
                (TokenKind::Char('-'), BinaryOperator::Sub),
                (TokenKind::Char('%'), BinaryOperator::Rem),
            ],
        )
    }

    fn parse_binary_op2(&mut self, tree: &'a Ast) -> Option<&'a Expression<'a>> {
        self.debug_trace("parse_binary_op2");
        self._parse_binary_op(
            tree,
            Parser::parse_unary_op,
            &[
                (TokenKind::Char('*'), BinaryOperator::Mul),
                (TokenKind::Char('/'), BinaryOperator::Div),
            ],
        )
    }

    fn parse_unary_op(&mut self, tree: &'a Ast) -> Option<&'a Expression<'a>> {
        self.debug_trace("parse_unary_op");

        let operator = match self.tokenizer.peek_kind() {
            TokenKind::Char('+') => UnaryOperator::Plus,
            TokenKind::Char('-') => UnaryOperator::Minus,
            _ => return self.parse_access(tree),
        };

        // unary operators are right associative.
        let mut code = Code::with_interpreted(tree, self.tokenizer.next_token());
        let mut operand = None;

        loop {
            if let Some(node) = self.parse_unary_op(tree) {
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
        let expr = UnaryExpression::new(operator, operand);
        let kind = ExpressionKind::UnaryExpression(expr);

        Some(tree.alloc(Expression::new(kind, code)))
    }

    fn parse_access(&mut self, tree: &'a Ast) -> Option<&'a Expression<'a>> {
        self.debug_trace("parse_access");

        let mut operand = self.parse_primary(tree)?;

        loop {
            let mut code = Code::with_node(tree, NodeKind::Expression(operand));

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
                        tree,
                        '[',
                        ']',
                        &mut code,
                        Parser::parse_expr,
                        NodeKind::Expression,
                    );

                    ExpressionKind::SubscriptExpression(SubscriptExpression::new(
                        tree, operand, arguments,
                    ))
                }
                TokenKind::Char('(') => {
                    let arguments = self._parse_elements(
                        tree,
                        '(',
                        ')',
                        &mut code,
                        Parser::parse_expr,
                        NodeKind::Expression,
                    );

                    ExpressionKind::CallExpression(CallExpression::new(tree, operand, arguments))
                }
                TokenKind::Char('.') => {
                    code.interpret(self.tokenizer.next_token());

                    let field = self.parse_name(tree);

                    if let Some(ref field) = field {
                        code.node(NodeKind::Identifier(field));
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

            operand = tree.alloc(Expression::new(kind, code));
        }

        Some(operand)
    }

    fn parse_primary(&mut self, tree: &'a Ast) -> Option<&'a Expression<'a>> {
        self.debug_trace("parse_primary");

        let token = self.tokenizer.peek();
        let node = match token.kind {
            TokenKind::Integer(_) => self.read_integer(tree),
            TokenKind::Identifier(_) => self.read_identifier(tree),
            TokenKind::StringStart => self.read_string(tree),
            TokenKind::Char('(') => self.read_paren(tree),
            TokenKind::Char('[') => self.read_array(tree),
            TokenKind::If => self.read_if_expression(tree),
            TokenKind::Case => self.read_case_expression(tree),
            _ => return None,
        };

        Some(node)
    }

    fn parse_pattern(&mut self, tree: &'a Ast) -> Option<&'a Pattern<'a>> {
        self.debug_trace("parse_pattern");

        let token = self.tokenizer.peek();
        let pattern = match token.kind {
            TokenKind::Integer(_) => self.read_integer_pattern(tree),
            TokenKind::Identifier(_) => self.read_identifier_pattern(tree),
            TokenKind::StringStart => self.read_string_pattern(tree),
            TokenKind::Char('[') => self.read_array_pattern(tree),
            TokenKind::Rest => self.read_rest_pattern(tree),
            _ => return None,
        };

        Some(pattern)
    }

    fn _read_integer(&mut self, tree: &'a Ast) -> (IntegerLiteral, Code<'a>) {
        let token = self.tokenizer.next_token();

        if let TokenKind::Integer(i) = token.kind {
            let code = Code::with_interpreted(tree, token);

            (IntegerLiteral::new(i), code)
        } else {
            unreachable!()
        }
    }

    fn read_integer(&mut self, tree: &'a Ast) -> &'a Expression<'a> {
        let (literal, code) = self._read_integer(tree);

        tree.alloc(Expression::new(
            ExpressionKind::IntegerLiteral(literal),
            code,
        ))
    }

    fn read_integer_pattern(&mut self, tree: &'a Ast) -> &'a Pattern<'a> {
        let (literal, code) = self._read_integer(tree);

        tree.alloc(Pattern::new(PatternKind::IntegerPattern(literal), code))
    }

    fn read_identifier(&mut self, tree: &'a Ast) -> &'a Expression<'a> {
        let id = self.parse_name(tree).unwrap();
        let mut code = Code::with_node(tree, NodeKind::Identifier(id));

        let kind = if *self.tokenizer.peek_kind() == TokenKind::Char('{') {
            let fields = self._parse_elements(
                tree,
                '{',
                '}',
                &mut code,
                Parser::parse_struct_field,
                NodeKind::ValueField,
            );

            ExpressionKind::StructLiteral(StructLiteral::new(tree, id, fields))
        } else {
            ExpressionKind::VariableExpression(id)
        };

        tree.alloc(Expression::new(kind, code))
    }

    fn read_identifier_pattern(&mut self, tree: &'a Ast) -> &'a Pattern<'a> {
        let id = self.parse_name(tree).unwrap();
        let mut code = Code::with_node(tree, NodeKind::Identifier(id));

        let kind = if *self.tokenizer.peek_kind() == TokenKind::Char('{') {
            let fields = self._parse_elements(
                tree,
                '{',
                '}',
                &mut code,
                Parser::parse_struct_field_pattern,
                NodeKind::ValueFieldPattern,
            );

            PatternKind::StructPattern(StructPattern::new(tree, id, fields))
        } else {
            PatternKind::VariablePattern(id)
        };

        tree.alloc(Pattern::new(kind, code))
    }

    fn _read_string(&mut self, tree: &'a Ast) -> (StringLiteral<'a>, Code<'a>) {
        let start_token = self.tokenizer.next_token(); // StringStart
        let mut code = Code::with_interpreted(tree, start_token);
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

        (StringLiteral::new(tree, value), code)
    }

    fn read_string(&mut self, tree: &'a Ast) -> &'a Expression<'a> {
        let (string, code) = self._read_string(tree);

        tree.alloc(Expression::new(ExpressionKind::StringLiteral(string), code))
    }

    fn read_string_pattern(&mut self, tree: &'a Ast) -> &'a Pattern<'a> {
        let (string, code) = self._read_string(tree);
        tree.alloc(Pattern::new(PatternKind::StringPattern(string), code))
    }

    fn read_paren(&mut self, tree: &'a Ast) -> &'a Expression<'a> {
        let mut code = Code::with_interpreted(tree, self.tokenizer.next_token()); // "("
        let node = self.parse_expr(tree);

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
        if let Some(ref expr) = node {
            tree.alloc(Expression::new(
                ExpressionKind::Expression(Some(expr)),
                code,
            ))
        } else {
            tree.alloc(Expression::new(ExpressionKind::Expression(None), code))
        }
    }

    fn read_array(&mut self, tree: &'a Ast) -> &'a Expression<'a> {
        let mut code = Code::new(tree);
        let elements = self._parse_elements(
            tree,
            '[',
            ']',
            &mut code,
            Parser::parse_expr,
            NodeKind::Expression,
        );

        let expr = ArrayExpression::new(tree, elements);

        tree.alloc(Expression::new(ExpressionKind::ArrayExpression(expr), code))
    }

    fn read_array_pattern(&mut self, tree: &'a Ast) -> &'a Pattern<'a> {
        let mut code = Code::new(tree);
        let elements = self._parse_elements(
            tree,
            '[',
            ']',
            &mut code,
            Parser::parse_pattern,
            NodeKind::Pattern,
        );

        tree.alloc(Pattern::new(
            PatternKind::ArrayPattern(ArrayPattern::new(tree, elements)),
            code,
        ))
    }

    fn read_rest_pattern(&mut self, tree: &'a Ast) -> &'a Pattern<'a> {
        let mut code = Code::with_interpreted(tree, self.tokenizer.next_token()); // "..."
        let name = self.parse_name(tree);

        if let Some(ref node) = name {
            code.node(NodeKind::Identifier(node));
        }

        tree.alloc(Pattern::new(
            PatternKind::RestPattern(RestPattern::new(name)),
            code,
        ))
    }

    fn read_if_expression(&mut self, tree: &'a Ast) -> &'a Expression<'a> {
        let mut code = Code::with_interpreted(tree, self.tokenizer.next_token()); // "if"
        let condition = self._parse_optional_item(
            tree,
            &mut code,
            Parser::parse_expr,
            NodeKind::Expression,
            MissingTokenKind::Expression,
        );

        // body
        let then_body = self._read_block(tree, &[TokenKind::End, TokenKind::Else]);
        let has_else = *self.tokenizer.peek_kind() == TokenKind::Else;

        code.node(NodeKind::Block(then_body));
        code.interpret(self.tokenizer.next_token()); // "else" or "end"

        let else_body = if has_else {
            let else_body = self._read_block(tree, &[TokenKind::End]);

            code.node(NodeKind::Block(else_body));
            code.interpret(self.tokenizer.next_token()); //  "end"

            Some(else_body)
        } else {
            None
        };

        let expr = IfExpression::new(condition, then_body, else_body);

        tree.alloc(Expression::new(ExpressionKind::IfExpression(expr), code))
    }

    fn read_case_expression(&mut self, tree: &'a Ast) -> &'a Expression<'a> {
        // case ...
        let mut code = Code::with_interpreted(tree, self.tokenizer.next_token()); // "case"
        let head = self._parse_optional_item(
            tree,
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
                    let arm = self.read_case_arm(tree);

                    code.node(NodeKind::CaseArm(arm));
                    arms.push(arm);
                }
                TokenKind::Else => {
                    code.interpret(self.tokenizer.next_token());

                    let block = self._read_block(tree, &[TokenKind::End]);
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

        let expr = CaseExpression::new(tree, head, arms, else_body);

        tree.alloc(Expression::new(ExpressionKind::CaseExpression(expr), code))
    }

    fn read_case_arm(&mut self, tree: &'a Ast) -> &'a CaseArm<'a> {
        let mut code = Code::new(tree);

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
                tree,
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
                tree,
                &mut code,
                Parser::parse_expr,
                NodeKind::Expression,
                MissingTokenKind::Expression,
            );
        }

        let then_body = self._read_block(tree, &[TokenKind::When, TokenKind::Else, TokenKind::End]);
        code.node(NodeKind::Block(then_body));

        tree.alloc(CaseArm::new(pattern, guard, then_body, code))
    }

    /// Reads statements until it meets a token listed in `stop_tokens`.
    /// But this function doesn't consume a stop token itself, consuming
    /// a stop token is caller's responsibility.
    fn _read_block(&mut self, tree: &'a Ast, stop_tokens: &[TokenKind]) -> &'a Block<'a> {
        let mut code = Code::new(tree);

        // body
        let mut body = vec![];

        // A separator must be appear before block
        self.tokenizer.peek();
        let mut newline_seen = self.tokenizer.is_newline_seen();
        let mut insertion_range = self.tokenizer.current_insertion_range();

        loop {
            let mut stmt_seen = false;

            if let Some(stmt) = self.parse_stmt(tree) {
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

                    // `parse_stmt(tree)` should consume at least one token.
                    // However, in case `parse_stmt(tree)` have not been able to consume a single token,
                    // we have to skip the current token.
                    if !stmt_seen {
                        code.skip(self.tokenizer.next_token(), MissingTokenKind::Statement);
                    }
                }
            }
        }

        tree.alloc(Block::new(tree, body, code))
    }

    fn _parse_optional_item<T>(
        &mut self,
        tree: &'a Ast,
        code: &mut Code<'a>,
        node_parser: fn(&mut Parser<'a>, &'a Ast) -> Option<&'a T>,
        kind_builder: fn(&'a T) -> NodeKind<'a>,
        missing_token: MissingTokenKind,
    ) -> Option<&'a T> {
        let node = node_parser(self, tree);

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
        tree: &'a Ast,
        open_char: char,
        close_char: char,
        code: &mut Code<'a>,
        element_parser: fn(&mut Parser<'a>, &'a Ast) -> Option<&'a T>,
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
                    if let Some(expr) = element_parser(self, tree) {
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
                let argument = element_parser(self, tree);

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
        tree: &'a Ast,
        next_parser: fn(&mut Parser<'a>, &'a Ast) -> Option<&'a Expression<'a>>,
        operators: &[(TokenKind, BinaryOperator)],
    ) -> Option<&'a Expression<'a>> {
        let mut lhs = next_parser(self, tree)?;

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
            let mut code = Code::new(tree);

            code.node(NodeKind::Expression(lhs)).interpret(op_token);

            loop {
                rhs = next_parser(self, tree);

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
            let expr = BinaryExpression::new(operator, lhs, rhs);

            lhs = tree.alloc(Expression::new(
                ExpressionKind::BinaryExpression(expr),
                code,
            ));
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
        let tree = Ast::new();
        let stmt = parse_statement(&tree, "42");

        assert_matches!(
            stmt.expression().unwrap().kind(),
            ExpressionKind::IntegerLiteral(n) => {
                assert_eq!(*n, IntegerLiteral::new(42));
            }
        );

        let mut code = stmt.expression().unwrap().code();
        assert_eq!(code.len(), 1);

        let token = next_interpreted_token(&mut code);
        assert_matches!(token.kind, TokenKind::Integer(42));
    }

    #[test]
    fn incomplete_string() {
        let tree = Ast::new();
        for src in vec!["\"Fizz\\\"", "\"Fizz\\\"\n"] {
            let stmt = parse_statement(&tree, src);
            let expr = stmt.expression().unwrap();

            assert_matches!(expr.kind(), ExpressionKind::StringLiteral(..));

            let mut tokens = stmt.expression().unwrap().code();
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
        let tree = Ast::new();
        for src in vec!["(\"Fizz\\\")", "(\"Fizz\\\")\n"] {
            let stmt = parse_statement(&tree, src);
            let expr = stmt.expression().unwrap();

            assert_matches!(expr.kind(), ExpressionKind::Expression(Some(expr)) => {
                assert_matches!(expr.kind(), ExpressionKind::StringLiteral(..));
            });

            let mut tokens = stmt.expression().unwrap().code();
            assert_eq!(tokens.len(), 3);

            let token = next_interpreted_token(&mut tokens);
            assert_matches!(token.kind, TokenKind::Char('('));

            let node = next_node(&mut tokens);
            assert_matches!(node, NodeKind::Expression(..));

            let (_, item) = next_missing_token(&mut tokens);
            assert_eq!(item, MissingTokenKind::Char(')'));
        }
    }

    #[test]
    fn add_integer() {
        let tree = Ast::new();
        let stmt = parse_statement(&tree, "1+2");
        let expr = stmt.expression().unwrap().binary_expression().unwrap();

        assert_eq!(expr.operator(), BinaryOperator::Add);
        assert_matches!(
            expr.lhs().kind(),
            ExpressionKind::IntegerLiteral(n) => {
                assert_eq!(*n, IntegerLiteral::new(1));
            }
        );
        assert_matches!(
            expr.rhs().unwrap().kind(),
            ExpressionKind::IntegerLiteral(n) => {
                assert_eq!(*n, IntegerLiteral::new(2));
            }
        );

        let mut tokens = stmt.expression().unwrap().code();
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
        let tree = Ast::new();
        let stmt = parse_statement(&tree, "1+");
        let expr = stmt.expression().unwrap().binary_expression().unwrap();

        assert_eq!(expr.operator(), BinaryOperator::Add);
        assert_matches!(
            expr.lhs().kind(),
            ExpressionKind::IntegerLiteral(n) => {
                assert_eq!(*n, IntegerLiteral::new(1));
            }
        );
        assert!(expr.rhs().is_none());

        let mut tokens = stmt.expression().unwrap().code();
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
        let tree = Ast::new();
        let stmt = parse_statement(&tree, "1 + % ? 2");
        let expr = stmt.expression().unwrap().binary_expression().unwrap();

        assert_eq!(expr.operator(), BinaryOperator::Add);
        assert_matches!(
            expr.lhs().kind(),
            ExpressionKind::IntegerLiteral(n) => {
                assert_eq!(*n, IntegerLiteral::new(1));
            }
        );
        assert_matches!(
            expr.rhs().unwrap().kind(),
            ExpressionKind::IntegerLiteral(n) => {
                assert_eq!(*n, IntegerLiteral::new(2));
            }
        );

        let mut tokens = stmt.expression().unwrap().code();
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
        let tree = Ast::new();
        let stmt = parse_statement(&tree, "-1");
        let expr = stmt.expression().unwrap().unary_expression().unwrap();

        assert_eq!(expr.operator(), UnaryOperator::Minus);
        assert_matches!(
            expr.operand().unwrap().kind(),
            ExpressionKind::IntegerLiteral(n) => {
                assert_eq!(*n, IntegerLiteral::new(1));
            }
        );

        let mut tokens = stmt.expression().unwrap().code();
        assert_eq!(tokens.len(), 2);

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('-'));

        let node = next_node(&mut tokens);
        assert!(node.is_expression());
    }

    #[test]
    fn unary_op_nested() {
        let tree = Ast::new();
        let stmt = parse_statement(&tree, "-+1");
        let expr = stmt.expression().unwrap().unary_expression().unwrap();

        assert_matches!(expr, UnaryExpression { operator: UnaryOperator::Minus, operand: Some(operand) } => {
            let operand = operand.unary_expression().unwrap();

            assert_matches!(operand, UnaryExpression { operator: UnaryOperator::Plus, operand: Some(operand) } => {
                assert_matches!(
                    operand.kind(),
                    ExpressionKind::IntegerLiteral(n) => {
                        assert_eq!(*n, IntegerLiteral::new(1));
                    }
                );
            });
        });

        let mut tokens = stmt.expression().unwrap().code();
        assert_eq!(tokens.len(), 2);

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('-'));

        let node = next_node(&mut tokens);
        assert!(node.is_expression());
    }

    #[test]
    fn subscript_index() {
        let tree = Ast::new();
        let stmt = parse_statement(&tree, "a[0]");
        let expr = stmt.expression().unwrap().subscript_expression().unwrap();

        assert_matches!(expr, SubscriptExpression{ .. } => {
            let id = expr.callee().variable_expression();
            assert!(id.is_some());

            let id = id.unwrap();
            assert_eq!(id.to_string(), "a");

            let arguments = expr.arguments().collect::<Vec<_>>();
            assert_eq!(arguments.len(), 1);
            assert_matches!(
                arguments[0].kind(),
                ExpressionKind::IntegerLiteral(n) => {
                    assert_eq!(*n, IntegerLiteral::new(0));
                }
            );
        });

        let mut tokens = stmt.expression().unwrap().code();
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
        let tree = Ast::new();
        let stmt = parse_statement(&tree, "a[]");
        let expr = stmt.expression().unwrap().subscript_expression().unwrap();

        assert_matches!(expr, SubscriptExpression{ .. } => {
            let id = expr.callee().variable_expression();
            assert!(id.is_some());

            let id = id.unwrap();
            assert_eq!(id.to_string(), "a");

            let arguments = expr.arguments().collect::<Vec<_>>();
            assert_eq!(arguments.len(), 0);
        });

        let mut tokens = stmt.expression().unwrap().code();
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
        let tree = Ast::new();
        let stmt = parse_statement(&tree, "a[1\nb");
        let expr = stmt.expression().unwrap().subscript_expression().unwrap();

        assert_matches!(expr, SubscriptExpression{ .. } => {
            let id = expr.callee().variable_expression();
            assert!(id.is_some());

            let id = id.unwrap();
            assert_eq!(id.to_string(), "a");

            let arguments = expr.arguments().collect::<Vec<_>>();
            assert_eq!(arguments.len(), 1);
            assert_matches!(
                arguments[0].kind(),
                ExpressionKind::IntegerLiteral(n) => {
                    assert_eq!(*n, IntegerLiteral::new(1));
                }
            );
        });

        let mut tokens = stmt.expression().unwrap().code();
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
        let tree = Ast::new();
        for src in vec!["a[\"", "a[\"\n"] {
            let stmt = parse_statement(&tree, src);
            let expr = stmt.expression().unwrap().subscript_expression().unwrap();

            assert_matches!(expr, SubscriptExpression{ .. } => {
                let arguments = expr.arguments().collect::<Vec<_>>();
                assert_eq!(arguments.len(), 1);
                assert_matches!(arguments[0].kind(), ExpressionKind::StringLiteral(..));
            });

            let mut tokens = stmt.expression().unwrap().code();
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
        let tree = Ast::new();
        let stmt = parse_statement(&tree, "[]");
        let expr = stmt.expression().unwrap().array_expression().unwrap();

        assert_matches!(expr, ArrayExpression{ .. } => {
            let elements = expr.elements().collect::<Vec<_>>();
            assert_eq!(elements.len(), 0);
        });

        let mut tokens = stmt.expression().unwrap().code();
        assert_eq!(tokens.len(), 2);

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char('['));

        let token = next_interpreted_token(&mut tokens);
        assert_matches!(token.kind, TokenKind::Char(']'));
    }

    #[test]
    fn array_one_element_and_trailing_comma() {
        let tree = Ast::new();
        let stmt = parse_statement(&tree, "[1,]");
        let expr = stmt.expression().unwrap().array_expression().unwrap();

        assert_matches!(expr, ArrayExpression{ .. } => {
            let elements = expr.elements().collect::<Vec<_>>();
            assert_eq!(elements.len(), 1);

            assert_eq!(elements.len(), 1);
            assert_matches!(
                elements[0].kind(),
                ExpressionKind::IntegerLiteral(n) => {
                    assert_eq!(*n, IntegerLiteral::new(1));
                }
            );
        });

        let mut tokens = stmt.expression().unwrap().code();
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
        let tree = Ast::new();
        let stmt = parse_statement(
            &tree,
            "if x > 0
                10
            else
                20
            end",
        );
        let expr = stmt.expression().unwrap().if_expression().unwrap();

        assert_matches!(expr, IfExpression { ref condition, ref else_body, .. } => {
            let condition = condition.as_ref().unwrap();

            assert_matches!(condition.kind(), ExpressionKind::BinaryExpression(..));
            assert!(else_body.is_some());
        });
    }

    #[test]
    fn if_expression_missing_condition() {
        let tree = Ast::new();
        let stmt = parse_statement(&tree, "if\nend");
        let expr = stmt.expression().unwrap().if_expression().unwrap();

        assert_matches!(expr, IfExpression { condition, then_body, else_body } => {
            assert!(condition.is_none());
            assert!(else_body.is_none());

            let stmts = then_body.statements();
            assert_eq!(stmts.len(), 0);
        });
    }

    #[test]
    fn if_expression_missing_newline() {
        let tree = Ast::new();
        let stmt = parse_statement(&tree, "if b x end");

        assert!(stmt.expression().unwrap().if_expression().is_some());

        // tokens
        let mut tokens = stmt.expression().unwrap().code();
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
        let tree = Ast::new();
        let stmt = parse_statement(
            &tree,
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

        assert_matches!(expr, CaseExpression { head, arms, else_body } => {
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

    fn parse_statement<'a>(tree: &'a Ast, src: &'a str) -> &'a Statement<'a> {
        let module = Parser::parse_string(tree, src);

        assert_eq!(!module.body().len(), 0);
        module.body().next().unwrap().statement().unwrap()
    }

    fn next_node<'a>(tokens: &'a mut slice::Iter<'_, CodeKind<'a>>) -> &'a NodeKind<'a> {
        unwrap_node(tokens.next().unwrap())
    }

    fn next_interpreted_token<'a>(tokens: &'a mut slice::Iter<'_, CodeKind<'a>>) -> &'a Token {
        unwrap_interpreted_token(tokens.next().unwrap())
    }

    fn next_missing_token(
        tokens: &mut slice::Iter<'_, CodeKind<'_>>,
    ) -> (EffectiveRange, MissingTokenKind) {
        unwrap_missing_token(tokens.next().unwrap())
    }

    fn next_skipped_token<'a>(
        tokens: &'a mut slice::Iter<'_, CodeKind<'a>>,
    ) -> (&'a Token, MissingTokenKind) {
        unwrap_skipped_token(tokens.next().unwrap())
    }

    fn unwrap_node<'a>(kind: &'a CodeKind<'a>) -> &'a NodeKind<'a> {
        if let CodeKind::Node(node) = kind {
            return node;
        }

        panic!("expected child node");
    }

    fn unwrap_interpreted_token<'a>(kind: &'a CodeKind<'a>) -> &'a Token {
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

    fn unwrap_skipped_token<'a>(kind: &'a CodeKind<'a>) -> (&'a Token, MissingTokenKind) {
        if let CodeKind::SyntaxToken(token) = kind {
            if let SyntaxToken::Skipped { token, expected } = token {
                return (token, *expected);
            }
        }

        panic!("expected missing token");
    }
}
