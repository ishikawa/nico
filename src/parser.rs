use crate::asm;
use crate::asm::wasm;
use crate::sem;
use crate::syntax::{ParseError, ParseErrorKind, Token, TokenKind, Tokenizer};
use crate::util::naming::PrefixNaming;
use crate::util::wrap;
use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

const DEBUG: bool = false;

fn debug_trace(name: &str, tokenizer: &Tokenizer<'_>) {
    if DEBUG {
        eprintln!("[{}] position: {}", name, tokenizer.current_position());
    }
}

// Program
pub struct Module {
    pub structs: Vec<StructDefinition>,
    pub functions: Vec<Function>,
    pub main: Option<Function>,
    pub strings: Option<Vec<Rc<RefCell<asm::ConstantString>>>>,
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

#[derive(Debug)]
pub struct StructDefinition {
    pub name: String,
    pub fields: Vec<TypeField>,
}

#[derive(Debug)]
pub struct TypeField {
    pub name: String,
    pub type_annotation: TypeAnnotation,
}

#[derive(Debug)]
pub enum TypeAnnotation {
    Name(String),
    Builtin(Rc<RefCell<sem::Type>>),
}

/// Function
#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub body: Vec<Node>,
    pub export: bool,
    // metadata
    pub params: Vec<Rc<RefCell<sem::Binding>>>,
    pub r#type: Rc<RefCell<sem::Type>>,

    pub locals: Option<asm::LocalVariables>,

    // The total size of stack frame required for executing this function.
    // It will be calculated by allocator.
    pub frame: Option<asm::StackFrame>,
}

#[derive(Debug)]
pub struct Node {
    pub expr: Expr,
    pub r#type: Rc<RefCell<sem::Type>>,
}

#[derive(Debug)]
pub enum Expr {
    // Primitive
    Integer(i32),
    String {
        content: String,
        storage: Option<Rc<RefCell<asm::ConstantString>>>,
    },
    Identifier {
        name: String,
        // A local variable / parameter that the identifier refers.
        binding: Option<Rc<RefCell<sem::Binding>>>,
    },
    Array {
        elements: Vec<Node>,
        /// The offset from the end of "static" in a stack frame.
        ///
        /// ```ignore
        /// ----+-----------+-----------+-----+-------------+
        ///     | element 0 | element 1 | ... | Caller's FP |
        /// ----o-----------+-----------+-----o-------------+
        ///     |<----------------------------|
        /// ```
        object_offset: Option<wasm::Size>,
    },
    Struct {
        name: String,
        fields: Vec<ValueField>,
        /// The offset from the end of "static" in a stack frame.
        ///
        /// ```ignore
        /// ----+-----------+-----------+-----+-------------+
        ///     | field 0   | field 1   | ... | Caller's FP |
        /// ----o-----------+-----------+-----o-------------+
        ///     |<----------------------------|
        /// ```
        object_offset: Option<wasm::Size>,
    },
    Subscript {
        operand: Box<Node>,
        index: Box<Node>,
    },
    Access {
        operand: Box<Node>,
        field: String,
    },
    Invocation {
        name: String,
        arguments: Vec<Node>,
        // A function that the invocation refers.
        binding: Option<Rc<RefCell<sem::Binding>>>,
    },

    // Binary operator :: LHS, RHS, Binding
    Add(Box<Node>, Box<Node>, Option<Rc<RefCell<sem::Binding>>>),
    Sub(Box<Node>, Box<Node>, Option<Rc<RefCell<sem::Binding>>>),
    Rem(Box<Node>, Box<Node>, Option<Rc<RefCell<sem::Binding>>>),
    Mul(Box<Node>, Box<Node>, Option<Rc<RefCell<sem::Binding>>>),
    Div(Box<Node>, Box<Node>, Option<Rc<RefCell<sem::Binding>>>),

    // Relational operator
    Lt(Box<Node>, Box<Node>, Option<Rc<RefCell<sem::Binding>>>), // Less Than
    Gt(Box<Node>, Box<Node>, Option<Rc<RefCell<sem::Binding>>>), // Greater Than
    Le(Box<Node>, Box<Node>, Option<Rc<RefCell<sem::Binding>>>), // Less than Equal
    Ge(Box<Node>, Box<Node>, Option<Rc<RefCell<sem::Binding>>>), // Greater than Equal
    Eq(Box<Node>, Box<Node>, Option<Rc<RefCell<sem::Binding>>>), // Equal
    Ne(Box<Node>, Box<Node>, Option<Rc<RefCell<sem::Binding>>>), // Not Equal

    // Unary operator
    Minus(Box<Node>, Option<Rc<RefCell<sem::Binding>>>),
    Plus(Box<Node>, Option<Rc<RefCell<sem::Binding>>>),

    // Statement
    Stmt(Box<Node>),

    // Control flow
    If {
        condition: Box<Node>,
        then_body: Vec<Node>,
        else_body: Option<Vec<Node>>,
    },
    Case {
        head: Box<Node>, // head expression
        head_storage: Option<Rc<asm::Storage>>,
        arms: Vec<CaseArm>,
        else_body: Option<Vec<Node>>,
    },

    // Variable binding
    Var {
        pattern: Pattern,
        init: Box<Node>,
    },
}

#[derive(Debug)]
pub enum Pattern {
    Variable(String, Rc<RefCell<sem::Binding>>),
    Integer(i32),
    Array(Vec<Pattern>),
    Struct {
        name: Option<String>,
        fields: Vec<PatternField>,
        r#type: Option<Rc<RefCell<sem::Type>>>,
    },
    Rest {
        name: String,
        binding: Rc<RefCell<sem::Binding>>,
        reference_offset: Option<wasm::Size>,
    },
}

#[derive(Debug)]
pub struct ValueField {
    pub name: String,
    pub value: Node,
}

#[derive(Debug)]
pub struct PatternField {
    pub name: String,
    pub pattern: Pattern,
}

#[derive(Debug)]
pub struct CaseArm {
    pub pattern: Pattern,
    pub condition: Option<Node>, // guard
    pub then_body: Vec<Node>,
}

#[derive(Debug, Default)]
pub struct Parser {}

#[derive(Debug)]
struct ParserContext {
    naming: PrefixNaming,
}

impl ParserContext {
    pub fn typed_expr(&mut self, expr: Expr) -> Node {
        let ty = match expr {
            Expr::Integer(_) => wrap(sem::Type::Int32),
            Expr::String { .. } => wrap(sem::Type::String),
            Expr::Stmt(..) => wrap(sem::Type::Void),
            _ => self.type_var(),
        };

        Node { expr, r#type: ty }
    }

    /// Returns a new type variable.
    pub fn type_var(&mut self) -> Rc<RefCell<sem::Type>> {
        let name = self.naming.next();
        wrap(sem::Type::new_type_var(&name))
    }
}

pub fn parse_string<S: AsRef<str>>(src: S) -> Result<Box<Module>, ParseError> {
    let mut tokenizer = Tokenizer::from_string(&src);
    let parser = Parser::new();
    parser.parse(&mut tokenizer)
}

impl Parser {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn parse(&self, tokenizer: &mut Tokenizer<'_>) -> Result<Box<Module>, ParseError> {
        let mut context = ParserContext {
            naming: PrefixNaming::new("?"),
        };

        let mut structs = vec![];
        let mut functions = vec![];
        // Parser collects top expressions and automatically build
        // `main` function which is the entry point of a program.
        let mut body = vec![];

        loop {
            // Type declaration
            if let Some(struct_def) = self.parse_struct_definition(tokenizer, &mut context)? {
                structs.push(struct_def);
            }
            // Function
            else if let Some(function) = self.parse_function(tokenizer, &mut context)? {
                functions.push(function);
            }
            // Body for main function
            else if let Some(expr) = self.parse_stmt(tokenizer, &mut context)? {
                body.push(Some(expr));
            }
            // No top level constructs can be consumed. It may be at the end of input or
            // parse error.
            else {
                let token = tokenizer.peek();

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

        let body = self.wrap_stmts(&mut body, &mut context);

        let main = if !body.is_empty() {
            let fun = Function {
                name: "main".to_string(),
                body,
                export: true,
                params: vec![],
                locals: None,
                r#type: wrap(sem::Type::Function {
                    params: vec![],
                    return_type: context.type_var(),
                }),
                frame: None,
            };

            Some(fun)
        } else {
            None
        };

        Ok(Box::new(Module {
            structs,
            functions,
            main,
            strings: None,
        }))
    }

    fn parse_struct_definition(
        &self,
        tokenizer: &mut Tokenizer<'_>,
        context: &mut ParserContext,
    ) -> Result<Option<StructDefinition>, ParseError> {
        debug_trace("parse_struct_definition", tokenizer);

        if match_token(tokenizer, TokenKind::Struct).is_none() {
            return Ok(None);
        }

        let name = expect_identifier(tokenizer, "struct name")?;

        // {...}
        expect_char(tokenizer, '{')?;
        let fields = parse_elements(tokenizer, context, '}', &mut |tokenizer, context| {
            self.parse_type_field(tokenizer, context)?.ok_or_else(|| {
                ParseError::syntax_error(tokenizer.current_position(), "Expected struct field")
            })
        })?;
        expect_char(tokenizer, '}')?;

        Ok(Some(StructDefinition { name, fields }))
    }

    fn parse_type_field(
        &self,
        tokenizer: &mut Tokenizer<'_>,
        context: &mut ParserContext,
    ) -> Result<Option<TypeField>, ParseError> {
        debug_trace("parse_type_field", tokenizer);

        let name = if let Some(name) = match_identifier(tokenizer, "field name") {
            name
        } else {
            return Ok(None);
        };

        expect_char(tokenizer, ':')?;

        let type_annotation = self
            .parse_type_annotation(tokenizer, context)
            .ok_or_else(|| {
                ParseError::syntax_error(tokenizer.current_position(), "Expected type annotation")
            })?;

        Ok(Some(TypeField {
            name,
            type_annotation,
        }))
    }

    fn parse_value_field(
        &self,
        tokenizer: &mut Tokenizer<'_>,
        context: &mut ParserContext,
    ) -> Result<Option<ValueField>, ParseError> {
        debug_trace("parse_value_field", tokenizer);

        let name = if let Some(name) = match_identifier(tokenizer, "field name") {
            name
        } else {
            return Ok(None);
        };

        // Desugar: field init shorthand syntax
        let value = if match_char(tokenizer, ':').is_some() {
            self.parse_expr(tokenizer, context)?.ok_or_else(|| {
                ParseError::syntax_error(tokenizer.current_position(), "Expected field value")
            })?
        } else {
            context.typed_expr(Expr::Identifier {
                name: name.clone(),
                binding: None,
            })
        };

        Ok(Some(ValueField { name, value }))
    }

    fn parse_type_annotation(
        &self,
        tokenizer: &mut Tokenizer<'_>,
        _context: &mut ParserContext,
    ) -> Option<TypeAnnotation> {
        debug_trace("parse_type_annotation", tokenizer);

        let type_annotation = if let Some(name) = match_identifier(tokenizer, "type name") {
            TypeAnnotation::Name(name)
        } else if match_token(tokenizer, TokenKind::IntType).is_some() {
            TypeAnnotation::Builtin(wrap(sem::Type::Int32))
        } else {
            return None;
        };

        Some(type_annotation)
    }

    fn parse_function(
        &self,
        tokenizer: &mut Tokenizer<'_>,
        context: &mut ParserContext,
    ) -> Result<Option<Function>, ParseError> {
        debug_trace("parse_function", tokenizer);

        // modifiers
        let export = match_token(tokenizer, TokenKind::Export).is_some();

        // fun
        if match_token(tokenizer, TokenKind::Fun).is_none() {
            return Ok(None);
        }

        let name = expect_identifier(tokenizer, "function name")?;

        let mut param_names = vec![];

        expect_char(tokenizer, '(')?;
        while let TokenKind::Identifier(_) = tokenizer.peek_kind() {
            let name = expect_identifier(tokenizer, "param")?;
            param_names.push(name);

            match tokenizer.peek_kind() {
                TokenKind::Char(',') => {
                    tokenizer.next_token();
                }
                _ => break,
            };
        }
        expect_char(tokenizer, ')')?;
        // TODO: check line separator before reading body

        let mut body = vec![];

        loop {
            if let TokenKind::End = tokenizer.peek_kind() {
                break;
            }

            match self.parse_stmt(tokenizer, context)? {
                None => break,
                Some(node) => body.push(Some(node)),
            };
        }
        expect_token_with(tokenizer, TokenKind::End)?;

        let body = self.wrap_stmts(&mut body, context);

        {
            let param_types = param_names
                .iter()
                .map(|_| context.type_var())
                .collect::<Vec<_>>();

            let params = param_names
                .iter()
                .zip(&param_types)
                .map(|(name, ty)| wrap(sem::Binding::typed_name(name, &ty)))
                .collect::<Vec<_>>();

            let function_type = wrap(sem::Type::Function {
                params: param_types,
                return_type: context.type_var(),
            });

            let function = Function {
                name,
                params,
                export,
                locals: None,
                body,
                r#type: function_type,
                frame: None,
            };

            Ok(Some(function))
        }
    }

    /// Returns `Stmt` if the result of `parse_stmt_expr()` is a variable binding.
    fn parse_stmt(
        &self,
        tokenizer: &mut Tokenizer<'_>,
        context: &mut ParserContext,
    ) -> Result<Option<Node>, ParseError> {
        debug_trace("parse_stmt", tokenizer);

        let node = self.parse_stmt_expr(tokenizer, context)?;
        let node = if let Some(node) = node {
            node
        } else {
            return Ok(None);
        };

        if let Expr::Var { .. } = node.expr {
            return Ok(Some(self.wrap_stmt(node, context)));
        }

        Ok(Some(node))
    }

    /// Variable binding or `Expr`
    fn parse_stmt_expr(
        &self,
        tokenizer: &mut Tokenizer<'_>,
        context: &mut ParserContext,
    ) -> Result<Option<Node>, ParseError> {
        debug_trace("parse_stmt_expr", tokenizer);

        match tokenizer.peek_kind() {
            TokenKind::Let => {
                tokenizer.next_token();
            }
            _ => return self.parse_expr(tokenizer, context),
        };

        // Variable binding - Pattern
        let pattern = parse_pattern(tokenizer, context)?.ok_or_else(|| {
            ParseError::syntax_error(tokenizer.current_position(), "Missing pattern in `let`")
        })?;

        expect_char(tokenizer, '=')?;

        let init = self.parse_expr(tokenizer, context)?.ok_or_else(|| {
            ParseError::syntax_error(tokenizer.current_position(), "No initializer")
        })?;

        Ok(Some(context.typed_expr(Expr::Var {
            pattern,
            init: Box::new(init),
        })))
    }

    fn parse_expr(
        &self,
        tokenizer: &mut Tokenizer<'_>,
        context: &mut ParserContext,
    ) -> Result<Option<Node>, ParseError> {
        self.parse_rel_op1(tokenizer, context)
    }

    // "==", "!="
    fn parse_rel_op1(
        &self,
        tokenizer: &mut Tokenizer<'_>,
        context: &mut ParserContext,
    ) -> Result<Option<Node>, ParseError> {
        debug_trace("parse_rel_op1", tokenizer);

        let lhs = self.parse_rel_op2(tokenizer, context)?;
        let lhs = if let Some(lhs) = lhs {
            lhs
        } else {
            return Ok(None);
        };

        let builder = match tokenizer.peek_kind() {
            TokenKind::Eq => Expr::Eq,
            TokenKind::Ne => Expr::Ne,
            _ => return Ok(Some(lhs)),
        };
        tokenizer.next_token();

        let rhs = self.parse_rel_op2(tokenizer, context)?.ok_or_else(|| {
            ParseError::syntax_error(tokenizer.current_position(), "Expected RHS")
        })?;

        Ok(Some(context.typed_expr(builder(
            Box::new(lhs),
            Box::new(rhs),
            None,
        ))))
    }

    // ">", "<", ">=", "<="
    fn parse_rel_op2(
        &self,
        tokenizer: &mut Tokenizer<'_>,
        context: &mut ParserContext,
    ) -> Result<Option<Node>, ParseError> {
        debug_trace("parse_rel_op2", tokenizer);

        let lhs = self.parse_binary_op1(tokenizer, context)?;
        let lhs = if let Some(lhs) = lhs {
            lhs
        } else {
            return Ok(None);
        };

        let builder = match tokenizer.peek_kind() {
            TokenKind::Le => Expr::Le,
            TokenKind::Ge => Expr::Ge,
            TokenKind::Char('<') => Expr::Lt,
            TokenKind::Char('>') => Expr::Gt,
            _ => return Ok(Some(lhs)),
        };
        tokenizer.next_token();

        let rhs = self.parse_binary_op1(tokenizer, context)?.ok_or_else(|| {
            ParseError::syntax_error(tokenizer.current_position(), "Expected RHS")
        })?;

        Ok(Some(context.typed_expr(builder(
            Box::new(lhs),
            Box::new(rhs),
            None,
        ))))
    }

    fn parse_binary_op1(
        &self,
        tokenizer: &mut Tokenizer<'_>,
        context: &mut ParserContext,
    ) -> Result<Option<Node>, ParseError> {
        debug_trace("parse_binary_op1", tokenizer);

        let lhs = self.parse_binary_op2(tokenizer, context)?;
        let mut lhs = if let Some(lhs) = lhs {
            lhs
        } else {
            return Ok(None);
        };

        loop {
            let builder = match tokenizer.peek_kind() {
                TokenKind::Char('+') => Expr::Add,
                TokenKind::Char('-') => Expr::Sub,
                TokenKind::Char('%') => Expr::Rem,
                _ => break,
            };

            // A newline character terminates node construction.
            if tokenizer.is_newline_seen() {
                break;
            }

            tokenizer.next_token();

            let rhs = self.parse_binary_op2(tokenizer, context)?.ok_or_else(|| {
                ParseError::syntax_error(tokenizer.current_position(), "Expected RHS")
            })?;

            lhs = context.typed_expr(builder(Box::new(lhs), Box::new(rhs), None));
        }

        Ok(Some(lhs))
    }

    fn parse_binary_op2(
        &self,
        tokenizer: &mut Tokenizer<'_>,
        context: &mut ParserContext,
    ) -> Result<Option<Node>, ParseError> {
        debug_trace("parse_binary_op2", tokenizer);

        let lhs = self.parse_unary_op(tokenizer, context)?;
        let mut lhs = if let Some(lhs) = lhs {
            lhs
        } else {
            return Ok(None);
        };

        loop {
            let builder = match tokenizer.peek_kind() {
                TokenKind::Char('*') => Expr::Mul,
                TokenKind::Char('/') => Expr::Div,
                _ => break,
            };
            tokenizer.next_token();

            let rhs = self.parse_unary_op(tokenizer, context)?.ok_or_else(|| {
                ParseError::syntax_error(tokenizer.current_position(), "Expected RHS")
            })?;

            lhs = context.typed_expr(builder(Box::new(lhs), Box::new(rhs), None));
        }

        Ok(Some(lhs))
    }

    fn parse_unary_op(
        &self,
        tokenizer: &mut Tokenizer<'_>,
        context: &mut ParserContext,
    ) -> Result<Option<Node>, ParseError> {
        debug_trace("parse_unary_op", tokenizer);

        let builder = match tokenizer.peek_kind() {
            TokenKind::Char('+') => Expr::Plus,
            TokenKind::Char('-') => Expr::Minus,
            _ => return self.parse_access(tokenizer, context),
        };
        tokenizer.next_token();

        // unary operators are right associative.
        let expr = match self.parse_unary_op(tokenizer, context)? {
            None => {
                return Err(ParseError::syntax_error(
                    tokenizer.current_position(),
                    "Expected operand",
                ))
            }
            Some(node) => builder(Box::new(node), None),
        };

        Ok(Some(context.typed_expr(expr)))
    }

    // `x[...]`, `x(...)`, `x.y`
    fn parse_access(
        &self,
        tokenizer: &mut Tokenizer<'_>,
        context: &mut ParserContext,
    ) -> Result<Option<Node>, ParseError> {
        debug_trace("parse_access", tokenizer);

        let node = self.parse_primary(tokenizer, context)?;
        let mut node = if let Some(node) = node {
            node
        } else {
            return Ok(None);
        };

        loop {
            // To distinguish `x\n[...]` from `x[...]`, we have to check a newline.
            if tokenizer.is_followed_by_newline() {
                break;
            }

            let token = tokenizer.peek();

            match token.kind {
                TokenKind::Char('[') => {
                    expect_char(tokenizer, '[')?;
                    let mut arguments =
                        parse_elements(tokenizer, context, ']', &mut |tokenizer, context| {
                            self.parse_expr(tokenizer, context)?.ok_or_else(|| {
                                ParseError::syntax_error(
                                    tokenizer.current_position(),
                                    "Expected subscript argument",
                                )
                            })
                        })?;
                    expect_char(tokenizer, ']')?;

                    if arguments.len() != 1 {
                        panic!(
                            "subscript operator `[]` takes 1 argument, but {} arguments given",
                            arguments.len()
                        );
                    }

                    node = context.typed_expr(Expr::Subscript {
                        operand: Box::new(node),
                        index: Box::new(arguments.remove(0)),
                    });
                }
                TokenKind::Char('.') => {
                    expect_char(tokenizer, '.')?;

                    let field = expect_identifier(tokenizer, "field name")?;

                    node = context.typed_expr(Expr::Access {
                        operand: Box::new(node),
                        field,
                    });
                }
                _ => break,
            }
        }

        Ok(Some(node))
    }

    fn parse_primary(
        &self,
        tokenizer: &mut Tokenizer<'_>,
        context: &mut ParserContext,
    ) -> Result<Option<Node>, ParseError> {
        debug_trace("parse_primary", tokenizer);

        let token = tokenizer.peek();

        match &token.kind {
            TokenKind::Eos => Ok(None),
            TokenKind::Char('(') => {
                expect_char(tokenizer, '(')?;
                let node = self.parse_expr(tokenizer, context)?;
                expect_char(tokenizer, ')')?;
                Ok(node)
            }
            TokenKind::Char('[') => {
                expect_char(tokenizer, '[')?;
                let elements =
                    parse_elements(tokenizer, context, ']', &mut |tokenizer, context| {
                        self.parse_expr(tokenizer, context)?.ok_or_else(|| {
                            ParseError::syntax_error(
                                tokenizer.current_position(),
                                "Expected element",
                            )
                        })
                    })?;
                expect_char(tokenizer, ']')?;

                Ok(Some(context.typed_expr(Expr::Array {
                    elements,
                    object_offset: None,
                })))
            }
            TokenKind::Identifier(_) => {
                let name = expect_identifier(tokenizer, "id")?;

                // function invocation?
                // TODO: Move to parse_access()
                if let TokenKind::Char('(') = tokenizer.peek_kind() {
                    if !tokenizer.is_newline_seen() {
                        expect_char(tokenizer, '(')?;
                        let arguments =
                            parse_elements(tokenizer, context, ')', &mut |tokenizer, context| {
                                self.parse_expr(tokenizer, context)?.ok_or_else(|| {
                                    ParseError::syntax_error(
                                        tokenizer.current_position(),
                                        "Expected argument",
                                    )
                                })
                            })?;
                        expect_char(tokenizer, ')')?;

                        return Ok(Some(context.typed_expr(Expr::Invocation {
                            name,
                            arguments,
                            binding: None,
                        })));
                    }
                }
                // struct literal?
                else if let TokenKind::Char('{') = tokenizer.peek_kind() {
                    if !tokenizer.is_newline_seen() {
                        expect_char(tokenizer, '{')?;
                        let fields =
                            parse_elements(tokenizer, context, '}', &mut |tokenizer, context| {
                                self.parse_value_field(tokenizer, context)?.ok_or_else(|| {
                                    ParseError::syntax_error(
                                        tokenizer.current_position(),
                                        "Expected struct field",
                                    )
                                })
                            })?;
                        expect_char(tokenizer, '}')?;

                        return Ok(Some(context.typed_expr(Expr::Struct {
                            name,
                            fields,
                            object_offset: None,
                        })));
                    }
                }

                Ok(Some(context.typed_expr(Expr::Identifier {
                    name,
                    binding: None,
                })))
            }
            TokenKind::Integer(i) => {
                let expr = Expr::Integer(*i);
                tokenizer.next_token();
                Ok(Some(context.typed_expr(expr)))
            }
            TokenKind::StringStart => {
                let content = expect_string(tokenizer, "constant")?;
                let expr = Expr::String {
                    content,
                    storage: None,
                };
                Ok(Some(context.typed_expr(expr)))
            }
            TokenKind::If => {
                tokenizer.next_token();

                let condition = self.parse_expr(tokenizer, context)?.ok_or_else(|| {
                    ParseError::syntax_error(tokenizer.current_position(), "missing condition")
                })?;

                let mut then_body = vec![];
                let mut else_body = None;

                loop {
                    match tokenizer.peek_kind() {
                        TokenKind::Else => break,
                        TokenKind::End => break,
                        _ => self.expect_stmt_push(&mut then_body, tokenizer, context)?,
                    };
                }

                let then_body = self.wrap_stmts(&mut then_body, context);

                if let TokenKind::Else = tokenizer.peek_kind() {
                    let mut body = vec![];
                    expect_token_with(tokenizer, TokenKind::Else)?;

                    loop {
                        match tokenizer.peek_kind() {
                            TokenKind::End => {
                                else_body.replace(self.wrap_stmts(&mut body, context));
                                break;
                            }
                            _ => self.expect_stmt_push(&mut body, tokenizer, context)?,
                        };
                    }
                }
                expect_token_with(tokenizer, TokenKind::End)?;

                let expr = Expr::If {
                    condition: Box::new(condition),
                    then_body,
                    else_body,
                };

                Ok(Some(context.typed_expr(expr)))
            }
            TokenKind::Case => {
                let case_token = tokenizer.next_token();

                let head = self.parse_expr(tokenizer, context)?.ok_or_else(|| {
                    ParseError::syntax_error(
                        tokenizer.current_position(),
                        "Missing head expression after `case`",
                    )
                })?;

                // when, ...
                let mut arms = vec![];

                while let TokenKind::When = tokenizer.peek_kind() {
                    tokenizer.next_token();

                    // pattern
                    let pattern = parse_pattern(tokenizer, context)?.ok_or_else(|| {
                        ParseError::syntax_error(
                            tokenizer.current_position(),
                            "Missing pattern in `when`",
                        )
                    })?;

                    // guard
                    let condition = match tokenizer.peek_kind() {
                        TokenKind::If => {
                            tokenizer.next_token();
                            let cond = self.parse_expr(tokenizer, context)?.ok_or_else(|| {
                                ParseError::syntax_error(
                                    tokenizer.current_position(),
                                    "Missing condition in `when if ...`",
                                )
                            })?;

                            Some(cond)
                        }
                        _ => None,
                    };

                    let mut then_body = vec![];

                    loop {
                        match tokenizer.peek_kind() {
                            TokenKind::When => break,
                            TokenKind::Else => break,
                            TokenKind::End => break,
                            _ => self.expect_stmt_push(&mut then_body, tokenizer, context)?,
                        };
                    }

                    let then_body = self.wrap_stmts(&mut then_body, context);

                    arms.push(CaseArm {
                        pattern,
                        condition,
                        then_body,
                    });
                }

                // else
                let mut else_body = None;

                if let TokenKind::Else = tokenizer.peek_kind() {
                    let mut body = vec![];
                    tokenizer.next_token();

                    loop {
                        match tokenizer.peek_kind() {
                            TokenKind::End => {
                                let body = self.wrap_stmts(&mut body, context);
                                else_body.replace(body);
                                break;
                            }
                            _ => self.expect_stmt_push(&mut body, tokenizer, context)?,
                        };
                    }
                }
                expect_token_with(tokenizer, TokenKind::End)?;

                if arms.is_empty() {
                    return Err(ParseError::syntax_error(
                        case_token.range.start,
                        "At least one arm required for `case`",
                    ));
                }

                let expr = Expr::Case {
                    head: Box::new(head),
                    head_storage: None,
                    arms,
                    else_body,
                };
                Ok(Some(context.typed_expr(expr)))
            }
            token_kind => {
                return Err(ParseError::syntax_error(
                    token.range.start,
                    format!("Unexpected token {}", token_kind),
                ));
            }
        }
    }
}

impl Parser {
    // Wrap an expression with statement if it is not statement.
    fn wrap_stmt(&self, node: Node, context: &mut ParserContext) -> Node {
        if let Expr::Stmt(..) = node.expr {
            // Don't wrap stmt with stmt.
            return node;
        }

        context.typed_expr(Expr::Stmt(Box::new(node)))
    }

    // Wrap an expressions with statements if it is not the last one.
    fn wrap_stmts(&self, nodes: &mut Vec<Option<Node>>, context: &mut ParserContext) -> Vec<Node> {
        let mut stmts = vec![];
        let mut it = nodes.iter_mut().peekable();

        while let Some(node) = it.next() {
            if it.peek().is_none() {
                stmts.push(node.take().unwrap());
            } else {
                stmts.push(self.wrap_stmt(node.take().unwrap(), context));
            }
        }

        stmts
    }

    fn expect_stmt_push(
        &self,
        stmts: &mut Vec<Option<Node>>,
        tokenizer: &mut Tokenizer<'_>,
        context: &mut ParserContext,
    ) -> Result<(), ParseError> {
        if !tokenizer.is_newline_seen() {
            return Err(ParseError::syntax_error(
                tokenizer.current_position(),
                "missing line terminator",
            ));
        }

        let stmt = self.parse_stmt(tokenizer, context)?.ok_or_else(|| {
            ParseError::syntax_error(tokenizer.current_position(), "Premature EOF")
        })?;

        stmts.push(Some(stmt));
        Ok(())
    }
}

fn parse_pattern(
    tokenizer: &mut Tokenizer<'_>,
    context: &mut ParserContext,
) -> Result<Option<Pattern>, ParseError> {
    debug_trace("parse_pattern", tokenizer);

    let pattern = parse_pattern_element(tokenizer, context)?;

    // Assert: Rest pattern must be in `[...]`
    if let Some(Pattern::Rest { .. }) = pattern {
        return Err(ParseError::syntax_error(
            tokenizer.current_position(),
            "Syntax error: Rest pattern must be in `[...]`",
        ));
    }

    Ok(pattern)
}

fn parse_pattern_element(
    tokenizer: &mut Tokenizer<'_>,
    context: &mut ParserContext,
) -> Result<Option<Pattern>, ParseError> {
    debug_trace("parse_pattern_element", tokenizer);

    match tokenizer.peek_kind() {
        TokenKind::Identifier(_) => {
            let name = expect_identifier(tokenizer, "variable or struct name")?;

            if let TokenKind::Char('{') = tokenizer.peek_kind() {
                // struct pattern
                return Ok(Some(parse_struct_pattern(Some(name), tokenizer, context)?));
            }

            Ok(Some(build_variable_pattern(name, context)))
        }
        TokenKind::Integer(i) => {
            let pat = Pattern::Integer(*i);
            tokenizer.next_token();
            Ok(Some(pat))
        }
        TokenKind::Char('[') => {
            expect_char(tokenizer, '[')?;
            let elements = parse_elements(tokenizer, context, ']', &mut |tokenizer, context| {
                parse_pattern_element(tokenizer, context)?.ok_or_else(|| {
                    ParseError::syntax_error(tokenizer.current_position(), "Expected pattern")
                })
            })?;
            expect_char(tokenizer, ']')?;

            // Assert: Rest element must be last element
            if let Some(i) = elements
                .iter()
                .position(|x| matches!(x, Pattern::Rest { .. }))
            {
                if i != (elements.len() - 1) {
                    return Err(ParseError::syntax_error(
                        tokenizer.current_position(),
                        format!("Rest element (#{}) must be last element", i),
                    ));
                }
            }

            Ok(Some(Pattern::Array(elements)))
        }
        TokenKind::Char('{') => Ok(Some(parse_struct_pattern(None, tokenizer, context)?)),
        TokenKind::Rest => {
            expect_token_with(tokenizer, TokenKind::Rest)?;

            // Rest pattern can be ignored by expressing `..._` or `...`.
            match tokenizer.peek_kind() {
                TokenKind::Identifier(_) => {
                    let name = expect_identifier(tokenizer, "rest variable")?;
                    let binding = if name == "_" {
                        wrap(sem::Binding::ignored(&context.type_var()))
                    } else {
                        wrap(sem::Binding::typed_name(&name, &context.type_var()))
                    };

                    Ok(Some(Pattern::Rest {
                        name,
                        binding,
                        reference_offset: None,
                    }))
                }
                _ => {
                    // ignored
                    let binding = wrap(sem::Binding::ignored(&context.type_var()));
                    let pat = Pattern::Rest {
                        name: "".to_string(),
                        binding,
                        reference_offset: None,
                    };
                    Ok(Some(pat))
                }
            }
        }
        _ => Ok(None),
    }
}

fn parse_struct_pattern(
    name: Option<String>,
    tokenizer: &mut Tokenizer<'_>,
    context: &mut ParserContext,
) -> Result<Pattern, ParseError> {
    debug_trace("parse_struct_pattern", tokenizer);

    expect_char(tokenizer, '{')?;

    let fields = parse_elements(tokenizer, context, '}', &mut |tokenizer, context| {
        parse_struct_pattern_field(tokenizer, context)?
            .ok_or_else(|| ParseError::syntax_error(tokenizer.current_position(), "Expected field"))
    })?;
    expect_char(tokenizer, '}')?;

    Ok(Pattern::Struct {
        name,
        fields,
        r#type: None,
    })
}

fn parse_struct_pattern_field(
    tokenizer: &mut Tokenizer<'_>,
    context: &mut ParserContext,
) -> Result<Option<PatternField>, ParseError> {
    debug_trace("parse_struct_pattern_field", tokenizer);

    let name = if let Some(name) = match_identifier(tokenizer, "field name") {
        name
    } else {
        return Ok(None);
    };

    let pattern = if match_char(tokenizer, ':').is_some() {
        parse_pattern_element(tokenizer, context)?.ok_or_else(|| {
            ParseError::syntax_error(tokenizer.current_position(), "Expected value pattern")
        })?
    } else {
        // Desugar: field value can be omitted.
        build_variable_pattern(name.clone(), context)
    };

    Ok(Some(PatternField { name, pattern }))
}

fn parse_elements<F, T>(
    tokenizer: &mut Tokenizer<'_>,
    context: &mut ParserContext,
    stop_char: char,
    parser: &mut F,
) -> Result<Vec<T>, ParseError>
where
    F: Fn(&mut Tokenizer<'_>, &mut ParserContext) -> Result<T, ParseError>,
{
    debug_trace("parse_elements", tokenizer);

    let mut elements = vec![];

    loop {
        if let TokenKind::Char(c) = tokenizer.peek_kind() {
            if *c == stop_char {
                break;
            }
        };

        let element = parser(tokenizer, context)?;
        elements.push(element);

        if let TokenKind::Char(',') = tokenizer.peek_kind() {
            tokenizer.next_token();
        } else {
            break;
        }
    }

    Ok(elements)
}

fn build_variable_pattern(name: String, context: &mut ParserContext) -> Pattern {
    let binding = if name == "_" {
        wrap(sem::Binding::ignored(&context.type_var()))
    } else {
        wrap(sem::Binding::typed_name(&name, &context.type_var()))
    };

    Pattern::Variable(name, binding)
}

fn match_token(tokenizer: &mut Tokenizer<'_>, expected: TokenKind) -> Option<Token> {
    if *tokenizer.peek_kind() == expected {
        Some(tokenizer.next_token())
    } else {
        None
    }
}

fn match_identifier(tokenizer: &mut Tokenizer<'_>, node_kind: &str) -> Option<String> {
    match tokenizer.peek_kind() {
        TokenKind::Identifier(_) => Some(expect_identifier(tokenizer, node_kind).unwrap()),
        _ => None,
    }
}

fn match_char(tokenizer: &mut Tokenizer<'_>, expected: char) -> Option<Token> {
    match_token(tokenizer, TokenKind::Char(expected))
}

fn expect_char(tokenizer: &mut Tokenizer<'_>, expected: char) -> Result<Token, ParseError> {
    expect_token_with(tokenizer, TokenKind::Char(expected))
}

fn expect_token_with(
    tokenizer: &mut Tokenizer<'_>,
    expected: TokenKind,
) -> Result<Token, ParseError> {
    let token = tokenizer.next_token();

    match token {
        token if token.kind == expected => Ok(token),
        token => Err(ParseError::mismatch_token(&token, expected.to_string())),
    }
}

fn expect_identifier(tokenizer: &mut Tokenizer<'_>, node_kind: &str) -> Result<String, ParseError> {
    let token = tokenizer.next_token();

    if let TokenKind::Identifier(name) = token.kind {
        Ok(name)
    } else {
        Err(ParseError::mismatch_token(&token, node_kind))
    }
}

fn expect_string(tokenizer: &mut Tokenizer<'_>, node_kind: &str) -> Result<String, ParseError> {
    let token = tokenizer.next_token();

    if let TokenKind::StringStart = token.kind {
        let mut string = String::new();

        loop {
            let token = tokenizer.next_token();

            match token.kind {
                TokenKind::StringEnd => break,
                TokenKind::StringContent(ref s) => string.push_str(s),
                TokenKind::StringEscapeSequence(c) => string.push(c),
                _ => return Err(ParseError::mismatch_token(&token, node_kind)),
            }
        }

        return Ok(string);
    }

    Err(ParseError::mismatch_token(&token, node_kind))
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Pattern::Variable(name, _) => write!(f, "{}", name),
            Pattern::Integer(i) => write!(f, "{}", i),
            Pattern::Array(patterns) => {
                let mut it = patterns.iter().peekable();

                write!(f, "[")?;
                while let Some(pattern) = it.next() {
                    write!(f, "{}", pattern)?;
                    if it.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "]")
            }
            Pattern::Struct { name, fields, .. } => {
                let mut it = fields.iter().peekable();

                if let Some(name) = name {
                    write!(f, "{} ", name)?;
                }

                write!(f, "{{ ")?;
                while let Some(field) = it.next() {
                    write!(f, "{}: {}", field.name, field.pattern)?;
                    if it.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, " }}")
            }
            Pattern::Rest { name, .. } => write!(f, "...{}", name),
        }
    }
}

impl Expr {
    pub fn short_name(&self) -> String {
        match self {
            Expr::Integer(i) => format!("Integer({})", i),
            Expr::String { content, .. } => format!("String(\"{}\")", content),
            Expr::Identifier { name, .. } => format!("Identifier(`{}`)", name),
            Expr::Array { elements, .. } => format!("Array[{}]", elements.len()),
            Expr::Subscript { .. } => "x[...]".to_string(),
            Expr::Access { field, .. } => format!("x.{}", field),
            Expr::Invocation {
                name, arguments, ..
            } => format!("{}({} args)", name, arguments.len()),
            Expr::Struct { name, fields, .. } => {
                format!("struct {} {{{} fields}}", name, fields.len())
            }
            Expr::Add(_, _, _) => "a + b".to_string(),
            Expr::Sub(_, _, _) => "a - b".to_string(),
            Expr::Rem(_, _, _) => "a % b".to_string(),
            Expr::Mul(_, _, _) => "a * b".to_string(),
            Expr::Div(_, _, _) => "a / b".to_string(),
            Expr::Lt(_, _, _) => "a < b".to_string(),
            Expr::Gt(_, _, _) => "a > b".to_string(),
            Expr::Le(_, _, _) => "a <= b".to_string(),
            Expr::Ge(_, _, _) => "a >= b".to_string(),
            Expr::Eq(_, _, _) => "a == b".to_string(),
            Expr::Ne(_, _, _) => "a != b".to_string(),
            Expr::Plus(_, _) => "+a".to_string(),
            Expr::Minus(_, _) => "-a".to_string(),
            Expr::Stmt(node) => format!("Stmt({})", node.expr.short_name()),
            Expr::If { .. } => "if".to_string(),
            Expr::Case { .. } => "case".to_string(),
            Expr::Var { .. } => "let".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;

    #[test]
    fn number_integer() {
        let program = parse_string("42").unwrap();
        assert!(program.functions.is_empty());
        assert!(program.main.is_some());

        let expr = &program.main.unwrap().body[0].expr;
        assert_matches!(expr, Expr::Integer(42));
    }

    #[test]
    fn number_integer_followed_by_letter() {
        let program = parse_string("123a").unwrap();
        assert!(program.functions.is_empty());

        let node = &program.main.unwrap().body[0];
        assert_matches!(&node.expr, Expr::Stmt(expr) => {
            assert_matches!(expr.expr, Expr::Integer(123));
        });
    }

    #[test]
    fn add_integer() {
        let program = parse_string("1 + 2").unwrap();
        assert!(program.functions.is_empty());

        let body = program.main.unwrap().body;
        assert_matches!(&body[0].expr, Expr::Add(lhs, rhs, None) => {
            assert_matches!(&lhs.expr, Expr::Integer(1));
            assert_matches!(&rhs.expr, Expr::Integer(2));
        });
    }

    #[test]
    fn operator_associative() {
        let program = parse_string("1 + 2 + 3").unwrap();
        assert!(program.functions.is_empty());

        let body = program.main.unwrap().body;
        assert_matches!(&body[0].expr, Expr::Add(lhs, rhs, None) => {
            assert_matches!(&lhs.expr, Expr::Add(x, y, None) => {
                assert_matches!(x.expr, Expr::Integer(1));
                assert_matches!(y.expr, Expr::Integer(2));
            });
            assert_matches!(&rhs.expr, Expr::Integer(3));
        });
    }
    #[test]
    fn paren_grouping() {
        let program = parse_string("(1 + 2) * 3").unwrap();
        assert!(program.functions.is_empty());

        let body = program.main.unwrap().body;
        assert_matches!(&body[0].expr, Expr::Mul(lhs, rhs, None) => {
            assert_matches!(&lhs.expr, Expr::Add(x, y, _) => {
                assert_matches!(x.expr, Expr::Integer(1));
                assert_matches!(y.expr, Expr::Integer(2));
            });
            assert_matches!(&rhs.expr, Expr::Integer(3));
        });
    }

    #[test]
    fn paren_array_empty() {
        let program = parse_string("[]").unwrap();
        let body = program.main.unwrap().body;

        assert_matches!(&body[0].expr, Expr::Array { elements, .. } => {
            assert!(elements.is_empty());
        });
    }

    #[test]
    fn paren_array() {
        let program = parse_string("[1, 2, 3]").unwrap();
        let body = program.main.unwrap().body;

        assert_matches!(&body[0].expr, Expr::Array { elements, .. } => {
            assert_matches!(elements[0].expr, Expr::Integer(1));
            assert_matches!(elements[1].expr, Expr::Integer(2));
            assert_matches!(elements[2].expr, Expr::Integer(3));
        });
    }

    #[test]
    fn parse_newline0() {
        let program = parse_string("1+\n2").unwrap();
        let body = program.main.unwrap().body;

        assert_matches!(&body[0].expr, Expr::Add(lhs, rhs, None) => {
            assert_matches!(&lhs.expr, Expr::Integer(1));
            assert_matches!(&rhs.expr, Expr::Integer(2));
        });
    }

    #[test]
    fn parse_newline1() {
        let program = parse_string("1\n+2").unwrap();
        let body = program.main.unwrap().body;

        assert_matches!(&body[0].expr, Expr::Stmt(node) => {
            assert_matches!(&node.expr, Expr::Integer(1));
        });
        assert_matches!(&body[1].expr, Expr::Plus(operand, None) => {
            assert_matches!(&operand.expr, Expr::Integer(2));
        });
    }
}
