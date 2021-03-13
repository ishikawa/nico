use crate::asm;
use crate::asm::wasm;
use crate::sem;
use crate::tokenizer::{Token, Tokenizer};
use crate::util::naming::PrefixNaming;
use crate::util::wrap;
use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

// Program
pub struct Module {
    pub functions: Vec<Function>,
    pub main: Option<Function>,
    pub strings: Option<Vec<Rc<RefCell<asm::ConstantString>>>>,
}

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
        // Stack: the offset from the end of Static in stack frame.
        //
        // ----+-----------+-----------+-----+-------------+
        //     | element 0 | element 1 | ... | Caller's FP |
        // ----o-----------+-----------+-----o-------------+
        //     |<----------------------------|
        object_offset: Option<wasm::Size>,
    },
    Subscript {
        operand: Box<Node>,
        index: Box<Node>,
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
    LT(Box<Node>, Box<Node>, Option<Rc<RefCell<sem::Binding>>>), // Less Than
    GT(Box<Node>, Box<Node>, Option<Rc<RefCell<sem::Binding>>>), // Greater Than
    LE(Box<Node>, Box<Node>, Option<Rc<RefCell<sem::Binding>>>), // Less than Equal
    GE(Box<Node>, Box<Node>, Option<Rc<RefCell<sem::Binding>>>), // Greater than Equal
    EQ(Box<Node>, Box<Node>, Option<Rc<RefCell<sem::Binding>>>), // Equal
    NE(Box<Node>, Box<Node>, Option<Rc<RefCell<sem::Binding>>>), // Not Equal

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
    Rest {
        name: String,
        binding: Rc<RefCell<sem::Binding>>,
        reference_offset: Option<wasm::Size>,
    },
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

impl Parser {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn parse(&self, tokenizer: &mut Tokenizer) -> Box<Module> {
        let mut context = ParserContext {
            naming: PrefixNaming::new("?"),
        };

        let mut functions = vec![];

        while let Some(function) = self.parse_function(tokenizer, &mut context) {
            functions.push(function);
        }

        // Parser collects top expressions and automatically build
        // `main` function which is the entry point of a program.
        let mut body = vec![];

        while let Some(expr) = self.parse_stmt(tokenizer, &mut context) {
            body.push(Some(expr));
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

        Box::new(Module {
            functions,
            main,
            strings: None,
        })
    }

    fn parse_function(
        &self,
        tokenizer: &mut Tokenizer,
        context: &mut ParserContext,
    ) -> Option<Function> {
        // modifiers
        let export = match tokenizer.peek() {
            Some(Token::Export) => {
                tokenizer.next();
                true
            }
            _ => false,
        };

        // fun
        match tokenizer.peek() {
            Some(Token::Fun) => {
                tokenizer.next();
            }
            _ => return None,
        };

        let name = match tokenizer.next() {
            Some(Token::Identifier(name)) => name,
            Some(token) => panic!("Expected function name, but was {:?}", token),
            None => panic!("Premature EOF, no function name"),
        };

        let mut param_names = vec![];

        consume_char(tokenizer, '(');
        while let Some(Token::Identifier(name)) = tokenizer.peek() {
            param_names.push(name.clone());
            tokenizer.next();

            match tokenizer.peek() {
                Some(Token::Char(',')) => {
                    tokenizer.next();
                }
                _ => break,
            };
        }
        consume_char(tokenizer, ')');
        // TODO: check line separator before reading body

        let mut body = vec![];

        loop {
            match tokenizer.peek() {
                None => panic!("Premature EOF"),
                Some(Token::End) => break,
                _ => {}
            };

            match self.parse_stmt(tokenizer, context) {
                None => break,
                Some(node) => body.push(Some(node)),
            };
        }
        consume_token(tokenizer, Token::End);

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

            Some(function)
        }
    }

    /// Returns `Stmt` if the result of `parse_stmt_expr()` is a variable binding.
    fn parse_stmt(&self, tokenizer: &mut Tokenizer, context: &mut ParserContext) -> Option<Node> {
        let node = match self.parse_stmt_expr(tokenizer, context) {
            Some(node) => node,
            None => return None,
        };

        if let Expr::Var { .. } = node.expr {
            return Some(self.wrap_stmt(node, context));
        }

        Some(node)
    }

    /// Variable binding or `Expr`
    fn parse_stmt_expr(
        &self,
        tokenizer: &mut Tokenizer,
        context: &mut ParserContext,
    ) -> Option<Node> {
        match tokenizer.peek() {
            Some(Token::Let) => {
                tokenizer.next();
            }
            _ => return self.parse_expr(tokenizer, context),
        };

        // Variable binding - Pattern
        let pattern =
            parse_pattern(tokenizer, context).unwrap_or_else(|| panic!("Missing pattern in `let`"));

        consume_char(tokenizer, '=');

        let init = self
            .parse_expr(tokenizer, context)
            .unwrap_or_else(|| panic!("No initializer"));

        Some(context.typed_expr(Expr::Var {
            pattern,
            init: Box::new(init),
        }))
    }

    fn parse_expr(&self, tokenizer: &mut Tokenizer, context: &mut ParserContext) -> Option<Node> {
        self.parse_rel_op1(tokenizer, context)
    }

    // "==", "!="
    fn parse_rel_op1(
        &self,
        tokenizer: &mut Tokenizer,
        context: &mut ParserContext,
    ) -> Option<Node> {
        let lhs = match self.parse_rel_op2(tokenizer, context) {
            Some(lhs) => lhs,
            None => return None,
        };

        let builder = match tokenizer.peek() {
            Some(Token::EQ) => Expr::EQ,
            Some(Token::NE) => Expr::NE,
            _ => return Some(lhs),
        };
        tokenizer.next();

        let rhs = match self.parse_rel_op2(tokenizer, context) {
            None => panic!("Expected RHS"),
            Some(rhs) => rhs,
        };

        Some(context.typed_expr(builder(Box::new(lhs), Box::new(rhs), None)))
    }

    // ">", "<", ">=", "<="
    fn parse_rel_op2(
        &self,
        tokenizer: &mut Tokenizer,
        context: &mut ParserContext,
    ) -> Option<Node> {
        let lhs = match self.parse_binary_op1(tokenizer, context) {
            Some(lhs) => lhs,
            None => return None,
        };

        let builder = match tokenizer.peek() {
            Some(Token::LE) => Expr::LE,
            Some(Token::GE) => Expr::GE,
            Some(Token::Char('<')) => Expr::LT,
            Some(Token::Char('>')) => Expr::GT,
            _ => return Some(lhs),
        };
        tokenizer.next();

        let rhs = match self.parse_binary_op1(tokenizer, context) {
            None => panic!("Expected RHS"),
            Some(rhs) => rhs,
        };

        Some(context.typed_expr(builder(Box::new(lhs), Box::new(rhs), None)))
    }

    fn parse_binary_op1(
        &self,
        tokenizer: &mut Tokenizer,
        context: &mut ParserContext,
    ) -> Option<Node> {
        let mut lhs = match self.parse_binary_op2(tokenizer, context) {
            None => return None,
            Some(lhs) => lhs,
        };

        loop {
            let builder = match tokenizer.peek() {
                Some(Token::Char('+')) => Expr::Add,
                Some(Token::Char('-')) => Expr::Sub,
                Some(Token::Char('%')) => Expr::Rem,
                _ => break,
            };

            // A newline character terminates node construction.
            if tokenizer.is_newline_seen() {
                break;
            }

            tokenizer.next();

            let rhs = match self.parse_binary_op2(tokenizer, context) {
                None => panic!("Expected RHS"),
                Some(rhs) => rhs,
            };

            lhs = context.typed_expr(builder(Box::new(lhs), Box::new(rhs), None));
        }

        Some(lhs)
    }

    fn parse_binary_op2(
        &self,
        tokenizer: &mut Tokenizer,
        context: &mut ParserContext,
    ) -> Option<Node> {
        let mut lhs = match self.parse_unary_op(tokenizer, context) {
            None => return None,
            Some(lhs) => lhs,
        };

        loop {
            let builder = match tokenizer.peek() {
                Some(Token::Char('*')) => Expr::Mul,
                Some(Token::Char('/')) => Expr::Div,
                Some(_) => break,
                None => return Some(lhs),
            };
            tokenizer.next();

            let rhs = match self.parse_unary_op(tokenizer, context) {
                None => panic!("Expected RHS"),
                Some(rhs) => rhs,
            };

            lhs = context.typed_expr(builder(Box::new(lhs), Box::new(rhs), None));
        }

        Some(lhs)
    }

    fn parse_unary_op(
        &self,
        tokenizer: &mut Tokenizer,
        context: &mut ParserContext,
    ) -> Option<Node> {
        let builder = match tokenizer.peek() {
            None => return None,
            Some(Token::Char('+')) => Expr::Plus,
            Some(Token::Char('-')) => Expr::Minus,
            Some(_) => return self.parse_access(tokenizer, context),
        };
        tokenizer.next();

        // unary operators are right associative.
        let expr = match self.parse_unary_op(tokenizer, context) {
            None => panic!("Expected operand"),
            Some(node) => builder(Box::new(node), None),
        };

        Some(context.typed_expr(expr))
    }

    // `... [...]`, `... (...)`
    fn parse_access(&self, tokenizer: &mut Tokenizer, context: &mut ParserContext) -> Option<Node> {
        let mut node = self.parse_primary(tokenizer, context)?;

        loop {
            let token = match tokenizer.peek() {
                None => return Some(node),
                Some(token) => token,
            };

            match token {
                Token::Char('[') => {
                    consume_char(tokenizer, '[');
                    let mut arguments =
                        parse_elements(tokenizer, context, ']', &mut |tokenizer, context| {
                            self.parse_expr(tokenizer, context)
                                .expect("Expected subscript argument")
                        });
                    consume_char(tokenizer, ']');

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
                _ => return Some(node),
            }
        }
    }

    fn parse_primary(
        &self,
        tokenizer: &mut Tokenizer,
        context: &mut ParserContext,
    ) -> Option<Node> {
        let token = match tokenizer.peek() {
            None => return None,
            Some(token) => token,
        };

        match token {
            Token::Char('(') => {
                consume_char(tokenizer, '(');
                let node = self.parse_expr(tokenizer, context);
                consume_char(tokenizer, ')');
                node
            }
            Token::Char('[') => {
                consume_char(tokenizer, '[');
                let elements =
                    parse_elements(tokenizer, context, ']', &mut |tokenizer, context| {
                        self.parse_expr(tokenizer, context)
                            .expect("Expected element")
                    });
                consume_char(tokenizer, ']');

                Some(context.typed_expr(Expr::Array {
                    elements,
                    object_offset: None,
                }))
            }
            Token::Identifier(name) => {
                let name = name.clone();
                tokenizer.next();

                // function invocation?
                // TODO: Move to parse_access()
                if let Some(Token::Char('(')) = tokenizer.peek() {
                    consume_char(tokenizer, '(');
                    let arguments =
                        parse_elements(tokenizer, context, ')', &mut |tokenizer, context| {
                            self.parse_expr(tokenizer, context)
                                .expect("Expected argument")
                        });
                    consume_char(tokenizer, ')');

                    Some(context.typed_expr(Expr::Invocation {
                        name,
                        arguments,
                        binding: None,
                    }))
                } else {
                    Some(context.typed_expr(Expr::Identifier {
                        name,
                        binding: None,
                    }))
                }
            }
            Token::Integer(i) => {
                let expr = Expr::Integer(*i);
                tokenizer.next();
                Some(context.typed_expr(expr))
            }
            Token::String(s) => {
                let expr = Expr::String {
                    content: s.clone(),
                    storage: None,
                };
                tokenizer.next();
                Some(context.typed_expr(expr))
            }
            Token::If => {
                tokenizer.next();

                let condition = self
                    .parse_expr(tokenizer, context)
                    .expect("missing condition");
                // TODO: check line separator before reading body

                let mut then_body = vec![];
                let mut else_body = None;

                loop {
                    match tokenizer.peek() {
                        None => panic!("Premature EOF"),
                        Some(Token::Else) => break,
                        Some(Token::End) => break,
                        _ => {
                            let stmt = self
                                .parse_stmt(tokenizer, context)
                                .unwrap_or_else(|| panic!("Premature EOF"));
                            then_body.push(Some(stmt));
                        }
                    };
                }

                let then_body = self.wrap_stmts(&mut then_body, context);

                if let Some(Token::Else) = tokenizer.peek() {
                    let mut body = vec![];

                    consume_token(tokenizer, Token::Else);

                    // TODO: check line separator before reading body
                    loop {
                        match tokenizer.peek() {
                            None => panic!("Premature EOF"),
                            Some(Token::End) => {
                                else_body.replace(self.wrap_stmts(&mut body, context));
                                break;
                            }
                            _ => {
                                let stmt = self
                                    .parse_stmt(tokenizer, context)
                                    .unwrap_or_else(|| panic!("Premature EOF"));
                                body.push(Some(stmt));
                            }
                        };
                    }
                }
                consume_token(tokenizer, Token::End);

                let expr = Expr::If {
                    condition: Box::new(condition),
                    then_body,
                    else_body,
                };

                Some(context.typed_expr(expr))
            }
            Token::Case => {
                tokenizer.next();

                let head = self
                    .parse_expr(tokenizer, context)
                    .expect("Missing head expression after `case`");

                // when, ...
                let mut arms = vec![];

                while let Some(Token::When) = tokenizer.peek() {
                    tokenizer.next();

                    // pattern
                    let pattern = parse_pattern(tokenizer, context)
                        .unwrap_or_else(|| panic!("Missing pattern in `when`"));

                    // guard
                    let condition = match tokenizer.peek() {
                        Some(Token::If) => {
                            tokenizer.next();
                            let cond = self
                                .parse_expr(tokenizer, context)
                                .expect("Missing condition in `when if ...`");
                            Some(cond)
                        }
                        _ => None,
                    };

                    // TODO: check line separator before reading body
                    let mut then_body = vec![];

                    loop {
                        match tokenizer.peek() {
                            None => panic!("Premature EOF"),
                            Some(Token::When) => break,
                            Some(Token::Else) => break,
                            Some(Token::End) => break,
                            _ => {
                                let stmt = self
                                    .parse_stmt(tokenizer, context)
                                    .unwrap_or_else(|| panic!("Premature EOF"));
                                then_body.push(Some(stmt));
                            }
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

                if let Some(Token::Else) = tokenizer.peek() {
                    let mut body = vec![];
                    tokenizer.next();

                    loop {
                        match tokenizer.peek() {
                            None => panic!("Premature EOF"),
                            Some(Token::End) => {
                                let body = self.wrap_stmts(&mut body, context);
                                else_body.replace(body);
                                break;
                            }
                            _ => {
                                let stmt = self
                                    .parse_stmt(tokenizer, context)
                                    .unwrap_or_else(|| panic!("Premature EOF"));
                                body.push(Some(stmt));
                            }
                        };
                    }
                }
                consume_token(tokenizer, Token::End);

                if arms.is_empty() {
                    panic!("At least one arm required for `case`")
                }

                let expr = Expr::Case {
                    head: Box::new(head),
                    head_storage: None,
                    arms,
                    else_body,
                };
                Some(context.typed_expr(expr))
            }
            token => panic!("Unexpected token {:?}", token),
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
}

fn parse_pattern(tokenizer: &mut Tokenizer, context: &mut ParserContext) -> Option<Pattern> {
    let pattern = parse_pattern_element(tokenizer, context);

    // Assert: Rest pattern must be in `[...]`
    if let Some(Pattern::Rest { .. }) = pattern {
        panic!("Syntax error: Rest pattern must be in `[...]`");
    }

    pattern
}

fn parse_pattern_element(
    tokenizer: &mut Tokenizer,
    context: &mut ParserContext,
) -> Option<Pattern> {
    match tokenizer.peek()? {
        Token::Identifier(ref name) => {
            let binding = wrap(sem::Binding::typed_name(name, &context.type_var()));
            let pat = Pattern::Variable(name.clone(), binding);
            tokenizer.next();
            Some(pat)
        }
        Token::Integer(i) => {
            let pat = Pattern::Integer(*i);
            tokenizer.next();
            Some(pat)
        }
        Token::Char('[') => {
            consume_char(tokenizer, '[');
            let elements = parse_elements(tokenizer, context, ']', &mut |tokenizer, context| {
                parse_pattern_element(tokenizer, context).expect("Expected pattern")
            });
            consume_char(tokenizer, ']');

            // Assert: Rest element must be last element
            if let Some(i) = elements
                .iter()
                .position(|x| matches!(x, Pattern::Rest {..}))
            {
                if i != (elements.len() - 1) {
                    panic!("Syntax error: Rest element (#{}) must be last element", i);
                }
            }

            Some(Pattern::Array(elements))
        }
        Token::Rest => {
            consume_token(tokenizer, Token::Rest);

            match tokenizer.peek() {
                Some(Token::Identifier(name)) => {
                    let binding = wrap(sem::Binding::typed_name(name, &context.type_var()));
                    let pat = Pattern::Rest {
                        name: name.clone(),
                        binding,
                        reference_offset: None,
                    };
                    tokenizer.next();
                    Some(pat)
                }
                t => panic!(
                    "`...` must be followed by an identifier, but it was followed by {:?}",
                    t
                ),
            }
        }
        _ => None,
    }
}

fn parse_elements<F, T>(
    tokenizer: &mut Tokenizer,
    context: &mut ParserContext,
    stop_char: char,
    parser: &mut F,
) -> Vec<T>
where
    F: Fn(&mut Tokenizer, &mut ParserContext) -> T,
{
    let mut elements = vec![];

    loop {
        match tokenizer.peek() {
            None => panic!("Premature EOF"),
            Some(Token::Char(c)) => {
                if *c == stop_char {
                    break;
                }
            }
            _ => {}
        };

        let element = parser(tokenizer, context);
        elements.push(element);

        if let Some(Token::Char(',')) = tokenizer.peek() {
            tokenizer.next();
        } else {
            break;
        }
    }

    elements
}

pub fn parse_string<S: AsRef<str>>(src: S) -> Box<Module> {
    let mut tokenizer = Tokenizer::from_string(&src);
    let parser = Parser::new();
    parser.parse(&mut tokenizer)
}

fn consume_token(tokenizer: &mut Tokenizer, expected: Token) {
    match tokenizer.next() {
        None => panic!("Premature EOF"),
        Some(token) if token == expected => {}
        Some(token) => panic!("Expected token \"{:?}\", but was {:?}", expected, token),
    }
}

fn consume_char(tokenizer: &mut Tokenizer, expected: char) {
    consume_token(tokenizer, Token::Char(expected));
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
            Expr::Invocation {
                name, arguments, ..
            } => format!("{}({} args)", name, arguments.len()),
            Expr::Add(_, _, _) => "a + b".to_string(),
            Expr::Sub(_, _, _) => "a - b".to_string(),
            Expr::Rem(_, _, _) => "a % b".to_string(),
            Expr::Mul(_, _, _) => "a * b".to_string(),
            Expr::Div(_, _, _) => "a / b".to_string(),
            Expr::LT(_, _, _) => "a < b".to_string(),
            Expr::GT(_, _, _) => "a > b".to_string(),
            Expr::LE(_, _, _) => "a <= b".to_string(),
            Expr::GE(_, _, _) => "a >= b".to_string(),
            Expr::EQ(_, _, _) => "a == b".to_string(),
            Expr::NE(_, _, _) => "a != b".to_string(),
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
        let program = parse_string("42");
        assert!(program.functions.is_empty());

        let expr = &program.main.unwrap().body[0].expr;
        assert_matches!(expr, Expr::Integer(42));
    }
    #[test]
    fn number_integer_followed_by_letter() {
        let program = parse_string("123a");
        assert!(program.functions.is_empty());

        let node = &program.main.unwrap().body[0];
        assert_matches!(&node.expr, Expr::Stmt(expr) => {
            assert_matches!(expr.expr, Expr::Integer(123));
        });
    }

    #[test]
    fn add_integer() {
        let program = parse_string("1 + 2");
        assert!(program.functions.is_empty());

        let body = program.main.unwrap().body;
        assert_matches!(&body[0].expr, Expr::Add(lhs, rhs, None) => {
            assert_matches!(&lhs.expr, Expr::Integer(1));
            assert_matches!(&rhs.expr, Expr::Integer(2));
        });
    }

    #[test]
    fn operator_associative() {
        let program = parse_string("1 + 2 + 3");
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
        let program = parse_string("(1 + 2) * 3");
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
        let program = parse_string("[]");
        let body = program.main.unwrap().body;

        assert_matches!(&body[0].expr, Expr::Array { elements, .. } => {
            assert!(elements.is_empty());
        });
    }

    #[test]
    fn paren_array() {
        let program = parse_string("[1, 2, 3]");
        let body = program.main.unwrap().body;

        assert_matches!(&body[0].expr, Expr::Array { elements, .. } => {
            assert_matches!(elements[0].expr, Expr::Integer(1));
            assert_matches!(elements[1].expr, Expr::Integer(2));
            assert_matches!(elements[2].expr, Expr::Integer(3));
        });
    }

    #[test]
    fn parse_newline0() {
        let program = parse_string("1+\n2");
        let body = program.main.unwrap().body;

        assert_matches!(&body[0].expr, Expr::Add(lhs, rhs, None) => {
            assert_matches!(&lhs.expr, Expr::Integer(1));
            assert_matches!(&rhs.expr, Expr::Integer(2));
        });
    }

    #[test]
    fn parse_newline1() {
        let program = parse_string("1\n+2");
        let body = program.main.unwrap().body;

        assert_matches!(&body[0].expr, Expr::Stmt(node) => {
            assert_matches!(&node.expr, Expr::Integer(1));
        });
        assert_matches!(&body[1].expr, Expr::Plus(operand, None) => {
            assert_matches!(&operand.expr, Expr::Integer(2));
        });
    }
}
