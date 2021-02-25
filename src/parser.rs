use crate::asm;
use crate::sem;
use crate::tokenizer::{Token, Tokenizer};
use crate::util::naming::PrefixNaming;
use crate::util::wrap;
use std::cell::RefCell;
use std::iter::Peekable;
use std::rc::Rc;

// Program
pub struct Module {
    pub functions: Vec<Function>,
    pub main: Option<Box<Function>>,
    // metadata
    pub env: Rc<RefCell<sem::Environment>>,
    pub strings: Option<Vec<Rc<RefCell<asm::ConstantString>>>>,
}

#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub body: Vec<Node>,
    pub export: bool,
    // metadata
    pub params: Vec<Rc<RefCell<sem::Binding>>>,
    pub locals: Vec<Rc<RefCell<asm::LocalStorage>>>,
    pub env: Rc<RefCell<sem::Environment>>,
    pub r#type: Rc<RefCell<sem::Type>>,
}

#[derive(Debug)]
pub struct Node {
    pub expr: Expr,
    // metadata
    pub env: Rc<RefCell<sem::Environment>>,
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
    Invocation {
        name: String,
        arguments: Vec<Node>,
        // A function that the invocation refers.
        binding: Option<Rc<RefCell<sem::Binding>>>,
    },

    // binop :: LHS, RHS, Binding
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

    // Statement
    Stmt(Box<Node>),

    // Control flow
    If {
        condition: Box<Node>,
        then_body: Vec<Node>,
        else_body: Vec<Node>,
    },
    Case {
        head: Box<Node>, // head expression
        head_storage: Option<Rc<RefCell<asm::LocalStorage>>>,
        arms: Vec<CaseArm>,
        else_body: Vec<Node>,
    },

    // Variable binding
    Var {
        pattern: Pattern,
        init: Box<Node>,
    },
}

#[derive(Debug)]
pub enum Pattern {
    Variable(String, Option<Rc<RefCell<sem::Binding>>>),
}

#[derive(Debug)]
pub struct CaseArm {
    pub pattern: Pattern,
    pub condition: Option<Box<Node>>, // guard
    pub then_body: Vec<Node>,
}

#[derive(Debug)]
pub struct Parser {
    naming: PrefixNaming,
    // This is the environment that will be used as a placeholder
    // until the correct scope chain is assigned in the semantic analysis.
    empty_env: Rc<RefCell<sem::Environment>>,
}

impl Default for Parser {
    fn default() -> Self {
        Self::new()
    }
}

impl Parser {
    pub fn new() -> Self {
        Self {
            naming: PrefixNaming::new("?"),
            empty_env: Rc::new(RefCell::new(sem::Environment::new())),
        }
    }

    pub fn parse(&mut self, tokenizer: &mut Tokenizer) -> Box<Module> {
        let mut tokenizer = tokenizer.peekable();

        let mut functions = vec![];

        while let Some(function) = self.parse_function(&mut tokenizer) {
            functions.push(*function);
        }

        // Parser collects top expressions and automatically build
        // `main` function which is the entry point of a program.
        let mut body = vec![];

        while let Some(expr) = self.parse_stmt(&mut tokenizer) {
            body.push(Some(*expr));
        }

        let body = self.wrap_stmts(&mut body);

        let main = if !body.is_empty() {
            let fun = Function {
                name: "main".to_string(),
                body,
                export: true,
                params: vec![],
                locals: vec![],
                env: Rc::clone(&self.empty_env),
                r#type: wrap(sem::Type::Function {
                    params: vec![],
                    return_type: self.type_var(),
                }),
            };

            Some(Box::new(fun))
        } else {
            None
        };

        Box::new(Module {
            functions,
            main,
            env: Rc::clone(&self.empty_env),
            strings: None,
        })
    }

    fn parse_function(
        &mut self,
        tokenizer: &mut Peekable<&mut Tokenizer>,
    ) -> Option<Box<Function>> {
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

            match self.parse_stmt(tokenizer) {
                None => break,
                Some(node) => body.push(Some(*node)),
            };
        }
        consume_token(tokenizer, Token::End);

        let body = self.wrap_stmts(&mut body);

        {
            let param_types = param_names
                .iter()
                .map(|_| self.type_var())
                .collect::<Vec<_>>();

            let params = param_names
                .iter()
                .zip(&param_types)
                .map(|(name, ty)| {
                    wrap(sem::Binding::Variable {
                        name: name.clone(),
                        r#type: Rc::clone(ty),
                        storage: None,
                    })
                })
                .collect::<Vec<_>>();

            let function_type = wrap(sem::Type::Function {
                params: param_types,
                return_type: self.type_var(),
            });

            let function = Function {
                name,
                params,
                export,
                locals: vec![],
                body,
                env: Rc::clone(&self.empty_env),
                r#type: function_type,
            };

            Some(Box::new(function))
        }
    }

    /// Returns `Stmt` if the result of `parse_stmt_expr()` is a variable binding.
    fn parse_stmt(&mut self, tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
        let node = match self.parse_stmt_expr(tokenizer) {
            Some(node) => node,
            None => return None,
        };

        if let Expr::Var { .. } = node.expr {
            return Some(Box::new(self.wrap_stmt(*node)));
        }

        Some(node)
    }

    /// Variable binding or `Expr`
    fn parse_stmt_expr(&mut self, tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
        match tokenizer.peek() {
            Some(Token::Let) => {
                tokenizer.next();
            }
            _ => return self.parse_expr(tokenizer),
        };

        // Variable binding - Pattern
        let pattern = self
            .parse_pattern(tokenizer)
            .unwrap_or_else(|| panic!("Missing pattern in `when`"));

        consume_char(tokenizer, '=');

        let init = self
            .parse_expr(tokenizer)
            .unwrap_or_else(|| panic!("No initializer"));

        Some(Box::new(self.typed_expr(Expr::Var { pattern, init })))
    }

    fn parse_expr(&mut self, tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
        self.parse_relop1(tokenizer)
    }

    // "==", "!="
    fn parse_relop1(&mut self, tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
        let lhs = match self.parse_relop2(tokenizer) {
            Some(lhs) => lhs,
            None => return None,
        };

        let builder = match tokenizer.peek() {
            Some(Token::EQ) => Expr::EQ,
            Some(Token::NE) => Expr::NE,
            _ => return Some(lhs),
        };
        tokenizer.next();

        let rhs = match self.parse_relop2(tokenizer) {
            None => panic!("Expected RHS"),
            Some(rhs) => rhs,
        };

        Some(Box::new(self.typed_expr(builder(lhs, rhs, None))))
    }

    // ">", "<", ">=", "<="
    fn parse_relop2(&mut self, tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
        let lhs = match self.parse_binop1(tokenizer) {
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

        let rhs = match self.parse_binop1(tokenizer) {
            None => panic!("Expected RHS"),
            Some(rhs) => rhs,
        };

        Some(Box::new(self.typed_expr(builder(lhs, rhs, None))))
    }

    fn parse_binop1(&mut self, tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
        let mut lhs = match self.parse_binop2(tokenizer) {
            None => return None,
            Some(lhs) => lhs,
        };

        loop {
            let builder = match tokenizer.peek() {
                Some(Token::Char('+')) => Expr::Add,
                Some(Token::Char('-')) => Expr::Sub,
                Some(Token::Char('%')) => Expr::Rem,
                Some(_) => break,
                None => return Some(lhs),
            };
            tokenizer.next();

            let rhs = match self.parse_binop2(tokenizer) {
                None => panic!("Expected RHS"),
                Some(rhs) => rhs,
            };

            lhs = Box::new(self.typed_expr(builder(lhs, rhs, None)));
        }

        Some(lhs)
    }

    fn parse_binop2(&mut self, tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
        let mut lhs = match self.parse_primary(tokenizer) {
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

            let rhs = match self.parse_primary(tokenizer) {
                None => panic!("Expected RHS"),
                Some(rhs) => rhs,
            };

            lhs = Box::new(self.typed_expr(builder(lhs, rhs, None)));
        }

        Some(lhs)
    }

    fn parse_primary(&mut self, tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
        let token = match tokenizer.peek() {
            None => return None,
            Some(token) => token,
        };

        match token {
            Token::Char('(') => {
                consume_char(tokenizer, '(');
                let node = self.parse_expr(tokenizer);
                consume_char(tokenizer, ')');
                node
            }
            Token::Identifier(name) => {
                let name = name.clone();
                tokenizer.next();

                // function invocation?
                if let Some(Token::Char('(')) = tokenizer.peek() {
                    let mut arguments = vec![];

                    consume_char(tokenizer, '(');
                    loop {
                        if let Some(Token::Char(')')) = tokenizer.peek() {
                            break;
                        }

                        let expr = self.parse_expr(tokenizer).expect("Expected param");
                        arguments.push(*expr);

                        if let Some(Token::Char(',')) = tokenizer.peek() {
                            tokenizer.next();
                        } else {
                            break;
                        }
                    }
                    consume_char(tokenizer, ')');
                    Some(Box::new(self.typed_expr(Expr::Invocation {
                        name,
                        arguments,
                        binding: None,
                    })))
                } else {
                    Some(Box::new(self.typed_expr(Expr::Identifier {
                        name,
                        binding: None,
                    })))
                }
            }
            Token::Integer(i) => {
                let expr = Expr::Integer(*i);
                tokenizer.next();
                Some(Box::new(self.typed_expr(expr)))
            }
            Token::String(s) => {
                let expr = Expr::String {
                    content: s.clone(),
                    storage: None,
                };
                tokenizer.next();
                Some(Box::new(self.typed_expr(expr)))
            }
            Token::If => {
                tokenizer.next();

                let condition = self.parse_expr(tokenizer).expect("missing condition");
                // TODO: check line separator before reading body

                let mut then_body = vec![];
                let mut else_body = vec![];
                let mut has_else = false;

                loop {
                    match tokenizer.peek() {
                        None => panic!("Premature EOF"),
                        Some(Token::Else) => {
                            // TODO: check line separator before reading body
                            has_else = true;
                            break;
                        }
                        Some(Token::End) => break,
                        _ => {}
                    };

                    match self.parse_stmt(tokenizer) {
                        None => break,
                        Some(node) => then_body.push(Some(*node)),
                    };
                }

                if has_else {
                    consume_token(tokenizer, Token::Else);

                    loop {
                        match tokenizer.peek() {
                            None => panic!("Premature EOF"),
                            Some(Token::End) => break,
                            _ => {}
                        };

                        match self.parse_stmt(tokenizer) {
                            None => break,
                            Some(node) => else_body.push(Some(*node)),
                        };
                    }
                }

                consume_token(tokenizer, Token::End);

                let mut then_body = self.wrap_stmts(&mut then_body);
                let else_body = self.wrap_stmts(&mut else_body);

                // If `else` clause is empty or omitted, convert the body of `then` to statements.
                if !has_else {
                    self.replace_last_expr_to_stmt(&mut then_body);
                }

                let expr = Expr::If {
                    condition,
                    then_body,
                    else_body,
                };

                Some(Box::new(self.typed_expr(expr)))
            }
            Token::Case => {
                tokenizer.next();

                let head = self
                    .parse_expr(tokenizer)
                    .expect("Missing head expression after `case`");

                // when, ...
                let mut arms = vec![];

                while let Some(Token::When) = tokenizer.peek() {
                    tokenizer.next();

                    // pattern
                    let pattern = self
                        .parse_pattern(tokenizer)
                        .unwrap_or_else(|| panic!("Missing pattern in `when`"));

                    // guard
                    let condition = match tokenizer.peek() {
                        Some(Token::If) => {
                            tokenizer.next();
                            Some(
                                self.parse_expr(tokenizer)
                                    .expect("Missing condition in `when if ...`"),
                            )
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
                            _ => {}
                        };

                        match self.parse_stmt(tokenizer) {
                            None => break,
                            Some(node) => then_body.push(Some(*node)),
                        };
                    }

                    let then_body = self.wrap_stmts(&mut then_body);

                    arms.push(CaseArm {
                        pattern,
                        condition,
                        then_body,
                    });
                }

                // else
                let mut else_body = vec![];

                if let Some(Token::Else) = tokenizer.peek() {
                    tokenizer.next();

                    loop {
                        match tokenizer.peek() {
                            None => panic!("Premature EOF"),
                            Some(Token::End) => break,
                            _ => {}
                        };

                        match self.parse_stmt(tokenizer) {
                            None => break,
                            Some(node) => else_body.push(Some(*node)),
                        };
                    }
                } else {
                    // If `else` clause is empty or omitted, convert the body of `then` to statements.
                    for CaseArm {
                        ref mut then_body, ..
                    } in &mut arms
                    {
                        self.replace_last_expr_to_stmt(then_body);
                    }
                }

                consume_token(tokenizer, Token::End);

                let else_body = self.wrap_stmts(&mut else_body);

                let expr = Expr::Case {
                    head,
                    head_storage: None,
                    arms,
                    else_body,
                };
                Some(Box::new(self.typed_expr(expr)))
            }
            token => panic!("Unexpected token {:?}", token),
        }
    }

    fn parse_pattern(&mut self, tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Pattern> {
        match tokenizer.peek() {
            Some(Token::Identifier(ref name)) => {
                let pat = Pattern::Variable(name.clone(), None);
                tokenizer.next();
                Some(pat)
            }
            _ => None,
        }
    }
}

impl Parser {
    // Wrap an expression with statement if it is not statement.
    fn wrap_stmt(&mut self, node: Node) -> Node {
        if let Expr::Stmt(..) = node.expr {
            // Don't wrap stmt with stmt.
            return node;
        }

        self.typed_expr(Expr::Stmt(Box::new(node)))
    }

    // Wrap an expressions with statements if it is not the last one.
    fn wrap_stmts(&mut self, nodes: &mut Vec<Option<Node>>) -> Vec<Node> {
        let mut stmts = vec![];
        let mut it = nodes.iter_mut().peekable();

        while let Some(node) = it.next() {
            if it.peek().is_none() {
                stmts.push(node.take().unwrap());
            } else {
                stmts.push(self.wrap_stmt(node.take().unwrap()));
            }
        }

        stmts
    }

    fn replace_last_expr_to_stmt(&mut self, nodes: &mut Vec<Node>) {
        if !nodes.is_empty() {
            let node = nodes.remove(nodes.len() - 1);
            nodes.push(self.wrap_stmt(node));
        }
    }

    fn typed_expr(&mut self, expr: Expr) -> Node {
        let ty = match expr {
            Expr::Integer(_) => wrap(sem::Type::Int32),
            Expr::String { .. } => wrap(sem::Type::String),
            Expr::Stmt(..) => wrap(sem::Type::Void),
            _ => self.type_var(),
        };

        Node {
            expr,
            r#type: ty,
            env: Rc::clone(&self.empty_env),
        }
    }

    /// Returns a new type variable.
    fn type_var(&mut self) -> Rc<RefCell<sem::Type>> {
        let name = self.naming.next();
        wrap(sem::Type::new_type_var(&name))
    }
}

pub fn parse_string<S: AsRef<str>>(src: S) -> Box<Module> {
    let mut tokenizer = Tokenizer::from_string(&src);
    let mut parser = Parser::new();
    parser.parse(&mut tokenizer)
}

fn consume_token(tokenizer: &mut Peekable<&mut Tokenizer>, expected: Token) {
    match tokenizer.next() {
        None => panic!("Premature EOF"),
        Some(token) if token == expected => {}
        Some(token) => panic!("Expected token \"{:?}\", but was {:?}", expected, token),
    }
}

fn consume_char(tokenizer: &mut Peekable<&mut Tokenizer>, expected: char) {
    consume_token(tokenizer, Token::Char(expected));
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
}
