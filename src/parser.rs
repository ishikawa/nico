use crate::asm;
use crate::sem;
use crate::tokenizer::{Token, Tokenizer};
use crate::util::{wrap, SequenceNaming, UniqueNaming};
use std::cell::RefCell;
use std::iter::Peekable;
use std::rc::Rc;

// Program
pub struct Module {
    pub function: Option<Box<Function>>,
    pub main: Option<Box<Function>>,
    // metadata
    pub env: Rc<RefCell<sem::Environment>>,
    pub strings: Option<Vec<Rc<RefCell<asm::ConstantString>>>>,
}

#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub body: Box<Node>,
    // metadata
    pub params: Vec<Rc<RefCell<sem::Binding>>>,
    pub locals: Vec<Rc<RefCell<asm::Storage>>>,
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

    // Control flow
    If {
        condition: Box<Node>,
        then_body: Box<Node>,
        else_body: Option<Box<Node>>,
    },
    Case {
        head: Box<Node>, // head expression
        head_storage: Option<Rc<RefCell<asm::Storage>>>,
        arms: Vec<CaseArm>,
        else_body: Option<Box<Node>>,
    },
}

#[derive(Debug)]
pub enum Pattern {
    Variable(String, Option<Rc<RefCell<sem::Binding>>>),
}

#[derive(Debug)]
pub struct CaseArm {
    pub pattern: Box<Pattern>,
    pub condition: Option<Box<Node>>, // guard
    pub then_body: Box<Node>,
}

#[derive(Debug)]
pub struct Parser {
    naming: SequenceNaming,
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
            naming: SequenceNaming::new("?"),
            empty_env: Rc::new(RefCell::new(sem::Environment::new())),
        }
    }

    fn typed_expr(&mut self, expr: Expr) -> Box<Node> {
        let ty = match expr {
            Expr::Integer(_) => wrap(sem::Type::Int32),
            Expr::String { .. } => wrap(sem::Type::String),
            _ => self.type_var(),
        };

        Box::new(Node {
            expr,
            r#type: ty,
            env: Rc::clone(&self.empty_env),
        })
    }

    /// Returns a new type variable.
    fn type_var(&mut self) -> Rc<RefCell<sem::Type>> {
        let name = self.naming.next();
        wrap(sem::Type::new_type_var(&name))
    }

    pub fn parse(&mut self, tokenizer: &mut Tokenizer) -> Box<Module> {
        let mut tokenizer = tokenizer.peekable();

        let function = self.parse_function(&mut tokenizer);

        // Parser collects top expressions and automatically build
        // `main` function which is the entry point of a program.
        let main = if let Some(body) = self.parse_expr(&mut tokenizer) {
            let fun = Function {
                name: "main".to_string(),
                body,
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
            function,
            main,
            env: Rc::clone(&self.empty_env),
            strings: None,
        })
    }

    fn parse_function(
        &mut self,
        tokenizer: &mut Peekable<&mut Tokenizer>,
    ) -> Option<Box<Function>> {
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

        // TODO: check line separator
        let body = self.parse_expr(tokenizer).expect("no function body");
        consume_token(tokenizer, Token::End);

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
                locals: vec![],
                body,
                env: Rc::clone(&self.empty_env),
                r#type: function_type,
            };

            Some(Box::new(function))
        }
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

        Some(self.typed_expr(builder(lhs, rhs, None)))
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

        Some(self.typed_expr(builder(lhs, rhs, None)))
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

            lhs = self.typed_expr(builder(lhs, rhs, None));
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

            lhs = self.typed_expr(builder(lhs, rhs, None));
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
                    Some(self.typed_expr(Expr::Invocation {
                        name,
                        arguments,
                        binding: None,
                    }))
                } else {
                    Some(self.typed_expr(Expr::Identifier {
                        name,
                        binding: None,
                    }))
                }
            }
            Token::Integer(i) => {
                let expr = Expr::Integer(*i);
                tokenizer.next();
                Some(self.typed_expr(expr))
            }
            Token::String(s) => {
                let expr = Expr::String {
                    content: s.clone(),
                    storage: None,
                };
                tokenizer.next();
                Some(self.typed_expr(expr))
            }
            Token::If => {
                tokenizer.next();

                let condition = self.parse_expr(tokenizer).expect("missing condition");

                // TODO: check line separator
                let then_body = self.parse_expr(tokenizer).expect("missing if body");

                let else_body = match tokenizer.peek() {
                    Some(Token::Else) => {
                        tokenizer.next();
                        Some(self.parse_expr(tokenizer).expect("missing else body"))
                    }
                    _ => None,
                };

                consume_token(tokenizer, Token::End);

                let expr = Expr::If {
                    condition,
                    then_body,
                    else_body,
                };
                Some(self.typed_expr(expr))
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
                    let pattern = match tokenizer.peek() {
                        Some(Token::Identifier(ref name)) => {
                            let pat = Pattern::Variable(name.clone(), None);
                            tokenizer.next();
                            pat
                        }
                        _ => panic!("Missing pattern in `when`"),
                    };

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

                    // TODO: check line separator
                    let then_body = self
                        .parse_expr(tokenizer)
                        .expect("Missing body after `when if ...`");

                    arms.push(CaseArm {
                        pattern: Box::new(pattern),
                        condition,
                        then_body,
                    });
                }

                // else
                let else_body = match tokenizer.peek() {
                    Some(Token::Else) => {
                        tokenizer.next();
                        Some(
                            self.parse_expr(tokenizer)
                                .expect("Missing else body for `case when ...`"),
                        )
                    }
                    _ => None,
                };

                consume_token(tokenizer, Token::End);
                let expr = Expr::Case {
                    head,
                    head_storage: None,
                    arms,
                    else_body,
                };
                Some(self.typed_expr(expr))
            }
            token => panic!("Unexpected token {:?}", token),
        }
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
        assert!(program.function.is_none());

        let expr = program.main.unwrap().body.expr;
        assert_matches!(expr, Expr::Integer(42));
    }
    #[test]
    fn number_integer_followed_by_letter() {
        let program = parse_string("123a");
        assert!(program.function.is_none());

        let expr = program.main.unwrap().body.expr;
        assert_matches!(expr, Expr::Integer(123));
    }

    #[test]
    fn add_integer() {
        let program = parse_string("1 + 2");
        assert!(program.function.is_none());

        let node = program.main.unwrap().body;
        assert_matches!(node.expr, Expr::Add(lhs, rhs, None) => {
            assert_matches!(lhs.expr, Expr::Integer(1));
            assert_matches!(rhs.expr, Expr::Integer(2));
        });
    }

    #[test]
    fn operator_associative() {
        let program = parse_string("1 + 2 + 3");
        assert!(program.function.is_none());

        let node = program.main.unwrap().body;
        assert_matches!(node.expr, Expr::Add(lhs, rhs, None) => {
            assert_matches!(lhs.expr, Expr::Add(x, y, None) => {
                assert_matches!(x.expr, Expr::Integer(1));
                assert_matches!(y.expr, Expr::Integer(2));
            });
            assert_matches!(rhs.expr, Expr::Integer(3));
        });
    }
    #[test]
    fn paren_grouping() {
        let program = parse_string("(1 + 2) * 3");
        assert!(program.function.is_none());

        let node = program.main.unwrap().body;
        assert_matches!(node.expr, Expr::Mul(lhs, rhs, None) => {
            assert_matches!(lhs.expr, Expr::Add(x, y, _) => {
                assert_matches!(x.expr, Expr::Integer(1));
                assert_matches!(y.expr, Expr::Integer(2));
            });
            assert_matches!(rhs.expr, Expr::Integer(3));
        });
    }
}
