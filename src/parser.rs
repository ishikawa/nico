use super::sem;
use super::tokenizer::{Token, Tokenizer};
use std::iter::Peekable;

// Program
pub struct Module {
    pub function: Option<Box<Function>>,
    pub expr: Option<Box<Node>>,
    pub name: Option<String>,
}

#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub params: Vec<String>,
    pub body: Box<Node>,
}

#[derive(Debug)]
pub struct Node {
    pub expr: Expr,
    pub r#type: Option<sem::Type>,
}

impl Node {
    pub fn expr(expr: Expr) -> Node {
        Node { expr, r#type: None }
    }
}

#[derive(Debug)]
pub enum Expr {
    // Primitive
    Identifier(String),
    Integer(i32),
    String(String),
    Invocation {
        name: String,
        arguments: Vec<Node>,
    },

    // binop
    Add(Box<Node>, Box<Node>),
    Sub(Box<Node>, Box<Node>),
    Mul(Box<Node>, Box<Node>),
    Div(Box<Node>, Box<Node>),

    // Relational operator
    LT(Box<Node>, Box<Node>), // Less Than
    GT(Box<Node>, Box<Node>), // Greater Than
    LE(Box<Node>, Box<Node>), // Less than Equal
    GE(Box<Node>, Box<Node>), // Greater than Equal
    EQ(Box<Node>, Box<Node>), // Equal
    NE(Box<Node>, Box<Node>), // Not Equal

    // Control flow
    If {
        condition: Box<Node>,
        then_body: Box<Node>,
        else_body: Option<Box<Node>>,
    },
}

pub fn parse_string<S: AsRef<str>>(src: S) -> Box<Module> {
    let mut tokenizer = Tokenizer::from_string(&src);
    parse(&mut tokenizer)
}

pub fn parse(tokenizer: &mut Tokenizer) -> Box<Module> {
    let mut tokenizer = tokenizer.peekable();

    let function = parse_function(&mut tokenizer);
    let expr = parse_expr(&mut tokenizer);

    Box::new(Module {
        function,
        expr,
        name: None,
    })
}

fn parse_function(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Function>> {
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

    let mut params = vec![];

    consume_char(tokenizer, '(');
    while let Some(Token::Identifier(name)) = tokenizer.peek() {
        params.push(name.clone());
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
    let body = parse_expr(tokenizer).expect("no function body");
    consume_token(tokenizer, Token::End);

    let function = Function { name, params, body };
    Some(Box::new(function))
}

fn parse_expr(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
    parse_relop1(tokenizer)
}

// "==", "!="
fn parse_relop1(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
    let lhs = match parse_relop2(tokenizer) {
        Some(lhs) => lhs,
        None => return None,
    };

    let builder = match tokenizer.peek() {
        Some(Token::EQ) => Expr::EQ,
        Some(Token::NE) => Expr::NE,
        _ => return Some(lhs),
    };
    tokenizer.next();

    let rhs = match parse_relop2(tokenizer) {
        None => panic!("Expected RHS"),
        Some(rhs) => rhs,
    };

    Some(boxed_expr(builder(lhs, rhs)))
}

// ">", "<", ">=", "<="
fn parse_relop2(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
    let lhs = match parse_binop1(tokenizer) {
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

    let rhs = match parse_binop1(tokenizer) {
        None => panic!("Expected RHS"),
        Some(rhs) => rhs,
    };

    Some(boxed_expr(builder(lhs, rhs)))
}

fn parse_binop1(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
    let mut lhs = match parse_binop2(tokenizer) {
        None => return None,
        Some(lhs) => lhs,
    };

    loop {
        let builder = match tokenizer.peek() {
            Some(Token::Char('+')) => Expr::Add,
            Some(Token::Char('-')) => Expr::Sub,
            Some(_) => break,
            None => return Some(lhs),
        };
        tokenizer.next();

        let rhs = match parse_binop2(tokenizer) {
            None => panic!("Expected RHS"),
            Some(rhs) => rhs,
        };

        lhs = boxed_expr(builder(lhs, rhs));
    }

    Some(lhs)
}

fn parse_binop2(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
    let mut lhs = match parse_primary(tokenizer) {
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

        let rhs = match parse_primary(tokenizer) {
            None => panic!("Expected RHS"),
            Some(rhs) => rhs,
        };

        lhs = boxed_expr(builder(lhs, rhs));
    }

    Some(lhs)
}

fn parse_primary(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
    let token = match tokenizer.peek() {
        None => return None,
        Some(token) => token,
    };

    match token {
        Token::Char('(') => {
            consume_char(tokenizer, '(');
            let node = parse_expr(tokenizer);
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

                    let expr = parse_expr(tokenizer).expect("Expected param");
                    arguments.push(*expr);

                    if let Some(Token::Char(',')) = tokenizer.peek() {
                        tokenizer.next();
                    } else {
                        break;
                    }
                }
                consume_char(tokenizer, ')');
                Some(boxed_expr(Expr::Invocation { name, arguments }))
            } else {
                Some(boxed_expr(Expr::Identifier(name)))
            }
        }
        Token::Integer(i) => {
            let expr = Expr::Integer(*i);
            tokenizer.next();
            Some(boxed_expr(expr))
        }
        Token::String(s) => {
            let expr = Expr::String(s.clone());
            tokenizer.next();
            Some(boxed_expr(expr))
        }
        Token::If => {
            tokenizer.next();

            let condition = parse_expr(tokenizer).expect("missing condition");

            // TODO: check line separator
            let then_body = parse_expr(tokenizer).expect("missing if body");

            let else_body = match tokenizer.peek() {
                Some(Token::Else) => {
                    tokenizer.next();
                    Some(parse_expr(tokenizer).expect("missing else body"))
                }
                _ => None,
            };

            consume_token(tokenizer, Token::End);

            let expr = Expr::If {
                condition,
                then_body,
                else_body,
            };
            Some(boxed_expr(expr))
        }
        token => panic!("Unexpected token {:?}", token),
    }
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

fn boxed_expr(expr: Expr) -> Box<Node> {
    Box::new(Node::expr(expr))
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;

    #[test]
    fn number_integer() {
        let program = parse_string("42");
        assert!(program.function.is_none());

        let expr = program.expr.unwrap().expr;
        assert_matches!(expr, Expr::Integer(42));
    }
    #[test]
    fn number_integer_followed_by_letter() {
        let program = parse_string("123a");
        assert!(program.function.is_none());

        let expr = program.expr.unwrap().expr;
        assert_matches!(expr, Expr::Integer(123));
    }

    #[test]
    fn add_integer() {
        let program = parse_string("1 + 2");
        assert!(program.function.is_none());

        let node = program.expr.unwrap();
        assert_matches!(node.expr, Expr::Add(lhs, rhs) => {
            assert_matches!(lhs.expr, Expr::Integer(1));
            assert_matches!(rhs.expr, Expr::Integer(2));
        });
    }

    #[test]
    fn operator_associative() {
        let program = parse_string("1 + 2 + 3");
        assert!(program.function.is_none());

        let node = program.expr.unwrap();
        assert_matches!(node.expr, Expr::Add(lhs, rhs) => {
            assert_matches!(lhs.expr, Expr::Add(x, y) => {
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

        let node = program.expr.unwrap();
        assert_matches!(node.expr, Expr::Mul(lhs, rhs) => {
            assert_matches!(lhs.expr, Expr::Add(x, y) => {
                assert_matches!(x.expr, Expr::Integer(1));
                assert_matches!(y.expr, Expr::Integer(2));
            });
            assert_matches!(rhs.expr, Expr::Integer(3));
        });
    }
}
