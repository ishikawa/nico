use super::tokenizer::{Token, Tokenizer};
use std::iter::Peekable;

// Program
pub struct Program {
    pub definition: Option<Box<Definition>>,
    pub expr: Option<Box<Expr>>,
}

#[derive(Debug)]
pub enum Definition {
    Function {
        name: String,
        params: Vec<String>,
        body: Box<Expr>,
    },
}

#[derive(Debug)]
pub enum Expr {
    // Primitive
    Identifier(String),
    Integer(i32),
    String(String),
    Invocation {
        name: String,
        arguments: Vec<Expr>,
    },

    // binop
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),

    // Relational operator
    LT(Box<Expr>, Box<Expr>), // Less Than
    GT(Box<Expr>, Box<Expr>), // Greater Than
    LE(Box<Expr>, Box<Expr>), // Less than Equal
    GE(Box<Expr>, Box<Expr>), // Greater than Equal
    EQ(Box<Expr>, Box<Expr>), // Equal
    NE(Box<Expr>, Box<Expr>), // Not Equal

    // Control flow
    If {
        condition: Box<Expr>,
        then_body: Box<Expr>,
        else_body: Option<Box<Expr>>,
    },
}

pub fn parse_string<S: AsRef<str>>(src: S) -> Box<Program> {
    let mut tokenizer = Tokenizer::from_string(&src);
    parse(&mut tokenizer)
}

pub fn parse(tokenizer: &mut Tokenizer) -> Box<Program> {
    let mut tokenizer = tokenizer.peekable();

    let function = parse_function(&mut tokenizer);
    let expr = parse_expr(&mut tokenizer);

    Box::new(Program {
        definition: function,
        expr,
    })
}

fn parse_function(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Definition>> {
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

    let definition = Definition::Function { name, params, body };
    Some(Box::new(definition))
}

fn parse_expr(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Expr>> {
    parse_relop1(tokenizer)
}

// "==", "!="
fn parse_relop1(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Expr>> {
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

    Some(Box::new(builder(lhs, rhs)))
}

// ">", "<", ">=", "<="
fn parse_relop2(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Expr>> {
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

    Some(Box::new(builder(lhs, rhs)))
}

fn parse_binop1(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Expr>> {
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

        lhs = Box::new(builder(lhs, rhs));
    }

    Some(lhs)
}

fn parse_binop2(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Expr>> {
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

        lhs = Box::new(builder(lhs, rhs));
    }

    Some(lhs)
}

fn parse_primary(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Expr>> {
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
                Some(Box::new(Expr::Invocation { name, arguments }))
            } else {
                Some(Box::new(Expr::Identifier(name)))
            }
        }
        Token::Integer(i) => {
            let node = Some(Box::new(Expr::Integer(*i)));
            tokenizer.next();
            node
        }
        Token::String(s) => {
            let node = Some(Box::new(Expr::String(s.clone())));
            tokenizer.next();
            node
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

            let node = Expr::If {
                condition,
                then_body,
                else_body,
            };
            Some(Box::new(node))
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

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;

    #[test]
    fn number_integer() {
        let program = parse_string("42");
        assert!(program.definition.is_none());

        let node = program.expr.unwrap();
        assert_matches!(*node, Expr::Integer(42));
    }
    #[test]
    fn number_integer_followed_by_letter() {
        let program = parse_string("123a");
        assert!(program.definition.is_none());

        let node = program.expr.unwrap();
        assert_matches!(*node, Expr::Integer(123));
    }

    #[test]
    fn add_integer() {
        let program = parse_string("1 + 2");
        assert!(program.definition.is_none());

        let node = program.expr.unwrap();
        assert_matches!(*node, Expr::Add(lhs, rhs) => {
            assert_matches!(*lhs, Expr::Integer(1));
            assert_matches!(*rhs, Expr::Integer(2));
        });
    }

    #[test]
    fn operator_associative() {
        let program = parse_string("1 + 2 + 3");
        assert!(program.definition.is_none());

        let node = program.expr.unwrap();
        assert_matches!(*node, Expr::Add(lhs, rhs) => {
            assert_matches!(*lhs, Expr::Add(x, y) => {
                assert_matches!(*x, Expr::Integer(1));
                assert_matches!(*y, Expr::Integer(2));
            });
            assert_matches!(*rhs, Expr::Integer(3));
        });
    }
    #[test]
    fn paren_grouping() {
        let program = parse_string("(1 + 2) * 3");
        assert!(program.definition.is_none());

        let node = program.expr.unwrap();
        assert_matches!(*node, Expr::Mul(lhs, rhs) => {
            assert_matches!(*lhs, Expr::Add(x, y) => {
                assert_matches!(*x, Expr::Integer(1));
                assert_matches!(*y, Expr::Integer(2));
            });
            assert_matches!(*rhs, Expr::Integer(3));
        });
    }
}
