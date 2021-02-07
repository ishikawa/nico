use super::tokenizer::{Token, Tokenizer};
use std::iter::Peekable;

// Program
pub struct Program {
    pub function: Option<Box<Node>>,
    pub expr: Option<Box<Node>>,
}

#[derive(Debug)]
pub enum Node {
    // Primitive
    Integer(u32),
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
    // Definition
    Function {
        name: String,
        params: Vec<String>,
        body: Box<Node>,
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

    Box::new(Program { function, expr })
}

fn parse_function(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
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

    let node = Node::Function { name, params, body };
    Some(Box::new(node))
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
        Some(Token::EQ) => Node::EQ,
        Some(Token::NE) => Node::NE,
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
fn parse_relop2(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
    let lhs = match parse_binop1(tokenizer) {
        Some(lhs) => lhs,
        None => return None,
    };

    let builder = match tokenizer.peek() {
        Some(Token::LE) => Node::LE,
        Some(Token::GE) => Node::GE,
        Some(Token::Char('<')) => Node::LT,
        Some(Token::Char('>')) => Node::GT,
        _ => return Some(lhs),
    };
    tokenizer.next();

    let rhs = match parse_binop1(tokenizer) {
        None => panic!("Expected RHS"),
        Some(rhs) => rhs,
    };

    Some(Box::new(builder(lhs, rhs)))
}

fn parse_binop1(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
    let mut lhs = match parse_binop2(tokenizer) {
        None => return None,
        Some(lhs) => lhs,
    };

    loop {
        let builder = match tokenizer.peek() {
            Some(Token::Char('+')) => Node::Add,
            Some(Token::Char('-')) => Node::Sub,
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

fn parse_binop2(tokenizer: &mut Peekable<&mut Tokenizer>) -> Option<Box<Node>> {
    let mut lhs = match parse_primary(tokenizer) {
        None => return None,
        Some(lhs) => lhs,
    };

    loop {
        let builder = match tokenizer.peek() {
            Some(Token::Char('*')) => Node::Mul,
            Some(Token::Char('/')) => Node::Div,
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
        Token::Integer(i) => {
            let node = Some(Box::new(Node::Integer(*i)));
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

            let node = Node::If {
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
        assert!(program.function.is_none());

        let node = program.expr.unwrap();
        assert_matches!(*node, Node::Integer(42));
    }
    #[test]
    fn number_integer_followed_by_letter() {
        let program = parse_string("123a");
        assert!(program.function.is_none());

        let node = program.expr.unwrap();
        assert_matches!(*node, Node::Integer(123));
    }

    #[test]
    fn add_integer() {
        let program = parse_string("1 + 2");
        assert!(program.function.is_none());

        let node = program.expr.unwrap();
        assert_matches!(*node, Node::Add(lhs, rhs) => {
            assert_matches!(*lhs, Node::Integer(1));
            assert_matches!(*rhs, Node::Integer(2));
        });
    }

    #[test]
    fn operator_associative() {
        let program = parse_string("1 + 2 + 3");
        assert!(program.function.is_none());

        let node = program.expr.unwrap();
        assert_matches!(*node, Node::Add(lhs, rhs) => {
            assert_matches!(*lhs, Node::Add(x, y) => {
                assert_matches!(*x, Node::Integer(1));
                assert_matches!(*y, Node::Integer(2));
            });
            assert_matches!(*rhs, Node::Integer(3));
        });
    }
    #[test]
    fn paren_grouping() {
        let program = parse_string("(1 + 2) * 3");
        assert!(program.function.is_none());

        let node = program.expr.unwrap();
        assert_matches!(*node, Node::Mul(lhs, rhs) => {
            assert_matches!(*lhs, Node::Add(x, y) => {
                assert_matches!(*x, Node::Integer(1));
                assert_matches!(*y, Node::Integer(2));
            });
            assert_matches!(*rhs, Node::Integer(3));
        });
    }
}
