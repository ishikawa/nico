use super::tokenizer::{Token, Tokenizer};
use std::iter::Peekable;
#[derive(Debug)]
pub enum Node {
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
}

pub fn parse<S: AsRef<str>>(src: S) -> Option<Box<Node>> {
    let mut tokenizer = Tokenizer::from_string(&src).peekable();
    parse_expr(&mut tokenizer)
}

fn parse_expr(tokenizer: &mut Peekable<Tokenizer>) -> Option<Box<Node>> {
    parse_relop1(tokenizer)
}

// "==", "!="
fn parse_relop1(tokenizer: &mut Peekable<Tokenizer>) -> Option<Box<Node>> {
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
fn parse_relop2(tokenizer: &mut Peekable<Tokenizer>) -> Option<Box<Node>> {
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

fn parse_binop1(tokenizer: &mut Peekable<Tokenizer>) -> Option<Box<Node>> {
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

fn parse_binop2(tokenizer: &mut Peekable<Tokenizer>) -> Option<Box<Node>> {
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

fn parse_primary(tokenizer: &mut Peekable<Tokenizer>) -> Option<Box<Node>> {
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
            let body = parse_expr(tokenizer).expect("missing if body");

            match tokenizer.peek() {
                Some(Token::End) => tokenizer.next(),
                Some(token) => panic!("Expected \"end\", but was {:?}", token),
                None => panic!("Premature EOF"),
            };

            let node = Node::If {
                condition,
                then_body: body,
                else_body: None,
            };
            Some(Box::new(node))
        }
        token => panic!("Unexpected token {:?}", token),
    }
}

fn consume_char(tokenizer: &mut Peekable<Tokenizer>, expected: char) {
    match tokenizer.next() {
        None => panic!("Premature EOF"),
        Some(Token::Char(c)) => match c {
            c if c == expected => {}
            c => panic!("Expected char \"{}\", but was \"{}\"", expected, c),
        },
        Some(token) => panic!("Unexpected token {:?}", token),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;

    #[test]
    fn number_integer() {
        let node = parse("42").unwrap();
        assert_matches!(*node, Node::Integer(42));
    }
    #[test]
    fn number_integer_followed_by_letter() {
        let node = parse("123a").unwrap();
        assert_matches!(*node, Node::Integer(123));
    }

    #[test]
    fn add_integer() {
        let node = parse("1 + 2").unwrap();
        assert_matches!(*node, Node::Add(lhs, rhs) => {
            assert_matches!(*lhs, Node::Integer(1));
            assert_matches!(*rhs, Node::Integer(2));
        });
    }

    #[test]
    fn operator_associative() {
        let node = parse("1 + 2 + 3").unwrap();

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
        let node = parse("(1 + 2) * 3").unwrap();

        assert_matches!(*node, Node::Mul(lhs, rhs) => {
            assert_matches!(*lhs, Node::Add(x, y) => {
                assert_matches!(*x, Node::Integer(1));
                assert_matches!(*y, Node::Integer(2));
            });
            assert_matches!(*rhs, Node::Integer(3));
        });
    }
}
