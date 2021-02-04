use std::{iter::Peekable, panic, str::Chars};
#[derive(Debug)]
pub enum Node {
    Integer(u32),
    Add(Box<Node>, Box<Node>),
    Sub(Box<Node>, Box<Node>),
    Mul(Box<Node>, Box<Node>),
    Div(Box<Node>, Box<Node>),
}

pub fn parse<S: AsRef<str>>(src: S) -> Option<Box<Node>> {
    let mut it = src.as_ref().chars().peekable();
    parse_expr(&mut it)
}

fn parse_expr(src: &mut Peekable<Chars>) -> Option<Box<Node>> {
    let lhs = match parse_primary(src) {
        None => return None,
        Some(lhs) => lhs,
    };

    let operator = match next_operator(src) {
        None => return Some(lhs),
        Some(operator) => operator,
    };

    let rhs = match parse_expr(src) {
        None => panic!("Expected integer for RHS"),
        Some(rhs) => rhs,
    };

    let node = match operator {
        '+' => Node::Add(lhs, rhs),
        '-' => Node::Sub(lhs, rhs),
        '*' => Node::Mul(lhs, rhs),
        '/' => Node::Div(lhs, rhs),
        _ => panic!("Unexpected operator {}", operator),
    };

    Some(Box::new(node))
}

fn parse_primary(src: &mut Peekable<Chars>) -> Option<Box<Node>> {
    skip_whitespaces(src);

    let nextc = match src.peek() {
        None => return None,
        Some(c) => *c,
    };

    match nextc {
        '(' => {
            consume_char(src, '(');
            let node = parse_expr(src);
            consume_char(src, ')');
            node
        }
        ' ' | '\t' | '\n' | '\r' => {
            skip_whitespaces(src);
            parse_primary(src)
        }
        '0'..='9' => parse_integer(src),
        x => panic!("Unexpected char {}", x),
    }
}

fn parse_integer(src: &mut Peekable<Chars>) -> Option<Box<Node>> {
    let mut value: Option<u32> = None;

    loop {
        match src.peek() {
            Some(x @ '0'..='9') => {
                let n = (*x as u32) - ('0' as u32);

                value = if let Some(v) = value {
                    Some(v * 10 + n)
                } else {
                    Some(n)
                }
            }
            _ => {
                return match value {
                    Some(value) => Some(Box::new(Node::Integer(value))),
                    None => None,
                }
            }
        };
        src.next();
    }
}

fn consume_char(src: &mut Peekable<Chars>, expected: char) {
    skip_whitespaces(src);
    match src.next() {
        None => panic!("Premature EOF"),
        Some(c) => match c {
            c if c == expected => {}
            c => panic!("Unexpected char {}", c),
        },
    }
}

fn skip_whitespaces(src: &mut Peekable<Chars>) {
    loop {
        match src.peek() {
            None => return,
            Some(c) => match c {
                ' ' | '\t' | '\n' | '\r' => {}
                _ => return,
            },
        }
        src.next();
    }
}

fn next_operator(src: &mut Peekable<Chars>) -> Option<char> {
    skip_whitespaces(src);

    let operator = match src.peek() {
        Some(c) => match c {
            '+' | '-' | '*' | '/' => Some(*c),
            _ => return None,
        },
        None => return None,
    };

    src.next();
    operator
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
}
