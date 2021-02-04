use std::{iter::Peekable, panic, str::Chars};

#[derive(Debug, PartialEq)]
pub enum Node {
    Integer(u32),
    Add(Box<Node>, Box<Node>),
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

    match next_operator(src) {
        Some('+') => match parse_expr(src) {
            Some(rhs) => Some(Box::new(Node::Add(lhs, rhs))),
            None => panic!("Expected integer for RHS"),
        },
        None => Some(lhs),
        Some(x) => panic!("Unexpected char {}", x),
    }
}

fn parse_primary(src: &mut Peekable<Chars>) -> Option<Box<Node>> {
    skip_whitespaces(src);

    match src.peek() {
        None => None,
        Some(c) => match c {
            ' ' | '\t' | '\n' | '\r' => {
                skip_whitespaces(src);
                parse_primary(src)
            }
            '0'..='9' => parse_integer(src),
            x => panic!("Unexpected char {}", x),
        },
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
        Some('+') => Some('+'),
        _ => return None,
    };

    src.next();
    operator
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn number_integer() {
        let node = parse("42").unwrap();
        assert_eq!(*node, Node::Integer(42));
    }
    #[test]
    fn number_integer_followed_by_letter() {
        let node = parse("123a").unwrap();
        assert_eq!(*node, Node::Integer(123));
    }

    #[test]
    fn add_integer() {
        let node = parse("1 + 2").unwrap();
        match *node {
            Node::Add(lhs, rhs) => {
                assert_eq!(*lhs, Node::Integer(1));
                assert_eq!(*rhs, Node::Integer(2));
            }
            _ => panic!(),
        }
    }
}
