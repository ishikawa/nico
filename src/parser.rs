use std::{iter::Peekable, panic, str::Chars};

#[derive(Debug, PartialEq)]
pub enum Node {
    Integer(u32),
}

pub fn parse<S: AsRef<str>>(src: S) -> Node {
    let mut it = src.as_ref().chars().peekable();
    parse_expr(&mut it).unwrap()
}

fn parse_expr(src: &mut Peekable<Chars>) -> Option<Node> {
    match src.peek() {
        None => None,
        Some('0'..='9') => parse_integer(src),
        Some(x) => panic!("Unexpected char {}", x),
    }
}

fn parse_integer(src: &mut Peekable<Chars>) -> Option<Node> {
    let mut value: u32 = 0;

    loop {
        match src.next() {
            Some(x @ '0'..='9') => {
                value *= 10;
                value += (x as u32) - ('0' as u32);
            }
            _ => break,
        };
    }

    return Some(Node::Integer(value));
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn number_integer() {
        let node = parse("42");
        assert_eq!(node, Node::Integer(42));
    }
    #[test]
    fn number_integer_followed_by_letter() {
        let node = parse("123a");
        assert_eq!(node, Node::Integer(123));
    }
}
