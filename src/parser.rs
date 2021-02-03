use std::{iter::Peekable, panic, str::Chars};

#[derive(Debug, PartialEq)]
pub enum Node {
    Integer(u32),
    Add(u32),
}

pub fn parse(src: &String) -> Node {
    let mut it = src.chars().peekable();
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
            Some(x) => panic!("Unexpected char {}", x),
            None => break,
        };
    }

    return Some(Node::Integer(value));
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn it_works() {
        let node = parse(&"42".to_string());
        assert_eq!(node, Node::Integer(42));
    }
}
