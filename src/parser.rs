use std::str::Chars;

#[derive(Debug, PartialEq)]
pub enum Node {
    Integer,
    Add(u32),
}

pub fn parse(src: &String) -> Node {
    parse_expr(&src.chars())
}

fn parse_expr(src: &Chars) -> Node {
    Node::Add(0)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn it_works() {
        let node = parse(&"".to_string());
        assert_eq!(node, Node::Add(0));
    }
}
