use std::{iter::Peekable, str::Chars};

#[derive(Debug)]
pub enum Token {
    Identifier(String),
    Integer(u32),

    // Operators
    EQ, // "=="
    NE, // "!="
    LE, // "<="
    GE, // ">="

    // punctuations
    Char(char),
}

pub struct Tokenizer<'a> {
    iter: Peekable<Chars<'a>>,
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_token()
    }
}

impl<'a> Tokenizer<'a> {
    pub fn from_string<S: AsRef<str> + ?Sized>(src: &'a S) -> Tokenizer<'a> {
        let it = src.as_ref().chars().peekable();

        Tokenizer { iter: it }
    }

    fn next_token(&mut self) -> Option<Token> {
        self.skip_whitespaces();

        let nextc = match self.iter.peek() {
            None => return None,
            Some(c) => *c,
        };

        let token = match nextc {
            '0'..='9' => self.read_integer(nextc),
            'a'..='z' | '_' => self.read_identifier(nextc),
            '!' | '=' | '<' | '>' => self.read_operator(nextc),
            x => {
                self.iter.next();
                Token::Char(x)
            }
        };

        Some(token)
    }

    fn read_operator(&mut self, nextc: char) -> Token {
        let c = nextc;
        self.iter.next();

        let nextc = match self.iter.peek() {
            None => return Token::Char(nextc),
            Some(c) => *c,
        };

        let token = match (c, nextc) {
            ('=', '=') => Token::EQ,
            ('!', '=') => Token::NE,
            ('<', '=') => Token::LE,
            ('>', '=') => Token::GE,
            _ => return Token::Char(c),
        };

        self.iter.next();
        token
    }

    fn read_identifier(&mut self, nextc: char) -> Token {
        let mut value = nextc.to_string();
        self.iter.next();

        loop {
            match self.iter.peek() {
                Some(x @ 'a'..='z') | Some(x @ '0'..='9') | Some(x @ '_') => {
                    value.push(*x);
                }
                _ => {
                    return Token::Identifier(value);
                }
            };
            self.iter.next();
        }
    }

    fn read_integer(&mut self, nextc: char) -> Token {
        let mut value: u32 = (nextc as u32) - ('0' as u32);
        self.iter.next();

        loop {
            match self.iter.peek() {
                Some(x @ '0'..='9') => {
                    let n = (*x as u32) - ('0' as u32);

                    value = value * 10 + n;
                }
                _ => {
                    return Token::Integer(value);
                }
            };
            self.iter.next();
        }
    }

    fn skip_whitespaces(&mut self) {
        loop {
            match self.iter.peek() {
                None => return,
                Some(c) => match c {
                    ' ' | '\t' | '\n' | '\r' => {}
                    _ => return,
                },
            }
            self.iter.next();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;

    #[test]
    fn tokenize() {
        let mut tokenizer = Tokenizer::from_string("42() ab_01");

        assert_matches!(tokenizer.next().unwrap(), Token::Integer(42));
        assert_matches!(tokenizer.next().unwrap(), Token::Char('('));
        assert_matches!(tokenizer.next().unwrap(), Token::Char(')'));

        assert_matches!(tokenizer.next().unwrap(), Token::Identifier(name) => {
            assert_eq!(name, "ab_01");
        });
    }

    #[test]
    fn operators() {
        let mut tokenizer = Tokenizer::from_string("!===<><=>=");

        assert_matches!(tokenizer.next().unwrap(), Token::NE);
        assert_matches!(tokenizer.next().unwrap(), Token::EQ);
        assert_matches!(tokenizer.next().unwrap(), Token::Char('<'));
        assert_matches!(tokenizer.next().unwrap(), Token::Char('>'));
        assert_matches!(tokenizer.next().unwrap(), Token::LE);
        assert_matches!(tokenizer.next().unwrap(), Token::GE);
    }
}
