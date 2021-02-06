use std::{iter::Peekable, str::Chars};

#[derive(Debug)]
pub enum Token {
    Identifier(String),
    Integer(u32),

    // Keywords
    If,
    Else,
    End,
    Fun,

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
    at_end: bool,
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

        Tokenizer {
            iter: it,
            at_end: false,
        }
    }

    pub fn is_at_end(&self) -> bool {
        self.at_end
    }

    fn peek_char(&mut self) -> Option<&char> {
        match self.iter.peek() {
            None => {
                self.at_end = true;
                None
            }
            c @ Some(_) => c,
        }
    }

    fn next_token(&mut self) -> Option<Token> {
        self.skip_whitespaces();

        let nextc = match self.peek_char() {
            None => return None,
            Some(c) => *c,
        };

        let token = match nextc {
            '0'..='9' => self.read_integer(nextc),
            'a'..='z' | '_' => self.read_name(nextc),
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

        let nextc = match self.peek_char() {
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

    fn read_name(&mut self, nextc: char) -> Token {
        let mut value = nextc.to_string();
        self.iter.next();

        loop {
            match self.peek_char() {
                Some(x @ 'a'..='z') | Some(x @ '0'..='9') | Some(x @ '_') => {
                    value.push(*x);
                }
                _ => {
                    return match value.as_str() {
                        "if" => Token::If,
                        "else" => Token::Else,
                        "end" => Token::End,
                        "fun" => Token::Fun,
                        _ => Token::Identifier(value),
                    }
                }
            };
            self.iter.next();
        }
    }

    fn read_integer(&mut self, nextc: char) -> Token {
        let mut value: u32 = (nextc as u32) - ('0' as u32);
        self.iter.next();

        loop {
            match self.peek_char() {
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
            match self.peek_char() {
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

        assert!(!tokenizer.is_at_end());
        assert_matches!(tokenizer.next().unwrap(), Token::Integer(42));
        assert_matches!(tokenizer.next().unwrap(), Token::Char('('));
        assert_matches!(tokenizer.next().unwrap(), Token::Char(')'));
        assert!(!tokenizer.is_at_end());

        assert_matches!(tokenizer.next().unwrap(), Token::Identifier(name) => {
            assert_eq!(name, "ab_01");
        });

        assert!(tokenizer.is_at_end());
        assert!(tokenizer.next().is_none());
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

    #[test]
    fn keywords() {
        let mut tokenizer = Tokenizer::from_string("if end fun");

        assert_matches!(tokenizer.next().unwrap(), Token::If);
        assert_matches!(tokenizer.next().unwrap(), Token::End);
        assert_matches!(tokenizer.next().unwrap(), Token::Fun);
    }
}