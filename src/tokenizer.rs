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

impl<'a> Tokenizer<'a> {
    pub fn from_string<S: AsRef<str> + ?Sized>(src: &'a S) -> Tokenizer<'a> {
        let it = src.as_ref().chars().peekable();

        Tokenizer { iter: it }
    }

    pub fn at_end(&mut self) -> bool {
        match self.iter.peek() {
            Some(_) => false,
            None => true,
        }
    }

    pub fn next(&mut self) -> Option<Token> {
        self.skip_whitespaces();

        let nextc = match self.iter.peek() {
            None => return None,
            Some(c) => *c,
        };

        let token = match nextc {
            '0'..='9' => self.read_integer(),
            'a'..='z' | '_' => self.read_identifier(),
            x => {
                self.iter.next();
                Token::Char(x)
            }
        };

        Some(token)
    }

    fn read_identifier(&mut self) -> Token {
        let mut value = String::new();

        loop {
            match self.iter.peek() {
                Some(x @ 'a'..='z') | Some(x @ '0'..='9') | Some(x @ '_') => {
                    value.push(*x);
                }
                _ => {
                    if value.is_empty() {
                        panic!("No chars met.")
                    }

                    return Token::Identifier(value);
                }
            };
            self.iter.next();
        }
    }

    fn read_integer(&mut self) -> Token {
        let mut value: Option<u32> = None;

        loop {
            match self.iter.peek() {
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
                        Some(value) => Token::Integer(value),
                        None => panic!("No digits met."),
                    }
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
        assert!(!tokenizer.at_end());

        assert_matches!(tokenizer.next().unwrap(), Token::Integer(42));
        assert_matches!(tokenizer.next().unwrap(), Token::Char('('));
        assert_matches!(tokenizer.next().unwrap(), Token::Char(')'));

        assert_matches!(tokenizer.next().unwrap(), Token::Identifier(name) => {
            assert_eq!(name, "ab_01");
        });
    }
}
