use std::{iter::Peekable, str::Chars};

#[derive(Debug, PartialEq)]
pub enum Token {
    // Primitive
    Identifier(String),
    Integer(i32),
    String(String),

    // Keywords
    If,
    Else,
    End,
    Fun,
    Case,
    When,
    Export,

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
        let mut iter = src.as_ref().chars().peekable();
        let at_end = iter.peek().is_none();

        Tokenizer { iter, at_end }
    }

    pub fn is_at_end(&self) -> bool {
        self.at_end
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
            '"' => self.read_string(),
            x => {
                self.iter.next();
                Token::Char(x)
            }
        };

        Some(token)
    }

    fn read_string(&mut self) -> Token {
        let mut string = String::new();
        self.iter.next();

        loop {
            match self.iter.peek() {
                Some('"') => {
                    self.iter.next();
                    break;
                }
                Some('\\') => {
                    self.iter.next();
                    let c = match self.iter.peek() {
                        Some(c) => *c,
                        None => panic!("Premature EOF while reading escape sequence"),
                    };

                    match c {
                        'n' => string.push('\n'),
                        'r' => string.push('\r'),
                        't' => string.push('\t'),
                        '"' => string.push('"'),
                        '\\' => string.push('\\'),
                        c => panic!("Unrecognized escape sequence: \"\\{}\"", c),
                    };
                    self.iter.next();
                }
                Some(c) => {
                    string.push(*c);
                    self.iter.next();
                }
                None => panic!("Premature EOF while reading string"),
            };
        }

        Token::String(string)
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

        while let Some(nextc) = self.peek_char() {
            match nextc {
                'a'..='z' | '0'..='9' | '_' => {
                    value.push(*nextc);
                }
                _ => break,
            };
            self.iter.next();
        }

        // trailing "!"
        if let Some(nextc @ '!') = self.peek_char() {
            value.push(*nextc);
            self.iter.next();
        }

        match value.as_str() {
            "if" => Token::If,
            "else" => Token::Else,
            "end" => Token::End,
            "fun" => Token::Fun,
            "case" => Token::Case,
            "when" => Token::When,
            "export" => Token::Export,
            _ => Token::Identifier(value),
        }
    }

    fn read_integer(&mut self, nextc: char) -> Token {
        let mut value: i32 = (nextc as i32) - ('0' as i32);
        self.iter.next();

        loop {
            match self.peek_char() {
                Some(x @ '0'..='9') => {
                    let n = (*x as i32) - ('0' as i32);

                    value = value * 10 + n;
                }
                _ => {
                    return Token::Integer(value);
                }
            };
            self.iter.next();
        }
    }

    fn peek_char(&mut self) -> Option<&char> {
        let c = self.iter.peek();
        self.at_end = c.is_none();
        c
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
    fn is_at_end_empty() {
        let tokenizer = Tokenizer::from_string("");
        assert!(tokenizer.is_at_end());
    }
    #[test]
    fn is_at_end_one() {
        let mut tokenizer = Tokenizer::from_string("o");
        assert!(!tokenizer.is_at_end());
        tokenizer.next();
        assert!(tokenizer.is_at_end());
    }

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

    #[test]
    fn strings() {
        let mut tokenizer = Tokenizer::from_string("\"\" \"\\n\" \"\\\"\"");

        assert_matches!(tokenizer.next().unwrap(), Token::String(str) => {
            assert_eq!(str, "");
        });
        assert_matches!(tokenizer.next().unwrap(), Token::String(str) => {
            assert_eq!(str, "\n");
        });
        assert_matches!(tokenizer.next().unwrap(), Token::String(str) => {
            assert_eq!(str, "\"");
        });
    }

    #[test]
    fn identifiers() {
        let mut tokenizer = Tokenizer::from_string("abc abc! ab!c");

        assert_matches!(tokenizer.next().unwrap(), Token::Identifier(str) => {
            assert_eq!(str, "abc");
        });
        assert_matches!(tokenizer.next().unwrap(), Token::Identifier(str) => {
            assert_eq!(str, "abc!");
        });
        assert_matches!(tokenizer.next().unwrap(), Token::Identifier(str) => {
            assert_eq!(str, "ab!");
        });
        assert_matches!(tokenizer.next().unwrap(), Token::Identifier(str) => {
            assert_eq!(str, "c");
        });
    }
}
