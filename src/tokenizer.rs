use std::fmt;
use std::{iter::Peekable, str::Chars};

/// Position in a text document expressed as zero-based line and character offset.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Default)]
pub struct Position {
    /// Line position in a document (zero-based).
    pub line: usize,
    /// Character offset on a line in a document (zero-based). Assuming that
    /// the line is represented as a string, the `character` value represents
    /// the gap between the `character` and `character + 1`.
    pub character: usize,
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Default)]
pub struct EffectiveRange {
    pub length: usize,
    pub start: Position,
    pub end: Position,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub range: EffectiveRange,
}

#[derive(Debug, PartialEq, Clone)]
pub enum TokenKind {
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
    Let,
    Rest, // "..."
    Struct,
    // Keywords (types)
    I32,

    // Operators
    Eq, // "=="
    Ne, // "!="
    Le, // "<="
    Ge, // ">="

    // punctuations
    Char(char),
}

pub struct Tokenizer<'a> {
    chars: Peekable<Chars<'a>>,
    at_end: bool,
    newline_seen: bool,
    /// Tracking the range of token.
    token_length: usize,

    /// Remember a peeked value, even if it was None.
    peeked: Option<Option<Token>>,
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        match self.peeked.take() {
            Some(v) => v,
            None => self.next_token(),
        }
    }
}

impl<'a> Tokenizer<'a> {
    pub fn from_string<S: AsRef<str> + ?Sized>(src: &'a S) -> Tokenizer<'a> {
        let mut iter = src.as_ref().chars().peekable();
        let at_end = iter.peek().is_none();

        Tokenizer {
            chars: iter,
            at_end,
            newline_seen: false,
            token_length: 0,
            peeked: None,
        }
    }

    pub fn is_at_end(&self) -> bool {
        self.at_end
    }

    pub fn is_newline_seen(&self) -> bool {
        self.newline_seen
    }

    /// Returns a reference to the `next()` value without advance the tokenizer.
    ///
    /// Like [`next`], if there is a token, it is wrapped in a `Some(T)`.
    // But if the iteration is over, `None` is returned.
    pub fn peek(&mut self) -> Option<&Token> {
        if self.peeked.is_none() {
            let token = self.next_token();
            self.peeked.get_or_insert(token).as_ref()
        } else {
            self.peeked.as_ref().unwrap().as_ref()
        }
    }

    pub fn peek_kind(&mut self) -> Option<&TokenKind> {
        self.peek().map(|x| &x.kind)
    }

    pub fn current_position(&self) -> Position {
        Position::default()
    }

    fn next_token(&mut self) -> Option<Token> {
        self.skip_white_spaces();
        self.begin_token();

        let nextc = match self.peek_char() {
            None => return None,
            Some(c) => *c,
        };

        let kind = match nextc {
            '0'..='9' => self.read_integer(nextc),
            'a'..='z' | 'A'..='Z' | '_' => self.read_name(nextc),
            '!' | '=' | '<' | '>' => self.read_operator(nextc),
            '"' => self.read_string(),
            '.' => self.read_dot(),
            x => {
                self.next_char();
                TokenKind::Char(x)
            }
        };

        let range = self.end_token();
        Some(Token { kind, range })
    }

    fn begin_token(&mut self) {
        self.token_length = 0;
    }

    fn end_token(&mut self) -> EffectiveRange {
        EffectiveRange {
            length: self.token_length,
            ..EffectiveRange::default()
        }
    }

    fn read_dot(&mut self) -> TokenKind {
        self.next_char();

        match self.peek_char() {
            Some('.') => {
                self.next_char();
                match self.peek_char() {
                    Some('.') => {
                        self.next_char();
                        TokenKind::Rest
                    }
                    _ => panic!("Unrecognized token `..`"),
                }
            }
            _ => TokenKind::Char('.'),
        }
    }

    fn read_string(&mut self) -> TokenKind {
        let mut string = String::new();
        self.next_char();

        loop {
            match self.chars.peek() {
                Some('"') => {
                    self.next_char();
                    break;
                }
                Some('\\') => {
                    self.next_char();
                    let c = match self.chars.peek() {
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
                    self.next_char();
                }
                Some(c) => {
                    string.push(*c);
                    self.next_char();
                }
                None => panic!("Premature EOF while reading string"),
            };
        }

        TokenKind::String(string)
    }

    fn read_operator(&mut self, nextc: char) -> TokenKind {
        let c = nextc;
        self.next_char();

        let nextc = match self.peek_char() {
            None => return TokenKind::Char(nextc),
            Some(c) => *c,
        };

        let token = match (c, nextc) {
            ('=', '=') => TokenKind::Eq,
            ('!', '=') => TokenKind::Ne,
            ('<', '=') => TokenKind::Le,
            ('>', '=') => TokenKind::Ge,
            _ => return TokenKind::Char(c),
        };

        self.next_char();
        token
    }

    fn read_name(&mut self, nextc: char) -> TokenKind {
        let mut value = nextc.to_string();
        self.next_char();

        while let Some(nextc) = self.peek_char() {
            match nextc {
                'a'..='z' | 'A'..='Z' | '0'..='9' | '_' => {
                    value.push(*nextc);
                }
                _ => break,
            };
            self.next_char();
        }

        // trailing "!"
        if let Some(nextc @ '!') = self.peek_char() {
            value.push(*nextc);
            self.next_char();
        }

        match value.as_str() {
            "if" => TokenKind::If,
            "else" => TokenKind::Else,
            "end" => TokenKind::End,
            "fun" => TokenKind::Fun,
            "case" => TokenKind::Case,
            "when" => TokenKind::When,
            "export" => TokenKind::Export,
            "let" => TokenKind::Let,
            "struct" => TokenKind::Struct,
            "i32" => TokenKind::I32,
            _ => TokenKind::Identifier(value),
        }
    }

    fn read_integer(&mut self, nextc: char) -> TokenKind {
        let mut value: i32 = (nextc as i32) - ('0' as i32);
        self.next_char();

        loop {
            match self.peek_char() {
                Some(x @ '0'..='9') => {
                    let n = (*x as i32) - ('0' as i32);

                    value = value * 10 + n;
                }
                _ => {
                    return TokenKind::Integer(value);
                }
            };
            self.next_char();
        }
    }

    fn peek_char(&mut self) -> Option<&char> {
        let c = self.chars.peek();
        self.at_end = c.is_none();
        c
    }

    fn next_char(&mut self) -> Option<char> {
        let c = self.chars.next();

        if c.is_some() {
            self.token_length += 1;
        }
        c
    }

    fn skip_white_spaces(&mut self) {
        let mut line_comment = false;

        self.newline_seen = false;

        loop {
            match self.peek_char() {
                None => return,
                Some(c) => match c {
                    '#' => {
                        line_comment = true;
                    }
                    // whitespace
                    ' ' | '\t' => {}
                    // newline
                    '\n' | '\r' => {
                        line_comment = false;
                        self.newline_seen = true;
                    }
                    _ => {
                        if !line_comment {
                            return;
                        }
                    }
                },
            }
            self.next_char();
        }
    }
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line:{}:{}", self.line, self.character)
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Identifier(name) => write!(f, "id<{}>", name),
            TokenKind::Integer(i) => write!(f, "int<{}>", i),
            TokenKind::String(s) => write!(f, "str<{}>", s),
            TokenKind::If => write!(f, "if"),
            TokenKind::Else => write!(f, "else"),
            TokenKind::End => write!(f, "end"),
            TokenKind::Fun => write!(f, "fun"),
            TokenKind::Case => write!(f, "case"),
            TokenKind::When => write!(f, "when"),
            TokenKind::Export => write!(f, "export"),
            TokenKind::Let => write!(f, "let"),
            TokenKind::Rest => write!(f, "..."),
            TokenKind::Struct => write!(f, "struct"),
            TokenKind::I32 => write!(f, "i32"),
            TokenKind::Eq => write!(f, "=="),
            TokenKind::Ne => write!(f, "!="),
            TokenKind::Le => write!(f, "<="),
            TokenKind::Ge => write!(f, ">="),
            TokenKind::Char(c) => write!(f, "{}", c),
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

        let token = tokenizer.next().unwrap();
        assert_matches!(token.kind, TokenKind::Integer(42));
        assert_eq!(
            token.range,
            EffectiveRange {
                start: Position {
                    line: 0,
                    character: 0
                },
                end: Position {
                    line: 0,
                    character: 1
                },
                length: 2
            }
        );

        let token = tokenizer.next().unwrap();
        assert_matches!(token.kind, TokenKind::Char('('));
        assert_eq!(
            token.range,
            EffectiveRange {
                start: Position {
                    line: 0,
                    character: 2
                },
                end: Position {
                    line: 0,
                    character: 2
                },
                length: 1
            }
        );

        let token = tokenizer.next().unwrap();
        assert_matches!(token.kind, TokenKind::Char(')'));
        assert_eq!(
            token.range,
            EffectiveRange {
                start: Position {
                    line: 0,
                    character: 3
                },
                end: Position {
                    line: 0,
                    character: 3
                },
                length: 1
            }
        );

        assert!(!tokenizer.is_at_end());

        let token = tokenizer.next().unwrap();
        assert_matches!(token.kind, TokenKind::Identifier(name) => {
            assert_eq!(name, "ab_01");
        });
        assert_eq!(
            token.range,
            EffectiveRange {
                start: Position {
                    line: 0,
                    character: 5
                },
                end: Position {
                    line: 0,
                    character: 9
                },
                length: 5
            }
        );
        assert!(tokenizer.is_at_end());
        assert!(tokenizer.next().is_none());
    }

    #[test]
    fn operators() {
        let mut tokenizer = Tokenizer::from_string("!===<><=>=");

        assert_matches!(tokenizer.next().unwrap().kind, TokenKind::Ne);
        assert_matches!(tokenizer.next().unwrap().kind, TokenKind::Eq);
        assert_matches!(tokenizer.next().unwrap().kind, TokenKind::Char('<'));
        assert_matches!(tokenizer.next().unwrap().kind, TokenKind::Char('>'));
        assert_matches!(tokenizer.next().unwrap().kind, TokenKind::Le);
        assert_matches!(tokenizer.next().unwrap().kind, TokenKind::Ge);
    }

    #[test]
    fn keywords() {
        let mut tokenizer = Tokenizer::from_string("if end fun");

        assert_matches!(tokenizer.next().unwrap().kind, TokenKind::If);
        assert_matches!(tokenizer.next().unwrap().kind, TokenKind::End);
        assert_matches!(tokenizer.next().unwrap().kind, TokenKind::Fun);
    }

    #[test]
    fn strings() {
        let mut tokenizer = Tokenizer::from_string("\"\" \"\\n\" \"\\\"\"");

        assert_matches!(tokenizer.next().unwrap().kind, TokenKind::String(str) => {
            assert_eq!(str, "");
        });
        assert_matches!(tokenizer.next().unwrap().kind, TokenKind::String(str) => {
            assert_eq!(str, "\n");
        });
        assert_matches!(tokenizer.next().unwrap().kind, TokenKind::String(str) => {
            assert_eq!(str, "\"");
        });
    }

    #[test]
    fn identifiers() {
        let mut tokenizer = Tokenizer::from_string("abc abc! ab!c");

        assert_matches!(tokenizer.next().unwrap().kind, TokenKind::Identifier(str) => {
            assert_eq!(str, "abc");
        });
        assert_matches!(tokenizer.next().unwrap().kind, TokenKind::Identifier(str) => {
            assert_eq!(str, "abc!");
        });
        assert_matches!(tokenizer.next().unwrap().kind, TokenKind::Identifier(str) => {
            assert_eq!(str, "ab!");
        });
        assert_matches!(tokenizer.next().unwrap().kind, TokenKind::Identifier(str) => {
            assert_eq!(str, "c");
        });
    }

    #[test]
    fn peek0() {
        let mut tokenizer = Tokenizer::from_string("1 2 3");

        // peek() lets us see into the future
        assert_eq!(tokenizer.peek().unwrap().kind, TokenKind::Integer(1));
        assert_eq!(tokenizer.next().unwrap().kind, TokenKind::Integer(1));
        assert_eq!(tokenizer.next().unwrap().kind, TokenKind::Integer(2));

        // The tokenizer does not advance even if we `peek` multiple times
        assert_eq!(tokenizer.peek().unwrap().kind, TokenKind::Integer(3));
        assert_eq!(tokenizer.peek().unwrap().kind, TokenKind::Integer(3));
        assert_eq!(tokenizer.next().unwrap().kind, TokenKind::Integer(3));

        // After the iterator is finished, so is `peek()`
        assert_eq!(tokenizer.peek(), None);
        assert_eq!(tokenizer.next(), None);
    }
}
