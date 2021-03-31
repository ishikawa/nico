use std::fmt;
use std::{iter::Peekable, str::Chars};
use thiserror::Error;

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

// The effective range of a token.
// `start` inclusive, `end` exclusive.
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
    pub leading_trivia: Vec<Trivia>,
    text: String,
}

/// Trivia is not part of the normal language syntax and can appear anywhere between any two tokens.
#[derive(Debug, PartialEq, Clone)]
pub struct Trivia {
    pub kind: TriviaKind,
    pub range: EffectiveRange,
    text: String,
}

impl Token {
    pub fn text(&self) -> &str {
        self.text.as_str()
    }
}

impl Trivia {
    pub fn text(&self) -> &str {
        self.text.as_str()
    }
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

    // End of input source
    Eos,
}

#[derive(Debug, PartialEq, Clone)]
pub enum TriviaKind {
    // comment
    LineComment(String),
    Whitespace,
}

#[derive(Debug)]
pub struct Tokenizer<'a> {
    chars: Peekable<Chars<'a>>,
    at_end: bool,
    newline_seen: bool,
    /// Tracking the range of token.
    lineno: usize,
    columnno: usize,
    start_position: Option<Position>,
    token_text: String,

    /// Remember a peeked value, even if it was None.
    peeked: Option<Result<Token, TokenError>>,
}

#[derive(Debug, Error, PartialEq, Eq)]
#[error("{kind} at {position}")]
pub struct TokenError {
    pub position: Position,
    pub kind: TokenErrorKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenErrorKind {
    Error(String), // Genetic error
}

impl fmt::Display for TokenErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenErrorKind::Error(message) => write!(f, "{}", message),
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
            lineno: 0,
            columnno: 0,
            start_position: None,
            token_text: "".to_string(),
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
    pub fn peek(&mut self) -> Result<&Token, &TokenError> {
        if self.peeked.is_none() {
            let token = self.advance_token();
            self.peeked.get_or_insert(token).as_ref()
        } else {
            self.peeked.as_ref().unwrap().as_ref()
        }
    }

    pub fn peek_kind(&mut self) -> Result<&TokenKind, &TokenError> {
        self.peek().map(|x| &x.kind)
    }

    pub fn current_position(&self) -> Position {
        Position {
            line: self.lineno,
            character: self.columnno,
        }
    }

    pub fn build_token<S: Into<String>>(&self, kind: TokenKind, text: S) -> Token {
        let text = text.into();

        Token {
            kind,
            range: EffectiveRange {
                length: text.len(),
                start: self.current_position(),
                end: self.current_position(),
            },
            text,
            leading_trivia: vec![],
        }
    }

    pub fn next_token(&mut self) -> Result<Token, TokenError> {
        match self.peeked.take() {
            Some(v) => v,
            None => self.advance_token(),
        }
    }

    fn begin_token(&mut self) {
        self.token_text.clear();
        self.start_position = Some(self.current_position());
    }

    fn end_token(&mut self) -> (String, EffectiveRange) {
        let range = EffectiveRange {
            length: self.token_text.len(),
            start: self.start_position.take().unwrap(),
            end: self.current_position(),
        };

        (self.token_text.clone(), range)
    }

    fn error<S: Into<String>>(&self, message: S) -> TokenError {
        TokenError {
            position: self.current_position(),
            kind: TokenErrorKind::Error(message.into()),
        }
    }

    fn advance_token(&mut self) -> Result<Token, TokenError> {
        self.newline_seen = false;

        let leading_trivia = self.read_trivia();

        self.begin_token();

        let kind = match self.peek_char() {
            None => TokenKind::Eos,
            Some(nextc) => match nextc {
                '0'..='9' => self.read_integer(nextc),
                'a'..='z' | 'A'..='Z' | '_' => self.read_name(nextc),
                '!' | '=' | '<' | '>' => self.read_operator(nextc),
                '"' => self.read_string()?,
                '.' => self.read_dot()?,
                x => {
                    self.next_char();
                    TokenKind::Char(x)
                }
            },
        };

        let (text, range) = self.end_token();

        Ok(Token {
            kind,
            range,
            text,
            leading_trivia,
        })
    }

    fn read_dot(&mut self) -> Result<TokenKind, TokenError> {
        self.next_char();

        let kind = match self.peek_char() {
            Some('.') => {
                self.next_char();
                match self.peek_char() {
                    Some('.') => {
                        self.next_char();
                        TokenKind::Rest
                    }
                    _ => return Err(self.error("Unrecognized token `..`")),
                }
            }
            _ => TokenKind::Char('.'),
        };

        Ok(kind)
    }

    fn read_string(&mut self) -> Result<TokenKind, TokenError> {
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
                        None => {
                            return Err(self.error("Premature EOF while reading escape sequence"))
                        }
                    };

                    match c {
                        'n' => string.push('\n'),
                        'r' => string.push('\r'),
                        't' => string.push('\t'),
                        '"' => string.push('"'),
                        '\\' => string.push('\\'),
                        c => {
                            return Err(
                                self.error(format!("Unrecognized escape sequence: \"\\{}\"", c))
                            )
                        }
                    };
                    self.next_char();
                }
                Some(c) => {
                    string.push(*c);
                    self.next_char();
                }
                None => return Err(self.error("Premature EOF while reading string")),
            };
        }

        Ok(TokenKind::String(string))
    }

    fn read_operator(&mut self, nextc: char) -> TokenKind {
        let c = nextc;
        self.next_char();

        let nextc = match self.peek_char() {
            None => return TokenKind::Char(nextc),
            Some(c) => c,
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
                    value.push(nextc);
                }
                _ => break,
            };
            self.next_char();
        }

        // trailing "!"
        if let Some(nextc @ '!') = self.peek_char() {
            value.push(nextc);
            self.next_char();
        }

        let kind = match value.as_str() {
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
        };

        kind
    }

    fn read_integer(&mut self, nextc: char) -> TokenKind {
        let mut value: i32 = (nextc as i32) - ('0' as i32);
        self.next_char();

        loop {
            match self.peek_char() {
                Some(x @ '0'..='9') => {
                    let n = (x as i32) - ('0' as i32);

                    value = value * 10 + n;
                }
                _ => {
                    return TokenKind::Integer(value);
                }
            };
            self.next_char();
        }
    }

    fn peek_char(&mut self) -> Option<char> {
        let c = self.chars.peek();
        self.at_end = c.is_none();
        c.copied()
    }

    fn next_char(&mut self) -> Option<char> {
        let c = self.chars.next()?;

        self.token_text.push(c);
        self.columnno += 1;

        if c == '\n' {
            self.lineno += 1;
            self.columnno = 0;
            self.newline_seen = true;
        }

        Some(c)
    }

    fn read_whitespace(&mut self) -> TriviaKind {
        while let Some(c) = self.peek_char() {
            if !(c == ' ' || c == '\t' || c == '\n' || c == '\r') {
                break;
            }
            self.next_char();
        }

        TriviaKind::Whitespace
    }

    fn read_comment(&mut self) -> TriviaKind {
        let mut comment = String::new();
        self.next_char(); // '#'

        while let Some(c) = self.peek_char() {
            if c == '\n' {
                break;
            }

            comment.push(c);
            self.next_char();
        }

        TriviaKind::LineComment(comment)
    }

    fn read_trivia(&mut self) -> Vec<Trivia> {
        let mut trivia = vec![];

        while let Some(c) = self.peek_char() {
            self.begin_token();

            let kind = if c == ' ' || c == '\t' || c == '\n' || c == '\r' {
                self.read_whitespace()
            } else if c == '#' {
                self.read_comment()
            } else {
                break;
            };

            let (text, range) = self.end_token();

            trivia.push(Trivia { kind, text, range })
        }

        trivia
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
            TokenKind::Eos => write!(f, "(EOF)"),
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
        tokenizer.next_token().unwrap();
        assert!(tokenizer.is_at_end());
    }

    #[test]
    fn tokenize() {
        let mut tokenizer = Tokenizer::from_string("42() ab_01");

        assert!(!tokenizer.is_at_end());

        let token = tokenizer.next_token().unwrap();
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
                    character: 2
                },
                length: 2
            }
        );

        let token = tokenizer.next_token().unwrap();
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
                    character: 3
                },
                length: 1
            }
        );

        let token = tokenizer.next_token().unwrap();
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
                    character: 4
                },
                length: 1
            }
        );

        assert!(!tokenizer.is_at_end());

        let token = tokenizer.next_token().unwrap();
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
                    character: 10
                },
                length: 5
            }
        );

        let token = tokenizer.next_token().unwrap();

        assert!(tokenizer.is_at_end());
        assert_eq!(token.kind, TokenKind::Eos);
    }

    #[test]
    fn operators() {
        let mut tokenizer = Tokenizer::from_string("!===<><=>=");

        assert_matches!(tokenizer.next_token().unwrap().kind, TokenKind::Ne);
        assert_matches!(tokenizer.next_token().unwrap().kind, TokenKind::Eq);
        assert_matches!(tokenizer.next_token().unwrap().kind, TokenKind::Char('<'));
        assert_matches!(tokenizer.next_token().unwrap().kind, TokenKind::Char('>'));
        assert_matches!(tokenizer.next_token().unwrap().kind, TokenKind::Le);
        assert_matches!(tokenizer.next_token().unwrap().kind, TokenKind::Ge);
    }

    #[test]
    fn keywords() {
        let mut tokenizer = Tokenizer::from_string("if end fun");

        assert_matches!(tokenizer.next_token().unwrap().kind, TokenKind::If);
        assert_matches!(tokenizer.next_token().unwrap().kind, TokenKind::End);
        assert_matches!(tokenizer.next_token().unwrap().kind, TokenKind::Fun);
    }

    #[test]
    fn comment() {
        let mut tokenizer = Tokenizer::from_string("# comment\n");

        let token = tokenizer.next_token().unwrap();

        assert_eq!(token.kind, TokenKind::Eos);
        assert_eq!(token.leading_trivia.len(), 2);

        let trivia = &token.leading_trivia[0];

        assert_matches!(trivia.kind, TriviaKind::LineComment(ref str) => {
            assert_eq!(str, " comment");
        });
        assert_eq!(
            trivia.range,
            EffectiveRange {
                start: Position {
                    line: 0,
                    character: 0
                },
                end: Position {
                    line: 0,
                    character: 9
                },
                length: 9
            }
        );

        let trivia = &token.leading_trivia[1];

        assert_eq!(trivia.kind, TriviaKind::Whitespace);
        assert_eq!(
            trivia.range,
            EffectiveRange {
                start: Position {
                    line: 0,
                    character: 9
                },
                end: Position {
                    line: 1,
                    character: 0
                },
                length: 1
            }
        );
    }

    #[test]
    fn strings() {
        let mut tokenizer = Tokenizer::from_string("\"\" \"\\n\" \n\"\\\"\"");

        let token = tokenizer.next_token().unwrap();
        assert_matches!(token.kind, TokenKind::String(str) => {
            assert_eq!(str, "");
        });
        assert_eq!(
            token.range,
            EffectiveRange {
                start: Position {
                    line: 0,
                    character: 0
                },
                end: Position {
                    line: 0,
                    character: 2
                },
                length: 2
            }
        );

        let token = tokenizer.next_token().unwrap();
        assert_matches!(token.kind, TokenKind::String(str) => {
            assert_eq!(str, "\n");
        });
        assert_eq!(
            token.range,
            EffectiveRange {
                start: Position {
                    line: 0,
                    character: 3
                },
                end: Position {
                    line: 0,
                    character: 7
                },
                length: 4
            }
        );

        let token = tokenizer.next_token().unwrap();
        assert_matches!(token.kind, TokenKind::String(str) => {
            assert_eq!(str, "\"");
        });
        assert_eq!(
            token.range,
            EffectiveRange {
                start: Position {
                    line: 1,
                    character: 0
                },
                end: Position {
                    line: 1,
                    character: 4
                },
                length: 4
            }
        );
    }

    #[test]
    fn identifiers() {
        let mut tokenizer = Tokenizer::from_string("abc abc! ab!c");

        assert_matches!(tokenizer.next_token().unwrap().kind, TokenKind::Identifier(str) => {
            assert_eq!(str, "abc");
        });
        assert_matches!(tokenizer.next_token().unwrap().kind, TokenKind::Identifier(str) => {
            assert_eq!(str, "abc!");
        });
        assert_matches!(tokenizer.next_token().unwrap().kind, TokenKind::Identifier(str) => {
            assert_eq!(str, "ab!");
        });
        assert_matches!(tokenizer.next_token().unwrap().kind, TokenKind::Identifier(str) => {
            assert_eq!(str, "c");
        });
    }

    #[test]
    fn peek0() {
        let mut tokenizer = Tokenizer::from_string("1 2 3");

        // peek() lets us see into the future
        assert_eq!(tokenizer.peek().unwrap().kind, TokenKind::Integer(1));
        assert_eq!(tokenizer.next_token().unwrap().kind, TokenKind::Integer(1));
        assert_eq!(tokenizer.next_token().unwrap().kind, TokenKind::Integer(2));

        // The tokenizer does not advance even if we `peek` multiple times
        assert_eq!(tokenizer.peek().unwrap().kind, TokenKind::Integer(3));
        assert_eq!(tokenizer.peek().unwrap().kind, TokenKind::Integer(3));
        assert_eq!(tokenizer.next_token().unwrap().kind, TokenKind::Integer(3));

        // After an iterator is finished.
        assert_eq!(tokenizer.peek().unwrap().kind, TokenKind::Eos);
        assert_eq!(tokenizer.peek().unwrap().kind, TokenKind::Eos);
    }
}
