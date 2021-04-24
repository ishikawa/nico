//! Even if there are syntax errors in the source code, a full token is generated and the source code is
//! published.For this purpose the tokenizer will never fail except for IO errors.
//!
//! Also, the tokenizer generates tokens only in units that do not require interpretation where tokenizer
//! syntax errors can occur. For example, a string consists of several tokens because of possible escape
//! sequences and EOF in the middle.
//!
//! It is responsibility of parsers to interpret these tokens and generate strings and other nodes.
use std::convert::TryFrom;
use std::fmt;
use std::iter::Peekable;
use std::str::Chars;

/// Position in a text document expressed as zero-based line and character offset.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Default)]
pub struct Position {
    /// Line position in a document (zero-based).
    pub line: u32,
    /// Character offset on a line in a document (zero-based). Assuming that
    /// the line is represented as a string, the `character` value represents
    /// the gap between the `character` and `character + 1`.
    pub character: u32,
}

// The effective range of a token.
// `start` inclusive, `end` exclusive.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Default)]
pub struct EffectiveRange {
    pub length: u32,
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

    // Keywords
    If,
    Else,
    End,
    Fun,
    Case,
    When,
    Export,
    Let,
    Range, // ".."
    Rest,  // "..."
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

    // String and interpretation errors
    StringStart,
    StringContent(String),
    StringEscapeSequence(char),
    StringUnrecognizedEscapeSequence(char),
    StringEnd,
}

#[derive(Debug, PartialEq, Clone)]
pub enum TriviaKind {
    // comment
    LineComment(String),
    Whitespace,
}

#[derive(Debug, PartialEq, Clone)]
enum TokenizerMode {
    Code,
    String,
}

#[derive(Debug)]
pub enum SyntaxToken {
    Interpreted(Token),
    Missing {
        range: EffectiveRange,
        item: MissingTokenKind,
    },
    /// A skipped token with the description of an expected node.
    Skipped {
        token: Token,
        expected: MissingTokenKind,
    },
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum MissingTokenKind {
    TopLevel,
    FunctionName,
    StructName,
    FieldName,
    TypeAnnotation,
    Statement,
    Pattern,
    Expression,
    End,
    EscapeSequence,
    StringEnd,
    Separator, // newline
    Char(char),
}

#[derive(Debug)]
pub struct Tokenizer<'a> {
    mode: TokenizerMode,
    chars: Peekable<Chars<'a>>,
    at_end: bool,
    newline_seen: bool,
    previous_token: Option<Token>,
    /// Tracking the range of token.
    lineno: usize,
    columnno: usize,
    start_position: Option<Position>,
    token_text: String,

    /// Remember a peeked value.
    peeked: Option<Token>,
}

impl<'a> Tokenizer<'a> {
    pub fn from_string<S: AsRef<str> + ?Sized>(src: &'a S) -> Tokenizer<'a> {
        let mut iter = src.as_ref().chars().peekable();
        let at_end = iter.peek().is_none();

        Tokenizer {
            mode: TokenizerMode::Code,
            chars: iter,
            at_end,
            newline_seen: false,
            lineno: 0,
            columnno: 0,
            start_position: None,
            token_text: "".to_string(),
            peeked: None,
            previous_token: None,
        }
    }

    pub fn is_at_end(&self) -> bool {
        self.at_end
    }

    pub fn is_newline_seen(&self) -> bool {
        self.newline_seen
    }

    /// Returns a reference to the `next()` value without advance the tokenizer.
    pub fn peek(&mut self) -> &Token {
        if self.peeked.is_none() {
            let token = self.advance_token();
            self.peeked.get_or_insert(token)
        } else {
            self.peeked.as_ref().unwrap()
        }
    }

    pub fn peek_kind(&mut self) -> &TokenKind {
        &self.peek().kind
    }

    /// Returns the effective range of the token at the current position that would be
    /// appropriate if a new token were to be inserted.
    pub fn current_insertion_range(&self) -> EffectiveRange {
        if self.newline_seen || self.is_at_end() {
            if let Some(ref token) = self.previous_token {
                return token.range;
            }
        }

        self.current_range()
    }

    pub fn current_position(&self) -> Position {
        // Convert usize to u32 in favor of LSP compatibility.
        let line = u32::try_from(self.lineno).unwrap_or_else(|_| panic!("overflow line number"));
        let character =
            u32::try_from(self.columnno).unwrap_or_else(|_| panic!("overflow column number"));

        Position { line, character }
    }

    fn current_range(&self) -> EffectiveRange {
        // Convert usize to u32 in favor of LSP compatibility.
        let length = u32::try_from(self.token_text.len())
            .unwrap_or_else(|_| panic!("overflow token length"));

        EffectiveRange {
            length,
            start: self.start_position.unwrap(),
            end: self.current_position(),
        }
    }

    pub fn build_missing<S: Into<String>>(&self, kind: TokenKind, name: S) -> Token {
        Token {
            kind,
            range: EffectiveRange {
                start: self.current_position(),
                end: self.current_position(),
                // A missing token must not have length.
                length: 0,
            },
            text: name.into(),
            leading_trivia: vec![],
        }
    }

    pub fn next_token(&mut self) -> Token {
        let token = match self.peeked.take() {
            Some(v) => v,
            None => self.advance_token(),
        };

        self.previous_token = Some(token.clone());
        token
    }

    fn begin_token(&mut self) {
        self.token_text.clear();
        self.start_position = Some(self.current_position());
    }

    fn end_token(&mut self, kind: TokenKind, leading_trivia: Vec<Trivia>) -> Token {
        Token {
            kind,
            range: self.current_range(),
            text: self.token_text.clone(),
            leading_trivia,
        }
    }

    fn advance_token(&mut self) -> Token {
        self.newline_seen = false;

        match self.mode {
            TokenizerMode::Code => {
                let leading_trivia = self.read_trivia();

                self.begin_token();

                let kind = match self.peek_char() {
                    None => TokenKind::Eos,
                    Some(nextc) => match nextc {
                        '0'..='9' => self.read_integer(nextc),
                        'a'..='z' | 'A'..='Z' | '_' => self.read_name(nextc),
                        '!' | '=' | '<' | '>' => self.read_operator(nextc),
                        '.' => self.read_dot(),
                        '"' => {
                            self.next_char();
                            self.mode = TokenizerMode::String;
                            TokenKind::StringStart
                        }
                        x => {
                            self.next_char();
                            TokenKind::Char(x)
                        }
                    },
                };

                self.end_token(kind, leading_trivia)
            }
            TokenizerMode::String => {
                self.begin_token();

                let kind = match self.peek_char() {
                    None => {
                        self.mode = TokenizerMode::Code;
                        TokenKind::Eos
                    }
                    Some(nextc) => match nextc {
                        '"' => {
                            self.next_char();
                            self.mode = TokenizerMode::Code;
                            TokenKind::StringEnd
                        }
                        // Do not include the newline character to prevent everything after
                        // the string when developer forgot to close from being interpreted as a string.
                        '\n' | '\r' => {
                            let c = self.next_char().unwrap();

                            self.mode = TokenizerMode::Code;
                            TokenKind::Char(c)
                        }
                        '\\' => self.read_escape_sequence(),
                        _ => self.read_string_content(),
                    },
                };

                self.end_token(kind, vec![])
            }
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
                    _ => TokenKind::Range,
                }
            }
            _ => TokenKind::Char('.'),
        }
    }

    fn read_escape_sequence(&mut self) -> TokenKind {
        self.next_char();

        let c = match self.next_char() {
            Some(c) => c,
            None => return TokenKind::Char('\\'),
        };

        let c = match c {
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            '"' => '"',
            '\\' => '\\',
            c => {
                // If an uninterpretable escape sequence is encountered,
                // ignore it for the time being and continue interpreting the string.
                return TokenKind::StringUnrecognizedEscapeSequence(c);
            }
        };

        TokenKind::StringEscapeSequence(c)
    }

    fn read_string_content(&mut self) -> TokenKind {
        let mut string = String::new();
        string.push(self.next_char().unwrap());

        while let Some(c) = self.peek_char() {
            match c {
                '"' | '\\' | '\r' | '\n' => {
                    break;
                }
                c => {
                    string.push(c);
                    self.next_char();
                }
            };
        }

        TokenKind::StringContent(string)
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

            trivia.push(Trivia {
                kind,
                range: self.current_range(),
                text: self.token_text.clone(),
            })
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
            TokenKind::If => write!(f, "if"),
            TokenKind::Else => write!(f, "else"),
            TokenKind::End => write!(f, "end"),
            TokenKind::Fun => write!(f, "fun"),
            TokenKind::Case => write!(f, "case"),
            TokenKind::When => write!(f, "when"),
            TokenKind::Export => write!(f, "export"),
            TokenKind::Let => write!(f, "let"),
            TokenKind::Range => write!(f, ".."),
            TokenKind::Rest => write!(f, "..."),
            TokenKind::Struct => write!(f, "struct"),
            TokenKind::I32 => write!(f, "i32"),
            TokenKind::Eq => write!(f, "=="),
            TokenKind::Ne => write!(f, "!="),
            TokenKind::Le => write!(f, "<="),
            TokenKind::Ge => write!(f, ">="),
            TokenKind::Char(c) => write!(f, "{}", c),
            TokenKind::Eos => write!(f, "(EOF)"),
            TokenKind::StringStart => write!(f, "\"..."),
            TokenKind::StringContent(s) => write!(f, "\"{}\"", s),
            TokenKind::StringEscapeSequence(c) => write!(f, "\\{}", c),
            TokenKind::StringUnrecognizedEscapeSequence(c) => write!(f, "\\{}", c),
            TokenKind::StringEnd => write!(f, "...\""),
        }
    }
}

impl fmt::Display for MissingTokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MissingTokenKind::TopLevel => write!(f, "declaration or statement"),
            MissingTokenKind::FunctionName => write!(f, "function name"),
            MissingTokenKind::StructName => write!(f, "struct name"),
            MissingTokenKind::FieldName => write!(f, "field name"),
            MissingTokenKind::TypeAnnotation => write!(f, "type annotation"),
            MissingTokenKind::Statement => write!(f, "statement"),
            MissingTokenKind::Pattern => write!(f, "pattern"),
            MissingTokenKind::Expression => write!(f, "expression"),
            MissingTokenKind::End => write!(f, "end"),
            MissingTokenKind::EscapeSequence => write!(f, "escape sequence"),
            MissingTokenKind::StringEnd => write!(f, "\""),
            MissingTokenKind::Separator => write!(f, "\\n"),
            MissingTokenKind::Char(c) => write!(f, "{}", c),
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
        tokenizer.next_token();
        assert!(tokenizer.is_at_end());
    }

    #[test]
    fn tokenize() {
        let mut tokenizer = Tokenizer::from_string("42() ab_01");

        assert!(!tokenizer.is_at_end());

        let token = tokenizer.next_token();
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

        let token = tokenizer.next_token();
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

        let token = tokenizer.next_token();
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

        let token = tokenizer.next_token();
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

        let token = tokenizer.next_token();

        assert!(tokenizer.is_at_end());
        assert_eq!(token.kind, TokenKind::Eos);
    }

    #[test]
    fn operators() {
        let mut tokenizer = Tokenizer::from_string("!===<><=>=");

        assert_matches!(tokenizer.next_token().kind, TokenKind::Ne);
        assert_matches!(tokenizer.next_token().kind, TokenKind::Eq);
        assert_matches!(tokenizer.next_token().kind, TokenKind::Char('<'));
        assert_matches!(tokenizer.next_token().kind, TokenKind::Char('>'));
        assert_matches!(tokenizer.next_token().kind, TokenKind::Le);
        assert_matches!(tokenizer.next_token().kind, TokenKind::Ge);
    }

    #[test]
    fn keywords() {
        let mut tokenizer = Tokenizer::from_string("if end fun");

        assert_matches!(tokenizer.next_token().kind, TokenKind::If);
        assert_matches!(tokenizer.next_token().kind, TokenKind::End);
        assert_matches!(tokenizer.next_token().kind, TokenKind::Fun);
    }

    #[test]
    fn comment() {
        let mut tokenizer = Tokenizer::from_string("# comment\n");

        let token = tokenizer.next_token();

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
        let mut tokenizer = Tokenizer::from_string("\"\" \"\\n\" \n\"\\\"\" \"hello\\n\"");

        // ""
        let token = tokenizer.next_token();
        assert_eq!(token.kind, TokenKind::StringStart);
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
                length: 1
            }
        );

        let token = tokenizer.next_token();
        assert_eq!(token.kind, TokenKind::StringEnd);
        assert_eq!(
            token.range,
            EffectiveRange {
                start: Position {
                    line: 0,
                    character: 1
                },
                end: Position {
                    line: 0,
                    character: 2
                },
                length: 1
            }
        );

        // "\n"
        let token = tokenizer.next_token();
        assert_eq!(token.kind, TokenKind::StringStart);
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

        let token = tokenizer.next_token();
        assert_eq!(token.kind, TokenKind::StringEscapeSequence('\n'));
        assert_eq!(
            token.range,
            EffectiveRange {
                start: Position {
                    line: 0,
                    character: 4
                },
                end: Position {
                    line: 0,
                    character: 6
                },
                length: 2
            }
        );

        let token = tokenizer.next_token();
        assert_eq!(token.kind, TokenKind::StringEnd);
        assert_eq!(
            token.range,
            EffectiveRange {
                start: Position {
                    line: 0,
                    character: 6
                },
                end: Position {
                    line: 0,
                    character: 7
                },
                length: 1
            }
        );

        // \"
        let token = tokenizer.next_token();
        assert_eq!(token.kind, TokenKind::StringStart);
        assert_eq!(
            token.range,
            EffectiveRange {
                start: Position {
                    line: 1,
                    character: 0
                },
                end: Position {
                    line: 1,
                    character: 1
                },
                length: 1
            }
        );

        let token = tokenizer.next_token();
        assert_eq!(token.kind, TokenKind::StringEscapeSequence('\"'));
        assert_eq!(
            token.range,
            EffectiveRange {
                start: Position {
                    line: 1,
                    character: 1
                },
                end: Position {
                    line: 1,
                    character: 3
                },
                length: 2
            }
        );

        let token = tokenizer.next_token();
        assert_eq!(token.kind, TokenKind::StringEnd);
        assert_eq!(
            token.range,
            EffectiveRange {
                start: Position {
                    line: 1,
                    character: 3
                },
                end: Position {
                    line: 1,
                    character: 4
                },
                length: 1
            }
        );

        // "hello\n"
        let token = tokenizer.next_token();
        assert_eq!(token.kind, TokenKind::StringStart);
        assert_eq!(
            token.range,
            EffectiveRange {
                start: Position {
                    line: 1,
                    character: 5
                },
                end: Position {
                    line: 1,
                    character: 6
                },
                length: 1
            }
        );

        let token = tokenizer.next_token();
        assert_matches!(token.kind, TokenKind::StringContent(s) => {
            assert_eq!(s, "hello");
        });
        assert_eq!(
            token.range,
            EffectiveRange {
                start: Position {
                    line: 1,
                    character: 6
                },
                end: Position {
                    line: 1,
                    character: 11
                },
                length: 5
            }
        );

        let token = tokenizer.next_token();
        assert_eq!(token.kind, TokenKind::StringEscapeSequence('\n'));
        assert_eq!(
            token.range,
            EffectiveRange {
                start: Position {
                    line: 1,
                    character: 11
                },
                end: Position {
                    line: 1,
                    character: 13
                },
                length: 2
            }
        );

        let token = tokenizer.next_token();
        assert_eq!(token.kind, TokenKind::StringEnd);
        assert_eq!(
            token.range,
            EffectiveRange {
                start: Position {
                    line: 1,
                    character: 13
                },
                end: Position {
                    line: 1,
                    character: 14
                },
                length: 1
            }
        );
    }

    #[test]
    fn identifiers() {
        let mut tokenizer = Tokenizer::from_string("abc abc! ab!c");

        assert_matches!(tokenizer.next_token().kind, TokenKind::Identifier(str) => {
            assert_eq!(str, "abc");
        });
        assert_matches!(tokenizer.next_token().kind, TokenKind::Identifier(str) => {
            assert_eq!(str, "abc!");
        });
        assert_matches!(tokenizer.next_token().kind, TokenKind::Identifier(str) => {
            assert_eq!(str, "ab!");
        });
        assert_matches!(tokenizer.next_token().kind, TokenKind::Identifier(str) => {
            assert_eq!(str, "c");
        });
    }

    #[test]
    fn peek0() {
        let mut tokenizer = Tokenizer::from_string("1 2 3");

        // peek() lets us see into the future
        assert_eq!(tokenizer.peek().kind, TokenKind::Integer(1));
        assert_eq!(tokenizer.next_token().kind, TokenKind::Integer(1));
        assert_eq!(tokenizer.next_token().kind, TokenKind::Integer(2));

        // The tokenizer does not advance even if we `peek` multiple times
        assert_eq!(tokenizer.peek().kind, TokenKind::Integer(3));
        assert_eq!(tokenizer.peek().kind, TokenKind::Integer(3));
        assert_eq!(tokenizer.next_token().kind, TokenKind::Integer(3));

        // After an iterator is finished.
        assert_eq!(tokenizer.peek().kind, TokenKind::Eos);
        assert_eq!(tokenizer.peek().kind, TokenKind::Eos);
    }

    #[test]
    fn dots() {
        let mut tokenizer = Tokenizer::from_string(".....");

        assert_eq!(tokenizer.next_token().kind, TokenKind::Rest);
        assert_eq!(tokenizer.next_token().kind, TokenKind::Range);
        assert_eq!(tokenizer.next_token().kind, TokenKind::Eos);
    }
}
