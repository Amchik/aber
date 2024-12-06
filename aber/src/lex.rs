use std::fmt::Display;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Token {
    /// Identificator
    Ident,
    Comment,
    LiteralInteger,
    LiteralFloat,
    LiteralChar,
    LiteralString,
    /// Char `:`
    Colon,
    /// Char `::`
    DoubleColon,
    /// Char `;`
    SemiColon,
    /// Char `,`
    Comma,
    /// Char `(`
    OpenParanthesis,
    /// Char `)`
    CloseParanthesis,
    /// Char `{`
    OpenBrace,
    /// Char `}`
    CloseBrace,
    /// Char `[`
    OpenBracket,
    /// Char `]`
    CloseBracket,
    /// Char `.`
    Dot,
    /// Char `@`
    At,
    /// Char `=`
    Equal,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Position {
    pub line: u32,
    pub char: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct WithPosition<T: ?Sized> {
    pub start: Position,
    pub end: Option<Position>,
    pub value: T,
}

impl<T> WithPosition<T> {
    pub fn location(value: T, start: Position) -> Self {
        WithPosition {
            start,
            end: None,
            value,
        }
    }

    pub fn range(value: T, start: Position, end: Position) -> Self {
        WithPosition {
            start,
            end: Some(end),
            value,
        }
    }

    pub fn range_or_dot(value: T, start: Position, end: Position) -> Self {
        if start == end {
            Self::location(value, start)
        } else {
            Self::range(value, start, end)
        }
    }

    pub fn map<U, F>(self, f: F) -> WithPosition<U>
    where
        F: FnOnce(T) -> U,
    {
        WithPosition {
            start: self.start,
            end: self.end,
            value: f(self.value),
        }
    }

    pub fn replace<U>(self, new_value: U) -> WithPosition<U> {
        WithPosition {
            start: self.start,
            end: self.end,
            value: new_value,
        }
    }
}

impl<T: Display> Display for WithPosition<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(end) = &self.end {
            if end.line == self.start.line {
                write!(
                    f,
                    "{}, line {} char {}..{}",
                    self.value, end.line, self.start.char, end.char
                )
            } else {
                write!(
                    f,
                    "{}, line {} char {} .. line {} char {}",
                    self.value, self.start.line, self.start.char, end.line, end.char
                )
            }
        } else {
            write!(
                f,
                "{}, line {} char {}",
                self.value, self.start.line, self.start.char
            )
        }
    }
}

/// [`Lex`]er error
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Error {
    /// Invalid symbol in input, eg. single `/`
    UnknownOperand(char),
    /// Unclosed char syntax
    UnclosedChar,
    /// Unclosed string (reached newline or EOF)
    UnclosedStr,
    /// Unclosed raw string (reached EOF)
    UnclosedRaw,
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownOperand(c) => write!(f, "unknown operand '{c}'"),
            Self::UnclosedChar => write!(f, "unclosed or too big char"),
            Self::UnclosedStr => write!(f, "unclosed string (unexpected EOF or newline)"),
            Self::UnclosedRaw => write!(f, "unclosed raw string (unexpected EOF)"),
        }
    }
}
impl std::error::Error for Error {}

pub struct Lex<'a> {
    v: &'a str,
    offset: usize,
    pos: Position,
}

impl<'a> Lex<'a> {
    pub fn new(v: &'a str) -> Self {
        Lex {
            v,
            offset: 0,
            pos: Position { line: 1, char: 0 },
        }
    }

    pub fn location(&self) -> usize {
        self.offset
    }

    fn skip_whitespaces(&mut self) {
        self.v
            .bytes()
            .skip(self.offset)
            .take_while(|&p| matches!(p, b' ' | b'\t' | b'\n' | b'\r'))
            .for_each(|c| {
                if c == b'\n' {
                    self.pos.line += 1;
                    self.pos.char = 0;
                } else {
                    self.pos.char += 1;
                }
                self.offset += 1;
            });
    }

    fn linear_offset(&mut self, offset: usize) -> WithPosition<()> {
        debug_assert!(
            offset > 0,
            "`offset` should be at least 1 because end position is exclusive"
        );
        self.offset += offset;
        let start = self.pos;
        let end = {
            let mut p = self.pos;
            p.char += offset as u32 - 1;
            p
        };
        self.pos.char += offset as u32;
        WithPosition {
            start,
            end: Some(end).filter(|_| end != start),
            value: (),
        }
    }

    fn step_char<const STOP: char>(&self, relative_offset: usize) -> Option<(usize, char)> {
        let mut chars = self.v[self.offset + relative_offset..].chars();
        match chars.next()? {
            '\n' => None,
            '\\' => {
                let c = chars.next()?;
                if c == '\n' {
                    return None;
                }
                Some((1 + c.len_utf8(), c))
            }
            c if c == STOP => Some((0, STOP)),
            c => Some((c.len_utf8(), c)),
        }
    }

    fn step_str(&self, relative_offset: usize) -> Option<usize> {
        let mut chars = self.v[self.offset + relative_offset..].chars();
        let mut counter = 0;
        loop {
            let c = chars.next()?;
            match c {
                '\n' => return None,
                '"' => return Some(counter + 1),
                '\\' => {
                    let c = chars.next()?;
                    if c == '\n' {
                        return None;
                    }
                    counter += 1 + c.len_utf8();
                }
                c => counter += c.len_utf8(),
            }
        }
    }

    fn is_ident_start_char(c: char) -> bool {
        c == '/' || (c != '-' && !c.is_ascii_digit() && Self::is_ident_middle_char(c))
    }

    fn is_ident_middle_char(c: char) -> bool {
        !matches!(
            c,
            '(' | ')'
                | '['
                | ']'
                | '{'
                | '}'
                | '/'
                | '@'
                | '.'
                | ','
                | ' '
                | '\t'
                | '\r'
                | '\n'
                | ':'
                | '='
                | ';'
                | '"'
                | '\''
        )
    }
}

impl Iterator for Lex<'_> {
    type Item = WithPosition<Result<Token, Error>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.skip_whitespaces();
        if self.v.len() == self.offset {
            return None;
        }

        let mut chars = self.v[self.offset..].chars();

        let r = match chars.next()? {
            ':' => {
                if chars.next() == Some(':') {
                    self.linear_offset(2).replace(Ok(Token::DoubleColon))
                } else {
                    self.linear_offset(1).replace(Ok(Token::Colon))
                }
            }

            ';' => self.linear_offset(1).replace(Ok(Token::SemiColon)),
            ',' => self.linear_offset(1).replace(Ok(Token::Comma)),
            '(' => self.linear_offset(1).replace(Ok(Token::OpenParanthesis)),
            '[' => self.linear_offset(1).replace(Ok(Token::OpenBracket)),
            '{' => self.linear_offset(1).replace(Ok(Token::OpenBrace)),
            ')' => self.linear_offset(1).replace(Ok(Token::CloseParanthesis)),
            ']' => self.linear_offset(1).replace(Ok(Token::CloseBracket)),
            '}' => self.linear_offset(1).replace(Ok(Token::CloseBrace)),
            '.' => self.linear_offset(1).replace(Ok(Token::Dot)),
            '@' => self.linear_offset(1).replace(Ok(Token::At)),
            '=' => self.linear_offset(1).replace(Ok(Token::Equal)),

            '/' => {
                if chars.next() == Some('/') {
                    self.linear_offset(self.v.bytes().take_while(|&p| p != b'\n').count())
                        .replace(Ok(Token::Comment))
                } else {
                    self.linear_offset(1).replace(Ok(Token::Ident))
                    // NOTE: make Ident("/")?
                    //self.linear_offset(1)
                    //    .replace(Err(Error::UnknownOperand('/')))
                }
            }

            '0'..='9' => {
                let (int_counts, delim) = {
                    let mut counter = 0_usize;
                    let delim = chars.by_ref().find(|c| {
                        if let '0'..='9' = c {
                            counter += 1;
                            false
                        } else {
                            true
                        }
                    });
                    (counter + 1, delim)
                };

                let is_float = delim == Some('.');

                if is_float {
                    let mut frac_counts = 0_usize;
                    let _ = chars.by_ref().find(|c| {
                        if let '0'..='9' = c {
                            frac_counts += 1;
                            false
                        } else {
                            true
                        }
                    });
                    self.linear_offset(int_counts + frac_counts)
                        .replace(Ok(Token::LiteralFloat))
                } else {
                    self.linear_offset(int_counts)
                        .replace(Ok(Token::LiteralInteger))
                }
            }

            '\'' => {
                if let Some((len, _)) = self.step_char::<'\''>(1) {
                    self.linear_offset(2 + len).replace(Ok(Token::LiteralChar))
                } else {
                    self.linear_offset(1).replace(Err(Error::UnclosedChar))
                }
            }

            '"' => {
                if let Some(len) = self.step_str(1) {
                    self.linear_offset(1 + len)
                        .replace(Ok(Token::LiteralString))
                } else {
                    self.linear_offset(1).replace(Err(Error::UnclosedStr))
                }
            }

            c if Self::is_ident_start_char(c) => {
                let len = chars.take_while(|&c| Self::is_ident_middle_char(c)).count();
                self.linear_offset(1 + len).replace(Ok(Token::Ident))
            }

            c => self.linear_offset(1).replace(Err(Error::UnknownOperand(c))),
        };

        Some(r)
    }
}
