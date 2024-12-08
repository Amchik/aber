//! # Aber lexer
//!
// TODO: comment

use std::fmt::Display;

/// Kind of lexical[^1] token. Usually wrapped in [`WithPosition<T>`].
///
/// [^1]: [`Lex`]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Token {
    /// Identificator. Can be single char or sequence of chars (eg. `/`, `-`)
    /// or string (eg. `ident`, `foobar`, `min-max`)
    Ident,
    /// Comment, span to ignore.
    Comment,
    /// Integer literal in base10. Can contains `_` chars used as visual separator,
    /// so `10_000__` and `10000` is a same integers, but `_10` is not an
    /// [`Token::LiteralInteger`].
    LiteralInteger,
    /// Float literal. Can contains `_` chars used as visual separator,
    /// so `10_000.01` and `10000.01` is a same numbers. Note that this literal can ends with `_`
    /// or dot, so `10.` and `10._` are valid literals.
    LiteralFloat,
    /// Single char literal is a single utf-8 symbol that can be after `\`, between two `'`
    /// symbols, eg. `'h'` and `'\e'`. Char cannot be a newline symbol (`\n`). UTF-8 examples of
    /// this literal: `'ё'` and `'\ё'`. Note that chars `'` and `\` can be written, using second
    /// variant of syntax: `'\''` and `\\`. Sequences `''`, `'''`, `'\'` are NOT valid
    /// [`Token::LiteralChar`].
    LiteralChar,
    /// UTF-8 string literal, contains unescaped string between two `"` symbols. Every single char
    /// are follow the same rules as chars in [`Token::LiteralChar`]. Some of them is that char
    /// cannot be a newline char, so this literal is one line. String cannot ends with single `\`
    /// char (but can with double) so `"\"` isn't valid literal. Example of valid literals:
    /// `"Πi \'\" \\"`. Literal can contain an empty string: `""`.
    LiteralString,
    /// Symbol `:`
    Colon,
    /// Symbol `::`
    DoubleColon,
    /// Symbol `;`
    SemiColon,
    /// Symbol `,`
    Comma,
    /// Symbol `(`
    OpenParanthesis,
    /// Symbol `)`
    CloseParanthesis,
    /// Symbol `{`
    OpenBrace,
    /// Symbol `}`
    CloseBrace,
    /// Symbol `[`
    OpenBracket,
    /// Symbol `]`
    CloseBracket,
    /// Symbol `.`
    Dot,
    /// Symbol `@`
    At,
    /// Symbol `=`
    Equal,
}

/// Position in code.
///
/// [^1]: [`WithPosition`]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Position {
    /// Line in code. In normal files it starts from `1` but zero is valid value for line.
    pub line: u32,
    /// Char at line in code. Usually starts from `0`.
    pub char: u32,
}

/// Describes position of element, like [`Token`]s or any other type.
///
/// # Example
/// ```
/// # use aber::lex::Token;
/// use aber::lex::{Position, WithPosition};
///
/// let start = Position { line: 1, char: 0 };
/// let end = Position { line: 1, char: 8 };
///
/// // One point:
/// let span = WithPosition::location(Token::Comma, start);
/// assert_eq!(span.start, start);
/// assert_eq!(span.end, None);
///
/// // Range:
/// let span = WithPosition::range(Token::Comma, start, start);
/// assert_eq!(span.end, Some(start)); // end can equal to start
///
/// // Range or dot:
/// let span = WithPosition::range_or_dot(Token::Comment, start, end);
/// assert_eq!(span.end, Some(end));
/// // but if start equals end...
/// let span = WithPosition::range_or_dot(Token::Comma, start, start);
/// assert_eq!(span.end, None);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct WithPosition<T: ?Sized> {
    /// Start position
    pub start: Position,
    /// End position. If end is `None` it equals to dot.
    pub end: Option<Position>,
    /// Wrapped value
    pub value: T,
}

impl<T> WithPosition<T> {
    /// Wrap in dot position.
    ///
    /// # Example
    /// ```
    /// use aber::lex::{Position, WithPosition};
    ///
    /// let dot = WithPosition::location((), Position { line: 1, char: 0 });
    /// assert_eq!(dot.end, None);
    /// ```
    pub fn location(value: T, start: Position) -> Self {
        WithPosition {
            start,
            end: None,
            value,
        }
    }

    /// Wrap in range. If you need to exclude zero-length range, use [`WithPosition::range_or_dot`].
    ///
    /// # Example
    /// ```
    /// use aber::lex::{Position, WithPosition};
    ///
    /// let start = Position { line: 1, char: 0 };
    /// let end = Position { line: 2, char: 2 };
    ///
    /// let span = WithPosition::range((), start, end);
    /// assert_eq!(span.start, start);
    /// assert_eq!(span.end, Some(end));
    /// ```
    ///
    /// Even if start equals end:
    /// ```
    /// # use aber::lex::{Position, WithPosition};
    /// # let start = Position { line: 1, char: 0 };
    /// let span = WithPosition::range((), start, start);
    /// assert_eq!(span.end, Some(start));
    /// ```
    pub fn range(value: T, start: Position, end: Position) -> Self {
        WithPosition {
            start,
            end: Some(end),
            value,
        }
    }

    /// Wrap in range. If range length is zero (`start == end`) wraps as dot (don't set end
    /// position).
    ///
    /// # Example
    /// ```
    /// use aber::lex::{Position, WithPosition};
    ///
    /// let start = Position { line: 1, char: 0 };
    /// let end = Position { line: 2, char: 2 };
    ///
    /// let span = WithPosition::range_or_dot((), start, end);
    /// assert_eq!(span.start, start);
    /// assert_eq!(span.end, Some(end));
    ///
    /// let dot = WithPosition::range_or_dot((), start, start);
    /// assert_eq!(dot.start, start);
    /// assert_eq!(dot.end, None);
    /// ```
    pub fn range_or_dot(value: T, start: Position, end: Position) -> Self {
        if start == end {
            Self::location(value, start)
        } else {
            Self::range(value, start, end)
        }
    }

    /// Maps wrapped value.
    ///
    /// # Example
    /// ```
    /// use aber::lex::{Position, WithPosition};
    ///
    /// let span = WithPosition::location(42_u32, Position { line: 4, char: 8 });
    /// let span = span.map(|v| v / 2);
    /// assert_eq!(span.value, 21);
    /// ```
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

    /// Drop previous value and replace it to new.
    ///
    /// # Example
    /// ```
    /// use aber::lex::{Position, WithPosition};
    ///
    /// let span = WithPosition::location(42_u32, Position { line: 4, char: 8 });
    /// let span = span.replace("Hello!");
    /// assert_eq!(span.value, "Hello!");
    /// ```
    pub fn replace<U>(self, new_value: U) -> WithPosition<U> {
        WithPosition {
            start: self.start,
            end: self.end,
            value: new_value,
        }
    }

    pub fn extract(&self) -> WithPosition<()> {
        WithPosition {
            start: self.start,
            end: self.end,
            value: (),
        }
    }

    pub fn linear(self, offset_start: usize, offset_end: usize) -> WithLinearPosition<T> {
        WithLinearPosition {
            offset_start,
            offset_end,
            value: self,
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

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct WithLinearPosition<T: ?Sized> {
    pub offset_start: usize,
    pub offset_end: usize,
    pub value: WithPosition<T>,
}

impl<T> WithLinearPosition<T> {
    pub(crate) fn zero(value: T) -> Self {
        WithLinearPosition {
            offset_start: 0,
            offset_end: 0,
            value: WithPosition {
                start: Position { line: 0, char: 0 },
                end: None,
                value,
            },
        }
    }

    pub fn map<U, F>(self, f: F) -> WithLinearPosition<U>
    where
        F: FnOnce(T) -> U,
    {
        WithLinearPosition {
            offset_start: self.offset_start,
            offset_end: self.offset_end,
            value: self.value.map(f),
        }
    }

    pub fn replace<U>(self, new_value: U) -> WithLinearPosition<U> {
        WithLinearPosition {
            offset_start: self.offset_start,
            offset_end: self.offset_end,
            value: self.value.replace(new_value),
        }
    }

    pub fn extract(&self) -> WithLinearPosition<()> {
        WithLinearPosition {
            offset_start: self.offset_start,
            offset_end: self.offset_end,
            value: self.value.extract(),
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

/// Aber lexer. See module-level documentation for more.
/// Lexer is an iterator.
///
/// # Example
/// ```
/// use aber::lex::{Lex, Token, WithPosition, Position};
///
/// let input = "foo 42;";
/// let result: Vec<_> = Lex::new(input).map(|v| v.map(Result::unwrap)).collect();
///
/// assert_eq!(&result[..], &[
///     WithPosition::range(
///         Token::Ident,
///         Position { line: 1, char: 0 },
///         Position { line: 1, char: 2 },
///     ),
///     WithPosition::range(
///         Token::LiteralInteger,
///         Position { line: 1, char: 4 },
///         Position { line: 1, char: 5 },
///     ),
///     WithPosition::location(
///         Token::SemiColon,
///         Position { line: 1, char: 6 },
///     ),
/// ]);
/// ```
pub struct Lex<'a> {
    v: &'a str,
    offset: usize,
    pos: Position,
}

impl<'a> Lex<'a> {
    /// Creates new [`Lex`] from string.
    pub fn new(v: &'a str) -> Self {
        Lex {
            v,
            offset: 0,
            pos: Position { line: 1, char: 0 },
        }
    }

    /// Current lexer location.
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

    fn linear_offset(&mut self, offset: usize) -> WithLinearPosition<()> {
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
        .linear(self.offset - offset, self.offset)
    }

    /// Steps one char or `\` + char and returns it's utf-8 length. If failed to get next char
    /// returns `None`. Also returns found char. If char is newline, returns `None`
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

    /// Works like `step_char`, stops at `"` symbol. Returns `None` on newline.
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
    type Item = WithLinearPosition<Result<Token, Error>>;

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
                let len: usize = chars
                    .take_while(|&c| Self::is_ident_middle_char(c))
                    .map(|v| v.len_utf8())
                    .sum();
                self.linear_offset(c.len_utf8() + len)
                    .replace(Ok(Token::Ident))
            }

            c => self.linear_offset(1).replace(Err(Error::UnknownOperand(c))),
        };

        Some(r)
    }
}
