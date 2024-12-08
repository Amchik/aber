//! # Abstract Syntax Tree
//!
//! Parser for lexical tokens[^1]. Main function are [`aber::ast::parse`].
//!
//!
//! [^1]: [`aber::lex::Token`]

use std::{borrow::Cow, iter::Peekable};

use crate::lex::{Token, WithLinearPosition, WithPosition};

/// Minimal code unit, including blocks, idents, numbers, etc...
/// Used as [`Expression`] unit.
#[derive(Debug, Clone, PartialEq)]
pub enum Unit<'a> {
    Ident(Cow<'a, str>),
    ConstInteger(u64),
    ConstNegInteger(u64),
    ConstFloat(f64),
    ConstChar(char),
    ConstString(Cow<'a, str>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum SyntaxCall<'a> {
    Opaque(Unit<'a>),
    Generic(Unit<'a>, Vec<Vec<ExpressionUnit<'a>>>),
    Tuple(Vec<ExpressionUnit<'a>>),
    Block(Vec<Expression<'a>>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExpressionUnitKind<'a> {
    SingleCall(SyntaxCall<'a>),
    MethodCall(SyntaxCall<'a>, Box<ExpressionUnitKind<'a>>),
    PathCall(SyntaxCall<'a>, Box<ExpressionUnitKind<'a>>),
    Assigment,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExpressionUnit<'a> {
    pub unit: ExpressionUnitKind<'a>,
    pub negated: bool,
    pub paired: bool,
}

pub type Expression<'a> = Vec<ExpressionUnit<'a>>;

#[derive(Debug, Clone, PartialEq)]
pub enum Error {
    UnexpectedEOF,
    UnexpectedToken(Token),
    MismatchedToken { expected: Token, actual: Token },
    InvalidInteger,
    InvalidFloat,
    InvalidCharEscape(char),
}
pub type Result<T> = std::result::Result<T, WithLinearPosition<Error>>;

fn parse_uint(input: &str) -> Option<u64> {
    let mut res: u64 = 0;
    for c in input.chars().filter(|&p| p != '_') {
        match c {
            '0'..='9' => {
                res = res
                    .checked_mul(10)?
                    .checked_add((c as u16 - '0' as u16).into())?
            }
            '_' => continue,
            _ => unreachable!("called parse_int() with invalid char '{c}'"),
        }
    }
    Some(res)
}
fn parse_int(input: &str) -> Option<i64> {
    if let Some(input) = input.strip_prefix('-') {
        parse_uint(input).and_then(|v| i64::try_from(v).ok()?.checked_neg())
    } else {
        parse_uint(input).and_then(|v| i64::try_from(v).ok())
    }
}
fn escape_char(c: char) -> Option<char> {
    match c {
        '0'..='9' => Some((c as u8 - b'0') as char),
        '\\' | '\"' | '\'' => Some(c),
        'a' => Some(7 as char),
        'b' => Some(8 as char),
        't' => Some(9 as char),
        'n' => Some(10 as char),
        'v' => Some(11 as char),
        'f' => Some(12 as char),
        'r' => Some(13 as char),
        'e' => Some(27 as char),

        _ => None,
    }
}
fn parse_str(input: &str) -> std::result::Result<Cow<str>, char> {
    let mut split = input.split('\\').peekable();
    let Some(first) = split.next() else {
        // empty string
        return Ok("".into());
    };

    if split.peek().is_none() {
        // no escapes
        return Ok(first.into());
    }

    let mut result = String::with_capacity(input.len());
    result.push_str(first);
    for segment in split {
        let Some(char) = segment.chars().next() else {
            // zero-length string, so it was `\`
            result.push('\\');
            continue;
        };
        result.push(escape_char(char).ok_or(char)?);
        result.push_str(&segment[char.len_utf8()..]);
    }

    Ok(result.into())
}

fn parse_expr_unit<'a>(
    input: &'a str,
    tokens: &mut Peekable<impl Iterator<Item = WithLinearPosition<Token>>>,
) -> Result<ExpressionUnit<'a>> {
    let token = tokens
        .next()
        .ok_or(WithLinearPosition::zero(Error::UnexpectedEOF))?;

    let pos = token.extract();

    let call = 'call: {
        let unit = match token.value.value {
            Token::Equal => {
                return Ok(ExpressionUnit {
                    unit: ExpressionUnitKind::Assigment,
                    negated: false,
                    paired: false,
                });
            }
            Token::At => {
                return parse_expr_unit(input, tokens).map(|mut v| {
                    v.negated = true;
                    v
                })
            }
            Token::LiteralInteger => {
                let span = &input[token.offset_start..token.offset_end];
                if let Some(span) = span.strip_prefix('-') {
                    Unit::ConstNegInteger(
                        parse_uint(span).ok_or(pos.replace(Error::InvalidInteger))?,
                    )
                } else {
                    Unit::ConstInteger(parse_uint(span).ok_or(pos.replace(Error::InvalidInteger))?)
                }
            }
            Token::LiteralFloat => {
                let span = &input[token.offset_start..token.offset_end];
                let (int, frac) = span
                    .split_once('.')
                    .expect("invalid float literal matched from lexer, failed to split by dot");

                let (int, frac) = match parse_int(int).zip(parse_uint(frac)) {
                    Some(v) => v,
                    _ => return Err(pos.replace(Error::InvalidFloat)),
                };

                let float = {
                    let digits = (frac as f64).log10().floor() as u32 + 1;
                    let scale = match 10u32.checked_pow(digits) {
                        Some(v) => v,
                        _ => return Err(pos.replace(Error::InvalidFloat)),
                    };
                    int as f64 + frac as f64 / scale as f64
                };

                Unit::ConstFloat(float)
            }
            Token::LiteralChar => {
                let span = &input[token.offset_start + 1..token.offset_end - 1];
                let char = span
                    .strip_prefix('\\')
                    .map(|v| {
                        let c = v.chars().next();
                        c.map(|c| escape_char(c).ok_or(c))
                    })
                    .unwrap_or_else(|| span.chars().next().map(std::result::Result::Ok))
                    .expect(
                        "invalid char literal matched from lexer, no char after escape sequence",
                    );

                match char {
                    Ok(c) => Unit::ConstChar(c),
                    Err(c) => return Err(pos.replace(Error::InvalidCharEscape(c))),
                }
            }
            Token::LiteralString => {
                let span = &input[token.offset_start + 1..token.offset_end - 1];

                match parse_str(span) {
                    Ok(v) => Unit::ConstString(v),
                    Err(c) => return Err(pos.replace(Error::InvalidCharEscape(c))),
                }
            }
            Token::Ident => {
                let span = &input[token.offset_start..token.offset_end];

                // FIXME: Cow for ident?
                Unit::Ident(span.into())
            }

            Token::OpenParanthesis => {
                let peek = tokens.peek().map(|v| v.value.value);
                let exprs = if peek == Some(Token::CloseParanthesis) {
                    _ = tokens.next();
                    Vec::new()
                } else {
                    let mut exprs = Vec::new();

                    loop {
                        exprs.push(parse_expr_unit(input, tokens)?);
                        let peek = tokens.peek().map(|v| v.value.value);
                        match peek {
                            Some(Token::Comma) => {
                                _ = tokens.next();
                                if tokens.peek().map(|v| v.value.value)
                                    == Some(Token::CloseParanthesis)
                                {
                                    _ = tokens.next();
                                    break;
                                }
                            }
                            Some(Token::CloseParanthesis) => {
                                _ = tokens.next();
                                break;
                            }
                            _ => (),
                        }
                    }

                    exprs
                };

                break 'call SyntaxCall::Tuple(exprs);
            }

            Token::OpenBrace => break 'call SyntaxCall::Block(parse_block(input, tokens)?),

            Token::Comment => unreachable!(),

            other => return Err(pos.replace(Error::UnexpectedToken(other))),
        };

        match tokens.peek() {
            Some(WithLinearPosition {
                value:
                    WithPosition {
                        value: Token::OpenBracket,
                        ..
                    },
                ..
            }) => {
                _ = tokens.next();

                let mut generics = Vec::new();
                let mut exprs = Vec::new();

                loop {
                    exprs.push(parse_expr_unit(input, tokens)?);
                    let peek = tokens.peek().map(|v| v.value.value);
                    match peek {
                        Some(Token::Comma) => {
                            _ = tokens.next();
                            generics.push(exprs);
                            exprs = Vec::new();
                            if tokens.peek().map(|v| v.value.value) == Some(Token::CloseBracket) {
                                _ = tokens.next();
                                break;
                            }
                        }
                        Some(Token::CloseBracket) => {
                            generics.push(exprs);
                            _ = tokens.next();
                            break;
                        }
                        _ => (),
                    }
                }

                SyntaxCall::Generic(unit, generics)
            }
            _ => SyntaxCall::Opaque(unit),
        }
    };

    match tokens.peek().map(|v| v.value.value) {
        Some(Token::Dot) => {
            _ = tokens.next();
            let expr_unit = parse_expr_unit(input, tokens)?;
            Ok(ExpressionUnit {
                unit: ExpressionUnitKind::MethodCall(call, Box::new(expr_unit.unit)),
                negated: expr_unit.negated,
                paired: expr_unit.paired,
            })
        }
        Some(Token::DoubleColon) => {
            _ = tokens.next();
            let expr_unit = parse_expr_unit(input, tokens)?;
            Ok(ExpressionUnit {
                unit: ExpressionUnitKind::PathCall(call, Box::new(expr_unit.unit)),
                negated: expr_unit.negated,
                paired: expr_unit.paired,
            })
        }
        Some(Token::Colon) => {
            _ = tokens.next();
            Ok(ExpressionUnit {
                unit: ExpressionUnitKind::SingleCall(call),
                negated: false,
                paired: true,
            })
        }
        _ => Ok(ExpressionUnit {
            unit: ExpressionUnitKind::SingleCall(call),
            negated: false,
            paired: false,
        }),
    }
}

fn parse_expression<'a>(
    input: &'a str,
    tokens: &mut Peekable<impl Iterator<Item = WithLinearPosition<Token>>>,
) -> Result<Expression<'a>> {
    let mut expr = Expression::new();

    while tokens.peek().map(|v| v.value.value) != Some(Token::SemiColon) {
        expr.push(parse_expr_unit(input, tokens)?);
    }

    _ = tokens.next();

    Ok(expr)
}

fn parse_block<'a>(
    input: &'a str,
    tokens: &mut Peekable<impl Iterator<Item = WithLinearPosition<Token>>>,
) -> Result<Vec<Expression<'a>>> {
    let mut exprs = Vec::new();

    while tokens.peek().map(|v| v.value.value) != Some(Token::CloseBrace) {
        exprs.push(parse_expression(input, tokens)?);
    }

    _ = tokens.next();

    Ok(exprs)
}

pub fn parse(
    input: &str,
    tokens: impl IntoIterator<Item = WithLinearPosition<Token>>,
) -> Result<Vec<Expression>> {
    let mut exprs = Vec::new();
    let tokens = &mut tokens
        .into_iter()
        .filter(|v| v.value.value != Token::Comment)
        .peekable();

    while tokens.peek().map(|v| v.value.value).is_some() {
        exprs.push(parse_expression(input, tokens)?);
    }

    Ok(exprs)
}
