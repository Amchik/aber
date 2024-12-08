//! # Semantic Intermediate Language (Aber SIL)
//!
//! *Aber Semantic Intermediate Language (Aber SIL)* is a simple language, containing simplified [`aber::ast`]
//! output. After parsing into Aber SIL, code will be executed in stage 1 environment to resolve some symbols.
//!
//! Main function are [`Symbol::parse`].

use std::borrow::Cow;

use crate::ast::{self, ExpressionUnit, ExpressionUnitKind, SyntaxCall, Unit};

/// Primitive symbols without any effects.
/// Calling any symbol except [`PrimitiveSymbol::UnknownSymbol`] will return itself.
#[derive(Clone, PartialEq, Debug)]
pub enum PrimitiveSymbol<'a> {
    /// Integer
    Integer(i64),
    /// Float
    Float(f64),
    /// Char
    Char(char),
    /// String
    String(Cow<'a, str>),
    /// Unknown symbol. Can be replaced to one of [`PrimitiveSymbol`] in SIL if called
    UnknownSymbol(Cow<'a, str>),
}

impl<'a> PrimitiveSymbol<'a> {
    /// Convert AST [`Unit`] to primitive symbol.
    ///
    /// # Example
    /// ```
    /// use aber::{ast::Unit, sir::PrimitiveSymbol};
    ///
    /// assert_eq!(PrimitiveSymbol::Integer(-42), Unit::ConstNegInteger(42));
    /// ```
    pub fn from_unit(v: Unit<'a>) -> Self {
        match v {
            Unit::Ident(v) => Self::UnknownSymbol(v),
            Unit::ConstInteger(v) => Self::Integer(v as i64),
            Unit::ConstNegInteger(v) => Self::Integer(-(v as i64)),
            Unit::ConstFloat(v) => Self::Float(v),
            Unit::ConstChar(c) => Self::Char(c),
            Unit::ConstString(s) => Self::String(s),
        }
    }
}

/// Symbol in Aber SIR.
#[derive(Clone, PartialEq, Debug)]
pub enum Symbol<'a> {
    /// [`PrimitiveSymbol`], without any effects.
    Primitive(PrimitiveSymbol<'a>),

    /// Primitive symbols with generic arguments. Generic arguments used only on call.
    Generic(PrimitiveSymbol<'a>, Vec<Symbol<'a>>),
    /// Pair symbol. Note that calling pair symbol on primitive is not resolvable even if primitive
    /// symbol is integer.
    Pair(Box<Symbol<'a>>),
    /// Set symbol used for assign.
    Set(Box<Symbol<'a>>, Box<Symbol<'a>>),

    /// Tuple, including zero-length.
    Tuple(Vec<Symbol<'a>>),
    /// Obtain method or property of object.
    Method(Box<Symbol<'a>>, Box<Symbol<'a>>),
    /// Obtain objects by their paths.
    Path(Box<Symbol<'a>>, Box<Symbol<'a>>),
    /// Block symbol. Like normal block, containing array of symbols to calculate consistently.
    /// File is also block.
    Block(Vec<Symbol<'a>>),

    /// Symbol to call other symbols. Usually, calling can be resolved in more higher stages.
    Call(Box<Symbol<'a>>, Option<Box<Symbol<'a>>>),
}

/// Error in semantics, when parsing from AST
#[derive(Clone, PartialEq, Debug)]
pub enum SemError {
    /// Expression contains two equation signs.
    DoubleAssigment,
    /// Invalid assignment structure.
    InvalidAssigment,
    /// Attempt to call with arguments negated symbol.
    IncorrectNegate,
}

impl<'a> Symbol<'a> {
    fn parse_negated_call(call: SyntaxCall<'a>) -> Result<Self, SemError> {
        match call {
            SyntaxCall::Opaque(v) => Ok(Self::Primitive(PrimitiveSymbol::from_unit(v))),
            SyntaxCall::Generic(v, exprs) => Ok(Self::Generic(
                PrimitiveSymbol::from_unit(v),
                exprs
                    .into_iter()
                    .map(Self::parse_expression)
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            SyntaxCall::Tuple(exprs) => Ok(Self::Tuple(
                exprs
                    .into_iter()
                    .map(Self::parse_expression_unit)
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            SyntaxCall::Block(exprs) => Self::parse(exprs),
        }
    }

    fn parse_expression_unit(unit: ExpressionUnit<'a>) -> Result<Self, SemError> {
        let kind = unit.unit;
        let sym = match kind {
            ExpressionUnitKind::SingleCall(v) => Self::parse_negated_call(v)?,
            ExpressionUnitKind::MethodCall(v, n) => Self::Method(
                Box::new(Self::parse_negated_call(v)?),
                Box::new(Self::parse_expression_unit(ExpressionUnit {
                    unit: *n,
                    negated: true,
                    paired: false,
                })?),
            ),
            ExpressionUnitKind::PathCall(v, n) => Self::Path(
                Box::new(Self::parse_negated_call(v)?),
                Box::new(Self::parse_expression_unit(ExpressionUnit {
                    unit: *n,
                    negated: true,
                    paired: false,
                })?),
            ),

            ExpressionUnitKind::Assigment => unreachable!(),
        };

        if unit.paired {
            Ok(Self::Pair(Box::new(sym)))
        } else {
            Ok(sym)
        }

        /*match (unit.negated, unit.paired) {
            (true, true) => Ok(Self::Negate(Box::new(Self::Pair(Box::new(sym))))),
            (true, false) => Ok(Self::Negate(Box::new(sym))),
            (false, true) => Ok(Self::Pair(Box::new(sym))),
            (false, false) => Ok(sym),
        }*/
    }

    fn parse_expression_but_assign(expr: Vec<ExpressionUnit<'a>>) -> Result<Self, SemError> {
        fn symb_last<'a, 'b>(s: &'b mut Symbol<'a>) -> &'b mut Option<Box<Symbol<'a>>> {
            match s {
                Symbol::Call(_, Some(v)) => symb_last(v),
                Symbol::Call(_, v) => v,
                _ => unreachable!(),
            }
        }

        let mut iter = expr.into_iter();
        let first = iter.next().expect("first element");
        if first.negated {
            if iter.next().is_some() {
                return Err(SemError::IncorrectNegate);
            }

            return Self::parse_expression_unit(first);
        }

        let mut first = Self::Call(
            Box::new(Self::parse_expression_unit(
                first,
            )?),
            None,
        );

        for expr in iter.by_ref() {
            let negate = expr.negated;
            let symb = Self::parse_expression_unit(expr)?;
            let last = symb_last(&mut first);
            if negate {
                *last = Some(Box::new(symb));
                break;
            } else {
                *last = Some(Box::new(Self::Call(Box::new(symb), None)));
            }
        }

        if iter.next().is_some() {
            return Err(SemError::IncorrectNegate);
        }

        Ok(first)
    }

    fn parse_expression(expression: Vec<ExpressionUnit<'a>>) -> Result<Self, SemError> {
        if matches!(
            expression.get(1),
            Some(ExpressionUnit {
                unit: ExpressionUnitKind::Assigment,
                ..
            })
        ) {
            if expression[0].unit == ExpressionUnitKind::Assigment
                || expression
                    .iter()
                    .skip(2)
                    .any(|p| p.unit == ExpressionUnitKind::Assigment)
            {
                return Err(SemError::DoubleAssigment);
            }

            let mut expression = expression;
            _ = expression.remove(1);
            let first = expression.remove(0);
            let first = Self::parse_expression_unit(first)?;
            let value = Self::parse_expression(expression)?;
            Ok(Self::Set(Box::new(first), Box::new(value)))
        } else if expression
            .iter()
            .any(|p| p.unit == ExpressionUnitKind::Assigment)
        {
            Err(SemError::InvalidAssigment)
        } else {
            Ok(Self::parse_expression_but_assign(expression)?)
        }
    }

    /// Parse AST document to [`Symbol::Block`]. See module-level documentation, section "Parsing
    /// from AST".
    pub fn parse(expressions: Vec<ast::Expression<'a>>) -> Result<Self, SemError> {
        let mut symbols = Vec::new();

        for expression in expressions.into_iter().filter(|v| !v.is_empty()) {
            symbols.push(Self::parse_expression(expression)?);
        }

        Ok(Self::Block(symbols))
    }
}
