use crate::scanner::{Scanner, Token};

use std::error::Error;
use std::fmt;

#[derive(Debug)]
pub struct SyntaxError {
    what: String,
}

impl SyntaxError {
    fn new(what: &str) -> Self {
        SyntaxError {
            what: what.to_string(),
        }
    }
}

impl fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.what)
    }
}

impl Error for SyntaxError {
    fn description(&self) -> &str {
        &self.what
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Float(f64),
}

fn is_same_value_type(l: &Value, r: &Value) -> bool {
    std::mem::discriminant(l) == std::mem::discriminant(r)
}

trait Expression {
    fn eval(&self) -> Result<Value, SyntaxError>;
}

struct BinaryExpr {
    left: Box<dyn Expression>,
    operator: Token,
    right: Box<dyn Expression>,
}

impl Expression for BinaryExpr {
    fn eval(&self) -> Result<Value, SyntaxError> {
        let left_value = self.left.eval()?;
        let right_value = self.right.eval()?;
        if is_same_value_type(&left_value, &right_value) {
            match left_value {
                Value::Float(lf) => match right_value {
                    Value::Float(rf) => match self.operator {
                        Token::Asterisc => Ok(Value::Float(lf * rf)),
                        Token::Plus => Ok(Value::Float(lf + rf)),
                        Token::Minus => Ok(Value::Float(lf - rf)),
                        Token::Slash => Ok(Value::Float(lf / rf)),
                        _ => Err(SyntaxError::new("Unsupported operator")),
                    },
                },
            }
        } else {
            Err(SyntaxError::new("Type mismatch in binary expression"))
        }
    }
}

struct UnaryExpression {
    operator: Token,
    right: Box<dyn Expression>,
}

impl Expression for UnaryExpression {
    fn eval(&self) -> Result<Value, SyntaxError> {
        let right_value = self.right.eval()?;
        match self.operator {
            Token::Minus => match right_value {
                Value::Float(rf) => Ok(Value::Float(-rf)),
            },
            _ => Err(SyntaxError::new("Invalid unary operator")),
        }
    }
}

struct LiteralNumber {
    value: Value,
}

impl Expression for LiteralNumber {
    fn eval(&self) -> Result<Value, SyntaxError> {
        Ok(self.value.clone())
    }
}

type ResultExpr = Result<Box<dyn Expression>, SyntaxError>;

struct Parser<'a> {
    pub scanner: Scanner<'a>,
}

impl<'a> Parser<'a> {
    fn new(scanner: Scanner<'a>) -> Self {
        Parser { scanner }
    }

    pub fn parse(&mut self) -> ResultExpr {
        self.term()
    }

    fn term(&mut self) -> ResultExpr {
        let mut expr = self.factor()?;
        while self.is_next(&[Token::Plus, Token::Minus]) {
            let op = self.next_token().unwrap();
            let right = self.factor()?;
            expr = Box::new(BinaryExpr {
                left: expr,
                operator: op,
                right,
            });
        }
        Ok(expr)
    }

    fn factor(&mut self) -> ResultExpr {
        let mut expr = self.unary()?;
        while self.is_next(&[Token::Asterisc, Token::Slash]) {
            let op = self.next_token().unwrap();
            let right = self.unary()?;
            expr = Box::new(BinaryExpr {
                left: expr,
                operator: op,
                right,
            });
        }
        Ok(expr)
    }

    fn unary(&mut self) -> ResultExpr {
        if self.is_next(&[Token::Minus]) {
            Ok(Box::new(UnaryExpression {
                operator: self.next_token().unwrap(),
                right: self.primary()?,
            }))
        } else {
            Ok(self.primary()?)
        }
    }

    fn primary(&mut self) -> ResultExpr {
        match self.next_token() {
            Some(token) => match token {
                Token::Number(n) => Ok(Box::new(LiteralNumber {
                    value: Value::Float(n.parse::<f64>().unwrap()),
                })),
                _ => Err(SyntaxError::new("Invalid primary token")),
            },
            _ => Err(SyntaxError::new("Unexptected EOF")),
        }
    }

    fn is_next(&self, tokens: &[Token]) -> bool {
        if let Some(token) = self.peek() {
            tokens.iter().any(|t| *t == token)
        } else {
            false
        }
    }

    fn next_token(&mut self) -> Option<Token> {
        self.scanner.next()
    }

    fn peek(&self) -> Option<Token> {
        self.scanner.clone().next()
    }
}

pub fn interprete(input: &str) -> Result<Value, SyntaxError> {
    let mut parser = Parser::new(Scanner::new(input));
    parser.parse()?.eval()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interpret_one_literal() {
        let value = interprete("1234");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(1234.0)),
            _ => assert!(false),
        }
    }

    #[test]
    fn negative_number() {
        let value = interprete("-3.2");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(-3.2)),
            _ => assert!(false),
        }
    }

    #[test]
    fn interpret_addition() {
        let value = interprete("45 + 101");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(146.0)),
            _ => assert!(false),
        }
    }

    #[test]
    fn interpret_subtraction() {
        let value = interprete("320 - 25");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(295.0)),
            _ => assert!(false),
        }
    }

    #[test]
    fn interpret_subtraction_negative_number() {
        let value = interprete("10 - -5");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(15.0)),
            _ => assert!(false),
        }
    }

    #[test]
    fn interpret_addition_with_decimals() {
        let value = interprete("9.95 + 10.08");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(20.03)),
            _ => assert!(false),
        }
    }

    #[test]
    fn interpret_multiple_factors() {
        let value = interprete("0.5 + 3 + 86.8 + 1000.0 + -500.0");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(590.3)),
            _ => assert!(false),
        }
    }

    #[test]
    fn add_number_with_identifier() {
        let value = interprete("1.5 + foo");

        match value {
            Ok(_) => assert!(false),
            Err(e) => assert_eq!("Invalid primary token", e.what),
        }
    }

    #[test]
    fn multiplication() {
        let value = interprete("3 * 2 + 1");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(7.0)),
            _ => assert!(false),
        }
    }

    #[test]
    fn division() {
        let value = interprete("3 / 2 + 1");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(2.5)),
            _ => assert!(false),
        }
    }

    #[test]
    fn arithmetic_precedence() {
        let value = interprete("3 + 5 / 2 * 3 + 1");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(11.5)),
            _ => assert!(false),
        }
    }
}
