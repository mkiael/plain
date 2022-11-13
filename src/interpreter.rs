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

trait Statement {
    fn execute(&self) -> Result<Value, SyntaxError>;
}

struct ExpressionStatement {
    expr: Expr,
}

impl Statement for ExpressionStatement {
    fn execute(&self) -> Result<Value, SyntaxError> {
        evaluate(&self.expr)
    }
}

enum Expr {
    Binary {
        operator: Token,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Unary {
        operator: Token,
        right: Box<Expr>,
    },
    LiteralNumber {
        value: Value,
    },
}

fn evaluate(expr: &Expr) -> Result<Value, SyntaxError> {
    match expr {
        Expr::Binary {
            operator,
            left,
            right,
        } => {
            let left_value = evaluate(left)?;
            let right_value = evaluate(right)?;
            if is_same_value_type(&left_value, &right_value) {
                match left_value {
                    Value::Float(lf) => match right_value {
                        Value::Float(rf) => match operator {
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
        Expr::Unary { operator, right } => {
            let right_value = evaluate(right)?;
            match operator {
                Token::Minus => match right_value {
                    Value::Float(rf) => Ok(Value::Float(-rf)),
                },
                _ => Err(SyntaxError::new("Invalid unary operator")),
            }
        }
        Expr::LiteralNumber { value } => Ok(value.clone()),
    }
}

type ResultStmt = Result<Box<dyn Statement>, SyntaxError>;
type ResultExpr = Result<Expr, SyntaxError>;

struct Parser<'a> {
    pub scanner: Scanner<'a>,
}

impl<'a> Parser<'a> {
    fn new(scanner: Scanner<'a>) -> Self {
        Parser { scanner }
    }

    pub fn parse(&mut self) -> ResultStmt {
        self.statement()
    }

    fn statement(&mut self) -> ResultStmt {
        self.exprstmt()
    }

    fn exprstmt(&mut self) -> ResultStmt {
        let expr = self.expression()?;
        if let Some(token) = self.next_token() {
            if token != Token::Newline {
                return Err(SyntaxError::new("Expected newline"));
            }
        } else {
            return Err(SyntaxError::new("Unexpected EOF"));
        }
        Ok(Box::new(ExpressionStatement { expr }))
    }

    fn expression(&mut self) -> ResultExpr {
        self.term()
    }

    fn term(&mut self) -> ResultExpr {
        let mut expr = self.factor()?;
        while self.is_next(&[Token::Plus, Token::Minus]) {
            let op = self.next_token().unwrap();
            let right = self.factor()?;
            expr = Expr::Binary {
                operator: op,
                left: Box::new(expr),
                right: Box::new(right),
            };
        }
        Ok(expr)
    }

    fn factor(&mut self) -> ResultExpr {
        let mut expr = self.unary()?;
        while self.is_next(&[Token::Asterisc, Token::Slash]) {
            let op = self.next_token().unwrap();
            let right = self.unary()?;
            expr = Expr::Binary {
                operator: op,
                left: Box::new(expr),
                right: Box::new(right),
            };
        }
        Ok(expr)
    }

    fn unary(&mut self) -> ResultExpr {
        if self.is_next(&[Token::Minus]) {
            Ok(Expr::Unary {
                operator: self.next_token().unwrap(),
                right: Box::new(self.primary()?),
            })
        } else {
            Ok(self.primary()?)
        }
    }

    fn primary(&mut self) -> ResultExpr {
        match self.next_token() {
            Some(token) => match token {
                Token::Number(n) => Ok(Expr::LiteralNumber {
                    value: Value::Float(n.parse::<f64>().unwrap()),
                }),
                Token::LeftParen => {
                    let expr = self.term()?;
                    match self.next_token() {
                        Some(token) => {
                            if token == Token::RightParen {
                                Ok(expr)
                            } else {
                                Err(SyntaxError::new("Missing closing parenthesis"))
                            }
                        }
                        _ => Err(SyntaxError::new(
                            "Missing closing parenthesis, unexpected EOF",
                        )),
                    }
                }
                _ => Err(SyntaxError::new("Invalid primary token")),
            },
            _ => Err(SyntaxError::new("Unexpected EOF")),
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
    parser.parse()?.execute()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interpret_one_literal() {
        let value = interprete("1234\n");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(1234.0)),
            _ => assert!(false),
        }
    }

    #[test]
    fn negative_number() {
        let value = interprete("-3.2\n");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(-3.2)),
            _ => assert!(false),
        }
    }

    #[test]
    fn interpret_addition() {
        let value = interprete("45 + 101\n");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(146.0)),
            _ => assert!(false),
        }
    }

    #[test]
    fn interpret_subtraction() {
        let value = interprete("320 - 25\n");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(295.0)),
            _ => assert!(false),
        }
    }

    #[test]
    fn interpret_subtraction_negative_number() {
        let value = interprete("10 - -5\n");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(15.0)),
            _ => assert!(false),
        }
    }

    #[test]
    fn interpret_addition_with_decimals() {
        let value = interprete("9.95 + 10.08\n");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(20.03)),
            _ => assert!(false),
        }
    }

    #[test]
    fn interpret_multiple_factors() {
        let value = interprete("0.5 + 3 + 86.8 + 1000.0 + -500.0\n");

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
        let value = interprete("3 * 2 + 1\n");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(7.0)),
            _ => assert!(false),
        }
    }

    #[test]
    fn division() {
        let value = interprete("3 / 2 + 1\n");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(2.5)),
            _ => assert!(false),
        }
    }

    #[test]
    fn arithmetic_precedence() {
        let value = interprete("3 + 5 / 2 * 3 + 1\n");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(11.5)),
            _ => assert!(false),
        }
    }

    #[test]
    fn grouping() {
        let value = interprete("(12 + 4) * (10 - 8)\n");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(32.0)),
            _ => assert!(false),
        }
    }

    #[test]
    fn nested_groups() {
        let value = interprete("(1 * ((1) + 2)) * (((1 - 1) * 100) + 2)\n");

        match value {
            Ok(v) => assert_eq!(v, Value::Float(6.0)),
            _ => assert!(false),
        }
    }

    #[test]
    fn no_expression_after_open_paren() {
        let value = interprete("(");

        match value {
            Ok(_) => assert!(false),
            Err(e) => assert_eq!("Unexpected EOF", e.what),
        }
    }

    #[test]
    fn missing_closing_paren() {
        let value = interprete("(1 + 1(");

        match value {
            Ok(_) => assert!(false),
            Err(e) => assert_eq!("Missing closing parenthesis", e.what),
        }
    }

    #[test]
    fn missing_closing_paren_at_eof() {
        let value = interprete("(1 + 1");

        match value {
            Ok(_) => assert!(false),
            Err(e) => assert_eq!("Missing closing parenthesis, unexpected EOF", e.what),
        }
    }
}
