use crate::scanner::{Scanner, Token};

use std::collections::HashMap;
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

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Value {
    Float(f64),

    #[allow(dead_code)]
    Callable(fn(Vec<Value>) -> Value),
}

fn is_same_value_type(l: &Value, r: &Value) -> bool {
    std::mem::discriminant(l) == std::mem::discriminant(r)
}

struct Environment {
    variables: HashMap<String, Value>,
}

impl Environment {
    fn new() -> Self {
        Environment {
            variables: HashMap::new(),
        }
    }

    fn define(&mut self, name: &str, value: Value) -> bool {
        if !self.variables.contains_key(name) {
            self.variables.insert(name.to_string(), value) == None
        } else {
            false
        }
    }

    fn get(&self, name: &str) -> Option<&Value> {
        self.variables.get(name)
    }
}

enum Stmt {
    Expr { expr: Expr },
    VarDecl { name: String, expr: Expr },
}

fn execute(stmt: &Stmt, env: &mut Environment) -> Result<Value, SyntaxError> {
    match stmt {
        Stmt::Expr { expr } => evaluate(expr, env),
        Stmt::VarDecl { name, expr } => {
            let value = evaluate(expr, env)?;
            if env.define(name, value) {
                Ok(value)
            } else {
                Err(SyntaxError::new(&format!(
                    "Variable {name} is already defined"
                )))
            }
        }
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
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
    LiteralNumber {
        value: Value,
    },
    Variable {
        name: String,
    },
}

fn evaluate(expr: &Expr, env: &mut Environment) -> Result<Value, SyntaxError> {
    match expr {
        Expr::Binary {
            operator,
            left,
            right,
        } => {
            let left_value = evaluate(left, env)?;
            let right_value = evaluate(right, env)?;
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
                        _ => Err(SyntaxError::new("Invalid binary operands")),
                    },
                    _ => Err(SyntaxError::new("Invalid binary operands")),
                }
            } else {
                Err(SyntaxError::new("Type mismatch in binary expression"))
            }
        }
        Expr::Unary { operator, right } => {
            let right_value = evaluate(right, env)?;
            match operator {
                Token::Minus => match right_value {
                    Value::Float(rf) => Ok(Value::Float(-rf)),
                    _ => Err(SyntaxError::new("Invalid unary operand")),
                },
                _ => Err(SyntaxError::new("Invalid unary operator")),
            }
        }
        Expr::Call { callee, args } => match evaluate(callee, env)? {
            Value::Callable(f) => Ok(f(args
                .iter()
                .map(|arg| evaluate(arg, env).unwrap())
                .collect())),
            _ => Err(SyntaxError::new("Expression not callable")),
        },
        Expr::LiteralNumber { value } => Ok(*value),
        Expr::Variable { name } => match env.get(name) {
            Some(value) => Ok(*value),
            _ => Err(SyntaxError::new(&format!("Variable {name} is not defined"))),
        },
    }
}

type ResultStmt = Result<Stmt, SyntaxError>;
type ResultExpr = Result<Expr, SyntaxError>;

struct Parser<'a> {
    pub scanner: Scanner<'a>,
}

impl<'a> Parser<'a> {
    fn new(scanner: Scanner<'a>) -> Self {
        Parser { scanner }
    }

    pub fn parse(&mut self) -> ResultStmt {
        self.variable_decl()
    }

    fn variable_decl(&mut self) -> ResultStmt {
        if self.is_next(&[Token::Let]) {
            self.next_token();
            match self.next_token() {
                Some(Token::Identifier(name)) => match self.next_token() {
                    Some(Token::Equal) => {
                        let var_decl = Stmt::VarDecl {
                            name,
                            expr: self.expression()?,
                        };
                        match self.next_token() {
                            Some(Token::Newline) => Ok(var_decl),
                            _ => Err(SyntaxError::new("Expected newline after declaration")),
                        }
                    }
                    _ => Err(SyntaxError::new("Expected equal sign after identifier")),
                },
                _ => Err(SyntaxError::new("Expected identifier")),
            }
        } else {
            self.statement()
        }
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
        Ok(Stmt::Expr { expr })
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
            self.call()
        }
    }

    fn call(&mut self) -> ResultExpr {
        let mut expr = self.primary()?;
        loop {
            if self.peek() == Some(Token::LeftParen) {
                self.next_token();
                let mut args: Vec<Expr> = Vec::new();
                if self.peek() != Some(Token::RightParen) {
                    loop {
                        args.push(self.expression()?);
                        if self.peek() == Some(Token::Comma) {
                            self.next_token();
                        } else {
                            break;
                        }
                    }
                }
                if self.next_token() == Some(Token::RightParen) {
                    expr = Expr::Call {
                        callee: Box::new(expr),
                        args,
                    };
                } else {
                    return Err(SyntaxError::new("Expected closing parenthesis"));
                }
            } else {
                break;
            }
        }
        Ok(expr)
    }

    fn primary(&mut self) -> ResultExpr {
        match self.next_token() {
            Some(token) => match token {
                Token::Identifier(name) => Ok(Expr::Variable { name }),
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

impl<'a> Iterator for Parser<'a> {
    type Item = ResultStmt;

    fn next(&mut self) -> Option<ResultStmt> {
        if self.peek() == None {
            None
        } else {
            Some(self.parse())
        }
    }
}

pub fn interprete(input: &str) -> Result<Value, SyntaxError> {
    let parser = Parser::new(Scanner::new(input));
    let mut env = Environment::new();
    let mut last_value = Value::Float(0.0);
    for stmt in parser {
        last_value = execute(&stmt?, &mut env)?;
    }
    Ok(last_value)
}

// TODO(mkiael): Remove this function when interpreter is more complete
#[allow(dead_code)]
fn interprete_with_env(input: &str, env: &mut Environment) -> Result<Value, SyntaxError> {
    let parser = Parser::new(Scanner::new(input));
    let mut last_value = Value::Float(0.0);
    for stmt in parser {
        last_value = execute(&stmt?, env)?;
    }
    Ok(last_value)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn add_floats(values: Vec<Value>) -> Value {
        Value::Float(
            values
                .into_iter()
                .map(|v| match v {
                    Value::Float(f) => f,
                    _ => panic!(),
                })
                .reduce(|acc, f| acc + f)
                .unwrap(),
        )
    }

    #[test]
    fn interpret_one_literal() {
        let value = interprete("1234\n");

        assert_eq!(value.unwrap(), Value::Float(1234.0));
    }

    #[test]
    fn negative_number() {
        let value = interprete("-3.2\n");

        assert_eq!(value.unwrap(), Value::Float(-3.2));
    }

    #[test]
    fn interpret_addition() {
        let value = interprete("45 + 101\n");

        assert_eq!(value.unwrap(), Value::Float(146.0));
    }

    #[test]
    fn interpret_subtraction() {
        let value = interprete("320 - 25\n");

        assert_eq!(value.unwrap(), Value::Float(295.0));
    }

    #[test]
    fn interpret_subtraction_negative_number() {
        let value = interprete("10 - -5\n");

        assert_eq!(value.unwrap(), Value::Float(15.0));
    }

    #[test]
    fn interpret_addition_with_decimals() {
        let value = interprete("9.95 + 10.08\n");

        assert_eq!(value.unwrap(), Value::Float(20.03));
    }

    #[test]
    fn interpret_multiple_factors() {
        let value = interprete("0.5 + 3 + 86.8 + 1000.0 + -500.0\n");

        assert_eq!(value.unwrap(), Value::Float(590.3));
    }

    #[test]
    fn add_number_with_identifier() {
        let value = interprete("1.5 + foo\n");

        assert_eq!(value.unwrap_err().what, "Variable foo is not defined")
    }

    #[test]
    fn multiplication() {
        let value = interprete("3 * 2 + 1\n");

        assert_eq!(value.unwrap(), Value::Float(7.0));
    }

    #[test]
    fn division() {
        let value = interprete("3 / 2 + 1\n");

        assert_eq!(value.unwrap(), Value::Float(2.5));
    }

    #[test]
    fn arithmetic_precedence() {
        let value = interprete("3 + 5 / 2 * 3 + 1\n");

        assert_eq!(value.unwrap(), Value::Float(11.5));
    }

    #[test]
    fn grouping() {
        let value = interprete("(12 + 4) * (10 - 8)\n");

        assert_eq!(value.unwrap(), Value::Float(32.0));
    }

    #[test]
    fn nested_groups() {
        let value = interprete("(1 * ((1) + 2)) * (((1 - 1) * 100) + 2)\n");

        assert_eq!(value.unwrap(), Value::Float(6.0));
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

        assert_eq!(value.unwrap_err().what, "Unexpected EOF");
    }

    #[test]
    fn missing_closing_paren_at_eof() {
        let value = interprete("(1 + 1");

        assert_eq!(
            value.unwrap_err().what,
            "Missing closing parenthesis, unexpected EOF"
        );
    }

    #[test]
    fn define_variable() {
        let mut env = Environment::new();

        env.define("foo", Value::Float(2.3));

        assert_eq!(env.get("foo"), Some(&Value::Float(2.3)));
    }

    #[test]
    fn declare_float_variable() {
        let value = interprete("let foo = 310.5\n");

        assert_eq!(value.unwrap(), Value::Float(310.5));
    }

    #[test]
    fn declare_variable_with_other_variable() {
        let value = interprete("let foo = 3\nlet bar = foo * foo - 1\n");

        assert_eq!(value.unwrap(), Value::Float(8.0));
    }

    #[test]
    fn declare_float_variable_with_complex_expression() {
        let value = interprete("let foo = 1.0 + (310.5 + 0.5) * 2\n");

        assert_eq!(value.unwrap(), Value::Float(623.0));
    }

    #[test]
    fn invalid_variable_declaration_no_identifier() {
        let value = interprete("let 3.14\n");

        assert_eq!(value.unwrap_err().what, "Expected identifier");
    }

    #[test]
    fn invalid_variable_declaration_no_equal_sign() {
        let value = interprete("let foo\n");

        assert_eq!(
            value.unwrap_err().what,
            "Expected equal sign after identifier"
        );
    }

    #[test]
    fn invalid_variable_declaration_no_newline() {
        let value = interprete("let foo = 123");

        assert_eq!(
            value.unwrap_err().what,
            "Expected newline after declaration"
        );
    }

    #[test]
    fn variable_already_defined() {
        let value = interprete("let foo = 123\nlet foo = 321\n");

        assert_eq!(value.unwrap_err().what, "Variable foo is already defined");
    }

    #[test]
    fn call_function() {
        let mut env = Environment::new();
        env.define("foo", Value::Callable(|_args| Value::Float(928.0)));

        let value = interprete_with_env("foo()\n", &mut env);

        assert_eq!(value.unwrap(), Value::Float(928.0));
    }

    #[test]
    fn call_function_with_one_argument() {
        let mut env = Environment::new();
        env.define("foo", Value::Callable(|args| *args.first().unwrap()));

        let value = interprete_with_env("foo(5)\n", &mut env);

        assert_eq!(value.unwrap(), Value::Float(5.0));
    }

    #[test]
    fn call_function_with_multiple_arguments() {
        let mut env = Environment::new();
        env.define("foo", Value::Callable(|args| add_floats(args)));

        let value = interprete_with_env("foo(5 + 3, (1 + 1) * 3)\n", &mut env);

        assert_eq!(value.unwrap(), Value::Float(14.0));
    }

    #[test]
    fn call_function_with_function_call_as_argument() {
        let mut env = Environment::new();

        let callable = Value::Callable(|args| add_floats(args));
        env.define("foo", callable);
        env.define("bar", callable);

        let value = interprete_with_env("foo(bar(2, 3), bar(6, 5))\n", &mut env);

        assert_eq!(value.unwrap(), Value::Float(16.0));
    }

    #[test]
    fn call_function_with_variable_as_argument() {
        let mut env = Environment::new();

        let callable = Value::Callable(|args| add_floats(args));
        env.define("foo", callable);
        env.define("bar", Value::Float(12.0));
        env.define("baz", Value::Float(8.0));

        let value = interprete_with_env("foo(bar, baz / 2 + 1)\n", &mut env);

        assert_eq!(value.unwrap(), Value::Float(17.0));
    }
}
