#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    Asterisc,
    Equal,
    Minus,
    Plus,
    Identifier(String),
    Number(String),
}

#[derive(Clone)]
pub struct Scanner<'a> {
    it: std::str::Chars<'a>,
}

impl<'a> Scanner<'a> {
    pub fn new(input: &'a str) -> Self {
        Scanner { it: input.chars() }
    }

    fn skip<F>(&mut self, f: F)
    where
        F: Fn(char) -> bool,
    {
        while self.it.clone().next().map_or(false, &f) {
            self.it.next();
        }
    }

    fn consume_number(&mut self) -> Token {
        let s = self.it.as_str();
        self.skip(|c| is_number(c));
        Token::Number(String::from(&s[..s.len() - self.it.as_str().len()]))
    }

    fn consume_identifier(&mut self) -> Token {
        let s = self.it.as_str();
        self.skip(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_');
        Token::Identifier(String::from(&s[..s.len() - self.it.as_str().len()]))
    }
}

impl<'a> Iterator for Scanner<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.skip(|c| c.is_ascii_whitespace());
        if let Some(c) = self.it.clone().next() {
            if c.is_ascii_digit() {
                Some(self.consume_number())
            } else if c.is_ascii_alphabetic() {
                Some(self.consume_identifier())
            } else if c == '*' {
                self.it.next();
                Some(Token::Asterisc)
            } else if c == '=' {
                self.it.next();
                Some(Token::Equal)
            } else if c == '-' {
                self.it.next();
                Some(Token::Minus)
            } else if c == '+' {
                self.it.next();
                Some(Token::Plus)
            } else {
                None
            }
        } else {
            None
        }
    }
}

fn is_number(c: char) -> bool {
    c.is_ascii_digit() || c == '.'
}

#[cfg(test)]
mod tests {
    use super::Scanner;
    use super::Token;

    #[test]
    fn scan_identifier() {
        let mut s = Scanner {
            it: "abc f0o 123".chars(),
        };

        assert_eq!(s.next(), Some(Token::Identifier(String::from("abc"))));
        assert_eq!(s.next(), Some(Token::Identifier(String::from("f0o"))));
        assert_eq!(s.next(), Some(Token::Number(String::from("123"))));
    }

    #[test]
    fn scan_number() {
        let mut s = Scanner {
            it: "44 -12.3".chars(),
        };

        assert_eq!(s.next(), Some(Token::Number(String::from("44"))));
        assert_eq!(s.next(), Some(Token::Minus));
        assert_eq!(s.next(), Some(Token::Number(String::from("12.3"))));
    }

    #[test]
    fn scan_assign() {
        let mut s = Scanner {
            it: "my_var = 4.5 + 1.5 - 1.0 * 2.0".chars(),
        };

        assert_eq!(s.next(), Some(Token::Identifier(String::from("my_var"))));
        assert_eq!(s.next(), Some(Token::Equal));
        assert_eq!(s.next(), Some(Token::Number(String::from("4.5"))));
        assert_eq!(s.next(), Some(Token::Plus));
        assert_eq!(s.next(), Some(Token::Number(String::from("1.5"))));
        assert_eq!(s.next(), Some(Token::Minus));
        assert_eq!(s.next(), Some(Token::Number(String::from("1.0"))));
        assert_eq!(s.next(), Some(Token::Asterisc));
        assert_eq!(s.next(), Some(Token::Number(String::from("2.0"))));
    }
}
