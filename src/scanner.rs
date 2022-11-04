#[derive(Debug, PartialEq)]
enum Token<'a> {
    Equal,
    Plus,
    Identifier(&'a str),
    Number(&'a str),
}

struct Scanner<'a> {
    it: std::str::Chars<'a>,
}

impl<'a> Scanner<'a> {
    fn skip<F>(&mut self, f: F)
    where
        F: Fn(char) -> bool,
    {
        while self.it.clone().next().map_or(false, &f) {
            self.it.next();
        }
    }

    fn consume_number(&mut self) -> Token<'a> {
        let s = self.it.as_str();
        self.skip(|c| is_number(c));
        Token::Number(&s[..s.len() - self.it.as_str().len()])
    }

    fn consume_identifier(&mut self) -> Token<'a> {
        let s = self.it.as_str();
        self.skip(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_');
        Token::Identifier(&s[..s.len() - self.it.as_str().len()])
    }
}

impl<'a> Iterator for Scanner<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.skip(|c| c.is_ascii_whitespace());
        if let Some(c) = self.it.clone().next() {
            if c.is_ascii_digit() {
                Some(self.consume_number())
            } else if c.is_ascii_alphabetic() {
                Some(self.consume_identifier())
            } else if c == '=' {
                self.it.next();
                Some(Token::Equal)
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

        assert_eq!(s.next(), Some(Token::Identifier("abc")));
        assert_eq!(s.next(), Some(Token::Identifier("f0o")));
        assert_eq!(s.next(), Some(Token::Number("123")));
    }

    #[test]
    fn scan_number() {
        let mut s = Scanner { it: "44 12.3".chars() };

        assert_eq!(s.next(), Some(Token::Number("44")));
        assert_eq!(s.next(), Some(Token::Number("12.3")));
    }

    #[test]
    fn scan_assign() {
        let mut s = Scanner {
            it: "my_var = 4.5 + 1.5".chars(),
        };

        assert_eq!(s.next(), Some(Token::Identifier("my_var")));
        assert_eq!(s.next(), Some(Token::Equal));
        assert_eq!(s.next(), Some(Token::Number("4.5")));
        assert_eq!(s.next(), Some(Token::Plus));
        assert_eq!(s.next(), Some(Token::Number("1.5")));
    }
}
