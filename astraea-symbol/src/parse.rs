use std::fmt::Display;
use std::iter::Peekable;
use std::str::CharIndices;

#[derive(Debug)]
pub struct ParseError {
    pub message: String,
}

impl ParseError {
    pub fn new<S: Into<String>>(message: S) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

pub struct Token<'a> {
    pub value: &'a str,
    pub offset: usize,
}

pub struct TokenStream<'a> {
    source: &'a str,
    chars: Peekable<CharIndices<'a>>,
}

impl<'a> TokenStream<'a> {
    pub fn new(source: &'a str) -> Self {
        Self {
            source,
            chars: source.char_indices().peekable(),
        }
    }
}

impl<'a> Iterator for TokenStream<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let &(start, first_char) = self.chars.peek()?;

            if first_char.is_whitespace() {
                self.chars.next();
                continue;
            }

            let mut end = start + first_char.len_utf8();
            self.chars.next();

            while let Some(&(offset, char)) = self.chars.peek() {
                if char.is_whitespace() {
                    break;
                }
                end = offset + char.len_utf8();
                self.chars.next();
            }

            return Some(Token {
                value: &self.source[start..end],
                offset: start,
            });
        }
    }
}
