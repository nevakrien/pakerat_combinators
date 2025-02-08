use std::rc::Rc;
use crate::core::fmt::Display;
use proc_macro2::{Delimiter, Ident, Literal, Punct, Span, TokenTree};
use std::cmp::Ordering;
use std::fmt;
use std::fmt::Formatter;
use syn::buffer::TokenBuffer;

use proc_macro2::extra::DelimSpan;
use syn::buffer::Cursor;

pub fn get_start_del(del: Delimiter) -> &'static str {
    match del {
        Delimiter::Parenthesis => "(",
        Delimiter::Bracket => "[",
        Delimiter::Brace => "{",
        Delimiter::None => "<empty delim (likely bug)>",
    }
}

pub fn get_end_del(del: Delimiter) -> &'static str {
    match del {
        Delimiter::Parenthesis => ")",
        Delimiter::Bracket => "]",
        Delimiter::Brace => "}",
        Delimiter::None => "<EOF>",
    }
}

/// Tracks delimiter information for error reporting.
#[derive(Clone, Copy, Debug)]
pub struct DelMark {
    del: Delimiter,
    span: Span,
}

impl DelMark {
    #[inline(always)]
    pub fn del(&self) -> Delimiter {
        self.del
    }
    #[inline(always)]
    pub fn span(&self) -> Span {
        self.span
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Found {
    Spot(Span),
    End(DelMark),
    ///this span is the best guess we can manage. it is the element before EOF or call_site
    EOF(Span),
    Start(DelMark),
}

impl Found {
    pub fn start_of(spot: Input) -> Self {
        if spot.eof() {
            return spot
                .block_end
                .map(Found::End)
                .unwrap_or_else(|| Found::EOF(spot.span()));
        }
        match spot.any_group() {
            Some((_, del, del_span, _)) => Found::Start(DelMark {
                del,
                span: del_span.open(),
            }),
            None => Found::Spot(spot.span()),
        }
    }

    ///end of the current cursor not the entire input
    pub fn end_of(spot: Input) -> Self {
        if spot.eof() {
            return spot
                .block_end
                .map(Found::End)
                .unwrap_or_else(|| Found::EOF(spot.span()));
        }
        match spot.any_group() {
            Some((_, del, del_span, _)) => Found::Start(DelMark {
                del,
                span: del_span.close(),
            }),
            None => Found::Spot(spot.span()),
        }
    }

    ///Retrieves the span associated with this `Found` variant. (for EOF we return the elemnt before)
    pub fn span(&self) -> Span {
        match self {
            Found::Spot(span) | Found::EOF(span) => *span,
            Found::Start(del_mark) | Found::End(del_mark) => del_mark.span(),
        }
    }
}

impl fmt::Display for Found {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Found::Spot(span) => match span.source_text() {
                Some(s) => write!(f, "{}", s),
                None => write!(f, "<missing source : {:?}>", span),
            },
            Found::Start(del_mark) => write!(f, "{}", get_start_del(del_mark.del())),
            Found::End(del_mark) => write!(f, "{}", get_end_del(del_mark.del())),
            Found::EOF(_span) => write!(f, "EOF"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Expected {
    OwnedText(Rc<str>),
    Text(&'static str),
    Punct(char),
    Spot(Span),
    End(Delimiter),
    Start(Delimiter),
}

impl Expected {
    pub fn start_of(spot: Input<'_>) -> Self {
        match spot.any_group() {
            Some((_, del, _, _)) => Expected::Start(del),
            None => Expected::Spot(spot.span()),
        }
    }
}

impl fmt::Display for Expected {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expected::Text(s) => write!(f, "{}", s),
            Expected::OwnedText(s) => write!(f, "{}", s),
            Expected::Spot(span) => match span.source_text() {
                Some(s) => write!(f, "\"{}\"", s),
                None => write!(f, "<missing source : {:?}>", span),
            },
            Expected::Start(del) => write!(f, "\"{}\"", get_start_del(*del)),
            Expected::End(del) => write!(f, "\"{}\"", get_end_del(*del)),
            Expected::Punct(c) => write!(f, "\"{}\"",c),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Mismatch {
    pub actual: Found,
    pub expected: Expected,
}

impl fmt::Display for Mismatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Expected {} but found \"{}\"",
            self.expected, self.actual
        )
    }
}

impl std::error::Error for Mismatch {}

impl From<Mismatch> for syn::Error {
    fn from(mismatch: Mismatch) -> Self {
        let span = mismatch.actual.span(); // Use the actual's span
        let msg = mismatch.to_string(); // Leverage Display implementation
        syn::Error::new(span, msg)
    }
}

#[derive(Clone, Debug)]
pub enum ParseError {
    Empty,
    Simple(Mismatch),
    Message(Span, &'static str),
    OwnedMessage(Span, Rc<str>),
    Syn(Rc<syn::Error>),
}

impl crate::combinator::Parsable for ParseError{

type Output<'a> = ParseError;
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        use ParseError::*;
        match self {
            Empty => write!(f, "<no debug info for this error>"),
            Simple(x) => x.fmt(f),
            ParseError::Message(_, message) => message.fmt(f),
            ParseError::OwnedMessage(_, message) => message.fmt(f),
            ParseError::Syn(x) => x.fmt(f),
        }
    }
}

impl std::error::Error for ParseError {}

impl From<ParseError> for syn::Error {
    fn from(err: ParseError) -> Self {
        match err {
            ParseError::Empty => {
                syn::Error::new(Span::call_site(), "<no debug info for this error>")
            }
            ParseError::Simple(mismatch) => mismatch.into(), // Uses Mismatch's Into<syn::Error>
            ParseError::Message(span, message) => syn::Error::new(span, message),
            ParseError::OwnedMessage(span, message) => syn::Error::new(span, message),
            ParseError::Syn(rc) => (*rc).clone(), // Already a syn::Error
        }
    }
}

impl From<Mismatch> for ParseError {
    fn from(m: Mismatch) -> Self {
        ParseError::Simple(m)
    }
}

impl From<syn::Error> for ParseError {
    fn from(e: syn::Error) -> Self {
        ParseError::Syn(e.into())
    }
}

/// A wrapper around `syn::Cursor` that tracks some metadata
#[derive(Clone, Copy)]
pub struct Input<'a> {
    cursor: Cursor<'a>,
    end: Cursor<'a>,
    block_end: Option<DelMark>,
}

impl PartialEq for Input<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.cursor == other.cursor && self.end == other.end
    }
}

impl PartialOrd for Input<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.cursor.partial_cmp(&other.cursor)
    }
}

impl<'a> From<Input<'a>> for Cursor<'a> {
    fn from(x: Input<'a>) -> Self {
        x.cursor
    }
}

impl<'a> Input<'a> {
    #[inline]
    fn check_end(&self) -> bool{
        self.cursor==self.end
    }
    /// Creates a new `Input` from a `TokenBuffer`, ensuring spans are valid.
    pub fn new(buffer: &'a TokenBuffer) -> Self {
        Self {
            cursor: buffer.begin(),
            end: Cursor::empty(),
            block_end: None, // No delimiter context initially.
        }
    }

    /// Returns an `Input` that references an empty token stream.
    pub fn empty() -> Self {
        Self {
            cursor: Cursor::empty(),
            end: Cursor::empty(),

            block_end: None,
        }
    }

    /// Truncates this input to not go past `spot` so `[input,spot,rest] -> [input]`
    pub fn truncate(self,spot:impl Into<Cursor<'a>>) -> Self{
        let new_end = spot.into();
        Self {
            cursor: self.cursor,
            end: if new_end < self.cursor { self.cursor } else { new_end },
            block_end: self.block_end,
        }
        
    }

    /// Returns `true` if the `Input` has reached the end of the token stream.
    pub fn eof(self) -> bool {
        self.check_end()||self.cursor.eof()
    }

    /// If the `Input` points at an identifier, returns it and an `Input` at the next token.
    pub fn ident(self) -> Option<(Ident, Self)> {
        if self.check_end(){
            return None;
        }
        let (ident, next_cursor) = self.cursor.ident()?;
        Some((
            ident,
            Self {
                cursor: next_cursor,
                end:self.end,
                block_end: self.block_end,
            },
        ))
    }

    /// If the `Input` points at a punctuation token, returns it and an `Input` at the next token.
    pub fn punct(self) -> Option<(Punct, Self)> {
        if self.check_end(){
            return None;
        }
        let (punct, next_cursor) = self.cursor.punct()?;
        Some((
            punct,
            Self {
                cursor: next_cursor,
                end:self.end,
                block_end: self.block_end,
            },
        ))
    }

    /// If the `Input` points at a literal, returns it and an `Input` at the next token.
    pub fn literal(self) -> Option<(Literal, Self)> {
        if self.check_end(){
            return None;
        }
        let (literal, next_cursor) = self.cursor.literal()?;
        Some((
            literal,
            Self {
                cursor: next_cursor,
                end:self.end,
                block_end: self.block_end,
            },
        ))
    }

    /// If the `Input` points at a lifetime, returns it and an `Input` at the next token.
    pub fn lifetime(self) -> Option<(syn::Lifetime, Self)> {
        let (lifetime, next_cursor) = self.cursor.lifetime()?;
        
        //lifetime is actually 2 tokens so its trickier
        if next_cursor>self.end{
            return None;
        }

        Some((
            lifetime,
            Self {
                cursor: next_cursor,
                end:self.end,
                block_end: self.block_end,
            },
        ))
    }

    /// If the `Input` points at a group with the given delimiter, returns:
    /// - A new `Input` for inside the group,
    /// - The `DelimSpan` tracking the group delimiters,
    /// - An `Input` pointing at the next token after the group.
    pub fn group(self, delim: Delimiter) -> Option<(Self, DelimSpan, Self)> {
        if self.check_end(){
            return None;
        }
        let (inner_cursor, delim_span, next_cursor) = self.cursor.group(delim)?;
        Some((
            Self {
                cursor: inner_cursor,
                end:self.end,

                block_end: Some(DelMark {
                    del: delim,
                    span: delim_span.close(),
                }),
            },
            delim_span,
            Self {
                cursor: next_cursor,
                end:self.end,

                block_end: self.block_end,
            },
        ))
    }

    /// If the `Input` points at any group, returns:
    /// - A new `Input` for inside the group,
    /// - The delimiter type of the group,
    /// - The `DelimSpan` tracking the group delimiters,
    /// - An `Input` pointing at the next token after the group.
    pub fn any_group(self) -> Option<(Self, Delimiter, DelimSpan, Self)> {
        if self.check_end(){
            return None;
        }
        let (inner_cursor, delim, delim_span, next_cursor) = self.cursor.any_group()?;
        Some((
            Self {
                cursor: inner_cursor,
                end:self.end,

                block_end: Some(DelMark {
                    del: delim,
                    span: delim_span.close(),
                }),
            },
            delim,
            delim_span,
            Self {
                cursor: next_cursor,
                end:self.end,

                block_end: self.block_end,
            },
        ))
    }

    /// If the `Input` points at a `TokenTree`, returns it along with an `Input` pointing at the next token.
    ///
    /// If the token is a group, updates `block_end` with its closing delimiter information.
    pub fn token_tree(self) -> Option<(TokenTree, Self)> {
        if self.check_end(){
            return None;
        }
        let (tree, next_cursor) = self.cursor.token_tree()?;
        let new_block_end = match &tree {
            TokenTree::Group(group) => Some(DelMark {
                del: group.delimiter(),
                span: group.span_close(),
            }),
            _ => self.block_end,
        };
        Some((
            tree,
            Self {
                cursor: next_cursor,
                end:self.end,

                block_end: new_block_end,
            },
        ))
    }

    /// Returns the `Span` of the current token, or `Span::call_site()` if the `Input` is at EOF.
    #[inline]
    pub fn span(self) -> Span {
        self.cursor.span()
    }

    /// Returns the internal `Cursor` for direct access.
    /// note that this ignores the end set for thi Input
    /// cursors from this method can go as far as they want
    #[inline(always)]
    pub fn cursor(&self) -> Cursor<'a> {
        self.cursor
    }

    /// Returns the tracked closing delimiter, if any.
    #[inline(always)]
    pub fn block_end(&self) -> Option<DelMark> {
        self.block_end
    }

    pub fn end_span(self) -> Span {
        match self.cursor.any_group() {
            None => self.cursor.span(),
            Some((_, _, delim_span, _)) => delim_span.close(),
        }
    }
}
