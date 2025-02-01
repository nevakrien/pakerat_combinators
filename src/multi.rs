use crate::cache::FlexibleCache;
use crate::combinator::{Pakerat,Combinator};
use crate::cache::Cache;
use crate::combinator::PakeratError;
use syn::buffer::Cursor;

use std::marker::PhantomData;

///this struct is mainly used for delimiter with delimiters as a way to parse "{something}"
///
///it can also be used to remove a prefix but thats about it
///
/// # Example Usage
/// ```rust
/// use proc_macro2::Delimiter;
/// use pakerat_combinators::basic_parsers::{DelParser, IdentParser};
/// use pakerat_combinators::multi::{Wrapped};
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::cache::BasicCache;
/// use syn::buffer::TokenBuffer;
/// use std::marker::PhantomData;
/// 
/// let tokens = "{ my_var }".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
///
///
/// let my_parser = Wrapped {
///     wrapper: DelParser(Delimiter::Brace),
///     inner: IdentParser,
///     _phantom: PhantomData,
/// };
///
/// let mut cache  = BasicCache::<0>::new();
/// let (_, parsed_ident) = my_parser.parse(buffer.begin(), &mut cache).unwrap();
/// assert_eq!(parsed_ident.to_string(), "my_var");
/// ```
pub struct Wrapped<'b, INNER,WRAPPER,T =(), O=T, C = FlexibleCache<'b,T>>
where
    INNER: Combinator<'b, T, O,C>,
    WRAPPER: Combinator<'b, Cursor<'b>, O,C>,
    O: Clone, 
    C: Cache<'b, O>
{	
	///finds the start for the inside parser
    pub wrapper: WRAPPER,
    ///main parser that returns the final output
    pub inner: INNER,
    ///used so we can have generics
    pub _phantom: PhantomData<(Cursor<'b>, T, O,C)>,
}


impl<'a, INNER, WRAPPER, T, O, C> Combinator<'a, T, O,C> for Wrapped<'a, INNER, WRAPPER, T, O, C>
where
    WRAPPER: Combinator<'a, Cursor<'a>, O,C>,
    INNER: Combinator<'a, T, O,C>,
    O: Clone, 
    C: Cache<'a, O>
{
    fn parse(
        &self,
        input: Cursor<'a>,
        cache: &mut C,
    ) -> Pakerat<(Cursor<'a>, T)> {
        let (next, inner_result) = self.wrapper.parse(input, cache)?;
        let (remaining, final_result) = self.inner.parse(inner_result, cache)?;

        if !remaining.eof() {
        	return Err(PakeratError::Regular(syn::Error::new(
        		remaining.span(),"expected one of '})]' or EOF"
        		)))
        }

        Ok((next, final_result))
    }

    fn parse_ignore(
        &self,
        input: Cursor<'a>,
        cache: &mut C,
    ) -> Pakerat<Cursor<'a>> {
        let (next, inner_result) = self.wrapper.parse(input, cache)?;
        let remaining= self.inner.parse_ignore(inner_result, cache)?;

        if !remaining.eof() {
            return Err(PakeratError::Regular(syn::Error::new(
                remaining.span(),"expected one of '})]' or EOF"
                )))
        }

        Ok(next)
    }
}

/// This struct attempts to parse an optional occurrence of an inner parser.
/// If the inner parser fails with a `Regular` error, `Maybe` will return `None` instead of failing.
/// If the inner parser fails with a `Recursive` error, the error is propagated.
///
/// # Example Usage
/// ```rust
/// use pakerat_combinators::multi::Maybe;
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::cache::BasicCache;
/// use syn::buffer::TokenBuffer;
/// use std::marker::PhantomData;
///
/// let tokens = "optional_var".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
///
/// let my_parser = Maybe::new(IdentParser);
///
/// let mut cache = BasicCache::<0>::new();
/// let (_, parsed_ident) = my_parser.parse(buffer.begin(), &mut cache).unwrap();
/// assert_eq!(parsed_ident.unwrap().to_string(), "optional_var");
/// ```
//
pub struct Maybe<'b, INNER,T =(), O=T, C = FlexibleCache<'b,T>>
where
    INNER: Combinator<'b, T, O,C>,
    O: Clone,
    C: Cache<'b, O>
{   
    pub inner: INNER,
    ///used so we can have generics
    pub _phantom: PhantomData<(Cursor<'b>, T, O,C)>,
}

impl<'a, INNER,T, O, C> Combinator<'a, Option<T>, O,C> for Maybe<'a, INNER,T, O, C> 
    where O: Clone, 
    C: Cache<'a, O>,
    INNER: Combinator<'a, T, O,C>,
{

fn parse(&self, input: Cursor<'a>, cache: &mut C) -> Pakerat<(Cursor<'a>, Option<T>)> { 
    match self.inner.parse(input,cache){
        Ok((cursor,x)) => Ok((cursor,Some(x))),
        Err(e) => match e {
            PakeratError::Regular(_) => Ok((input,None)),
            PakeratError::Recursive(_) => Err(e)
        }
    }
}
fn parse_ignore(&self, input: Cursor<'a>, cache: &mut C) -> Pakerat<Cursor<'a>> { 
    match self.inner.parse_ignore(input,cache){
        Ok(cursor) => Ok(cursor),
        Err(e) => match e {
            PakeratError::Regular(_) => Ok(input),
            PakeratError::Recursive(_) => Err(e)
        }
    }
}
}

impl<'b, INNER,T, O, C> Maybe<'b, INNER,T, O, C> 
where
    INNER: Combinator<'b, T, O,C>,
    O: Clone, 
    C: Cache<'b, O>,
{
    
    pub fn new(inner:INNER) -> Self{
        Maybe{
            inner,
            _phantom:PhantomData
        }
    }
}

/// This struct parses zero or more occurrences of an inner parser.
/// It keeps collecting results until the inner parser fails with a `Regular` error.
/// If the inner parser fails with a `Recursive` error, the error is propagated.
///
/// # Example Usage
/// ```rust
/// use pakerat_combinators::multi::Many0;
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::cache::BasicCache;
/// use syn::buffer::TokenBuffer;
/// use std::marker::PhantomData;
///
/// let tokens = "var1 var2 var3".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
///
/// let my_parser = Many0::new(IdentParser);
///
/// let mut cache = BasicCache::<0>::new();
/// let (_, parsed_idents) = my_parser.parse(buffer.begin(), &mut cache).unwrap();
/// assert_eq!(parsed_idents.len(), 3);
/// ```
pub struct Many0<'b, INNER,T =(), O=T, C = FlexibleCache<'b,T>>
where
    INNER: Combinator<'b, T, O,C>,
    O: Clone, 
    C: Cache<'b, O>
{   
    pub inner: INNER,
    ///used so we can have generics
    pub _phantom: PhantomData<(Cursor<'b>, T, O,C)>,
}

impl<'a, INNER,T, O, C> Combinator<'a, Vec<T>, O,C> for Many0<'a, INNER,T, O, C> 
    where O: Clone, 
    C: Cache<'a, O>,
    INNER: Combinator<'a, T, O,C>,
{

fn parse(&self, mut input: Cursor<'a>, cache: &mut C) -> Pakerat<(Cursor<'a>, Vec<T>)> { 
    let mut vec = Vec::new();
    loop{
        match self.inner.parse(input,cache){
            Ok((cursor,x)) => {
                input=cursor;
                vec.push(x);
            },
            Err(e) => return match e{
                PakeratError::Regular(_)=> Ok((input,vec)),
                PakeratError::Recursive(_)=>Err(e)
            }
        }
    }
}
fn parse_ignore(&self, mut input: Cursor<'a>, cache: &mut C) -> Pakerat<Cursor<'a>> { 
    loop{
        match self.inner.parse(input,cache){
            Ok((cursor,_x)) => {
                input=cursor;
            },
            Err(e) => return match e{
                PakeratError::Regular(_)=> Ok(input),
                PakeratError::Recursive(_)=>Err(e)
            }
        }
    }
}
}

impl<'b, INNER,T, O, C> Many0<'b, INNER,T, O, C> 
where
    INNER: Combinator<'b, T, O,C>,
    O: Clone, 
    C: Cache<'b, O>,
{
    
    pub fn new(inner:INNER) -> Self{
        Many0{
            inner,
            _phantom:PhantomData
        }
    }
}


/// This struct parses one or more occurrences of an inner parser.
/// It behaves like `Many0` but ensures at least one successful parse before stopping.
/// If the first attempt fails, `Many1` returns an error.
///
/// # Example Usage
/// ```rust
/// use pakerat_combinators::multi::Many1;
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::cache::BasicCache;
/// use syn::buffer::TokenBuffer;
/// use std::marker::PhantomData;
///
/// let tokens = "var1 var2 var3".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
///
/// let my_parser = Many1::new(IdentParser);
///
/// let mut cache = BasicCache::<0>::new();
/// let (_, parsed_idents) = my_parser.parse(buffer.begin(), &mut cache).unwrap();
/// assert_eq!(parsed_idents.len(), 3);
/// ```
pub struct Many1<'b, INNER,T =(), O=T, C = FlexibleCache<'b>>
where
    INNER: Combinator<'b, T, O,C>,
    O: Clone, 
    C: Cache<'b, O>
{   
    pub inner: INNER,
    ///used so we can have generics
    pub _phantom: PhantomData<(Cursor<'b>, T, O,C)>,
}

impl<'a, INNER,T, O, C> Combinator<'a, Vec<T>, O,C> for Many1<'a, INNER,T, O, C> 
    where O: Clone, 
    C: Cache<'a, O>,
    INNER: Combinator<'a, T, O,C>,
{

fn parse(&self, input: Cursor<'a>, cache: &mut C) -> Pakerat<(Cursor<'a>, Vec<T>)> { 
    let (mut input,first) = self.inner.parse(input,cache)?;
    let mut vec = vec![first];
    loop{
        match self.inner.parse(input,cache){
            Ok((cursor,x)) => {
                input=cursor;
                vec.push(x);
            },
            Err(e) => return match e{
                PakeratError::Regular(_)=> Ok((input,vec)),
                PakeratError::Recursive(_)=>Err(e)
            }
        }
    }
}
fn parse_ignore(&self, input: Cursor<'a>, cache: &mut C) -> Pakerat<Cursor<'a>> { 
    let (mut input,_first) = self.inner.parse(input,cache)?;
    loop{
        match self.inner.parse(input,cache){
            Ok((cursor,_x)) => {
                input=cursor;
            },
            Err(e) => return match e{
                PakeratError::Regular(_)=> Ok(input),
                PakeratError::Recursive(_)=>Err(e)
            }
        }
    }
}
}

impl<'b, INNER,T, O, C> Many1<'b, INNER,T, O, C> 
where
    INNER: Combinator<'b, T, O,C>,
    O: Clone, 
    C: Cache<'b, O>,
{
    
    pub fn new(inner:INNER) -> Self{
        Many1{
            inner,
            _phantom:PhantomData
        }
    }
}

/// This struct parses zero or more occurrences of an inner parser.
/// It keeps collecting results until the inner parser fails with a `Regular` error.
/// If the inner parser fails with a `Recursive` error, the error is propagated.
///
/// # Example Usage
/// ```rust
/// use pakerat_combinators::multi::Ignore;
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::cache::BasicCache;
/// use syn::buffer::TokenBuffer;
/// use std::marker::PhantomData;
///
/// let tokens = "optional_var".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
///
/// let my_parser = Ignore::new(IdentParser);
///
/// let mut cache = BasicCache::<0>::new();
/// let (_cursor, ()) = my_parser.parse(buffer.begin(), &mut cache).unwrap();
/// ```
pub struct Ignore<'b, INNER,T =(), O=T, C = FlexibleCache<'b>>
where
    INNER: Combinator<'b, T, O,C>,
    O: Clone, 
    C: Cache<'b, O>
{   
    pub inner: INNER,
    ///used so we can have generics
    pub _phantom: PhantomData<(Cursor<'b>, T, O,C)>,
}

impl<'a, INNER,T, O, C> Combinator<'a, (), O,C> for Ignore<'a, INNER,T, O, C> 
    where O: Clone, 
    C: Cache<'a, O>,
    INNER: Combinator<'a, T, O,C>,
{

fn parse(&self, input: Cursor<'a>, cache: &mut C) -> Pakerat<(Cursor<'a>, ())> { 
    let c = self.inner.parse_ignore(input,cache)?;
    Ok((c,()))
}
}

impl<'b, INNER,T, O, C> Ignore<'b, INNER,T, O, C> 
where
    INNER: Combinator<'b, T, O,C>,
    O: Clone, 
    C: Cache<'b, O>,
{
    
    pub fn new(inner:INNER) -> Self{
        Ignore{
            inner,
            _phantom:PhantomData
        }
    }
}



#[cfg(test)]
mod tests {

use proc_macro2::TokenStream;
use syn::buffer::TokenBuffer;
use super::*;
use crate::basic_parsers::LiteralParser;
use crate::basic_parsers::AnyDelParser;
use crate::basic_parsers::PunctParser;
use std::collections::HashMap;
use crate::cache::BasicCache;


    use crate::basic_parsers::DelParser;

use proc_macro2::Delimiter;

use crate::basic_parsers::IdentParser;
/// Macro to safely create a `TokenBuffer` and `Cursor` with a proper lifetime.
macro_rules! token_cursor {
    ($name:ident, $input:expr) => {
        let tokens: TokenStream = $input.parse().unwrap(); // Unwrap directly for clearer failure
        let buffer = TokenBuffer::new2(tokens); // Keep buffer alive
        let $name = buffer.begin(); // Extract cursor
    };
}

#[test]
fn test_lifetimes() {
    let parser : Maybe<'static,_>= Maybe::new(Ignore::new(Maybe::new(IdentParser)));

    {
        token_cursor!(buffer, "maybe_var");
        let mut cache = FlexibleCache::new();
        let (_, _result) = parser.parse(buffer, &mut cache).unwrap();
    }

    {
        token_cursor!(buffer, "maybe_var");
        let mut cache = FlexibleCache::new();
        let (_, _result) = parser.parse(buffer, &mut cache).unwrap();
    }
}



#[test]
fn test_maybe_parser() {
    token_cursor!(buffer, "maybe_var");
    let parser = Maybe { inner: IdentParser, _phantom: PhantomData };
    let mut cache = BasicCache::<0>::new();
    let (_, result) = parser.parse(buffer, &mut cache).unwrap();
    assert_eq!(result.unwrap().to_string(), "maybe_var");
}

#[test]
fn test_maybe_parser_none() {
    token_cursor!(buffer, "123");
    let parser = Maybe { inner: IdentParser, _phantom: PhantomData };
    let mut cache = BasicCache::<0>::new();
    let (_, result) = parser.parse(buffer, &mut cache).unwrap();
    assert!(result.is_none());
}

#[test]
fn test_many0_parser() {
    token_cursor!(buffer, "var1 var2 var3");
    let parser = Many0 { inner: IdentParser, _phantom: PhantomData };
    let mut cache = BasicCache::<0>::new();
    let (_, result) = parser.parse(buffer, &mut cache).unwrap();
    assert_eq!(result.len(), 3);
}

#[test]
fn test_many1_parser() {
    token_cursor!(buffer, "var1 var2 var3");
    let parser = Many1 { inner: IdentParser, _phantom: PhantomData };
    let mut cache = BasicCache::<0>::new();
    let (_, result) = parser.parse(buffer, &mut cache).unwrap();
    assert_eq!(result.len(), 3);
}

#[test]
fn test_many1_parser_fail() {
    token_cursor!(buffer, "");
    let parser = Many1 { inner: IdentParser, _phantom: PhantomData };
    let mut cache = BasicCache::<0>::new();
    let result = parser.parse(buffer, &mut cache);
    assert!(result.is_err());
}

#[test]
    fn test_inside_delimited_ident() {
        // Create token cursor from `{ my_var }`
        token_cursor!(buffer, "{ my_var }");

        // Combine them in Wrapped
        let inside_parser = Wrapped {
            wrapper: DelParser(Delimiter::Brace),
            inner: IdentParser,
            _phantom: PhantomData,
        };

        let mut cache: BasicCache<0> = HashMap::new();
        let result = inside_parser.parse(buffer, &mut cache);

        assert!(result.is_ok(), "Wrapped parser should successfully parse an identifier inside `{{}}`");
        let (remaining, parsed_ident) = result.unwrap();
        assert_eq!(parsed_ident.to_string(), "my_var", "Parsed identifier should be 'my_var'");
        assert!(remaining.eof(), "Remaining cursor should be empty");
    }

    #[test]
    fn test_inside_delimited_punct() {
        token_cursor!(buffer, "( + )");

        let inside_parser = Wrapped {
            wrapper: DelParser(Delimiter::Parenthesis),
            inner: PunctParser,
            _phantom: PhantomData,
        };

        let mut cache: BasicCache<0> = HashMap::new();
        let result = inside_parser.parse(buffer, &mut cache);

        assert!(result.is_ok(), "Wrapped parser should successfully parse a punctuation inside `()`");
        let (remaining, parsed_punct) = result.unwrap();
        assert_eq!(parsed_punct.as_char(), '+', "Parsed punctuation should be `+`");
        assert!(remaining.eof(), "Remaining cursor should be empty");
    }

    #[test]
    fn test_inside_any_delimiter_literal() {
        token_cursor!(buffer, "[ \"Hello\" ]");

        let inside_parser = Wrapped {
            wrapper: AnyDelParser,
            inner: LiteralParser,
            _phantom: PhantomData,
        };

        let mut cache: BasicCache<0> = HashMap::new();
        let result = inside_parser.parse(buffer, &mut cache);

        assert!(result.is_ok(), "Wrapped parser should successfully parse a literal inside any delimiter");
        let (remaining, parsed_literal) = result.unwrap();
        assert_eq!(parsed_literal.to_string(), "\"Hello\"", "Parsed literal should be '\"Hello\"'");
        assert!(remaining.eof(), "Remaining cursor should be empty");
    }

    #[test]
    fn test_inside_fail_no_delimiter() {
        token_cursor!(buffer, "my_var");

        let inside_parser = Wrapped {
            wrapper: DelParser(Delimiter::Brace),
            inner: IdentParser,
            _phantom: PhantomData,
        };

        let mut cache: BasicCache<0> = HashMap::new();
        let result = inside_parser.parse(buffer, &mut cache);

        assert!(result.is_err(), "Wrapped parser should fail when no `{{}}` is present");
    }

    #[test]
    fn test_inside_fail_wrong_inner_type() {
        token_cursor!(buffer, "{ 123 }");

        let inside_parser = Wrapped {
            wrapper: DelParser(Delimiter::Brace),
            inner: IdentParser,
            _phantom: PhantomData,
        };

        let mut cache: BasicCache<0> = HashMap::new();
        let result = inside_parser.parse(buffer, &mut cache);

        assert!(result.is_err(), "Wrapped parser should fail when `{{}}` contains a number instead of an identifier");
    }

    #[test]
    fn test_inside_fail_extra_tokens() {
        token_cursor!(buffer, "{ my_var extra }");

        let inside_parser = Wrapped {
            wrapper: DelParser(Delimiter::Brace),
            inner: IdentParser,
            _phantom: PhantomData,
        };

        let mut cache: BasicCache<0> = HashMap::new();
        let result = inside_parser.parse(buffer, &mut cache);

        assert!(result.is_err(), "Wrapped parser should fail when extra tokens exist inside `{{}}`");
    }


}
