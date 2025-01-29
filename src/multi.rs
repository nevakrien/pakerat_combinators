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
/// use syn::buffer::TokenBuffer;
/// use pakerat_combinators::basic_parsers::{DelParser, IdentParser};
/// use pakerat_combinators::multi::{Inside};
/// use pakerat_combinators::cache::BasicCache;
/// use pakerat_combinators::combinator::Combinator;
/// use std::marker::PhantomData;
/// 
/// let tokens = "{ my_var }".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
///
///
/// let my_parser = Inside {
///     outside: DelParser(Delimiter::Brace),
///     inside: IdentParser,
///     _phantom: PhantomData,
/// };
///
/// let mut cache  = BasicCache::<0>::new();
/// let (_, parsed_ident) = my_parser.parse(buffer.begin(), &mut cache).unwrap();
/// assert_eq!(parsed_ident.to_string(), "my_var");
/// ```
pub struct Inside<'b, INNER,OUT,T, K, O, C>
where
    INNER: Combinator<'b, T, syn::Error, K, O,C>,
    OUT: Combinator<'b, Cursor<'b>, syn::Error, K, O,C>,
    O: Clone, 
    C: Cache<'b, O, syn::Error, K>
{	
	///finds the start for the inside parser
    pub outside: OUT,
    ///main parser that returns the final output
    pub inside: INNER,
    ///used so we can have generics
    pub _phantom: PhantomData<(Cursor<'b>, T,K, O,C)>,
}


impl<'a, INNER, OUT, T, K, O, C> Combinator<'a, T, syn::Error, K, O,C> for Inside<'a, INNER, OUT, T, K, O, C>
where
    OUT: Combinator<'a, Cursor<'a>, syn::Error, K, O,C>,
    INNER: Combinator<'a, T, syn::Error, K, O,C>,
    O: Clone, 
    C: Cache<'a, O, syn::Error, K>
{
    fn parse(
        &self,
        input: Cursor<'a>,
        cache: &mut C,
    ) -> Pakerat<(Cursor<'a>, T)> {
        let (next, inner_result) = self.outside.parse(input, cache)?;
        let (remaining, final_result) = self.inside.parse(inner_result, cache)?;

        if !remaining.eof() {
        	return Err(PakeratError::Regular(syn::Error::new(
        		remaining.span(),"expected one of '})]' or EOF"
        		)))
        }

        Ok((next, final_result))
    }
}


#[cfg(test)]
mod tests {

use proc_macro2::TokenStream;
use syn::buffer::TokenBuffer;
use super::*;
use crate::basic_parsers::MatchParser;
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
    fn test_inside_delimited_ident() {
        // Create token cursor from `{ my_var }`
        token_cursor!(buffer, "{ my_var }");

        // Outer parser: DelParser for `{}` blocks
        let del_parser = DelParser(Delimiter::Brace);

        // Inside parser: IdentParser
        let ident_parser = IdentParser;

        // Combine them in Inside
        let inside_parser = Inside {
            outside: del_parser,
            inside: ident_parser,
            _phantom: PhantomData,
        };

        let mut cache: BasicCache<0> = HashMap::new();
        let result = inside_parser.parse(buffer, &mut cache);

        assert!(result.is_ok(), "Inside parser should successfully parse an identifier inside `{{}}`");
        let (remaining, parsed_ident) = result.unwrap();
        assert_eq!(parsed_ident.to_string(), "my_var", "Parsed identifier should be 'my_var'");
        assert!(remaining.eof(), "Remaining cursor should be empty");
    }

    #[test]
    fn test_inside_delimited_punct() {
        token_cursor!(buffer, "( + )");

        let del_parser = DelParser(Delimiter::Parenthesis);
        let punct_parser = PunctParser;

        let inside_parser = Inside {
            outside: del_parser,
            inside: punct_parser,
            _phantom: PhantomData,
        };

        let mut cache: BasicCache<0> = HashMap::new();
        let result = inside_parser.parse(buffer, &mut cache);

        assert!(result.is_ok(), "Inside parser should successfully parse a punctuation inside `()`");
        let (remaining, parsed_punct) = result.unwrap();
        assert_eq!(parsed_punct.as_char(), '+', "Parsed punctuation should be `+`");
        assert!(remaining.eof(), "Remaining cursor should be empty");
    }

    #[test]
    fn test_inside_any_delimiter_literal() {
        token_cursor!(buffer, "[ \"Hello\" ]");

        let any_del_parser = AnyDelParser;
        let literal_parser = LiteralParser;

        let inside_parser = Inside {
            outside: any_del_parser,
            inside: literal_parser,
            _phantom: PhantomData,
        };

        let mut cache: BasicCache<0> = HashMap::new();
        let result = inside_parser.parse(buffer, &mut cache);

        assert!(result.is_ok(), "Inside parser should successfully parse a literal inside any delimiter");
        let (remaining, parsed_literal) = result.unwrap();
        assert_eq!(parsed_literal.to_string(), "\"Hello\"", "Parsed literal should be '\"Hello\"'");
        assert!(remaining.eof(), "Remaining cursor should be empty");
    }

    #[test]
    fn test_inside_fail_no_delimiter() {
        token_cursor!(buffer, "my_var");

        let del_parser = DelParser(Delimiter::Brace);
        let ident_parser = IdentParser;

        let inside_parser = Inside {
            outside: del_parser,
            inside: ident_parser,
            _phantom: PhantomData,
        };

        let mut cache: BasicCache<0> = HashMap::new();
        let result = inside_parser.parse(buffer, &mut cache);

        assert!(result.is_err(), "Inside parser should fail when no `{{}}` is present");
    }

    #[test]
    fn test_inside_fail_wrong_inner_type() {
        token_cursor!(buffer, "{ 123 }");

        let del_parser = DelParser(Delimiter::Brace);
        let ident_parser = IdentParser;

        let inside_parser = Inside {
            outside: del_parser,
            inside: ident_parser,
            _phantom: PhantomData,
        };

        let mut cache: BasicCache<0> = HashMap::new();
        let result = inside_parser.parse(buffer, &mut cache);

        assert!(result.is_err(), "Inside parser should fail when `{{}}` contains a number instead of an identifier");
    }

    #[test]
    fn test_inside_fail_extra_tokens() {
        token_cursor!(buffer, "{ my_var extra }");

        let del_parser = DelParser(Delimiter::Brace);
        let ident_parser = IdentParser;

        let inside_parser = Inside {
            outside: del_parser,
            inside: ident_parser,
            _phantom: PhantomData,
        };

        let mut cache: BasicCache<0> = HashMap::new();
        let result = inside_parser.parse(buffer, &mut cache);

        assert!(result.is_err(), "Inside parser should fail when extra tokens exist inside `{{}}`");
    }

    #[test]
    fn test_inside_match_parser() {
        token_cursor!(buffer, "let x = 42; let y = 10;");

        let start = buffer;
        let mut cursor = buffer;

        for _ in 0..3 {
            if let Some((_, next_cursor)) = cursor.token_tree() {
                cursor = next_cursor;
            } else {
                panic!("Failed to advance cursor within the same buffer.");
            }
        }

        let end = cursor;

        let parser = MatchParser { start, end };

        let mut cache: BasicCache<0> = HashMap::new();
        let (remaining, _) = parser.parse(buffer, &mut cache).unwrap();

        assert!(
            remaining == end,
            "Expected the remaining cursor to be at `end`, but it was somewhere else."
        );
    }
}
