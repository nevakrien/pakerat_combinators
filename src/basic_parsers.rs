use syn::__private::ToTokens;
use syn::parse::ParseStream;
use syn::LitInt;
use syn::parse::Parse;
use syn::Lifetime;
use proc_macro2::Literal;
use proc_macro2::Ident;
use proc_macro2::Punct;
use std::fmt;
use crate::combinator::PakeratError;
use crate::combinator::DumbyError;
use crate::combinator::Combinator;
use crate::cache::Cache;
use crate::combinator::Pakerat;
use proc_macro2::extra::DelimSpan;
use proc_macro2::Span;
use proc_macro2::TokenTree;
use proc_macro2::Delimiter;
use syn::buffer::Cursor;

pub struct DelMark{
	pub del:Delimiter,
	pub span:Span
}

pub enum Found<'a> {
	Spot(Cursor<'a>),
	End(DelMark),
	Start(DelMark),
}

impl<'a> Found<'a> {
	pub fn start_of(spot:Cursor<'a>) -> Self{
		match spot.any_group(){
			Some((_,del,del_span,_)) => Found::Start(DelMark{del,span:del_span.open()}),
			None => Found::Spot(spot)
		}
	}

	/// Retrieves the span associated with this `Found` variant.
    fn span(&self) -> Span {
        match self {
            Found::Spot(cursor) => cursor.span(),
            Found::Start(del_mark) | Found::End(del_mark) => del_mark.span,
        }
    }
}

impl fmt::Display for Found<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Found::Spot(cursor) => match cursor.span().source_text() {
            	Some(s) => write!(f, "{}",s),
            	None => write!(f, "<missing source : {:?}>",cursor.span()),
            }
            Found::Start(del_mark) => write!(f, "{}", get_start_del(del_mark.del)),
            Found::End(del_mark) => write!(f, "{}", get_end_del(del_mark.del)),
        }
    }
}

pub enum Expected<'a> {
	Spot(Cursor<'a>),
	End(Delimiter),
	Start(Delimiter),
}

impl<'a> Expected<'a> {
	pub fn start_of(spot:Cursor<'a>) -> Self{
		match spot.any_group(){
			Some((_,del,_,_)) => Expected::Start(del),
			None => Expected::Spot(spot)
		}
	}
}

impl fmt::Display for Expected<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expected::Spot(cursor) => match cursor.span().source_text() {
            	Some(s) => write!(f, "{}",s),
            	None => write!(f, "<missing source : {:?}>",cursor.span()),
            }
            Expected::Start(del) => write!(f, "{}", get_start_del(*del)),
            Expected::End(del) => write!(f, "{}", get_end_del(*del)),
        }
    }
}

pub struct Mismatch<'a,'b>{
	pub actual:Found<'a>,
	pub expected: Expected<'b>,
}

pub fn get_start_del(del:Delimiter) -> &'static str {
	match del {
        Delimiter::Parenthesis => "(",
        Delimiter::Bracket => "[",
        Delimiter::Brace => "{",
        Delimiter::None => "<empty delim (likely bug)>",
    }
}

pub fn get_end_del(del:Delimiter) -> &'static str {
	match del {
        Delimiter::Parenthesis => ")",
        Delimiter::Bracket => "]",
        Delimiter::Brace => "}",
        Delimiter::None => "<EOF>",
    }
}

#[allow(clippy::from_over_into)]
impl Into<syn::Error> for Mismatch<'_, '_> {
    fn into(self) -> syn::Error {
        let span = self.actual.span(); // Use the actual's span in all cases
        let msg =  format!("Expected \"{}\" but found \"{}\"", self.expected,self.actual);

        syn::Error::new(span, msg)
    }
}

pub fn streams_match<'a,'b>(mut start:Cursor<'b>,end:Cursor<'_>,mut input:Cursor<'a>,del:Delimiter,end_span:Option<&DelimSpan>) -> Result<Cursor<'a>,Mismatch<'a,'b>>{
	while start!=end {
		let (new_start,a) = match start.token_tree() {
			None => break,
			Some((tree,spot)) => {
				(spot,tree)
			}
		};

		let (new_input,b) = match input.token_tree() {
			None => return Err(Mismatch{
				expected: Expected::Spot(start),
				actual:Found::End(DelMark{del,span:end_span.map(|x| x.close()).unwrap_or_else(|| input.span())})
			}),
			Some((tree,spot)) => {
				(spot,tree)
			}
		};

		let matches = match (a,b) {
			(TokenTree::Ident(x),TokenTree::Ident(y)) => x==y,
			(TokenTree::Punct(x),TokenTree::Punct(y)) => x.as_char()==y.as_char(),
			(TokenTree::Literal(x),TokenTree::Literal(y)) => x.to_string()==y.to_string(),
			(TokenTree::Group(_),TokenTree::Group(_)) => {
				let (a,del_a,_,_) = start.any_group().unwrap();
				let (b,del_b,del_span,_) = input.any_group().unwrap();
				if del_a!=del_b {
					false
				}else{
					let remaining = streams_match(a,end,b,del_b,Some(&del_span))?;
					if !remaining.eof() {
						return Err(
							Mismatch{
								expected:Expected::End(del_a),
								actual:Found::Spot(remaining)
							});
					}
					true
				}
			},
			
		    _ => false,
		};

		if !matches {
			return Err(Mismatch{expected:Expected::start_of(start),actual:Found::start_of(input)})
		}

		input = new_input;
		start = new_start;
	}
	Ok(input)
}

pub fn streams_just_match<'a>(mut start:Cursor<'_>,end:Cursor<'_>,mut input:Cursor<'a>) -> Result<Cursor<'a>,DumbyError>{
	while start!=end {
		let (new_start,a) = match start.token_tree() {
			None => break,
			Some((tree,spot)) => {
				(spot,tree)
			}
		};

		let (new_input,b) = match input.token_tree() {
			None => return Err(DumbyError),
			Some((tree,spot)) => {
				(spot,tree)
			}
		};

		let matches = match (a,b) {
			(TokenTree::Ident(x),TokenTree::Ident(y)) => x==y,
			(TokenTree::Punct(x),TokenTree::Punct(y)) => x.as_char()==y.as_char(),
			(TokenTree::Literal(x),TokenTree::Literal(y)) => x.to_string()==y.to_string(),
			(TokenTree::Group(_),TokenTree::Group(_)) => {
				let (a,del_a,_,_) = start.any_group().unwrap();
				let (b,del_b,_,_) = input.any_group().unwrap();
				if del_a!=del_b {
					false
				}else{
					let remaining = streams_just_match(a,end,b)?;
					if !remaining.eof() {
						return Err(DumbyError)
					}
					true
				}
			},
			
		    _ => false,
		};

		if !matches {
			return Err(DumbyError)
		}

		input = new_input;
		start = new_start;
	}
	Ok(input)
}
#[derive(Clone,Copy,PartialEq)]
pub struct MatchParser<'b>{
	pub start:Cursor<'b>,
	pub end:Cursor<'b>
}

impl<'a, K, O:Clone> Combinator<'a,(), DumbyError,K,O> for MatchParser<'_>{
	fn parse(&self, input: Cursor<'a>,_state: &mut impl Cache<'a,O,DumbyError,K>) -> Pakerat<(Cursor<'a>,()), DumbyError>{
		let ans = streams_just_match(self.start,self.end,input).map_err(PakeratError::Regular)?;
		Ok((ans,()))
	}
}

impl<'a, K, O:Clone> Combinator<'a, (), syn::Error,K,O> for MatchParser<'_>{
	fn parse(&self, input: Cursor<'a>,_state: &mut impl Cache<'a,O,syn::Error,K>) -> Pakerat<(Cursor<'a>,()), syn::Error>{
		let ans = streams_match(self.start,self.end,input,Delimiter::None,None)
			.map_err(|e| PakeratError::Regular(e.into()))?;
		Ok((ans,()))
	}
}

macro_rules! define_parser {
    ($name:ident, $output:ty, $method:ident, $syn_err_msg:expr) => {
        #[derive(Debug, Clone, Copy, PartialEq)]
        pub struct $name;

        impl<'a, K, O:Clone> Combinator<'a, $output, syn::Error, K,O> for $name {
            #[inline]
            fn parse(&self, input: Cursor<'a>, _state: &mut impl Cache<'a, O, syn::Error, K>) -> Pakerat<(Cursor<'a>, $output), syn::Error> {
                if let Some((x, ans)) = input.$method() {
                    Ok((ans, x))
                } else {
                    Err(PakeratError::Regular(syn::Error::new(input.span(), $syn_err_msg)))
                }
            }
        }

        impl<'a, K, O:Clone> Combinator<'a, $output, DumbyError, K,O> for $name {
            #[inline]
            fn parse(&self, input: Cursor<'a>, _state: &mut impl Cache<'a, O, DumbyError, K>) -> Pakerat<(Cursor<'a>, $output), DumbyError> {
                if let Some((x, ans)) = input.$method() {
                    Ok((ans, x))
                } else {
                    Err(PakeratError::Regular(DumbyError))
                }
            }
        }
    };
}

define_parser!(AnyParser, TokenTree, token_tree, "unexpected EOF");
define_parser!(PunctParser, Punct, punct, "expected one of +-=?;.*&^%$#@!...");
define_parser!(IdentParser, Ident, ident, "expected a name");
define_parser!(LiteralParser, Literal, literal, "expected a literal (string char int etc)");
define_parser!(LifetimeParser, Lifetime, lifetime, "expected a lifetime");


#[derive(Debug, Clone, Copy, PartialEq)]
pub struct NumParser;

#[repr(transparent)]
struct BasicInt(i64);
impl Parse for BasicInt {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let lit: LitInt = input.parse()?;
        let value = lit.base10_parse::<i64>()?;
        Ok(BasicInt(value))
    }
}

impl<'a, K, O:Clone> Combinator<'a, i64, syn::Error,K,O> for NumParser{
	fn parse(&self, input: Cursor<'a>,_state: &mut impl Cache<'a,O,syn::Error,K>) -> Pakerat<(Cursor<'a>,i64), syn::Error>{
		if let Some((x, cursor)) = input.literal() {
            let i : BasicInt = syn:: parse2(x.into_token_stream()).map_err(PakeratError::Regular)?;
            Ok((cursor,i.0))
        } else {
            Err(PakeratError::Regular(syn::Error::new(input.span(), "expected an integer")))
        }
	}
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(transparent)]
pub struct DelParser(pub Delimiter);


impl<'a, K, O:Clone> Combinator<'a, Cursor<'a>, DumbyError, K,O> for DelParser {
    #[inline]
    fn parse(&self, input: Cursor<'a>, _state: &mut impl Cache<'a, O, DumbyError, K>) -> Pakerat<(Cursor<'a>, Cursor<'a>), DumbyError>{
        if let Some((x,_span, next)) = input.group(self.0) {
            Ok((next, x))
        } else {
            Err(PakeratError::Regular(DumbyError))
        }
    }
}

impl<'a, K, O:Clone> Combinator<'a, Cursor<'a>, syn::Error, K,O> for DelParser {
    #[inline]
    fn parse(&self, input: Cursor<'a>, _state: &mut impl Cache<'a, O, syn::Error, K>) -> Pakerat<(Cursor<'a>, Cursor<'a>), syn::Error>{
        if let Some((x,_span, next)) = input.group(self.0) {
            Ok((next, x))
        } else {
            Err(PakeratError::Regular(syn::Error::new(input.span(),format!("expected {}",get_start_del(self.0)))))
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct AnyDelParser;
impl<'a, K, O:Clone> Combinator<'a, Cursor<'a>, DumbyError, K,O> for AnyDelParser {
    #[inline]
    fn parse(&self, input: Cursor<'a>, _state: &mut impl Cache<'a, O, DumbyError, K>) -> Pakerat<(Cursor<'a>, Cursor<'a>), DumbyError>{
        if let Some((x,_,_, next)) = input.any_group() {
            Ok((next, x))
        } else {
            Err(PakeratError::Regular(DumbyError))
        }
    }
}

impl<'a, K, O:Clone> Combinator<'a, Cursor<'a>, syn::Error, K,O> for AnyDelParser {
    #[inline]
    fn parse(&self, input: Cursor<'a>, _state: &mut impl Cache<'a, O, syn::Error, K>) -> Pakerat<(Cursor<'a>, Cursor<'a>), syn::Error>{
        if let Some((x,_,_, next)) = input.any_group() {
            Ok((next, x))
        } else {
            Err(PakeratError::Regular(syn::Error::new(input.span(),"expected one of '{[('")))
        }
    }
}

#[cfg(test)]
mod exact_match_tests {
    
use crate::cache::BasicCache;
use std::collections::HashMap;
use super::*;
    use proc_macro2::TokenStream;
    use syn::buffer::{Cursor, TokenBuffer};
    

    /// Macro to safely create a `TokenBuffer` and `Cursor` with a proper lifetime.
    macro_rules! token_cursor {
        ($name:ident, $input:expr) => {
            let tokens: TokenStream = $input.parse().unwrap(); // Unwrap directly for clearer failure
            let buffer = TokenBuffer::new2(tokens); // Keep buffer alive
            let $name = buffer.begin(); // Extract cursor
        };
    }

    #[test]
    fn match_parser_exact_match_dumby_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 42;");
        let parser = MatchParser { start: buffer1, end: Cursor::empty() };

        let mut cache: BasicCache<0> = HashMap::new();

        let (remaining, _) = parser.parse(buffer2, &mut cache).unwrap();
        assert!(remaining.eof(), "Expected to consume the entire input, but some tokens remain.");
    }

    #[test]
    fn match_parser_exact_match_syn_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 42;");
        let parser = MatchParser { start: buffer1, end: Cursor::empty() };

        let mut cache: BasicCache<0> = HashMap::new();


        let (remaining, _) = parser.parse(buffer2, &mut cache).unwrap();
        assert!(remaining.eof(), "Expected to consume the entire input, but some tokens remain.");
    }

    #[test]
    fn match_parser_subset_should_pass() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 42; let y = 10;");
        let parser = MatchParser { start: buffer1, end: Cursor::empty() };

        let mut cache: BasicCache<0> = HashMap::new();

        let (remaining, _) = parser.parse(buffer2, &mut cache).unwrap();
        assert!(
            !remaining.eof(),
            "Expected remaining tokens to exist, but the parser consumed everything."
        );
    }

    #[test]
    fn match_parser_mismatch_dumby_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 43;");
        let parser = MatchParser { start: buffer1, end: Cursor::empty() };

        let mut cache: BasicCache<0> = HashMap::new();

        let result = parser.parse(buffer2, &mut cache);
        assert!(result.is_err(), "DumbyError parser should have failed on mismatched input.");
    }

    #[test]
    fn match_parser_mismatch_syn_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 43;");
        let parser = MatchParser { start: buffer1, end: Cursor::empty() };

        let mut cache: BasicCache<0> = HashMap::new();

        let result = parser.parse(buffer2, &mut cache);
        assert!(result.is_err(), "SynError parser should have failed on mismatched input.");
    }

    #[test]
    fn match_parser_incomplete_input_dumby_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x =");
        let parser = MatchParser { start: buffer1, end: Cursor::empty() };

        let mut cache: BasicCache<0, (), DumbyError> = HashMap::new();


        let result = parser.parse(buffer2, &mut cache);
        assert!(result.is_err(), "DumbyError parser should have failed on incomplete input.");
    }

    #[test]
    fn match_parser_incomplete_input_syn_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x =");
        let parser = MatchParser { start: buffer1, end: Cursor::empty() };

        let mut cache: BasicCache<0> = HashMap::new();

        let result = parser.parse(buffer2, &mut cache);
        assert!(result.is_err(), "SynError parser should have failed on incomplete input.");
    }

    #[test]
    fn match_parser_extra_tokens_fail() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 42; let y = 10; let z = 20;");
        let parser = MatchParser { start: buffer2, end: Cursor::empty() }; // Reverse case: expected is longer

        let mut cache: BasicCache<0> = HashMap::new();

        let result = parser.parse(buffer1, &mut cache);
        assert!(result.is_err(), "Parser should fail when expected is longer than input.");
    }

	#[test]
	fn match_parser_non_empty_end() {
	    token_cursor!(buffer, "let x = 42; let y = 10;");
	    
	    let start = buffer;
	    let mut cursor = buffer;
	    
	    // Move forward to get a valid end cursor
	    for _ in 0..3 {
	        if let Some((_, next_cursor)) = cursor.token_tree() {
	            cursor = next_cursor;
	        } else {
	            panic!("Failed to advance cursor within the same buffer.");
	        }
	    }
	    
	    let end = cursor; // This should point to the position after `42;`
	    
	    let parser = MatchParser { start, end };

	    let mut cache: BasicCache<0> = HashMap::new();

	    let (remaining, _) = parser.parse(buffer, &mut cache).unwrap();

	    // The parser should succeed, and the final cursor should match `end`
	    assert!(
	        remaining == end,
	        "Expected the remaining cursor to be at `end`, but it was somewhere else."
	    );
	}

}
