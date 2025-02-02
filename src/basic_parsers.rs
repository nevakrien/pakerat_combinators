use crate::core::ParseError;
use crate::core::Expected;
use crate::core::Mismatch;
use crate::core::Found;
use crate::core::get_start_del;
use syn::__private::ToTokens;
use syn::parse::ParseStream;
use syn::LitInt;
use syn::parse::Parse;
use syn::Lifetime;
use proc_macro2::Literal;
use proc_macro2::Ident;
use proc_macro2::Punct;
use crate::combinator::PakeratError;
use crate::combinator::Combinator;
use crate::cache::Cache;
use crate::combinator::Pakerat;
use proc_macro2::TokenTree;
use proc_macro2::Delimiter;
use crate::core::Input;




pub fn streams_match<'a,'b>(mut start:Input<'b>,end:Input<'_>,mut input:Input<'a>) -> Result<Input<'a>,Mismatch>{
	while start!=end {
		let (new_start,a) = match start.token_tree() {
			None => break,
			Some((tree,spot)) => {
				(spot,tree)
			}
		};

		let (new_input,b) = match input.token_tree() {
			None => {
				let actual = match input.block_end(){
					Some(del_mark) =>Found::End(del_mark),
					None=>Found::EOF(input.end_span()),
				};
				return Err(Mismatch{
					expected: Expected::Spot(start.span()),
					actual
				})
			},
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
					let remaining = streams_match(a,end,b)?;
					if !remaining.eof() {
						return Err(
							Mismatch{
								expected:Expected::End(del_a),
								actual:Found::Spot(remaining.span())
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

// pub fn streams_just_match<'a>(mut start:Input<'_>,end:Input<'_>,mut input:Input<'a>) -> Result<Input<'a>,DumbyError>{
// 	while start!=end {
// 		let (new_start,a) = match start.token_tree() {
// 			None => break,
// 			Some((tree,spot)) => {
// 				(spot,tree)
// 			}
// 		};

// 		let (new_input,b) = match input.token_tree() {
// 			None => return Err(DumbyError),
// 			Some((tree,spot)) => {
// 				(spot,tree)
// 			}
// 		};

// 		let matches = match (a,b) {
// 			(TokenTree::Ident(x),TokenTree::Ident(y)) => x==y,
// 			(TokenTree::Punct(x),TokenTree::Punct(y)) => x.as_char()==y.as_char(),
// 			(TokenTree::Literal(x),TokenTree::Literal(y)) => x.to_string()==y.to_string(),
// 			(TokenTree::Group(_),TokenTree::Group(_)) => {
// 				let (a,del_a,_,_) = start.any_group().unwrap();
// 				let (b,del_b,_,_) = input.any_group().unwrap();
// 				if del_a!=del_b {
// 					false
// 				}else{
// 					let remaining = streams_just_match(a,end,b)?;
// 					if !remaining.eof() {
// 						return Err(DumbyError)
// 					}
// 					true
// 				}
// 			},
			
// 		    _ => false,
// 		};

// 		if !matches {
// 			return Err(DumbyError)
// 		}

// 		input = new_input;
// 		start = new_start;
// 	}
// 	Ok(input)
// }
#[derive(Clone,Copy)]
pub struct MatchParser<'b>{
	pub start:Input<'b>,
	pub end:Input<'b>
}


impl<'a, O:Clone,C: Cache<'a, O>> Combinator<'a, (),O,C> for MatchParser<'_>{
	fn parse(&self, input: Input<'a>,_state: &mut C) -> Pakerat<(Input<'a>,())>{
		let ans = streams_match(self.start,self.end,input)
			.map_err(|e| PakeratError::<ParseError>::Regular(e.into()))?;
		Ok((ans,()))
	}
}

macro_rules! define_parser {
    ($name:ident, $output:ty, $method:ident, $expected:expr) => {
        #[derive(Debug, Clone, Copy, PartialEq)]
        pub struct $name;

        impl<'a, O: Clone, C: Cache<'a, O>> Combinator<'a, $output, O, C> for $name {
            #[inline]
            fn parse(&self, input: Input<'a>, _state: &mut C) -> Pakerat<(Input<'a>, $output)> {
                if let Some((x, ans)) = input.$method() {
                    Ok((ans, x))
                } else {
                    Err(PakeratError::Regular(ParseError::Simple(Mismatch {
                        actual: Found::start_of(input),
                        expected: Expected::Text($expected),
                    })))
                }
            }
        }
    };
}

// Define the parsers using the updated macro
define_parser!(AnyParser, TokenTree, token_tree, "any token");
define_parser!(PunctParser, Punct, punct, "one of +-=?;.*&^%$#@!...");
define_parser!(IdentParser, Ident, ident, "a name");
define_parser!(LiteralParser, Literal, literal, "a literal (string, char, int, etc.)");
define_parser!(LifetimeParser, Lifetime, lifetime, "a lifetime");



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

impl<'a, O:Clone,C: Cache<'a, O>> Combinator<'a, i64,O,C> for NumParser{
	fn parse(&self, input: Input<'a>,_state: &mut C) -> Pakerat<(Input<'a>,i64)>{
		if let Some((x, new_input)) = input.literal() {
            let i : BasicInt = syn:: parse2(x.into_token_stream()).map_err(PakeratError::Regular)?;
            Ok((new_input,i.0))
        } else {
            Err(PakeratError::Regular(ParseError::Simple(
            	Mismatch{
            		actual:Found::start_of(input),
            		expected:Expected::Text("integer")
            	})))
        }
	}
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(transparent)]
pub struct DelParser(pub Delimiter);


impl<'a, O:Clone,C: Cache<'a, O>> Combinator<'a, Input<'a>,O,C> for DelParser {
    #[inline]
    fn parse(&self, input: Input<'a>, _state: &mut C) -> Pakerat<(Input<'a>, Input<'a>)>{
        if let Some((x,_span, next)) = input.group(self.0) {
            Ok((next, x))
        } else {
            Err(PakeratError::Regular(ParseError::Simple(
            	Mismatch{
            		actual:Found::start_of(input),
            		expected:Expected::End(self.0)
            	})))
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct AnyDelParser;

impl<'a, O:Clone,C: Cache<'a, O>> Combinator<'a, Input<'a>,O,C> for AnyDelParser {
    #[inline]
    fn parse(&self, input: Input<'a>, _state: &mut C) -> Pakerat<(Input<'a>, Input<'a>)>{
        if let Some((x,_,_, next)) = input.any_group() {
            Ok((next, x))
        } else {
            Err(PakeratError::Regular(ParseError::Simple(
            	Mismatch{
            		actual:Found::start_of(input),
            		expected:Expected::Text("one of ({[")
            	})))
        }
    }
}

#[cfg(test)]
mod exact_match_tests {
    
use crate::cache::BasicCache;
use std::collections::HashMap;
use super::*;
    use proc_macro2::TokenStream;
    use syn::buffer::{TokenBuffer};
    

    /// Macro to safely create a `TokenBuffer` and `Input` with a proper lifetime.
    macro_rules! token_cursor {
        ($name:ident, $input:expr) => {
            let tokens: TokenStream = $input.parse().unwrap(); // Unwrap directly for clearer failure
            let buffer = TokenBuffer::new2(tokens); // Keep buffer alive
            let $name = Input::new(&buffer); // Extract Input
        };
    }

    #[test]
    fn match_parser_exact_match_dumby_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 42;");
        let parser = MatchParser { start: buffer1, end: Input::empty() };

        let mut cache: BasicCache<0> = HashMap::new();

        let (remaining, _) = parser.parse(buffer2, &mut cache).unwrap();
        assert!(remaining.eof(), "Expected to consume the entire input, but some tokens remain.");
    }

    #[test]
    fn match_parser_exact_match_syn_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 42;");
        let parser = MatchParser { start: buffer1, end: Input::empty() };

        let mut cache: BasicCache<0> = HashMap::new();


        let (remaining, _) = parser.parse(buffer2, &mut cache).unwrap();
        assert!(remaining.eof(), "Expected to consume the entire input, but some tokens remain.");
    }

    #[test]
    fn match_parser_subset_should_pass() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 42; let y = 10;");
        let parser = MatchParser { start: buffer1, end: Input::empty() };

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
        let parser = MatchParser { start: buffer1, end: Input::empty() };

        let mut cache: BasicCache<0> = HashMap::new();

        let result = parser.parse(buffer2, &mut cache);
        assert!(result.is_err(), "DumbyError parser should have failed on mismatched input.");
    }

    #[test]
    fn match_parser_mismatch_syn_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 43;");
        let parser = MatchParser { start: buffer1, end: Input::empty() };

        let mut cache: BasicCache<0> = HashMap::new();

        let result = parser.parse(buffer2, &mut cache);
        assert!(result.is_err(), "SynError parser should have failed on mismatched input.");
    }

    #[test]
    fn match_parser_incomplete_input_dumby_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x =");
        let parser = MatchParser { start: buffer1, end: Input::empty() };

        let mut cache: BasicCache<0, ()> = HashMap::new();


        let result = parser.parse(buffer2, &mut cache);
        assert!(result.is_err(), "DumbyError parser should have failed on incomplete input.");
    }

    #[test]
    fn match_parser_incomplete_input_syn_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x =");
        let parser = MatchParser { start: buffer1, end: Input::empty() };

        let mut cache: BasicCache<0> = HashMap::new();

        let result = parser.parse(buffer2, &mut cache);
        assert!(result.is_err(), "SynError parser should have failed on incomplete input.");
    }

    #[test]
    fn match_parser_extra_tokens_fail() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 42; let y = 10; let z = 20;");
        let parser = MatchParser { start: buffer2, end: Input::empty() }; // Reverse case: expected is longer

        let mut cache: BasicCache<0> = HashMap::new();

        let result = parser.parse(buffer1, &mut cache);
        assert!(result.is_err(), "Parser should fail when expected is longer than input.");
    }

	#[test]
	fn match_parser_non_empty_end() {
	    token_cursor!(buffer, "let x = 42; let y = 10;");
	    
	    let start = buffer;
	    let mut input = buffer;
	    
	    // Move forward to get a valid end Input
	    for _ in 0..3 {
	        if let Some((_, next_cursor)) = input.token_tree() {
	            input = next_cursor;
	        } else {
	            panic!("Failed to advance Input within the same buffer.");
	        }
	    }
	    
	    let end = input; // This should point to the position after `42;`
	    
	    let parser = MatchParser { start, end };

	    let mut cache: BasicCache<0> = HashMap::new();

	    let (remaining, _) = parser.parse(buffer, &mut cache).unwrap();

	    // The parser should succeed, and the final Input should match `end`
	    assert!(
	        remaining == end,
	        "Expected the remaining Input to be at `end`, but it was somewhere else."
	    );
	}

}
