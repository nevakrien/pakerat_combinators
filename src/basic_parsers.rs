use crate::cache::DynCache;
use crate::combinator::BorrowParse;
use crate::combinator::Combinator;
use crate::combinator::Pakerat;
use crate::combinator::PakeratError;
use crate::core::Expected;
use crate::core::Found;
use crate::core::Input;
use crate::core::Mismatch;
use crate::core::ParseError;
use proc_macro2::Delimiter;
use proc_macro2::Ident;
use proc_macro2::Literal;
use proc_macro2::Punct;
use proc_macro2::TokenTree;
use syn::__private::ToTokens;
use syn::parse::Parse;
use syn::parse::ParseStream;
use syn::Lifetime;
use syn::LitInt;

///detects an exact match between an input stream and the stream from start to end (not including end)
pub fn streams_match<'a>(
    mut start: Input<'_>,
    end: Input<'_>,
    mut input: Input<'a>,
) -> Result<Input<'a>, Mismatch> {
    while start != end {
        let (new_start, a) = match start.token_tree() {
            None => break,
            Some((tree, spot)) => (spot, tree),
        };

        let (new_input, b) = match input.token_tree() {
            None => {
                let actual = match input.block_end() {
                    Some(del_mark) => Found::End(del_mark),
                    None => Found::EOF(input.end_span()),
                };
                return Err(Mismatch {
                    expected: Expected::Spot(start.span()),
                    actual,
                });
            }
            Some((tree, spot)) => (spot, tree),
        };

        let matches = match (a, b) {
            (TokenTree::Ident(x), TokenTree::Ident(y)) => x == y,
            (TokenTree::Punct(x), TokenTree::Punct(y)) => x.as_char() == y.as_char(),
            (TokenTree::Literal(x), TokenTree::Literal(y)) => x.to_string() == y.to_string(),
            (TokenTree::Group(_), TokenTree::Group(_)) => {
                let (a, del_a, _, _) = start.any_group().unwrap();
                let (b, del_b, _, _) = input.any_group().unwrap();
                if del_a != del_b {
                    false
                } else {
                    let remaining = streams_match(a, end, b)?;
                    if !remaining.eof() {
                        return Err(Mismatch {
                            expected: Expected::End(del_a),
                            actual: Found::Spot(remaining.span()),
                        });
                    }
                    true
                }
            }

            _ => false,
        };

        if !matches {
            return Err(Mismatch {
                expected: Expected::start_of(start),
                actual: Found::start_of(input),
            });
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

///detects an exact match between an input stream and the stream from start to end (not including end)
#[derive(Clone, Copy)]
pub struct MatchParser<'b> {
    pub start: Input<'b>,
    pub end: Input<'b>,
}

impl<O: BorrowParse> Combinator<(), O> for MatchParser<'_> {
    fn parse<'a>(
        &self,
        input: Input<'a>,
        _state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, ())> {
        let ans = streams_match(self.start, self.end, input)
            .map_err(|e| PakeratError::<ParseError>::Regular(e.into()))?;
        Ok((ans, ()))
    }
}

macro_rules! define_parser {
    ($name:ident, $output:ty, $method:ident, $expected:expr) => {
        #[doc = concat!("thin wrapper around [`Input::", stringify!($method), "()`]")]
        #[doc = "that extracts a [`"]
        #[doc = stringify!($output)]
        #[doc = "`] token from the input stream."]
        #[doc = "If the expected token is not found, it produces a [`ParseError`]."]
        #[derive(Debug, Clone, Copy, PartialEq)]
        pub struct $name;

        impl<O: BorrowParse> Combinator<$output, O> for $name {
            #[inline]
            fn parse<'a>(
                &self,
                input: Input<'a>,
                _state: &mut dyn DynCache<'a, O>,
            ) -> Pakerat<(Input<'a>, $output)> {
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
define_parser!(
    LiteralParser,
    Literal,
    literal,
    "a literal (string, char, int, etc.)"
);
define_parser!(LifetimeParser, Lifetime, lifetime, "a lifetime");

///parses an i64 using [`syn`]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct IntParser;

#[repr(transparent)]
struct BasicInt(i64);
impl Parse for BasicInt {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let lit: LitInt = input.parse()?;
        let value = lit.base10_parse::<i64>()?;
        Ok(BasicInt(value))
    }
}

impl<O: BorrowParse> Combinator<i64, O> for IntParser {
    fn parse<'a>(
        &self,
        input: Input<'a>,
        _state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, i64)> {
        if let Some((x, new_input)) = input.literal() {
            let i: BasicInt = syn::parse2(x.into_token_stream()).map_err(PakeratError::Regular)?;
            Ok((new_input, i.0))
        } else {
            Err(PakeratError::Regular(ParseError::Simple(Mismatch {
                actual: Found::start_of(input),
                expected: Expected::Text("integer"),
            })))
        }
    }
}

/// parses a group delimited by a specific [`Delimiter`] returining an Input to the inside of the group
///
/// this methods api is a result of how [`proc_macro2::TokenTree`] works. 
/// We are unable to parse individual delimiters
#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(transparent)]
pub struct DelParser(pub Delimiter);
impl<O: BorrowParse> Combinator<Input<'_>, O> for DelParser {
    #[inline]
    fn parse<'a>(
        &self,
        input: Input<'a>,
        _state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, Input<'a>)> {
        if let Some((x, _span, next)) = input.group(self.0) {
            Ok((next, x))
        } else {
            Err(PakeratError::Regular(ParseError::Simple(Mismatch {
                actual: Found::start_of(input),
                expected: Expected::End(self.0),
            })))
        }
    }
}

/// parses any group delimited by [`Delimiter`] returining an Input to the inside of the group
///
/// this methods api is a result of how [`proc_macro2::TokenTree`] works. 
/// We are unable to parse individual delimiters
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct AnyDelParser;

impl<O: BorrowParse> Combinator<Input<'_>, O> for AnyDelParser {
    #[inline]
    fn parse<'a>(
        &self,
        input: Input<'a>,
        _state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, Input<'a>)> {
        if let Some((x, _, _, next)) = input.any_group() {
            Ok((next, x))
        } else {
            Err(PakeratError::Regular(ParseError::Simple(Mismatch {
                actual: Found::start_of(input),
                expected: Expected::Text("one of ({["),
            })))
        }
    }
}

#[cfg(test)]
mod exact_match_tests {

    use super::*;
    use crate::cache::BasicCache;
    use proc_macro2::TokenStream;
    use std::collections::HashMap;
    use syn::buffer::TokenBuffer;

    use crate::macros::token_cursor;

    #[test]
    fn match_parser_exact_match_dumby_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 42;");
        let parser = MatchParser {
            start: buffer1,
            end: Input::empty(),
        };

        let mut cache: BasicCache<0> = HashMap::new();

        let (remaining, _) = parser.parse(buffer2, &mut cache).unwrap();
        assert!(
            remaining.eof(),
            "Expected to consume the entire input, but some tokens remain."
        );
    }

    #[test]
    fn match_parser_exact_match_syn_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 42;");
        let parser = MatchParser {
            start: buffer1,
            end: Input::empty(),
        };

        let mut cache: BasicCache<0> = HashMap::new();

        let (remaining, _) = parser.parse(buffer2, &mut cache).unwrap();
        assert!(
            remaining.eof(),
            "Expected to consume the entire input, but some tokens remain."
        );
    }

    #[test]
    fn match_parser_subset_should_pass() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 42; let y = 10;");
        let parser = MatchParser {
            start: buffer1,
            end: Input::empty(),
        };

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
        let parser = MatchParser {
            start: buffer1,
            end: Input::empty(),
        };

        let mut cache: BasicCache<0> = HashMap::new();

        let result = parser.parse(buffer2, &mut cache);
        assert!(
            result.is_err(),
            "DumbyError parser should have failed on mismatched input."
        );
    }

    #[test]
    fn match_parser_mismatch_syn_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 43;");
        let parser = MatchParser {
            start: buffer1,
            end: Input::empty(),
        };

        let mut cache: BasicCache<0> = HashMap::new();

        let result = parser.parse(buffer2, &mut cache);
        assert!(
            result.is_err(),
            "SynError parser should have failed on mismatched input."
        );
    }

    #[test]
    fn match_parser_incomplete_input_dumby_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x =");
        let parser = MatchParser {
            start: buffer1,
            end: Input::empty(),
        };

        let mut cache: BasicCache<0, ()> = HashMap::new();

        let result = parser.parse(buffer2, &mut cache);
        assert!(
            result.is_err(),
            "DumbyError parser should have failed on incomplete input."
        );
    }

    #[test]
    fn match_parser_incomplete_input_syn_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x =");
        let parser = MatchParser {
            start: buffer1,
            end: Input::empty(),
        };

        let mut cache: BasicCache<0> = HashMap::new();

        let result = parser.parse(buffer2, &mut cache);
        assert!(
            result.is_err(),
            "SynError parser should have failed on incomplete input."
        );
    }

    #[test]
    fn match_parser_extra_tokens_fail() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 42; let y = 10; let z = 20;");
        let parser = MatchParser {
            start: buffer2,
            end: Input::empty(),
        }; // Reverse case: expected is longer

        let mut cache: BasicCache<0> = HashMap::new();

        let result = parser.parse(buffer1, &mut cache);
        assert!(
            result.is_err(),
            "Parser should fail when expected is longer than input."
        );
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
