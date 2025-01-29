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

pub struct Mismatch<'a,'b>{
	pub actual:Found<'a>,
	pub expected: Expected<'b>,
}

impl Into<syn::Error> for Mismatch<'_, '_> {
    fn into(self) -> syn::Error {
        let span = self.actual.span(); // Use the actual's span in all cases
        let msg = match (&self.actual, &self.expected) {
            (Found::Spot(_), Expected::Spot(_)) => "Expected a different token.".to_string(),
            (Found::Start(found), Expected::Start(expected)) => {
                format!("Expected {:?} but found {:?}", expected, found.del)
            }
            (Found::End(found), Expected::End(expected)) => {
                format!("Expected {:?} but found {:?}", expected, found.del)
            }
            _ => "Mismatched token structures.".to_string(),
        };

        syn::Error::new(span, msg)
    }
}

pub fn streams_match<'a,'b>(mut start:Cursor<'b>,end:Cursor<'_>,mut input:Cursor<'a>,del:Delimiter,del_span:Option<&DelimSpan>) -> Result<Cursor<'a>,Mismatch<'a,'b>>{
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
				actual:Found::End(DelMark{del,span:del_span.map(|x|x.close()).unwrap_or_else(|| Span::mixed_site())})
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
	return Ok(input)
}

pub fn streams_just_match<'a,'b>(mut start:Cursor<'b>,end:Cursor<'_>,mut input:Cursor<'a>) -> Result<Cursor<'a>,DumbyError>{
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
	return Ok(input)
}
#[derive(Clone,Copy,PartialEq)]
pub struct MatchParser<'b>{
	pub start:Cursor<'b>,
	pub end:Cursor<'b>
}

impl<K> Combinator<(), DumbyError,K> for MatchParser<'_>{
	fn parse<'a>(&self, input: Cursor<'a>,_state: &mut impl Cache<'a,(),DumbyError,K>) -> Pakerat<(Cursor<'a>,()), DumbyError>{
		let ans = streams_just_match(self.start,self.end,input).map_err(PakeratError::Regular)?;
		Ok((ans,()))
	}
}

impl<K> Combinator<(), syn::Error,K> for MatchParser<'_>{
	fn parse<'a>(&self, input: Cursor<'a>,_state: &mut impl Cache<'a,(),syn::Error,K>) -> Pakerat<(Cursor<'a>,()), syn::Error>{
		let ans = streams_match(self.start,self.end,input,Delimiter::None,None)
			.map_err(|e| PakeratError::Regular(e.into()))?;
		Ok((ans,()))
	}
}

#[cfg(test)]
mod tests {
    use super::*;
    use proc_macro2::TokenStream;
    use syn::buffer::{Cursor, TokenBuffer};
    use crate::cache::{ArrayCache};

    /// Macro to safely create a `TokenBuffer` and `Cursor` with a proper lifetime.
    macro_rules! token_cursor {
        ($name:ident, $input:expr) => {
            let tokens: TokenStream = $input.parse().unwrap(); // Unwrap directly for clearer failure
            let buffer = TokenBuffer::new2(tokens); // Keep buffer alive
            let $name = buffer.begin(); // Extract cursor
        };
    }

    #[test]
    fn test_match_parser_exact_match_dumby_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 42;");
        let parser = MatchParser { start: buffer1, end: Cursor::empty() };

        let mut cache: ArrayCache<8, (), DumbyError> = Default::default();

        let (remaining, _) = parser.parse(buffer2, &mut cache).unwrap();
        assert!(remaining.eof(), "Expected to consume the entire input, but some tokens remain.");
    }

    #[test]
    fn test_match_parser_exact_match_syn_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 42;");
        let parser = MatchParser { start: buffer1, end: Cursor::empty() };

        let mut cache: ArrayCache<8, (), syn::Error> = Default::default();

        let (remaining, _) = parser.parse(buffer2, &mut cache).unwrap();
        assert!(remaining.eof(), "Expected to consume the entire input, but some tokens remain.");
    }

    #[test]
    fn test_match_parser_subset_should_pass() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 42; let y = 10;");
        let parser = MatchParser { start: buffer1, end: Cursor::empty() };

        let mut cache: ArrayCache<8, (), syn::Error> = Default::default();

        let (remaining, _) = parser.parse(buffer2, &mut cache).unwrap();
        assert!(
            !remaining.eof(),
            "Expected remaining tokens to exist, but the parser consumed everything."
        );
    }

    #[test]
    fn test_match_parser_mismatch_dumby_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 43;");
        let parser = MatchParser { start: buffer1, end: Cursor::empty() };

        let mut cache: ArrayCache<8, (), DumbyError> = Default::default();

        let result = parser.parse(buffer2, &mut cache);
        assert!(result.is_err(), "DumbyError parser should have failed on mismatched input.");
    }

    #[test]
    fn test_match_parser_mismatch_syn_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 43;");
        let parser = MatchParser { start: buffer1, end: Cursor::empty() };

        let mut cache: ArrayCache<8, (), syn::Error> = Default::default();

        let result = parser.parse(buffer2, &mut cache);
        assert!(result.is_err(), "SynError parser should have failed on mismatched input.");
    }

    #[test]
    fn test_match_parser_incomplete_input_dumby_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x =");
        let parser = MatchParser { start: buffer1, end: Cursor::empty() };

        let mut cache: ArrayCache<8, (), DumbyError> = Default::default();

        let result = parser.parse(buffer2, &mut cache);
        assert!(result.is_err(), "DumbyError parser should have failed on incomplete input.");
    }

    #[test]
    fn test_match_parser_incomplete_input_syn_error() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x =");
        let parser = MatchParser { start: buffer1, end: Cursor::empty() };

        let mut cache: ArrayCache<8, (), syn::Error> = Default::default();

        let result = parser.parse(buffer2, &mut cache);
        assert!(result.is_err(), "SynError parser should have failed on incomplete input.");
    }

    #[test]
    fn test_match_parser_extra_tokens_fail() {
        token_cursor!(buffer1, "let x = 42;");
        token_cursor!(buffer2, "let x = 42; let y = 10; let z = 20;");
        let parser = MatchParser { start: buffer2, end: Cursor::empty() }; // Reverse case: expected is longer

        let mut cache: ArrayCache<8, (), syn::Error> = Default::default();

        let result = parser.parse(buffer1, &mut cache);
        assert!(result.is_err(), "Parser should fail when expected is longer than input.");
    }

	#[test]
	fn test_match_parser_non_empty_end() {
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

	    let mut cache: ArrayCache<8, (), syn::Error> = Default::default();

	    let (remaining, _) = parser.parse(buffer, &mut cache).unwrap();

	    // The parser should succeed, and the final cursor should match `end`
	    assert!(
	        remaining == end,
	        "Expected the remaining cursor to be at `end`, but it was somewhere else."
	    );
	}

}
