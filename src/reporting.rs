use crate::combinator::CombinatorExt;
use std::marker::PhantomData;
use crate::combinator::{Combinator, Parsable, Pakerat, PakeratError};
use crate::core::{Input, Expected, Found, Mismatch, ParseError};
use crate::cache::DynCache;


/// A parser that reports an error when the inner parser succeeds.
///
/// If the inner parser finds a match, this parser returns an error (`Err(PakeratError::Regular(ParseError::Empty))`),
/// indicating that an unexpected match occurred.  
/// If the inner parser fails regularly, this parser returns `Ok((input, e))`, effectively "inverting" the result,
/// and the original error is returned while no input is consumed.
/// Recursive errors from the inner parser are escalated as-is.
///
/// Note that this parser does not consume any input.
///
/// # Example
/// ```rust
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::cache::BasicCache;
/// use pakerat_combinators::core::{Input, ParseError};
/// use pakerat_combinators::reporting::ParseReport;
/// use syn::buffer::TokenBuffer;
///
/// fn main() {
///     let tokens = "dummy".parse().unwrap();
///     let buffer = TokenBuffer::new2(tokens);
///     let input = Input::new(&buffer);
///     let mut cache = BasicCache::<0>::new();
///
///     let reporter = ParseReport::new(IdentParser);
///
///     // If IdentParser succeeds (i.e. "dummy" is an identifier),
///     // the inverse parser returns an error.
///     match reporter.parse(input, &mut cache) {
///         Ok((_input, err)) => {
///             println!("Inner parser did not match as expected. Error: {:?}", err);
///         },
///         Err(e) => {
///             println!("Unexpected match: {:?}", e);
///         }
///     }
/// }
/// ```
pub struct ParseReport<INNER, T = (), O = T>
where
    INNER: Combinator<T, O>,
    T: Parsable,
    O: Parsable,
{
    pub inner: INNER,
    pub _phantom: PhantomData<(T, O)>,
}

impl<INNER, T, O> ParseReport<INNER, T, O>
where
    INNER: Combinator<T, O>,
    T: Parsable,
    O: Parsable,
{
    pub fn new(inner: INNER) -> Self {
        Self {
            inner,
            _phantom: PhantomData,
        }
    }
}

impl<INNER, T, O> Combinator<ParseError, O> for ParseReport<INNER, T, O>
where
    INNER: Combinator<T, O>,
    T: Parsable,
    O: Parsable,
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, ParseError)> {
        match self.inner.parse_recognize(input, cache) {
            Ok(_) => Err(PakeratError::Regular(ParseError::Empty)),
            Err(PakeratError::Regular(e)) => Ok((input,e)),
            Err(PakeratError::Recursive(e)) => Err(PakeratError::Recursive(e)),
        }
    }
}

/// A parser that reports a mismatch error when the inner parser succeeds.
///
/// This is useful for detecting unexpected matches.  
/// If the inner parser finds a match, this parser returns `Ok(ParseError::Simple(Mismatch))`,  
/// reporting that the found token (only the first token is used) does not match the expected pattern.  
/// If the inner parser fails normally, this parser returns `Err(ParseError::Empty)`.  
/// Recursive errors from the inner parser are escalated unchanged.
///
/// # Example
/// ```rust
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::cache::BasicCache;
/// use pakerat_combinators::core::{Input, Expected};
/// use pakerat_combinators::reporting::ParseMissmatch;
/// use syn::buffer::TokenBuffer;
///
/// let tokens = "dummy".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
/// let mut cache = BasicCache::<0>::new();
///
/// let mismatcher = ParseMissmatch::new(IdentParser, Expected::Text("a literal"));
/// let _ = mismatcher.parse(input, &mut cache);
/// ```
pub struct ParseMissmatch<INNER, T = (), O = T>
where
    INNER: Combinator<T, O>,
    T: Parsable,
    O: Parsable,
{
    pub inner: INNER,
    pub expected: Expected,
    pub _phantom: PhantomData<(T, O)>,
}

impl<INNER, T, O> ParseMissmatch<INNER, T, O>
where
    INNER: Combinator<T, O>,
    T: Parsable,
    O: Parsable,
{
    pub fn new(inner: INNER, expected: Expected) -> Self {
        Self {
            inner,
            expected,
            _phantom: PhantomData,
        }
    }
}

impl<INNER, T, O> Combinator<ParseError, O> for ParseMissmatch<INNER, T, O>
where
    INNER: Combinator<T, O>,
    T: Parsable,
    O: Parsable,
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, ParseError)> {
        match self.inner.parse_recognize(input, cache) {
            Ok((next, recognized)) => {
                let mismatch = Mismatch {
                    actual: Found::start_of(recognized),
                    expected: self.expected.clone(),
                };
                Ok((next, ParseError::Simple(mismatch)))
            }
            Err(PakeratError::Regular(_)) => Err(PakeratError::Regular(ParseError::Empty)),
            Err(PakeratError::Recursive(e)) => Err(PakeratError::Recursive(e)),
        }
    }
}

/// A parser that reports a forbidden construct when the inner parser succeeds.
///
/// If the inner parser matches, this parser returns `Ok(ParseError::Message)`,  
/// tagging the recognized input with a custom error message.  
/// If the inner parser fails normally, this parser returns `Err(ParseError::Empty)`.  
/// Recursive errors from the inner parser are escalated unchanged.
///
/// # Example
/// ```rust
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::cache::BasicCache;
/// use pakerat_combinators::core::Input;
/// use pakerat_combinators::reporting::ParseForbiden;
/// use syn::buffer::TokenBuffer;
///
/// let tokens = "dummy".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
/// let mut cache = BasicCache::<0>::new();
///
/// let forbidden = ParseForbiden::new(IdentParser, "forbidden identifier usage");
/// let _ = forbidden.parse(input, &mut cache);
/// ```
pub struct ParseForbiden<INNER, T = (), O = T>
where
    INNER: Combinator<T, O>,
    T: Parsable,
    O: Parsable,
{
    pub inner: INNER,
    pub message: &'static str,
    pub _phantom: PhantomData<(T, O)>,
}

impl<INNER, T, O> ParseForbiden<INNER, T, O>
where
    INNER: Combinator<T, O>,
    T: Parsable,
    O: Parsable,
{
    pub fn new(inner: INNER, message: &'static str) -> Self {
        Self {
            inner,
            message,
            _phantom: PhantomData,
        }
    }
}

impl<INNER, T, O> Combinator<ParseError, O> for ParseForbiden<INNER, T, O>
where
    INNER: Combinator<T, O>,
    T: Parsable,
    O: Parsable,
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, ParseError)> {
        match self.inner.parse_recognize(input, cache) {
            Ok((next, recognized)) => {
                Ok((next, ParseError::Message(recognized.span(), self.message)))
            }
            Err(PakeratError::Regular(_)) => Err(PakeratError::Regular(ParseError::Empty)),
            Err(PakeratError::Recursive(e)) => Err(PakeratError::Recursive(e)),
        }
    }
}

/// Inverted parser that raises errors on inner successes.
///
/// If the inner parser returns `Ok((_, err))`, its error is raised as a failure.
/// If it returns a regular error the parser succeeds returning the input.
///
/// This parser is useful as a way to validate inputs. The returned error can be customized, which is the main benefit.
///
/// # Example
/// ```rust
/// use pakerat_combinators::combinator::{PakeratError,Combinator};
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::cache::BasicCache;
/// use pakerat_combinators::core::{Input, Expected, ParseError};
/// use pakerat_combinators::reporting::{ParseMissmatch, ChecError};
/// use syn::buffer::TokenBuffer;
/// use std::marker::PhantomData;
///
/// let tokens = "identifier".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
/// let mut cache = BasicCache::<0>::new();
///
/// // Create a parser that expects a literal but finds an identifier.
/// let mismatcher = ParseMissmatch::new(IdentParser, Expected::Text("a literal"));
///
/// // Wrap it in ChecError to turn the mismatch into a raised error.
/// let raise = ChecError {
///     inner: mismatcher,
///     _phantom: PhantomData,
/// };
///
/// let result = raise.parse(input, &mut cache);
///
/// // Since the input is an identifier, ParseMissmatch will succeed with an error,
/// // which ChecError should then raise.
/// assert!(matches!(result, Err(PakeratError::Regular(ParseError::Simple(_)))));
/// ```
pub struct ChecError<INNER,O> 
where INNER:Combinator<ParseError,O>,O:Parsable
{
    pub inner: INNER,
    pub _phantom: PhantomData<O>,
}

impl<INNER,O> Combinator<(),O> for ChecError<INNER,O>
where INNER:Combinator<ParseError,O>,O:Parsable{
fn parse<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>,())> {
    match self.inner.parse(input,cache) {
        Ok((_,err)) => Err(PakeratError::Regular(err)),
        Err(PakeratError::Regular(_)) => Ok((input,())),
        Err(e)=> Err(e),
    }

}
}