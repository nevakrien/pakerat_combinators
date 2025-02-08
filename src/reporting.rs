use crate::combinator::CombinatorExt;
use std::marker::PhantomData;
use crate::combinator::{Combinator, Parsable, Pakerat, PakeratError};
use crate::core::{Input, Expected, Found, Mismatch, ParseError};
use crate::cache::DynCache;

/// This combinator is meant for diagnostic purposes: when used, it catches a non-recursive error from the inner parser
/// (if one occurs) and returns it as a successful result: reporting what the error would have been without consuming any input.
/// Conversely, if the inner parser succeeds, it returns a failure (`ParseError::Empty`).
///
/// **IMPORTANT: Recursive errors are escalated unchanged as an error.** This behavior is crucial to prevent infinite loops
/// in recursive parsing contexts. If this is not desired use [`ParseReportAll`] instead.
///
/// This parser acts as a bridge between regular parsers and the error-style parsers found in the [`reporting`] module.
///
///[`reporting`]: crate::reporting
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
///     let tokens = "2 dummy".parse().unwrap();
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
///             panic!("Unexpected match: {:?}", e);
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

/// This combinator is meant for diagnostic purposes: when used, it catches errors from its inner parser, both
/// non‑recursive and recursive returning them as a successful result, reporting what the error would have been
/// without consuming any input. Conversely, if the inner parser succeeds (i.e. produces no error), it returns a
/// failure (`ParseError::Empty`).
///
/// **WARNING:** If you intend to allow the child to call this combinator (i.e. if the child parser contains the parent
/// in its recursive definitions), it is **highly recommended** to wrap a `ParseReportAll` instance in a caching
/// combinator (such as [`CachedComb`]) with a dedicated cache key. In cases where the child never calls the parent,
/// such wrapping is not necessary. However, when the child does invoke this combinator, failure to cache may result in
/// non‑linear or infinite parse times.
///
/// In most cases, [`ParseReport`]—which only catches non‑recursive errors—is the superior diagnostic option.
/// Use `ParseReportAll` only when you explicitly need to report recursive errors as well.
///
/// [`CachedComb`]: crate::cache::CachedComb
/// [`ParseReport`]: crate::reporting::ParseReport
///
/// # Example
///
/// ```rust
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::cache::{CachedComb, BasicCache};
/// use pakerat_combinators::core::{Input, ParseError};
/// use pakerat_combinators::reporting::ParseReportAll;
/// use syn::buffer::TokenBuffer;
///
/// fn main() {
///     // Our base parser is an identifier parser.
///     let base_parser = IdentParser;
///     
///     // Wrap the base parser in ParseReportAll to catch both non‑recursive and recursive errors.
///     let report_all = ParseReportAll::new(base_parser);
///     
///     // If your inner parser (the child) might call this combinator recursively,
///     // it is highly recommended to wrap the report_all parser in a caching combinator with a dedicated cache key.
///     let reporting_parser = CachedComb::new(report_all, 0, "infinite loop bug");
///     
///     let tokens = "dummy".parse().unwrap();
///     let buffer = TokenBuffer::new2(tokens);
///     let input = Input::new(&buffer);
///     
///     // Ensure that the cache is sized sufficiently (here, 1 is used because key 0 is accessed).
///     let mut cache = BasicCache::<1, ParseError>::new();
///     
///     // Use the reporting parser. If the inner parser succeeds (i.e. no error occurs), then
///     // ParseReportAll returns a failure. Otherwise, it reports the error (whether non‑recursive or recursive).
///     match reporting_parser.parse(input, &mut cache) {
///         Ok((_remaining, error)) => {
///             println!("Reported error: {:?}", error);
///         },
///         Err(e) => {
///             println!("Unexpected success (inner parser matched): {:?}", e);
///         }
///     }
/// }
/// ```
pub struct ParseReportAll<INNER, T = (), O = T>
where
    INNER: Combinator<T, O>,
    T: Parsable,
    O: Parsable,
{
    pub inner: INNER,
    pub _phantom: PhantomData<(T, O)>,
}

impl<INNER, T, O> ParseReportAll<INNER, T, O>
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

impl<INNER, T, O> Combinator<ParseError, O> for ParseReportAll<INNER, T, O>
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
            // If the inner parser succeeds (i.e. produces no error), then report a failure.
            Ok(_) => Err(PakeratError::Regular(ParseError::Empty)),
            // If the inner parser fails with a regular error, report that error.
            Err(PakeratError::Regular(e)) => Ok((input, e)),
            // If the inner parser fails with a recursive error, also report that error.
            Err(PakeratError::Recursive(e)) => Ok((input, e)),
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
/// use pakerat_combinators::reporting::ParseMismatch;
/// use syn::buffer::TokenBuffer;
///
/// let tokens = "dummy".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
/// let mut cache = BasicCache::<0>::new();
///
/// let mismatcher = ParseMismatch::new(IdentParser, Expected::Text("a literal"));
/// let _ = mismatcher.parse(input, &mut cache);
/// ```
pub struct ParseMismatch<INNER, T = (), O = T>
where
    INNER: Combinator<T, O>,
    T: Parsable,
    O: Parsable,
{
    pub inner: INNER,
    pub expected: Expected,
    pub _phantom: PhantomData<(T, O)>,
}

impl<INNER, T, O> ParseMismatch<INNER, T, O>
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

impl<INNER, T, O> Combinator<ParseError, O> for ParseMismatch<INNER, T, O>
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
/// use pakerat_combinators::reporting::{ParseMismatch, CheckError};
/// use syn::buffer::TokenBuffer;
/// use std::marker::PhantomData;
///
/// let tokens = "identifier".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
/// let mut cache = BasicCache::<0>::new();
///
/// // Create a parser that expects a literal but finds an identifier.
/// let mismatcher = ParseMismatch::new(IdentParser, Expected::Text("a literal"));
///
/// // Wrap it in CheckError to turn the mismatch into a raised error.
/// let raise = CheckError {
///     inner: mismatcher,
///     _phantom: PhantomData,
/// };
///
/// let result = raise.parse(input, &mut cache);
///
/// // Since the input is an identifier, ParseMismatch will succeed with an error,
/// // which CheckError should then raise.
/// assert!(matches!(result, Err(PakeratError::Regular(ParseError::Simple(_)))));
/// ```
pub struct CheckError<INNER,O> 
where INNER:Combinator<ParseError,O>,O:Parsable
{
    pub inner: INNER,
    pub _phantom: PhantomData<O>,
}

impl<INNER,O> Combinator<(),O> for CheckError<INNER,O>
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