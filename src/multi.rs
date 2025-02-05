use crate::combinator::CombinatorExt;
use crate::cache::DynCache;
use crate::combinator::BorrowParse;
use crate::combinator::PakeratError;
use crate::combinator::{Combinator, Pakerat};
use crate::core::Expected;
use crate::core::Found;
use crate::core::Input;
use crate::core::Mismatch;
use crate::core::ParseError;

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
/// use pakerat_combinators::core::Input;
/// use syn::buffer::TokenBuffer;
/// use std::marker::PhantomData;
///
/// let tokens = "{ my_var }".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
///
/// let my_parser = Wrapped {
///     wrapper: DelParser(Delimiter::Brace),
///     inner: IdentParser,
///     _phantom: PhantomData,
/// };
///
/// let mut cache  = BasicCache::<0>::new();
/// let (_, parsed_ident) = my_parser.parse(input, &mut cache).unwrap();
/// assert_eq!(parsed_ident.to_string(), "my_var");
/// ```
pub struct Wrapped<INNER, WRAPPER, T: BorrowParse = (), O = T>
where
    INNER: Combinator<T, O>,
    //'static resolves like Input<'_>
    WRAPPER: Combinator<Input<'static>, O>,

    O: BorrowParse,
{
    ///finds the start for the inside parser
    pub wrapper: WRAPPER,
    ///main parser that returns the final output
    pub inner: INNER,
    ///used so we can have generics
    pub _phantom: PhantomData<(T, O)>,
}

impl<INNER, WRAPPER, T, O> Combinator<T, O> for Wrapped<INNER, WRAPPER, T, O>
where
    WRAPPER: Combinator<Input<'static>, O>,
    INNER: Combinator<T, O>,
    O: BorrowParse,
    T: BorrowParse,
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, T::Output<'a>)> {
        let (next, inner_result) = self.wrapper.parse(input, cache)?;
        let (remaining, final_result) = self.inner.parse(inner_result, cache)?;

        if !remaining.eof() {
            return Err(PakeratError::Regular(ParseError::Simple(Mismatch {
                actual: Found::end_of(remaining),
                expected: Expected::Text("expected one of '})]' or EOF"),
            })));
        }

        Ok((next, final_result))
    }

    fn parse_ignore<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<Input<'a>> {
        let (next, inner_result) = self.wrapper.parse(input, cache)?;
        let remaining = self.inner.parse_ignore(inner_result, cache)?;

        if !remaining.eof() {
            return Err(PakeratError::Regular(ParseError::Simple(Mismatch {
                actual: Found::end_of(remaining),
                expected: Expected::Text("expected one of '})]' or EOF"),
            })));
        }

        Ok(next)
    }
}

impl<INNER, WRAPPER, T, O> Wrapped<INNER, WRAPPER, T, O>
where
    WRAPPER: Combinator<Input<'static>, O>,
    INNER: Combinator<T, O>,
    O: BorrowParse,
    T: BorrowParse,
{
    pub fn new(wrapper: WRAPPER, inner: INNER) -> Self {
        Self {
            wrapper,
            inner,
            _phantom: PhantomData,
        }
    }
}

/// This struct attempts to parse an optional occurrence of an inner parser.
///
/// If the inner parser fails with a `Regular` error, `Maybe` will return `None` instead of failing.
/// If the inner parser fails with a `Recursive` error, the error is propagated.
///
/// # Example Usage
/// ```rust
/// use pakerat_combinators::multi::Maybe;
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::cache::BasicCache;
/// use pakerat_combinators::core::Input;
/// use syn::buffer::TokenBuffer;
/// use std::marker::PhantomData;
///
/// let tokens = "optional_var".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
/// let my_parser = Maybe::new(IdentParser);
///
/// let mut cache = BasicCache::<0>::new();
/// let (_, parsed_ident) = my_parser.parse(input, &mut cache).unwrap();
/// assert_eq!(parsed_ident.unwrap().to_string(), "optional_var");
/// ```
///
pub struct Maybe<INNER, T = (), O = T>
where
    INNER: Combinator<T, O>,
    T: BorrowParse,
    O: BorrowParse,
{
    pub inner: INNER,
    /// Used so we can have generics
    pub _phantom: PhantomData<(T, O)>,
}

impl<INNER, T, O> Combinator<Option<T>, O> for Maybe<INNER, T, O>
where
    O: BorrowParse,
    T: BorrowParse,
    INNER: Combinator<T, O>,
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, Option<T::Output<'a>>)> {
        match self.inner.parse(input, cache) {
            Ok((new_input, x)) => Ok((new_input, Some(x))),
            Err(e) => match e {
                PakeratError::Regular(_) => Ok((input, None)),
                PakeratError::Recursive(_) => Err(e),
            },
        }
    }

    fn parse_ignore<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<Input<'a>> {
        match self.inner.parse_ignore(input, cache) {
            Ok(new_input) => Ok(new_input),
            Err(e) => match e {
                PakeratError::Regular(_) => Ok(input),
                PakeratError::Recursive(_) => Err(e),
            },
        }
    }
}

impl<INNER, T, O> Maybe<INNER, T, O>
where
    INNER: Combinator<T, O>,
    O: BorrowParse,
    T: BorrowParse,
{
    pub fn new(inner: INNER) -> Self {
        Maybe {
            inner,
            _phantom: PhantomData,
        }
    }
}

/// This struct parses zero or more occurrences of an inner parser.
///
/// It keeps collecting results until the inner parser fails with a `Regular` error.
/// If the inner parser fails with a `Recursive` error, the error is propagated.
///
/// # Example Usage
/// ```rust
/// use pakerat_combinators::multi::Many0;
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::cache::BasicCache;
/// use pakerat_combinators::core::Input;
/// use syn::buffer::TokenBuffer;
/// use std::marker::PhantomData;
///
/// let tokens = "var1 var2 var3".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
/// let my_parser = Many0::new(IdentParser);
///
/// let mut cache = BasicCache::<0>::new();
/// let (_, parsed_idents) = my_parser.parse(input, &mut cache).unwrap();
/// assert_eq!(parsed_idents.len(), 3);
/// ```
pub struct Many0<INNER, T = (), O = T>
where
    INNER: Combinator<T, O>,
    O: BorrowParse,
    T: BorrowParse,
{
    pub inner: INNER,
    ///used so we can have generics
    pub _phantom: PhantomData<(T, O)>,
}

impl<INNER, T, O> Combinator<Vec<T>, O> for Many0<INNER, T, O>
where
    O: BorrowParse,
    T: BorrowParse,
    INNER: Combinator<T, O>,
{
    fn parse<'a>(
        &self,
        mut input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, Vec<T::Output<'a>>)> {
        let mut vec = Vec::new();
        loop {
            match self.inner.parse(input, cache) {
                Ok((new_input, x)) => {
                    input = new_input;
                    vec.push(x);
                }
                Err(e) => {
                    return match e {
                        PakeratError::Regular(_) => Ok((input, vec)),
                        PakeratError::Recursive(_) => Err(e),
                    }
                }
            }
        }
    }
    fn parse_ignore<'a>(
        &self,
        mut input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<Input<'a>> {
        loop {
            match self.inner.parse(input, cache) {
                Ok((new_input, _x)) => {
                    input = new_input;
                }
                Err(e) => {
                    return match e {
                        PakeratError::Regular(_) => Ok(input),
                        PakeratError::Recursive(_) => Err(e),
                    }
                }
            }
        }
    }
}

impl<INNER, T, O> Many0<INNER, T, O>
where
    INNER: Combinator<T, O>,
    O: BorrowParse,
    T: BorrowParse,
{
    pub fn new(inner: INNER) -> Self {
        Many0 {
            inner,
            _phantom: PhantomData,
        }
    }
}

/// This struct parses one or more occurrences of an inner parser.
///
/// It behaves like `Many0` but ensures at least one successful parse before stopping.
/// If the first attempt fails, `Many1` returns an error.
///
/// # Example Usage
/// ```rust
/// use pakerat_combinators::multi::Many1;
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::core::Input;
/// use pakerat_combinators::cache::BasicCache;
/// use syn::buffer::TokenBuffer;
/// use std::marker::PhantomData;
///
/// let tokens = "var1 var2 var3".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
///
/// let my_parser = Many1::new(IdentParser);
/// let input = Input::new(&buffer);
///
/// let mut cache = BasicCache::<0>::new();
/// let (_, parsed_idents) = my_parser.parse(input, &mut cache).unwrap();
/// assert_eq!(parsed_idents.len(), 3);
/// ```
pub struct Many1<INNER, T = (), O = T>
where
    INNER: Combinator<T, O>,
    T: BorrowParse,
    O: BorrowParse,
{
    pub inner: INNER,
    ///used so we can have generics
    pub _phantom: PhantomData<(T, O)>,
}

impl<INNER, T, O> Combinator<Vec<T>, O> for Many1<INNER, T, O>
where
    O: BorrowParse,
    T: BorrowParse,

    INNER: Combinator<T, O>,
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, Vec<T::Output<'a>>)> {
        let (mut input, first) = self.inner.parse(input, cache)?;
        let mut vec = vec![first];
        loop {
            match self.inner.parse(input, cache) {
                Ok((new_input, x)) => {
                    input = new_input;
                    vec.push(x);
                }
                Err(e) => {
                    return match e {
                        PakeratError::Regular(_) => Ok((input, vec)),
                        PakeratError::Recursive(_) => Err(e),
                    }
                }
            }
        }
    }
    fn parse_ignore<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<Input<'a>> {
        let (mut input, _first) = self.inner.parse(input, cache)?;
        loop {
            match self.inner.parse(input, cache) {
                Ok((new_input, _x)) => {
                    input = new_input;
                }
                Err(e) => {
                    return match e {
                        PakeratError::Regular(_) => Ok(input),
                        PakeratError::Recursive(_) => Err(e),
                    }
                }
            }
        }
    }
}

impl<INNER, T, O> Many1<INNER, T, O>
where
    INNER: Combinator<T, O>,
    T: BorrowParse,
    O: BorrowParse,
{
    pub fn new(inner: INNER) -> Self {
        Many1 {
            inner,
            _phantom: PhantomData,
        }
    }
}

/// This parser simply discards the output returning a ().
///
/// It attempts to avoid allocating the output using see [`Combinator::parse_ignore`] for a version that discards output.
///
/// # Example Usage
/// ```rust
/// use pakerat_combinators::multi::Ignore;
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::core::Input;
/// use pakerat_combinators::cache::BasicCache;
/// use syn::buffer::TokenBuffer;
/// use std::marker::PhantomData;
///
/// let tokens = "optional_var".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
/// let my_parser = Ignore::new(IdentParser);
///
/// let mut cache = BasicCache::<0>::new();
/// let (_cursor, ()) = my_parser.parse(input, &mut cache).unwrap();
/// ```
pub struct Ignore<INNER, T = (), O = T>
where
    INNER: Combinator<T, O>,
    O: BorrowParse,
    T: BorrowParse,
{
    pub inner: INNER,
    ///used so we can have generics
    pub _phantom: PhantomData<(T, O)>,
}

impl<INNER, T, O> Combinator<(), O> for Ignore<INNER, T, O>
where
    O: BorrowParse,
    T: BorrowParse,

    INNER: Combinator<T, O>,
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, ())> {
        let c = self.inner.parse_ignore(input, cache)?;
        Ok((c, ()))
    }
}

impl<INNER, T, O> Ignore<INNER, T, O>
where
    INNER: Combinator<T, O>,
    T: BorrowParse,
    O: BorrowParse,
{
    pub fn new(inner: INNER) -> Self {
        Ignore {
            inner,
            _phantom: PhantomData,
        }
    }
}

/// A parser that recognizes a portion of the input and returns it as an `Input`.
///
/// This is useful for separating recognition from validation. For example,
/// you can extract a sequence of tokens and later process them separately,
/// allowing detailed error collection.
///
/// See [`multi::Recognize`] for a combinator that applies this pattern to repeated parsing.
///
/// # Example Usage
/// ```rust
/// use pakerat_combinators::multi::{Recognize, Many0,Maybe,Pair};
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::{SpecificPunct,IdentParser,AnyParser};
/// use pakerat_combinators::core::Input;
/// use pakerat_combinators::cache::{BasicCache,DynCache};
/// use syn::buffer::TokenBuffer;
///
/// let tokens = "var1; var2 name ; *;".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
/// // contrived parser
/// let parser = Many0::new(Recognize::new(Pair::new(Pair::new(AnyParser,Maybe::new(IdentParser)), SpecificPunct(';'))));
///
/// //check if the first token is a name
/// fn is_valid<'a>(input:Input<'a>,cache: &mut dyn DynCache<'a>) -> bool{
///     if let Ok(_) = IdentParser.parse(input,cache){
///         true
///     }
///     else{
///         false
///     }
///  }
/// let mut cache = BasicCache::<0>::new();
/// let (_cursor, recognized_inputs) = parser.parse(input, &mut cache).unwrap();
///
/// // Now, we can validate the recognized names separately.
/// let invalid_names: Vec<_> = recognized_inputs
///     .iter()
///     .filter(|segment| !is_valid(**segment, &mut cache)) // Replace `is_valid_name` with actual validation logic
///     .collect();
///
/// assert_eq!(invalid_names.len(), 1); // Only 1 statment started with punctioation
/// ```
pub struct Recognize<INNER, T, O = T>
where
    INNER: Combinator<T, O>,
    O: BorrowParse,
    T: BorrowParse,
{
    pub inner: INNER,
    pub _phantom: PhantomData<(T, O)>,
}

impl<INNER, T, O> Combinator<Input<'static>, O> for Recognize<INNER, T, O>
where
    INNER: Combinator<T, O>,
    O: BorrowParse,
    T: BorrowParse,
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, Input<'a>)> {
        let recognized = self.inner.parse_recognize(input, cache)?;
        Ok(recognized)
    }
}

impl<INNER, T, O> Recognize<INNER, T, O>
where
    INNER: Combinator<T, O>,
    O: BorrowParse,
    T: BorrowParse,
{
    pub fn new(inner: INNER) -> Self {
        Recognize {
            inner,
            _phantom: PhantomData,
        }
    }
}


/// A combinator that tries `A` first, then falls back to `B` if `A` fails.
///
/// This combinator does **not** provide a good error message!  
/// If both `A` and `B` fail, it **only returns the error from `B`**,  
/// rather than a meaningful message that explains what was expected.  
///
/// This is usually fixed by using [`ErrorWrapper`] right after to provide better error messages.
///
/// This struct is used **internally** as a building block for [`one_of!`]  
/// to ensure optimal static dispatch. It is generally not recommended for direct use.
///
/// [`ErrorWrapper`]: crate::multi::ErrorWrapper  
/// [`one_of!`]: crate::one_of
/// # Example
/// ```rust
/// use pakerat_combinators::multi::{OrLast,Ignore};
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::basic_parsers::LiteralParser;
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::cache::BasicCache;
/// use pakerat_combinators::core::Input;
/// use syn::buffer::TokenBuffer;
///
/// let tokens = "my_var rest".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
/// let parser = OrLast {
///     a: Ignore::new(IdentParser),
///     b: Ignore::new(LiteralParser),
///     _phantom: std::marker::PhantomData,
/// };
///
/// let mut cache = BasicCache::<0>::new();
/// let next = parser.parse_ignore(input, &mut cache).unwrap();
/// assert_eq!(next.span().source_text(), Some("rest".to_string()));
/// ```
pub struct OrLast<A, B, T = (), O = T>
where
    A: Combinator<T, O>,
    T: BorrowParse,
    B: Combinator<T, O>,
    O: BorrowParse,
{
    ///first element
    pub a: A,
    ///second element
    pub b: B,
    pub _phantom: PhantomData<(T, O)>,
}

impl<A, B, T, O> Combinator<T, O> for OrLast<A, B, T, O>
where
    A: Combinator<T, O>,
    T: BorrowParse,
    B: Combinator<T, O>,
    O: BorrowParse,
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, T::Output<'a>)> {
        match self.a.parse(input, cache) {
            ok @ Ok(_) => ok,
            Err(PakeratError::Recursive(e)) => Err(PakeratError::Recursive(e)),
            Err(PakeratError::Regular(_)) => self.b.parse(input, cache),
        }
    }

    fn parse_ignore<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<Input<'a>> {
        match self.a.parse_ignore(input, cache) {
            ok @ Ok(_) => ok,
            Err(PakeratError::Recursive(e)) => Err(PakeratError::Recursive(e)),
            Err(PakeratError::Regular(_)) => self.b.parse_ignore(input, cache),
        }
    }
}
impl<A, B, T, O> OrLast<A, B, T, O>
where
    A: Combinator<T, O>,
    T: BorrowParse,
    B: Combinator<T, O>,
    O: BorrowParse,
{
    pub fn new(a: A, b: B) -> Self {
        OrLast {
            a,
            b,
            _phantom: PhantomData,
        }
    }
}

/// Wraps a parser to provide a custom error message if parsing fails.
/// The returned error is a [`Mismatch`] with the expected field as text.
/// Note that [`PakeratError::Recursive`] is not affected by this.
///
/// This combinator helps in getting a clear error message.
/// It is used internally by [`one_of!`] to ensure meaningful errors.
///
/// [`PakeratError::Recursive`]: crate::combinator::PakeratError::Recursive
/// # Example
/// ```rust
/// use pakerat_combinators::multi::ErrorWrapper;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::combinator::{Combinator, PakeratError};
/// use pakerat_combinators::cache::BasicCache;
/// use pakerat_combinators::core::{Input, ParseError};
/// use syn::buffer::TokenBuffer;
///
/// let tokens = "123".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
/// let parser = ErrorWrapper {
///     parser: IdentParser,
///     expected: "a name",
///     _phantom: std::marker::PhantomData,
/// };
///
/// let mut cache = BasicCache::<0>::new();
/// let result = parser.parse(input, &mut cache);
///
/// match result {
///     Err(PakeratError::Regular(e)) => {
///         let msg = e.to_string();
///         assert_eq!(msg, "Expected a name but found \"123\"");
///     }
///     _ => panic!("Expected a `PakeratError::Regular` with the correct error text"),
/// }
/// ```
pub struct ErrorWrapper<P, T = (), O = T>
where
    P: Combinator<T, O>,
    T: BorrowParse,
    O: BorrowParse,
{
    /// The internal parser to be wrapped.
    pub parser: P,
    /// The custom error message to be used if parsing fails.
    pub expected: &'static str,
    /// Phantom data to let us do generics
    pub _phantom: PhantomData<(T, O)>,
}

impl<P, T, O> Combinator<T, O> for ErrorWrapper<P, T, O>
where
    P: Combinator<T, O>,
    T: BorrowParse,
    O: BorrowParse,
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, T::Output<'a>)> {
        match self.parser.parse(input, cache) {
            Ok((next_input, result)) => Ok((next_input, result)),
            Err(PakeratError::Recursive(e)) => Err(PakeratError::Recursive(e)),
            Err(PakeratError::Regular(_)) => Err(PakeratError::Regular(ParseError::Simple(
                Mismatch{
                    actual:Found::start_of(input),
                    expected:Expected::Text(self.expected),
                }
            ))),
        }
    }

    fn parse_ignore<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<Input<'a>> {
        match self.parser.parse_ignore(input, cache) {
            Ok(next_input) => Ok(next_input),
            Err(PakeratError::Recursive(e)) => Err(PakeratError::Recursive(e)),
            Err(PakeratError::Regular(_)) => Err(PakeratError::Regular(ParseError::Simple(
                Mismatch{
                    actual:Found::start_of(input),
                    expected:Expected::Text(self.expected),
                }
            ))),
        }
    }
}

impl<P, T, O> ErrorWrapper<P, T, O>
where
    P: Combinator<T, O>,
    T: BorrowParse,
    O: BorrowParse,
{
    pub fn new(parser: P, expected: &'static str) -> Self {
        ErrorWrapper {
            parser,
            expected,
            _phantom: PhantomData,
        }
    }
}

/// Creates a statically dispatched `OneOf` parser from arbitrary input [`Combinator`]s.
///
/// This macro generates a chain of [`OrLast`] parsers, then wraps it with [`ErrorWrapper`].
///
/// The provided parsers must share an output type. (If this is an issue try making the output an enum)
///The easiest way to ensure this is by using [`Ignore`] to make the output `()`.
///
/// ### Performance notes
/// This entire thing is statically compiled to become essentially a tuple on the stack.
/// This is nice for runtime speeds but terible for compile times.
/// Consider the tradeoffs to using [`OneOf`]
///
///
/// # Example
/// ```rust
/// use pakerat_combinators::one_of;
/// use pakerat_combinators::multi::Ignore;
/// use pakerat_combinators::basic_parsers::{IdentParser, PunctParser, IntParser};
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::cache::BasicCache;
/// use pakerat_combinators::core::Input;
/// use syn::buffer::TokenBuffer;
///
/// let tokens = "my_var rest".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
/// let parser = one_of!("an identifier, an integer, or punctuation",
///     Ignore::new(IdentParser),
///     Ignore::new(IntParser),
///     Ignore::new(PunctParser)
/// );
///
/// let mut cache = BasicCache::<0>::new();
/// let next = parser.parse_ignore(input, &mut cache).unwrap();
/// assert_eq!(next.span().source_text(), Some("rest".to_string()));
/// ```
///
/// ## ⚠ **Potential Pitfall: Ordering Matters!**
/// `one_of!` **selects the first parser that succeeds**, meaning that if an earlier parser is too permissive,  
/// later parsers may **never get a chance to execute**.
///
/// - If `Maybe::new(IdentParser)` is **first**, it **always matches** (even when empty),
///   preventing `IntParser` or `PunctParser` from ever running.
/// - **Solution:** **Order your parsers carefully** to avoid unintentional behavior.
///
/// ### **Example: Parser Ordering Issue**
///
/// ```rust
/// use pakerat_combinators::one_of;
/// use pakerat_combinators::multi::{Ignore, Maybe};
/// use pakerat_combinators::basic_parsers::{IdentParser, PunctParser, IntParser};
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::cache::BasicCache;
/// use pakerat_combinators::core::Input;
/// use syn::buffer::TokenBuffer;
///
/// let tokens = "123 rest".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
/// // ❌ The first parser (Maybe::new(IdentParser)) **always matches**, so IntParser and PunctParser are never checked.
/// let parser = one_of!("expected an identifier, an integer, or punctuation",
///     Ignore::new(Maybe::new(IdentParser)), // <-- This **always matches**, so the next parsers are ignored.
///     Ignore::new(IntParser),  // <-- Never executed.
///     Ignore::new(PunctParser) // <-- Never executed.
/// );
///
/// let mut cache = BasicCache::<0>::new();
/// let next = parser.parse_ignore(input, &mut cache).unwrap();
///
/// // Since `Maybe(IdentParser)` matched, the input **did not advance** as expected.
/// assert_eq!(next.span().source_text(), Some("123".to_string()));
/// ```
///
/// ## **🔧 How to Fix This Issue**
///
/// **To ensure `IntParser` and `PunctParser` get checked**, place `Maybe` **after** more restrictive parsers:
///
/// ```rust,ignore
/// let parser = one_of!("expected an identifier, an integer, or punctuation",
///     Ignore::new(IntParser),   // <-- Tries to match an integer first.
///     Ignore::new(PunctParser), // <-- Tries punctuation next.
///     Ignore::new(Maybe::new(IdentParser)) // <-- Only tries identifier if the first two fail.
/// );
/// ```
///
/// [`OrLast`]: crate::multi::OrLast
/// [`ErrorWrapper`]: crate::multi::ErrorWrapper
#[macro_export]
macro_rules! one_of {
    ($err:expr, $first:expr $(, $rest:expr)+ $(,)?) => {
        $crate::multi::ErrorWrapper {
            parser: $crate::__one_of_internal!($first $(, $rest)+),
            expected: $err,
            _phantom: std::marker::PhantomData,
        }
    };
}
pub use one_of;

/// This macro is used internally by `one_of!` to construct an `OrLast` chain.
///
/// **Users should not call this macro directly.**
#[macro_export]
macro_rules! __one_of_internal {
    ($first:expr, $second:expr $(, $rest:expr)*) => {
        $crate::multi::OrLast {
            a: $first,
            b: $crate::__one_of_internal!($second $(, $rest)*),
            _phantom: std::marker::PhantomData,
        }
    };
    ($last:expr) => {
        $last
    };
}
/// A `OneOf` combinator that attempts multiple parsers in sequence.
/// On fail would return a [`Mismatch`] error
///
/// Unlike [`one_of!`], this combinator allows an arbitrary number of parsers
/// at runtime. However, all parsers **must be of the same type**, which often
/// requires dynamic dispatch via Rc<dyn [`Combinator`]>.
///
/// This introduces 2 levels of indirection which is not ideal.
///
/// [`one_of!`]: crate::one_of
///
/// # Example
///
/// ```rust
/// use proc_macro2::{Delimiter, TokenStream};
/// use std::{marker::PhantomData, rc::Rc};
/// use syn::buffer::TokenBuffer;
/// use pakerat_combinators::{
///     basic_parsers::{DelParser, IntParser},
///     combinator::Combinator,
///     core::Input,
///     multi::{OneOf,Wrapped},
///     cache::{BasicCache, FlexibleCache},
/// };
///
/// // Define input with an integer and a delimited integer
/// let tokens: TokenStream = "42 {99}".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
/// let mut cache = FlexibleCache::new();
///
/// // Create individual parsers
/// let int_parser = Rc::new(IntParser) as Rc<dyn Combinator<i64, ()>>;
/// let delimited_int_parser = Rc::new(Wrapped {
///     wrapper: DelParser(Delimiter::Brace),
///     inner: IntParser,
///     _phantom: PhantomData,
/// }) as Rc<dyn Combinator<_, _>>;
///
/// // Create OneOf parser with both alternatives
/// let one_of_parser = OneOf::new(vec![int_parser, delimited_int_parser].into_boxed_slice(), "an int or {int}");
///
/// // Parse first integer
/// let (remaining, parsed_int) = one_of_parser.parse(input, &mut cache).unwrap();
/// assert_eq!(parsed_int, 42);
///
/// // Parse delimited integer
/// let (_, parsed_del_int) = one_of_parser.parse(remaining, &mut cache).unwrap();
/// assert_eq!(parsed_del_int, 99);
///
/// //this bit is optional
/// //std::mem::drop(one_of_parser);
/// //unsafe{
/// //   let _ = Box::from_raw(ptr);
/// //}
/// ```
pub struct OneOf<P, T = (), O = T>
where
    P: Combinator<T, O>,
    T: BorrowParse,

    O: BorrowParse,
{
    /// A list of parsers of the **same type**, stored in a boxed slice.
    pub alternatives: Box<[P]>,
    /// A description of the expected part
    pub expected: &'static str,
    /// Phantom data to tie lifetimes and types together.
    pub _phantom: PhantomData<(T, O)>,
}

impl<P, T, O> Combinator<T, O> for OneOf<P, T, O>
where
    P: Combinator<T, O>,
    T: BorrowParse,
    O: BorrowParse,
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, T::Output<'a>)> {
        for alt in &*self.alternatives {
            match alt.parse(input, cache) {
                Ok(ok) => return Ok(ok),
                Err(PakeratError::Recursive(e)) => return Err(PakeratError::Recursive(e)),
                Err(PakeratError::Regular(_)) => {} // Try next parser
            }
        }
        Err(PakeratError::Regular(ParseError::Simple(
            Mismatch{
                actual:Found::start_of(input),
                expected:Expected::Text(self.expected),
            }
        )))
    }

    fn parse_ignore<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<Input<'a>> {
        for alt in &*self.alternatives {
            match alt.parse_ignore(input, cache) {
                Ok(ok) => return Ok(ok),
                Err(PakeratError::Recursive(e)) => return Err(PakeratError::Recursive(e)),
                Err(PakeratError::Regular(_)) => {} // Try next parser
            }
        }
        Err(PakeratError::Regular(ParseError::Simple(
            Mismatch{
                actual:Found::start_of(input),
                expected:Expected::Text(self.expected),
            }
        )))
    }
}

impl<Parser, T, O> OneOf<Parser, T, O>
where
    Parser: Combinator<T, O>,
    T: BorrowParse,
    O: BorrowParse,
{
    /// Creates a new `OneOf` parser.
    pub fn new(parsers: Box<[Parser]>, expected: &'static str) -> Self {
        OneOf {
            alternatives: parsers,
            expected,
            _phantom: PhantomData,
        }
    }
}

/// A `Pair` combinator that applies two parsers sequentially.
///
/// This combinator runs the first parser (`first`) and, if it succeeds,
/// applies the second parser (`second`) to the remaining input.
/// If both parsers succeed, it returns a tuple `(A, B)`, where:
/// - `A` is the output of the first parser.
/// - `B` is the output of the second parser.
///
/// This is useful when parsing structured data where elements appear in sequence.
///
/// # Example
///
/// ```rust
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::multi::Pair;
/// use pakerat_combinators::basic_parsers::{IdentParser, IntParser};
/// use pakerat_combinators::cache::BasicCache;
/// use pakerat_combinators::core::Input;
/// use std::marker::PhantomData;
/// use syn::buffer::TokenBuffer;
///
/// let tokens = "my_var 42".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
/// let my_parser = Pair {
///     first: IdentParser,
///     second: IntParser,
///     _phantom: PhantomData,
/// };
///
/// let mut cache = BasicCache::<0>::new();
/// let (_, (ident, number)) = my_parser.parse(input, &mut cache).unwrap();
/// assert_eq!(ident.to_string(), "my_var");
/// assert_eq!(number, 42);
/// ```
pub struct Pair<FIRST, SECOND, T1, T2, O>
where
    FIRST: Combinator<T1, O>,
    SECOND: Combinator<T2, O>,
    T1: BorrowParse,
    T2: BorrowParse,

    O: BorrowParse,
{
    /// First parser to apply.
    pub first: FIRST,
    /// Second parser to apply.
    pub second: SECOND,
    /// Used for generic type binding.
    pub _phantom: PhantomData<(T1, T2, O)>,
}

impl<FIRST, SECOND, T1, T2, O> Combinator<(T1, T2), O> for Pair<FIRST, SECOND, T1, T2, O>
where
    FIRST: Combinator<T1, O>,
    SECOND: Combinator<T2, O>,
    T1: BorrowParse,
    T2: BorrowParse,
    O: BorrowParse,
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, (T1::Output<'a>, T2::Output<'a>))> {
        let (next, first_result) = self.first.parse(input, cache)?;
        let (remaining, second_result) = self.second.parse(next, cache)?;

        Ok((remaining, (first_result, second_result)))
    }

    fn parse_ignore<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<Input<'a>> {
        let next = self.first.parse_ignore(input, cache)?;
        let remaining = self.second.parse_ignore(next, cache)?;

        Ok(remaining)
    }
}

impl<FIRST, SECOND, T1, T2, O> Pair<FIRST, SECOND, T1, T2, O>
where
    FIRST: Combinator<T1, O>,
    SECOND: Combinator<T2, O>,
    T1: BorrowParse,
    T2: BorrowParse,
    O: BorrowParse,
{
    pub fn new(first: FIRST, second: SECOND) -> Self {
        Pair {
            first,
            second,
            _phantom: PhantomData,
        }
    }
}




#[cfg(test)]
mod tests {
    use crate::cache::FlexibleCache;

    use super::*;
    use crate::basic_parsers::AnyDelParser;
    use crate::basic_parsers::IdentParser;
    use crate::basic_parsers::IntParser;
    use crate::basic_parsers::LiteralParser;
    use crate::basic_parsers::PunctParser;
    use crate::cache::BasicCache;
    use crate::macros::token_cursor;
    use proc_macro2::TokenStream;
    use std::collections::HashMap;
    use std::rc::Rc;
    use syn::buffer::TokenBuffer;

    use crate::one_of;

    use crate::basic_parsers::DelParser;

    use proc_macro2::Delimiter;

    #[test]
    fn test_oneof_parsing() {
        // Define input with an integer and a delimited integer
        let tokens: TokenStream = "42 {99}".parse().unwrap();
        let buffer = TokenBuffer::new2(tokens); // Leak the token buffer
        let input = Input::new(&buffer);
        let mut cache = FlexibleCache::new();

        // Create individual parsers
        let int_parser = Rc::new(IntParser) as Rc<dyn Combinator<i64, ()>>;
        let delimited_int_parser = Rc::new(Wrapped {
            wrapper: DelParser(Delimiter::Brace),
            inner: IntParser,
            _phantom: PhantomData,
        }) as Rc<dyn Combinator<_, _>>;

        // Create OneOf parser with both alternatives
        let one_of_parser = OneOf::new(
            vec![int_parser, delimited_int_parser].into_boxed_slice(),
            "Expected int or {int}",
        );

        // Parse first integer
        let (remaining, parsed_int) = one_of_parser.parse(input, &mut cache).unwrap();
        assert_eq!(parsed_int, 42_i64);

        // Parse delimited integer
        let (_, parsed_del_int) = one_of_parser.parse(remaining, &mut cache).unwrap();
        assert_eq!(parsed_del_int, 99_i64);
    }

    // Macro to safely create a `TokenBuffer` and `Input` with a proper lifetime.
    #[test]
    fn test_one_of_macro() {
        // ✅ **Case 1: Matching an Identifier**
        let tokens = "my_var rest".parse().unwrap();
        let buffer = TokenBuffer::new2(tokens);
        let input = Input::new(&buffer);

        let parser = one_of!(
            "an identifier, an integer, or punctuation",
            Ignore::new(IdentParser),
            Ignore::new(IntParser),
            Ignore::new(PunctParser)
        );

        let mut cache = BasicCache::<0>::new();
        let next = parser.parse_ignore(input, &mut cache).unwrap();
        assert_eq!(next.span().source_text(), Some("rest".to_string()));

        // ✅ **Case 2: Matching an Integer**
        let tokens = "123 rest".parse().unwrap();
        let buffer = TokenBuffer::new2(tokens);
        let input = Input::new(&buffer);

        let next = parser.parse_ignore(input, &mut cache).unwrap();
        assert_eq!(next.span().source_text(), Some("rest".to_string()));

        // ✅ **Case 3: Matching a Punctuation**
        let tokens = "+ rest".parse().unwrap();
        let buffer = TokenBuffer::new2(tokens);
        let input = Input::new(&buffer);

        let next = parser.parse_ignore(input, &mut cache).unwrap();
        assert_eq!(next.span().source_text(), Some("rest".to_string()));

        // ❌ **Case 4: No Match (Should Fail with a Custom Error)**
        let tokens = "\"\" rest".parse().unwrap();
        let buffer = TokenBuffer::new2(tokens);
        let input = Input::new(&buffer);

        let result = parser.parse(input, &mut cache);

        match result {
            Err(PakeratError::Regular(ParseError::Simple(
                Mismatch{actual: _,
                    expected:Expected::Text(msg)
                }))) => {
                assert_eq!(msg, "an identifier, an integer, or punctuation");
            }
            _ => panic!("Expected a `ParseError::Simple` with the correct error text"),
        }
    }

    #[test]
    fn test_lifetimes() {
        let parser: Maybe<_> = Maybe::new(Ignore::new(Maybe::new(IdentParser)));

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
        let parser = Maybe {
            inner: IdentParser,
            _phantom: PhantomData,
        };
        let mut cache = BasicCache::<0>::new();
        let (_, result) = parser.parse(buffer, &mut cache).unwrap();
        assert_eq!(result.unwrap().to_string(), "maybe_var");
    }

    #[test]
    fn test_maybe_parser_none() {
        token_cursor!(buffer, "123");
        let parser = Maybe {
            inner: IdentParser,
            _phantom: PhantomData,
        };
        let mut cache = BasicCache::<0>::new();
        let (_, result) = parser.parse(buffer, &mut cache).unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn test_many0_parser() {
        token_cursor!(buffer, "var1 var2 var3");
        let parser = Many0 {
            inner: IdentParser,
            _phantom: PhantomData,
        };
        let mut cache = BasicCache::<0>::new();
        let (_, result) = parser.parse(buffer, &mut cache).unwrap();
        assert_eq!(result.len(), 3);
    }

    #[test]
    fn test_many1_parser() {
        token_cursor!(buffer, "var1 var2 var3");
        let parser = Many1 {
            inner: IdentParser,
            _phantom: PhantomData,
        };
        let mut cache = BasicCache::<0>::new();
        let (_, result) = parser.parse(buffer, &mut cache).unwrap();
        assert_eq!(result.len(), 3);
    }

    #[test]
    fn test_many1_parser_fail() {
        token_cursor!(buffer, "");
        let parser = Many1 {
            inner: IdentParser,
            _phantom: PhantomData,
        };
        let mut cache = BasicCache::<0>::new();
        let result = parser.parse(buffer, &mut cache);
        assert!(result.is_err());
    }

    #[test]
    fn test_inside_delimited_ident() {
        // Create token Input from `{ my_var }`
        token_cursor!(buffer, "{ my_var }");

        // Combine them in Wrapped
        let inside_parser = Wrapped {
            wrapper: DelParser(Delimiter::Brace),
            inner: IdentParser,
            _phantom: PhantomData,
        };

        let mut cache: BasicCache<0> = HashMap::new();
        let result = inside_parser.parse(buffer, &mut cache);

        assert!(
            result.is_ok(),
            "Wrapped parser should successfully parse an identifier inside `{{}}`"
        );
        let (remaining, parsed_ident) = result.unwrap();
        assert_eq!(
            parsed_ident.to_string(),
            "my_var",
            "Parsed identifier should be 'my_var'"
        );
        assert!(remaining.eof(), "Remaining Input should be empty");
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

        assert!(
            result.is_ok(),
            "Wrapped parser should successfully parse a punctuation inside `()`"
        );
        let (remaining, parsed_punct) = result.unwrap();
        assert_eq!(
            parsed_punct.as_char(),
            '+',
            "Parsed punctuation should be `+`"
        );
        assert!(remaining.eof(), "Remaining Input should be empty");
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

        assert!(
            result.is_ok(),
            "Wrapped parser should successfully parse a literal inside any delimiter"
        );
        let (remaining, parsed_literal) = result.unwrap();
        assert_eq!(
            parsed_literal.to_string(),
            "\"Hello\"",
            "Parsed literal should be '\"Hello\"'"
        );
        assert!(remaining.eof(), "Remaining Input should be empty");
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

        assert!(
            result.is_err(),
            "Wrapped parser should fail when no `{{}}` is present"
        );
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

        assert!(
            result.is_err(),
            "Wrapped parser should fail when `{{}}` contains a number instead of an identifier"
        );
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

        assert!(
            result.is_err(),
            "Wrapped parser should fail when extra tokens exist inside `{{}}`"
        );
    }
}
