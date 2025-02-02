use crate::core::Found;
use crate::core::Expected;
use crate::core::Mismatch;
use crate::core::ParseError;
use crate::cache::FlexibleCache;
use crate::combinator::{Pakerat,Combinator};
use crate::cache::Cache;
use crate::combinator::PakeratError;
use crate::core::Input;

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
pub struct Wrapped<'b, INNER,WRAPPER,T =(), O=T, C = FlexibleCache<'b,T>>
where
    INNER: Combinator<'b, T, O,C>,
    WRAPPER: Combinator<'b, Input<'b>, O,C>,
    O: Clone, 
    C: Cache<'b, O>
{	
	///finds the start for the inside parser
    pub wrapper: WRAPPER,
    ///main parser that returns the final output
    pub inner: INNER,
    ///used so we can have generics
    pub _phantom: PhantomData<(Input<'b>, T, O,C)>,
}


impl<'a, INNER, WRAPPER, T, O, C> Combinator<'a, T, O,C> for Wrapped<'a, INNER, WRAPPER, T, O, C>
where
    WRAPPER: Combinator<'a, Input<'a>, O,C>,
    INNER: Combinator<'a, T, O,C>,
    O: Clone, 
    C: Cache<'a, O>
{
    fn parse(
        &self,
        input: Input<'a>,
        cache: &mut C,
    ) -> Pakerat<(Input<'a>, T)> {
        let (next, inner_result) = self.wrapper.parse(input, cache)?;
        let (remaining, final_result) = self.inner.parse(inner_result, cache)?;

        if !remaining.eof() {
            return Err(PakeratError::Regular(ParseError::Simple(
                Mismatch{
                    actual:Found::end_of(remaining),
                    expected:Expected::Text("expected one of '})]' or EOF")
                })))
        }

        Ok((next, final_result))
    }

    fn parse_ignore(
        &self,
        input: Input<'a>,
        cache: &mut C,
    ) -> Pakerat<Input<'a>> {
        let (next, inner_result) = self.wrapper.parse(input, cache)?;
        let remaining= self.inner.parse_ignore(inner_result, cache)?;

        if !remaining.eof() {
            return Err(PakeratError::Regular(ParseError::Simple(
                Mismatch{
                    actual:Found::end_of(remaining),
                    expected:Expected::Text("expected one of '})]' or EOF")
                })))
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
//
pub struct Maybe<'b, INNER,T =(), O=T, C = FlexibleCache<'b,T>>
where
    INNER: Combinator<'b, T, O,C>,
    O: Clone,
    C: Cache<'b, O>
{   
    pub inner: INNER,
    ///used so we can have generics
    pub _phantom: PhantomData<(Input<'b>, T, O,C)>,
}

impl<'a, INNER,T, O, C> Combinator<'a, Option<T>, O,C> for Maybe<'a, INNER,T, O, C> 
    where O: Clone, 
    C: Cache<'a, O>,
    INNER: Combinator<'a, T, O,C>,
{

fn parse(&self, input: Input<'a>, cache: &mut C) -> Pakerat<(Input<'a>, Option<T>)> { 
    match self.inner.parse(input,cache){
        Ok((new_input,x)) => Ok((new_input,Some(x))),
        Err(e) => match e {
            PakeratError::Regular(_) => Ok((input,None)),
            PakeratError::Recursive(_) => Err(e)
        }
    }
}
fn parse_ignore(&self, input: Input<'a>, cache: &mut C) -> Pakerat<Input<'a>> { 
    match self.inner.parse_ignore(input,cache){
        Ok(new_input) => Ok(new_input),
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
pub struct Many0<'b, INNER,T =(), O=T, C = FlexibleCache<'b,T>>
where
    INNER: Combinator<'b, T, O,C>,
    O: Clone, 
    C: Cache<'b, O>
{   
    pub inner: INNER,
    ///used so we can have generics
    pub _phantom: PhantomData<(Input<'b>, T, O,C)>,
}

impl<'a, INNER,T, O, C> Combinator<'a, Vec<T>, O,C> for Many0<'a, INNER,T, O, C> 
    where O: Clone, 
    C: Cache<'a, O>,
    INNER: Combinator<'a, T, O,C>,
{

fn parse(&self, mut input: Input<'a>, cache: &mut C) -> Pakerat<(Input<'a>, Vec<T>)> { 
    let mut vec = Vec::new();
    loop{
        match self.inner.parse(input,cache){
            Ok((new_input,x)) => {
                input=new_input;
                vec.push(x);
            },
            Err(e) => return match e{
                PakeratError::Regular(_)=> Ok((input,vec)),
                PakeratError::Recursive(_)=>Err(e)
            }
        }
    }
}
fn parse_ignore(&self, mut input: Input<'a>, cache: &mut C) -> Pakerat<Input<'a>> { 
    loop{
        match self.inner.parse(input,cache){
            Ok((new_input,_x)) => {
                input=new_input;
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
pub struct Many1<'b, INNER,T =(), O=T, C = FlexibleCache<'b>>
where
    INNER: Combinator<'b, T, O,C>,
    O: Clone, 
    C: Cache<'b, O>
{   
    pub inner: INNER,
    ///used so we can have generics
    pub _phantom: PhantomData<(Input<'b>, T, O,C)>,
}

impl<'a, INNER,T, O, C> Combinator<'a, Vec<T>, O,C> for Many1<'a, INNER,T, O, C> 
    where O: Clone, 
    C: Cache<'a, O>,
    INNER: Combinator<'a, T, O,C>,
{

fn parse(&self, input: Input<'a>, cache: &mut C) -> Pakerat<(Input<'a>, Vec<T>)> { 
    let (mut input,first) = self.inner.parse(input,cache)?;
    let mut vec = vec![first];
    loop{
        match self.inner.parse(input,cache){
            Ok((new_input,x)) => {
                input=new_input;
                vec.push(x);
            },
            Err(e) => return match e{
                PakeratError::Regular(_)=> Ok((input,vec)),
                PakeratError::Recursive(_)=>Err(e)
            }
        }
    }
}
fn parse_ignore(&self, input: Input<'a>, cache: &mut C) -> Pakerat<Input<'a>> { 
    let (mut input,_first) = self.inner.parse(input,cache)?;
    loop{
        match self.inner.parse(input,cache){
            Ok((new_input,_x)) => {
                input=new_input;
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
pub struct Ignore<'b, INNER,T =(), O=T, C = FlexibleCache<'b>>
where
    INNER: Combinator<'b, T, O,C>,
    O: Clone, 
    C: Cache<'b, O>
{   
    pub inner: INNER,
    ///used so we can have generics
    pub _phantom: PhantomData<(Input<'b>, T, O,C)>,
}

impl<'a, INNER,T, O, C> Combinator<'a, (), O,C> for Ignore<'a, INNER,T, O, C> 
    where O: Clone, 
    C: Cache<'a, O>,
    INNER: Combinator<'a, T, O,C>,
{

fn parse(&self, input: Input<'a>, cache: &mut C) -> Pakerat<(Input<'a>, ())> { 
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
pub struct OrLast<'a,A, B, T = (), O = T, C = FlexibleCache<'a, T>>
where
    A: Combinator<'a, T, O, C>,
    B: Combinator<'a, T, O, C>,
    O: Clone,
    C: Cache<'a, O>,
{   
    ///first element
    pub a: A,
    ///second element
    pub b: B,
    pub _phantom: PhantomData<(Input<'a>,T, O, C)>,
}

impl<'a, A, B, T, O, C> Combinator<'a, T, O, C> for OrLast<'a, A, B, T, O, C>
where
    A: Combinator<'a, T, O, C>,
    B: Combinator<'a, T, O, C>,
    O: Clone,
    C: Cache<'a, O>,
{
    fn parse(&self, input: Input<'a>, cache: &mut C) -> Pakerat<(Input<'a>, T)> {
        match self.a.parse(input, cache) {
            ok @ Ok(_) => ok,
            Err(PakeratError::Recursive(e)) => Err(PakeratError::Recursive(e)),
            Err(PakeratError::Regular(_)) => self.b.parse(input, cache),
        }
    }

    fn parse_ignore(&self, input: Input<'a>, cache: &mut C) -> Pakerat<Input<'a>> {
        match self.a.parse_ignore(input, cache) {
            ok @ Ok(_) => ok,
            Err(PakeratError::Recursive(e)) => Err(PakeratError::Recursive(e)),
            Err(PakeratError::Regular(_)) => self.b.parse_ignore(input, cache),
        }
    }
}
impl<'a, A, B, T, O, C> OrLast<'a, A, B, T, O, C>
where
    A: Combinator<'a, T, O, C>,
    B: Combinator<'a, T, O, C>,
    O: Clone,
    C: Cache<'a, O>,
{
    pub fn new(a:A,b:B) -> Self { OrLast{a,b,_phantom:PhantomData} }
}

/// Wraps a parser to provide a **custom error message** if parsing fails.
///
/// This combinator ensures that the user **always gets a clear error message** instead of an
/// ambiguous default one. This is used internally by `one_of!` to ensure meaningful errors.
///
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
///     err_msg: "expected an identifier",
///     _phantom: std::marker::PhantomData,
/// };
///
/// let mut cache = BasicCache::<0>::new();
/// let result = parser.parse(input, &mut cache);
///
/// match result {
///     Err(PakeratError::Regular(ParseError::Message(_, msg))) => {
///         assert_eq!(msg, "expected an identifier");
///     }
///     _ => panic!("Expected a `ParseError::Message` with the correct error text"),
/// }
/// ```
pub struct ErrorWrapper<'a, P, T = (), O = T, C = FlexibleCache<'a, T>>
where
    P: Combinator<'a, T, O, C>,
    O: Clone,
    C: Cache<'a, O>,
{
    /// The internal parser to be wrapped.
    pub parser: P,
    /// The custom error message to be used if parsing fails.
    pub err_msg: &'static str,
    /// Phantom data to tie lifetimes and types together.
    pub _phantom: PhantomData<(Input<'a>, T, O, C)>,
}

impl<'a, P, T, O, C> Combinator<'a, T, O, C> for ErrorWrapper<'a, P, T, O, C>
where
    P: Combinator<'a, T, O, C>,
    O: Clone,
    C: Cache<'a, O>,
{
    fn parse(&self, input: Input<'a>, cache: &mut C) -> Pakerat<(Input<'a>, T)> {
        match self.parser.parse(input, cache) {
            Ok((next_input, result)) => Ok((next_input, result)),
            Err(PakeratError::Recursive(e)) => Err(PakeratError::Recursive(e)),
            Err(PakeratError::Regular(_)) => {
                Err(PakeratError::Regular(ParseError::Message(input.span(), self.err_msg)))
            }
        }
    }

    fn parse_ignore(&self, input: Input<'a>, cache: &mut C) -> Pakerat<Input<'a>> {
        match self.parser.parse_ignore(input, cache) {
            Ok(next_input) => Ok(next_input),
            Err(PakeratError::Recursive(e)) => Err(PakeratError::Recursive(e)),
            Err(PakeratError::Regular(_)) => {
                Err(PakeratError::Regular(ParseError::Message(input.span(), self.err_msg)))
            }
        }
    }
}

impl<'a, P, T, O, C> ErrorWrapper<'a, P, T, O, C>
where
    P: Combinator<'a, T, O, C>,
    O: Clone,
    C: Cache<'a, O>,
{
    pub fn new(parser:P,err_msg: &'static str) -> Self{
        ErrorWrapper{parser,err_msg,_phantom:PhantomData}
    }
}

/// Creates an optimal **statically dispatched** `OneOf` parser using [`OrLast`] chains.
///
/// This macro generates the most efficient possible chain of parsers using [`OrLast`],
/// and **wraps the final result in [`ErrorWrapper`]** to ensure a **good error message**.
///
/// ## **Important Notes:**
/// - The provided parsers **must** share an output type.  
/// - The easiest way to ensure this is by using [`Ignore::new(Parser)`] to make the output `()`.  
/// - This macro **does not use dynamic dispatch**; it expands into a **fully static** chain.
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
/// let parser = one_of!("expected an identifier, an integer, or punctuation",
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
            err_msg: $err,
            _phantom: std::marker::PhantomData,
        }
    };
}

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
///
/// Unlike [`one_of!`], this combinator allows an arbitrary number of parsers
/// at runtime. However, all parsers **must be of the same type**, which often
/// requires dynamic dispatch via `Rc<dyn Combinator<'a, _, _, _>>`. 
/// The issue is that this binds the lifetime of the parser to the input.
/// If this is unacceptable, using [`one_of!`] or leaking then manually freeing the TokenBuffer can decouple the lifetimes.
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
/// let input = Input::new(Box::leak(Box::new(buffer))); // Leak the token buffer
/// let mut cache = FlexibleCache::new();
///
/// // Create individual parsers
/// let int_parser = Rc::new(IntParser) as Rc<dyn Combinator<i64, (), _>>;
/// let delimited_int_parser = Rc::new(Wrapped {
///     wrapper: DelParser(Delimiter::Brace),
///     inner: IntParser,
///     _phantom: PhantomData,
/// }) as Rc<dyn Combinator<_, _, _>>;
///
/// // Create OneOf parser with both alternatives
/// let one_of_parser = OneOf::new(vec![int_parser, delimited_int_parser].into_boxed_slice(), "Expected int or {int}");
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

pub struct OneOf<'a, P, T = (), O = T, C = FlexibleCache<'a, T>>
where
    P: Combinator<'a, T, O, C>,
    C: Cache<'a, O>,
    O:Clone,
{
    /// A list of parsers of the **same type**, stored in a boxed slice.
    pub alternatives: Box<[P]>,
    /// The error message returned if all alternatives fail.
    pub err_msg: &'static str,
    /// Phantom data to tie lifetimes and types together.
    pub _phantom: PhantomData<(Input<'a>, T, O, C)>,
}

impl<'a, P, T, O, C> Combinator<'a, T, O, C> for OneOf<'a, P, T, O, C>
where
    P: Combinator<'a, T, O, C>,
    O: Clone,
    C: Cache<'a, O>,
{
    fn parse(&self, input: Input<'a>, cache: &mut C) -> Pakerat<(Input<'a>, T)> {
        for alt in &*self.alternatives {
            match alt.parse(input, cache) {
                Ok(ok) => return Ok(ok),
                Err(PakeratError::Recursive(e)) => return Err(PakeratError::Recursive(e)),
                Err(PakeratError::Regular(_)) => {} // Try next parser
            }
        }
        Err(PakeratError::Regular(ParseError::Message(
            input.span(),
            self.err_msg,
        )))
    }

    fn parse_ignore(&self, input: Input<'a>, cache: &mut C) -> Pakerat<Input<'a>> {
        for alt in &*self.alternatives {
            match alt.parse_ignore(input, cache) {
                Ok(ok) => return Ok(ok),
                Err(PakeratError::Recursive(e)) => return Err(PakeratError::Recursive(e)),
                Err(PakeratError::Regular(_)) => {} // Try next parser
            }
        }
        Err(PakeratError::Regular(ParseError::Message(
            input.span(),
            self.err_msg,
        )))
    }
}

impl<'a, P, T, O, C> OneOf<'a, P, T, O, C>
where
    P: Combinator<'a, T, O, C>,
    O: Clone,
    C: Cache<'a, O>,
{
    /// Creates a new `OneOf` parser.
    ///
    /// Unlike [`one_of!`], the number of parsers **does not need to be known at compile time**.  
    /// However, all parsers **must be of the same type**.
    ///
    /// # Parameters:
    /// - `parsers`: A **boxed slice** of parsers of the **same type**.
    /// - `err_msg`: The custom error message used when parsing fails.
    ///
    /// **Tip:** If your parsers have different types, use **dynamic dispatch** with `Rc<dyn Combinator>`.
    pub fn new(parsers: Box<[P]>, err_msg: &'static str) -> Self {
        OneOf {
            alternatives: parsers,
            err_msg,
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
pub struct Pair<'b, FIRST, SECOND, T1, T2, O, C = FlexibleCache<'b, O>>
where
    FIRST: Combinator<'b, T1, O, C>,
    SECOND: Combinator<'b, T2, O, C>,
    O: Clone,
    C: Cache<'b, O>,
{
    /// First parser to apply.
    pub first: FIRST,
    /// Second parser to apply.
    pub second: SECOND,
    /// Used for generic type binding.
    pub _phantom: PhantomData<(Input<'b>, T1, T2, O, C)>,
}

impl<'a, FIRST, SECOND, T1, T2, O, C> Combinator<'a, (T1, T2), O, C>
    for Pair<'a, FIRST, SECOND, T1, T2, O, C>
where
    FIRST: Combinator<'a, T1, O, C>,
    SECOND: Combinator<'a, T2, O, C>,
    O: Clone,
    C: Cache<'a, O>,
{
    fn parse(
        &self,
        input: Input<'a>,
        cache: &mut C,
    ) -> Pakerat<(Input<'a>, (T1, T2))> {
        let (next, first_result) = self.first.parse(input, cache)?;
        let (remaining, second_result) = self.second.parse(next, cache)?;

        Ok((remaining, (first_result, second_result)))
    }

    fn parse_ignore(
        &self,
        input: Input<'a>,
        cache: &mut C,
    ) -> Pakerat<Input<'a>> {
        let next = self.first.parse_ignore(input, cache)?;
        let remaining = self.second.parse_ignore(next, cache)?;

        Ok(remaining)
    }
}


impl<'a, FIRST, SECOND, T1, T2, O, C>Pair<'a, FIRST, SECOND, T1, T2, O, C>
where
    FIRST: Combinator<'a, T1, O, C>,
    SECOND: Combinator<'a, T2, O, C>,
    O: Clone,
    C: Cache<'a, O>
{
    pub fn new(first:FIRST,second:SECOND) -> Self{
        Pair{first,second,_phantom:PhantomData}
    }
}

#[cfg(test)]
mod tests {

use std::rc::Rc;
use crate::basic_parsers::IntParser;
use crate::basic_parsers::IdentParser;
use crate::macros::token_cursor;
use proc_macro2::TokenStream;
use syn::buffer::TokenBuffer;
use super::*;
use crate::basic_parsers::LiteralParser;
use crate::basic_parsers::AnyDelParser;
use crate::basic_parsers::PunctParser;
use std::collections::HashMap;
use crate::cache::BasicCache;

    use crate::one_of;

    use crate::basic_parsers::DelParser;

use proc_macro2::Delimiter;

#[test]
fn test_oneof_parsing() {
    // Define input with an integer and a delimited integer
    let tokens: TokenStream = "42 {99}".parse().unwrap();
    let buffer = Box::leak(Box::new(TokenBuffer::new2(tokens))); // Leak the token buffer
    let ptr = buffer as *mut _;
    let input = Input::new(buffer); 
    let mut cache = FlexibleCache::new();

    // Create individual parsers
    let int_parser = Rc::new(IntParser) as Rc<dyn Combinator<i64, (), _>>;
    let delimited_int_parser = Rc::new(Wrapped {
        wrapper: DelParser(Delimiter::Brace),
        inner: IntParser,
        _phantom: PhantomData,
    }) as Rc<dyn Combinator<_, _, _>>;
    
    // Create OneOf parser with both alternatives
    let one_of_parser = OneOf::new(vec![int_parser, delimited_int_parser].into_boxed_slice(), "Expected int or {int}");
    
    // Parse first integer
    let (remaining, parsed_int) = one_of_parser.parse(input, &mut cache).unwrap();
    assert_eq!(parsed_int, 42 as i64);
    
    // Parse delimited integer
    let (_, parsed_del_int) = one_of_parser.parse(remaining, &mut cache).unwrap();
    assert_eq!(parsed_del_int, 99 as i64);

    // this bit is optional
    std::mem::drop(one_of_parser);
    unsafe{
        let _ = Box::from_raw(ptr);
    }
}

// Macro to safely create a `TokenBuffer` and `Input` with a proper lifetime.
#[test]
fn test_one_of_macro() {


    // ✅ **Case 1: Matching an Identifier**
    let tokens = "my_var rest".parse().unwrap();
    let buffer = TokenBuffer::new2(tokens);
    let input = Input::new(&buffer);

    let parser = one_of!("expected an identifier, an integer, or punctuation",
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
        Err(PakeratError::Regular(ParseError::Message(_, msg))) => {
            assert_eq!(msg, "expected an identifier, an integer, or punctuation");
        }
        _ => panic!("Expected a `ParseError::Message` with the correct error text"),
    }
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

        assert!(result.is_ok(), "Wrapped parser should successfully parse an identifier inside `{{}}`");
        let (remaining, parsed_ident) = result.unwrap();
        assert_eq!(parsed_ident.to_string(), "my_var", "Parsed identifier should be 'my_var'");
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

        assert!(result.is_ok(), "Wrapped parser should successfully parse a punctuation inside `()`");
        let (remaining, parsed_punct) = result.unwrap();
        assert_eq!(parsed_punct.as_char(), '+', "Parsed punctuation should be `+`");
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

        assert!(result.is_ok(), "Wrapped parser should successfully parse a literal inside any delimiter");
        let (remaining, parsed_literal) = result.unwrap();
        assert_eq!(parsed_literal.to_string(), "\"Hello\"", "Parsed literal should be '\"Hello\"'");
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
