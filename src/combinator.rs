use crate::core::Expected;
use crate::core::Found;
use crate::core::Mismatch;
use crate::cache::DynCache;
use crate::core::Input;
use crate::core::ParseError;
use proc_macro2::Delimiter;
use proc_macro2::Group;
use proc_macro2::Ident;
use proc_macro2::Literal;
use proc_macro2::Punct;
use proc_macro2::Span;
use proc_macro2::TokenTree;
use std::error::Error;
use std::marker::PhantomData;
use std::ops::Deref;
use syn::Lifetime;

///error type for handeling recursive parses.
///
///unlike the usual errors a recursive parse error should terminate the entire parse.
///
///these recursive errors fundementally mean there was an infinite loop in the program.
///
///miss reporting an error as regular can lead to weird caching behivior and wrong/unpredictble behivior.
///
///as well as program panics on bad parses (this was chosen over errors to avoid corupted states).
#[derive(Debug, Clone)]
pub enum PakeratError<E = ParseError>
where
    E: Clone + Error,
{
    ///these are the errors most user code should generate
    ///
    ///dont construct these from a recursive error
    Regular(E),

    ///when you encounter this avoid calling ANY other parsers on the state.
    ///
    ///and return a recursive error back
    Recursive(E),
}

impl<E: Error + std::clone::Clone> PakeratError<E> {
    pub fn inner(self) -> E {
        match self {
            PakeratError::Regular(e) => e,
            PakeratError::Recursive(e) => e,
        }
    }

    pub fn map<F: FnOnce(E) -> T, T: Error + Clone>(self, f: F) -> PakeratError<T> {
        match self {
            PakeratError::Regular(e) => PakeratError::Regular(f(e)),
            PakeratError::Recursive(e) => PakeratError::Recursive(f(e)),
        }
    }
}

impl From<PakeratError<syn::Error>> for PakeratError<ParseError> {
    fn from(e: PakeratError<syn::Error>) -> Self {
        e.map(|x| x.into())
    }
}

impl From<PakeratError> for syn::Error {
    fn from(e: PakeratError) -> Self {
        e.inner().into()
    }
}

///result type used for internal cache managment
pub type Pakerat<T, E = ParseError> = Result<T, PakeratError<E>>;

// Implement Clone when `E: Clone`
impl<E: PartialEq + Error + Clone> PartialEq for PakeratError<E> {
    fn eq(&self, other: &PakeratError<E>) -> bool {
        match (self, other) {
            (PakeratError::Regular(a), PakeratError::Regular(b)) => a == b,
            (PakeratError::Recursive(a), PakeratError::Recursive(b)) => a == b,
            _ => false,
        }
    }
}

/// A trait that defines the output type of a combinator.
///
/// This trait allows the output type to depend on the input's lifetime,
/// making it possible to represent parsed values that borrow from their source.
///
/// note that the type itself is entirly decorative, this shows up when you see Input<'static> which in fact has Output<'a>=Input<'a>.
pub trait Parsable {
    /// The output type produced by the combinator.
    ///
    /// - `'a` represents the lifetime of the input being parsed.
    /// - The output may be owned (`T::Output<'a> = T`) or borrow from input (`T::Output<'a> = Input<'a>`).
    type Output<'a>;
}

///this is the main reason we want it
impl Parsable for Input<'_> {
    type Output<'a> = Input<'a>;
}

macro_rules! impl_parsble {
    ($($t:ty),*) => {
        $(impl $crate::combinator::Parsable for $t {
            type Output<'a> = $t;
        })*
    };
}

// Implement `Parsable` for common types
impl_parsble!(
    (),
    u8,
    u16,
    u32,
    u64,
    u128,
    i8,
    i16,
    i32,
    i64,
    i128,
    f32,
    f64,
    char,
    bool,
    String
);
impl_parsble!(Ident, Punct, Literal, TokenTree, Group, Delimiter, Span, Lifetime);

impl<E> Parsable for PakeratError<E>
where
    E: Error + Clone + Parsable,
    for<'a> E::Output<'a>: Clone + std::error::Error, 
{
    type Output<'a> = PakeratError<E::Output<'a>>;
}



// Macro to implement Parsable for generic containers
macro_rules! impl_parsble_for_container {
    ($container:ident <T> $(, $extra:ty)?) => {
        impl<T: Parsable $(+ $extra)?> Parsable for $container<T> {
            type Output<'a> = $container<T::Output<'a>>;
        }
    };

}
impl_parsble_for_container!(Vec<T>);
impl_parsble_for_container!(Option<T>);
impl_parsble_for_container!(Box<T>);
impl_parsble_for_container!(Rc<T>);
impl_parsble_for_container!(Arc<T>);

impl<T:Parsable,const N:usize> Parsable for [T;N]{

type Output<'a> = [T::Output<'a>;N];
}

macro_rules! impl_parsble_for_array_container {
    ($container:ident <[T]> $(, $extra:ty)?) => {
        impl<T: Parsable $(+ $extra)?> Parsable for $container<[T]> {
            type Output<'a> = $container<[T::Output<'a>]>;
        }
    };

}
impl_parsble_for_array_container!(Box<[T]>);
impl_parsble_for_array_container!(Rc<[T]>);
impl_parsble_for_array_container!(Arc<[T]>);

impl<V: Parsable, E: Parsable> Parsable for Result<V, E> {
    type Output<'a> = Result<V::Output<'a>, E::Output<'a>>;
}

macro_rules! impl_parsble_for_tuples {
    ($( $T:ident ),*) => {
        impl<$( $T: Parsable ),*> Parsable for ($( $T, )*) {
            type Output<'a> = ($( $T::Output<'a>, )*);
        }
    };
}

// Implement for common tuple sizes
impl_parsble_for_tuples!(T1, T2);
impl_parsble_for_tuples!(T1, T2, T3);
impl_parsble_for_tuples!(T1, T2, T3, T4);
impl_parsble_for_tuples!(T1, T2, T3, T4, T5);
impl_parsble_for_tuples!(T1, T2, T3, T4, T5, T6);
impl_parsble_for_tuples!(T1, T2, T3, T4, T5, T6, T7);
impl_parsble_for_tuples!(T1, T2, T3, T4, T5, T6, T7, T8);
//if you somehow for some reason need more than 8 something is defintly goe very very wrong

/// A `Combinator` is a fundamental parser used throughout this crate.
///
/// These combinators are designed to behave similarly to closures; in fact, closures are also valid combinators.  
/// Combinators are usually combined together to form larger parsers.  
/// You will find more references to this [`multi`], along with code examples.
///
/// There is also a syntax sugar trait named [`CombinatorExt`] with useful methods like [`map`].
///
/// [`map`]: crate::combinator::CombinatorExt::map
/// [`multi`]: crate::multi
pub trait Combinator<T: Parsable = (), O: Parsable = T> {
    /// Parses the given input, utilizing the provided cache.
    ///
    /// Returns a [`Pakerat`] result containing the remaining input and the parsed output.
    fn parse<'a>(
        &self,
        input: Input<'a>,
        state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, T::Output<'a>)>;

    /// Parses the input while discarding the output.
    ///
    /// This method exists to avoid allocating memory for parses that are ignored.
    /// For the most parts users are not expected to implement this directly.
    fn parse_ignore<'a>(
        &self,
        input: Input<'a>,
        state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<Input<'a>> {
        let (ans, _) = self.parse(input, state)?;
        Ok(ans)
    }
}

/// We would ideally not need this, but Rust requires explicit implementations
// for trait objects due to its object safety rules.
macro_rules! impl_combinator_for_wrappers {
    ($wrapper:ty) => {
        impl<T, O> Combinator<T, O> for $wrapper
        where
            O: Parsable,
            T: Parsable,
        {
            fn parse<'a>(
                &self,
                input: Input<'a>,
                cache: &mut dyn DynCache<'a, O>,
            ) -> Pakerat<(Input<'a>, T::Output<'a>)> {
                (**self).parse(input, cache) // Delegate to the inner trait object
            }

            fn parse_ignore<'a>(
                &self,
                input: Input<'a>,
                cache: &mut dyn DynCache<'a, O>,
            ) -> Pakerat<Input<'a>> {
                (**self).parse_ignore(input, cache)
            }
        }
    };
}

use std::rc::Rc;
use std::sync::Arc;

impl_combinator_for_wrappers!(&dyn Combinator<T, O>);
impl_combinator_for_wrappers!(Box<dyn Combinator<T, O>>);
impl_combinator_for_wrappers!(Rc<dyn Combinator<T, O>>);
impl_combinator_for_wrappers!(Arc<dyn Combinator<T, O>>);

// We would ideally not need this, but Rust requires explicit implementations
// for trait objects due to its object safety rules.
macro_rules! impl_combinator_for_wrapper_p {
    ($wrapper:ty) => {
        impl<T, O, P> Combinator<T, O> for $wrapper
        where
            O: Parsable,
            T: Parsable,
            P: Combinator<T, O>,
        {
            fn parse<'a>(
                &self,
                input: Input<'a>,
                cache: &mut dyn DynCache<'a, O>,
            ) -> Pakerat<(Input<'a>, T::Output<'a>)> {
                P::parse(self, input, cache) // Delegate to the inner trait object
            }

            fn parse_ignore<'a>(
                &self,
                input: Input<'a>,
                cache: &mut dyn DynCache<'a, O>,
            ) -> Pakerat<Input<'a>> {
                P::parse_ignore(self, input, cache)
            }
        }
    };
}

// Implement for Rc<P> and Arc<P>
impl_combinator_for_wrapper_p!(Rc<P>);
// Uncomment if needed
// impl_combinator_for_wrapper_p!(Box<P>);

impl_combinator_for_wrapper_p!(Arc<P>);

/// Implementing for function-like types
impl<F, T, O> Combinator<T, O> for F
where
    F: for<'a> Fn(Input<'a>, &mut dyn DynCache<'a, O>) -> Pakerat<(Input<'a>, T::Output<'a>)>,
    O: Parsable,
    T: Parsable,
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, T::Output<'a>)> {
        (self)(input, state)
    }
}

#[test]
fn test_closures() {
    use crate::multi::Maybe;
    use std::marker::PhantomData;

    fn example_parser<'a>(input: Input<'a>, _state: &mut dyn DynCache) -> Pakerat<(Input<'a>, ())> {
        Ok((input, ()))
    }

    #[allow(dead_code)]
    fn dumb(_maybe: Maybe<&'static dyn Combinator>) {}

    let dumby2: Box<dyn Combinator> = Box::new(example_parser);
    let _maybe = Maybe::new(&*dumby2);
    let _maybe = Maybe {
        inner: dumby2,
        _phantom: PhantomData,
    };
}

#[test]
fn test_dyn_closure_combinator_error_mapping() {
    use crate::cache::FlexibleCache;
    use std::rc::Rc;
    use syn::buffer::TokenBuffer;

    // A simple parser that always fails with a Regular error
    fn failing_parser<'a>(
        input: Input<'a>,
        _state: &mut dyn DynCache<'a, ()>,
    ) -> Pakerat<(Input<'a>, ())> {
        Err(PakeratError::Regular(ParseError::Message(
            input.span(),
            "Inner parser error",
        )))
    }

    // Create token buffer first so it's dropped last
    let tokens = "test".parse().unwrap();
    let buffer = TokenBuffer::new2(tokens);

    // Explicitly define the closure with a for<'a> annotation
    let closure: &dyn for<'a> Fn(Input<'a>, &mut dyn DynCache<'a, ()>) -> Pakerat<(Input<'a>, ())> =
        &|input, cache| {
            failing_parser(input, cache).map_err(|e| {
                e.map(|e| {
                    let err: syn::Error = e.into(); // Explicitly create the `err` variable
                    let mut new_err = syn::Error::new(err.span(), "failed doing something");
                    new_err.combine(err); // Capture the original error
                    ParseError::Syn(new_err.into()) // Return the transformed error
                })
            })
        };

    // Convert the closure into a trait object that implements Combinator
    let error_mapping_combinator: Rc<dyn for<'a> Combinator<(), ()>> = Rc::new(closure);

    let mut cache = FlexibleCache::<()>::default();

    {
        // Run the parser
        let result = error_mapping_combinator.parse(Input::new(&buffer), &mut cache);

        // Verify that the error was transformed
        if let Err(PakeratError::Regular(e)) = result {
            assert!(e.to_string().contains("failed doing something"));
        } else {
            panic!("Expected an error but got a successful parse");
        }
    }
}

#[test]
fn test_leak2_safety() {
    use crate::basic_parsers::IdentParser;
    // Create a leaked parser
    let (leaked_parser, ptr): (RefParser<'_, IdentParser, proc_macro2::Ident, ()>, *mut IdentParser) = IdentParser.leak2();

    // Ensure that the pointer is non-null
    assert!(!ptr.is_null());

    assert_eq!(ptr as *const _, leaked_parser.inner as *const _);

    // SAFETY: We manually free the leaked memory.
    unsafe {
        drop(Box::from_raw(ptr));
    }
}


/// Extension trait for [`Combinator`] holding useful syntax sugar
/// see individual methods for more detail
pub trait CombinatorExt<T: Parsable = (), O: Parsable = T>: Combinator<T, O> {
    /// Creates a reference-based wrapper (`RefParser`) for the combinator.
    ///
    /// This allows a single combinator instance to be passed to multiple combinators
    /// that require references, avoiding ownership and borrowing issues.
    ///
    /// # Example
    /// ```rust
    /// use pakerat_combinators::combinator::{Combinator, CombinatorExt};
    /// use pakerat_combinators::multi::{Pair, Maybe};
    /// use pakerat_combinators::core::Input;
    /// use pakerat_combinators::cache::BasicCache;
    /// use pakerat_combinators::basic_parsers::IdentParser;
    ///
    /// let ident_parser = IdentParser; // A basic combinator.
    ///
    ///
    /// // Use the reference-based parser in different combinators.
    /// let pair_parser = Pair::new(ident_parser.as_ref(), ident_parser.as_ref());
    /// let maybe_parser = Maybe::new(ident_parser.as_ref());
    ///
    /// let mut cache = BasicCache::<0>::new();
    ///
    /// // Parse input using both combinators
    /// let _ = pair_parser.parse(Input::empty(), &mut cache);
    /// let _ = maybe_parser.parse(Input::empty(), &mut cache);
    /// ```
    fn as_ref(&self) -> RefParser<'_, Self, T, O>
    where
        Self: Sized,
    {
        RefParser {
            inner: self,
            _phantom: PhantomData,
        }
    }


    /// Constructs a box around this object then leaks it
    ///
    /// This allows the parser to be returned from a function with a reference that outlives the function scope,
    /// making it useful when a parser needs a `'static` reference
    ///
    /// # Example
    /// ```rust
    /// use pakerat_combinators::combinator::{Combinator, CombinatorExt, RefParser};
    /// use pakerat_combinators::multi::Pair;
    /// use pakerat_combinators::basic_parsers::IdentParser;
    /// use proc_macro2::Ident;
    ///
    /// // Function that constructs and returns a leaked parser.
    /// fn create_parser() -> &'static dyn Combinator<(Ident,Ident)> {
    ///     let ident_parser = IdentParser.leak();
    ///     Pair::new(ident_parser, ident_parser).leak().inner
    /// }
    ///
    /// let pair_parser = create_parser();
    /// ```
    fn leak(self) -> RefParser<'static, Self, T, O> where Self: Sized{
        let inner = Box::leak(Box::new(self));
        RefParser{
            inner,
            _phantom:PhantomData
        }
    }

    /// Constructs a box around this object then leaks it,
    /// returning a *mut pointer to it for freeing later
    ///
    /// This is similar to [`leak`](CombinatorExt::leak)
    /// # Example
    /// ```rust
    /// use pakerat_combinators::combinator::{Combinator, CombinatorExt, RefParser};
    /// use pakerat_combinators::basic_parsers::IdentParser;
    /// use pakerat_combinators::multi::Ignore;
    /// use std::ptr;
    ///
    /// // Function that constructs and returns a leaked parser and its pointer.
    /// fn create_parser() -> (&'static dyn Combinator<(), ()>, *mut dyn Combinator<(), ()>,) {
    ///     let (leaked_parser, ptr) = Ignore::new(IdentParser).leak2();
    ///     (leaked_parser.inner, ptr)
    /// }
    ///
    /// let (parser, ptr) = create_parser();
    /// // SAFETY: Manually free the leaked memory when done
    /// unsafe {
    ///     drop(Box::from_raw(ptr));
    /// }
    /// ```
    fn leak2(self) -> (RefParser<'static, Self, T, O>,*mut Self) where Self: Sized{
        let r = Box::leak(Box::new(self));
        let ptr = r as *mut _;
        let inner :&Self = r;
        
        (
            RefParser{
                inner,
                _phantom:PhantomData
            },
            ptr
        )
    }

    /// Applies a transformation function to the output of the combinator.
    ///
    /// This is syntax sugar around [`MapCombinator`], allowing you to modify
    /// parsed results without changing the underlying parser logic.
    ///
    /// # Example
    /// ```rust
    /// use pakerat_combinators::combinator::{Combinator, CombinatorExt};
    /// use pakerat_combinators::basic_parsers::IdentParser;
    /// use pakerat_combinators::core::Input;
    /// use pakerat_combinators::cache::BasicCache;
    /// use syn::buffer::TokenBuffer;
    ///
    /// let tokens = "example".parse().unwrap();
    /// let buffer = TokenBuffer::new2(tokens);
    /// let input = Input::new(&buffer);
    ///
    /// let ident_parser = IdentParser;
    ///
    /// // Convert parsed identifier output into uppercase
    /// let uppercase_parser = ident_parser.map(|ident: proc_macro2::Ident| ident.to_string().to_uppercase());
    ///
    /// let mut cache = BasicCache::<0>::new();
    ///
    /// let (_, result) = uppercase_parser.parse(input, &mut cache).unwrap();
    /// assert_eq!(result, "EXAMPLE");
    /// ```
    fn map<F, T2>(self, map_fn: F) -> MapCombinator<Self, F, T, T2, O>
    where
        F: for<'a> Fn(T::Output<'a>) -> T2,
        T2: for<'a> Parsable<Output<'a> = T2>,
        Self: Sized,
    {
        MapCombinator {
            inner: self,
            map_fn,
            _phantom: PhantomData,
        }
    }

    /// Wraps a parser to filter its output based on a predicate.
    ///
    /// After parsing using the inner parser, the given filtering function is applied to the result.
    /// If the filtering function returns `true`, the output is accepted; otherwise, a missmatch error is returned.
    /// "Found x Expected {}" with a user define expected text.
    ///
    /// This is just syntax sugar around [`Filter`]
    fn filter<F>(self, filter_fn: F, expected: &'static str) -> Filter<Self, T, O, F>
    where
        F: for<'a> Fn(&T::Output<'a>) -> bool,
        Self: Sized,
    {
        Filter::new(self, filter_fn, expected)
    }


    /// Parses input calling into on both the sides of the [`Result`]
    ///
    /// This is mainly useful for integrating with syn
    ///
    /// # Example
    /// ```rust
    /// use pakerat_combinators::combinator::{Combinator, CombinatorExt, PakeratError};
    /// use pakerat_combinators::core::{Input};
    /// use pakerat_combinators::basic_parsers::AnyDelParser;
    /// use pakerat_combinators::cache::BasicCache;
    /// use syn::buffer::{TokenBuffer,Cursor};
    ///
    /// let tokens = "(content)".parse().unwrap();
    /// let buffer = TokenBuffer::new2(tokens);
    /// let input = Input::new(&buffer);
    ///
    /// let parser = AnyDelParser; // Parses any delimited group and returns Input
    /// let mut cache = BasicCache::<0>::new();
    ///
    /// // Convert parsed input into a `Cursor`, handling errors as `syn::Error`
    /// let result: Result<(Input, Cursor), syn::Error> = parser.parse_into(input, &mut cache);
    ///
    /// assert!(result.is_ok());
    /// ```
    fn parse_into<'a, V, E2>(
        &self,
        input: Input<'a>,
        state: &mut dyn DynCache<'a, O>,
    ) -> Result<(Input<'a>, V), E2>
    where
        V: From<T::Output<'a>>,
        E2: Error + From<PakeratError>,
    {
        let (input, t) = self.parse(input, state)?;
        Ok((input, t.into()))
    }

    
    /// Runs this parser, returning the consumed tokens as an [`Input`] as well as the rest of the stream.
    ///
    /// This is useful for splitting parsing into distinct stages.
    /// The recognized input can then be passed to another parser for further processing.
    ///
    /// See [`Recognize`] for an example of how to integrate this into a workflow.
    ///
    /// [`Recognize`]: crate::multi::Recognize
    ///
    /// # Example
    /// ```rust
    /// use pakerat_combinators::combinator::{Combinator, CombinatorExt};
    /// use pakerat_combinators::multi::Pair;
    /// use pakerat_combinators::basic_parsers::{IdentParser, AnyParser};
    /// use pakerat_combinators::core::Input;
    /// use pakerat_combinators::cache::BasicCache;
    /// use syn::buffer::TokenBuffer;
    ///
    /// // Example input
    /// let tokens = "some_token another_token".parse().unwrap();
    /// let buffer = TokenBuffer::new2(tokens);
    /// let input = Input::new(&buffer);
    ///
    /// let pair_parser = Pair::new(AnyParser, IdentParser);
    ///
    /// // First, recognize and extract the input segment.
    /// let mut cache = BasicCache::<0>::new();
    /// let (remaining, recognized) = pair_parser.parse_recognize(input, &mut cache).unwrap();
    ///
    /// // Now, apply `IdentParser` to the recognized input.
    /// let (_, ident) = IdentParser.parse(recognized, &mut cache).unwrap();
    ///
    /// // Ensure the second parser matched an identifier.
    /// assert_eq!(ident.to_string(), "some_token");
    /// ```
    fn parse_recognize<'a>(&self,input:Input<'a>,cache: &mut dyn DynCache<'a,O>) -> Pakerat<(Input<'a>,Input<'a>)>{
        let next = self.parse_ignore(input,cache)?;
        Ok((next,input.truncate(next)))
    }

    /// Wraps the parser in an [`RcParser`], giving it a static‑like lifetime.
    #[allow(clippy::wrong_self_convention)]
    fn as_rc(self) -> RcParser<T, O,Self>
    where
        Self: Sized,
    {
        RcParser::new(self)
    }


}

impl<T: Parsable, O: Parsable, F: Combinator<T, O>> CombinatorExt<T, O> for F {}

/// A combinator that transforms the output of another parser using a mapping function.
/// see [`CombinatorExt::map`] for a full example.
///
/// note that the outputs lifetime can not depend on the input.
/// if this is a problem implement [`Combinator`] directly for MyStruct(Base)
pub struct MapCombinator<Base, F, In, Out, Cached>
where
    Base: Combinator<In, Cached>,
    F: for<'a> Fn(In::Output<'a>) -> Out,
    In: Parsable,
    Out: for<'a> Parsable<Output<'a> = Out>,
    Cached: Parsable,
{
    pub inner: Base,
    pub map_fn: F,
    pub _phantom: PhantomData<(In, Out, Cached)>,
}

impl<Base, F, In, Out, Cached> Combinator<Out, Cached> for MapCombinator<Base, F, In, Out, Cached>
where
    Base: Combinator<In, Cached>,
    In: Parsable,
    Out: for<'a> Parsable<Output<'a> = Out>,
    F: for<'a> Fn(In::Output<'a>) -> Out,
    Cached: Parsable,
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        state: &mut dyn DynCache<'a, Cached>,
    ) -> Pakerat<(Input<'a>, Out::Output<'a>)> {
        let (input, output) = self.inner.parse(input, state)?;
        Ok((input, (self.map_fn)(output)))
    }
}

/// A reference-based wrapper around an existing `Combinator`.
///
/// This struct is primarily created using [`CombinatorExt::as_ref`], which allows
/// an existing combinator to be reused in multiple combinator constructions without
/// ownership issues. See [`CombinatorExt::as_ref`] for a full example.
pub struct RefParser<'parser, INNER: Combinator<T, O>, T: Parsable, O: Parsable> {
    pub inner: &'parser INNER,
    pub _phantom: PhantomData<(T, O)>,
}

impl<INNER: Combinator<T, O>, T: Parsable, O: Parsable> Clone for RefParser<'_, INNER, T, O>{
fn clone(&self) -> Self { *self }
}
impl<INNER: Combinator<T, O>, T: Parsable, O: Parsable> Copy for RefParser<'_, INNER, T, O>{}

impl<T: Parsable, O: Parsable, INNER: Combinator<T, O>> Combinator<T, O>
    for RefParser<'_, INNER, T, O>
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, T::Output<'a>)> {
        self.inner.parse(input, state)
    }

    fn parse_ignore<'a>(
        &self,
        input: Input<'a>,
        state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<Input<'a>> {
        self.inner.parse_ignore(input, state)
    }
}

impl<INNER, T, O> Deref for RefParser<'_, INNER, T, O>
where
    INNER: Combinator<T, O>,
    T: Parsable,
    O: Parsable,
{
    type Target = INNER;

    fn deref(&self) -> &Self::Target {
        self.inner
    }
}

impl<'parser, INNER: Combinator<T, O>, T: Parsable, O: Parsable>
    RefParser<'parser, INNER, T, O>
{
    pub fn new(inner: &'parser INNER) -> Self {
        Self {
            inner,
            _phantom: PhantomData,
        }
    }
}

/// Wraps a parser to filter its output based on a predicate.
///
/// After parsing using the inner parser, the given filtering function is applied to the result.
/// If the filtering function returns `true`, the output is accepted; otherwise, a missmatch error is returned.
/// "Found x Expected {}" with a user define expected text.
///
/// # Example
/// ```rust
/// use pakerat_combinators::combinator::Filter;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::cache::BasicCache;
/// use pakerat_combinators::core::Input;
/// use syn::buffer::TokenBuffer;
///
/// let tokens = "my_var".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
/// // Create a parser that accepts identifiers that are not equal to "forbidden"
/// let parser = Filter::new(
///     IdentParser,
///     |ident| {
///         ident != "forbidden"
///     },
///     "identifier cannot be 'forbidden'"
/// );
///
/// let mut cache = BasicCache::<0>::new();
/// let (_next_input, result) = parser.parse(input, &mut cache).unwrap();
/// assert_eq!(result, "my_var".to_string());
/// ```
pub struct Filter<P, T, O, F>
where
    P: Combinator<T, O>,
    T: Parsable,
    O: Parsable,
    // The filter function accepts a reference to the parsed output and returns a bool.
    // We require it to work for any lifetime.
    F: for<'a> Fn(&T::Output<'a>) -> bool,
{
    /// The inner parser whose output will be filtered.
    pub parser: P,
    /// The filtering function that determines if the parsed output is acceptable.
    pub filter: F,
    /// the text that would be shown in the error as "Found X expected {}"
    pub expected: &'static str,
    /// Used so we can have generics.
    pub _phantom: std::marker::PhantomData<(T, O)>,
}

impl<P, T, O, F> Combinator<T, O> for Filter<P, T, O, F>
where
    P: Combinator<T, O>,
    T: Parsable,
    O: Parsable,
    F: for<'a> Fn(&T::Output<'a>) -> bool,
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, T::Output<'a>)> {
        match self.parser.parse(input, cache) {
            Ok((next_input, result)) => {
                if (self.filter)(&result) {
                    Ok((next_input, result))
                } else {
                    Err(PakeratError::Regular(
                        ParseError::Simple(Mismatch {
                            actual: Found::start_of(input),
                            expected: Expected::Text(self.expected),
                        })
                    ))
                }
            }
            Err(e) => Err(e),
        }
    }

    fn parse_ignore<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<Input<'a>> {
        match self.parser.parse(input, cache) {
            Ok((next_input, result)) => {
                if (self.filter)(&result) {
                    Ok(next_input)
                } else {
                    Err(PakeratError::Regular(
                        ParseError::Simple(Mismatch {
                            actual: Found::start_of(input),
                            expected: Expected::Text(self.expected),
                        })
                    ))
                }
            }
            Err(e) => Err(e),
        }
    }
}

impl<P, T, O, F> Filter<P, T, O, F>
where
    P: Combinator<T, O>,
    T: Parsable,
    O: Parsable,
    F: for<'a> Fn(&T::Output<'a>) -> bool,
{
    /// Creates a new Filter combinator with the given inner parser, filtering function, and error message.
    pub fn new(parser: P, filter: F, expected: &'static str) -> Self {
        Filter {
            parser,
            filter,
            expected,
            _phantom: std::marker::PhantomData,
        }
    }
}

/// A reference-counted parser wrapper.
/// This enables you to produce a parser with a pseudo‑static lifetime.
pub struct RcParser<T:Parsable, O:Parsable, P: Combinator<T, O>>
   
{
    pub inner: Rc<P>,
    pub _phantom: PhantomData<(T, O)>,
}

impl<T:Parsable, O:Parsable, P: Combinator<T, O>> Clone for RcParser<T, O, P>{

fn clone(&self) -> Self {Self{inner:self.inner.clone(),_phantom:PhantomData}}
}

impl<T:Parsable, O:Parsable, P: Combinator<T, O>> RcParser<T, O, P>
{
    /// Creates a new `RcParser` from the given combinator.
    pub fn new(parser: P) -> Self {
        RcParser {
            inner: Rc::new(parser),
            _phantom: PhantomData,
        }
    }

    /// Creates a weak reference to the parser, allowing it to be referenced without extending its lifetime.
    ///
    /// This method is useful for avoiding reference cycles when using [`as_rc`](CombinatorExt::as_rc).
    /// It allows a parser to be referenced without preventing it from being deallocated when no strong references remain.
    /// 
    /// This is a fairly neich feature you would usually want [`leak`](CombinatorExt::leak) or [`as_ref`](CombinatorExt::as_ref).
    /// keep in mind most parsers live for the lifetime of the aplication.
    ///
    /// # Example
    /// ```rust
    /// use pakerat_combinators::basic_parsers::IdentParser;
    /// use pakerat_combinators::combinator::{CombinatorExt, RcParser, WeakParser};
    /// use proc_macro2::Ident;
    ///
    /// struct Container {
    ///     parser: RcParser<Ident, (),IdentParser>,
    ///     reference: WeakParser<Ident,(),IdentParser>,
    /// }
    ///
    /// impl Container {
    ///     fn new() -> Self {
    ///         let parser = IdentParser.as_rc();
    ///         let weak_parser = parser.weak();
    ///
    ///         Self {
    ///             parser,
    ///             reference: weak_parser,
    ///         }
    ///     }
    ///
    /// }
    ///
    /// let container = Container::new();
    /// let weak = container.parser.weak();
    ///
    /// std::mem::drop(container); // The strong reference to parser is dropped.
    ///
    /// assert_eq!(weak.inner.strong_count(),0)
    /// ```
    pub fn weak(&self) -> WeakParser<T, O,P> {
        WeakParser {
            inner: Rc::downgrade(&self.inner),
            _phantom: PhantomData,
        }
    }
}

impl<T:Parsable, O:Parsable, P: Combinator<T, O>> Combinator<T, O> for RcParser<T, O, P>
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, T::Output<'a>)> {
        self.inner.parse(input, state)
    }

    fn parse_ignore<'a>(
        &self,
        input: Input<'a>,
        state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<Input<'a>> {
        self.inner.parse_ignore(input, state)
    }
}

/// A weak pointer based parser.
/// It holds a `Weak` reference to the inner combinator so that it does not extend the lifetime of the parser.
///
/// See ['RcParser::weak'] for more details
pub struct WeakParser< T: Parsable, O: Parsable, P: Combinator<T, O>,>
where
    P: Combinator<T, O>,
{
    pub inner: std::rc::Weak<P>,
    pub _phantom: std::marker::PhantomData<(T, O)>,
}

impl<T:Parsable, O:Parsable, P: Combinator<T, O>> Clone for WeakParser<T, O, P>{

fn clone(&self) -> Self {Self{inner:self.inner.clone(),_phantom:PhantomData}}
}

impl< T: Parsable, O: Parsable, P: Combinator<T, O>,> WeakParser<T, O,P>
{
    /// Attempts to upgrade the weak reference, panicking if it fails.
    fn upgrade(&self) -> Rc<P> {
        self.inner
            .upgrade()
            .expect("WeakParser upgrade failed: the Rc instance has been dropped.")
    }
}

impl< T: Parsable, O: Parsable, P: Combinator<T, O>,> Combinator<T, O> for WeakParser<T, O,P>
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, T::Output<'a>)> {
        self.upgrade().parse(input, state)
    }

    fn parse_ignore<'a>(
        &self,
        input: Input<'a>,
        state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<Input<'a>> {
        self.upgrade().parse_ignore(input, state)
    }
}
