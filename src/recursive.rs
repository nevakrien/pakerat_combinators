//! This module exposes parsers ([`RecursiveParser`] and [`OwnedRecursiveParser`]) that can be passed around before they are fully defined.
//! The idea is to allow for self-referential parsers, enabling them to refer to themselves
//! before they are fully initialized. 
//!
//! However, this recursion can fundamentally cause infinite loops, so it is generally
//! a good idea to use caching to prevent this and guarantee linear time complexity.
//!
//! Most interesting parsers usually have at least one recursive element, as many grammars
//! inherently contain nested structures. Recursive parsers enable handling constructs like
//! expressions, nested blocks, and complex syntactic forms.
//!
//! # Example Usage:
//!
//! Parsing arithmetic expressions with `+`, `*`, and `()`.
//!
//! ## Parsing Rules:
//! ```text
//! (num) => num
//! add_num * num => num
//! add_num => num
//! int + num => add_num
//! int => add_num
//! ```
//!
//! ## Example Code:
//!
//! ```rust
//! use pakerat_combinators::{
//!     one_of_last,
//!     basic_parsers::{DelParser, IntParser, SpecificPunct},
//!     combinator::{Combinator, CombinatorExt},
//!     core::Input,
//!     cache::{CachedComb, BasicCache},
//!     multi::{Pair, Wrapped},
//!     recursive::RecursiveParser
//! };
//! use proc_macro2::Delimiter;
//! use syn::buffer::TokenBuffer;
//!
//! let tokens = "3 + 4 * (2 + 5)".parse().unwrap();
//! let buffer = TokenBuffer::new2(tokens);
//! let input = Input::new(&buffer);
//!
//! let mut cache = BasicCache::<2, i64>::new(); // Cache size of 2 for `num` and `add_num`
//!
//! let expr_parser = RecursiveParser::new();
//! let add_num_parser = RecursiveParser::new();
//!
//! // Define `add_num`
//! let add_num_parser_holder = CachedComb::new(
//!     one_of_last!(
//!         // int + num => add_num
//!         Pair::new(IntParser, Pair::new(SpecificPunct('+'), expr_parser.as_ref()))
//!             .map(|(lhs, (_, rhs))| lhs + rhs),
//!         // int => add_num
//!         IntParser
//!     ),
//!     1,
//!     "infinite loop bug"
//! );
//! add_num_parser.set(&add_num_parser_holder);
//!
//! // Define `expr`
//! let expr_parser_holder = CachedComb::new(one_of_last!(
//!     // (num) => num
//!     Wrapped::new(
//!         DelParser(Delimiter::Parenthesis),
//!         expr_parser.as_ref()
//!     ),
//!     // add_num * num => num
//!     Pair::new(add_num_parser.as_ref(), Pair::new(SpecificPunct('*'), expr_parser.as_ref()))
//!         .map(|(lhs, (_, rhs))| lhs * rhs),
//!     
//!     // add_num => num 
//!     add_num_parser.as_ref()
//! ),
//! 0,
//! "infinite loop bug"
//! );
//!
//! expr_parser.set(&expr_parser_holder);
//!
//! let (_, result) = expr_parser.parse(input, &mut cache).unwrap();
//! assert_eq!(result, 3 + 4 * (2 + 5)); // sanity check
//! ```
//!
//! ## Avoiding Left Recursion
//!
//! When defining a recursive grammar, it is important to avoid left recursion. 
//! Left recursion occurs when a rule calls itself as its first element, leading to an infinite loop.
//!
//! **Example of Left Recursion (Bad)**
//! ```text
//! expr => expr + term
//! term => factor
//! ```
//! The above rule will **never terminate** because `expr` immediately calls `expr` again.
//!
//! **Fixed Version (Good)**
//! ```text
//! expr => term + expr
//! term => factor
//! ```
//! This ensures recursion happens at a later point in the rule, avoiding infinite recursion.
//! If you are **caching** recursive parsers (as you should be), 
//! the caching layer should catch and report infinite loops.



use crate::cache::DynCache;
use crate::combinator::Parsable;
use crate::combinator::Combinator;
use crate::combinator::Pakerat;
use crate::core::Input;
use std::cell::OnceCell;
use std::marker::PhantomData;

/// A combinator that allows for recursive parsing by deferring initialization.
///
/// `RecursiveParser` enables defining self-referential parsing rules in a safe manner.
/// It uses [`OnceCell`] to lazily store and resolve the actual parser.
///
/// Note that the lifetime requirement can be a bit annoying, so using an [`leaking`](crate::combinator::CombinatorExt) or using an arena allocator is a good idea.
/// See [`typed-arena`](https://crates.io/crates/typed-arena) for a good arena implementation.
///
/// # Example
/// ```rust
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::{IdentParser,AnyDelParser, PunctParser, IntParser};
/// use pakerat_combinators::core::Input;
/// use pakerat_combinators::cache::{BasicCache, FlexibleCache};
/// use syn::buffer::TokenBuffer;
/// use pakerat_combinators::one_of;
/// use pakerat_combinators::recursive::RecursiveParser;
/// use pakerat_combinators::multi::{Pair,Ignore,Wrapped};
/// use crate::pakerat_combinators::combinator::CombinatorExt;
///
/// // Example input
/// let tokens = "a + (b + c)".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
/// // Define the recursive parser
/// let parser = RecursiveParser::new().leak();
///
/// let terminal_parser = one_of!("expected it or ident",
///     Ignore::new(IdentParser),
///     Ignore::new(IntParser),
///  ).leak();
///
/// // Define an actual expression parser using the recursive reference.
/// let expr_parser = one_of!("expected an expression",
///     Ignore::new(Wrapped::new(AnyDelParser,parser)),
///     Ignore::new(Pair::new(terminal_parser,Pair::new(PunctParser, parser))),
///     terminal_parser
/// );
///
/// // Initialize the recursive parser
/// parser.set(expr_parser.leak().inner);
///
///
/// let mut cache = BasicCache::<0>::new();
///
/// // Parse input
/// let (remaining, result) = parser.parse(input, &mut cache).unwrap();
/// assert!(remaining.eof());
/// ```
pub struct RecursiveParser<'parser, T : Parsable = (), O: Parsable = T> {
    pub cell: OnceCell<&'parser dyn Combinator<T, O>>,
    pub _phantom: PhantomData<(T, O)>,
}
    
impl<T: Parsable, O: Parsable> Default for RecursiveParser<'_, T, O> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'parser, T: Parsable, O: Parsable> RecursiveParser<'parser, T, O> {
    /// Creates a new recursive parser without an initial implementation.
    ///
    /// The parser must be initialized using [`set`] before use.
    ///
    ///[`set`]: RecursiveParser::set
    pub fn new() -> Self {
        Self {
            cell: OnceCell::new(),
            _phantom: PhantomData,
        }
    }

    /// Initializes the recursive parser with a concrete implementation.
    ///
    /// This function should only be called once.
    pub fn set<P>(&self, parser: &'parser P)
    where
        P: Combinator<T, O> + 'parser,
    {
        self.cell
            .set(parser)
            .unwrap_or_else(|_| panic!("Recursive parser already initialized"));
    }

    /// Retrieves the underlying parser, or panics if used before initialization.
    fn get(&self) -> &(dyn Combinator<T, O> + 'parser) {
        self.cell
            .get()
            .expect("Used uninitialized recursive parser")
    }
}

impl<T: Parsable, O: Parsable> Combinator<T, O> for RecursiveParser<'_, T, O> {
    fn parse<'a>(
        &self,
        input: Input<'a>,
        state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, T::Output<'a>)> {
        self.get().parse(input, state)
    }

    fn parse_ignore<'a>(
        &self,
        input: Input<'a>,
        state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<Input<'a>> {
        self.get().parse_ignore(input, state)
    }
}


/// A combinator that allows for recursive parsing by deferring initialization.
///
/// This struct enables defining self‑referential parsing rules.
/// Unlike [`RecursiveParser`] it owns the internal parser, and that parser must have a static lifetime. 
/// This can be achieved by using [`RcParser`] and [`WeakParser`].
///
/// **Note:** For most applications, it is generally recommended to use the regular recursive
/// parser with [`leak`] since most applications need only parsers that are static.
/// This struct is only useful if you need the internal parser to eventually be dropped.
/// Be careful to avoid cycles in your recursive definitions:
/// hold only one recursive strong [`RcParser`] and use its [`weak`] method when
/// passing it around recursively.
///
/// [`RcParser`]: crate::combinator::RcParser
/// [`WeakParser`]: crate::combinator::WeakParser
/// [`weak`]: crate::combinator::RcParser::weak
/// [`leak`]: crate::combinator::CombinatorExt::leak
///
/// # Example
///
/// ```rust
/// use pakerat_combinators::combinator::{Combinator, CombinatorExt, RcParser};
/// use pakerat_combinators::basic_parsers::{IdentParser, AnyDelParser, PunctParser, IntParser};
/// use pakerat_combinators::core::Input;
/// use pakerat_combinators::cache::BasicCache;
/// use pakerat_combinators::multi::{Pair, Ignore, Wrapped};
/// use pakerat_combinators::one_of;
/// use pakerat_combinators::recursive::OwnedRecursiveParser;
/// use std::rc::Rc;
/// use syn::buffer::TokenBuffer;
///
/// // Constructs a recursive parser and returns an RcParser wrapping it.
/// // This avoids leaking the parser and instead manages memory via reference counting.
/// fn create_recursive_parser() -> Rc<OwnedRecursiveParser> {
///     // Create a new recursive parser (uninitialized)
///     let recursive_parser = OwnedRecursiveParser::new();
///
///     // Wrap it in an RcParser for shared ownership.
///     let rc_recursive = RcParser::new(recursive_parser);
///
///     // Define a terminal parser for example purposes.
///     let terminal_parser = one_of!("expected ident or int",
///         Ignore::new(IdentParser),
///         Ignore::new(IntParser)
///     ).as_rc();
///
///     // Build an expression parser that uses the recursive parser for sub-expressions.
///     // Use weak() on the RcParser when referencing it recursively to avoid cycles.
///     // terminal_parser is with clone so it wont be dropped
///     let expr_parser = one_of!("expected an expression",
///         Ignore::new(Wrapped::new(AnyDelParser, rc_recursive.weak())),
///         Ignore::new(Pair::new(terminal_parser.clone(), Pair::new(PunctParser, rc_recursive.weak()))),
///         terminal_parser
///     );
///
///     // Initialize the recursive parser with the actual expression parser.
///     rc_recursive.inner.set(expr_parser);
///
///     // Return the RcParser wrapping the recursive parser.
///     rc_recursive.inner
/// }
///
/// // Later, the parser can be used as follows:
/// let tokens = "a + (b + c)".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
/// let mut cache = BasicCache::<0>::new();
///
/// let rc_parser = create_recursive_parser();
/// let (remaining, result) = rc_parser.parse(input, &mut cache).unwrap();
/// assert!(remaining.eof());
/// ```
pub struct OwnedRecursiveParser<T: Parsable = (), O: Parsable = T> {
    pub cell: OnceCell<Box<dyn Combinator<T, O>>>,
    pub _phantom: PhantomData<(T, O)>,
}

impl<T: Parsable, O: Parsable> Default for OwnedRecursiveParser<T, O> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Parsable, O: Parsable> OwnedRecursiveParser<T, O> {
    /// Creates a new recursive parser without an initial implementation.
    ///
    /// The parser must be initialized using [`set`](OwnedRecursiveParser::set) before use.
    pub fn new() -> Self {
        Self {
            cell: OnceCell::new(),
            _phantom: PhantomData,
        }
    }

    /// Initializes the recursive parser with a concrete implementation.
    ///
    /// This function should only be called once.
    pub fn set<P>(&self, parser: P)
    where
        P: Combinator<T, O> + 'static,
    {
        self.cell
            .set(Box::new(parser))
            .unwrap_or_else(|_| panic!("Recursive parser already initialized"));
    }

    /// Retrieves the underlying parser, or panics if used before initialization.
    pub fn get(&self) -> &dyn Combinator<T, O> {
        self.cell
            .get()
            .expect("Used uninitialized recursive parser")
            .as_ref()
    }
}

impl<T: Parsable, O: Parsable> Combinator<T, O> for OwnedRecursiveParser<T, O> {
    fn parse<'a>(
        &self,
        input: Input<'a>,
        state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, T::Output<'a>)> {
        self.get().parse(input, state)
    }

    fn parse_ignore<'a>(
        &self,
        input: Input<'a>,
        state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<Input<'a>> {
        self.get().parse_ignore(input, state)
    }
}


#[cfg(test)]
mod tests {
    use crate::one_of_last;
use crate::basic_parsers::DelParser;
use proc_macro2::Delimiter;
use crate::combinator::CombinatorExt;
use crate::combinator::Combinator;
    use crate::basic_parsers::{IntParser,SpecificPunct};
    use crate::core::Input;
    use crate::cache::{CachedComb, BasicCache};
    use crate::multi::{Pair, Wrapped};
    
    use crate::recursive::RecursiveParser;
    use syn::buffer::TokenBuffer;

    /// Example usage: Parsing arithmetic expressions with +, *, and ()
    ///
    /// Parsing rules:
    /// (num) => num
    /// add_num * num => num
    /// add_num => num
    ///
    /// int + num => add_num
    /// int => add_num
    #[test]
    fn test_arithmetic_parsing_recursive() {
        let tokens = "3 + 4 * (2 + 5)".parse().unwrap();
        let buffer = TokenBuffer::new2(tokens);
        let input = Input::new(&buffer);
        
        let mut cache = BasicCache::<2,i64>::new(); // Cache size of 2 for `num` and `add_num`
        
        let expr_parser = RecursiveParser::new();
        let add_num_parser = RecursiveParser::new();

        //add num
        let add_num_parser_holder = CachedComb::new(
            one_of_last!(
                //int + num => add_num
                Pair::new(IntParser, Pair::new(SpecificPunct('+'), expr_parser.as_ref()))
                    .map(|(lhs, (_, rhs))| lhs + rhs),
                //int => add_num
                IntParser
            ),
            1,
            "infinite loop bug"
        );
        add_num_parser.set(&add_num_parser_holder);
        
        //expr
        let expr_parser_holder = CachedComb::new(one_of_last!(
            //(num) => num
            Wrapped::new(
                DelParser(Delimiter::Parenthesis)
                ,expr_parser.as_ref()
            ),
            //add_num * num => num
            Pair::new(add_num_parser.as_ref(), Pair::new(SpecificPunct('*'), expr_parser.as_ref()))
                .map(|(lhs, (_, rhs))| lhs * rhs),
            
            //add_num => num 
            add_num_parser.as_ref()
        ),
        0,
        "infinite loop bug"
        );
        
        expr_parser.set(&expr_parser_holder);
        
        let (_, result) = expr_parser.parse(input, &mut cache).unwrap();
        assert_eq!(result, 3 + 4 * (2 + 5)); // Ensure correct parsing
    }
}
