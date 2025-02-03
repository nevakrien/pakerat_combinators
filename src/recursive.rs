use crate::combinator::Pakerat;
use crate::core::Input;
use std::cell::OnceCell;
use std::marker::PhantomData;
use crate::combinator::Combinator;
use crate::cache::{Cache, FlexibleCache};

/// A combinator that allows for recursive parsing by deferring initialization.
///
/// `RecursiveParser` enables defining self-referential parsing rules in a safe manner.
/// It uses `OnceCell` to lazily store and resolve the actual parser.
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
/// use std::rc::Rc;
///
/// // Example input
/// let tokens = "a + (b + c)".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
/// // Define the recursive parser
/// let parser = Rc::new(RecursiveParser::new());
///
/// let terminal_parser = Rc::new(one_of!("expected it or ident",
///     Ignore::new(IdentParser),
///     Ignore::new(IntParser),
///  ));
///
/// // Define an actual expression parser using the recursive reference.
/// let expr_parser = one_of!("expected an expression",
///     Ignore::new(Wrapped::new(AnyDelParser,parser.clone())),
///     Ignore::new(Pair::new(terminal_parser.clone(),Pair::new(PunctParser, parser.clone()))),
///     terminal_parser
/// );
///
/// // Initialize the recursive parser
/// parser.set(expr_parser);
///
///
/// let mut cache = BasicCache::<0>::new();
///
/// // Parse input
/// let (remaining, result) = parser.parse(input, &mut cache).unwrap();
/// assert!(remaining.eof());
/// ```
pub struct RecursiveParser<'a, T, O: Clone = T, C: Cache<'a, O> = FlexibleCache<'a, T>> {
    cell: OnceCell<Box<dyn Combinator<'a, T, O, C> + 'a>>,
    _phantom: PhantomData<(&'a (), T, O, C)>,
}

impl<'a, T, O: Clone, C: Cache<'a, O>> RecursiveParser<'a, T, O, C> {
    /// Creates a new recursive parser without an initial implementation.
    ///
    /// The parser must be initialized using [`set`] before use.
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
        P: Combinator<'a, T, O, C> + 'a,
    {
        self.cell
            .set(Box::new(parser))
            .unwrap_or_else(|_| panic!("Recursive parser already initialized"));
    }

    /// Retrieves the underlying parser, or panics if used before initialization.
    fn get(&self) -> &(dyn Combinator<'a, T, O, C> + 'a) {
        self.cell.get().expect("Used uninitialized recursive parser").as_ref()
    }
}

impl<'a, T, O: Clone, C: Cache<'a, O>> Combinator<'a, T, O, C> for &RecursiveParser<'a, T, O, C> {
    fn parse(&self, input: Input<'a>, state: &mut C) -> Pakerat<(Input<'a>, T)> {
        self.get().parse(input, state)
    }
}

impl<'a, T, O: Clone, C: Cache<'a, O>> Combinator<'a, T, O, C> for RecursiveParser<'a, T, O, C> {
    fn parse(&self, input: Input<'a>, state: &mut C) -> Pakerat<(Input<'a>, T)> {
        self.get().parse(input, state)
    }
}

