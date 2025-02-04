use crate::cache::DynCache;
use crate::combinator::BorrowParse;
use crate::combinator::Combinator;
use crate::combinator::Pakerat;
use crate::core::Input;
use std::cell::OnceCell;
use std::marker::PhantomData;

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
/// use crate::pakerat_combinators::combinator::CombinatorExt;
///
/// // Example input
/// let tokens = "a + (b + c)".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
/// // Define the recursive parser
/// let parser = RecursiveParser::new();
///
/// let terminal_parser = one_of!("expected it or ident",
///     Ignore::new(IdentParser),
///     Ignore::new(IntParser),
///  );
///
/// // Define an actual expression parser using the recursive reference.
/// let expr_parser = one_of!("expected an expression",
///     Ignore::new(Wrapped::new(AnyDelParser,parser.as_ref())),
///     Ignore::new(Pair::new(terminal_parser.as_ref(),Pair::new(PunctParser, parser.as_ref()))),
///     terminal_parser.as_ref()
/// );
///
/// // Initialize the recursive parser
/// parser.set(&expr_parser);
///
///
/// let mut cache = BasicCache::<0>::new();
///
/// // Parse input
/// let (remaining, result) = parser.parse(input, &mut cache).unwrap();
/// assert!(remaining.eof());
/// ```
pub struct RecursiveParser<'parser, T: BorrowParse, O: BorrowParse = T> {
    cell: OnceCell<&'parser dyn Combinator<T, O>>,
    _phantom: PhantomData<(T, O)>,
}

impl<T: BorrowParse, O: BorrowParse> Default for RecursiveParser<'_, T, O> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'parser, T: BorrowParse, O: BorrowParse> RecursiveParser<'parser, T, O> {
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

impl<T: BorrowParse, O: BorrowParse> Combinator<T, O> for RecursiveParser<'_, T, O> {
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
    use crate::basic_parsers::DelParser;
use proc_macro2::Delimiter;
use crate::combinator::CombinatorExt;
use crate::combinator::Combinator;
    use crate::basic_parsers::{IntParser, PunctParser};
    use crate::core::Input;
    use crate::cache::{CachedComb, BasicCache};
    use crate::multi::{Pair, Wrapped};
    use crate::one_of;
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
    fn test_arithmetic_parsing() {
        let tokens = "3 + 4 * (2 + 5)".parse().unwrap();
        let buffer = TokenBuffer::new2(tokens);
        let input = Input::new(&buffer);
        
        let mut cache = BasicCache::<2,i64>::new(); // Cache size of 2 for `num` and `add_num`
        
        let expr_parser = RecursiveParser::new();
        let add_num_parser = RecursiveParser::new();

        //add num
        let add_num_parser_holder = CachedComb::new(
            one_of!("expected num or num + num",
                Pair::new(IntParser, Pair::new(PunctParser.filter(|c| c.as_char()=='+',"expected +"), expr_parser.as_ref()))
                    .map(|(lhs, (_, rhs))| lhs + rhs),
                IntParser
            ),
            1,
            "infinite loop bug"
        );
        add_num_parser.set(&add_num_parser_holder);
        
        //expr
        let expr_parser_holder = CachedComb::new(one_of!("expected int",
            Wrapped::new(
                DelParser(Delimiter::Parenthesis)
                ,expr_parser.as_ref()
            ),
            Pair::new(add_num_parser.as_ref(), Pair::new(PunctParser.filter(|c| c.as_char()=='*',"expected *"), expr_parser.as_ref()))
                .map(|(lhs, (_, rhs))| lhs * rhs),
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
