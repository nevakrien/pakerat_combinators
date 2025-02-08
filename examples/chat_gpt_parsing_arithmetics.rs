#![allow(dead_code)]

/// this example was made by giving chatgpt a few important pages of docs then mostly just letting it do its thing
/// it took about 3 prompts to get and is mostly here as a way for me as a maintainer to see how LLMs handle my code
/// in terms of quality its probably not the best example
/// in paticular the poor thing could not figure out how to use the cache correctly which is a sign to update cache documentation


use pakerat_combinators::combinator::{Parsable, Combinator, CombinatorExt};
use pakerat_combinators::basic_parsers::{IdentParser, IntParser, PunctParser, DelParser};
use pakerat_combinators::cache::{CachedComb, BasicCache};
use pakerat_combinators::one_of;
use pakerat_combinators::recursive::RecursiveParser;
use pakerat_combinators::multi::{Pair, Wrapped, Many0};
use pakerat_combinators::core::Input;
use proc_macro2::Delimiter;
use syn::buffer::TokenBuffer;

// Define our AST.
#[derive(Debug, Clone)]
enum Expr {
    Number(i64),
    Ident(String),
    BinaryOp {
        op: String,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Grouped(Box<Expr>),
}

// Implement Parsable for Expr.
impl Parsable for Expr {
    type Output<'a> = Expr;
}

// Define cache keys for the terminal parsers.
#[derive(Clone, Copy, Debug)]
enum TerminalType {
    Ident = 0,
    Number,
}
impl From<TerminalType> for usize {
    fn from(val: TerminalType) -> Self {
        val as usize
    }
}

// We use a basic cache with two slots.
const CACHE_SIZE: usize = 2;
type MyCache<'a> = BasicCache<'a, CACHE_SIZE, Expr>;

fn main() {
    // Example input.
    let input_str = "a + (b + 42)";
    let tokens = input_str.parse().expect("Failed to parse tokens");
    let buffer = TokenBuffer::new2(tokens);
    let input = Input::new(&buffer);

    // Create a recursive parser instance.
    let expr_parser = RecursiveParser::new();

    // Define a parser for a "factor": either a grouped expression or a terminal.
    let factor = one_of!("expected a factor",
        // Grouped expression: an expression in parentheses.
        Wrapped::new(
            DelParser(Delimiter::Parenthesis),
            expr_parser.as_ref()
        ).map(|inner_expr| Expr::Grouped(Box::new(inner_expr))),
        // Terminal: either an identifier or a number.
        one_of!("expected an identifier or a number",
            CachedComb::new(
                IdentParser.map(|ident: proc_macro2::Ident| Expr::Ident(ident.to_string())),
                TerminalType::Ident.into(),
                "error while parsing identifier"
            ),
            CachedComb::new(
                IntParser.map(Expr::Number),
                TerminalType::Number.into(),
                "error while parsing number"
            )
        )
    );

    // Define the addition tail: zero or more pairs of '+' and a factor.
    let add_tail = Many0::new(
        Pair::new(
            // Filter to accept only '+'.
            PunctParser.filter(|p| p.as_char() == '+', "expected '+' operator"),
            factor.as_ref()
        )
    );

    // Define the full expression as a factor optionally followed by additional '+ factor' pairs.
    let add_expr = Pair::new(factor.as_ref(), add_tail).map(|(first, tail)| {
        tail.into_iter().fold(first, |acc, (op, factor)| {
            Expr::BinaryOp {
                op: op.as_char().to_string(),
                left: Box::new(acc),
                right: Box::new(factor),
            }
        })
    });

    // Set the recursive parser to the addition expression.
    expr_parser.set(&add_expr);

    // Create a cache.
    let mut cache = MyCache::default();

    // Parse the input.
    match expr_parser.parse(input, &mut cache) {
        Ok((remaining, ast)) => {
            if remaining.eof() {
                println!("Parsed AST: {:#?}", ast);
            } else {
                println!("Parsed AST: {:#?}", ast);
                println!("Note: There is remaining input that was not parsed.");
            }
        },
        Err(e) => {
            eprintln!("Parse error: {:?}", e);
        }
    }
}
