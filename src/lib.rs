//for now in testing
// #![feature(specialization)]

pub mod cache;
pub mod combinator;
pub mod basic_parsers;
pub mod multi;
pub mod core;
pub mod recursive;
mod macros {
	#![allow(unused_macros,unused_imports)]

    macro_rules! token_cursor {
    ($name:ident, $input:expr) => {
        let tokens: TokenStream = $input.parse().unwrap(); // Unwrap directly for clearer failure
        let buffer = TokenBuffer::new2(tokens); // Keep buffer alive
        let $name = Input::new(&buffer); // Extract Input
    };
}

    pub(crate) use token_cursor;    // <-- the trick
    // pub use crate::one_of;    // <-- the trick
}