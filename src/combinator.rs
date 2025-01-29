use std::error::Error;
use crate::cache::Cache;
use syn::buffer::Cursor;

///error type for handeling recursive parses.
///
///unlike the usual errors a recursive parse error should terminate the entire parse.
///
///these recursive errors fundementally mean there was an infinite loop in the program.
///
///miss reporting an error as regular can lead to weird caching behivior and wrong/unpredictble behivior.
///
///as well as program panics on bad parses (this was chosen over errors to avoid corupted states).
#[derive(Debug)]
pub enum PakeratError<E> where E: std::error::Error,{
    ///these are the errors most user code should generate
    ///
    ///dont construct these from a recursive error
    Regular(E),

    ///when you encounter this avoid calling ANY other parsers on the state. 
    ///
    ///and return a recursive error back
    Recursive(E)
}

impl<E: std::error::Error> PakeratError<E>{
    pub fn inner(self) -> E {
        match self {
            PakeratError::Regular(e) => e,
            PakeratError::Recursive(e) => e,
        }
    }

}

// Implement Clone when `E: Clone`
impl<E: Clone + std::error::Error> Clone for PakeratError<E> {
    fn clone(&self) -> Self {
        match self {
            PakeratError::Regular(e) => PakeratError::Regular(e.clone()),
            PakeratError::Recursive(e) => PakeratError::Recursive(e.clone()),
        }
    }
}

// Implement Clone when `E: Clone`
impl<E: PartialEq + std::error::Error> PartialEq for PakeratError<E> {

fn eq(&self, other: &PakeratError<E>) -> bool {
    match(self,other){
        (PakeratError::Regular(a),PakeratError::Regular(b)) => a==b,
        (PakeratError::Recursive(a),PakeratError::Recursive(b)) => a==b,
        _=> false,
    }
}
}


///result type used for internal cache managment
pub type Pakerat<T,E = syn::Error> = Result<T,PakeratError<E>>;

pub trait Combinator<T, E :Error = syn::Error,K = usize>
where
    E: std::error::Error,

{   

    ///this function respect the caching scheme and thus can work with recursive grammers
    fn parse<'a>(&self, input: Cursor<'a>,state: &mut impl Cache<'a,T,E,K>,) -> Pakerat<(Cursor<'a>, T), E>;

}