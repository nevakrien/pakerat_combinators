
use std::fmt;
// use crate::cache::CacheExt;
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
#[derive(Debug,Clone)]
pub enum PakeratError<E> where E: Clone+Error,{
    ///these are the errors most user code should generate
    ///
    ///dont construct these from a recursive error
    Regular(E),

    ///when you encounter this avoid calling ANY other parsers on the state. 
    ///
    ///and return a recursive error back
    Recursive(E)
}

impl<E: Error + std::clone::Clone> PakeratError<E>{
    pub fn inner(self) -> E {
        match self {
            PakeratError::Regular(e) => e,
            PakeratError::Recursive(e) => e,
        }
    }

    pub fn map<F:FnOnce(E) -> T,T:Error+Clone>(self,f:F) -> PakeratError<T>{
        match self {
            PakeratError::Regular(e) => PakeratError::Regular(f(e)),
            PakeratError::Recursive(e) => PakeratError::Recursive(f(e)),
        }
    }

}

#[derive(Debug,Clone,Copy)]
pub struct DumbyError;
impl From<()> for DumbyError{

fn from(_: ()) -> Self { DumbyError }
}
impl fmt::Display for DumbyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "DumbyError occurred")
    }
}
impl Error for DumbyError {}

impl From<PakeratError<syn::Error>> for syn::Error{
fn from(x: PakeratError<syn::Error>) -> Self { x.inner() }
}


// Implement Clone when `E: Clone`
impl<E: PartialEq + Error + Clone> PartialEq for PakeratError<E> {

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

pub trait Combinator<'a,T  =(), E :Error + Clone = syn::Error,K = usize,O : Clone=T>
{   

    ///this function respect the caching scheme and thus can work with recursive grammers
    fn parse(&self, input: Cursor<'a>,state: &mut impl Cache<'a,O,E,K>) -> Pakerat<(Cursor<'a>, T), E>;

    ///similar to parse just for raw tokens
    fn parse_ignore(&self, input: Cursor<'a>,state: &mut impl Cache<'a,O,E,K>) -> Pakerat<Cursor<'a>, E>{
        let (ans,_) = self.parse(input,state)?;
        Ok(ans)
    }
}

// use crate::basic_parsers::AnyDelParser;
// impl<T , E:Clone+Error, K, O :Clone> ConstCombinator<T,E,K,O> for AnyDelParser where for<'a> AnyDelParser: Combinator<'a, T, E, K, O>{}
// trait ConstCombinator<T = (), E: Error + Clone = syn::Error, K = usize, O: Clone = T>:
//     for<'a> Combinator<'a, T, E, K, O>
// {
// }

pub struct CodeRef<'a>{
    pub start:Cursor<'a>,
    pub end:Cursor<'a>,
}

pub trait CombinatorExt<'a, T, E :Error + Clone = syn::Error,K = usize,O : Clone=T> : Combinator<'a, T,E,K,O>{
    fn parse_recognize(&self, input: Cursor<'a>,state: &mut impl Cache<'a,O,E,K>) -> Pakerat<CodeRef<'a>, E>{
        Ok(CodeRef{
            start:input,
            end: self.parse_ignore(input,state)?,
        })
    }

    fn compose<F,M>(self,make:F) -> M where F: FnOnce(Self) -> M, Self: Sized{
        make(self)
    }

    fn parse_into<V :From<T>,E2:Error + From<PakeratError<E>>>(&self, input: Cursor<'a>,state: &mut impl Cache<'a,O,E,K>) -> Result<(Cursor<'a>, V), E2>{
        let (cursor,t) = self.parse(input,state)?;
        Ok((cursor,t.into()))
    }

}

pub trait CacheCombinator<'a, T :Clone, E :Clone+Error = syn::Error,K : Copy = usize> : Combinator<'a, T,E,K,T> {
    fn my_key(&self) -> K;
    fn make_error(&self,original_input: Cursor<'_>) -> E;
    fn parse_cached(&self, input: Cursor<'a>,state: &mut impl Cache<'a,T,E,K>) -> Pakerat<(Cursor<'a>, T), E>{
        state.parse_cached(input,self.my_key(),self,|| {self.make_error(input)})
    }
}