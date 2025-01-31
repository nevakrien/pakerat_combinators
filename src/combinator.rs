use std::marker::PhantomData;
use crate::cache::FlexibleCache;
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
///result type used for internal cache managment
pub type Pakerat<T,E = syn::Error> = Result<T,PakeratError<E>>;

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



pub trait Combinator<'a, T = (), E:Clone+Error = syn::Error, K =usize, O: Clone = T, C: Cache<'a, O , E, K> = FlexibleCache<'a,K,T,E>> {
    fn parse(&self, input: Cursor<'a>, state: &mut C) -> Pakerat<(Cursor<'a>, T), E>;
    fn parse_ignore(&self, input: Cursor<'a>,state: &mut C) -> Pakerat<Cursor<'a>, E>{
        let (ans,_) = self.parse(input,state)?;
        Ok(ans)
    }
}

//we would ideally not need this but for some reason rust is a bit dense....
//so we need to implement Combinator for all cases of dyn Combinator because thats just what rust wants
macro_rules! impl_combinator_for_wrappers {
    ($wrapper:ty) => {
        impl<'b, T, E, K, O, C> Combinator<'b, T, E, K, O, C> for $wrapper
        where
            O: Clone,
            E: Error + Clone,
            C: Cache<'b, O, E, K>,
        {
            fn parse(
                &self,
                input: syn::buffer::Cursor<'b>,
                cache: &mut C,
            ) -> Result<(syn::buffer::Cursor<'b>, T), PakeratError<E>> {
                (**self).parse(input, cache) // Delegate to the inner trait object
            }

            fn parse_ignore(
                &self,
                input: Cursor<'b>,
                cache: &mut C,
            ) -> Pakerat<Cursor<'b>, E> {
                (**self).parse_ignore(input, cache)
            }
        }
    };
}

use std::rc::Rc;
use std::sync::Arc;

impl_combinator_for_wrappers!(&dyn Combinator<'b, T, E, K, O, C>);
impl_combinator_for_wrappers!(Box<dyn Combinator<'b, T, E, K, O, C>>);
impl_combinator_for_wrappers!(Rc<dyn Combinator<'b, T, E, K, O, C>>);
impl_combinator_for_wrappers!(Arc<dyn Combinator<'b, T, E, K, O, C>>);



// Implementing for function-like types
impl<'a, F, T, E, K, O, C> Combinator<'a, T, E, K, O, C> for F
where
    F: Fn(Cursor<'a>, &mut C) -> Pakerat<(Cursor<'a>, T), E>,
    E: Clone + Error,
    C: Cache<'a, O, E, K>,
    O: Clone,
{
    fn parse(&self, input: Cursor<'a>, state: &mut C) -> Pakerat<(Cursor<'a>, T), E> {
        (self)(input, state)
    }
}

#[test]
fn test_closures() {
    use crate::multi::Maybe;

    fn example_parser<'a>(input: Cursor<'a>, _state: &mut FlexibleCache<'a>) -> Pakerat<(Cursor<'a>, ())> {
        Ok((input, ()))
    }

    #[allow(dead_code)]
    fn dumb(_maybe: Maybe::<'static ,&'static dyn Combinator<'static>>){

    }

    let dumby2: Box<dyn Combinator> = Box::new(example_parser);
    let _maybe = Maybe::new(&*dumby2);
    let _maybe = Maybe{
        inner:dumby2,
        _phantom:PhantomData
    };
}


#[test]
fn test_dyn_closure_combinator_error_mapping() {
    use syn::buffer::TokenBuffer;

    // A simple parser that always fails with a Regular error
    fn failing_parser<'a>(input: Cursor<'a>, _state: &mut FlexibleCache<'a>) -> Pakerat<(Cursor<'a>, ())> {
        Err(PakeratError::Regular(syn::Error::new(input.span(), "Inner parser error")))
    }

    // Create token buffer first so its dropped last
    let tokens = "test".parse().unwrap();
    let buffer = TokenBuffer::new2(tokens);

    // make a closure that wraps `failing_parser`(we need a helper function so that the lifetimes work like we want)
    fn make_combinator<'b>() ->  Box<dyn Combinator<'b, (), syn::Error, usize, (), FlexibleCache<'b,  usize, ()>>>{
        Box::new(move  |input: Cursor<'b>, cache: &mut FlexibleCache<'b, usize, ()>| {
            failing_parser(input, cache).map_err(move |e| {
                e.map(|inner| {
                    let mut err = syn::Error::new(inner.span(),"failed doing something");
                    err.combine(inner);
                    err
                })
            }) 
        })
    }

    let error_mapping_combinator = make_combinator();


    let mut cache = FlexibleCache::<usize, ()>::default();
    {
        // Run the parser
        let result = error_mapping_combinator.parse(buffer.begin(), &mut cache);

        // Verify that the error was transformed
        if let Err(PakeratError::Regular(e)) = result {
            assert!(e.to_string().contains("failed doing something"));
        } else {
            panic!("Expected an error but got a successful parse");
        }
    }
}


pub struct CodeRef<'a>{
    pub start:Cursor<'a>,
    pub end:Cursor<'a>,
}

pub trait CombinatorExt<'a, T, E :Error + Clone,K,O:Clone ,C: Cache<'a, O, E, K>> : Combinator<'a, T,E,K,O,C>{
    fn parse_recognize(&self, input: Cursor<'a>,state: &mut C) -> Pakerat<CodeRef<'a>, E>{
        Ok(CodeRef{
            start:input,
            end: self.parse_ignore(input,state)?,
        })
    }

    fn compose<F,M>(self,make:F) -> M where F: FnOnce(Self) -> M, Self: Sized{
        make(self)
    }

    fn parse_into<V :From<T>,E2:Error + From<PakeratError<E>>>(&self, input: Cursor<'a>,state: &mut C) -> Result<(Cursor<'a>, V), E2>{
        let (cursor,t) = self.parse(input,state)?;
        Ok((cursor,t.into()))
    }

}

impl<'a, T, E:Clone + Error, K, O:Clone, C: Cache<'a, O, E, K>,F:Combinator<'a, T, E, K, O, C>> CombinatorExt<'a, T, E, K, O, C> for F{}

//this one is potentially confusing better not have it here.
// pub trait CacheCombinator<'a, C: Cache<'a, T, E, K>,T :Clone, E :Clone+Error = syn::Error,K : Copy = usize> : Combinator<'a, T,E,K,T,C> {
//     fn my_key(&self) -> K;
//     fn make_error(&self,original_input: Cursor<'_>) -> E;
//     fn parse_cached(&self, input: Cursor<'a>,state: &mut C) -> Pakerat<(Cursor<'a>, T), E>{
//         state.parse_cached(input,self.my_key(),self,|| {self.make_error(input)})
//     }
// }

// pub struct CachedSelfRef<'a,T,E = syn::Error,K= usize,C=FlexibleCache<'a,K,T,E>> 
// where 
// C:Cache<'a, T, E, K>,
// T :Clone,
// E :Clone+Error,
// K : Copy {
//     _phantom:PhantomData<(Cursor<'a>,T,E,K,C)>
// }