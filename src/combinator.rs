
use crate::core::ParseError;
use crate::cache::FlexibleCache;
// use crate::cache::CacheExt;
use std::error::Error;
use crate::cache::Cache;
use crate::core::Input;

// #[derive(Debug,Clone)]
// pub enum ParseError{
//     Syn(Rc<syn::Error>),
//     Regular(),
//     Stock
//     None,
// }

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
pub enum PakeratError<E=ParseError> where E: Clone+Error,{
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

impl From<PakeratError<syn::Error>> for PakeratError<ParseError>{

fn from(e: PakeratError<syn::Error>) -> Self { e.map(|x| x.into())}
}
///result type used for internal cache managment
pub type Pakerat<T,E = ParseError> = Result<T,PakeratError<E>>;


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



pub trait Combinator<'a, T = (), O: Clone = T, C: Cache<'a, O> = FlexibleCache<'a,T>> {
    fn parse(&self, input: Input<'a>, state: &mut C) -> Pakerat<(Input<'a>, T)>;
    fn parse_ignore(&self, input: Input<'a>,state: &mut C) -> Pakerat<Input<'a>>{
        let (ans,_) = self.parse(input,state)?;
        Ok(ans)
    }
}

// pub trait Parser<T, O, C>: for<'a> Combinator<'a, T, O, C>
// where
//     C: for<'a> Cache<'a, O>, O:Clone
// {}
// impl<T, O, C, P> Parser<T, O, C> for P
// where
//     P: for<'a> Combinator<'a, T, O, C>,
//     C: for<'a> Cache<'a, O>, O: Clone
// {}



//we would ideally not need this but for some reason rust is a bit dense....
//so we need to implement Combinator for all cases of dyn Combinator because thats just what rust wants
macro_rules! impl_combinator_for_wrappers {
    ($wrapper:ty) => {
        impl<'b, T, O, C> Combinator<'b, T, O, C> for $wrapper
        where
            O: Clone,
            C: Cache<'b, O>,
        {
            fn parse(
                &self,
                input: Input<'b>,
                cache: &mut C,
            ) -> Pakerat<(Input<'b>, T)> {
                (**self).parse(input, cache) // Delegate to the inner trait object
            }

            fn parse_ignore(
                &self,
                input: Input<'b>,
                cache: &mut C,
            ) -> Pakerat<Input<'b>> {
                (**self).parse_ignore(input, cache)
            }
        }
    };
}

use std::rc::Rc;
use std::sync::Arc;

impl_combinator_for_wrappers!(&dyn Combinator<'b, T, O, C>);
impl_combinator_for_wrappers!(Box<dyn Combinator<'b, T, O, C>>);
impl_combinator_for_wrappers!(Rc<dyn Combinator<'b, T, O, C>>);
impl_combinator_for_wrappers!(Arc<dyn Combinator<'b, T, O, C>>);

// impl_combinator_for_wrappers!(Rc<dyn for<'a> Combinator<'a, T, O, C>>);






// Implementing for function-like types
impl<'a, F, T, O, C> Combinator<'a, T, O, C> for F
where
    F: Fn(Input<'a>, &mut C) -> Pakerat<(Input<'a>, T)>,
    C: Cache<'a, O>,
    O: Clone,
{
    fn parse(&self, input: Input<'a>, state: &mut C) -> Pakerat<(Input<'a>, T)> {
        (self)(input, state)
    }
}

#[test]
fn test_closures() {
    use crate::multi::Maybe;
    use std::marker::PhantomData;


    fn example_parser<'a>(input: Input<'a>, _state: &mut FlexibleCache<'a>) -> Pakerat<(Input<'a>, ())> {
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
    fn failing_parser<'a>(input: Input<'a>, _state: &mut FlexibleCache<'a>) -> Pakerat<(Input<'a>, ())> {
        Err(PakeratError::Regular(ParseError::Message(input.span(),"Inner parser error")))
    }

    // Create token buffer first so its dropped last
    let tokens = "test".parse().unwrap();
    let buffer = TokenBuffer::new2(tokens);

    // make a closure that wraps `failing_parser`(we need a helper function so that the lifetimes work like we want)
    fn make_combinator<'b>() ->  Rc<dyn Combinator<'b, (), (), FlexibleCache<'b, ()>>>{
        Rc::new(move  |input: Input<'b>, cache: &mut FlexibleCache<'b, ()>| {
            failing_parser(input, cache).map_err(move |e| {
                e.map(|e| {
                    let err:syn::Error = e.into();
                    let mut new_err = syn::Error::new(err.span(),"failed doing something");
                    new_err.combine(err);
                    ParseError::Syn(new_err)
                })
            }) 
        })
    }

    let error_mapping_combinator = make_combinator();


    let mut cache = FlexibleCache::< ()>::default();
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


pub struct CodeRef<'a>{
    pub start:Input<'a>,
    pub end:Input<'a>,
}

pub trait CombinatorExt<'a, T,O:Clone ,C: Cache<'a, O>> : Combinator<'a, T,O,C>{
    fn parse_recognize(&self, input: Input<'a>,state: &mut C) -> Pakerat<CodeRef<'a>>{
        Ok(CodeRef{
            start:input,
            end: self.parse_ignore(input,state)?,
        })
    }

    fn compose<F,M>(self,make:F) -> M where F: FnOnce(Self) -> M, Self: Sized{
        make(self)
    }

    fn parse_into<V :From<T>,E2:Error + From<PakeratError>>(&self, input: Input<'a>,state: &mut C) -> Result<(Input<'a>, V), E2>{
        let (input,t) = self.parse(input,state)?;
        Ok((input,t.into()))
    }

}

impl<'a, T, O:Clone, C: Cache<'a, O>,F:Combinator<'a, T, O, C>> CombinatorExt<'a, T, O, C> for F{}
