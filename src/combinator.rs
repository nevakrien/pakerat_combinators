
use crate::cache::DynCache;
use syn::Lifetime;
use proc_macro2::Span;
use proc_macro2::Literal;
use proc_macro2::Punct;
use proc_macro2::TokenTree;
use proc_macro2::Group;
use proc_macro2::Delimiter;
use proc_macro2::Ident;
use std::marker::PhantomData;
use crate::core::ParseError;
// use crate::cache::CacheExt;
use std::error::Error;
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

// pub struct State<'a,'me,Extra = (),T = (), O: Clone = T, C: Cache<'a, O> = FlexibleCache<'a,T>>{
//     pub cache:&'me mut C,
//     pub extra:Extra,
//     _phantom:PhantomData<(Input<'a>,T,O)>
// }

// impl<'a,'me,T, O: Clone, C: Cache<'a, O>, Extra> Cache<'a,O> for  State<'a,'me,Extra,T, O, C>{
// type Item = C::Item;
// fn get_slot(&mut self, id: usize) -> &mut Self::Item { self.cache.get_slot(id)}
// }

// impl<'a,'me,T, O: Clone, C: Cache<'a, O>>
// State<'a,'me,(),T, O, C>{
//     pub fn new_empty(cache:&'me mut C) -> Self{
//         State{
//             cache,
//             extra: (),
//             _phantom:PhantomData
//         }
//     }

//     pub fn make_child<Extra>(&mut self,extra:Extra) -> State<'a,'_,Extra,T, O, C>{
//         State{
//             cache: self.cache,
//             extra,
//             _phantom:PhantomData
//         }
//     }
// }

// impl<'a,'me,T, O: Clone, C: Cache<'a, O>> 
// From<&'me mut C> for State<'a,'me,(),T, O, C>{
// fn from(cache: &'me mut C) -> Self {State::new_empty(cache)}
// }

// impl<'a,'me,'inner,Extra,T, O: Clone, C: Cache<'a, O>>
// State<'a,'me,&'inner mut Extra,T, O, C>{
//     pub fn new(cache:&'me mut C,extra:&'inner mut Extra) -> Self{
//         State{cache,extra,_phantom:PhantomData}
//     }

//     pub fn make_child<Added>(&mut self,add:Added) -> State<'a,'_, (&mut Extra,Added),T, O, C>{
//         let extra : (&mut Extra,Added)= (self.extra,add);
//         State{
//             cache: self.cache,
//             extra,
//             _phantom:PhantomData
//         }
//     }
// }

// impl<'a,'b,'parent,Parent,Added,T, O: Clone, C: Cache<'a, O>>
// State<'a,'b, (&'parent mut Parent,Added),T, O, C>{
//     pub fn as_parent(&mut self) -> State<'a,'_,&mut Parent,T, O, C>{
//         State{
//             cache:self.cache,
//             extra:self.extra.0,
//             _phantom:PhantomData
//         }
//     }
// }


/// A trait that defines the output type of a combinator.
///
/// This trait allows the output type to depend on the input's lifetime,
/// making it possible to represent parsed values that borrow from their source.
///
/// # Associated Type
/// - `Output<'a>`: The result of parsing, which may have a lifetime tied to `'a`.
///
/// # Purpose
/// - Enables lifetimes in combinator outputs to be properly handled.
/// - Used to abstract over different output types in parsing.
pub trait BorrowParse {
    /// The output type produced by the combinator.
    ///
    /// - `'a` represents the lifetime of the input being parsed.
    /// - The output may be owned (`T::Output<'a> = T`) or borrow from input (`T::Output<'a> = Input<'a>`).
    type Output<'a>;
}


#[macro_export]
/// Implements the [`BorrowParse`] trait for multiple types.
///
/// This macro provides a blanket implementation where `Output<'a>` is simply `Self`,
/// meaning the type does not borrow from the input.
///
/// # Usage
/// ```ignore
/// impl_borrow_parse!(u8, u16, u32, String, Vec<u8>);
/// ```
/// Expands to:
/// ```ignore
/// impl BorrowParse for u8 {
///     type Output<'a> = u8;
/// }
/// impl BorrowParse for String {
///     type Output<'a> = String;
/// }
/// ```
///
/// # Limitations
/// - This macro is for **fully owned types**.
/// - If a type borrows from input (e.g., `&'a str`), a manual implementation is needed.
macro_rules! impl_borrow_parse {
    ($($t:ty),*) => {
        $(impl $crate::combinator::BorrowParse for $t {
            type Output<'a> = $t;
        })*
    };
}
// Specialization is now valid
impl BorrowParse for Input<'_> {
    type Output<'a> = Input<'a>;
}


// Implement `BorrowParse` for common types
impl_borrow_parse!((),u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64, char, bool, String);
impl_borrow_parse!(Ident,Punct,Literal,TokenTree,Group,Delimiter,Span,Lifetime);

impl<T:BorrowParse> BorrowParse for Vec<T>{
    type Output<'a> = Vec<T::Output<'a>>;
}

impl<T:BorrowParse> BorrowParse for Option<T>{
    type Output<'a> = Option<T::Output<'a>>;
}

macro_rules! impl_borrow_parse_for_tuples {
    ($( $T:ident ),*) => {
        impl<$( $T: BorrowParse ),*> BorrowParse for ($( $T, )*) {
            type Output<'a> = ($( $T::Output<'a>, )*);
        }
    };
}

// Implement for common tuple sizes
impl_borrow_parse_for_tuples!(T1, T2);
impl_borrow_parse_for_tuples!(T1, T2, T3);
impl_borrow_parse_for_tuples!(T1, T2, T3, T4);
impl_borrow_parse_for_tuples!(T1, T2, T3, T4, T5);





/// A `Combinator` is a fundamental parser used throughout this crate.
/// 
/// These combinators are designed to behave similarly to closures and, in many cases, 
/// compile down to simple function pointers for efficiency. They serve as building blocks 
/// for more complex parsing operations, ensuring flexibility while maintaining performance.
pub trait Combinator<T : BorrowParse = (), O : BorrowParse = T> {
    // type Output<'b>;

    /// Parses the given `input`, utilizing the provided cache `state` for intermediate storage.
    ///
    /// Returns a [`Pakerat`] result containing the remaining input and the parsed output.
    fn parse<'a>(&self, input: Input<'a>, state: &mut dyn DynCache<'a,O>) -> Pakerat<(Input<'a>, T::Output<'a>)>;

    /// Parses the input while discarding the output.
    ///
    /// This method exists to avoid allocating memory for parses that are ignored.
    /// For the most parts users are expected to not really consider it.
    fn parse_ignore<'a>(&self, input: Input<'a>, state: &mut dyn DynCache<'a,O>) -> Pakerat<Input<'a>> {
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
            O: BorrowParse,
            T: BorrowParse,
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
            O: BorrowParse,
            T: BorrowParse,
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
    O: BorrowParse,
    T: BorrowParse,
{
    fn parse<'a>(&self, input: Input<'a>, state: &mut dyn DynCache<'a, O>) -> Pakerat<(Input<'a>, T::Output<'a>)> {
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
    fn dumb(_maybe: Maybe::<&'static dyn Combinator>){

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
    use std::rc::Rc;
    use crate::cache::FlexibleCache;
    
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
    let closure: &dyn for<'a> Fn(
        Input<'a>,
        &mut dyn DynCache<'a, ()>,
    ) -> Pakerat<(Input<'a>, ())> = &|input, cache| {
        failing_parser(input, cache).map_err(|e| {
            e.map(|e| {
                let err: syn::Error = e.into(); // Explicitly create the `err` variable
                let mut new_err = syn::Error::new(err.span(), "failed doing something");
                new_err.combine(err); // Capture the original error
                ParseError::Syn(new_err) // Return the transformed error
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



pub struct CodeRef<'a>{
    pub start:Input<'a>,
    pub end:Input<'a>,
}

pub trait CombinatorExt<T: BorrowParse, O: BorrowParse>: Combinator<T, O> {
    fn parse_recognize<'a>(
        &self,
        input: Input<'a>,
        state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<CodeRef<'a>> {
        Ok(CodeRef {
            start: input,
            end: self.parse_ignore(input, state)?,
        })
    }

    fn compose<F, M>(self, make: F) -> M
    where
        F: FnOnce(Self) -> M,
        Self: Sized,
    {
        make(self)
    }

    fn map<F, T2>(
        self,
        map_fn: F,
    ) -> MapCombinator<Self, F, T, T2, O>
    where
        F: for<'a> Fn(T::Output<'a>) -> T2,
        T2:for<'a> BorrowParse<Output<'a> = T2>,
        Self: Sized,
    {
        MapCombinator {
            inner: self,
            map_fn,
            _phantom: PhantomData,
        }
    }

    fn parse_into<'a,V, E2>(&self, input: Input<'a>, state: &mut dyn DynCache<'a, O>) -> Result<(Input<'a>, V), E2>
    where
        V: From<T::Output<'a>>,
        E2: Error + From<PakeratError>,
    {
        let (input, t) = self.parse(input, state)?;
        Ok((input, t.into()))
    }
}

impl<T: BorrowParse, O: BorrowParse, F: Combinator<T, O>> CombinatorExt<T, O> for F {}



/// A combinator that transforms the output of another parser using a mapping function.
pub struct MapCombinator<P, F, T, T2, O>
where
    P: Combinator<T, O>,
    F: for<'a> Fn(T::Output<'a>) -> T2,
    T: BorrowParse,
    T2: BorrowParse,
    O: BorrowParse,
{
    inner: P,
    map_fn: F,
    _phantom: PhantomData<(T, T2, O)>,
}

impl<P, F, T, T2, O> Combinator<T2, O> for MapCombinator<P, F, T, T2, O>
where
    P: Combinator<T, O>,
    T: BorrowParse,
    T2: for<'a> BorrowParse<Output<'a> = T2>,
    F: for<'a> Fn(T::Output<'a>) -> T2,
    O: BorrowParse,
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        state: &mut dyn DynCache<'a, O>,
    ) -> Pakerat<(Input<'a>, T2::Output<'a>)> {
        let (input, output) = self.inner.parse(input, state)?;
        Ok((input, (self.map_fn)(output)))
    }
}
