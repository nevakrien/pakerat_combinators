//! Caching for combinator-based parsing.
//!
//! This module introduces the [`Cache`] trait, which provides storage for parsing results.  
//! Cached values should generally be cheap to clone since they are cloned for every parse that retrieves them.
//! Note that errors are also cached. The cache is responsible for detecting infinite recursion via [`CacheStatus::Pending`].
//!
//! A cache requires a usize id for knowing which slot to read.
//! In general try and cache every parse rule into its own dedicated id.
//! this is usally captured very nicely in an enum
//!
//! The two main implementations are [`FlexibleCache`] and [`BasicCache`].
//!
//! While [`FlexibleCache`] supports any key range, [`BasicCache`] is recommended where possible,
//! as it allows for better performance when the number of parse rules is known ahead of time.  
//!
//! ## Example: Structured Caching with `one_of!`
//!
//! ```rust
//! use pakerat_combinators::combinator::{Parsable,Combinator,CombinatorExt};
//! use pakerat_combinators::basic_parsers::{IdentParser, IntParser};
//! use pakerat_combinators::{one_of};
//! use pakerat_combinators::core::Input;
//! use pakerat_combinators::cache::{CachedComb, BasicCache};
//! use syn::buffer::TokenBuffer;
//! use proc_macro2::Ident;
//!
//! #[derive(Clone, Debug)]
//! enum ParsedValue {
//!     Ident(Ident),
//!     Number(i64),
//! }
//!
//! impl Parsable for ParsedValue{
//!    type Output<'a>= ParsedValue;//does not depend on input lifetime
//! }
//!
//!
//! #[derive(Clone, Copy, Debug)]
//! enum ParserType {
//!     Ident = 0,
//!     Number,
//! }
//! const CACHE_SIZE : usize = 2;
//!
//! impl Into<usize> for ParserType {
//!     fn into(self) -> usize {
//!         self as usize
//!     }
//! }
//! type MyCache<'a> = BasicCache::<'a,CACHE_SIZE, ParsedValue>;
//!
//! // Define a parser that can handle both identifiers and numbers.
//! let combined_parser = one_of!("expected an identifier or an integer",
//!     CachedComb::<_,ParsedValue>::new(
//!         IdentParser.map(ParsedValue::Ident), ParserType::Ident.into(), "infinite loop bug"),
//!     CachedComb::<_,ParsedValue>::new(
//!         IntParser.map(ParsedValue::Number), ParserType::Number.into(), "infinite loop bug")
//! );
//!
//! let tokens = "aaa 42".parse().unwrap();
//! let buffer = TokenBuffer::new2(tokens);
//! let input = Input::new(&buffer);
//!
//! let mut cache = MyCache::default();
//!
//! // Parse the first token (identifier) and store it in the cache
//! let (input, parsed_ident) = combined_parser.parse(input, &mut cache).unwrap();
//! assert!(matches!(parsed_ident, ParsedValue::Ident(_)));
//!
//! // Parse the next token (number) and store it in the cache
//! let (_, parsed_number) = combined_parser.parse(input, &mut cache).unwrap();
//! assert!(matches!(parsed_number, ParsedValue::Number(_)));
//! 
//! //now we trick the cache by making something with the same byte range
//! let tokens = "333 42".parse().unwrap();
//! let buffer = TokenBuffer::new2(tokens);
//! let input = Input::new(&buffer);
//!
//! // Parsing again should retrieve from the cache
//! let (_, cached_ident) = combined_parser.parse(input, &mut cache).unwrap();
//! assert!(matches!(cached_ident, ParsedValue::Ident(_)));
//! ```

use std::ops::Range;
use crate::core::Found;
use std::fmt;
use crate::combinator::Parsable;
use crate::combinator::Combinator;
use crate::combinator::Pakerat;
use crate::combinator::PakeratError;
use crate::core::Input;
use crate::core::ParseError;
use std::collections::HashMap;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::ops::Index;
use std::ops::IndexMut;

///a basic collection type for modifible maps
pub trait Collection<T = ()> {
    ///this should only return null when an error message is about to be printed
    fn get(&mut self, key: usize) -> Option<&mut T>;
}

#[repr(transparent)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixedCollection<T, const L: usize>(pub [T; L]);
impl<T, const L: usize> Collection<T> for FixedCollection<T, L> {
    fn get(&mut self, key: usize) -> Option<&mut T> {
        self.0.get_mut(key)
    }
}

impl<T: Default, const L: usize> Default for FixedCollection<T, L> {
    fn default() -> Self {
        Self(std::array::from_fn(|_| T::default()))
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HashCollection<T>(pub HashMap<usize, T>);
impl<T> Collection<T> for HashCollection<T> {
    fn get(&mut self, key: usize) -> Option<&mut T> {
        self.0.get_mut(&key)
    }
}

#[test]
fn hashes() {
    let mut map: HashCollection<Input> = HashCollection(HashMap::new());
    map.get(2);
}

#[derive(Default)]
pub enum CacheStatus<T> {
    #[default]
    Empty,
    Pending,
    Full(T),
}

impl<T: Clone> Clone for CacheStatus<T> {
    fn clone(&self) -> Self {
        match self {
            Self::Empty => Self::Empty,
            Self::Pending => Self::Pending,
            Self::Full(value) => Self::Full(value.clone()),
        }
    }
}

impl<T: Debug> Debug for CacheStatus<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, "CacheStatus::Empty"),
            Self::Pending => write!(f, "CacheStatus::Pending"),
            Self::Full(value) => f.debug_tuple("CacheStatus::Full").field(value).finish(),
        }
    }
}

impl<T: PartialEq> PartialEq for CacheStatus<T> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Empty, Self::Empty) => true,
            (Self::Pending, Self::Pending) => true,
            (Self::Full(a), Self::Full(b)) => a == b,
            _ => false,
        }
    }
}

impl<T: Eq> Eq for CacheStatus<T> {}
// #[derive(Default)]
pub struct CacheEntry<'a, T: Parsable = ()>(
    pub CacheStatus<Pakerat<(Input<'a>, T::Output<'a>)>>,
);

impl<'a, T: Parsable> fmt::Debug for CacheEntry<'a, T> where <T as Parsable>::Output<'a>: Debug{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result  {
        match &self.0 {
            CacheStatus::Full(pakerat) => {
                match pakerat {
                    Ok((input, output)) => write!(
                        f,
                        "CacheEntry::Full {{ start_token: {:?}, source_text: {:?}, output: {:?} }}",
                        Found::start_of(*input),
                        input.span().source_text(),
                        output
                    ),
                    Err(err) => write!(f, "CacheEntry::Full {{ error: {:?} }}", err),
                }
            }
            CacheStatus::Empty => write!(f, "CacheEntry::Empty"),
            CacheStatus::Pending => write!(f, "CacheEntry::Pending"),
        }
    }
}


impl<T: Parsable> Default for CacheEntry<'_, T> {
    fn default() -> Self {
        CacheEntry(CacheStatus::default())
    }
}

impl<'a, T: Parsable> From<CacheStatus<Pakerat<(Input<'a>, T::Output<'a>)>>>
    for CacheEntry<'a, T>
{
    fn from(x: CacheStatus<Pakerat<(Input<'a>, <T as Parsable>::Output<'a>)>>) -> Self {
        Self(x)
    }
}

impl<'a, T: Parsable> From<CacheEntry<'a, T>>
    for CacheStatus<Pakerat<(Input<'a>, T::Output<'a>)>>
{
    fn from(x: CacheEntry<'a, T>) -> Self {
        x.0
    }
}

impl<'a, T: Parsable> Clone for CacheEntry<'a, T>
where
    T::Output<'a>: Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<'a, T> CacheEntry<'a, T>
where
    T: Parsable,
    T::Output<'a>: Clone,
{
    ///this is used to finalize the result of a search
    ///
    ///it will automatically move pending results to full errors and panic on an empty cache
    pub fn finalize<F: FnOnce() -> ParseError>(
        &mut self,
        err_f: F,
    ) -> Pakerat<(Input<'a>, T::Output<'a>)> {
        // panic!("this is the bug");
        match &self.0 {
            CacheStatus::Empty => unreachable!("bad finalize call on an empty cache"),
            CacheStatus::Pending => {
                let err = Err(PakeratError::Recursive(err_f()));
                self.0 = CacheStatus::Full(err.clone());
                err
            }
            CacheStatus::Full(res) => res.clone(),
        }
    }
}

pub type ArrayCache<'a, const L: usize, T = ()> = FixedCollection<CacheEntry<'a, T>, L>;

///a cache that allways returns a value in get
#[repr(transparent)]
#[derive(Clone)]
pub struct HashCache<'a, T: Parsable = ()>(pub HashMap<usize, CacheEntry<'a, T>>)
where
    T::Output<'a>: Clone;
impl<'a, T: Parsable> Collection<CacheEntry<'a, T>> for HashCache<'a, T>
where
    T::Output<'a>: Clone,
{
    #[inline]
    fn get(&mut self, key: usize) -> Option<&mut CacheEntry<'a, T>> {
        Some(self.0.entry(key).or_insert(CacheStatus::Empty.into()))
    }
}

// Implement `Index` for immutable access
impl<'a, T: Parsable> Index<usize> for HashCache<'a, T>
where
    T::Output<'a>: Clone,
{
    type Output = CacheEntry<'a, T>;

    fn index(&self, key: usize) -> &Self::Output {
        self.0.get(&key).unwrap_or(&CacheEntry(CacheStatus::Empty))
    }
}
impl<'a, T: Parsable> IndexMut<usize> for HashCache<'a, T>
where
    T::Output<'a>: Clone,
{
    fn index_mut(&mut self, key: usize) -> &mut Self::Output {
        self.0.entry(key).or_insert(CacheStatus::Empty.into())
    }
}

impl<'a, T: Parsable> Default for HashCache<'a, T>
where
    T::Output<'a>: Clone,
{
    fn default() -> Self {
        HashCache(HashMap::new())
    }
}

#[test]
fn hash_cache() {
    let mut map: HashCache<i8> = HashCache::default();
    assert!(matches!(
        *map.get(3).unwrap(),
        CacheEntry(CacheStatus::Empty)
    ));
}

pub trait CacheSpot<'a, T: Parsable = ()>: Collection<CacheEntry<'a, T>> {
    fn clear(&mut self);
}

impl<'a, const L: usize, T: Parsable> CacheSpot<'a, T> for ArrayCache<'a, L, T>
where
    T::Output<'a>: Clone,
{
    fn clear(&mut self) {
        for x in self.0.iter_mut() {
            *x = CacheStatus::Empty.into();
        }
    }
}

impl<'a, T: Parsable> CacheSpot<'a, T> for HashCache<'a, T>
where
    T::Output<'a>: Clone,
{
    fn clear(&mut self) {
        self.0 = HashMap::new();
    }
}


/// A `Cache` is meant to be used with [`Combinator`].
///
/// Caching guarantees linear time complexity in all public APIs (including recursive ones).
/// This is achieved by erroring when the same input is attempted to be parsed a second time.
///
/// In the worst case, the time complexity is O(inputs_len * parse_types).
///
/// As a bonus, caching also prevents accidental infinite recursion.
pub trait Cache<'a, T: Parsable = ()>
where
    T::Output<'a>: Clone,
{
    /// The type of cache slot stored in the cache
    type Item: CacheSpot<'a, T>;

    /// Retrieves the cache for the byte anotated by slot
    fn get_slot(&mut self, slot: Range<usize>) -> &mut Self::Item;
}

#[derive(Debug)]
pub struct DebugCache<'a,C,T=()> where T:Parsable,T::Output<'a>: Clone,C : Cache<'a,T>{
    pub inner:C,
    pub _phantom:PhantomData<(T,Input<'a>)>
}

impl<'a,T,C> Cache<'a,T> for DebugCache<'a,C,T> where T:Parsable,T::Output<'a>: Clone,C : Cache<'a,T>{
type Item = C::Item;

fn get_slot(&mut self, id: Range<usize>) -> &mut <Self as Cache<'a, T>>::Item {
    println!("getting slot {:?}",id);
    self.inner.get_slot(id)
}
}

impl<'a,T,C>  DebugCache<'a,C,T> where T:Parsable,T::Output<'a>: Clone,C : Cache<'a,T>{
    pub fn new(inner:C) -> Self{
        Self{inner,_phantom:PhantomData}
    }
}

///A dynamic runtime cache derived from [`Cache`]
pub trait DynCache<'a, T = ()> {
    /// Retrieves the cache for the byte anotated by slot
    fn get_dyn_slot(&mut self, slot: Range<usize>) -> &mut dyn CacheSpot<'a, T>;
}

impl<'a, T: Parsable, C: Cache<'a, T>> DynCache<'a, T> for C
where
    T::Output<'a>: Clone,
{
    fn get_dyn_slot(&mut self, slot: Range<usize>) -> &mut dyn CacheSpot<'a, T> {
        self.get_slot(slot) // Automatically converts to `dyn CacheSpot`
    }
}



/// this function implements caching which will never break any valid peg parser and will never return wrong results.
///
/// it detects most potential infinite loops by keeping track of all the pending calls.
///
/// however it will still reject some grammers.
/// for instance "expr + term => expr" would not work because it causes an infinite left recursive loop.
/// but "term + expr => expr" will work
pub fn parse_cached<'a, T, P, FE>(
    cache: &mut dyn DynCache<'a, T>,
    input: Input<'a>,
    key: usize,
    parser: &P,
    recurse_err: FE,
) -> Pakerat<(Input<'a>, T::Output<'a>)>
where
    T: Parsable,
    for<'b> T::Output<'b>: Clone,

    P: Combinator<T, T> + ?Sized,
    FE: FnOnce() -> ParseError,
{
    let id = input.span().byte_range();
    let spot = cache.get_dyn_slot(id.clone()).get(key).expect("missing key");
    match &spot.0 {
        CacheStatus::Full(res) => res.clone(),
        CacheStatus::Empty => {
            spot.0 = CacheStatus::Pending;
            let ans = parser.parse(input, cache);

            //need to get spot again since parse may of changed it
            let spot = cache.get_dyn_slot(id).get(key).expect("missing key");
            spot.0 = CacheStatus::Full(ans.clone());
            ans
        }
        CacheStatus::Pending => {
            let err = Err(PakeratError::Recursive(recurse_err()));
            spot.0 = CacheStatus::Full(err.clone());
            err
        }
    }
}

// /// this function implements caching which will never break any valid peg parser and will never return wrong results.
// ///
// /// it detects most potential infinite loops by keeping track of all the pending calls.
// ///
// /// however it will still reject some grammers.
// /// for instance "expr + term => expr" would not work because it causes an infinite left recursive loop.
// /// but "term + expr => expr" will work
// pub fn parse_cached<'a,T,P,FE>(cache: &mut dyn DynCache<'a,T>,input:Input<'a>, key: usize ,parser:&P,recurse_err:FE) -> Pakerat<(Input<'a>,T)>
// where
// T:Clone ,
// P:Combinator<T,T>,
// FE:FnOnce() -> ParseError,
// {
// 	let id = input.span().byte_range().start;
// 	let spot = cache.get_dyn_slot(id).get(key).expect("missing key");
// 	match spot{
// 		CacheStatus::Full(res) => res.clone(),
// 		CacheStatus::Empty => {
// 			*spot = CacheStatus::Pending;
// 			let ans = parser.parse(input,cache);

// 			//need to get spot again since parse may of changed it
// 			let spot = cache.get_dyn_slot(id).get(key).expect("missing key");
// 			*spot = CacheStatus::Full(ans.clone());
// 			ans
// 		}
// 		CacheStatus::Pending => {
// 			let err =  Err(PakeratError::Recursive(recurse_err()));
//         	*spot = CacheStatus::Full(err.clone());
//         	err
// 		},
// 	}
// }

impl<'a, T: Parsable, C> Cache<'a, T> for HashMap<Range<usize>, C>
where
    C: CacheSpot<'a, T> + Default,
    <T as Parsable>::Output<'a>: Clone,
{
    type Item = C;
    fn get_slot(&mut self, slot: Range<usize>) -> &mut C {
        self.entry(slot).or_default()
    }
}

/// this cache is fairly performent, it relies on knowing the number of parse rules ahead of time
pub type BasicCache<'a, const L: usize, T = ()> = HashMap<Range<usize>, ArrayCache<'a, L, T>>;
/// this cache can work with any id range.
pub type FlexibleCache<'a, T = ()> = HashMap<Range<usize>, HashCache<'a, T>>;

/// A combinator that caches the results of an inner parser.
///
/// This allows detecting infinite loops and excuting in linear time. 
/// see [`Cache`] and [`parse_cached`] for details.
///
/// # Example
/// ```
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::core::Input;
/// use pakerat_combinators::cache::{CachedComb, BasicCache, CacheStatus};
/// use proc_macro2::Ident;
/// use syn::buffer::TokenBuffer;
///
/// // --- Step 1: Parse an identifier and cache it ---
/// let tokens = "aaa".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
/// let mut cache = BasicCache::<1,Ident>::new();
/// let ident_parser = CachedComb::new(IdentParser, 0, "infinite loop bug");
///
/// // Parse the identifier and store it in the cache
/// let (_, parsed_ident) = ident_parser.parse(input, &mut cache).unwrap();
/// assert_eq!(parsed_ident.to_string(), "aaa");
///
/// // --- Step 2: Trick the cache by using the same byte range ---
/// let tokens = "333".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
/// // Parsing again should retrieve from the cache
/// let (_, cached_ident) = ident_parser.parse(input, &mut cache).unwrap();
/// assert_eq!(cached_ident.to_string(), "aaa"); // Cache returned the old entry
///
///```

pub struct CachedComb<INNER, T = ()>
where
    INNER: Combinator<T, T>,
    T: Parsable,
    for<'b> T::Output<'b>: Clone,
{
    pub inner: INNER,
    pub key: usize,
    pub message: &'static str,

    ///used so we can have generics
    pub _phantom: PhantomData<T>,
}

// pub type UsizeCachedComb<'a, INNER,T =()> = CachedComb<'a,INNER, T,FlexibleCache<'a,T>>;
// pub type FixedCachedComb<'a,const L: usize, INNER,T =()> = CachedComb<'a,INNER, T ,BasicCache<'a, L,T>>;

impl<INNER, T> Combinator<T, T> for CachedComb<INNER, T>
where
    INNER: Combinator<T, T>,
    T: Parsable,
    for<'b> T::Output<'b>: Clone,
{
    fn parse<'a>(
        &self,
        input: Input<'a>,
        cache: &mut dyn DynCache<'a, T>,
    ) -> Pakerat<(Input<'a>, T::Output<'a>)> {
        parse_cached(cache, input, self.key, &self.inner, || {
            ParseError::Message(input.span(), self.message)
        })
    }
}

impl<INNER, T> CachedComb<INNER, T>
where
    INNER: Combinator<T, T>,
    T: Parsable,
    for<'b> T::Output<'b>: Clone,
{
    pub fn new(inner: INNER, key: usize, message: &'static str) -> Self {
        CachedComb {
            inner,
            key,
            message,
            _phantom: PhantomData,
        }
    }
}
