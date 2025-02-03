//! Caching for combinator-based parsing.
//!
//! This module introduces the [`Cache`] trait, which provides storage for parsing results.  
//! Cached values should generally be cheap to clone since they are cloned for every parse that retrieves them.
//! Note that errors are also cached. The cache is responsible for detecting infinite recursion via [`CacheStatus::Pending`].
//!
//! The two main implementations are [`FlexibleCache`] and [`BasicCache`].
//! 
//! Users are encouraged to define a custom enum for cache slots, implementing `Into<usize>`
//! to provide a structured way to manage different parse states. This improves clarity and
//! reduces the risk of collisions when multiple rules are cached.
//!
//! While [`FlexibleCache`] supports any key range, [`BasicCache`] is recommended where possible,
//! as it allows for better performance when the number of parse rules is known ahead of time.  
//!
//! ## Example: Structured Caching with `one_of!`
//!
//! ```rust
//! use pakerat_combinators::combinator::Combinator;
//! use pakerat_combinators::basic_parsers::{IdentParser, IntParser};
//! use pakerat_combinators::one_of;
//! use pakerat_combinators::core::Input;
//! use crate::pakerat_combinators::combinator::CombinatorExt;
//! use pakerat_combinators::cache::{CachedComb, BasicCache, FixedCachedComb};
//! use syn::buffer::TokenBuffer;
//! use proc_macro2::Ident;
//!
//! /// Enum representing different possible parsed values stored in the cache.
//! #[derive(Clone, Debug)]
//! enum ParsedValue {
//!     Ident(Ident),
//!     Number(i64),
//! }
//!
//! /// Enum representing different parser types, each assigned a unique ID.
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
//! type MyCacheComb<'a,INNER,T> = FixedCachedComb::<'a,CACHE_SIZE,INNER,T>;
//!
//! // Define a parser that can handle both identifiers and numbers.
//! let combined_parser = one_of!("expected an identifier or an integer",
//!     MyCacheComb::<_,ParsedValue>::new(
//!         IdentParser.map(ParsedValue::Ident), ParserType::Ident.into(), "Cache miss error"),
//!     MyCacheComb::<_,ParsedValue>::new(
//!         IntParser.map(ParsedValue::Number), ParserType::Number.into(), "Cache miss error")
//! );
//!
//! let tokens = "variable 42".parse().unwrap();
//! let buffer = TokenBuffer::new2(tokens);
//! let input = Input::new(&buffer);
//!
//! // Create a cache instance with structured storage
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
//! // Parsing again should retrieve from the cache
//! let (_, cached_ident) = combined_parser.parse(Input::empty(), &mut cache).unwrap();
//! assert!(matches!(cached_ident, ParsedValue::Ident(_)));
//! ```


use crate::core::ParseError;
use std::marker::PhantomData;
use crate::combinator::Combinator;
use crate::combinator::Pakerat;
use crate::combinator::PakeratError;
use crate::core::Input;
use std::ops::IndexMut;
use std::ops::Index;
use std::fmt::Debug;
use std::collections::HashMap;


///a basic collection type for modifible maps
pub trait Collection< T  = ()>{
	///this should only return null when an error message is about to be printed
	fn get(&mut self,key:usize) -> Option<&mut T>;
}

#[repr(transparent)]
#[derive(Debug,Clone,PartialEq,Eq)]
pub struct FixedCollection<T  ,const L: usize >(pub [T;L]);
impl<T ,const L: usize > Collection<T> for FixedCollection<T,L>{
	fn get(&mut self, key: usize) -> Option<&mut T>  {
		self.0.get_mut(key)
	}
}

impl<T: Default, const L: usize> Default for FixedCollection<T, L> {
    fn default() -> Self {
        Self(std::array::from_fn(|_| T::default()))
    }
}

#[repr(transparent)]
#[derive(Debug,Clone,PartialEq,Eq)]
pub struct HashCollection<T>(pub HashMap<usize,T>);
impl<T> Collection<T> for HashCollection<T>{
	fn get(&mut self, key: usize) -> Option<&mut T>  {
		self.0.get_mut(&key)
	}
}

#[test]
fn hashes() {
	let mut map: HashCollection<Input> = HashCollection(HashMap::new());
	map.get(2);
}

#[derive(Default)]
pub enum CacheStatus<T>{
	#[default]
	Empty,
	Pending,
	Full(T)	
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
pub type CacheEntry<'a,T = ()> = CacheStatus<Pakerat<(Input<'a>,T)>>;

impl<'a, T> CacheEntry<'a, T>
where
    T: Clone,
{	
	///this is used to finalize the result of a search
	///
	///it will automatically move pending results to full errors and panic on an empty cache
    pub fn finalize<F: FnOnce() -> ParseError>(&mut self, err_f: F) -> Pakerat<(Input<'a>,T)> {
        match self {
            CacheStatus::Empty => unreachable!("bad finalize call on an empty cache"),
            CacheStatus::Pending => {
            	let err =  Err(PakeratError::Recursive(err_f()));
            	*self = CacheStatus::Full(err.clone());
            	err
            	
            },
            CacheStatus::Full(res) => res.clone(),
        }
    }
}




pub type ArrayCache<'a,const L: usize,T = ()> = FixedCollection<CacheEntry<'a,T>, L>;

#[test]
fn array_cache() {
	let mut map: ArrayCache<9,i8> = ArrayCache::default();
	assert!(matches!(*map.get(3).unwrap(),CacheStatus::Empty));
}

///a cache that allways returns a value in get
#[repr(transparent)]
#[derive(Clone)]
pub struct HashCache<'a,T : Clone = ()>(pub HashMap<usize,CacheEntry<'a,T>>);
impl<'a,T : Clone> Collection<CacheEntry<'a,T>> for HashCache<'a,T>{
	#[inline]
	fn get(&mut self, key: usize) -> Option<&mut CacheEntry<'a,T>>  {
		Some(self.0.entry(key).or_insert(CacheStatus::Empty))
	}
}

// Implement `Index` for immutable access
impl<'a, T:Clone> Index<usize> for HashCache<'a, T> {
    type Output = CacheEntry<'a,T>;

    fn index(&self, key: usize) -> &Self::Output {
        self.0.get(&key).unwrap_or(&CacheStatus::Empty)
    }
}
impl<T:Clone> IndexMut<usize> for HashCache<'_,T> {
    fn index_mut(&mut self, key: usize) -> &mut Self::Output {
        self.0.entry(key).or_insert(CacheStatus::Empty)
    }
}

impl<T:Clone> Default for HashCache<'_,T>{

fn default() -> Self { HashCache(HashMap::new()) }
}

#[test]
fn hash_cache() {
	let mut map: HashCache<i8> = HashCache::default();
	assert!(matches!(*map.get(3).unwrap(),CacheStatus::Empty));
}

pub trait CacheSpot<'a, T:Clone=()>: Collection<CacheEntry<'a, T>> {
	fn clear(&mut self);
}

impl<'a, const L: usize,T:Clone> CacheSpot<'a, T> for ArrayCache<'a,L,T> 
{	
	fn clear(&mut self) {
		for x in self.0.iter_mut() {
			*x = CacheStatus::Empty;
		}
	}
}

impl<'a,T:Clone> CacheSpot<'a, T> for HashCache<'a,T> 
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
pub trait Cache<'a, T : Clone = ()> {
    /// The type of cache slot stored in the cache
    type Item: CacheSpot<'a, T>;

    /// Retrieves the cache for the byte anotated by slot
    fn get_slot(&mut self, slot: usize) -> &mut Self::Item;

    /// this function implements caching which will never break any valid peg parser and will never return wrong results.
	///
	/// it detects most potential infinite loops by keeping track of all the pending calls. 
	///
	/// however it will still reject some grammers.
	/// for instance "expr + term => expr" would not work because it causes an infinite left recursive loop. 
	/// but "term + expr => expr" will work
    fn parse_cached<P,FE>(&mut self,input:Input<'a>, key: usize ,parser:&P,recurse_err:FE) -> Pakerat<(Input<'a>,T)>
    where P:Combinator<'a,T,T,Self> + ?Sized, FE:FnOnce() -> ParseError, Self: Sized
    {	
    	let id = input.span().byte_range().start;
    	let spot = self.get_slot(id).get(key).expect("missing key");
    	match spot{
    		CacheStatus::Full(res) => res.clone(),
    		CacheStatus::Empty => {
    			*spot = CacheStatus::Pending;
    			let ans = parser.parse(input,self);

    			//need to get spot again since parse may of changed it
    			let spot = self.get_slot(id).get(key).expect("missing key");
    			*spot = CacheStatus::Full(ans.clone());
    			ans
    		}
    		CacheStatus::Pending => {
    			let err =  Err(PakeratError::Recursive(recurse_err()));
            	*spot = CacheStatus::Full(err.clone());
            	err
    		},
    	}
    }

}

impl<'a, T : Clone , C > Cache<'a,T> for HashMap<usize,C> where C : CacheSpot<'a, T> + Default{
	type Item = C;
	fn get_slot(&mut self, slot: usize) -> &mut C {
		self.entry(slot).or_default()
	}
}

/// this cache is fairly performent, it relies on knowing the number of parse rules ahead of time
pub type BasicCache<'a,const L: usize,T=()>= HashMap<usize, ArrayCache<'a,L, T>>;
/// this cache can work with any id range.
pub type FlexibleCache<'a,T=()>= HashMap<usize, HashCache<'a, T>>;
// pub type StrCache<'a,T=(),E=syn::Error>= HashMap<usize, HashCache<'a,&'a str, T, E>>;

impl<'a, T: Clone, C> Cache<'a, T> for Vec<C>
where
    C: CacheSpot<'a, T> + Default,
{
    type Item = C;

    fn get_slot(&mut self, slot: usize) -> &mut C {
        if slot >= self.len() {
            self.resize_with(slot + 1,C::default);
        }
        &mut self[slot]
    }
}


/// A combinator that caches the results of an inner parser, reducing redundant computations.
///
/// ## Type Alias Recommendation
/// Since `CachedComb` has many generics, it's recommended to create a type alias for ease of use.
/// A good pattern is to define an alias that fits your cache setup:
///
/// ```rust
/// use pakerat_combinators::cache::{CachedComb, FlexibleCache};
///
/// type MyCachedParser<'a, P> = CachedComb<'a, P, (), FlexibleCache<'a, ()>>;
/// ```
///
/// This alias simplifies usage, assuming you want:
/// - `usize` as the cache key type.
/// - A `FlexibleCache` for storing results.
/// - Error messages stored as `&'static str`.
///
/// ## Example Usage
/// Below are examples of using `CachedComb` with `UsizeCachedComb` and `FixedCachedComb`.
///
/// ### Using `UsizeCachedComb`
/// ```rust
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::core::Input;
/// use pakerat_combinators::cache::{CachedComb, FlexibleCache,UsizeCachedComb};
/// use syn::buffer::{TokenBuffer};
///
///
/// let tokens = "cached_var".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
/// let my_parser = UsizeCachedComb::new(IdentParser, 0, "Cache miss error");
///
/// let mut cache = FlexibleCache::<_>::default();
/// let (_, parsed_ident) = my_parser.parse(input, &mut cache).unwrap();
///
/// assert_eq!(parsed_ident.to_string(), "cached_var");
///
/// // Parsing again should retrieve from the cache (even if the input is diffrent)
/// let (_, cached_ident) = my_parser.parse(Input::empty(), &mut cache).unwrap();
/// assert_eq!(cached_ident.to_string(), "cached_var");
/// ```
///
/// ### Using `FixedCachedComb` with `ArrayCache`
/// ```rust
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::core::Input;
/// use pakerat_combinators::cache::{CachedComb, BasicCache,FixedCachedComb};
/// use syn::buffer::{TokenBuffer};
/// use proc_macro2::Ident;
///
///
/// let tokens = "fixed_cached_var".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
/// let input = Input::new(&buffer);
///
/// let my_parser = FixedCachedComb::<8, _,_>::new(IdentParser, 0, "Cache miss error");
///
/// let mut cache = BasicCache::<8,Ident>::new();
/// let (_, parsed_ident) = my_parser.parse(input, &mut cache).unwrap();
///
/// assert_eq!(parsed_ident.to_string(), "fixed_cached_var");
///
/// // Parsing again should retrieve from the cache (even if the input is diffrent)
/// let (_, cached_ident) = my_parser.parse(Input::empty(), &mut cache).unwrap();
/// assert_eq!(cached_ident.to_string(), "fixed_cached_var");
/// ```
pub struct CachedComb<'a, INNER,T =(), C = FlexibleCache<'a,T>>
where
    INNER: Combinator<'a, T, T,C>,
    T: Clone,
    C: Cache<'a, T>,

{   
    pub inner: INNER,
    pub key:usize,
    pub message:&'static str,

    ///used so we can have generics
    pub _phantom: PhantomData<(Input<'a>, T,C)>,
}

pub type UsizeCachedComb<'a, INNER,T =()> = CachedComb<'a,INNER, T,FlexibleCache<'a,T>>;
pub type FixedCachedComb<'a,const L: usize, INNER,T =()> = CachedComb<'a,INNER, T ,BasicCache<'a, L,T>>;

impl<'a, INNER,T, C> Combinator<'a, T, T,C> for CachedComb <'a,INNER, T,C>
where  
	INNER: Combinator<'a, T, T,C>,
    T: Clone,
    C: Cache<'a, T>,
{

    fn parse(&self, input: Input<'a>, cache: &mut C) -> Pakerat<(Input<'a>, T)> { 
    	cache.parse_cached(input,self.key,&self.inner,|| {ParseError::Syn(syn::Error::new(input.span(),self.message.to_string()))})
    }
}

impl<'a,INNER, T ,C> CachedComb<'a,INNER, T ,C> 

where
    INNER: Combinator<'a, T, T,C>,
    T: Clone,
    C: Cache<'a, T>,
{
	pub fn new(inner:INNER,key:usize,message:&'static str) -> Self{
		CachedComb{inner,key,message,_phantom:PhantomData}
	}
}