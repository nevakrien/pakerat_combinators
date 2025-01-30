use std::fmt::Display;
use std::marker::PhantomData;
use crate::combinator::Combinator;
use crate::combinator::Pakerat;
use crate::combinator::PakeratError;
use std::error::Error;
use syn::buffer::Cursor;
use std::ops::IndexMut;
use std::ops::Index;
use std::fmt::Debug;
use std::collections::HashMap;
use std::hash::Hash;

pub trait Keyble<K  = usize>{
	fn get_key(self) -> K;
}

impl<K:Clone> Keyble<K> for K{
	#[inline]
	fn get_key(self) -> K{
		self
	}
}

impl<K:Clone> Keyble<K> for &K{
	#[inline(always)]
	fn get_key(self) -> K{
		(*self).clone()
	}
}



///a basic collection type for modifible maps
pub trait Collection< T  = (),K  =usize>{
	///this should only return null when an error message is about to be printed
	fn get(&mut self,key:impl Keyble<K>) -> Option<&mut T>;
}

#[repr(transparent)]
#[derive(Debug,Clone,PartialEq,Eq)]
pub struct FixedCollection<T  ,const L: usize >(pub [T;L]);
impl<T ,const L: usize > Collection<T,usize> for FixedCollection<T,L>{
	fn get(&mut self, key: impl Keyble<usize>) -> Option<&mut T>  {
		self.0.get_mut(key.get_key())
	}
}

impl<T: Default, const L: usize> Default for FixedCollection<T, L> {
    fn default() -> Self {
        Self(std::array::from_fn(|_| T::default()))
    }
}

#[repr(transparent)]
#[derive(Debug,Clone,PartialEq,Eq)]
pub struct HashCollection<K : Hash+Eq,T>(pub HashMap<K,T>);
impl<T,K : Hash+Eq> Collection<T,K> for HashCollection<K,T>{
	fn get(&mut self, key: impl Keyble<K>) -> Option<&mut T>  {
		self.0.get_mut(&key.get_key())
	}
}

#[test]fn hashes() {
use syn::buffer::Cursor;

	let mut map: HashCollection<&str,Cursor> = HashCollection(HashMap::new());
	map.get("hi");
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
pub type CacheEntry<'a,T = (),E  = syn::Error> = CacheStatus<Pakerat<(Cursor<'a>,T),E>>;

impl<'a, T, E> CacheEntry<'a, T, E>
where
    T: Clone,
    E: Error + Clone,
{	
	///this is used to finalize the result of a search
	///
	///it will automatically move pending results to full errors and panic on an empty cache
    pub fn finalize<F: FnOnce() -> E>(&mut self, err_f: F) -> Pakerat<(Cursor<'a>,T), E> {
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




pub type ArrayCache<'a,const L: usize,T = (),E  = syn::Error> = FixedCollection<CacheEntry<'a,T,E>, L>;

#[test]
fn array_cache() {
	let mut map: ArrayCache<9,i8> = ArrayCache::default();
	assert!(matches!(*map.get(3).unwrap(),CacheStatus::Empty));
}

///a cache that allways returns a value in get
#[repr(transparent)]
#[derive(Clone,PartialEq)]
pub struct HashCache<'a,K : Hash+Eq,T : Clone = (),E : Error + Clone = syn::Error>(pub HashMap<K,CacheEntry<'a,T,E>>);
impl<'a,T : Clone,E:Error + Clone,K : Hash+Eq> Collection<CacheEntry<'a,T,E>,K> for HashCache<'a,K,T,E>{
	#[inline]
	fn get(&mut self, key: impl Keyble<K>) -> Option<&mut CacheEntry<'a,T,E>>  {
		Some(self.0.entry(key.get_key()).or_insert(CacheStatus::Empty))
	}
}

// Implement `Index` for immutable access
impl<'a, K: Hash + Eq, T:Clone,E:Error+ Clone> Index<K> for HashCache<'a,K, T,E> {
    type Output = CacheEntry<'a,T,E>;

    fn index(&self, key: K) -> &Self::Output {
        self.0.get(&key).unwrap_or(&CacheStatus::Empty)
    }
}
impl<K: Hash + Eq, T:Clone,E:Error+ Clone> IndexMut<K> for HashCache<'_, K, T, E> {
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        self.0.entry(key).or_insert(CacheStatus::Empty)
    }
}

impl<K :Hash+Eq, T:Clone,E:Error+ Clone> Default for HashCache<'_,K,T,E>{

fn default() -> Self { HashCache(HashMap::new()) }
}

#[test]
fn hash_cache() {
	let mut map: HashCache<&str,i8> = HashCache::default();
	assert!(matches!(*map.get("hey").unwrap(),CacheStatus::Empty));
}

pub trait CacheSpot<'a, T:Clone=(), E : Error+Clone= syn::Error, K=usize>: Collection<CacheEntry<'a, T, E>, K> {
	fn clear(&mut self);
}

impl<'a, const L: usize, E : Error+Clone,T:Clone> CacheSpot<'a, T, E, usize> for ArrayCache<'a,L,T,E> 
{	
	fn clear(&mut self) {
		for x in self.0.iter_mut() {
			*x = CacheStatus::Empty;
		}
	}
}

impl<'a, K: Hash + Eq, E : Error+Clone,T:Clone> CacheSpot<'a, T, E, K> for HashCache<'a,K,T,E> 
{	
	fn clear(&mut self) {
		self.0 = HashMap::new();
	}
}



pub trait Cache<'a, T : Clone = (), E: Error + Clone = syn::Error, K = usize> {
    /// The type of cache slot stored in the cache
    type Item: CacheSpot<'a, T, E, K>;

    /// Retrieves the cache for the byte anotated by slot
    fn get_slot(&mut self, slot: usize) -> &mut Self::Item;

    ///this function implements caching which will never break any valid peg parser and will never return wrong results.
	///
	///it detects most potential infinite loops by keeping track of all the pending calls. 
	///
	///however it will still reject some grammers.
	///for instance "expr + term => expr" would not work because it causes an infinite left recursive loop. 
	///but "term + expr => expr" will work
    fn parse_cached<P,FE>(&mut self,input:Cursor<'a>, key: impl Keyble<K> + Copy ,parser:&P,recurse_err:FE) -> Pakerat<(Cursor<'a>,T), E>
    where P:Combinator<'a,T, E, K,T,Self> + ?Sized, FE:FnOnce() -> E, Self: Sized
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

impl<'a, T : Clone , E: Error + Clone , K, C > Cache<'a,T,E,K> for HashMap<usize,C> where C : CacheSpot<'a, T, E, K> + Default{
	type Item = C;
	fn get_slot(&mut self, slot: usize) -> &mut C {
		self.entry(slot).or_default()
	}
}

pub type BasicCache<'a,const L: usize,T=(),E=syn::Error>= HashMap<usize, ArrayCache<'a,L, T, E>>;
pub type FlexibleCache<'a,K = usize,T=(),E=syn::Error>= HashMap<usize, HashCache<'a,K, T, E>>;
// pub type StrCache<'a,T=(),E=syn::Error>= HashMap<usize, HashCache<'a,&'a str, T, E>>;

impl<'a, T: Clone, E: Error + Clone, K, C> Cache<'a, T, E, K> for Vec<C>
where
    C: CacheSpot<'a, T, E, K> + Default,
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
/// type MyCachedParser<'a, P> = CachedComb<'a, P, (), usize, usize, &'static str, FlexibleCache<'a, usize, ()>>;
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
/// use pakerat_combinators::cache::{CachedComb, FlexibleCache,UsizeCachedComb};
/// use syn::buffer::{TokenBuffer,Cursor};
///
///
/// let tokens = "cached_var".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
///
/// let my_parser = UsizeCachedComb::new(IdentParser, 0, "Cache miss error");
///
/// let mut cache = FlexibleCache::<usize, _>::default();
/// let (_, parsed_ident) = my_parser.parse(buffer.begin(), &mut cache).unwrap();
///
/// assert_eq!(parsed_ident.to_string(), "cached_var");
///
/// // Parsing again should retrieve from the cache (even if the input is diffrent)
/// let (_, cached_ident) = my_parser.parse(Cursor::empty(), &mut cache).unwrap();
/// assert_eq!(cached_ident.to_string(), "cached_var");
/// ```
///
/// ### Using `FixedCachedComb` with `ArrayCache`
/// ```rust
/// use pakerat_combinators::combinator::Combinator;
/// use pakerat_combinators::basic_parsers::IdentParser;
/// use pakerat_combinators::cache::{CachedComb, BasicCache,FixedCachedComb};
/// use syn::buffer::{TokenBuffer,Cursor};
/// use proc_macro2::Ident;
///
///
/// let tokens = "fixed_cached_var".parse().unwrap();
/// let buffer = TokenBuffer::new2(tokens);
///
/// let my_parser = FixedCachedComb::<8, _,_,_>::new(IdentParser, 0, "Cache miss error");
///
/// let mut cache = BasicCache::<8,Ident>::new();
/// let (_, parsed_ident) = my_parser.parse(buffer.begin(), &mut cache).unwrap();
///
/// assert_eq!(parsed_ident.to_string(), "fixed_cached_var");
///
/// // Parsing again should retrieve from the cache (even if the input is diffrent)
/// let (_, cached_ident) = my_parser.parse(Cursor::empty(), &mut cache).unwrap();
/// assert_eq!(cached_ident.to_string(), "fixed_cached_var");
/// ```
pub struct CachedComb<'a, INNER,T =(), K= usize,MYKEY=K,MESSAGE=&'static str, C = FlexibleCache<'a,K,T>>
where
    INNER: Combinator<'a, T, syn::Error , K, T,C>,
    T: Clone,
    C: Cache<'a, T, syn::Error, K>,
    MYKEY:Keyble<K> + Copy,
    MESSAGE:Display

{   
    pub inner: INNER,
    ///for complex keys (like  c<str>) this should be a &key and then it would clone when needed.
    pub key:MYKEY,
    pub message:MESSAGE,

    ///used so we can have generics
    pub _phantom: PhantomData<(Cursor<'a>, T,K,C)>,
}

pub type UsizeCachedComb<'a, INNER,T =(),MESSAGE=&'static str,C = FlexibleCache<'a,usize,T>> = CachedComb<'a,INNER, T , usize,usize,MESSAGE,C>;
pub type FixedCachedComb<'a,const L: usize, INNER,T =(),MESSAGE=&'static str> = CachedComb<'a,INNER, T , usize,usize,MESSAGE,BasicCache<'a, L,T>>;

impl<'a, INNER,MYKEY,MESSAGE,T, K, C> Combinator<'a, T, syn::Error , K, T,C> for CachedComb <'a,INNER, T , K,MYKEY,MESSAGE,C>
where  
	INNER: Combinator<'a, T, syn::Error , K, T,C>,
    T: Clone,
    C: Cache<'a, T, syn::Error, K>,
    MYKEY:Keyble<K> + Copy,
    MESSAGE:Display
{

    fn parse(&self, input: Cursor<'a>, cache: &mut C) -> Pakerat<(Cursor<'a>, T)> { 
    	cache.parse_cached(input,self.key,&self.inner,|| {syn::Error::new(input.span(),self.message.to_string())})
    }
}

impl<'a,INNER, T , K,MYKEY,MESSAGE,C> CachedComb<'a,INNER, T , K,MYKEY,MESSAGE,C> 

where
    INNER: Combinator<'a, T, syn::Error , K, T,C>,
    T: Clone,
    C: Cache<'a, T, syn::Error, K>,
    MYKEY:Keyble<K> + Copy,
    MESSAGE:Display
{
	pub fn new(inner:INNER,key:MYKEY,message:MESSAGE) -> Self{
		CachedComb{inner,key,message,_phantom:PhantomData}
	}
}