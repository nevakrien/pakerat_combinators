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


pub type ArrayCache<'a,const L: usize,T = (),E  = syn::Error> = FixedCollection<CacheEntry<'a,T,E>, L>;

#[test]
fn array_cache() {
	let mut map: ArrayCache<9,i8> = ArrayCache::default();
	assert!(matches!(*map.get(3).unwrap(),CacheStatus::Empty));
}

///a cache that allways returns a value in get
#[repr(transparent)]
#[derive(Clone,PartialEq)]
pub struct HashCache<'a,K : Hash+Eq,T = (),E : Error = syn::Error>(pub HashMap<K,CacheEntry<'a,T,E>>);
impl<'a,T,E:Error,K : Hash+Eq> Collection<CacheEntry<'a,T,E>,K> for HashCache<'a,K,T,E>{
	#[inline]
	fn get(&mut self, key: impl Keyble<K>) -> Option<&mut CacheEntry<'a,T,E>>  {
		Some(self.0.entry(key.get_key()).or_insert(CacheStatus::Empty))
	}
}

// Implement `Index` for immutable access
impl<'a, K: Hash + Eq, T,E:Error> Index<K> for HashCache<'a,K, T,E> {
    type Output = CacheEntry<'a,T,E>;

    fn index(&self, key: K) -> &Self::Output {
        self.0.get(&key).unwrap_or(&CacheStatus::Empty)
    }
}
impl<K: Hash + Eq, T,E:Error> IndexMut<K> for HashCache<'_, K, T, E> {
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        self.0.entry(key).or_insert(CacheStatus::Empty)
    }
}

impl<K :Hash+Eq, T, E : Error> Default for HashCache<'_,K,T,E>{

fn default() -> Self { HashCache(HashMap::new()) }
}

#[test]
fn hash_cache() {
	let mut map: HashCache<&str,i8> = HashCache::default();
	assert!(matches!(*map.get("hey").unwrap(),CacheStatus::Empty));
}

pub trait Cache<'a, T=(), E : Error= syn::Error, K=usize>: Collection<CacheEntry<'a, T, E>, K> {
	fn clear(&mut self);
}

impl<'a, const L: usize, E : Error,T> Cache<'a, T, E, usize> for ArrayCache<'a,L,T,E> 
{	
	fn clear(&mut self) {
		for x in self.0.iter_mut() {
			*x = CacheStatus::Empty;
		}
	}
}

impl<'a, K: Hash + Eq, E : Error,T> Cache<'a, T, E, K> for HashCache<'a,K,T,E> 
{	
	fn clear(&mut self) {
		self.0 = HashMap::new();
	}
}


/// Helper Trait for Cache
pub trait CacheExt<'a, T :Clone, E:Clone + Error, K>: Cache<'a, T, E, K> + Sized{
    #[inline(always)]
    fn get_existing(&mut self, key: impl Keyble<K>) -> &mut CacheEntry<'a, T, E>{
    	self.get(key).unwrap()
    }

    fn parse_cached<P,FE>(&mut self,input:Cursor<'a>, key: impl Keyble<K> + Copy ,parser:&P,recurse_err:FE) -> Pakerat<(Cursor<'a>,T), E>
    where P:Combinator<T, E, K> + ?Sized, FE:FnOnce() -> E
    {	
    	let spot = self.get_existing(key);
    	match spot{
    		CacheStatus::Full(res) => res.clone(),
    		CacheStatus::Empty => {
    			*spot = CacheStatus::Pending;
    			let ans = parser.parse(input,self);

    			//need to get spot again since parse may of changed it
    			let spot = self.get_existing(key);
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

    #[inline]
    fn try_get(&mut self, key: impl Keyble<K>,spot:Cursor) -> syn::Result<&mut CacheEntry<'a, T, E>> {
        self.get(key)
            .ok_or_else(|| syn::Error::new(spot.span(), "Key missing"))
    }
}

impl<'a, T, E, K, C> CacheExt<'a, T, E, K> for C
where
    T: Clone,
    E: Clone + Error,
    C: Cache<'a, T, E, K>, // Ensures it only applies to valid `Cache` types
{}

#[test]
fn cache_refs() {
	#[allow(dead_code)]
	fn check_bounds<'a, P,FE>(cache: &mut ArrayCache<'a,9>,input:Cursor<'a>, key: &usize,parser:&P,recurse_err:FE) -> Pakerat<(Cursor<'a>,())>
	where P:Combinator<()>, FE:FnOnce() -> syn::Error{
		CacheExt::parse_cached(cache,input,key,parser,recurse_err)
	}

	#[allow(dead_code)]
	fn check_bounds_hash<'a, P,FE>(cache: &mut HashCache<'a,&'a str>,input:Cursor<'a>, key: &'a str,parser:&P,recurse_err:FE) -> Pakerat<(Cursor<'a>,())>
	where P: Combinator<(),syn::Error,&'a str>, FE:FnOnce() -> syn::Error{
		CacheExt::parse_cached(cache,input,key,parser,recurse_err)
	}
}


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