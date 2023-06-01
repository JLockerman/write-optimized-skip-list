use std::{hash::Hash, rc::Rc};

use indexmap::IndexMap;

pub struct IndexMultimap<K, V> {
    map: IndexMap<K, Vec<V>>,
}

#[macro_export]
macro_rules! index_multimap {
    ($($k: expr $(=> [$($value:expr),* $(,)?])?)*) => {
        {
            #[allow(unused_mut)]
            let mut map = IndexMultimap::new();
            $(
                #[allow(dead_code)]
                let mut values = map.ensure_key($k);
                $(
                    *values = vec![$($value),*];
                )?
            )*
            map
        }
    };
}

impl<K, V> IndexMultimap<K, V> {
    pub fn new() -> Self {
        Self {
            map: IndexMap::new(),
        }
    }

    pub fn with_capacity(n: usize) -> Self {
        Self {
            map: IndexMap::with_capacity(n),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn num_keys(&self) -> usize {
        self.map.len()
    }

    pub fn at_index(&self, index: usize) -> (&K, &Vec<V>) {
        self.map.get_index(index).unwrap()
    }

    pub fn ensure_key(&mut self, k: K) -> &mut Vec<V>
    where
        K: Hash + Eq,
    {
        self.map.entry(k).or_insert(vec![])
    }

    pub fn insert(&mut self, k: K, v: V)
    where
        K: Hash + Eq,
    {
        self.map.entry(k).or_insert(vec![]).push(v)
    }

    pub fn last_or(&mut self, k: K) -> &mut Vec<V>
    where
        K: Hash + Eq,
    {
        if self.map.is_empty() {
            return self.map.entry(k).or_insert(vec![]);
        }

        return self.last_mut();
    }

    pub fn last_mut(&mut self) -> &mut Vec<V> {
        let (_, v) = self.map.last_mut().unwrap();
        v
    }

    pub fn into_inner(self) -> IndexMap<K, Vec<V>> {
        self.map
    }

    pub fn last(&self) -> Option<(&K, &Vec<V>)> {
        self.map.last()
    }

    pub fn iter(&self) -> impl Iterator<Item=(&K, &Vec<V>)> {
        self.map.iter()
    }
}

impl<K, V> IntoIterator for IndexMultimap<K, V> {
    type Item = (K, Vec<V>);

    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.map.into_iter())
    }
}

pub struct IntoIter<K, V>(indexmap::map::IntoIter<K, Vec<V>>);

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, Vec<V>);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

#[derive(Copy, Clone)]
pub struct PhysicalIdent<T>(pub T);

trait AsAddr {
    fn as_addr(&self) -> usize;
}

impl<T> AsAddr for Rc<T> {
    fn as_addr(&self) -> usize {
        // Rc::as_ptr(self).addr()
        Rc::as_ptr(self) as usize
    }
}

impl<T> AsAddr for &'_ T
where
    T: AsAddr,
{
    fn as_addr(&self) -> usize {
        T::as_addr(self)
    }
}

impl<T> Hash for PhysicalIdent<T>
where
    T: AsAddr,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.as_addr().hash(state);
    }
}

impl<T> PartialEq for PhysicalIdent<T>
where
    T: AsAddr,
{
    fn eq(&self, other: &Self) -> bool {
        self.0.as_addr() == other.0.as_addr()
    }
}

impl<T> Eq for PhysicalIdent<T> where T: AsAddr {}

impl<T> From<T> for PhysicalIdent<T> {
    fn from(value: T) -> Self {
        PhysicalIdent(value)
    }
}
