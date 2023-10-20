use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
    hash::Hash,
    rc::Rc,
};

#[derive(Debug, Clone)]
pub struct RegionedMap<K, V>
where
    K: PartialEq + Eq + Hash,
    V: Clone,
{
    parent: Option<Rc<RegionedMap<K, V>>>,
    map: HashMap<K, V>,
}

impl<K: PartialEq + Eq + Hash, V: Clone, const N: usize> From<[(K, V); N]> for RegionedMap<K, V> {
    fn from(arr: [(K, V); N]) -> Self {
        let mut map = HashMap::new();
        for (k, v) in arr.into_iter() {
            map.insert(k, v);
        }
        Self { parent: None, map }
    }
}

impl<K: PartialEq + Eq + Hash, V: Clone> Default for RegionedMap<K, V> {
    fn default() -> Self {
        Self {
            parent: None,
            map: HashMap::new(),
        }
    }
}

impl<K: PartialEq + Eq + Hash, V: Clone> RegionedMap<K, V> {
    pub fn new(parent: Option<Rc<RegionedMap<K, V>>>) -> Self {
        Self {
            parent,
            map: HashMap::new(),
        }
    }

    pub fn insert(&mut self, key: K, value: V) {
        self.map.insert(key, value);
    }

    pub fn contains_key_local(&self, key: &K) -> bool {
        self.map.contains_key(key)
    }

    pub fn contains_key(&self, key: &K) -> bool {
        self.map.contains_key(key)
            || match &self.parent {
                Some(parent) => parent.contains_key(key),
                None => false,
            }
    }

    pub fn get_local(&self, key: &K) -> Option<&V> {
        self.map.get(key)
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        self.map.get(key).or_else(|| match &self.parent {
            Some(parent) => parent.get(key),
            None => None,
        })
    }

    pub fn keys(&self) -> Vec<&K> {
        return self.map.keys().collect();
    }

    pub fn values(&self) -> Vec<&V> {
        return self.map.values().collect();
    }

    pub fn remove(&mut self, key: &K) -> Option<V> {
        return self.map.remove(key);
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        return self.map.iter();
    }

    pub fn parent(&self) -> Option<Rc<RegionedMap<K, V>>> {
        self.parent.clone()
    }
}
