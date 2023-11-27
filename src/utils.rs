use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
    fmt::{Display, Formatter},
    hash::Hash,
    rc::Rc,
};

#[derive(Debug, Clone)]
pub struct RegionedMap<K, V>
where
    K: PartialEq + Eq + Hash,
    V: Clone,
{
    maps: Vec<HashMap<K, V>>,
}

impl<K, V> Default for RegionedMap<K, V>
where
    K: PartialEq + Eq + Hash,
    V: Clone,
{
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Display for RegionedMap<String, String> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (key, value) in self.maps.last().unwrap().iter() {
            writeln!(f, "{}: {}", key, value)?;
        }
        Ok(())
    }
}

impl<K: PartialEq + Eq + Hash, V: Clone> RegionedMap<K, V> {
    pub fn new() -> Self {
        Self {
            maps: vec![HashMap::new()],
        }
    }

    pub fn push(&mut self) {
        self.maps.push(HashMap::new());
    }

    pub fn pop(&mut self) -> Option<HashMap<K, V>> {
        self.maps.pop()
    }

    pub fn insert(&mut self, key: K, value: V) {
        self.maps.last_mut().unwrap().insert(key, value);
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        for map in self.maps.iter().rev() {
            if let Some(value) = map.get(key) {
                return Some(value);
            }
        }
        None
    }

    pub fn contains_key(&self, key: &K) -> bool {
        for map in self.maps.iter().rev() {
            if map.contains_key(key) {
                return true;
            }
        }
        false
    }

    pub fn contains_key_local(&self, key: &K) -> bool {
        self.maps.last().unwrap().contains_key(key)
    }

    pub fn get_local(&self, key: &K) -> Option<&V> {
        self.maps.last().unwrap().get(key)
    }

    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.maps.last().unwrap().keys()
    }

    pub fn remove(&mut self, key: &K) -> Option<V> {
        for map in self.maps.iter_mut().rev() {
            if let Some(value) = map.remove(key) {
                return Some(value);
            }
        }
        None
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.maps.last().unwrap().iter()
    }
}

pub mod testing {
    use std::{path::Path, time::Duration};

    pub fn run_n_times(n: usize, f: impl Fn() -> Duration, report: &str) -> Duration {
        let mut total = Duration::new(0, 0);
        let mut each = vec![];
        for _ in 0..n {
            let time = f();
            total += time;
            each.push(time);
        }
        let avg_time = total / n as u32;
        let std_dev = {
            let mut sum = 0.0;
            for time in each.into_iter() {
                sum += ((time.as_secs_f64() - avg_time.as_secs_f64()) * 1000.0).powf(2.0);
            }
            (sum as f64 / n as f64).sqrt()
        };
        std::fs::write(
            report,
            format!(
                "{{\"avg_time\": {}, \"std\": {}}}",
                avg_time.as_secs_f64() * 1000.0,
                std_dev
            ),
        )
        .unwrap();
        avg_time
    }
}
