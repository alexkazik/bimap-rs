use alloc::collections::{btree_map, BTreeMap};
use core::borrow::Borrow;
use core::iter::FusedIterator;
use core::ops::RangeBounds;

use crate::traits::*;
use crate::util::{Ref, Wrapper};

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct InnerMap<K, V> {
    map: BTreeMap<Ref<K>, Ref<V>>,
}

impl<K, V> InnerMap<K, V> {
    pub(crate) fn range<T: ?Sized, A>(&self, range: A) -> Range<'_, K, V>
    where
        K: Ord + Borrow<T>,
        T: Ord,
        A: RangeBounds<T>,
    {
        let start = Wrapper::wrap_bound(range.start_bound());
        let end = Wrapper::wrap_bound(range.end_bound());
        Range {
            inner: self.map.range::<Wrapper<_>, _>((start, end)),
        }
    }
}

impl<K, V> Core for InnerMap<K, V>
where
    K: Ord,
{
    type Key = K;
    type Value = V;
}

impl<K, V> New for InnerMap<K, V>
where
    K: Ord,
{
    fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }
}

impl<K, V> Length for InnerMap<K, V>
where
    K: Ord,
{
    fn len(&self) -> usize {
        self.map.len()
    }

    fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

impl<K, V> Insert for InnerMap<K, V>
where
    K: Ord,
{
    fn insert(&mut self, (key, value): (Ref<K>, Ref<V>)) {
        self.map.insert(key, value);
    }
}

impl<K, V, Q: ?Sized> Contains<Q> for InnerMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: Ord,
{
    fn contains(&self, k: &Q) -> bool {
        self.map.contains_key(Wrapper::wrap(k))
    }
}

impl<K, V, Q: ?Sized> Get<Q> for InnerMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: Ord,
{
    fn get(&self, k: &Q) -> Option<&Ref<V>> {
        self.map.get(Wrapper::wrap(k))
    }
}

impl<K, V, Q: ?Sized> Remove<Q> for InnerMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: Ord,
{
    fn remove(&mut self, k: &Q) -> Option<(Ref<K>, Ref<V>)> {
        self.map.remove_entry(Wrapper::wrap(k))
    }
}

impl<K, V> MapIterator for InnerMap<K, V>
where
    K: Ord,
{
    type MapIter<'a, K_: 'a, V_: 'a> = Iter<'a, K_, V_>;
    type MapIntoIter<K_, V_> = IntoIter<K_, V_>;

    fn map_iter(&self) -> Self::MapIter<'_, K, V> {
        Iter {
            inner: self.map.iter(),
        }
    }

    fn map_into_iter(self) -> Self::MapIntoIter<K, V> {
        IntoIter {
            inner: self.map.into_iter(),
        }
    }
}

#[derive(Debug)]
pub struct IntoIter<K, V> {
    inner: btree_map::IntoIter<Ref<K>, Ref<V>>,
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (Ref<K>, Ref<V>);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {}

impl<K, V> FusedIterator for IntoIter<K, V> {}

#[derive(Debug)]
pub struct Iter<'a, K, V> {
    inner: btree_map::Iter<'a, Ref<K>, Ref<V>>,
}

impl<'a, K, V> Clone for Iter<'a, K, V> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a Ref<K>, &'a Ref<V>);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {}

impl<'a, K, V> FusedIterator for Iter<'a, K, V> {}

#[derive(Debug)]
pub struct Range<'a, K, V> {
    inner: btree_map::Range<'a, Ref<K>, Ref<V>>,
}

impl<'a, K, V> Clone for Range<'a, K, V> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K, V> Iterator for Range<'a, K, V> {
    type Item = (&'a Ref<K>, &'a Ref<V>);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for Range<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<'a, K, V> ExactSizeIterator for Range<'a, K, V> {}

impl<'a, K, V> FusedIterator for Range<'a, K, V> {}