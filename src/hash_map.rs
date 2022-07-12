//! A bimap backed by two `HashMap`s.

use crate::{
    mem::{Ref, Wrapper},
    OverwrittenMap,
};
use std::{
    borrow::Borrow,
    collections::{hash_map, HashMap},
    fmt,
    hash::{BuildHasher, Hash},
    iter::{Extend, FromIterator, FusedIterator},
    rc::Rc,
};

/// A bimap backed by two `HashMap`s.
///
/// See the [module-level documentation] for more details and examples.
///
/// [module-level documentation]: crate
pub struct BiHashMap<L, R, T, LS = hash_map::RandomState, RS = hash_map::RandomState> {
    left2right: HashMap<Ref<L>, (Ref<R>, T), LS>,
    right2left: HashMap<Ref<R>, Ref<L>, RS>,
}

impl<L, R, T> BiHashMap<L, R, T, hash_map::RandomState, hash_map::RandomState>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    /// Creates an empty `BiHashMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let bimap = BiHashMap::<char, i32, i8>::new();
    /// ```
    pub fn new() -> Self {
        Self {
            left2right: HashMap::new(),
            right2left: HashMap::new(),
        }
    }

    /// Creates a new empty `BiHashMap` with the given capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let bimap = BiHashMap::<char, i32, i8>::with_capacity(10);
    /// assert!(bimap.capacity() >= 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            left2right: HashMap::with_capacity(capacity),
            right2left: HashMap::with_capacity(capacity),
        }
    }
}

impl<L, R, T, LS, RS> BiHashMap<L, R, T, LS, RS>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    /// Returns the number of left-right pairs in the bimap.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let mut bimap = BiHashMap::new();
    /// bimap.insert('a', 1, 7);
    /// bimap.insert('b', 2, 8);
    /// bimap.insert('c', 3, 9);
    /// assert_eq!(bimap.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.left2right.len()
    }

    /// Returns `true` if the bimap contains no left-right pairs, and `false`
    /// otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let mut bimap = BiHashMap::new();
    /// assert!(bimap.is_empty());
    /// bimap.insert('a', 1, ());
    /// assert!(!bimap.is_empty());
    /// bimap.remove_by_right(&1);
    /// assert!(bimap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.left2right.is_empty()
    }

    /// Returns a lower bound on the number of left-right pairs the `BiHashMap`
    /// can store without reallocating memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let bimap = BiHashMap::<char, i32, i8>::with_capacity(10);
    /// assert!(bimap.capacity() >= 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.left2right.capacity().min(self.right2left.capacity())
    }

    /// Removes all left-right pairs from the bimap.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let mut bimap = BiHashMap::new();
    /// bimap.insert('a', 1, 7);
    /// bimap.insert('b', 2, 8);
    /// bimap.insert('c', 3, 9);
    /// bimap.clear();
    /// assert!(bimap.len() == 0);
    /// ```
    pub fn clear(&mut self) {
        self.left2right.clear();
        self.right2left.clear();
    }

    /// Creates an iterator over the left-right pairs in the bimap in arbitrary
    /// order.
    ///
    /// The iterator element type is `(&L, &R)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let mut bimap = BiHashMap::new();
    /// bimap.insert('a', 1, 7);
    /// bimap.insert('b', 2, 8);
    /// bimap.insert('c', 3, 9);
    ///
    /// for (left, right, value) in bimap.iter() {
    ///     println!("({}, {}, {})", left, right, value);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, L, R, T> {
        Iter {
            inner: self.left2right.iter(),
        }
    }

    /// TODO
    pub fn iter_mut(&mut self) -> IterMut<'_, L, R, T> {
        IterMut {
            inner: self.left2right.iter_mut(),
        }
    }

    /// Creates an iterator over the left values in the bimap in arbitrary
    /// order.
    ///
    /// The iterator element type is `&L`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let mut bimap = BiHashMap::new();
    /// bimap.insert('a', 1, 7);
    /// bimap.insert('b', 2, 8);
    /// bimap.insert('c', 3, 9);
    ///
    /// for char_value in bimap.keys_left() {
    ///     println!("{}", char_value);
    /// }
    /// ```
    pub fn keys_left(&self) -> LeftKeys<'_, L, R, T> {
        LeftKeys {
            inner: self.left2right.iter(),
        }
    }

    /// Creates an iterator over the right values in the bimap in arbitrary
    /// order.
    ///
    /// The iterator element type is `&R`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let mut bimap = BiHashMap::new();
    /// bimap.insert('a', 1, 7);
    /// bimap.insert('b', 2, 8);
    /// bimap.insert('c', 3, 9);
    ///
    /// for int_value in bimap.keys_right() {
    ///     println!("{}", int_value);
    /// }
    /// ```
    pub fn keys_right(&self) -> RightKeys<'_, L, R> {
        RightKeys {
            inner: self.right2left.iter(),
        }
    }
}

impl<L, R, T, LS, RS> BiHashMap<L, R, T, LS, RS>
where
    L: Eq + Hash,
    R: Eq + Hash,
    LS: BuildHasher,
    RS: BuildHasher,
{
    /// Creates a new empty `BiHashMap` using `hash_builder_left` to hash left
    /// values and `hash_builder_right` to hash right values.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::hash_map::RandomState;
    /// use bimap::BiHashMap;
    ///
    /// let s_left = RandomState::new();
    /// let s_right = RandomState::new();
    /// let mut bimap = BiHashMap::<char, i32, i8>::with_hashers(s_left, s_right);
    /// bimap.insert('a', 42, 7);
    /// ```
    pub fn with_hashers(hash_builder_left: LS, hash_builder_right: RS) -> Self {
        Self {
            left2right: HashMap::with_hasher(hash_builder_left),
            right2left: HashMap::with_hasher(hash_builder_right),
        }
    }

    /// Creates a new empty `BiHashMap` with the given capacity, using
    /// `hash_builder_left` to hash left values and `hash_builder_right` to
    /// hash right values.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::hash_map::RandomState;
    /// use bimap::BiHashMap;
    ///
    /// let s_left = RandomState::new();
    /// let s_right = RandomState::new();
    /// let bimap = BiHashMap::<char, i32, i8>::with_capacity_and_hashers(10, s_left, s_right);
    /// assert!(bimap.capacity() >= 10);
    /// ```
    pub fn with_capacity_and_hashers(
        capacity: usize,
        hash_builder_left: LS,
        hash_builder_right: RS,
    ) -> Self {
        Self {
            left2right: HashMap::with_capacity_and_hasher(capacity, hash_builder_left),
            right2left: HashMap::with_capacity_and_hasher(capacity, hash_builder_right),
        }
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `BiHashMap`. The collection may reserve more space to avoid
    /// frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows [`usize`].
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let mut bimap = BiHashMap::<char, i32, i8>::new();
    /// bimap.reserve(10);
    /// assert!(bimap.capacity() >= 10);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.left2right.reserve(additional);
        self.right2left.reserve(additional);
    }

    /// Shrinks the capacity of the bimap as much as possible. It will drop
    /// down as much as possible while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let mut bimap = BiHashMap::<char, i32, i8>::with_capacity(100);
    /// bimap.insert('a', 1, 7);
    /// bimap.insert('b', 2, 8);
    /// assert!(bimap.capacity() >= 100);
    /// bimap.shrink_to_fit();
    /// assert!(bimap.capacity() >= 2);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.left2right.shrink_to_fit();
        self.right2left.shrink_to_fit();
    }

    /// Shrinks the capacity of the bimap with a lower limit. It will drop
    /// down no lower than the supplied limit while maintaining the internal
    /// rules and possibly leaving some space in accordance with the resize
    /// policy.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let mut bimap = BiHashMap::<char, i32, i8>::with_capacity(100);
    /// bimap.insert('a', 1, 7);
    /// bimap.insert('b', 2, 8);
    /// assert!(bimap.capacity() >= 100);
    /// bimap.shrink_to(10);
    /// assert!(bimap.capacity() >= 10);
    /// bimap.shrink_to(0);
    /// assert!(bimap.capacity() >= 2);
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.left2right.shrink_to(min_capacity);
        self.right2left.shrink_to(min_capacity);
    }

    /// Returns a reference to the right value corresponding to the given left
    /// value.
    ///
    /// The input may be any borrowed form of the bimap's left type, but `Eq`
    /// and `Hash` on the borrowed form *must* match those for the left type.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let mut bimap = BiHashMap::new();
    /// bimap.insert('a', 1, 7);
    /// assert_eq!(bimap.get_key_by_left(&'a'), Some(&1));
    /// assert_eq!(bimap.get_key_by_left(&'z'), None);
    /// ```
    pub fn get_key_by_left<Q>(&self, left: &Q) -> Option<&R>
    where
        L: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.left2right.get(Wrapper::wrap(left)).map(|(r, _)| &*r.0)
    }

    /// TODO
    pub fn get_value_by_left<Q>(&self, left: &Q) -> Option<&T>
    where
        L: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.left2right.get(Wrapper::wrap(left)).map(|(_, t)| t)
    }

    /// TODO
    pub fn get_mut_value_by_left<Q>(&mut self, left: &Q) -> Option<&mut T>
    where
        L: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.left2right.get_mut(Wrapper::wrap(left)).map(|(_, t)| t)
    }

    /// TODO
    pub fn get_key_value_by_left<Q>(&self, left: &Q) -> Option<(&R, &T)>
    where
        L: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.left2right
            .get(Wrapper::wrap(left))
            .map(|(r, t)| (&*r.0, t))
    }

    /// Returns a reference to the left value corresponding to the given right
    /// value.
    ///
    /// The input may be any borrowed form of the bimap's right type, but `Eq`
    /// and `Hash` on the borrowed form *must* match those for the right type.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let mut bimap = BiHashMap::new();
    /// bimap.insert('a', 1, 7);
    /// assert_eq!(bimap.get_key_by_right(&1), Some(&'a'));
    /// assert_eq!(bimap.get_key_by_right(&2), None);
    /// ```
    pub fn get_key_by_right<Q>(&self, right: &Q) -> Option<&L>
    where
        R: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.right2left.get(Wrapper::wrap(right)).map(|l| &*l.0)
    }

    /// Returns `true` if the bimap contains the given left value and `false`
    /// otherwise.
    ///
    /// The input may be any borrowed form of the bimap's left type, but `Eq`
    /// and `Hash` on the borrowed form *must* match those for the left type.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let mut bimap = BiHashMap::new();
    /// bimap.insert('a', 1, 7);
    /// assert!(bimap.contains_key_by_left(&'a'));
    /// assert!(!bimap.contains_key_by_left(&'b'));
    /// ```
    pub fn contains_key_by_left<Q>(&self, left: &Q) -> bool
    where
        L: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.left2right.contains_key(Wrapper::wrap(left))
    }

    /// Returns `true` if the map contains the given right value and `false`
    /// otherwise.
    ///
    /// The input may be any borrowed form of the bimap's right type, but `Eq`
    /// and `Hash` on the borrowed form *must* match those for the right type.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let mut bimap = BiHashMap::new();
    /// bimap.insert('a', 1, 7);
    /// assert!(bimap.contains_key_by_right(&1));
    /// assert!(!bimap.contains_key_by_right(&2));
    /// ```
    pub fn contains_key_by_right<Q>(&self, right: &Q) -> bool
    where
        R: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.right2left.contains_key(Wrapper::wrap(right))
    }

    /// Removes the left-right pair corresponding to the given left value.
    ///
    /// Returns the previous left-right pair if the map contained the left value
    /// and `None` otherwise.
    ///
    /// The input may be any borrowed form of the bimap's left type, but `Eq`
    /// and `Hash` on the borrowed form *must* match those for the left type.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let mut bimap = BiHashMap::new();
    /// bimap.insert('a', 1, 7);
    /// bimap.insert('b', 2, 8);
    /// bimap.insert('c', 3, 9);
    ///
    /// assert_eq!(bimap.remove_by_left(&'b'), Some(('b', 2, 8)));
    /// assert_eq!(bimap.remove_by_left(&'b'), None);
    /// ```
    pub fn remove_by_left<Q>(&mut self, left: &Q) -> Option<(L, R, T)>
    where
        L: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.left2right
            .remove(Wrapper::wrap(left))
            .map(|(right_rc, t)| {
                // unwrap is safe because we know right2left contains the key (it's a bimap)
                let left_rc = self.right2left.remove(&right_rc).unwrap();
                // at this point we can safely unwrap because the other pointers are gone
                (
                    Rc::try_unwrap(left_rc.0).ok().unwrap(),
                    Rc::try_unwrap(right_rc.0).ok().unwrap(),
                    t,
                )
            })
    }

    /// Removes the left-right pair corresponding to the given right value.
    ///
    /// Returns the previous left-right pair if the map contained the right
    /// value and `None` otherwise.
    ///
    /// The input may be any borrowed form of the bimap's right type, but `Eq`
    /// and `Hash` on the borrowed form *must* match those for the right type.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let mut bimap = BiHashMap::new();
    /// bimap.insert('a', 1, 7);
    /// bimap.insert('b', 2, 8);
    /// bimap.insert('c', 3, 9);
    ///
    /// assert_eq!(bimap.remove_by_right(&2), Some(('b', 2, 8)));
    /// assert_eq!(bimap.remove_by_right(&2), None);
    /// ```
    pub fn remove_by_right<Q>(&mut self, right: &Q) -> Option<(L, R, T)>
    where
        R: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.right2left.remove(Wrapper::wrap(right)).map(|left_rc| {
            // unwrap is safe because we know left2right contains the key (it's a bimap)
            let (right_rc, t) = self.left2right.remove(&left_rc).unwrap();
            // at this point we can safely unwrap because the other pointers are gone
            (
                Rc::try_unwrap(left_rc.0).ok().unwrap(),
                Rc::try_unwrap(right_rc.0).ok().unwrap(),
                t,
            )
        })
    }

    /// Inserts the given left-right pair into the bimap.
    ///
    /// Returns an enum `OverwrittenMap` representing any left-right pairs that
    /// were overwritten by the call to `insert`. The example below details
    /// all possible enum variants that can be returned.
    ///
    /// # Warnings
    ///
    /// Somewhat paradoxically, calling `insert()` can actually reduce the size
    /// of the bimap! This is because of the invariant that each left value
    /// maps to exactly one right value and vice versa.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::{BiHashMap, OverwrittenMap};
    ///
    /// let mut bimap = BiHashMap::new();
    /// assert_eq!(bimap.len(), 0); // {}
    ///
    /// // no values are overwritten.
    /// assert_eq!(bimap.insert('a', 1, 7), OverwrittenMap::Neither);
    /// assert_eq!(bimap.len(), 1); // {'a' <> 1}
    ///
    /// // no values are overwritten.
    /// assert_eq!(bimap.insert('b', 2, 8), OverwrittenMap::Neither);
    /// assert_eq!(bimap.len(), 2); // {'a' <> 1, 'b' <> 2}
    ///
    /// // ('a', 1) already exists, so inserting ('a', 4) overwrites 'a', the left value.
    /// // the previous left-right pair ('a', 1) is returned.
    /// assert_eq!(bimap.insert('a', 4, 9), OverwrittenMap::Left('a', 1, 7));
    /// assert_eq!(bimap.len(), 2); // {'a' <> 4, 'b' <> 2}
    ///
    /// // ('b', 2) already exists, so inserting ('c', 2) overwrites 2, the right value.
    /// // the previous left-right pair ('b', 2) is returned.
    /// assert_eq!(bimap.insert('c', 2, 10), OverwrittenMap::Right('b', 2, 8));
    /// assert_eq!(bimap.len(), 2); // {'a' <> 1, 'c' <> 2}
    ///
    /// // both ('a', 4) and ('c', 2) already exist, so inserting ('a', 2) overwrites both.
    /// // ('a', 4) has the overwritten left value ('a'), so it's the first tuple returned.
    /// // ('c', 2) has the overwritten right value (2), so it's the second tuple returned.
    /// assert_eq!(bimap.insert('a', 2, 11), OverwrittenMap::Both(('a', 4, 9), ('c', 2, 10)));
    /// assert_eq!(bimap.len(), 1); // {'a' <> 2} // bimap is smaller than before!
    ///
    /// // ('a', 2) already exists, so inserting ('a', 2) overwrites the pair.
    /// // the previous left-right pair ('a', 2) is returned.
    /// assert_eq!(bimap.insert('a', 2, 12), OverwrittenMap::Pair('a', 2, 11));
    /// assert_eq!(bimap.len(), 1); // {'a' <> 2}
    /// ```
    pub fn insert(&mut self, left: L, right: R, value: T) -> OverwrittenMap<L, R, T> {
        let retval = match (self.remove_by_left(&left), self.remove_by_right(&right)) {
            (None, None) => OverwrittenMap::Neither,
            (None, Some(r_pair)) => OverwrittenMap::Right(r_pair.0, r_pair.1, r_pair.2),
            (Some(l_pair), None) => {
                // since remove_by_left() was called first, it's possible the right value was
                // removed if a duplicate pair is being inserted
                if l_pair.1 == right {
                    OverwrittenMap::Pair(l_pair.0, l_pair.1, l_pair.2)
                } else {
                    OverwrittenMap::Left(l_pair.0, l_pair.1, l_pair.2)
                }
            }
            (Some(l_pair), Some(r_pair)) => OverwrittenMap::Both(l_pair, r_pair),
        };
        self.insert_unchecked(left, right, value);
        retval
    }

    /// Inserts the given left-right pair into the bimap without overwriting any
    /// existing values.
    ///
    /// Returns `Ok(())` if the pair was successfully inserted into the bimap.
    /// If either value exists in the map, `Err((left, right)` is returned
    /// with the attempted left-right pair and the map is unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let mut bimap = BiHashMap::new();
    /// assert_eq!(bimap.insert_no_overwrite('a', 1, 6), Ok(()));
    /// assert_eq!(bimap.insert_no_overwrite('b', 2, 7), Ok(()));
    /// assert_eq!(bimap.insert_no_overwrite('a', 3, 8), Err(('a', 3, 8)));
    /// assert_eq!(bimap.insert_no_overwrite('c', 2, 9), Err(('c', 2, 9)));
    /// ```
    pub fn insert_no_overwrite(&mut self, left: L, right: R, value: T) -> Result<(), (L, R, T)> {
        if self.contains_key_by_left(&left) || self.contains_key_by_right(&right) {
            Err((left, right, value))
        } else {
            self.insert_unchecked(left, right, value);
            Ok(())
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all left-right pairs `(l, r)` such that `f(&l,
    /// &r)` returns `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiHashMap;
    ///
    /// let mut bimap = BiHashMap::new();
    /// bimap.insert('a', 1, 7);
    /// bimap.insert('b', 2, 8);
    /// bimap.insert('c', 3, 9);
    /// bimap.retain(|&l, &r, &v| r >= 2);
    /// assert_eq!(bimap.len(), 2);
    /// assert_eq!(bimap.get_key_by_left(&'b'), Some(&2));
    /// assert_eq!(bimap.get_key_by_left(&'c'), Some(&3));
    /// assert_eq!(bimap.get_key_by_left(&'a'), None);
    /// ```
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&L, &R, &T) -> bool,
    {
        let mut f = f;
        let right2left = &mut self.right2left;
        self.left2right.retain(|l, (r, t)| {
            let to_retain = f(&l.0, &r.0, t);
            if !to_retain {
                right2left.remove(r);
            }
            to_retain
        });
    }

    /// Inserts the given left-right pair into the bimap without checking if the
    /// pair already exists.
    fn insert_unchecked(&mut self, left: L, right: R, value: T) {
        let left = Ref(Rc::new(left));
        let right = Ref(Rc::new(right));
        self.left2right.insert(left.clone(), (right.clone(), value));
        self.right2left.insert(right, left);
    }
}

impl<L, R, T, LS, RS> Clone for BiHashMap<L, R, T, LS, RS>
where
    L: Clone + Eq + Hash,
    R: Clone + Eq + Hash,
    T: Clone,
    LS: BuildHasher + Clone,
    RS: BuildHasher + Clone,
{
    fn clone(&self) -> BiHashMap<L, R, T, LS, RS> {
        let mut new_bimap = BiHashMap::with_capacity_and_hashers(
            self.capacity(),
            self.left2right.hasher().clone(),
            self.right2left.hasher().clone(),
        );
        for (l, r, t) in self.iter() {
            new_bimap.insert(l.clone(), r.clone(), t.clone());
        }
        new_bimap
    }
}

impl<L, R, T, LS, RS> fmt::Debug for BiHashMap<L, R, T, LS, RS>
where
    L: fmt::Debug,
    R: fmt::Debug,
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        struct EntryDebugger<'a, L, R, T> {
            left: &'a L,
            right: &'a R,
            value: &'a T,
        }
        impl<'a, L, R, T> fmt::Debug for EntryDebugger<'a, L, R, T>
        where
            L: fmt::Debug,
            R: fmt::Debug,
            T: fmt::Debug,
        {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                self.left.fmt(f)?;
                write!(f, " <> ")?;
                self.right.fmt(f)?;
                write!(f, " = ")?;
                self.value.fmt(f)
            }
        }
        f.debug_set()
            .entries(
                self.left2right
                    .iter()
                    .map(|(left, (right, value))| EntryDebugger { left, right, value }),
            )
            .finish()
    }
}

impl<L, R, T, LS, RS> Default for BiHashMap<L, R, T, LS, RS>
where
    L: Eq + Hash,
    R: Eq + Hash,
    LS: BuildHasher + Default,
    RS: BuildHasher + Default,
{
    fn default() -> BiHashMap<L, R, T, LS, RS> {
        BiHashMap {
            left2right: HashMap::default(),
            right2left: HashMap::default(),
        }
    }
}

impl<L, R, T, LS, RS> Eq for BiHashMap<L, R, T, LS, RS>
where
    L: Eq + Hash,
    R: Eq + Hash,
    T: Eq,
    LS: BuildHasher,
    RS: BuildHasher,
{
}

impl<L, R, T, LS, RS> FromIterator<(L, R, T)> for BiHashMap<L, R, T, LS, RS>
where
    L: Eq + Hash,
    R: Eq + Hash,
    LS: BuildHasher + Default,
    RS: BuildHasher + Default,
{
    fn from_iter<I>(iter: I) -> BiHashMap<L, R, T, LS, RS>
    where
        I: IntoIterator<Item = (L, R, T)>,
    {
        let iter = iter.into_iter();
        let mut bimap = match iter.size_hint() {
            (lower, None) => {
                BiHashMap::with_capacity_and_hashers(lower, LS::default(), RS::default())
            }
            (_, Some(upper)) => {
                BiHashMap::with_capacity_and_hashers(upper, LS::default(), RS::default())
            }
        };
        for (left, right, value) in iter {
            bimap.insert(left, right, value);
        }
        bimap
    }
}

impl<'a, L, R, T, LS, RS> IntoIterator for &'a BiHashMap<L, R, T, LS, RS>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    type Item = (&'a L, &'a R, &'a T);
    type IntoIter = Iter<'a, L, R, T>;

    fn into_iter(self) -> Iter<'a, L, R, T> {
        self.iter()
    }
}

impl<L, R, T, LS, RS> IntoIterator for BiHashMap<L, R, T, LS, RS>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    type Item = (L, R, T);
    type IntoIter = IntoIter<L, R, T>;

    fn into_iter(self) -> IntoIter<L, R, T> {
        IntoIter {
            inner: self.left2right.into_iter(),
        }
    }
}

impl<L, R, T, LS, RS> Extend<(L, R, T)> for BiHashMap<L, R, T, LS, RS>
where
    L: Eq + Hash,
    R: Eq + Hash,
    LS: BuildHasher,
    RS: BuildHasher,
{
    fn extend<I: IntoIterator<Item = (L, R, T)>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |(l, r, t)| {
            self.insert(l, r, t);
        });
    }
}

impl<L, R, T, LS, RS> PartialEq for BiHashMap<L, R, T, LS, RS>
where
    L: Eq + Hash,
    R: Eq + Hash,
    T: Eq,
    LS: BuildHasher,
    RS: BuildHasher,
{
    fn eq(&self, other: &Self) -> bool {
        self.left2right == other.left2right
    }
}

/// An owning iterator over the left-right pairs in a `BiHashMap`.
pub struct IntoIter<L, R, T> {
    inner: hash_map::IntoIter<Ref<L>, (Ref<R>, T)>,
}

impl<L, R, T> ExactSizeIterator for IntoIter<L, R, T> {}

impl<L, R, T> FusedIterator for IntoIter<L, R, T> {}

impl<L, R, T> Iterator for IntoIter<L, R, T> {
    type Item = (L, R, T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(l, (r, t))| {
            (
                Rc::try_unwrap(l.0).ok().unwrap(),
                Rc::try_unwrap(r.0).ok().unwrap(),
                t,
            )
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// An iterator over the left-right pairs in a `BiHashMap`.
///
/// This struct is created by the [`iter`] method of `BiHashMap`.
///
/// [`iter`]: BiHashMap::iter
pub struct Iter<'a, L, R, T> {
    inner: hash_map::Iter<'a, Ref<L>, (Ref<R>, T)>,
}

impl<'a, L, R, T> ExactSizeIterator for Iter<'a, L, R, T> {}

impl<'a, L, R, T> FusedIterator for Iter<'a, L, R, T> {}

impl<'a, L, R, T> Iterator for Iter<'a, L, R, T> {
    type Item = (&'a L, &'a R, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(l, (r, t))| (&*l.0, &*r.0, t))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// TODO
pub struct IterMut<'a, L, R, T> {
    inner: hash_map::IterMut<'a, Ref<L>, (Ref<R>, T)>,
}

impl<'a, L, R, T> ExactSizeIterator for IterMut<'a, L, R, T> {}

impl<'a, L, R, T> FusedIterator for IterMut<'a, L, R, T> {}

impl<'a, L, R, T> Iterator for IterMut<'a, L, R, T> {
    type Item = (&'a L, &'a R, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(l, (r, t))| (&*l.0, &*r.0, t))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// An iterator over the left values in a `BiHashMap`.
///
/// This struct is created by the [`left_values`] method of `BiHashMap`.
///
/// [`left_values`]: BiHashMap::left_values
pub struct LeftKeys<'a, L, R, T> {
    inner: hash_map::Iter<'a, Ref<L>, (Ref<R>, T)>,
}

impl<'a, L, R, T> ExactSizeIterator for LeftKeys<'a, L, R, T> {}

impl<'a, L, R, T> FusedIterator for LeftKeys<'a, L, R, T> {}

impl<'a, L, R, T> Iterator for LeftKeys<'a, L, R, T> {
    type Item = &'a L;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(l, _)| &*l.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// An iterator over the right values in a `BiHashMap`.
///
/// This struct is created by the [`right_values`] method of `BiHashMap`.
///
/// [`right_values`]: BiHashMap::right_values
pub struct RightKeys<'a, L, R> {
    inner: hash_map::Iter<'a, Ref<R>, Ref<L>>,
}

impl<'a, L, R> ExactSizeIterator for RightKeys<'a, L, R> {}

impl<'a, L, R> FusedIterator for RightKeys<'a, L, R> {}

impl<'a, L, R> Iterator for RightKeys<'a, L, R> {
    type Item = &'a R;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(r, _)| &*r.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

// safe because internal Rcs are not exposed by the api and the reference counts
// only change in methods with &mut self
unsafe impl<L, R, T, LS, RS> Send for BiHashMap<L, R, T, LS, RS>
where
    L: Send,
    R: Send,
    T: Send,
    LS: Send,
    RS: Send,
{
}
unsafe impl<L, R, T, LS, RS> Sync for BiHashMap<L, R, T, LS, RS>
where
    L: Sync,
    R: Sync,
    T: Sync,
    LS: Sync,
    RS: Sync,
{
}
