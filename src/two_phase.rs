#[cfg_attr(nightly, feature(is_sorted))]
use std::{
    cell::RefCell,
    cmp,
    collections::VecDeque,
    hash::{Hash, Hasher},
    iter::zip,
    rc::Rc,
};

use twox_hash::XxHash64;

use crate::index_multimap::{IndexMultimap, PhysicalIdent};

#[derive(Debug)]
pub struct List<K, V> {
    root: Option<Rc<Node<K, V>>>,
    token: MutabilityToken,
    b: u32,
}

#[derive(Debug)]
struct MutabilityToken;

#[derive(Debug)]
struct Node<K, V> {
    height: Height,
    pivots: Vec<K>,
    values: Values<K, V>,
}

#[derive(Debug)]
enum Values<K, V> {
    Leaf(Vec<V>),
    Internal {
        children: Vec<Rc<Node<K, V>>>,
        buffer: RefCell<Vec<Op<K, V>>>,
    },
    First {
        children: Vec<Rc<Node<K, V>>>,
        buffer: RefCell<Vec<Op<K, V>>>,
    },
}

// enum NodeValues<K, V> {
//     Upper(Height, Vec<Rc<Node<K, V>>>),
//     Lower(Vec<Rc<Leaf<K, V>>>),
// }

type Height = u8;

#[derive(Debug, Clone)]
enum Op<K, V> {
    Insert(K, V, Height),
    Delete(K, Height),
}

#[must_use]
enum BinarySearchResult {
    Found(usize),
    NotFound(usize),
}

#[must_use]
enum NodeValue<'a, K, V> {
    Val(&'a V),
    Ptr(&'a Node<K, V>),
}

impl<K, V> List<K, V> {
    pub fn new(b: u32) -> Self {
        Self {
            root: None,
            token: MutabilityToken,
            b,
        }
    }

    pub fn get<'s>(&'s self, k: &K) -> Option<&'s V>
    where
        K: Ord,
    {
        let Some(root) = &self.root else {
            return None
        };

        root.get(k, &self.token)
    }

    pub fn insert(&mut self, k: K, v: V)
    where
        K: Hash + Ord + Clone,
        V: Clone, // TODO required by immutability of leaves, can/should remove?
    {
        let mut hasher = XxHash64::default();
        k.hash(&mut hasher);
        let hash = hasher.finish();
        let height = hash.leading_ones() as u8; // TODO
        match &mut self.root {
            root @ None if height == 0 => {
                let new_root = Node::new_root_leaf(k, v);
                *root = Some(new_root)
            }
            root @ None => {
                let new_root = Node::empty_first(height, self.b);
                let insert = Op::Insert(k, v, height);
                let mut replacements = VecDeque::new();
                // TODO this is dumb
                new_root.add_ops([insert].into(), &mut replacements, self.b, &mut self.token);
                debug_assert!(replacements.is_empty());
                *root = Some(new_root)
            }
            Some(root) if root.height < height => {
                let new_root = Node::empty_first(height, self.b);
                let insert = Op::Insert(k, v, height);
                let mut replacements = VecDeque::new();
                // TODO this is dumb
                new_root.add_ops([insert].into(), &mut replacements, self.b, &mut self.token);
                debug_assert!(replacements.is_empty());
                *root = new_root
            }
            Some(root) if height == 0 => {
                let root = Rc::get_mut(root).unwrap();
                root.add_to_root_leaf(k, v);
            }
            Some(root) => {
                let insert = Op::Insert(k, v, height);
                let mut replacements = VecDeque::new();
                // TODO this is dumb
                root.add_ops([insert].into(), &mut replacements, self.b, &mut self.token);
                let Some(new_root) = replacements.pop_front() else {
                    return
                };
                debug_assert!(replacements.is_empty());
                *root = new_root
            }
        }
    }
}

impl<K, V> Node<K, V> {
    fn empty_first(height: u8, b: u32) -> Rc<Self> {
        Rc::new(Self {
            height,
            pivots: vec![],
            values: Values::First {
                children: vec![],
                buffer: RefCell::new(Vec::with_capacity(b as usize)),
            },
        })
    }

    fn new_root_leaf(k: K, v: V) -> Rc<Self> {
        Rc::new(Self {
            height: 0,
            pivots: vec![k],
            values: Values::Leaf(vec![v]),
        })
    }

    pub fn get<'s>(&'s self, k: &K, token: &MutabilityToken) -> Option<&'s V>
    where
        K: Ord,
    {
        use NodeValue::*;

        if let Some(result) = self.values.get_from_buffer(k, token) {
            return result;
        }

        let location = self.pivots.binary_search(k).into();
        let Some(next) = self.values.get_value(location) else {
            return None
        };
        match next {
            Val(value) => Some(value),
            Ptr(child) => child.get(k, token),
        }
    }

    pub fn contains_key<'s>(&'s self, k: &K, token: &MutabilityToken) -> bool
    where
        K: Ord,
    {
        self.pivots.get(0) == Some(k) || self.values.buffer_contains_key(k, token)
    }

    fn add_to_root_leaf(&mut self, k: K, v: V)
    where
        K: Ord,
    {
        use BinarySearchResult::*;

        let location = self.pivots.binary_search(&k).into();
        if let &NotFound(i) = &location {
            self.pivots.insert(i, k)
        }
        self.values.add_to_root_values(location, v);
    }

    fn add_ops(
        &self,
        mut ops: VecDeque<Op<K, V>>,
        replacement_nodes: &mut VecDeque<Rc<Self>>,
        b: u32,
        token: &mut MutabilityToken,
    ) where
        K: Ord + Clone,
        V: Clone,
    {
        assert!(self.height >= 1);
        assert!(ops.len() <= b as usize);
        #[cfg(nightly)]
        {
            assert!(ops.as_slices().0.is_sorted());
            assert!(ops.as_slices().1.is_sorted());
        }

        let remaining_buffer_space = (b as usize).saturating_sub(self.values.slots_used());

        if remaining_buffer_space >= ops.len() {
            self.values.extend_buffer_with_ops(ops.into_iter());
            return;
        }

        // TODO think long and hard about what this means for durability
        self.values
            .extend_buffer_with_ops(ops.drain(..remaining_buffer_space));

        let new_nodes = self.flush(b, token);

        for node in new_nodes.iter().rev() {
            let ops_for_child = if node.values.is_first() {
                ops.drain(..)
            } else {
                let first_key = node.pivots.first().unwrap();
                let ops_before_child = ops
                    .iter()
                    .enumerate()
                    .rev()
                    .find(|(_, op)| op.key() < first_key)
                    .map(|(i, _)| i);
                match ops_before_child {
                    None => ops.drain(..),
                    Some(i) if i + 1 < ops.len() => ops.drain((i + 1)..),
                    Some(_) => continue,
                }
            };

            node.values.extend_buffer_with_ops(ops_for_child)
        }

        replacement_nodes.extend(new_nodes);
    }

    pub fn flush(&self, b: u32, token: &mut MutabilityToken) -> Vec<Rc<Self>>
    where
        K: Ord + Clone,
        V: Clone,
    {
        debug_assert!(self.height > 0);

        let buffer = self.values.take_buffer();
        let new_nodes = self
            .values
            .apply_ops(self.height, &self.pivots, buffer, b, token);

        new_nodes
    }
}

impl<K, V> Values<K, V> {
    fn is_first(&self) -> bool {
        matches!(self, Values::First { .. })
    }

    fn get_from_buffer(&self, k: &K, _token: &MutabilityToken) -> Option<Option<&V>>
    where
        K: Ord,
    {
        use Values::*;
        let (First { buffer, .. } | Internal { buffer, .. }) = self else {
            return None
        };
        // SAFETY The MutabilityToken serves as a witness to the immutability of
        //        the list.
        let buffer = unsafe { buffer.try_borrow_unguarded() };
        buffer
            .unwrap()
            .iter()
            .rfind(|b| b.key() == k)
            .map(Op::value)
    }

    fn buffer_contains_key(&self, k: &K, _token: &MutabilityToken) -> bool
    where
        K: Ord,
    {
        use Values::*;
        let (First { buffer, .. } | Internal { buffer, .. }) = self else {
            return false
        };
        // SAFETY The MutabilityToken serves as a witness to the immutability of
        //        the list.
        let buffer = unsafe { buffer.try_borrow_unguarded() };
        buffer.unwrap().iter().rfind(|b| b.key() == k).is_some()
    }

    fn get_value(&self, location: BinarySearchResult) -> Option<NodeValue<'_, K, V>> {
        use BinarySearchResult::*;
        use NodeValue::*;
        use Values::*;
        match (self, location) {
            (Leaf(values), Found(idx)) => Some(Val(&values[idx])),
            (Leaf(_), NotFound(_)) => None,
            (Internal { children, .. } | First { children, .. }, location) => {
                let idx = self.location_to_index(location);
                Some(Ptr(&children[idx]))
            }
        }
    }

    fn slots_used(&self) -> usize {
        use Values::*;
        match self {
            Leaf(values) => values.len(),
            Internal {
                children, buffer, ..
            }
            | First {
                children, buffer, ..
            } => children.len() + buffer.borrow().len(),
        }
    }

    fn add_to_root_values(&mut self, location: BinarySearchResult, v: V)
    where
        K: Ord,
    {
        use BinarySearchResult::*;
        use Values::*;

        let Leaf(values) = self else {
            unreachable!()
        };
        match location {
            Found(i) => values[i] = v,
            NotFound(i) => values.insert(i, v),
        }
    }

    fn extend_buffer_with_ops(&self, ops: impl Iterator<Item = Op<K, V>>)
    where
        K: Ord,
    {
        use Values::*;
        let (Internal { buffer, .. } | First { buffer, .. }) = self else {
            unreachable!()
        };

        let mut buffer = buffer.borrow_mut();
        buffer.extend(ops);
        buffer.sort_by(|a, b| a.key().cmp(b.key()))
    }

    #[inline]
    fn location_to_index(&self, location: BinarySearchResult) -> usize {
        use BinarySearchResult::*;
        use Values::*;
        match (self, location) {
            (Leaf(_), Found(idx)) => idx,
            (Leaf(_), NotFound(_)) => unreachable!(),

            (Internal { .. }, Found(idx)) => idx,
            (Internal { .. }, NotFound(0)) => unreachable!(),
            (Internal { .. }, NotFound(i)) => i - 1,

            (First { .. }, Found(i)) => i + 1,
            (First { .. }, NotFound(i)) => i,
        }
    }

    fn take_buffer(&self) -> Vec<Op<K, V>>
    where
        K: Clone,
        V: Clone,
    {
        use Values::*;
        match self {
            Internal { buffer, .. } | First { buffer, .. } => {
                let buffer = buffer.borrow();
                (*buffer).clone()
            }
            Leaf(_) => unreachable!(),
        }
    }

    fn apply_ops(
        &self,
        current_height: Height,
        pivots: &[K],
        mut buffer: Vec<Op<K, V>>,
        b: u32,
        token: &mut MutabilityToken,
    ) -> Vec<Rc<Node<K, V>>>
    where
        K: Ord + Clone,
        V: Clone,
    {
        use self::*;
        use crate::index_multimap;
        use Mapping::*;
        use Op::*;

        buffer.sort_by(|a, b| a.key().cmp(b.key()));
        dedup_all_but_last_by(&mut buffer, |a, b| a.key() == b.key());

        let mappings = self.map_pivots_to_children(pivots);

        let pivots_and_ops = merge_by(mappings, buffer, |a, b| {
            use cmp::Ordering::*;
            match a {
                NegInf(_) => Less,
                &LeadPivot(k, _) | &InnerPivot(k, _) => k.cmp(b.key()),
            }
        });

        let contains_neg_inf_key = matches!(pivots_and_ops.first(), Some((Some(NegInf(..)), ..)));

        let mut pivot_arrays = vec![];
        let mut child_ops = index_multimap!();

        // update the pivots for the current node, splitting if needed
        for (old_mapping, op) in pivots_and_ops {
            let new_pivot = old_mapping.is_none();
            if let Some(mapping) = old_mapping {
                let (is_lead, pivot, child) = mapping.decompose();

                let mapping_is_deleted = matches!(&op, Some(Delete(..)));
                if mapping_is_deleted {
                    todo!("mark that this array of pivots needs to be merged with prev")
                }
                if !mapping_is_deleted && (is_lead || pivot_arrays.is_empty()) {
                    pivot_arrays.push(vec![]);
                }

                child_ops.ensure_key(child.map(PhysicalIdent));

                if let Some(pivot) = pivot.filter(|_| !mapping_is_deleted) {
                    pivot_arrays.last_mut().unwrap().push(pivot.clone())
                }
            };

            if let Some(op) = op {
                if let (Insert(k, _, height), true) = (&op, new_pivot) {
                    if pivot_arrays.is_empty() || *height > current_height {
                        pivot_arrays.push(vec![]);
                    }

                    if *height >= current_height {
                        pivot_arrays.last_mut().unwrap().push(k.clone());
                    }

                    if child_ops.is_empty() {
                        child_ops.ensure_key(None);
                    }
                }

                if !child_ops.is_empty() {
                    child_ops.last_mut().push(op);
                } else {
                    assert!(matches!(op, Delete(..)))
                }
            }
        }

        let mut child_arrays = vec![];
        if current_height == 1 {
            todo!()
        } else {
            let mut new_children = VecDeque::new();
            for (child, ops) in child_ops {
                match child {
                    None => {
                        // TODO double check, is this right?
                        let new_child = Node::empty_first(current_height - 1, b);
                        new_child.add_ops(ops.into(), &mut new_children, b, token);
                        new_children.push_back(new_child);
                    }
                    Some(child) => child.0.add_ops(ops.into(), &mut new_children, b, token),
                }
            }

            let mut first = true;
            for node in &pivot_arrays {
                let mut children = vec![];
                if first && contains_neg_inf_key {
                    children.push(new_children.front().unwrap().clone());
                }
                first = false;
                for pivot in node {
                    let child = new_children.front().unwrap();
                    if !child.contains_key(pivot, token) {
                        new_children.pop_front();
                    }
                    let child = new_children.front().unwrap();
                    assert!(child.contains_key(pivot, token));
                    children.push(child.clone())
                }
                child_arrays.push(children)
            }
        }

        let mut first = true;
        zip(pivot_arrays, child_arrays)
            .map(|(pivots, children)| {
                use Values::*;
                let values = if first && contains_neg_inf_key {
                    first = false;
                    First {
                        buffer: vec![].into(),
                        children,
                    }
                } else {
                    Internal {
                        children,
                        buffer: vec![].into(),
                    }
                };
                Node {
                    height: current_height,
                    pivots,
                    values,
                }
                .into()
            })
            .collect()
    }

    fn map_pivots_to_children<'s>(&'s self, pivots: &'s [K]) -> Vec<Mapping<'s, K, V>> {
        use self::*;
        use Mapping::*;

        match self {
            Values::Leaf(_) => unreachable!(),
            Values::Internal { children, .. } => {
                let mut mappings = Vec::with_capacity(children.len());
                if let [first, others @ ..] = &children[..] {
                    mappings.push(LeadPivot(&pivots[0], first));
                    mappings.extend(zip(&pivots[1..], others).map(|(p, c)| InnerPivot(p, c)));
                }
                mappings
            }
            Values::First { children, .. } => {
                let mut mappings = Vec::with_capacity(children.len());
                match &children[..] {
                    [] => mappings.push(NegInf(None)),
                    [first, others @ ..] => {
                        mappings.push(NegInf(Some(first)));
                        mappings.extend(zip(pivots, others).map(|(p, c)| InnerPivot(p, c)))
                    }
                }
                mappings
            }
        }
    }
}

fn dedup_all_but_last_by<T>(buffer: &mut Vec<T>, mut eq: impl FnMut(&T, &T) -> bool) {
    {
        let mut buffer = &mut buffer[..];
        while !buffer.is_empty() {
            let lead = &buffer[0];
            let run_end = buffer.partition_point(|v| eq(v, lead));
            if run_end > 1 {
                buffer.swap(0, run_end - 1);
            }
            buffer = &mut buffer[run_end..]
        }
    }
    buffer.dedup_by(|a, b| eq(&*a, &*b))
}

#[derive(Clone, Copy)]
enum Mapping<'a, K, V> {
    NegInf(Option<&'a Rc<Node<K, V>>>),
    LeadPivot(&'a K, &'a Rc<Node<K, V>>),
    InnerPivot(&'a K, &'a Rc<Node<K, V>>),
}

type IsLead = bool;

impl<'a, K, V> Mapping<'a, K, V> {
    fn decompose(self) -> (IsLead, Option<&'a K>, Option<&'a Rc<Node<K, V>>>) {
        use Mapping::*;
        match self {
            NegInf(None) => (true, None, None),
            NegInf(Some(child)) => (true, None, Some(child)),
            LeadPivot(pivot, child) => (true, Some(pivot), Some(child)),
            InnerPivot(pivot, child) => (false, Some(pivot), Some(child)),
        }
    }
}

fn merge_by<A, B>(
    a: Vec<A>,
    b: Vec<B>,
    mut cmp: impl FnMut(&A, &B) -> cmp::Ordering,
) -> Vec<(Option<A>, Option<B>)> {
    use cmp::Ordering::*;
    let mut merged = Vec::with_capacity(a.len() + b.len());

    let mut a = a.into_iter();
    let mut b = b.into_iter();
    loop {
        match (a.as_slice(), b.as_slice()) {
            ([], _) => {
                merged.extend(b.map(|b| (None, Some(b))));
                return merged;
            }
            (_, []) => {
                merged.extend(a.map(|a| (Some(a), None)));
                return merged;
            }
            ([a_0, ..], [b_0, ..]) => match cmp(a_0, b_0) {
                Less => merged.push((Some(a.next().unwrap()), None)),
                Greater => merged.push((None, Some(b.next().unwrap()))),
                Equal => merged.push((Some(a.next().unwrap()), Some(b.next().unwrap()))),
            },
        }
    }
}

impl<K, V> Op<K, V> {
    fn height(&self) -> Height {
        match self {
            &Op::Insert(_, _, height) => height,
            &Op::Delete(_, height) => height,
        }
    }

    fn key(&self) -> &K {
        match self {
            Op::Insert(k, _, _) | Op::Delete(k, _) => k,
        }
    }

    fn value(&self) -> Option<&V> {
        match self {
            Op::Insert(_, v, _) => Some(v),
            Op::Delete(_, _) => None,
        }
    }
}

impl From<Result<usize, usize>> for BinarySearchResult {
    fn from(value: Result<usize, usize>) -> Self {
        match value {
            Ok(i) => Self::Found(i),
            Err(i) => Self::NotFound(i),
        }
    }
}
