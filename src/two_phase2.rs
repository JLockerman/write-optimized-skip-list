use std::mem::replace;
#[cfg_attr(nightly, feature(is_sorted))]
use std::{
    cell::RefCell,
    cmp,
    collections::VecDeque,
    hash::{Hash, Hasher},
    iter::{empty, once, zip},
    rc::Rc,
};

use twox_hash::XxHash64;

use itertools::{merge_join_by, Itertools};

use crate::index_multimap::{IndexMultimap, PhysicalIdent};

#[derive(Debug)]
pub struct List<K, V> {
    root: Root<K, V>,
    token: MutabilityToken,
    b: u32,
}

#[derive(Debug)]
enum Root<K, V> {
    Nothing,
    Node(Rc<UpperNode<K, V>>),
    Leaf(Rc<LeafNode<K, V>>),
}

#[derive(Debug)]
struct MutabilityToken;

#[derive(Debug)]
struct UpperNode<K, V> {
    pivots: Vec<K>,
    values: UpperValues<K, V>,
    buffer: RefCell<Vec<Op<K, V>>>,
}

#[derive(Debug)]
enum UpperValues<K, V> {
    High {
        height: Height,
        values: Pointers<UpperNode<K, V>>,
    },
    Low {
        values: Pointers<LeafNode<K, V>>,
    },
}

#[derive(Debug)]
enum Pointers<Node> {
    First { children: Vec<Rc<Node>> },
    Internal { children: Vec<Rc<Node>> },
}

#[derive(Debug)]
struct LeafNode<K, V> {
    entries: Vec<(K, V)>,
}

type Height = u8;

#[derive(Debug, Clone)]
enum Op<K, V> {
    Insert(K, V, Height),
    #[allow(dead_code)]
    Delete(K, Height),
}

#[must_use]
enum BinarySearchResult {
    Found(usize),
    NotFound(usize),
}

#[must_use]
enum GetResult<'a, K, V> {
    Val(Option<&'a V>),
    Upper(&'a UpperNode<K, V>),
    Lower(&'a LeafNode<K, V>),
}

impl<K, V> List<K, V> {
    pub fn new(b: u32) -> Self {
        Self {
            root: Root::Nothing,
            token: MutabilityToken,
            b,
        }
    }

    pub fn get<'s>(&'s self, k: &K) -> Option<&'s V>
    where
        K: Ord,
    {
        use GetResult::*;
        use Root::*;

        let mut node = match &self.root {
            Nothing => return None,
            Node(root) => &**root,
            Leaf(leaf) => return leaf.get(k, &self.token),
        };

        loop {
            match node.get(k, &self.token) {
                Val(result) => return result,
                Lower(leaf) => return leaf.get(k, &self.token),
                Upper(n) => node = n,
            }
        }
    }

    pub fn insert(&mut self, k: K, v: V)
    where
        K: Hash + Ord + Clone,
        V: Clone, // TODO required by immutability of leaves, can/should remove?
    {
        use Root::*;

        let mut hasher = XxHash64::default();
        k.hash(&mut hasher);
        let hash = hasher.finish();
        let height = hash.leading_ones() as u8; // TODO
        match &mut self.root {
            root @ Nothing if height == 0 => {
                let new_root = LeafNode::new_root(k, v);
                *root = Leaf(new_root)
            }
            Leaf(root) if height == 0 => {
                let root = Rc::get_mut(root).unwrap();
                root.insert(k, v);
            }
            Node(root) if height <= root.height() => {
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
            root => {
                let old_root = replace(root, Nothing);
                let new_root =
                    UpperNode::new_level(height, self.b, old_root, once(Op::Insert(k, v, height)));
                *root = Node(new_root)
            }
        }
    }
}

impl<K, V> UpperNode<K, V> {
    fn new_level(
        height: u8,
        _b: u32, //TODO
        next_level: Root<K, V>,
        ops: impl Iterator<Item = Op<K, V>>,
    ) -> Rc<Self> {
        Self {
            pivots: vec![],
            values: UpperValues::new_level(height, next_level),
            buffer: RefCell::new(ops.collect()),
        }
        .into()

        // Rc::new(Self {
        //     height,
        //     pivots: vec![],
        //     values: UpperValues::First {
        //         children: vec![],
        //         buffer: RefCell::new(Vec::with_capacity(b as usize)),
        //     },
        // })
    }

    fn height(&self) -> u8 {
        self.values.height()
    }

    pub fn get<'s>(&'s self, k: &K, token: &MutabilityToken) -> GetResult<'s, K, V>
    where
        K: Ord,
    {
        use GetResult::*;

        if let Some(result) = self.get_from_buffer(k, token) {
            return Val(result);
        }

        let location = self.pivots.binary_search(k).into();
        self.values.get_child(location)
    }

    fn get_from_buffer(&self, k: &K, _token: &MutabilityToken) -> Option<Option<&V>>
    where
        K: Ord,
    {
        // SAFETY The MutabilityToken serves as a witness to the immutability of
        //        the list.
        let buffer = unsafe { self.buffer.try_borrow_unguarded() };
        buffer
            .unwrap()
            .iter()
            .rfind(|b| b.key() == k)
            .map(Op::value)
    }

    pub fn contains_key<'s>(&'s self, k: &K, token: &MutabilityToken) -> bool
    where
        K: Ord,
    {
        self.pivots.get(0) == Some(k) || self.buffer_contains_key(k, token)
    }

    fn buffer_contains_key(&self, k: &K, _token: &MutabilityToken) -> bool
    where
        K: Ord,
    {
        // SAFETY The MutabilityToken serves as a witness to the immutability of
        //        the list.
        let buffer = unsafe { self.buffer.try_borrow_unguarded() };
        buffer.unwrap().iter().rfind(|b| b.key() == k).is_some()
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
        assert!(self.height() >= 1);
        assert!(ops.len() <= b as usize);
        #[cfg(nightly)]
        {
            assert!(ops.as_slices().0.is_sorted());
            assert!(ops.as_slices().1.is_sorted());
        }

        let remaining_buffer_space = (b as usize).saturating_sub(self.slots_used());

        if remaining_buffer_space >= ops.len() {
            self.extend_buffer_with_ops(ops.into_iter());
            return;
        }

        // TODO think long and hard about what this means for durability
        self.extend_buffer_with_ops(ops.drain(..remaining_buffer_space));

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

            node.extend_buffer_with_ops(ops_for_child)
        }

        replacement_nodes.extend(new_nodes);
    }

    fn extend_buffer_with_ops(&self, ops: impl Iterator<Item = Op<K, V>>)
    where
        K: Ord,
    {
        let mut buffer = self.buffer.borrow_mut();
        buffer.extend(ops);
        buffer.sort_by(|a, b| a.key().cmp(b.key()))
    }

    fn slots_used(&self) -> usize {
        self.buffer.borrow().len() + self.values.slots_used()
    }

    pub fn flush(&self, b: u32, token: &mut MutabilityToken) -> Vec<Rc<Self>>
    where
        K: Ord + Clone,
        V: Clone,
    {
        debug_assert!(self.height() > 0);

        let buffer = self.take_buffer();
        let new_nodes = self.values.apply_ops(&self.pivots, buffer, b, token);

        new_nodes
    }

    fn take_buffer(&self) -> Vec<Op<K, V>>
    where
        K: Clone,
        V: Clone,
    {
        self.buffer.clone().into_inner()
    }
}

impl<K, V> UpperValues<K, V> {
    fn new_level(height: u8, next_level: Root<K, V>) -> Self {
        use Root::*;
        use UpperValues::*;
        match (height, next_level) {
            (0, Leaf(leaf)) => Low {
                values: Pointers::new_first(once(leaf)),
            },
            (0, Nothing) => Low {
                values: Pointers::new_first(empty()),
            },
            (_, Nothing) => High {
                height,
                values: Pointers::new_first(empty()),
            },
            (_, Node(node)) => High {
                height,
                values: Pointers::new_first(once(node)),
            },
            _ => unreachable!(),
        }
    }

    fn is_first(&self) -> bool {
        match self {
            UpperValues::High { values, .. } => values.is_first(),
            UpperValues::Low { values, .. } => values.is_first(),
        }
    }

    fn height(&self) -> u8 {
        match self {
            UpperValues::High { height, .. } => *height,
            UpperValues::Low { .. } => 1,
        }
    }

    fn get_child(&self, location: BinarySearchResult) -> GetResult<'_, K, V> {
        use GetResult::*;
        use UpperValues::*;

        // if we only have a buffer but no children we're done searching
        if self.slots_used() == 0 {
            return Val(None);
        }

        match self {
            High { values, .. } => Upper(&values[location]),
            Low { values } => Lower(&values[location]),
        }
    }

    fn slots_used(&self) -> usize {
        use UpperValues::*;
        match self {
            High { values, .. } => values.slots_used(),
            Low { values } => values.slots_used(),
        }
    }

    fn apply_ops(
        &self,
        pivots: &[K],
        mut buffer: Vec<Op<K, V>>,
        b: u32,
        token: &mut MutabilityToken,
    ) -> Vec<Rc<UpperNode<K, V>>>
    where
        K: Ord + Clone,
        V: Clone,
    {
        use UpperValues::*;

        buffer.sort_by(|a, b| a.key().cmp(b.key()));
        dedup_all_but_last_by(&mut buffer, |a, b| a.key() == b.key());

        match self {
            High {
                height: current_height,
                values,
            } => {
                let (pivot_arrays, child_ops) =
                    values.apply_ops_to_node(pivots, buffer, *current_height);

                let contains_neg_inf_key = values.is_first();

                let mut new_children = VecDeque::new();
                for (child, ops) in child_ops {
                    match child {
                        None => {
                            // TODO double check, is this right?
                            let new_child =
                                UpperNode::new_level(current_height - 1, b, Root::Nothing, empty());
                            new_child.add_ops(ops.into(), &mut new_children, b, token);
                            new_children.push_back(new_child);
                        }
                        Some(child) => child.0.add_ops(ops.into(), &mut new_children, b, token),
                    }
                }

                let mut child_arrays = vec![];
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

                let mut first = true;
                zip(pivot_arrays, child_arrays)
                    .map(|(pivots, children)| {
                        use Pointers::*;
                        let values = if first && contains_neg_inf_key {
                            first = false;
                            First { children }
                        } else {
                            Internal { children }
                        };
                        UpperNode {
                            pivots,
                            values: High {
                                height: *current_height,
                                values,
                            },
                            buffer: vec![].into(),
                        }
                        .into()
                    })
                    .collect()
            }
            Low { values } => {
                use itertools::EitherOrBoth::*;
                use AnnotatedPivot::*;
                use Op::*;
                // let (pivot_arrays, child_ops) = values.apply_ops_to_node(pivots, buffer, 1);

                // let mut new_children = VecDeque::new();

                // TODO a heuristic letting us keep leaves that haven't changed
                //      would be useful, but this one isn't _quite_ right:
                //       1. We need to see if a node needs to split b/c a pivot
                //          was added in its key range.
                //       2. In the presence of DELETEs we may need to mutate the
                //          leaf before the one that has the first op.
                //
                // let ops_start = child_ops
                //     .iter()
                //     .map_while(|(child, ops)| {
                //         let (Some(child), []) = (child, &ops[..]) else {
                //             return None
                //         };
                //         new_children.push_back(Rc::clone(&child.0));
                //         Some(())
                //     })
                //     .count();

                // for (child, ops) in child_ops.into_iter().skip(ops_start) {
                //     todo!()
                // }

                let annotated_pivots_and_ops =
                    values
                        .annotate_pivots(pivots)
                        .merge_join_by(buffer.iter(), |a, b| {
                            use cmp::Ordering::*;
                            match a {
                                NegInf => Less,
                                &Lead(k) | &Inner(k) => k.cmp(b.key()),
                            }
                        });

                let mut pivot_arrays = vec![];
                for pop in annotated_pivots_and_ops {
                    match pop {
                        Left(NegInf) => pivot_arrays.push(vec![]),
                        Both(Lead(k), Insert(..)) | Left(Lead(k)) => {
                            pivot_arrays.push(vec![k.clone()])
                        }
                        Both(Inner(k), Insert(..)) | Left(Inner(k)) => {
                            pivot_arrays.last_mut().unwrap().push(k.clone())
                        }
                        Right(Insert(k, _, height)) => {
                            if *height > 1 {
                                pivot_arrays.push(vec![])
                            }

                            if *height >= 1 {
                                pivot_arrays.last_mut().unwrap().push(k.clone())
                            }
                        }
                        Both(_, Delete(..)) | Right(Delete(..)) => {}
                        Both(NegInf, _) => unreachable!(),
                    }
                }

                let leaf_entries = values.iter().flat_map(|leaf| leaf.entries.iter());
                let entries = leaf_entries
                    .merge_join_by(buffer, |(k, _), op| k.cmp(op.key()))
                    .filter_map(|eop| match eop {
                        Both(_, Insert(k, v, ..)) | Right(Insert(k, v, ..)) => Some((k, v)),
                        Both(_, Delete(..)) | Right(Delete(..)) => None,
                        Left((k, v)) => Some((k.clone(), v.clone())),
                    });

                let has_neg_inf = values.is_first();
                let first_keyed_pivot = if has_neg_inf { 1 } else { 0 };
                let mut remaining_nodes = &pivot_arrays[first_keyed_pivot..];
                let mut group_key = None;
                let values_per_child = entries.group_by(|(k, _)| {
                    if !remaining_nodes.is_empty() && k >= &remaining_nodes[0][0] {
                        group_key = Some(&remaining_nodes[0][0]);
                        remaining_nodes = &remaining_nodes[1..];
                    }
                    group_key
                });

                let mut child_arrays = Vec::with_capacity(pivot_arrays.len());
                for (i, (_, values)) in values_per_child.into_iter().enumerate() {
                    let mut remaining_pivots = &pivot_arrays[i][..];
                    let mut group_key = None;
                    let pivot_lead_runs = values.group_by(|(k, _)| {
                        if !remaining_pivots.is_empty() && k >= &remaining_pivots[0] {
                            group_key = Some(&remaining_pivots[0]);
                            remaining_pivots = &remaining_pivots[..];
                        }
                        group_key
                    });
                    let mut children = VecDeque::new();
                    let mut current_leaf = vec![];
                    let mut num_runs = 0;
                    for (_, group) in &pivot_lead_runs {
                        let run = group.collect_vec();
                        let new_len = current_leaf.len() + run.len();
                        if current_leaf.is_empty() {
                            current_leaf = run;
                            num_runs = 1;
                        } else if new_len > b as usize {
                            children.push_back((num_runs, LeafNode::from_entries(current_leaf)));
                            current_leaf = run;
                            num_runs = 1;
                        } else {
                            current_leaf.extend(run);
                            num_runs += 1;
                        }
                    }
                    children.push_back((num_runs, LeafNode::from_entries(current_leaf)));
                    child_arrays.push(children)
                }

                let mut first = true;
                zip(pivot_arrays, child_arrays)
                    .map(|(pivots, children)| {
                        use Pointers::*;
                        // TODO
                        let children = children
                            .into_iter()
                            .flat_map(|(c, leaf)| (0..c).map(move |_| leaf.clone()))
                            .collect();
                        let values = if first && has_neg_inf {
                            first = false;
                            First { children }
                        } else {
                            Internal { children }
                        };
                        UpperNode {
                            pivots,
                            values: Low { values },
                            buffer: vec![].into(),
                        }
                        .into()
                    })
                    .collect()
            }
        }
    }
}

impl<K, V> LeafNode<K, V> {
    fn new_root(k: K, v: V) -> Rc<Self> {
        Self {
            entries: vec![(k, v)],
        }
        .into()
    }

    fn from_entries(entries: Vec<(K, V)>) -> Rc<Self> {
        Self { entries }.into()
    }

    fn get(&self, k: &K, _token: &MutabilityToken) -> Option<&V>
    where
        K: Ord,
    {
        let Ok(idx) = self.entries.binary_search_by_key(&k, |(k, _)| k) else {
            return None
        };

        Some(&self.entries[idx].1)
    }

    fn insert(&mut self, k: K, v: V)
    where
        K: Ord,
    {
        let location = self.entries.binary_search_by_key(&&k, |(k, _)| k);
        match location {
            Ok(i) => self.entries[i].1 = v,
            Err(i) => self.entries.insert(i, (k, v)),
        }
    }
}

impl<Node> Pointers<Node> {
    fn new_first(node: impl Iterator<Item = Rc<Node>>) -> Self {
        Self::First {
            children: node.collect(),
        }
    }

    fn is_first(&self) -> bool {
        matches!(self, &Pointers::First { .. })
    }

    fn slots_used(&self) -> usize {
        use Pointers::*;
        let (First { children } | Internal { children }) = self;
        children.len()
    }

    fn apply_ops_to_node<'a, K, V>(
        &'a self,
        pivots: &'a [K],
        buffer: Vec<Op<K, V>>,
        current_height: u8,
    ) -> (
        Vec<Vec<K>>,
        IndexMultimap<Option<PhysicalIdent<&Rc<Node>>>, Op<K, V>>,
    )
    where
        K: Ord + Clone,
    {
        use crate::index_multimap;
        use Mapping::*;
        use Op::*;

        let mappings = self.map_pivots_to_children(pivots);

        let pivots_and_ops = merge_by(mappings, buffer, |a, b| {
            use cmp::Ordering::*;
            match a {
                NegInf(_) => Less,
                &LeadPivot(k, _) | &InnerPivot(k, _) => k.cmp(b.key()),
            }
        });

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
        (pivot_arrays, child_ops)
    }

    fn map_pivots_to_children<'s, K>(&'s self, pivots: &'s [K]) -> Vec<Mapping<'s, K, Node>> {
        use Mapping::*;
        use Pointers::*;

        match self {
            Internal { children, .. } => {
                let mut mappings = Vec::with_capacity(children.len());
                if let [first, others @ ..] = &children[..] {
                    mappings.push(LeadPivot(&pivots[0], first));
                    mappings.extend(zip(&pivots[1..], others).map(|(p, c)| InnerPivot(p, c)));
                }
                mappings
            }
            First { children, .. } => {
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

    fn annotate_pivots<'s, K>(
        &'s self,
        pivots: &'s [K],
    ) -> impl Iterator<Item = AnnotatedPivot<'s, K>> {
        use AnnotatedPivot::*;
        use Pointers::*;

        let (first, others) = match self {
            First { .. } => (Some(NegInf), pivots),
            Internal { .. } => pivots
                .split_first()
                .map(|(f, s)| (Some(Lead(f)), s))
                .unwrap_or((None, &[])),
        };
        first.into_iter().chain(others.into_iter().map(Inner))
    }

    fn iter(&self) -> impl Iterator<Item = &Rc<Node>> {
        use Pointers::*;
        let (First { children } | Internal { children }) = self;
        children.iter()
    }

    // #[inline]
    // fn location_to_index(&self, location: BinarySearchResult) -> usize {
    //     use BinarySearchResult::*;
    //     use Pointers::*;
    //     match (self, location) {
    //         // (Leaf(_), Found(idx)) => idx,
    //         // (Leaf(_), NotFound(_)) => unreachable!(),

    //         (Internal { .. }, Found(idx)) => idx,
    //         (Internal { .. }, NotFound(0)) => unreachable!(),
    //         (Internal { .. }, NotFound(i)) => i - 1,

    //         (First { .. }, Found(i)) => i + 1,
    //         (First { .. }, NotFound(i)) => i,
    //     }
    // }
}

impl<Node> std::ops::Index<BinarySearchResult> for Pointers<Node> {
    type Output = Node;

    fn index(&self, index: BinarySearchResult) -> &Self::Output {
        use BinarySearchResult::*;
        use Pointers::*;
        let idx = match (self, index) {
            // (Leaf(_), Found(idx)) => idx,
            // (Leaf(_), NotFound(_)) => unreachable!(),
            (Internal { .. }, Found(idx)) => idx,
            (Internal { .. }, NotFound(0)) => unreachable!(),
            (Internal { .. }, NotFound(i)) => i - 1,

            (First { .. }, Found(i)) => i + 1,
            (First { .. }, NotFound(i)) => i,
        };

        let (First { children } | Internal { children }) = self;
        &children[idx]
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
enum Mapping<'a, K, Node> {
    NegInf(Option<&'a Rc<Node>>),
    LeadPivot(&'a K, &'a Rc<Node>),
    InnerPivot(&'a K, &'a Rc<Node>),
}

type IsLead = bool;

impl<'a, K, Node> Mapping<'a, K, Node> {
    fn decompose(self) -> (IsLead, Option<&'a K>, Option<&'a Rc<Node>>) {
        use Mapping::*;
        match self {
            NegInf(None) => (true, None, None),
            NegInf(Some(child)) => (true, None, Some(child)),
            LeadPivot(pivot, child) => (true, Some(pivot), Some(child)),
            InnerPivot(pivot, child) => (false, Some(pivot), Some(child)),
        }
    }
}

#[derive(Clone, Copy)]
enum AnnotatedPivot<'a, K> {
    NegInf,
    Lead(&'a K),
    Inner(&'a K),
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
