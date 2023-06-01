#[cfg_attr(nightly, feature(is_sorted))]
use std::{
    cmp,
    collections::VecDeque,
    hash::{Hash, Hasher},
    iter::{empty, once},
    rc::Rc,
};
use std::{collections::HashSet, mem::{replace, swap}};

use twox_hash::XxHash64;

use rand::{distributions::Bernoulli, prelude::Distribution, rngs::StdRng, SeedableRng};

use itertools::{merge_join_by, zip_eq, EitherOrBoth, Itertools};

#[derive(Debug)]
pub struct List<K, V> {
    b: u32,
    distribution: Bernoulli,
    root: Root<K, V>,
}

#[derive(Debug)]
enum Root<K, V> {
    Nothing,
    Node(Rc<UpperNode<K, V>>),
    Leaf(Rc<LeafNode<K, V>>),
}

#[derive(Debug)]
struct MutabilityToken;

#[derive(Debug, Clone)]
struct UpperNode<K, V> {
    buffer: Vec<Op<K, V>>,
    pivots: Vec<K>,
    values: UpperValues<K, V>,
}

#[derive(Debug, Clone)]
enum UpperValues<K, V> {
    High {
        height: Height,
        values: Pointers<UpperNode<K, V>>,
    },
    Low {
        values: Pointers<LeafNode<K, V>>,
    },
}

#[derive(Debug, Clone)]
enum Pointers<Node> {
    First { children: Vec<Rc<Node>> },
    Internal { children: Vec<Rc<Node>> },
}

#[derive(Debug, Clone)]
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
            b,
            // TODO allow changing eplison (currently always 0.5)
            distribution: Bernoulli::new(1.0 / (b as f64).sqrt()).unwrap(),
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
            Leaf(leaf) => return leaf.get(k),
        };

        loop {
            match node.get(k) {
                Val(result) => return result,
                Lower(leaf) => return leaf.get(k),
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
        // let height = hash.leading_ones() as u8; // TODO
        let rng = StdRng::seed_from_u64(hash);
        let height = self
            .distribution
            .sample_iter(rng)
            .take_while(|sample| *sample)
            .count() as u8;
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
                let root_node = Rc::get_mut(root).unwrap();
                let insert = Op::Insert(k, v, height);
                let new = root_node.add_op_to_root(insert, self.b);
                if let Some(new_root) = new {
                    *root = new_root
                };
            }
            root => {
                let old_root = replace(root, Nothing);
                let new_root =
                    UpperNode::new_level(height, self.b, old_root, once(Op::Insert(k, v, height)));
                *root = Node(new_root)
            }
        }
    }

    pub fn assert_structure(&self)
    where
        K: Ord,
    {
        use Root::*;
        match &self.root {
            Nothing => {}
            Node(node) => node.assert_structure(),
            Leaf(leaf) => leaf.assert_structure(),
        }
    }
}

impl<K, V> UpperNode<K, V> {
    fn new_level(
        height: u8,
        b: u32, //TODO
        next_level: Root<K, V>,
        ops: impl Iterator<Item = Op<K, V>>,
    ) -> Rc<Self> {
        Self {
            pivots: vec![],
            values: UpperValues::new_level(height, b, next_level),
            buffer: ops.collect(),
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

    fn assert_structure(&self)
    where
        K: Ord,
    {
        use Pointers::*;
        use UpperValues::*;
        assert!(self.pivots.windows(2).all(|w| w[0] < w[1]));

        match &self.values {
            High {
                height: _,
                values: First { children },
            } => {
                for child in children {
                    child.assert_structure()
                }
            }
            High {
                height: _,
                values: Internal { children },
            } => {
                for child in children {
                    child.assert_structure()
                }
            }
            Low {
                values: First { children },
            } => {
                for child in children {
                    child.assert_structure()
                }
            }
            Low {
                values: Internal { children },
            } => {
                for child in children {
                    child.assert_structure()
                }
            }
        }
    }

    fn height(&self) -> u8 {
        self.values.height()
    }

    pub fn get<'s>(&'s self, k: &K) -> GetResult<'s, K, V>
    where
        K: Ord,
    {
        use GetResult::*;

        if let Some(result) = self.get_from_buffer(k) {
            return Val(result);
        }

        let location = self.pivots.binary_search(k).into();
        self.values.get_child(location)
    }

    fn get_from_buffer(&self, k: &K) -> Option<Option<&V>>
    where
        K: Ord,
    {
        self.buffer.iter().rfind(|b| b.key() == k).map(Op::value)
    }

    pub fn contains_key<'s>(&'s self, k: &K) -> bool
    where
        K: Ord,
    {
        self.pivots.get(0) == Some(k) || self.buffer_contains_key(k)
    }

    fn buffer_contains_key(&self, k: &K) -> bool
    where
        K: Ord,
    {
        self.buffer.iter().rfind(|b| b.key() == k).is_some()
    }

    fn bfs(&self) {
        use UpperValues::*;

        let mut next_level = VecDeque::new();
        match &self.values {
            High { values, .. } => {
                for child in values.unique_children() {
                    next_level.push_back(child)
                }
            }
            Low { values } => todo!(),
        }

        let mut current_level = next_level;
        let mut next_level = VecDeque::new();
        loop {
            let children = current_level
                .drain(..)
                .flat_map(|n| match &n.values {
                    High { values, .. } => values.unique_children(),
                    Low { values } => todo!(),
                })
                .dedup_by(|a, b| Rc::ptr_eq(a, b));
            for child in children {
                next_level.push_back(child)
            }
            swap(&mut current_level, &mut next_level)
        }
    }

    fn add_op_to_root(&mut self, op: Op<K, V>, b: u32) -> Option<Rc<Self>>
    where
        K: Ord + Clone,
        V: Clone,
    {
        debug_assert!(self.height() >= 1);
        let remaining_buffer_space = (b as usize).saturating_sub(self.slots_used());

        if remaining_buffer_space >= 1 {
            self.extend_buffer_with_ops(once(op));
            return None;
        }

        // TODO can we elide the VecDeque
        // let mut new_nodes = self.flush(b, once(op));
        let mut new_nodes = self.flush(b);

        assert_eq!(new_nodes.len(), 1);
        // new_nodes.pop_front()
        let mut new_root = new_nodes.pop_front().unwrap();
        let root = Rc::get_mut(&mut new_root).unwrap();
        root.extend_buffer_with_ops(once(op));
        Some(new_root)
    }

    fn add_ops(
        &self,
        mut ops: VecDeque<Op<K, V>>,
        replacement_nodes: &mut VecDeque<Rc<Self>>,
        b: u32,
    ) where
        K: Ord + Clone,
        V: Clone,
    {
        debug_assert!(self.height() >= 1);
        debug_assert!(ops.len() <= b as usize);
        #[cfg(nightly)]
        {
            debug_assert!(ops.as_slices().0.is_sorted());
            debug_assert!(ops.as_slices().1.is_sorted());
        }

        let remaining_buffer_space = (b as usize).saturating_sub(self.slots_used());

        if remaining_buffer_space >= ops.len() {
            let mut new_node = self.clone();
            new_node.buffer.extend(ops);
            replacement_nodes.push_back(Rc::new(new_node));
            return;
        }

        // TODO think long and hard about what flushing the ops immediately
        //      means for durability
        // let new_nodes = self.flush(b, ops.into_iter());
        let mut new_nodes = self.flush(b);

        for node in new_nodes.iter_mut().rev() {
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

            let node = Rc::get_mut(node).unwrap();
            node.extend_buffer_with_ops(ops_for_child)
        }

        replacement_nodes.extend(new_nodes);
    }

    fn extend_buffer_with_ops(&mut self, ops: impl Iterator<Item = Op<K, V>>)
    where
        K: Ord,
    {
        self.buffer.extend(ops);
        self.buffer.sort_by(|a, b| a.key().cmp(b.key()))
    }

    fn slots_used(&self) -> usize {
        self.buffer.len() + self.values.slots_used()
    }

    fn flush(&self, b: u32) -> VecDeque<Rc<UpperNode<K, V>>>
    where
        K: Ord + Clone,
        V: Clone,
    {
        // TODO think long and hard about what flushing the ops immediately
        //      means for durability
        // let to_flush = self.buffer.iter().cloned().chain(additional_ops);
        let to_flush = self.buffer.iter().cloned();
        let new_nodes = self.values.apply_ops(&self.pivots, to_flush, b);
        new_nodes
    }
}

impl<K, V> UpperValues<K, V> {
    fn new_level(height: u8, b: u32, next_level: Root<K, V>) -> Self {
        use Root::*;
        use UpperValues::*;
        match (height, next_level) {
            (1, Leaf(leaf)) => Low {
                values: Pointers::new_first(once(leaf)),
            },
            (1, Nothing) => Low {
                values: Pointers::new_first(empty()),
            },
            (height, leaf @ Leaf(..)) => High {
                height,
                values: Pointers::new_first(once(UpperNode::new_level(
                    height - 1,
                    b,
                    leaf,
                    empty(),
                ))),
            },
            (_, Node(node)) if node.height() == height - 1 => High {
                height,
                values: Pointers::new_first(once(node)),
            },
            (_, Node(node)) => High {
                height,
                values: Pointers::new_first(once(UpperNode::new_level(
                    height - 1,
                    b,
                    Node(node),
                    empty(),
                ))),
            },
            (_, Nothing) => High {
                height,
                values: Pointers::new_first(empty()),
            },
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
        ops: impl Iterator<Item = Op<K, V>>,
        b: u32,
    ) -> VecDeque<Rc<UpperNode<K, V>>>
    where
        K: Ord + Clone,
        V: Clone,
    {
        use UpperValues::*;

        let mut buffer = ops.collect_vec();
        buffer.sort_by(|a, b| a.key().cmp(b.key()));
        dedup_all_but_last_by(&mut buffer, |a, b| a.key() == b.key());

        let pivot_arrays = self.apply_ops_to_pivots(pivots, &buffer);

        match self {
            High { height, values } => {
                // TODO if we're splitting the current node into multiple,
                // should we try to allocate the buffer amongst the new nodes at
                // the current level first?
                let child_arrays =
                    values.apply_ops_to_children(height, b, buffer, &pivot_arrays, pivots);

                Self::build_from_parts(pivot_arrays, child_arrays, |values| High {
                    height: *height,
                    values,
                })
            }
            Low { values } => {
                let child_arrays = values.apply_ops_to_children(buffer, &pivot_arrays, b);

                Self::build_from_parts(pivot_arrays, child_arrays, |values| Low { values })
            }
        }
    }

    fn apply_ops_to_pivots(&self, pivots: &[K], buffer: &[Op<K, V>]) -> Vec<Vec<K>>
    where
        K: Ord + Clone,
        V: Clone,
    {
        use UpperValues::*;
        match self {
            High { values, height } => {
                let annotated_pivots_and_ops = values.annotate_pivots_and_ops(pivots, buffer);
                Self::build_pivot_arrays(*height, annotated_pivots_and_ops)
            }
            Low { values } => {
                let annotated_pivots_and_ops = values.annotate_pivots_and_ops(pivots, buffer);
                Self::build_pivot_arrays(1, annotated_pivots_and_ops)
            }
        }
    }

    fn build_pivot_arrays<'a>(
        current_height: u8,
        annotated_pivots_and_ops: impl Iterator<
            Item = EitherOrBoth<AnnotatedPivot<'a, K>, &'a Op<K, V>>,
        >,
    ) -> Vec<Vec<K>>
    where
        K: Clone + 'a,
        V: 'a,
    {
        use itertools::EitherOrBoth::*;
        use AnnotatedPivot::*;
        use Op::*;

        let mut pivot_arrays = vec![];
        for pop in annotated_pivots_and_ops {
            match pop {
                Left(NegInf) => pivot_arrays.push(vec![]),
                Both(Lead(k), Insert(..)) | Left(Lead(k)) => pivot_arrays.push(vec![k.clone()]),
                Both(Inner(k), Insert(..)) | Left(Inner(k)) => {
                    pivot_arrays.last_mut().unwrap().push(k.clone())
                }
                Right(Insert(k, _, height)) => {
                    if *height > current_height {
                        pivot_arrays.push(vec![])
                    }

                    if *height >= current_height {
                        pivot_arrays.last_mut().unwrap().push(k.clone())
                    }
                }
                Both(_, Delete(..)) | Right(Delete(..)) => {}
                Both(NegInf, _) => unreachable!(),
            }
        }
        pivot_arrays
    }

    fn build_from_parts<N>(
        pivot_arrays: Vec<Vec<K>>,
        child_arrays: Vec<N>,
        mut values_builder: impl FnMut(N) -> UpperValues<K, V>,
    ) -> VecDeque<Rc<UpperNode<K, V>>> {
        zip_eq(pivot_arrays, child_arrays)
            .map(|(pivots, values)| {
                UpperNode {
                    pivots,
                    values: values_builder(values),
                    buffer: vec![].into(),
                }
                .into()
            })
            .collect()
    }
}

impl<K, V> LeafNode<K, V> {
    fn new_root(k: K, v: V) -> Rc<Self> {
        Self {
            entries: vec![(k, v)],
        }
        .into()
    }

    fn assert_structure(&self)
    where
        K: Ord,
    {
        assert!(self.entries.windows(2).all(|w| w[0].0 < w[1].0));
    }

    fn from_entries(entries: Vec<(K, V)>) -> Rc<Self> {
        Self { entries }.into()
    }

    fn get(&self, k: &K) -> Option<&V>
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

impl<K, V> Pointers<UpperNode<K, V>> {
    fn apply_ops_to_children(
        &self,
        current_height: &u8,
        b: u32,
        buffer: Vec<Op<K, V>>,
        pivot_arrays: &Vec<Vec<K>>,
        pivots: &[K],
    ) -> Vec<Self>
    where
        K: Ord + Clone,
        V: Clone,
    {
        if self.is_empty() {
            // FIXME is this right?
            debug_assert!(self.is_first());
            let child =
                UpperNode::new_level(current_height - 1, b, Root::Nothing, buffer.into_iter());

            if child.slots_used() >= b as usize {
                let new_children = child.flush(b);
                return self.place_children_with_pivots(pivot_arrays, new_children);
            }

            let mut child_arrays = Vec::with_capacity(pivot_arrays.len());
            let mut first = true;
            for pivots in pivot_arrays {
                let children = vec![child.clone(); pivots.len() + first as usize];
                child_arrays.push(Pointers::First { children }.into());
                first = false;
            }
            return child_arrays;
        }

        let mut pivots_and_children = self
            .map_pivots_to_children(pivots)
            .dedup_by(|(_, a), (_, b)| Rc::ptr_eq(a, b))
            .peekable();
        let _first_child = pivots_and_children.next().unwrap().1;
        let mut group_key = 0;
        // FIXME need to dedup to physical children
        let ops_per_pivot = buffer.into_iter().group_by(|op| {
            let increment = pivots_and_children
                .peeking_take_while(|(pivot, _)| pivot <= op.key())
                .count();
            group_key += increment;
            group_key
        });

        let mut new_children = VecDeque::new();
        let old_children = self.unique_children().enumerate();
        let children_and_ops =
            merge_join_by(old_children, &ops_per_pivot, |(i, _), (j, _)| i.cmp(j));
        for child_state in children_and_ops {
            use EitherOrBoth::{Both as Mutated, Left as Unchanged, Right as OnlyOps};
            match child_state {
                OnlyOps(_) => unreachable!(),
                Unchanged((_, child)) => new_children.push_back(child.clone()),
                Mutated((_, child), (_, ops)) => child.add_ops(ops.collect(), &mut new_children, b),
            }
        }

        self.place_children_with_pivots(pivot_arrays, new_children)
    }
}

impl<K, V> Pointers<LeafNode<K, V>> {
    fn apply_ops_to_children(
        &self,
        buffer: Vec<Op<K, V>>,
        pivot_arrays: &Vec<Vec<K>>,
        b: u32,
    ) -> Vec<Self>
    where
        K: Ord + Clone,
        V: Clone,
    {
        use itertools::EitherOrBoth::*;
        use Op::*;

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
        //
        // for (child, ops) in child_ops.into_iter().skip(ops_start) {
        //     ...
        // }

        let leaf_entries = self.unique_children().flat_map(|leaf| leaf.entries.iter());
        let entries = leaf_entries
            .merge_join_by(buffer, |(k, _), op| k.cmp(op.key()))
            .filter_map(|eop| match eop {
                Both(_, Insert(k, v, ..)) | Right(Insert(k, v, ..)) => Some((k, v)),
                Both(_, Delete(..)) | Right(Delete(..)) => None,
                Left((k, v)) => Some((k.clone(), v.clone())),
            });

        let has_neg_inf = self.is_first();
        let first_keyed_pivot = if has_neg_inf { 1 } else { 0 };
        let mut remaining_nodes = &pivot_arrays[first_keyed_pivot..];
        let mut group_key = 0;
        let values_per_child = entries.group_by(|(k, _)| {
            while !remaining_nodes.is_empty() && k >= &remaining_nodes[0][0] {
                remaining_nodes = &remaining_nodes[1..];
                group_key += 1;
            }
            group_key
        });

        let mut new_children = VecDeque::new();
        for (i, values) in values_per_child.into_iter() {
            let mut remaining_pivots = &pivot_arrays[i][..];
            let mut group_key = None;
            // FIXME is this right?
            let pivot_lead_runs = values.group_by(|(k, _)| {
                while !remaining_pivots.is_empty() && k >= &remaining_pivots[0] {
                    group_key = Some(&remaining_pivots[0]);
                    remaining_pivots = &remaining_pivots[1..];
                }
                group_key
            });

            let mut current_leaf = vec![];
            for (_, group) in &pivot_lead_runs {
                let run = group.collect_vec();
                let new_len = current_leaf.len() + run.len();
                if current_leaf.is_empty() {
                    current_leaf = run;
                } else if new_len > b as usize {
                    new_children.push_back(LeafNode::from_entries(current_leaf));
                    current_leaf = run;
                } else {
                    current_leaf.extend(run);
                }
            }
            let num_children = new_children.len();
            if num_children < i {
                new_children.extend((num_children..i).map(|_| LeafNode::from_entries(vec![])))
            }
            new_children.push_back(LeafNode::from_entries(current_leaf));
        }

        self.place_children_with_pivots(pivot_arrays, new_children)
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

    fn is_empty(&self) -> bool {
        self.slots_used() == 0
    }

    fn slots_used(&self) -> usize {
        use Pointers::*;
        let (First { children } | Internal { children }) = self;
        children.len()
    }

    fn map_pivots_to_children<'s, K>(
        &'s self,
        pivots: &'s [K],
    ) -> impl Iterator<Item = (AnnotatedPivot<'s, K>, &'s Rc<Node>)> {
        use Pointers::*;

        let annotated = self.annotate_pivots(pivots);
        let (First { children, .. } | Internal { children, .. }) = self;
        annotated.zip_eq(children)
    }

    fn annotate_pivots_and_ops<'a, K, V>(
        &'a self,
        pivots: &'a [K],
        buffer: &'a [Op<K, V>],
    ) -> impl Iterator<Item = EitherOrBoth<AnnotatedPivot<'a, K>, &'a Op<K, V>>>
    where
        K: Ord,
    {
        self.annotate_pivots(pivots)
            .merge_join_by(buffer.iter(), |a, b| a.partial_cmp(b.key()).unwrap())
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

    fn unique_children(&self) -> impl Iterator<Item = &Rc<Node>> {
        use Pointers::*;
        let (First { children } | Internal { children }) = self;
        children.iter().dedup_by(|a, b| Rc::ptr_eq(a, b))
    }

    fn place_children_with_pivots<K>(
        &self,
        pivot_arrays: &Vec<Vec<K>>,
        mut new_children: VecDeque<Rc<Node>>,
    ) -> Vec<Self>
    where
        K: Ord,
        Rc<Node>: ContainsKey<K>,
    {
        let has_neg_inf = self.is_first();

        let mut child_arrays = Vec::with_capacity(pivot_arrays.len());

        let mut first = true;
        for node in pivot_arrays {
            let mut children = vec![];
            if first && has_neg_inf {
                // TODO may not be right?
                children.push(new_children.front().unwrap().clone());
            }

            for pivot in node {
                let child = new_children.front().unwrap();
                if !child.contains_key(pivot) {
                    new_children.pop_front();
                }
                let child = new_children.front().unwrap();
                assert!(child.contains_key(pivot));
                children.push(child.clone())
            }

            let pointers = if first && has_neg_inf {
                Self::First { children }
            } else {
                Self::Internal { children }
            };

            child_arrays.push(pointers);
            first = false;
        }

        child_arrays
    }
}

impl<Node> std::ops::Index<BinarySearchResult> for Pointers<Node> {
    type Output = Node;

    fn index(&self, index: BinarySearchResult) -> &Self::Output {
        use BinarySearchResult::*;
        use Pointers::*;
        let idx = match (self, index) {
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
enum AnnotatedPivot<'a, K> {
    NegInf,
    Lead(&'a K),
    Inner(&'a K),
}

impl<'a, K> PartialEq<K> for AnnotatedPivot<'a, K>
where
    K: PartialEq,
{
    fn eq(&self, other: &K) -> bool {
        use AnnotatedPivot::*;
        match self {
            NegInf => false,
            &Lead(pivot) | &Inner(pivot) => pivot.eq(other),
        }
    }
}

impl<'a, K> PartialOrd<K> for AnnotatedPivot<'a, K>
where
    K: PartialOrd,
{
    fn partial_cmp(&self, other: &K) -> Option<cmp::Ordering> {
        use cmp::Ordering::Less;
        use AnnotatedPivot::*;
        match self {
            NegInf => Some(Less),
            &Lead(pivot) | &Inner(pivot) => pivot.partial_cmp(other),
        }
    }
}

impl<K, V> Op<K, V> {
    // fn height(&self) -> Height {
    //     match self {
    //         &Op::Insert(_, _, height) => height,
    //         &Op::Delete(_, height) => height,
    //     }
    // }

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

trait ContainsKey<K> {
    fn contains_key(&self, key: &K) -> bool;
}

impl<K, V> ContainsKey<K> for Rc<UpperNode<K, V>>
where
    K: Ord,
{
    fn contains_key(&self, key: &K) -> bool {
        let this: &UpperNode<_, _> = self;
        this.contains_key(key)
    }
}

impl<K, V> ContainsKey<K> for Rc<LeafNode<K, V>>
where
    K: Ord,
{
    fn contains_key(&self, key: &K) -> bool {
        let this: &LeafNode<_, _> = self;
        this.get(key).is_some()
    }
}

const TABLE_START: &str = "<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\">";
const TABLE_END: &str = "</TABLE>";

impl<K, V> List<K, V> {
    pub fn output_dot(&self) -> String
    where
        K: std::fmt::Debug,
        V: std::fmt::Debug,
    {
        use std::fmt::Write;
        use Root::*;

        let mut out = String::new();
        writeln!(
            out,
            "digraph {{\n  \
            node [shape=plaintext];\n  \
            rankdir=\"TB\";\n  \
            ranksep=\"0.02\";\n  \
            splines=polyline;\n"
        )
        .unwrap();

        let mut edges = String::new();

        match &self.root {
            Nothing => {}
            Node(node) => node.output_dot(&mut out, &mut edges, &mut HashSet::new()),
            Leaf(leaf) => leaf.output_dot(&mut out, &mut HashSet::new()),
        }

        out.push_str(&edges);

        writeln!(out, "}}").unwrap();

        out
    }
}

impl<K, V> UpperNode<K, V> {
    pub fn output_dot(&self, out: &mut String, edges: &mut String, seen: &mut HashSet<*const ()>)
    where
        K: std::fmt::Debug,
        V: std::fmt::Debug,
    {
        use std::fmt::Write;
        use Pointers::*;
        use UpperValues::*;

        if !seen.insert(self as *const _ as *const ()) {
            return;
        }

        let ptr = self as *const _;
        let height = self.height();

        writeln!(
            out,
            "n{ptr:?} [group=\"h{height}\",label=<\n\
              <TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\">"
        )
        .unwrap();

        writeln!(out, "    <TR><TD>").unwrap();
        for (i, buffered) in self.buffer.iter().enumerate() {
            if i > 0 {
                write!(out, "{}", if i % 5 == 0 { "<BR/>" } else { " " }).unwrap()
            }
            write!(out, "      {buffered:?}").unwrap()
        }
        writeln!(out, "    </TD></TR>").unwrap();

        writeln!(out, "    <TR><TD>").unwrap();
        let mut first = true;
        let (neg_inf, others) = self.mappings();
        let mut i = 0;
        if let Some(child) = neg_inf {
            writeln!(out, "      {TABLE_START}\n        <TR>").unwrap();
            first = false;
            write!(out, "          <TD PORT=\"p{i}\">-∞</TD>").unwrap();
            writeln!(edges, "  n{ptr:?}:p{i}:s -> n{child:?}:n [weight=0.01]").unwrap();
            i += 1;
        }
        for (pivot, child) in others {
            if first {
                writeln!(out, "      {TABLE_START}\n        <TR>").unwrap();
            }
            first = false;
            writeln!(out, "          <TD PORT=\"p{i}\">{pivot:?}</TD>").unwrap();
            writeln!(edges, "  n{ptr:?}:p{i}:s -> n{child:?}:n [weight=0.01]").unwrap();
            i += 1;
        }
        if !first {
            writeln!(out, "        </TR>\n      {TABLE_END}").unwrap();
        }
        writeln!(out, "    </TD></TR>\n  {TABLE_END}\n>]\n").unwrap();

        match &self.values {
            High {
                values: First { children } | Internal { children },
                ..
            } => {
                for child in children {
                    child.output_dot(out, edges, seen)
                }
            }
            Low {
                values: First { children } | Internal { children },
            } => {
                for child in children {
                    child.output_dot(out, seen)
                }
            }
        }
    }

    fn mappings(
        &self,
    ) -> (
        Option<*mut ()>,
        Box<dyn Iterator<Item = (&K, *mut ())> + '_>,
    ) {
        use Pointers::*;
        use UpperValues::*;
        match &self.values {
            High {
                values: First { children },
                ..
            } => {
                if self.pivots.len() != 0 {
                    assert_eq!(self.pivots.len() + 1, children.len());
                }
                let (neg_inf, others) = children
                    .split_first()
                    .map(|(n, o)| (Some(n), o))
                    .unwrap_or((None, &[]));
                let neg_inf = neg_inf.map(|c| Rc::as_ptr(c) as _);
                let ptrs = others.iter().map(|c| Rc::as_ptr(c) as _);
                (neg_inf, Box::new(zip_eq(&self.pivots, ptrs)))
            }
            Low {
                values: First { children },
            } => {
                if self.pivots.len() != 0 {
                    assert_eq!(self.pivots.len() + 1, children.len());
                }
                let (neg_inf, others) = children
                    .split_first()
                    .map(|(n, o)| (Some(n), o))
                    .unwrap_or((None, &[]));
                let neg_inf = neg_inf.map(|c| Rc::as_ptr(c) as _);
                let ptrs = others.iter().map(|c| Rc::as_ptr(c) as _);
                (neg_inf, Box::new(zip_eq(&self.pivots, ptrs)))
            }
            High {
                values: Internal { children },
                ..
            } => {
                assert_eq!(self.pivots.len(), children.len());
                let ptrs = children.iter().map(|c| Rc::as_ptr(c) as _);
                (None, Box::new(zip_eq(&self.pivots, ptrs)))
            }
            Low {
                values: Internal { children },
            } => {
                assert_eq!(self.pivots.len(), children.len());
                let ptrs = children.iter().map(|c| Rc::as_ptr(c) as _);
                (None, Box::new(zip_eq(&self.pivots, ptrs)))
            }
        }
    }
}

impl<K, V> LeafNode<K, V> {
    pub fn output_dot(&self, out: &mut String, seen: &mut HashSet<*const ()>)
    where
        K: std::fmt::Debug,
        V: std::fmt::Debug,
    {
        use std::fmt::Write;
        let ptr = self as *const _;
        let height = 0;

        if !seen.insert(self as *const _ as *const ()) {
            return;
        }

        writeln!(
            out,
            "n{ptr:?} [group=\"h{height}\",label=<\n\
              <TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\">"
        )
        .unwrap();

        let mut first = true;
        for (k, _) in &self.entries {
            if first {
                writeln!(out, "    <TR>").unwrap();
            }
            first = false;
            writeln!(out, "      <TD>{k:?}</TD>").unwrap();
        }
        if !first {
            writeln!(out, "    </TR>").unwrap();
            writeln!(out, "    <TR>").unwrap();
        }
        for (_, v) in &self.entries {
            writeln!(out, "      <TD>{v:?}</TD>").unwrap();
        }
        if !first {
            writeln!(out, "    </TR>").unwrap();
        } else {
            writeln!(out, "    <TR><TD> ∅ </TD></TR>").unwrap();
        }
        writeln!(out, "  {TABLE_END}\n>]\n").unwrap();
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn test() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(199, 0);
        list.insert(19172, 0);
        list.insert(19712, 0);
        list.insert(1677273165, 1667457891);
        list.assert_structure();
    }

    #[test]
    fn test2() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(199, 0);
        list.insert(19712, 0);
        list.insert(19712, 0);
        list.insert(1677273165, 1667457891);
        list.get(&1677273165);
        list.get(&19712);
        list.get(&199);
        list.assert_structure();
    }

    #[test]
    fn test3() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(165, 0);
        list.insert(1970610208, 1970632053);
        list.insert(16777077, 1970631936);
        list.insert(150994944, 1291845632);
        list.assert_structure();
    }

    #[test]
    fn each_leaf_only_itered_once() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(88211655, 0);
        list.assert_structure();
        list.insert(42528, 1293503744);
        list.assert_structure();
        list.insert(1295974400, 16377);
        list.assert_structure();
        list.insert(63821, 16776192);
        list.assert_structure();
        list.insert(1325400064, 1667496232);
        list.assert_structure();
    }

    #[test]
    fn test4() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(199, 2063597691);
        list.assert_structure();
        list.insert(123, 42249);
        list.assert_structure();
        list.insert(19744, 0);
        list.assert_structure();
        list.insert(19744, 0);
        list.assert_structure();
        list.insert(33554176, 1667496232);
        println!("{}", list.output_dot());
        list.assert_structure();
    }

    #[test]
    fn test5() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        print!("a ");
        list.insert(1048699, 2560137368);
        list.assert_structure();
        // println!("{}", list.output_dot());
        print!("b ");
        list.insert(0, 42249);
        list.assert_structure();
        // println!("{}", list.output_dot());
        print!("c ");
        list.insert(16, 1291845632);
        list.assert_structure();
        // println!("{}", list.output_dot());
        print!("d ");
        list.insert(1308164096, 0);
        list.assert_structure();
        // println!("{}", list.output_dot());
        print!("e ");
        list.insert(4180167936, 1667457891);
        list.assert_structure();
        list.insert(1, 1);
        println!("{}", list.output_dot());
        list.insert(2, 2);
        println!("{}", list.output_dot());
    }
}
