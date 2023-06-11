use std::{
    any::Any,
    cell::RefCell,
    collections::{HashMap, VecDeque},
    hash::{Hash, Hasher},
    iter::once,
    mem::replace,
    ops::RangeBounds,
    rc::Rc,
};

use twox_hash::XxHash64;

use rand::{distributions::Bernoulli, prelude::Distribution, rngs::StdRng, SeedableRng};

use itertools::Itertools;

use crate::{
    dense_range_map::{
        map_builder, DenseRangeMap, KeyBuilder, Range, RangeBound, SubEntries, ValueBuilder,
    },
    merge_dedup::{dedup_all_but_last_by, merge_dedup},
};

thread_local! {
    static COUNTERS: Counters = Counters::new();
}

struct Counters(RefCell<CountersInner>);

#[derive(Default)]
struct CountersInner {
    depth: u64,
    new_nodes: usize,
    new_nodes_hist: HashMap<usize, u64>,
    node_sizes: HashMap<usize, u64>,
    total_inserts: u64,
    total_new_nodes: u64,
}

impl Counters {
    fn new() -> Self {
        Self(RefCell::new(CountersInner::default()))
    }

    fn reset(&self) {
        let mut this = self.0.borrow_mut();
        *this = CountersInner::default();
    }

    fn inc_depth(&self) {
        let mut this = self.0.borrow_mut();
        this.depth += 1;
    }

    fn dec_depth(&self) -> u64 {
        let mut this = self.0.borrow_mut();
        this.depth -= 1;
        this.depth
    }

    fn new_node(&self, size: usize) {
        let mut this = self.0.borrow_mut();
        this.new_nodes += 1;
        *this.node_sizes.entry(size).or_insert(0) += 1;
    }

    fn finish_insert(&self) {
        let mut this = self.0.borrow_mut();
        let new = this.new_nodes;
        this.total_new_nodes += new as u64;
        *this.new_nodes_hist.entry(new).or_insert(0) += 1;
        this.new_nodes = 0;
        this.total_inserts += 1;
    }

    fn counts(&self) -> CountersInner {
        let mut this = self.0.borrow_mut();
        replace(&mut *this, CountersInner::default())
    }
}

impl CountersInner {
    fn print(self) {
        let new_nodes = self
            .new_nodes_hist
            .into_iter()
            .sorted_unstable_by_key(|(num, _)| *num)
            .collect_vec();
        println!("new_nodes/insert: {new_nodes:?}");

        let node_sizes = self
            .node_sizes
            .into_iter()
            .sorted_unstable_by_key(|(num, _)| *num)
            .collect_vec();
        println!("sizes/insert: {node_sizes:?}");

        println!(
            "inserts {}, nodes {}",
            self.total_inserts, self.total_new_nodes
        );
        println!(
            "avg {} nodes/insert\navg {} insert/node\n",
            self.total_new_nodes as f64 / self.total_inserts as f64,
            self.total_inserts as f64 / self.total_new_nodes as f64,
        );
    }
}

#[derive(Debug)]
pub struct List<K, V> {
    b: u32,
    distribution: Bernoulli,
    root: Root<K, V>,
    flush_policy: FlushPolicy,
}

#[derive(Debug)]
enum Root<K, V> {
    Nothing,
    Node(Rc<UpperNode<K, V>>),
    Leaf(Rc<LeafNode<K, V>>),
}

impl<K: 'static, V: 'static> Root<K, V> {
    fn to_node(self) -> (Height, Node) {
        use Root::*;
        match self {
            Nothing => unreachable!(),
            Node(upper) => (upper.height, upper as _),
            Leaf(leaf) => (0, leaf as _),
        }
    }
}

type Node = Rc<dyn Any>;

#[derive(Debug)]
struct UpperNode<K, V> {
    height: Height,
    b: u32,
    starts_with_lead: bool,
    flush_policy: FlushPolicy,
    buffer: Vec<Op<K, V>>,
    entries: DenseRangeMap<K, Node>,
}

#[derive(Copy, Clone, Debug)]
pub enum FlushPolicy {
    Everything,
    FirstRun,
}

#[derive(Debug, Clone)]
struct LeafNode<K, V> {
    entries: Vec<(K, V)>,
}

type Height = u8;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Op<K, V> {
    Insert(K, V, Height),
    #[allow(dead_code)]
    Delete(K, Height),
}

#[must_use]
enum GetResult<'a, K, V> {
    Val(Option<&'a V>),
    Upper(&'a UpperNode<K, V>, Range<&'a K>),
    Lower(&'a LeafNode<K, V>),
}

impl<K: 'static, V: 'static> List<K, V>
where
    K: std::fmt::Debug,
    V: std::fmt::Debug,
{
    #[allow(dead_code)]
    fn from_upper(root: impl Into<Root<K, V>>) -> Self {
        Self {
            b: 0,
            distribution: Bernoulli::new(1.0 / (2 as f64).sqrt()).unwrap(),
            root: root.into(),
            flush_policy: FlushPolicy::Everything,
        }
    }

    pub fn new(b: u32) -> Self {
        Self {
            root: Root::Nothing,
            b,
            // TODO allow changing eplison (currently always 0.5)
            distribution: Bernoulli::new(1.0 / (b as f64).sqrt()).unwrap(),
            flush_policy: FlushPolicy::Everything,
        }
    }

    pub fn with_strategy(b: u32, flush_policy: FlushPolicy) -> Self {
        Self {
            root: Root::Nothing,
            b,
            // TODO allow changing eplison (currently always 0.5)
            distribution: Bernoulli::new(1.0 / (b as f64).sqrt()).unwrap(),
            flush_policy,
        }
    }

    pub fn get<'s>(&'s self, k: &K) -> Option<&'s V>
    where
        K: Ord,
    {
        use GetResult::*;
        use Root::*;

        let mut range = Range::everything();

        let mut node = match &self.root {
            Nothing => return None,
            Node(root) => &**root,
            Leaf(leaf) => return leaf.get(k, range),
        };

        loop {
            match node.get(k, range) {
                Val(result) => return result,
                Lower(leaf) => return leaf.get(k, range),
                Upper(n, r) => {
                    node = n;
                    range = r;
                }
            }
        }
    }

    pub fn insert(&mut self, key: K, val: V)
    where
        K: Hash + Ord + Clone,
        V: Clone,
    {
        let height = self.calculate_height(&key);

        self.insert_at_height(height, key, val);
    }

    fn calculate_height(&mut self, key: &K) -> Height
    where
        K: Hash,
    {
        let mut hasher = XxHash64::default();
        key.hash(&mut hasher);
        let hash = hasher.finish();
        let rng = StdRng::seed_from_u64(hash);
        self.distribution
            .sample_iter(rng)
            .take_while(|sample| *sample)
            .count() as Height
    }

    pub fn insert_at_height(&mut self, height: Height, key: K, val: V)
    where
        K: Ord + Clone,
        V: Clone,
    {
        use Op::Insert;
        use Root::*;
        match &mut self.root {
            root @ Nothing => {
                *root = if height > 0 {
                    Node(UpperNode::new_root(
                        self.b,
                        key,
                        val,
                        height,
                        self.flush_policy,
                    ))
                } else {
                    Leaf(LeafNode::new_root(key, val))
                }
            }
            Leaf(leaf) if height == 0 => {
                let this = Rc::get_mut(leaf).unwrap();
                this.insert(key, val)
            }
            Node(upper) if height <= upper.height => {
                let this = Rc::get_mut(upper).unwrap();
                let new_root = this.add_op_to_root(Insert(key, val, height));
                if let Some(root) = new_root {
                    *upper = root
                }
            }
            root => {
                let (old_height, mut old_root) = replace(root, Nothing).to_node();
                if old_height > 0 {
                    let mut r = Rc::downcast::<UpperNode<K, V>>(old_root).unwrap();
                    Rc::get_mut(&mut r).unwrap().canonicalize_buffer();
                    old_root = r;
                }
                let new_root = UpperNode::new_level(
                    self.b,
                    key,
                    val,
                    height,
                    self.flush_policy,
                    (old_height, old_root),
                );
                *root = Node(new_root);
            }
        }
        COUNTERS.with(|c| c.finish_insert());
    }
}

impl<K: 'static, V: 'static> UpperNode<K, V>
where
    K: std::fmt::Debug,
    V: std::fmt::Debug,
{
    fn empty(b: u32, height: Height, flush_policy: FlushPolicy) -> Self {
        Self {
            height,
            b,
            starts_with_lead: false,
            buffer: vec![],
            entries: DenseRangeMap::new(),
            flush_policy,
        }
    }

    fn new_root(b: u32, key: K, val: V, height: Height, flush_policy: FlushPolicy) -> Rc<Self> {
        // COUNTERS.with(|c| c.new_node(1));
        Rc::new(Self {
            height,
            b,
            flush_policy,
            starts_with_lead: false,
            buffer: vec![Op::Insert(key, val, height)],
            entries: DenseRangeMap::new(),
        })
    }

    fn new_level(
        b: u32,
        key: K,
        value: V,
        height: Height,
        flush_policy: FlushPolicy,
        (mut old_height, mut old_root): (Height, Node),
    ) -> Rc<Self> {
        while old_height < height - 1 {
            COUNTERS.with(|c| c.new_node(1));
            old_height += 1;
            old_root = Rc::new(Self {
                height: old_height,
                b,
                flush_policy,
                starts_with_lead: true,
                buffer: vec![],
                entries: (Range::everything(), old_root).into(),
            }) as Node
        }
        // COUNTERS.with(|c| c.new_node(2));
        Rc::new(Self {
            height,
            b,
            flush_policy,
            starts_with_lead: true,
            buffer: vec![Op::Insert(key, value, height)],
            entries: (Range::everything(), old_root).into(),
        })
    }

    fn clone_range(&self, range: Range<&K>) -> Self
    where
        K: Ord + Clone,
        V: Clone,
    {
        Self {
            height: self.height,
            b: self.b,
            flush_policy: self.flush_policy,
            starts_with_lead: true,
            buffer: self.sub_buffer(range).to_vec(),
            entries: self.entries.sub_entries(range).cloned(),
        }
    }

    pub fn get<'s>(&'s self, k: &K, search_range: Range<&'s K>) -> GetResult<'s, K, V>
    where
        K: Ord,
    {
        use std::ops::Bound::{Excluded, Unbounded};
        use GetResult::*;

        debug_assert!(search_range.contains(&k));

        if let Some(result) = self.get_from_buffer(k, search_range) {
            return Val(result);
        }

        let Some((mut range, child)) = self.entries.get_bounded(k, search_range) else {
            return Val(None)
        };

        if self.height == 1 {
            Lower(child.as_leaf())
        } else {
            if let (Unbounded, Excluded(old_end)) = (range.end_bound(), search_range.end_bound()) {
                range.contract_end(RangeBound::Includes(old_end))
            }
            Upper(child.as_upper(), range)
        }
    }

    fn get_from_buffer(&self, k: &K, search_range: Range<&K>) -> Option<Option<&V>>
    where
        K: Ord,
    {
        if search_range.is_everything() {
            // TODO assert is root?
            self.buffer.iter().rfind(|b| b.key() == k).map(Op::value)
        } else {
            // TODO assert is not root?
            let buffer = self.sub_buffer(search_range);
            let idx = buffer.binary_search_by(|op| op.key().cmp(k));
            let Ok(mut idx) = idx else {
                return None
            };
            while idx + 1 < buffer.len() && buffer[idx + 1].key() == k {
                idx += 1
            }

            buffer[idx].value().into()
        }
    }

    fn sub_buffer(&self, search_range: Range<&K>) -> &[Op<K, V>]
    where
        K: Ord,
    {
        let start = self
            .buffer
            .partition_point(|op| *search_range.start() > &op.key());
        let end = self
            .buffer
            .partition_point(|op| *search_range.end() > &op.key());
        let buffer = &self.buffer[start..end];
        buffer
    }

    fn remaining_buffer_space(&self, range: Range<&K>) -> usize
    where
        K: Ord,
    {
        (self.b as usize).saturating_sub(self.slots_used(range))
    }

    fn slots_used(&self, range: Range<&K>) -> usize
    where
        K: Ord,
    {
        if range.is_everything() {
            return self.buffer.len() + self.entries.len();
        }
        self.sub_buffer(range).len() + self.entries.sub_entries(range).len()
    }

    fn add_op_to_root(&mut self, op: Op<K, V>) -> Option<Rc<Self>>
    where
        K: Ord + Clone,
        V: Clone,
    {
        let remaining_buffer_space = self.remaining_buffer_space(Range::everything());

        if remaining_buffer_space >= 1 {
            self.buffer.push(op);
            return None;
        }

        self.canonicalize_buffer();
        // TODO can we elide the VecDeque
        let mut new_nodes = self.flush(Range::everything(), once(op));
        // let mut new_nodes = self.flush(b, empty());

        assert_eq!(new_nodes.len(), 1);
        let new_root = new_nodes.pop_front().unwrap();
        // let mut new_root = new_nodes.pop_front().unwrap();
        // let root = Rc::get_mut(&mut new_root).unwrap();
        // root.extend_buffer_with_ops(once(op));
        Some(new_root)
    }

    fn extend_buffer_with_ops(&mut self, ops: impl Iterator<Item = Op<K, V>>)
    where
        K: Ord,
    {
        self.buffer.extend(ops);
        self.canonicalize_buffer();
        COUNTERS.with(|c| c.new_node(self.slots_used(Range::everything())))
    }

    fn canonicalize_buffer(&mut self)
    where
        K: Ord,
    {
        self.buffer.sort_by(|a, b| a.key().cmp(b.key()));
        dedup_all_but_last_by(&mut self.buffer, |a, b| a.key() == b.key());
    }

    fn flush(
        &self,
        range: Range<&K>,
        additional_ops: impl Iterator<Item = Op<K, V>>,
    ) -> VecDeque<Rc<Self>>
    where
        K: Ord + Clone,
        V: Clone,
    {
        // TODO think long and hard about what flushing the ops immediately
        //      means for durability
        let buffer = self.sub_buffer(range);
        let buffered_ops = buffer
            .iter()
            .coalesce(|a, b| {
                if a.key() == b.key() {
                    Ok(a)
                } else {
                    Err((a, b))
                }
            })
            .cloned();
        let to_flush = merge_dedup(buffered_ops, additional_ops, |a, b| a.key().cmp(b.key()));
        self.apply_ops(range, to_flush)
    }

    fn apply_ops(&self, range: Range<&K>, ops: impl Iterator<Item = Op<K, V>>) -> VecDeque<Rc<Self>>
    where
        K: Ord + Clone,
        V: Clone,
    {
        let (to_flush, to_retain) = self.pick_ops_to_flush(range, ops);
        assert!(!to_flush.is_empty());
        let sub_entries = self.entries.sub_entries(range);

        let mut key_builder = map_builder();

        self.apply_ops_to_pivots(sub_entries, &to_flush, &mut key_builder, range);

        let mut value_builder = key_builder.finish_with(range.end().cloned());

        COUNTERS.with(|c| c.inc_depth());

        if self.height == 1 {
            self.apply_ops_to_leaves(range, sub_entries, to_flush, &mut value_builder);
        } else if sub_entries.is_empty() {
            let temp_child: Self = Self::empty(self.b, self.height - 1, self.flush_policy);
            temp_child.add_ops(range, to_flush.into_iter(), &mut value_builder);
        } else {
            Self::apply_ops_to_children(range, sub_entries, to_flush, &mut value_builder);
        }

        let current_depth = COUNTERS.with(|c| c.dec_depth());

        let mut for_nodes = to_retain.into_iter().peekable();
        value_builder
            .finish()
            .map(|(entries, starts_with_lead)| {
                if current_depth > 0 {
                    COUNTERS.with(|c| c.new_node(entries.len()));
                }
                let range = entries.range();
                let buffer = for_nodes
                    .peeking_take_while(|op| range.contains(&op.key()))
                    .collect();
                Rc::new(Self {
                    height: self.height,
                    b: self.b,
                    flush_policy: self.flush_policy,
                    starts_with_lead,
                    buffer,
                    entries,
                })
            })
            .collect()
    }

    fn pick_ops_to_flush(
        &self,
        range: Range<&K>,
        ops: impl Iterator<Item = Op<K, V>>,
    ) -> (VecDeque<Op<K, V>>, VecDeque<Op<K, V>>)
    where
        K: Ord,
    {
        use FlushPolicy::*;
        match self.flush_policy {
            FirstRun if self.height > 1 => {
                let mut all_ops: VecDeque<_> = ops.collect();
                let num_children = self.entries.sub_entries(range).len();
                let mut allowed_to_remain = (self.b as usize).saturating_sub(num_children);
                let mut ops_iter = all_ops.iter();
                let mut to_flush = ops_iter
                    .peeking_take_while(|op| op.height() < self.height)
                    .count();
                while to_flush < all_ops.len()
                    && (all_ops.len() - to_flush > allowed_to_remain || to_flush == 0)
                {
                    to_flush += 1;
                    allowed_to_remain = allowed_to_remain.saturating_sub(1);
                    _ = ops_iter.next().unwrap();
                    to_flush += ops_iter
                        .peeking_take_while(|op| op.height() < self.height)
                        .count();
                }
                (all_ops.drain(..to_flush).collect(), all_ops)
            }
            _ => (ops.collect(), VecDeque::new()),
        }
    }

    fn apply_ops_to_pivots(
        &self,
        sub_entries: SubEntries<K, Rc<dyn Any>>,
        buffer: &VecDeque<Op<K, V>>,
        key_builder: &mut KeyBuilder<K, bool>,
        range: Range<&K>,
    ) where
        K: Ord + Clone,
    {
        use crate::dense_range_map::RangeBound::{Includes, NegInf};
        use itertools::EitherOrBoth::*;
        use Op::*;

        let pivots_and_ops = sub_entries
            .leads()
            .merge_join_by(buffer.iter(), |k, op| k.cmp(&Includes(op.key())));

        // if this is the first node in a new row we need to have a NegInf key at the front
        // TODO this seems like a pretty bad heuristic, what's a better way to determine this?
        if self.entries.sub_entries(Range::everything()).is_empty() && range.contains_bound(NegInf)
        {
            key_builder.start_new_map_with(NegInf, true);
        }

        let mut seen_first_pivot = false;
        for pop in pivots_and_ops {
            // TODO FIXME if we have an Insert in a range we may need to split it
            if let (false, Left(k) | Both(k, Insert(..))) = (seen_first_pivot, &pop) {
                seen_first_pivot = true;
                // if this is the first pivot in the node then it may be a lead pivot
                if range.contains_bound(*k) && (key_builder.is_empty() || self.starts_with_lead) {
                    key_builder.start_new_map_with(k.cloned(), self.starts_with_lead);
                    continue;
                } else if key_builder.is_empty() {
                    continue; // TODO
                }
            } else if let Right(Insert(k, _, height)) = pop {
                if *height > self.height {
                    key_builder.start_new_map_with(Includes(k.clone()), true);
                    continue;
                } else if key_builder.is_empty() {
                    // TODO double check
                    if *height == self.height {
                        key_builder.start_new_map_with(Includes(k.clone()), false);
                    } else {
                        debug_assert!(matches!(range.start(), NegInf));
                        key_builder.start_new_map_with(NegInf, true);
                        if *height == self.height {
                            key_builder.add_key_to_map(Includes(k.clone()));
                        }
                    }
                    continue;
                }
            }

            let bound = match pop {
                Both(k, Insert(..)) => k.cloned(),
                Left(k) => k.cloned(),
                Right(Insert(k, _, h)) if *h >= self.height => Includes(k.clone()),
                Right(Insert(..)) | Both(_, Delete(..)) | Right(Delete(..)) => continue,
            };
            key_builder.add_key_to_map(bound);
        }
    }

    fn apply_ops_to_leaves(
        &self,
        range: Range<&K>,
        sub_entries: SubEntries<K, Node>,
        buffer: VecDeque<Op<K, V>>,
        value_builder: &mut ValueBuilder<K, Node, bool>,
    ) where
        K: Ord + Clone,
        V: Clone,
    {
        use itertools::EitherOrBoth::*;
        use Op::*;

        let mut entries = sub_entries
            .iter()
            .coalesce(|(ka, va), (kb, vb)| {
                if Rc::ptr_eq(va, vb) {
                    Ok((Range::merge(ka, kb), va))
                } else {
                    Err(((ka, va), (kb, vb)))
                }
            })
            .flat_map(|(child_range, node)| {
                <_ as AsNode<K, V>>::as_leaf(node)
                    .sub_entries(child_range.clamp_to(range))
                    .iter()
            })
            .merge_join_by(buffer, |(k, _), op| k.cmp(op.key()))
            .filter_map(|eop| match eop {
                Both(_, Insert(k, v, ..)) | Right(Insert(k, v, ..)) => Some((k, v)),
                Both(_, Delete(..)) | Right(Delete(..)) => None,
                Left((k, v)) => Some((k.clone(), v.clone())),
            })
            .peekable();

        while let Some(..) = entries.peek() {
            let current_range = value_builder.current_range().unwrap();
            let mut current_entries = entries
                .peeking_take_while(|(k, _)| current_range.contains(&k))
                .collect_vec();

            while let Some(next_range) = value_builder.next_range_in_map() {
                let next_run = entries
                    .peeking_take_while(|(k, _)| next_range.contains(&k))
                    .collect_vec();
                let new_len = current_entries.len() + next_run.len();
                if new_len <= self.b as usize {
                    current_entries.extend(next_run);
                    value_builder.increment_range();
                    continue;
                } else {
                    value_builder.add_value(LeafNode::new(current_entries) as Node);
                    current_entries = next_run;
                }
            }

            COUNTERS.with(|c| c.new_node(current_entries.len()));
            value_builder.add_value(LeafNode::new(current_entries) as Node);
        }

        debug_assert!(entries.peek().is_none());
        debug_assert!(value_builder.current_range().is_none());
    }

    fn add_ops(
        &self,
        range: Range<&K>,
        new_ops: impl ExactSizeIterator<Item = Op<K, V>>,
        value_builder: &mut ValueBuilder<K, Node, bool>,
    ) where
        K: Ord + Clone,
        V: Clone,
    {
        debug_assert!(self.height >= 1);

        let remaining_buffer_space = self.remaining_buffer_space(range);
        if remaining_buffer_space >= new_ops.len() {
            let mut new_node = self.clone_range(range); // FIXME only clone in range
            new_node.extend_buffer_with_ops(new_ops);
            value_builder.add_value_for_range(range, Rc::new(new_node));
            return;
        }
        // println!("{}", self.height);
        let replacement_nodes = self.flush(range, new_ops);
        // println!("{}", Self::out_put_dot_for_iter(&replacement_nodes));
        for node in replacement_nodes {
            // TODO is the clamp needed?
            let node_range = node.entries.range().clamp_to(range);
            // println!("node: {node_range:?}");
            // let node_range = node.entries.range();
            value_builder.add_value_for_range(node_range, node.clone());
        }
        // println!("/{}", self.height);
    }

    fn apply_ops_to_children(
        range: Range<&K>,
        sub_entries: SubEntries<K, Node>,
        mut buffer: VecDeque<Op<K, V>>,
        value_builder: &mut ValueBuilder<K, Node, bool>,
    ) where
        K: Ord + Clone,
        V: Clone,
    {
        let child_ranges = sub_entries.iter().coalesce(|(ka, va), (kb, vb)| {
            if Rc::ptr_eq(va, vb) {
                Ok((Range::merge(ka, kb), va))
            } else {
                Err(((ka, va), (kb, vb)))
            }
        });

        // for (child_range, _) in sub_entries.iter().coalesce(|(ka, va), (kb, vb)| {
        //     if Rc::ptr_eq(va, vb) {
        //         Ok((Range::merge(ka, kb), va))
        //     } else {
        //         Err(((ka, va), (kb, vb)))
        //     }
        // }) {
        //     println!("child: {:?}", child_range.clamp_to(range));
        // }

        for (child_range, child_node) in child_ranges {
            let child_range = child_range.clamp_to(range);
            // let end = buffer.partition_point(|op| *child_range.end() > &op.key());
            let end = buffer.partition_point(|op| child_range.contains(&op.key()));
            if end == 0 {
                value_builder.add_value_for_range(child_range, child_node.clone());
                continue;
            }

            let child = child_node.as_upper();
            child.add_ops(child_range, buffer.drain(..end), value_builder);
        }
    }
}

impl<K, V> LeafNode<K, V> {
    fn new_root(k: K, v: V) -> Rc<Self> {
        // COUNTERS.with(|c| c.new_node(1));
        Self {
            entries: vec![(k, v)],
        }
        .into()
    }

    fn new(entries: Vec<(K, V)>) -> Rc<Self> {
        Self { entries }.into()
    }

    fn assert_structure(&self)
    where
        K: Ord,
    {
        assert!(self.entries.windows(2).all(|w| w[0].0 < w[1].0));
    }

    fn sub_entries(&self, search_range: Range<&K>) -> &[(K, V)]
    where
        K: Ord,
    {
        let start = self
            .entries
            .partition_point(|(k, _)| *search_range.start() > &k);
        let end = self
            .entries
            .partition_point(|(k, _)| *search_range.end() > &k);
        let entries = &self.entries[start..end];
        entries
    }

    fn get(&self, k: &K, search_range: Range<&K>) -> Option<&V>
    where
        K: Ord,
    {
        let sub_entries = self.sub_entries(search_range);
        let Ok(idx) = sub_entries.binary_search_by_key(&k, |(k, _)| k) else {
            return None
        };

        Some(&sub_entries[idx].1)
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

impl<K, V> Op<K, V> {
    fn height(&self) -> Height {
        match self {
            Op::Insert(_, _, h) | Op::Delete(_, h) => *h,
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

trait AsNode<K, V> {
    fn as_upper(&self) -> &UpperNode<K, V>;
    fn as_leaf(&self) -> &LeafNode<K, V>;
}

impl<K: 'static, V: 'static> AsNode<K, V> for Node {
    fn as_upper(&self) -> &UpperNode<K, V> {
        self.downcast_ref::<UpperNode<K, V>>().unwrap()
    }

    fn as_leaf(&self) -> &LeafNode<K, V> {
        self.downcast_ref::<LeafNode<K, V>>().unwrap()
    }
}

const TABLE_START: &str = "<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\">";
const TABLE_END: &str = "</TABLE>";

impl<K, V> List<K, V> {
    pub fn output_simple_dot(&self) -> String
    where
        K: std::fmt::Debug + Ord + 'static,
        V: std::fmt::Debug + 'static,
    {
        self.output_dot_inner(false)
    }

    pub fn output_dot(&self) -> String
    where
        K: std::fmt::Debug + Ord + 'static,
        V: std::fmt::Debug + 'static,
    {
        self.output_dot_inner(true)
    }

    fn output_dot_inner(&self, detailed: bool) -> String
    where
        K: std::fmt::Debug + Ord + 'static,
        V: std::fmt::Debug + 'static,
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
            Node(node) => node.output_dot(&mut out, &mut edges, &mut HashMap::new(), detailed),
            Leaf(leaf) => leaf.output_dot(&mut out, &mut HashMap::new(), detailed),
        }

        out.push_str(&edges);

        writeln!(out, "}}").unwrap();

        out
    }
}

impl<K: 'static, V: 'static> UpperNode<K, V> {
    pub fn out_put_dot_for_iter<'a, P>(iter: impl IntoIterator<Item = &'a P>) -> String
    where
        P: AsRef<Self> + 'static,
        K: std::fmt::Debug + Ord,
        V: std::fmt::Debug,
    {
        use std::fmt::Write;

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
        let mut map = HashMap::new();

        for node in iter {
            node.as_ref()
                .output_dot(&mut out, &mut edges, &mut map, true);
        }

        out.push_str(&edges);

        writeln!(out, "}}").unwrap();

        out
    }

    pub fn output_dot(
        &self,
        out: &mut String,
        edges: &mut String,
        seen: &mut HashMap<*const (), usize>,
        detailed: bool,
    ) where
        K: std::fmt::Debug + Ord,
        V: std::fmt::Debug,
    {
        use std::collections::hash_map::Entry::*;
        use std::fmt::Write;

        let ptr = seen.len();
        let Vacant(entry) = seen.entry(self as *const _ as *const ()) else {
            return
        };
        entry.insert(ptr);

        let height = self.height;

        for (_, child) in self.entries.iter() {
            if self.height == 1 {
                <_ as AsNode<K, V>>::as_leaf(child).output_dot(out, seen, detailed)
            } else {
                <_ as AsNode<K, V>>::as_upper(child).output_dot(out, edges, seen, detailed)
            }
        }

        writeln!(
            out,
            "n{ptr:?} [group=\"h{height}\",label=<\n\
              <TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\">"
        )
        .unwrap();

        writeln!(out, "    <TR><TD>").unwrap();
        if detailed {
            for (i, buffered) in self.buffer.iter().enumerate() {
                if i == 0 {
                    write!(out, "      ").unwrap()
                } else if i > 0 {
                    write!(out, "{}", if i % 5 == 0 { "<BR/> " } else { " " }).unwrap()
                }
                write!(out, "{buffered:?}").unwrap()
            }
        } else {
            write!(out, "      {}", self.buffer.len()).unwrap();
        }
        writeln!(out, "    </TD></TR>").unwrap();

        writeln!(out, "    <TR><TD>").unwrap();
        let mut end_range = None;
        for (i, (range, child)) in self.entries.iter().enumerate() {
            if i == 0 {
                writeln!(out, "      {TABLE_START}\n        <TR>").unwrap();
            }

            let (start, end) = range.inner();
            end_range = Some(end);
            if detailed {
                writeln!(out, "          <TD PORT=\"p{i}\">{start:?}</TD>").unwrap();
            } else {
                writeln!(out, "          <TD PORT=\"p{i}\"> </TD>").unwrap();
            }
            let child = if self.height == 1 {
                <_ as AsNode<K, V>>::as_leaf(child) as *const _ as *const ()
            } else {
                <_ as AsNode<K, V>>::as_upper(child) as *const _ as *const ()
            };
            let child = seen.get(&child).unwrap();
            writeln!(edges, "  n{ptr:?}:p{i}:s -> n{child:?}:n [weight=0.01]").unwrap();
        }
        if let Some(end) = end_range {
            if detailed {
                writeln!(out, "          <TD>{end:?}</TD>").unwrap();
            } else {
                let count = self.entries.len();
                writeln!(out, "          <TD>{count:?}</TD>").unwrap();
            }
            writeln!(out, "        </TR>\n      {TABLE_END}").unwrap();
        }
        writeln!(out, "    </TD></TR>\n  {TABLE_END}\n>]\n").unwrap();
    }

    fn typed_buffer(&self) -> Vec<Op<K, V>> {
        vec![]
    }
}

impl<K, V> LeafNode<K, V> {
    pub fn output_dot(&self, out: &mut String, seen: &mut HashMap<*const (), usize>, detailed: bool)
    where
        K: std::fmt::Debug,
        V: std::fmt::Debug,
    {
        use std::collections::hash_map::Entry::*;
        use std::fmt::Write;
        let height = 0;

        let ptr = seen.len();
        let Vacant(entry) = seen.entry(self as *const _ as *const ()) else {
            return
        };
        entry.insert(ptr);

        writeln!(
            out,
            "n{ptr:?} [group=\"h{height}\",label=<\n\
              <TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\">"
        )
        .unwrap();

        let mut first = true;
        if detailed {
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
        } else {
            writeln!(out, "    <TR><TD> {} </TD></TR>", self.entries.len()).unwrap();
        }
        writeln!(out, "  {TABLE_END}\n>]\n").unwrap();
    }

    fn typed_buffer(&self) -> Vec<Op<K, V>> {
        vec![]
    }
}

fn structural_eq<K, V>(a: &List<K, V>, b: &List<K, V>) -> bool
where
    K: Ord + 'static,
    V: Ord + 'static,
{
    use itertools::EitherOrBoth::Both;
    use Root::*;

    fn leaf_eq<K, V>(a: &LeafNode<K, V>, b: &LeafNode<K, V>) -> bool
    where
        K: Ord,
        V: Ord,
    {
        a.entries == b.entries
    }

    fn upper_eq<K, V>(
        a: &UpperNode<K, V>,
        b: &UpperNode<K, V>,
        canonical_nodes: &mut HashMap<usize, usize>,
    ) -> bool
    where
        K: Ord + 'static,
        V: Ord + 'static,
    {
        if a.height != b.height || a.buffer != b.buffer {
            return false;
        }

        let child_addr = |child: &Rc<dyn Any>| -> usize {
            if a.height == 1 {
                <_ as AsNode<K, V>>::as_leaf(child) as *const _ as usize
            } else {
                <_ as AsNode<K, V>>::as_upper(child) as *const _ as usize
            }
        };

        for pair in a.entries.iter().zip_longest(b.entries.iter()) {
            let Both((a_range, a_child), (b_range, b_child)) = pair else {
                return false
            };
            if a_range != b_range {
                return false;
            }

            let cb = canonical_nodes.get(&child_addr(a_child));
            let ca = canonical_nodes.get(&child_addr(b_child));

            if cb.is_some() && cb != Some(&child_addr(b_child)) {
                return false;
            }

            if ca.is_some() && ca != Some(&child_addr(a_child)) {
                return false;
            }

            let eq = if a.height == 1 {
                leaf_eq::<K, V>(a_child.as_leaf(), b_child.as_leaf())
            } else {
                upper_eq::<K, V>(a_child.as_upper(), b_child.as_upper(), canonical_nodes)
            };

            if !eq {
                return false;
            }

            canonical_nodes.insert(child_addr(a_child), child_addr(b_child));
            canonical_nodes.insert(child_addr(b_child), child_addr(a_child));
        }

        true
    }

    let mut canonical_nodes = HashMap::new();
    match (&a.root, &b.root) {
        (Nothing, Nothing) => true,
        (Leaf(a), Leaf(b)) => leaf_eq(a, b),
        (Node(a), Node(b)) => upper_eq(a, b, &mut canonical_nodes),
        _ => false,
    }
}

impl<K, V> From<Rc<UpperNode<K, V>>> for Root<K, V> {
    fn from(value: Rc<UpperNode<K, V>>) -> Self {
        Root::Node(value)
    }
}

impl<K, V> From<Rc<LeafNode<K, V>>> for Root<K, V> {
    fn from(value: Rc<LeafNode<K, V>>) -> Self {
        Root::Leaf(value)
    }
}

#[cfg(test)]
mod test {
    use crate::dense_range_map::Range;

    // use RangeBound::{NegInf, PosInf};

    use super::{LeafNode, COUNTERS};

    // macro_rules! Leaf {
    //     ($($key:expr => $val:expr),* $(,)?) => {
    //         std::rc::Rc::new(LeafNode {
    //             entries: vec![$(($key, $val)),*],
    //         })
    //     };
    // }

    // macro_rules! Upper {
    //     ($height:expr; $first_key:expr $(, $val:expr, $key:expr)+  ) => {
    //         {
    //             use std::rc::Rc;
    //             use std::any::Any;

    //             let mut key_builder = crate::dense_range_map::map_builder();
    //             key_builder.start_new_map_with(RangeBound::from($first_key), ());
    //             $(key_builder.add_key_to_map(RangeBound::from($key));)+
    //             let mut val_builder = key_builder.finish();
    //             $(val_builder.add_value(Rc::clone(&$val) as Rc<dyn Any>);)+
    //             let mut maps = val_builder.finish();
    //             let (entries, _) = maps.next().unwrap();
    //             assert!(maps.next().is_none());
    //             Rc::new(super::UpperNode {
    //                 b: 0,
    //                 height: $height,
    //                 starts_with_lead: false,
    //                 buffer: {
    //                     #[allow(unused_mut)]
    //                     let mut buffer;
    //                     $( _ = buffer; buffer = $val.typed_buffer(); )+
    //                     buffer
    //                 },
    //                 entries,
    //             })
    //         }
    //     };
    // }

    #[test]
    fn leaf_sub_entries() {
        let leaf = LeafNode {
            entries: vec![(0, 0), (1, 1), (2, 2), (100, 100), (2000, 2000)],
        };
        assert_eq!(
            leaf.sub_entries(Range::everything()),
            [(0, 0), (1, 1), (2, 2), (100, 100), (2000, 2000)]
        );

        assert_eq!(
            leaf.sub_entries((&0, &2001).into()),
            [(0, 0), (1, 1), (2, 2), (100, 100), (2000, 2000)]
        );

        assert_eq!(
            leaf.sub_entries((&0, &2000).into()),
            [(0, 0), (1, 1), (2, 2), (100, 100)]
        );

        assert_eq!(
            leaf.sub_entries((&0, &150).into()),
            [(0, 0), (1, 1), (2, 2), (100, 100)]
        );

        assert_eq!(
            leaf.sub_entries((&0, &100).into()),
            [(0, 0), (1, 1), (2, 2)]
        );

        assert_eq!(
            leaf.sub_entries((&1, &2001).into()),
            [(1, 1), (2, 2), (100, 100), (2000, 2000)]
        );

        assert_eq!(
            leaf.sub_entries((&2, &2001).into()),
            [(2, 2), (100, 100), (2000, 2000)]
        );

        assert_eq!(leaf.sub_entries((&2, &150).into()), [(2, 2), (100, 100)]);
    }

    #[test]
    fn leaf_eq() {
        // let a = LeafNode {
        //     entries: vec![(0, 0), (1, 1), (2, 2), (100, 100), (2000, 2000)],
        // };
        // assert!(structural_eq(&a, &a));

        // let b = LeafNode {
        //     entries: vec![(0, 0), (1, 1), (2, 2), (100, 100), (2000, 2000)],
        // };
        // assert!(structural_eq(&a, &b));

        // let c = LeafNode {
        //     entries: vec![(0, 0), (1, 1), (2, 2), (100, 100)],
        // };
        // assert!(!structural_eq(&a, &c));
    }

    #[test]
    fn insert_at_leaves() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        assert_eq!(list.get(&0), None);
        assert_eq!(list.get(&1), None);
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), None);
        assert_eq!(list.get(&100), None);

        list.insert_at_height(0, 0, 6);
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), None);
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), None);
        assert_eq!(list.get(&100), None);

        list.insert_at_height(0, 1, 1);
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), Some(&1));
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), None);
        assert_eq!(list.get(&100), None);

        list.insert_at_height(0, 7, 71);
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), Some(&1));
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), Some(&71));
        assert_eq!(list.get(&100), None);

        list.insert_at_height(0, 3, 13);
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), Some(&1));
        assert_eq!(list.get(&3), Some(&13));
        assert_eq!(list.get(&7), Some(&71));
        assert_eq!(list.get(&100), None);
        insta::assert_snapshot!(list.output_dot());
    }

    #[test]
    fn flush_to_leaves() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        // println!("{}", list.output_dot());
        assert_eq!(list.get(&0), None);
        assert_eq!(list.get(&1), None);
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), None);
        assert_eq!(list.get(&100), None);

        list.insert_at_height(1, 0, 6);
        // println!("{}", list.output_dot());
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), None);
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), None);
        assert_eq!(list.get(&100), None);

        list.insert_at_height(1, 1, 1);
        // println!("{}", list.output_dot());
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), Some(&1));
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), None);
        assert_eq!(list.get(&100), None);

        list.insert_at_height(1, 7, 71);
        // println!("{}", list.output_dot());
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), Some(&1));
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), Some(&71));
        assert_eq!(list.get(&100), None);

        list.insert_at_height(1, 3, 13);
        // println!("{}", list.output_dot());
        insta::assert_snapshot!(list.output_dot());
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), Some(&1));
        assert_eq!(list.get(&3), Some(&13));
        assert_eq!(list.get(&7), Some(&71));
        assert_eq!(list.get(&100), None);
    }

    #[test]
    fn flush_to_upper() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        // println!("{}", list.output_dot());
        assert_eq!(list.get(&0), None);
        assert_eq!(list.get(&1), None);
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), None);
        assert_eq!(list.get(&100), None);

        list.insert_at_height(2, 0, 6);
        // println!("{}", list.output_dot());
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), None);
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), None);
        assert_eq!(list.get(&100), None);

        list.insert_at_height(2, 1, 1);
        // println!("{}", list.output_dot());
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), Some(&1));
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), None);
        assert_eq!(list.get(&100), None);

        list.insert_at_height(2, 7, 71);
        // println!("{}", list.output_dot());
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), Some(&1));
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), Some(&71));
        assert_eq!(list.get(&100), None);

        list.insert_at_height(2, 3, 13);
        // println!("{}", list.output_dot());
        insta::assert_snapshot!(list.output_dot());
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), Some(&1));
        assert_eq!(list.get(&3), Some(&13));
        assert_eq!(list.get(&7), Some(&71));
        assert_eq!(list.get(&100), None);
    }

    #[test]
    fn flush_to_gap() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        // println!("{}", list.output_dot());
        assert_eq!(list.get(&0), None);
        assert_eq!(list.get(&1), None);
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), None);
        assert_eq!(list.get(&100), None);

        list.insert_at_height(1, 0, 6);
        // println!("{}", list.output_dot());
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), None);
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), None);
        assert_eq!(list.get(&100), None);

        list.insert_at_height(3, 1, 1);
        // println!("{}", list.output_dot());
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), Some(&1));
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), None);
        assert_eq!(list.get(&100), None);

        list.insert_at_height(3, 7, 71);
        // println!("{}", list.output_dot());
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), Some(&1));
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), Some(&71));
        assert_eq!(list.get(&100), None);

        list.insert_at_height(3, 3, 13);
        // println!("{}", list.output_dot());
        insta::assert_snapshot!(list.output_dot());

        // assert_eq!(list.get(&0), Some(&6));
        // assert_eq!(list.get(&1), Some(&1));
        // assert_eq!(list.get(&3), Some(&13));
        // assert_eq!(list.get(&7), Some(&71));
        // assert_eq!(list.get(&100), None);

        // let leaf0 = Leaf!(0 => 6);
        // let upper1_0 = Upper!(1; 0, leaf0, 1);
        // let upper2_n = Upper!(2; NegInf, upper1_0, 1);

        // let leaf1 = Leaf!(1 => 1);
        // let upper1_1 = Upper!(1; 1, leaf1, 3);
        // let upper2_1 = Upper!(2; 1, upper1_1, 3);

        // let leaf3 = Leaf!(3 => 13);
        // let upper1_3 = Upper!(1; 3, leaf3, 7);
        // let upper2_3 = Upper!(2; 3, upper1_3, 7);

        // let leaf7 = Leaf!(7 => 71);
        // let upper1_7 = Upper!(1; 7, leaf7, PosInf);
        // let upper2_7 = Upper!(2; 7, upper1_7, PosInf);

        // let root = Upper!(3; NegInf, upper2_n, 1, upper2_1, 3, upper2_3, 7, upper2_7, PosInf);
        // let expected = super::List::from_upper(root);
        // assert!(
        //     structural_eq(&list, &expected),
        //     "{}\n{}",
        //     list.output_dot(),
        //     expected.output_dot()
        // );
    }

    #[test]
    fn leaf_with_neg_inf() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        // println!("{}", list.output_dot());
        assert_eq!(list.get(&0), None);
        assert_eq!(list.get(&1), None);
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), None);
        assert_eq!(list.get(&100), None);

        list.insert_at_height(1, 7, 71);
        assert_eq!(list.get(&0), None);
        assert_eq!(list.get(&1), None);
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), Some(&71));
        assert_eq!(list.get(&100), None);

        list.insert_at_height(0, 0, 6);
        // println!("{}", list.output_dot());
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), None);
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), Some(&71));
        assert_eq!(list.get(&100), None);

        list.insert_at_height(0, 1, 1);
        // println!("{}", list.output_dot());
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), Some(&1));
        assert_eq!(list.get(&3), None);
        assert_eq!(list.get(&7), Some(&71));
        assert_eq!(list.get(&100), None);

        list.insert_at_height(0, 3, 13);
        insta::assert_snapshot!(list.output_dot());
        // println!("{}", list.output_dot());
        assert_eq!(list.get(&0), Some(&6));
        assert_eq!(list.get(&1), Some(&1));
        assert_eq!(list.get(&3), Some(&13));
        assert_eq!(list.get(&7), Some(&71));
        assert_eq!(list.get(&100), None);
    }

    #[test]
    fn fuzz_repro1() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(0, 1509949530);
        assert_eq!(list.get(&0), Some(&1509949530));
        list.insert(0, 16777216);
        assert_eq!(list.get(&0), Some(&16777216));
        list.insert(10246746, 0);
        assert_eq!(list.get(&10246746), Some(&0));
        list.insert(1, 1515847770);
        // println!("{}", list.output_dot());
        insta::assert_snapshot!(list.output_dot());
        assert_eq!(list.get(&1), Some(&1515847770));
        assert_eq!(list.get(&0), Some(&16777216));
        assert_eq!(list.get(&10246746), Some(&0));
    }

    // TODO this case seems less than ideal, but I don't know if it can be
    // eliminated
    #[test]
    fn fuzz_repro2() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(8192, 1509949530);
        list.insert(0, 90);
        list.insert(2354731520, 0);
        // println!("{}", list.output_dot());
        list.insert(256, 12288);
        // println!("{}", list.output_dot());
        insta::assert_snapshot!(list.output_dot());
    }

    #[test]
    fn fuzz_repro3() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(4294967071, 4294967295);
        list.insert(0, 741092864);
        list.insert(0, 1509949440);
        list.insert(741223468, 741092396);
        // println!("{}", list.output_dot());
        assert_eq!(list.get(&4294967071), Some(&4294967295));
        insta::assert_snapshot!(list.output_dot());
    }

    #[test]
    fn add_neg_inf_to_l1_root() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(3145818, 23040);
        list.insert(1518339839, 3473564);
        list.insert(4294967295, 1512528639);
        list.insert(9198170, 0);
        list.insert(1, 5900341);
        insta::assert_snapshot!(list.output_dot());
    }

    #[test]
    fn old_roots_get_sorted() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(2122219057, 12670);
        list.insert(875836468, 369112372);
        list.insert(830373502, 4281401344);
        list.insert(9686330, 4294967289);
        list.insert(557990526, 656877402);
        assert_eq!(list.get(&875836468), Some(&369112372));
        insta::assert_snapshot!(list.output_dot());
    }

    #[test]
    fn old_roots_get_deduped() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(0, 0);
        list.insert(0, 1107296256);
        list.insert(1111638594, 52);
        list.insert(5632, 4294508593);
        list.insert(2122219134, 16962);
        insta::assert_snapshot!(list.output_dot());
        assert_eq!(list.get(&0), Some(&1107296256));
    }

    #[test]
    fn use_precise_leads() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(1515847713, 1048576);
        list.insert(10246656, 1245184);
        list.insert(1509949441, 10246746);
        list.insert(4244581665, 0);
        list.insert(4294967295, 4294967295);
        insta::assert_snapshot!(list.output_dot());
    }

    #[test]
    fn index_subentries_in_leaf_search() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(2565275692, 1509960833);
        assert_eq!(list.get(&2565275692), Some(&1509960833));
        list.insert(59, 1817837568);
        assert_eq!(list.get(&2565275692), Some(&1509960833));
        list.insert(168034394, 945460521);
        assert_eq!(list.get(&2565275692), Some(&1509960833));
        list.insert(4279185920, 65535);
        assert_eq!(list.get(&2565275692), Some(&1509960833));
        list.insert(805329408, 741684533);
        insta::assert_snapshot!(list.output_dot());
        assert_eq!(list.get(&2565275692), Some(&1509960833));
    }

    #[test]
    fn new_neginfs_propogate() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(1229539659, 1229539657);
        list.insert(1263094016, 1229539657);
        list.insert(1516849481, 27738);
        list.insert(1230690906, 7101018);
        list.insert(5954138, 5910528);
        assert_eq!(list.get(&5954138), Some(&5910528));
        insta::assert_snapshot!(list.output_dot());
    }

    #[test]
    fn all_levels_start_with_neginf() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(6488064, 825307445);
        list.insert(890384433, 892679477);
        list.insert(2139062143, 2139062143);
        list.insert(2139062143, 2139062143);
        list.insert(8192, 134217728);
        list.insert(905262389, 892679477);
        insta::assert_snapshot!(list.output_dot());
    }

    #[test]
    fn cloned_nodes_dedup_buffer() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(16843009, 16843009);
        list.insert(16843009, 1431655937);
        list.insert(16843009, 1431655765);
        list.insert(1442906369, 1431655765);
        list.insert(16843009, 16843009);
        list.insert(16843248, 1509987073);
        assert_eq!(list.get(&16843009), Some(&16843009));
        insta::assert_snapshot!(list.output_dot());
    }

    #[test]
    fn child_flushes_stay_in_range() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(3419130826, 3420980);
        list.insert(0, 0);
        list.insert(0, 0);
        list.insert(0, 0);
        list.insert(0, 873381631);
        list.insert(3170893824, 1111638594);
        list.insert(876757570, 52);
        list.insert(3242345026, 4342324);
        insta::assert_snapshot!(list.output_dot());
    }

    #[test]
    fn only_add_neginf_to_first_logical_node() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(3419130156, 559546571);
        list.insert(0, 0);
        list.insert(0, 0);
        list.insert(1094795585, 1094795585);
        list.insert(1094795585, 4276545);
        list.insert(4, 0);
        list.insert(0, 0);
        list.insert(0, 1515847680);
        insta::assert_snapshot!(list.output_dot());
    }

    #[test]
    fn obey_logical_leaves_when_balancing() {
        let mut list: super::List<u32, u32> = super::List::new(3);
        list.insert(2122219060, 0);
        list.insert(0, 0);
        list.insert(0, 0);
        list.insert(1073741824, 4278202368);
        list.insert(0, 0);
        list.insert(656894976, 23895898);
        list.insert(11520, 16748800);
        list.insert(0, 0);
        list.insert(0, 805322752);
        insta::assert_snapshot!(list.output_dot());
    }

    #[test]
    fn flush_first() {
        let mut list: super::List<u32, u32> =
            super::List::with_strategy(3, super::FlushPolicy::FirstRun);
        list.insert(1599564650, 1600085855);
        list.insert(1600085855, 30464);
        list.insert(8388608, 16);
        list.insert(5729111, 1086879488);
        insta::assert_snapshot!(list.output_dot());
    }

    #[test]
    fn flush_leaves() {
        let mut list: super::List<u32, u32> =
            super::List::with_strategy(3, super::FlushPolicy::FirstRun);
        list.insert(1869573999, 1869573999);
        list.insert(0, 0);
        list.insert(1862270976, 1869573999);
        list.insert(1869573999, 249786223);
        println!("{}", list.output_dot());
        insta::assert_snapshot!(list.output_dot());
    }

    #[test]
    fn flush_more() {
        let mut list: super::List<u32, u32> =
            super::List::with_strategy(3, super::FlushPolicy::FirstRun);
        list.insert(503316480, 2049755281);
        list.insert(0, 2439217152);
        list.insert(318782058, 1785366528);
        list.insert(286331153, 286331153);
        list.insert(286331153, 286331153);
        list.insert(286331153, 286331153);
        list.insert(286331153, 1785358954);
        println!("{}", list.output_dot());
        list.insert(2290186071, 2439670479);
        println!("{}", list.output_dot());
        insta::assert_snapshot!(list.output_dot());
    }

    #[test]
    fn random_inserts_128() {
        COUNTERS.with(|c| c.reset());
        let mut list: super::List<u64, u64> = super::List::new(128);
        for _ in 0..1_000_000 {
            list.insert(rand::random(), rand::random());
        }
        let counts = COUNTERS.with(|c| c.counts());
        counts.print();
    }

    #[test]
    fn ordered_inserts_128() {
        COUNTERS.with(|c| c.reset());
        let mut list: super::List<u64, u64> = super::List::new(128);
        for i in 0..1_000_000 {
            list.insert(i, rand::random());
        }
        let counts = COUNTERS.with(|c| c.counts());
        counts.print();
    }

    #[test]
    fn random_inserts_1024() {
        COUNTERS.with(|c| c.reset());
        let mut list: super::List<u64, u64> = super::List::new(1024);
        for _ in 0..10_000_000 {
            list.insert(rand::random(), rand::random());
        }
        let counts = COUNTERS.with(|c| c.counts());
        counts.print();
    }

    #[test]
    fn random_inserts_1000() {
        COUNTERS.with(|c| c.reset());
        let mut list: super::List<u64, u64> = super::List::new(1000);
        for _ in 0..10_000_000 {
            list.insert(rand::random(), rand::random());
        }
        let counts = COUNTERS.with(|c| c.counts());
        counts.print();
    }

    #[test]
    fn random_inserts_1500() {
        COUNTERS.with(|c| c.reset());
        let mut list: super::List<u64, u64> = super::List::new(1500);
        for _ in 0..10_000_000 {
            list.insert(rand::random(), rand::random());
        }
        let counts = COUNTERS.with(|c| c.counts());
        counts.print();
    }

    #[test]
    fn random_inserts_10000() {
        COUNTERS.with(|c| c.reset());
        let mut list: super::List<u64, u64> = super::List::new(10000);
        for _ in 0..10_000_000 {
            list.insert(rand::random(), rand::random());
        }
        let counts = COUNTERS.with(|c| c.counts());
        counts.print();
    }

    #[test]
    fn ordered_inserts_1024() {
        COUNTERS.with(|c| c.reset());
        let mut list: super::List<u64, u64> = super::List::new(1024);
        for i in 0..10_000_000 {
            list.insert(i, rand::random());
        }
        let counts = COUNTERS.with(|c| c.counts());
        counts.print();
    }

    #[test]
    fn ordered_inserts_1000() {
        COUNTERS.with(|c| c.reset());
        let mut list: super::List<u64, u64> = super::List::new(1000);
        for i in 0..10_000_000 {
            list.insert(i, rand::random());
        }
        let counts = COUNTERS.with(|c| c.counts());
        counts.print();
    }

    #[test]
    fn ordered_inserts_10000() {
        COUNTERS.with(|c| c.reset());
        let mut list: super::List<u64, u64> = super::List::new(10_000);
        for i in 0..10_000_000 {
            list.insert(i, rand::random());
        }
        let counts = COUNTERS.with(|c| c.counts());
        counts.print();
    }

    #[test]
    fn random_inserts_flush_first_1024() {
        COUNTERS.with(|c| c.reset());
        let mut list: super::List<u64, u64> =
            super::List::with_strategy(1024, super::FlushPolicy::FirstRun);
        for _ in 0..10_000_000 {
            list.insert(rand::random(), rand::random());
        }
        let counts = COUNTERS.with(|c| c.counts());
        counts.print();
    }

    #[test]
    fn ordered_inserts_flush_first_1024() {
        COUNTERS.with(|c| c.reset());
        let mut list: super::List<u64, u64> =
            super::List::with_strategy(1024, super::FlushPolicy::FirstRun);
        for i in 0..10_000_000 {
            list.insert(i, rand::random());
        }
        let counts = COUNTERS.with(|c| c.counts());
        counts.print();
    }

    // #[test]
    // fn small_random_inserts() {
    //     COUNTERS.with(|c| c.reset());
    //     let mut list: super::List<u64, u64> = super::List::new(64);
    //     for _ in 0..3_000 {
    //         list.insert(rand::random(), rand::random());
    //     }
    //     let counts = COUNTERS.with(|c| c.counts());
    //     // counts.print();
    //     println!("{}", list.output_simple_dot());
    // }

    // #[test]
    // fn small_ordered_inserts() {
    //     COUNTERS.with(|c| c.reset());
    //     let mut list: super::List<u64, u64> = super::List::new(64);
    //     for i in 0..3_000 {
    //         list.insert(i, rand::random());
    //     }
    //     let counts = COUNTERS.with(|c| c.counts());
    //     // counts.print();
    //     println!("{}", list.output_simple_dot());
    // }
}
