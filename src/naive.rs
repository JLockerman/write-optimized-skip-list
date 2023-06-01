use std::{
    cell::{self, RefCell},
    cmp::min,
    collections::{HashMap, VecDeque},
    fmt::{Debug, Write},
    hash::{Hash, Hasher},
    iter::once,
    mem::take,
    ops::{Deref, DerefMut},
    rc::{Rc, Weak},
    slice, vec,
};

use twox_hash::XxHash64;

// 1 - e = 2e
// 1 = 3e
// e = 1 / 3
pub struct List<K, V> {
    meta: Metadata<K, V>,
}

#[derive(Debug)]
struct Metadata<K, V> {
    mapping: HashMap<(K, Height), Ptr<Node<K, V>>>,
    first_nodes: Vec<Ptr<Node<K, V>>>,
    b: u32,
}

type Ptr<T> = Rc<RefCell<T>>;
type Height = u8;

struct Node<K, V> {
    height: Height,
    pivots: Vec<K>,
    values: Vec<V>,
    buffer: Vec<Op<K, V>>,

    this: Weak<RefCell<Self>>,
    prev: Option<Ptr<Node<K, V>>>,
    next: Option<Ptr<Node<K, V>>>,
}

#[derive(Debug)]
enum Op<K, V> {
    Insert(K, V, Height),
    Delete(K, Height),
}

impl<K, V> List<K, V> {
    pub fn new(b: u32) -> Self {
        Self {
            meta: Metadata {
                mapping: HashMap::new(),
                first_nodes: Vec::new(),
                b,
            },
        }
    }

    pub fn get<'s>(&'s self, k: &K) -> Option<&'s V>
    where
        K: Hash + Ord + Clone,
    {
        let root = self.meta.first_nodes.last().cloned();
        let Some(root) = root else {
            return None
        };

        let root = root.borrow();
        root.get(k, &self.meta)
    }

    pub fn insert(&mut self, k: K, v: V)
    where
        K: Hash + Ord + Clone,
        V: Clone,
    {
        let mut hasher = XxHash64::default();
        k.hash(&mut hasher);
        let hash = hasher.finish();
        let height = hash.leading_ones() as u8;
        let root_height = self.meta.first_nodes.len().saturating_sub(1);
        if self.meta.first_nodes.is_empty() || root_height < height as usize {
            self.meta.alloc_first(height);
        }
        let root = self.meta.first_nodes.last().cloned().unwrap();
        let mut root = RefCell::borrow_mut(&*root);
        root.insert(k, v, height, &mut self.meta);
    }

    #[allow(dead_code)]
    fn output_dot(&self) -> String
    where
        K: Hash + Eq + Clone + Debug,
        V: Debug,
    {
        let mut out = String::new();
        writeln!(
            out,
            "digraph {{\n  \
            node [shape=plaintext];\n  \
            rankdir=\"LR\";\n  \
            ranksep=\"0.02\";\n  \
            splines=polyline;\n"
        )
        .unwrap();

        let mut edges = String::new();

        let table_start = "<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\">";
        let table_end = "</TABLE>";

        let max_height = self.meta.first_nodes.len().saturating_sub(1);
        for (height, list) in self.meta.first_nodes.iter().enumerate().rev() {
            writeln!(
                out,
                "  subgraph cluster_{height} {{\n    \
                label = \"height {height}\";"
            )
            .unwrap();

            writeln!(
                out,
                "start_{height} [group=\"h{height}\",label=<\n\
                {table_start}\n\
                <TR><TD>{table_start}\n    \
                    <TR>\n    \
                    <TD PORT=\"next\">start</TD>\n    \
                    </TR>\n  \
                {table_end}</TD></TR>\
                <TR><TD PORT=\"p\"></TD></TR>\
                {table_end}>]\n"
            )
            .unwrap();

            if height < max_height {
                let parent_height = height + 1;
                writeln!(
                    &mut edges,
                    "  start_{parent_height}:p:s -> start_{height}:n [constraint=false]"
                )
                .unwrap();
            }

            let mut node = list.clone();
            loop {
                let borrow = node.borrow();
                let ptr = borrow.this.as_ptr();
                writeln!(
                    out,
                    "n{ptr:?} [group=\"h{height}\",label=<\n\
                    <TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\">\n\
                <TR><TD>{table_start}\n      \
                    <TR><TD PORT=\"prev\">prev</TD><TD PORT=\"next\">next</TD></TR>\
                {table_end}</TD></TR>\n"
                )
                .unwrap();
                writeln!(out, "<TR><TD>").unwrap();
                for (i, buffered) in borrow.buffer.iter().enumerate() {
                    if i > 0 {
                        write!(out, "{}", if i % 5 == 0 { "<BR/>" } else { " " }).unwrap()
                    }
                    write!(out, "{buffered:?}").unwrap()
                }
                writeln!(out, "</TD></TR>").unwrap();
                match &borrow.prev {
                    None => {
                        if height < max_height {
                            let parent = height + 1;
                            writeln!(
                                &mut edges,
                                "  start_{parent}:next:e -> n{ptr:?} [style=invis]"
                            )
                            .unwrap();
                        }
                        writeln!(&mut edges, "  start_{height}:next:e -> n{ptr:?}:prev:w").unwrap();
                        writeln!(
                            &mut edges,
                            "  n{ptr:?}:prev:w -> start_{height}:next:e [constraint=false]"
                        )
                        .unwrap()
                    }
                    Some(prev) => {
                        let prev = Rc::as_ptr(prev);
                        writeln!(
                            &mut edges,
                            "  n{ptr:?}:prev:w -> n{prev:?}:next:e [constraint=false]"
                        )
                        .unwrap()
                    }
                }
                writeln!(out, "<TR><TD>").unwrap();
                let mut first = true;
                for (i, pivot) in borrow.pivots.iter().enumerate() {
                    if first {
                        writeln!(out, "{table_start}\n    <TR>").unwrap();
                    }
                    first = false;
                    write!(out, "<TD PORT=\"p{i}\">{pivot:?}</TD>").unwrap();
                    if borrow.height > 0 {
                        let child = self
                            .meta
                            .mapping
                            .get(&(pivot.clone(), borrow.height - 1))
                            .map(Rc::as_ptr)
                            .unwrap_or(std::ptr::null());
                        writeln!(
                            &mut edges,
                            "  n{ptr:?}:p{i}:s -> n{child:?}:n [weight=0.01]"
                        )
                        .unwrap();
                    }
                }
                if let Some(next) = &borrow.next {
                    let next = Rc::as_ptr(next);
                    writeln!(&mut edges, "  n{ptr:?}:next:e -> n{next:?}:prev:w").unwrap()
                }
                if !first {
                    writeln!(out, "</TR>").unwrap();
                    if !borrow.values.is_empty() {
                        write!(out, "<TR>").unwrap();
                        for value in &borrow.values {
                            write!(out, "<TD>{value:?}</TD>").unwrap()
                        }
                        write!(out, "</TR>").unwrap();
                    }
                    writeln!(out, "{table_end}").unwrap();
                }

                writeln!(out, "</TD></TR>{table_end}>]\n").unwrap();
                match borrow.next.as_ref().cloned() {
                    None => break,
                    Some(next) => {
                        drop(borrow);
                        node = next
                    }
                }
            }
            writeln!(out, "}}").unwrap();
        }

        out.push_str(&edges);

        writeln!(out, "}}").unwrap();

        out
    }

    #[allow(dead_code)]
    pub fn assert_structure(&self)
    where
        K: Hash + Ord + Clone,
    {
        for (height, list) in self.meta.first_nodes.iter().enumerate().rev() {
            let mut node = list.clone();
            let mut prev_child = None;
            let mut prev_child_ptr =
                (height > 0).then(|| self.meta.first_nodes[height - 1].clone());
            loop {
                let borrow = node.borrow();

                match &borrow.prev {
                    None => assert!(Rc::ptr_eq(&self.meta.first_nodes[height], &node)),
                    Some(prev) => {
                        let prev = prev.borrow();
                        assert!(Rc::ptr_eq(prev.next.as_ref().unwrap(), &node))
                    }
                }

                assert!(borrow.pivots.windows(2).all(|w| w[0] <= w[1]));

                for pivot in borrow.pivots.iter() {
                    if borrow.height > 0 {
                        let child_node = self
                            .meta
                            .mapping
                            .get(&(pivot.clone(), borrow.height - 1))
                            .unwrap();
                        if let Some(prev_child_ptr) = prev_child_ptr {
                            if !Rc::ptr_eq(child_node, &prev_child_ptr) {
                                prev_child = Some(prev_child_ptr)
                            }
                        }

                        let child = child_node.borrow();
                        assert_eq!(child.height, borrow.height - 1);
                        match &prev_child {
                            None => assert!(child.prev.is_none()),
                            Some(prev_child) => {
                                assert!(child.prev.is_some());
                                assert!(Rc::ptr_eq(child.prev.as_ref().unwrap(), prev_child));
                            }
                        }

                        prev_child_ptr = Some(child_node.clone());
                    }
                }

                if let Some(next) = &borrow.next {
                    let next = next.borrow();
                    assert!(Rc::ptr_eq(next.prev.as_ref().unwrap(), &node));
                    assert!(next.pivots.first() > borrow.pivots.last());
                }

                if !borrow.values.is_empty() {
                    assert!(borrow.height == 0);
                    assert_eq!(borrow.values.len(), borrow.pivots.len())
                }
                match borrow.next.as_ref().cloned() {
                    None => break,
                    Some(next) => {
                        drop(borrow);
                        node = next
                    }
                }
            }
        }
    }
}

impl<K, V> Node<K, V> {
    fn ptr(height: Height) -> Ptr<Self> {
        Rc::new_cyclic(|w| RefCell::new(Self::new(height, w.clone())))
    }

    fn new(height: Height, this: Weak<RefCell<Self>>) -> Self {
        Self {
            height,
            pivots: vec![],
            values: vec![],
            buffer: vec![],

            this,
            next: None,
            prev: None,
        }
    }

    fn get<'s>(&self, k: &K, mapper: &'s Metadata<K, V>) -> Option<&'s V>
    where
        K: Hash + Ord + Clone,
    {
        use Op::*;

        let b = self.buffer.iter().rfind(|&b| b == k);
        match b {
            Some(Insert(_, v, ..)) => {
                // SAFETY mapper serves as a sentinel that we're not going to mutate
                //        the structure of the DAG until the borrow ends
                let v = unsafe { mapper.extend_lifetime(v) };
                return Some(v);
            }
            Some(Delete(..)) => return None,
            None => (),
        }

        let res = self.pivots.binary_search(k);

        if self.height == 0 {
            match res {
                Err(_) => return None,
                Ok(idx) => {
                    let v = &self.values[idx];
                    // SAFETY mapper serves as a sentinel that we're not going to mutate
                    //        the structure of the DAG until the borrow ends
                    let v = unsafe { mapper.extend_lifetime(v) };
                    return Some(v);
                }
            }
        }

        let child_height = self.height - 1;
        let next_node_to_search = match res {
            Err(0) => match self.prev.as_ref().cloned() {
                Some(prev) => prev,
                None => mapper.first_nodes[child_height as usize].clone(),
            },
            Err(idx) => mapper.get(&(self.pivots[idx - 1].clone(), child_height)),
            Ok(idx) => mapper.get(&(self.pivots[idx].clone(), child_height)),
        };
        let next = next_node_to_search.borrow();
        next.get(k, mapper)
    }

    fn insert(&mut self, k: K, v: V, height: Height, mapper: &mut Metadata<K, V>)
    where
        K: Hash + Ord + Clone,
        V: Clone,
    {
        if self.height == 0 {
            match self.pivots.binary_search(&k) {
                Ok(idx) => {
                    self.pivots[idx] = k;
                    self.values[idx] = v;
                }
                Err(idx) => {
                    self.pivots.insert(idx, k);
                    self.values.insert(idx, v);
                }
            }

            return;
        }
        let op = Op::Insert(k, v, height);
        self.push_ops(once(op), mapper);
    }

    fn push_ops(&mut self, ops: impl Iterator<Item = Op<K, V>>, mapper: &mut Metadata<K, V>)
    where
        K: Hash + Ord + Clone,
        V: Clone,
    {
        if self.height != 0 {
            self.buffer.extend(ops);
            if self.buffer.len() + self.pivots.len() >= mapper.b as usize {
                self.flush(mapper);
            }
        } else {
            for op in ops {
                self.apply_to_leaf(op)
            }
        }
    }

    fn flush(&mut self, mapper: &mut Metadata<K, V>)
    where
        K: Hash + Ord + Clone,
        V: Clone,
    {
        debug_assert!(self.height > 0);
        debug_assert!(self.values.is_empty());

        let pivots = take(&mut self.pivots);
        let mut buffer = take(&mut self.buffer);

        buffer.sort_by(|a, b| a.key().cmp(b.key()));
        // TODO for runs of the same op, last op wins?

        let above_leaves = self.height == 1;
        let leaves: Option<Vec<_>> =
            above_leaves.then(|| pivots.iter().map(|k| mapper.get(&(k.clone(), 0))).collect());
        let mutations = MergeIter {
            pivots: pivots.into_iter(),
            buffer: buffer.iter(),
        };

        let mut new_node = Node::new(self.height, self.this.clone());
        new_node.next = self.next.clone();
        new_node.prev = self.prev.clone();

        let mut new_siblings = vec![];

        Self::apply_mutations(Root::Mut(&mut new_node), mutations, mapper, |sib| {
            if above_leaves {
                new_siblings.push(sib.clone())
            }
        });

        *self = new_node;

        match leaves {
            None => self.push_ops_to_children(buffer, mapper),
            Some(mut leaves) => {
                leaves.dedup_by(|a, b| Rc::ptr_eq(a, b));
                let mut leaves = VecDeque::from(leaves);
                if self.prev.is_none()
                    && leaves
                        .front()
                        .map(|a| !Rc::ptr_eq(a, &mapper.first_nodes[0]))
                        .unwrap_or(true)
                {
                    leaves.push_front(mapper.first_nodes[0].clone())
                }
                self.push_ops_to_leaves(leaves, new_siblings, buffer, mapper)
            }
        }
    }

    fn apply_mutations(
        mut current_node_ptr: Root<K, V>,
        mutations: MergeIter<K, V>,
        mapper: &mut Metadata<K, V>,
        mut on_new_sibling: impl FnMut(&Ptr<Self>),
    ) where
        K: Hash + Ord + Clone,
    {
        use Mutation::*;
        for mutation in mutations {
            let mut current_node = current_node_ptr.borrow_mut();
            debug_assert!(current_node.height > 0);
            debug_assert!(current_node.values.is_empty());
            match mutation {
                Pivot(pivot) => current_node.pivots.push(pivot),
                Buffer(op) => {
                    let new_node = current_node.apply_op_to_node(op, mapper);
                    drop(current_node);
                    if let Some(new_node) = new_node {
                        on_new_sibling(&new_node);
                        current_node_ptr = Root::Ptr(new_node);
                    }
                }
                Both(pivot, op) => {
                    current_node.pivots.push(pivot);

                    let new_node = current_node.apply_op_to_node(op, mapper);
                    if let Some(new_node) = new_node {
                        drop(current_node);
                        current_node_ptr = Root::Ptr(new_node);
                    }
                }
            }
        }
    }

    fn apply_op_to_node(&mut self, op: &Op<K, V>, mapper: &mut Metadata<K, V>) -> Option<Ptr<Self>>
    where
        K: Hash + Ord + Clone,
    {
        use Op::*;
        debug_assert!(self.height > 0);

        let op_height = op.height();
        // i > h_e
        if self.height > op_height {
            return None;
        }

        if self.height == op_height || self.pivots.is_empty() {
            match op {
                Insert(k, _, _) if self.pivots.last() == Some(&k) => {}
                Insert(k, _, _) => {
                    mapper.duplicate_ptr(self.pivots.last().cloned(), k.clone(), self.height - 1);
                    self.pivots.push(k.clone());
                }
                Delete(k, op_height) => {
                    if self.pivots.last() == Some(&k) {
                        self.pivots.pop();
                        todo!("delete child pointer?");
                    }
                }
            }
            return None;
        }

        debug_assert!(self.height < op_height);
        match op {
            Insert(k, _, _) if self.pivots.last() == Some(&k) => None,
            Insert(k, _, _) => {
                let next = Self::ptr(self.height);
                mapper.set((k.clone(), self.height), next.clone());

                let mut next_node = next.borrow_mut();

                mapper.duplicate_ptr(self.pivots.last().cloned(), k.clone(), self.height - 1);
                next_node.pivots.push(k.clone());

                next_node.next = self.next.clone();
                next_node.prev = self.this.upgrade();
                self.next = Some(next.clone());

                if let Some(next_next) = &mut next_node.next {
                    let mut nn = next_next.borrow_mut();
                    nn.prev = Some(next.clone());
                }
                drop(next_node);

                Some(next)
            }
            Delete(k, op_height) => todo!("merge node"),
        }
    }

    fn push_ops_to_children(&mut self, mut buffer: Vec<Op<K, V>>, mapper: &mut Metadata<K, V>)
    where
        K: Hash + Ord + Clone,
        V: Clone,
    {
        if buffer.is_empty() {
            return;
        }

        // find the subset of nodes for each child, then push ops
        // we go in reverse child order for compatibility with our the intended
        // locking strategy for deletes
        // even if we split out new nodes at the current level their children
        // won't be split, so we don't need to look at any neighbors
        for pivot in self.pivots.iter().rev() {
            if buffer.is_empty() {
                break;
            }

            let child_index = buffer.partition_point(|op| op.key() < pivot);
            if child_index >= buffer.len() {
                continue;
            }

            let child = mapper.get(&(pivot.clone(), self.height - 1));
            let mut child = child.borrow_mut();
            let for_child = buffer.drain(child_index..);
            child.push_ops(for_child, mapper);
        }

        // if we have any ops left over we must be the first node,
        // push to the first node on the lower level
        assert!(self.prev.is_none());
        assert!(Weak::as_ptr(&self.this) == Rc::as_ptr(&mapper.first_nodes[self.height as usize]));
        let child = mapper.first_nodes[self.height as usize - 1].clone();
        let mut child = child.borrow_mut();
        let for_child = buffer.into_iter();
        child.push_ops(for_child, mapper);
    }

    fn push_ops_to_leaves(
        &mut self,
        old_leaves: VecDeque<Ptr<Self>>,
        new_siblings: Vec<Ptr<Self>>,
        mut buffer: Vec<Op<K, V>>,
        mapper: &mut Metadata<K, V>,
    ) where
        K: Hash + Ord + Clone,
        V: Clone,
    {
        debug_assert_eq!(self.height, 1);

        dedup_all_but_last(&mut buffer);

        let prev_leaf = match old_leaves.front() {
            Some(leaf) => {
                let node = leaf.borrow();
                // FIXME likely wrong
                node.prev.clone()
            }
            None => Some(mapper.first_nodes[0].clone()),
        };

        let next_leaf = old_leaves.back().and_then(|leaf| {
            let node = leaf.borrow();
            node.next.clone()
        });

        let mut keys_and_values: VecDeque<Op<K, V>> = Default::default();
        {
            let mut parent_pivots = self.pivots.clone();
            for sibling_node in new_siblings {
                let sib = sibling_node.borrow();
                parent_pivots.extend_from_slice(&sib.pivots)
            }
            let mut parent_pivots = VecDeque::from(parent_pivots);

            if prev_leaf.is_none() {
                let mut prev_sib = self.prev.clone();
                while let Some(prev_node) = prev_sib {
                    let prev = prev_node.borrow();
                    for p in prev.pivots.iter().rev() {
                        parent_pivots.push_front(p.clone());
                    }
                    prev_sib = prev.prev.clone();
                }
            }

            let mut buffer = VecDeque::from(buffer);

            for leaf_node in old_leaves {
                use std::iter::zip;
                use Op::Insert;

                let leaf = leaf_node.borrow();
                for (k, v) in zip(&leaf.pivots, &leaf.values) {
                    if !buffer.is_empty() {
                        while let Some(true) = buffer.front().map(|op| op < k) {
                            let op = buffer.pop_front().unwrap();
                            keys_and_values.push_back(op);
                        }
                        if let Some(true) = buffer.front().map(|op| op == k) {
                            let op = buffer.pop_front().unwrap();
                            if matches!(op, Insert(..)) {
                                keys_and_values.push_back(op);
                            }
                            continue;
                        }
                    }

                    while let Some(true) = parent_pivots.front().map(|p| p < k) {
                        parent_pivots.pop_front();
                    }

                    let next_parent_pivot = parent_pivots.front();
                    if next_parent_pivot == Some(k) {
                        keys_and_values.push_back(Insert(k.clone(), v.clone(), 1));
                        parent_pivots.pop_front();
                    } else {
                        keys_and_values.push_back(Insert(k.clone(), v.clone(), 0));
                    }
                }
            }
            keys_and_values.extend(buffer)
        };

        let new_leaf = |mut leaf: std::cell::RefMut<Node<K, V>>| {
            let new_leaf = Self::ptr(0);
            {
                let mut next = new_leaf.borrow_mut();
                next.prev = leaf.this.upgrade();
                leaf.next = Some(new_leaf.clone());
            }
            new_leaf
        };

        let mut current_leaf = Self::ptr(0);
        match prev_leaf {
            Some(..) => {
                let mut leaf = current_leaf.borrow_mut();
                leaf.prev = prev_leaf.clone();
                if let Some(prev_leaf) = prev_leaf {
                    let mut prev = prev_leaf.borrow_mut();
                    prev.next = Some(current_leaf.clone());
                }
            }
            None => {
                let first_parent_pivot: &K = self.pivots.first().unwrap();
                // TODO should be later
                mapper.first_nodes[0] = current_leaf.clone();
                while !keys_and_values.is_empty() {
                    let next_run_pivot: &K = keys_and_values.front().unwrap().key();
                    if next_run_pivot >= first_parent_pivot {
                        break;
                    }

                    let next_run_len: usize = keys_and_values
                        .iter()
                        .skip(1)
                        .take_while(|op| op.height() == 0)
                        .count()
                        + 1usize;

                    let leaf = current_leaf.borrow_mut();

                    let expanded_len = leaf.pivots.len() + next_run_len;
                    let mut sink = if expanded_len <= mapper.b as usize {
                        leaf
                    } else {
                        current_leaf = new_leaf(leaf);
                        current_leaf.borrow_mut()
                    };

                    mapper.set((next_run_pivot.clone(), 0), current_leaf.clone());
                    for op in keys_and_values.drain(..next_run_len) {
                        sink.apply_to_leaf(op)
                    }
                }
                let leaf = current_leaf.borrow_mut();
                current_leaf = new_leaf(leaf);
            }
        }

        while !keys_and_values.is_empty() {
            let leaf = current_leaf.borrow_mut();

            let run_must_start_leaf = keys_and_values.front().unwrap().height() > 1;
            let can_add_run_to_current_leaf = if run_must_start_leaf {
                leaf.pivots.is_empty()
            } else {
                true
            };

            let next_run_len: usize = keys_and_values
                .iter()
                .skip(1)
                .take_while(|op| op.height() == 0)
                .count()
                + 1usize;

            let expanded_len = leaf.pivots.len() + next_run_len;
            let run_fits_in_leaf = leaf.pivots.is_empty() || expanded_len <= mapper.b as usize;

            let mut sink = if can_add_run_to_current_leaf && run_fits_in_leaf {
                leaf
            } else {
                current_leaf = new_leaf(leaf);
                current_leaf.borrow_mut()
            };

            let next_run_pivot = keys_and_values.front().unwrap().key();
            mapper.set((next_run_pivot.clone(), 0), current_leaf.clone());

            for op in keys_and_values.drain(..next_run_len) {
                sink.apply_to_leaf(op)
            }
        }

        let mut current = current_leaf.borrow_mut();
        current.next = next_leaf.clone();
        if let Some(next_leaf) = next_leaf {
            let mut next = next_leaf.borrow_mut();
            next.prev = Some(current_leaf.clone());
        }
    }

    fn apply_to_leaf(&mut self, op: Op<K, V>)
    where
        K: Ord,
    {
        use Op::*;
        debug_assert_eq!(self.height, 0);
        debug_assert_eq!(self.pivots.len(), self.values.len());

        let loc = self.pivots.binary_search_by(|pivot| pivot.cmp(op.key()));
        match (op, loc) {
            (Insert(_, v, _), Ok(i)) => self.values[i] = v,
            (Insert(k, v, _), Err(i)) if i < self.values.len() => {
                self.pivots.insert(i, k);
                self.values.insert(i, v)
            }
            (Insert(k, v, _), Err(_)) => {
                self.pivots.push(k);
                self.values.push(v);
            }
            (Delete(_, _), Ok(i)) => {
                self.pivots.remove(i);
                self.values.remove(i);
            }
            (Delete(_, _), Err(_)) => { /* nop */ }
        }
    }

    #[allow(dead_code)]
    fn split_leaf(&mut self, first_pivot: &K) -> Ptr<Self>
    where
        K: Ord,
    {
        debug_assert_eq!(self.height, 0);
        debug_assert_eq!(self.pivots.len(), self.values.len());
        let split_location = self.pivots.partition_point(|p| p < first_pivot);
        let new_child_pivots = self.pivots.split_off(split_location);
        let new_child_values = self.values.split_off(split_location);
        let new_node = Node::ptr(0);
        {
            let mut new = new_node.borrow_mut();
            new.pivots = new_child_pivots;
            new.values = new_child_values;
            new.next = self.next.clone();
            new.prev = self.this.upgrade();
        }
        self.next = Some(new_node.clone());
        new_node
    }

    #[allow(dead_code)]
    fn merge_with(
        &mut self,
        partition_points: &[K],
        new_ops: &mut vec::IntoIter<Op<K, V>>,
        mapper: &mut Metadata<K, V>,
    ) -> Option<Ptr<Self>>
    where
        K: Ord,
    {
        assert_eq!(self.height, 0);
        assert_eq!(self.pivots.len(), self.values.len());

        let pivots = take(&mut self.pivots).into_iter();
        let values = take(&mut self.values).into_iter();

        let mut merger = LeafMergeIter {
            partition_points,
            pivots,
            values,
            buffer: new_ops,
        };

        let mut current_node = Root::Mut(self);

        while !merger.is_done() {
            let next_run_len = merger.next_run_len();
            let mut current = current_node.borrow_mut();
            // TODO block size instead
            if current.pivots.len() + next_run_len > mapper.b as usize {
                let next_node = Self::ptr(0);
                // TODO
                // mapper.set((k.clone(), self.height), next.clone());

                let mut next = next_node.borrow_mut();

                next.next = current.next.clone();
                next.prev = current.this.upgrade();
                current.next = Some(next_node.clone());
                drop(next);
                drop(current);
                current_node = Root::Ptr(next_node);
                continue;
            }
            let current = &mut *current;
            merger.add_next_run(&mut current.pivots, &mut current.values);
        }

        match current_node {
            Root::Mut(_) => None,
            Root::Ptr(p) => Some(p),
        }
    }
}

fn dedup_all_but_last<K, V>(buffer: &mut Vec<Op<K, V>>)
where
    K: Ord,
{
    {
        let mut buffer = &mut buffer[..];
        while !buffer.is_empty() {
            let key = buffer[0].key();
            let run_end = buffer.partition_point(|op| op.key() == key);
            if run_end > 1 {
                buffer.swap(0, run_end - 1);
            }
            buffer = &mut buffer[run_end..]
        }
    }
    buffer.dedup_by(|a, b| a.key() == b.key())
}

struct MergeIter<'a, K, V> {
    pivots: vec::IntoIter<K>,
    buffer: slice::Iter<'a, Op<K, V>>,
}

enum Mutation<'a, K, V> {
    Pivot(K),
    Buffer(&'a Op<K, V>),
    Both(K, &'a Op<K, V>),
}

impl<'a, K, V> Iterator for MergeIter<'a, K, V>
where
    K: Ord,
{
    type Item = Mutation<'a, K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        use std::cmp::Ordering::{Equal as BothNext, Greater as PivotNext, Less as BufferNext};
        use Mutation::*;

        if self.pivots.as_slice().is_empty() && self.buffer.as_slice().is_empty() {
            return None;
        }

        if self.pivots.as_slice().is_empty() {
            return self.buffer.next().map(Buffer);
        }
        if self.buffer.as_slice().is_empty() {
            return self.pivots.next().map(Pivot);
        }

        let ord = self.buffer.as_slice()[0]
            .partial_cmp(&self.pivots.as_slice()[0])
            .unwrap();

        match ord {
            BufferNext => Some(Buffer(self.buffer.next().unwrap())),
            PivotNext => Some(Pivot(self.pivots.next().unwrap())),
            BothNext => {
                let k = self.pivots.next().unwrap();
                let op = self.buffer.next().unwrap();
                Some(Both(k, op))
            }
        }
    }
}

struct LeafMergeIter2<'a, K, V> {
    partition_points: &'a [K],
    next_node_partition: Option<&'a K>,
    old_leaves: LeafIter<K, V>,
    buffer: vec::IntoIter<Op<K, V>>,
}

type RunSize = (usize, usize);

impl<'a, K, V> LeafMergeIter2<'a, K, V>
where
    K: Ord,
{
    fn is_done(&self) -> bool {
        self.partition_points.is_empty()
            || (self.old_leaves.is_empty() && self.buffer.as_slice().is_empty())
    }

    fn add_next_run(
        &mut self,
        (mut remaining_pivots, mut remaining_ops): RunSize,
        pivots: &mut Vec<K>,
        values: &mut Vec<V>,
    ) -> &'a K
    where
        K: Clone,
        V: Clone,
    {
        use self::Op::*;
        use std::cmp::Ordering::{Equal as BothNext, Greater as BufferNext, Less as PivotNext};

        let (first_pivot, remaining_partition_points) =
            self.partition_points.split_first().unwrap();
        self.partition_points = remaining_partition_points;
        println!("\nstart");
        loop {
            println!(
                "{remaining_ops} {} {remaining_pivots} {}",
                self.buffer.len(),
                self.old_leaves.len()
            );
            debug_assert!(self.buffer.as_slice().len() >= remaining_ops);

            if remaining_pivots == 0 && remaining_ops == 0 {
                break first_pivot;
            }

            if remaining_pivots == 0 {
                for _ in 0..remaining_ops {
                    let Insert(key, value, _) = self.buffer.next().unwrap() else {
                        continue
                    };
                    pivots.push(key);
                    values.push(value);
                }
                break first_pivot;
            }
            if remaining_ops == 0 {
                self.old_leaves.take(
                    remaining_pivots,
                    |pivot| pivots.push(pivot.clone()),
                    |value| values.push(value.clone()),
                );
                break first_pivot;
            }

            let ord = self
                .old_leaves
                .partial_cmp(&self.buffer.as_slice()[0].key())
                .unwrap();

            match ord {
                BufferNext => {
                    remaining_ops -= 1;
                    let Insert(key, value, _) = self.buffer.next().unwrap() else {
                        continue
                    };
                    pivots.push(key);
                    values.push(value);
                }
                PivotNext => {
                    remaining_pivots -= 1;
                    let (pivot, value) = self.old_leaves.next_pair().unwrap();
                    pivots.push(pivot);
                    values.push(value);
                }
                BothNext => {
                    remaining_ops -= 1;
                    remaining_pivots -= 1;
                    let _ = self.old_leaves.next_pair().unwrap();
                    let Insert(key, value, _) = self.buffer.next().unwrap() else {
                        continue
                    };
                    pivots.push(key);
                    values.push(value);
                }
            }
        }
    }

    fn next_run_len(&self) -> (usize, RunSize) {
        use self::Op::*;
        use std::cmp::Ordering::{Equal as BothNext, Greater as BufferNext, Less as PivotNext};

        let pivots_end = self.pivot_run_end();
        let buffer_end = self.buffer_run_end();
        let mut pivots = self.old_leaves.get_until(pivots_end);
        let mut buffer = &self.buffer.as_slice()[..buffer_end];
        let mut run_size = 0;
        loop {
            if pivots.is_empty() && buffer.is_empty() {
                break;
            }

            if pivots.is_empty() {
                run_size += buffer.iter().filter(|op| matches!(op, Insert(..))).count();
                break;
            }

            if buffer.is_empty() {
                run_size += pivots.len();
                break;
            }

            let ord = pivots.partial_cmp(&buffer[0].key()).unwrap();

            match ord {
                BufferNext => {
                    if matches!(&buffer[0], Insert(..)) {
                        run_size += 1
                    }
                    buffer = &buffer[1..];
                }
                PivotNext => {
                    run_size += 1;
                    pivots.increment();
                }
                BothNext => {
                    if matches!(&buffer[0], Insert(..)) {
                        run_size += 1
                    }
                    buffer = &buffer[1..];
                    pivots.increment();
                }
            }
        }
        println!("{pivots_end} {buffer_end}");
        (run_size, (pivots_end, buffer_end))
    }

    fn pivot_run_end(&self) -> usize {
        let run_end = match (self.partition_points.len(), self.next_node_partition) {
            (0 | 1, None) => return self.old_leaves.len(),
            (1, Some(next)) => next,
            _ => &self.partition_points[1],
        };
        self.old_leaves.partition_point(|p| p < run_end)
    }

    fn buffer_run_end(&self) -> usize {
        let run_end = match (self.partition_points.len(), self.next_node_partition) {
            (0 | 1, None) => return self.buffer.len(),
            (1, Some(next)) => next,
            _ => &self.partition_points[1],
        };
        self.buffer
            .as_slice()
            .partition_point(|op| op.key() < run_end)
    }
}

struct LeafIter<K, V> {
    leaves: VecDeque<Ptr<Node<K, V>>>,
    first_leaf_index: usize,
}

impl<K, V> LeafIter<K, V> {
    fn next_pair(&mut self) -> Option<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        if self.leaves.is_empty() {
            return None;
        }

        while !self.leaves.is_empty() {
            let first_node = &self.leaves[0];
            let first = first_node.borrow();
            if self.first_leaf_index > first.pivots.len() {
                drop(first);
                self.first_leaf_index = 0;
                let _ = self.leaves.pop_front();
                continue;
            }

            let next_pivot = first.pivots[self.first_leaf_index].clone();
            let next_value = first.values[self.first_leaf_index].clone();
            self.first_leaf_index += 1;
            return Some((next_pivot, next_value));
        }

        None
    }

    fn is_empty(&self) -> bool {
        self.leaves.is_empty()
    }

    fn len(&self) -> usize {
        self.get_until(usize::MAX).len()
    }

    fn partition_point(&self, mut f: impl FnMut(&K) -> bool) -> usize
    where
        K: Ord,
    {
        let mut total = 0;
        for leaf_node in &self.leaves {
            let leaf = leaf_node.borrow();
            let point = leaf.pivots.partition_point(&mut f);
            total += point;
            if point < leaf.pivots.len() {
                break;
            }
        }
        total
    }

    fn partial_cmp(&self, other: &K) -> Option<std::cmp::Ordering>
    where
        K: Ord,
    {
        let Some(first_node) = self.leaves.front() else {
            return None
        };

        let first = first_node.borrow();
        first.pivots[self.first_leaf_index].partial_cmp(other)
    }

    fn get_until(&self, pivots_end: usize) -> PivotIter<K, V> {
        PivotIter {
            leaves: self.leaves.as_slices().0, // TODO
            current_leaf_index: self.first_leaf_index,
            remaining: pivots_end,
        }
    }

    fn take(
        &mut self,
        mut remaining_pivots: usize,
        mut with_pivot: impl FnMut(&K),
        mut with_value: impl FnMut(&V),
    ) {
        loop {
            let first_node = self.leaves.front().unwrap();
            {
                let first = first_node.borrow();
                let pivots_in_first = min(remaining_pivots, first.pivots.len());
                remaining_pivots -= pivots_in_first;
                self.first_leaf_index += pivots_in_first;
                for i in 0..pivots_in_first {
                    with_pivot(&first.pivots[i]);
                    with_value(&first.values[i]);
                }
            }

            if remaining_pivots > 0 {
                let _ = self.leaves.pop_front();
                self.first_leaf_index = 0;
            } else {
                break;
            }
        }
    }
}

struct PivotIter<'a, K, V> {
    leaves: &'a [Ptr<Node<K, V>>],
    current_leaf_index: usize,
    remaining: usize,
}
impl<K, V> PivotIter<'_, K, V> {
    fn len(&self) -> usize {
        let Some((first_node, others)) = self.leaves.split_first() else {
            return 0
        };
        let first = first_node.borrow();
        let mut len = first.pivots[self.current_leaf_index..].len();

        for node in others {
            let leaf = node.borrow();
            len += leaf.pivots.len()
        }

        min(len, self.remaining)
    }

    fn partial_cmp(&self, other: &K) -> Option<std::cmp::Ordering>
    where
        K: Ord,
    {
        let Some(first_node) = self.leaves.first() else {
            return None
        };

        let first = first_node.borrow();
        first.pivots[self.current_leaf_index].partial_cmp(other)
    }

    fn increment(&mut self) {
        if self.leaves.is_empty() {
            return;
        }

        if self.remaining == 0 {
            return;
        }

        self.remaining -= 1;
        let first = self.leaves[0].borrow();
        if self.current_leaf_index + 1 < first.pivots.len() {
            self.current_leaf_index += 1;
            return;
        }

        self.leaves = &self.leaves[1..];
        self.current_leaf_index = 1;
    }

    fn is_empty(&self) -> bool {
        let Some((first_node, others)) = self.leaves.split_first() else {
            return true
        };
        if others.len() > 0 {
            return false;
        }

        let first = first_node.borrow();
        first.pivots[self.current_leaf_index..].is_empty()
    }
}

struct LeafMergeIter<'a, 'b, K, V> {
    partition_points: &'a [K],
    pivots: vec::IntoIter<K>,
    values: vec::IntoIter<V>,
    buffer: &'b mut vec::IntoIter<Op<K, V>>,
}

impl<'a, 'b, K, V> LeafMergeIter<'a, 'b, K, V>
where
    K: Ord,
{
    fn is_done(&self) -> bool {
        self.partition_points.is_empty()
            || (self.pivots.as_slice().is_empty() && self.buffer.as_slice().is_empty())
    }

    fn add_next_run(&mut self, pivots: &mut Vec<K>, values: &mut Vec<V>) {
        use self::Op::*;
        use std::cmp::Ordering::{Equal as BothNext, Greater as PivotNext, Less as BufferNext};

        let mut remaining_pivots = self.pivot_run_end();
        let mut remaining_ops = self.buffer_run_end();
        self.partition_points = &self.partition_points[1..];

        loop {
            if remaining_pivots == 0 && remaining_ops == 0 {
                break;
            }

            if remaining_pivots == 0 {
                for _ in 0..remaining_ops {
                    let Insert(key, value, _) = self.buffer.next().unwrap() else {
                        continue
                    };
                    pivots.push(key);
                    values.push(value);
                }
                break;
            }
            if remaining_ops == 0 {
                pivots.extend((&mut self.pivots).take(remaining_pivots));
                values.extend((&mut self.values).take(remaining_pivots));
                break;
            }

            let ord = self.buffer.as_slice()[0]
                .partial_cmp(&self.pivots.as_slice()[0])
                .unwrap();

            match ord {
                BufferNext => {
                    remaining_ops -= 1;
                    let Insert(key, value, _) = self.buffer.next().unwrap() else {
                        continue
                    };
                    pivots.push(key);
                    values.push(value);
                }
                PivotNext => {
                    remaining_pivots -= 1;
                    pivots.push(self.pivots.next().unwrap());
                    values.push(self.values.next().unwrap());
                }
                BothNext => {
                    remaining_ops -= 1;
                    remaining_pivots -= 1;
                    let _ = self.pivots.next().unwrap();
                    let _ = self.values.next().unwrap();
                    let Insert(key, value, _) = self.buffer.next().unwrap() else {
                        continue
                    };
                    pivots.push(key);
                    values.push(value);
                }
            }
        }
    }

    fn next_run_len(&self) -> usize {
        use self::Op::*;
        use std::cmp::Ordering::{Equal as BothNext, Greater as PivotNext, Less as BufferNext};

        let pivots_end = self.pivot_run_end();
        let buffer_end = self.buffer_run_end();
        let mut pivots = &self.pivots.as_slice()[..pivots_end];
        let mut buffer = &self.buffer.as_slice()[..buffer_end];
        let mut run_size = 0;
        loop {
            if self.pivots.as_slice().is_empty() && self.buffer.as_slice().is_empty() {
                break;
            }

            if self.pivots.as_slice().is_empty() {
                run_size += buffer.iter().filter(|op| matches!(op, Insert(..))).count();
                break;
            }
            if self.buffer.as_slice().is_empty() {
                run_size += pivots.len();
                break;
            }

            let ord = self.buffer.as_slice()[0]
                .partial_cmp(&self.pivots.as_slice()[0])
                .unwrap();

            match ord {
                BufferNext => {
                    if matches!(&buffer[0], Insert(..)) {
                        run_size += 1
                    }
                    buffer = &buffer[1..];
                }
                PivotNext => {
                    run_size += 1;
                    pivots = &pivots[1..];
                }
                BothNext => {
                    if matches!(&buffer[0], Insert(..)) {
                        run_size += 1
                    }
                    buffer = &buffer[1..];
                    pivots = &pivots[1..];
                }
            }
        }
        run_size
    }

    fn pivot_run_end(&self) -> usize {
        if self.partition_points.len() == 1 {
            return self.pivots.len();
        }
        let run_end = &self.partition_points[1];
        self.pivots.as_slice().partition_point(|p| p < run_end)
    }

    fn buffer_run_end(&self) -> usize {
        if self.partition_points.len() == 1 {
            return self.buffer.len();
        }
        let run_end = &self.partition_points[1];
        self.buffer
            .as_slice()
            .partition_point(|op| op.key() < run_end)
    }
}

enum Root<'a, K, V> {
    Mut(&'a mut Node<K, V>),
    Ptr(Ptr<Node<K, V>>),
}

impl<'a, K, V> Root<'a, K, V> {
    fn borrow_mut<'s>(&'s mut self) -> Borrow<'s, K, V> {
        match self {
            Root::Mut(m) => Borrow::Mut(&mut *m),
            Root::Ptr(p) => Borrow::Guard(p.borrow_mut()),
        }
    }
}

enum Borrow<'a, K, V> {
    Mut(&'a mut Node<K, V>),
    Guard(cell::RefMut<'a, Node<K, V>>),
}

impl<'a, K, V> Deref for Borrow<'a, K, V> {
    type Target = Node<K, V>;

    fn deref(&self) -> &Self::Target {
        match self {
            Borrow::Mut(m) => &*m,
            Borrow::Guard(g) => &*g,
        }
    }
}

impl<'a, K, V> DerefMut for Borrow<'a, K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Borrow::Mut(m) => &mut *m,
            Borrow::Guard(g) => &mut *g,
        }
    }
}

// struct NodeIter<'a, K, V> {
//     current: Option<Root<'a, K, V>>,
//     last: Option<Ptr<Node<K, V>>>,
// }

// impl<'a, K, V> NodeIter<'a, K, V> {
//     fn new(first: &'a mut Node<K, V>, last: Option<Ptr<Node<K, V>>>) -> Self {
//         Self {
//             current: Some(Root::Mut(first)),
//             last,
//         }
//     }
// }

// impl<'a, K, V> Iterator for NodeIter<'a, K, V> {
//     type Item = Root<'a, K, V>;

//     fn next(&mut self) -> Option<Self::Item> {
//         match self.current.take() {
//             None => None,
//             Some(mut root) => {
//                 let node = root.borrow_mut();
//                 if let Some(last) = &self.last {
//                     if node.this.as_ptr() != Rc::as_ptr(last) {
//                         let next = node.next.clone().unwrap();
//                         self.current = Some(Root::Ptr(next));
//                     }
//                 }
//                 drop(node);
//                 Some(root)
//             }
//         }
//     }
// }

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
}

impl<K, V> Metadata<K, V> {
    #[track_caller]
    fn get(&self, pivot: &(K, Height)) -> Ptr<Node<K, V>>
    where
        K: Hash + Eq,
    {
        self.mapping[pivot].clone()
    }

    fn set(&mut self, pivot: (K, Height), node: Ptr<Node<K, V>>)
    where
        K: Hash + Eq,
    {
        self.mapping.insert(pivot, node);
    }

    // fn update(&mut self, pivot: &(K, u8), old_node: &Ptr<Node<K, V>>, new_node: &Ptr<Node<K, V>>)
    // where
    //     K: Hash + Eq,
    // {
    //     let current = self.mapping.get_mut(pivot).unwrap();
    //     if Rc::ptr_eq(current, old_node) {
    //         *current = new_node.clone()
    //     }
    // }

    fn alloc_first(&mut self, height: Height) {
        if height as usize >= self.first_nodes.len() {
            let first = self.first_nodes.len() as u8;
            self.first_nodes
                .extend((first..=height).map(|h| Node::ptr(h)))
        }
    }

    fn duplicate_ptr(&mut self, from: Option<K>, to: K, height: Height)
    where
        K: Hash + Eq,
    {
        let child = match from {
            Some(from) => self.get(&(from, height)),
            None => {
                self.alloc_first(height);
                self.first_nodes[height as usize].clone()
            }
        };
        self.set((to, height), child);
    }

    unsafe fn extend_lifetime<'s>(&'s self, v: &V) -> &'s V {
        std::mem::transmute(v)
    }
}

impl<K, V> std::fmt::Debug for List<K, V>
where
    K: Hash + Eq + Clone + Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut f = f.debug_list();
        // let mut f = &mut f;

        if self.meta.first_nodes.is_empty() {
            return f.finish();
        };

        // let mut seen_nodes = HashSet::new();

        // let num_levels = self.meta.first_nodes.len();
        for list in self.meta.first_nodes.iter().rev() {
            f.entry(&DebugList(list.clone(), &self.meta));
        }

        f.finish()
    }
}

struct DebugList<'a, K, V>(Ptr<Node<K, V>>, &'a Metadata<K, V>);

impl<'a, K, V> std::fmt::Debug for DebugList<'a, K, V>
where
    K: Hash + Eq + Clone + Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut node = self.0.clone();
        let mut f = f.debug_list();
        let mut f = &mut f;
        loop {
            // let new = seen_nodes.insert(Rc::as_ptr(&node));
            let borrow = node.borrow();
            f = f.entry(&DebugNode(&borrow, self.1));
            match borrow.next.as_ref().cloned() {
                None => break,
                Some(next) => {
                    drop(borrow);
                    node = next.clone()
                }
            }
        }
        f.finish()
    }
}

struct DebugNode<'a, K, V>(&'a Node<K, V>, &'a Metadata<K, V>);

impl<'a, K, V> std::fmt::Debug for DebugNode<'a, K, V>
where
    K: Hash + Eq + Clone + Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Node")
            .field("height", &self.0.height)
            .field(
                "pivots",
                &DebugPivots(&self.0.pivots, self.1, self.0.height),
            )
            .field("values", &self.0.values)
            .field("buffer", &self.0.buffer)
            .field("this", &Weak::as_ptr(&self.0.this))
            .field("next", &self.0.next.as_ref().map(Rc::as_ptr))
            .field("prev", &self.0.prev.as_ref().map(Rc::as_ptr))
            .finish()
    }
}

struct DebugPivots<'a, K, V>(&'a [K], &'a Metadata<K, V>, Height);

impl<'a, K, V> std::fmt::Debug for DebugPivots<'a, K, V>
where
    K: Hash + Eq + Clone + Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut list = f.debug_list();
        let list = if self.2 > 0 {
            list.entries(self.0.iter().map(|k| {
                (
                    k,
                    self.1.mapping.get(&(k.clone(), self.2 - 1)).map(Rc::as_ptr),
                )
            }))
        } else {
            list.entries(self.0)
        };
        list.finish()
    }
}

impl<K, V> std::fmt::Debug for Node<K, V>
where
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Node")
            .field("height", &self.height)
            .field("pivots", &self.pivots)
            .field("values", &self.values)
            .field("buffer", &self.buffer)
            .finish()
    }
}

impl<K, V> std::cmp::PartialEq for Op<K, V>
where
    K: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}

impl<K, V> std::cmp::PartialOrd for Op<K, V>
where
    K: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.key().partial_cmp(other.key())
    }
}

impl<K, V> std::cmp::PartialEq<K> for Op<K, V>
where
    K: PartialEq,
{
    fn eq(&self, other: &K) -> bool {
        self.key() == other
    }
}

impl<K, V> std::cmp::PartialOrd<K> for Op<K, V>
where
    K: PartialOrd,
{
    fn partial_cmp(&self, other: &K) -> Option<std::cmp::Ordering> {
        self.key().partial_cmp(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let mut list = List::new(8);
        list.insert(1, 10);
        list.insert(2, 22);
        list.insert(3, 30);

        assert_eq!(list.get(&1), Some(&10));
        assert_eq!(list.get(&2), Some(&22));
        assert_eq!(list.get(&3), Some(&30));
    }

    #[test]
    fn fuzz1() {
        let mut list = List::new(10);
        list.insert(183893248, 267);

        assert_eq!(list.get(&0), None);
    }

    #[test]
    fn fuzz2() {
        let mut list = List::new(10);
        list.insert(4294905344u32, 4294967295u32);
        list.insert(268435200, 1);

        assert_eq!(list.get(&4294905344), Some(&4294967295));
        assert_eq!(list.get(&268435200), Some(&1));
    }

    #[test]
    fn fuzz3() {
        let mut list = List::new(10);
        list.insert(0, 0);
        list.insert(3707772928u32, 3421833810u32);

        assert_eq!(list.get(&0), Some(&0));
        assert_eq!(list.get(&3707772928), Some(&3421833810));
    }

    #[test]
    fn fuzz4() {
        let mut list = List::new(10);
        list.insert(0, 0);
        list.insert(2818048u32, 4110417920u32);

        assert_eq!(list.get(&0), Some(&0));
        assert_eq!(list.get(&2818048u32), Some(&4110417920u32));
    }

    #[test]
    fn flush_works() {
        let mut list: List<u32, u32> = List::new(10);
        list.insert(2122241918, 2122219134);
        list.insert(2122219134, 2122219134);
        list.insert(4294901759, 4294967295);
        list.insert(2122219134, 2122219134);
        list.insert(2122219134, 2122219134);
        list.insert(2122219134, 2122219225);
        list.insert(3622, 0);
        list.insert(0, 0);
        assert_eq!(list.get(&0), Some(&0));

        list.insert(16843007, 4278196238);

        assert_eq!(list.get(&0), Some(&0));

        list.insert(65535, 0);
        assert_eq!(list.get(&0), Some(&0));
    }

    #[test]
    fn flush_works2() {
        let mut list: List<u32, u32> = List::new(10);
        list.insert(524288, 0);
        assert_eq!(list.get(&0), None);
        list.insert(0, 4278222848);
        assert_eq!(list.get(&0), Some(&4278222848));
        list.insert(2048, 0);
        assert_eq!(list.get(&0), Some(&4278222848));
        list.insert(2147483648, 16711943);
        assert_eq!(list.get(&0), Some(&4278222848));
        list.insert(16778496, 65);
        assert_eq!(list.get(&0), Some(&4278222848));
        list.insert(149, 0);
        assert_eq!(list.get(&0), Some(&4278222848));
        list.insert(0, 2147483648);
        assert_eq!(list.get(&0), Some(&2147483648));
        list.insert(134218752, 0);
        assert_eq!(list.get(&0), Some(&2147483648));
        list.insert(0, 17268736);
        assert_eq!(list.get(&0), Some(&17268736));
        list.insert(83886080, 4260096);
        assert_eq!(list.get(&0), Some(&17268736));
    }

    #[test]
    fn flush_overflowing_child_directs_nodes() {
        let mut list: List<u32, u32> = List::new(10);
        macro_rules! op {
            (Insert { key: $key:expr, value: $val:expr $(,)? }) => {
                list.insert($key, $val);
            };
        }
        op!(Insert {
            key: 38,
            value: 16779776,
        });
        op!(Insert {
            key: 503_316_736,
            value: 505290270,
        });
        op!(Insert {
            key: 505290270,
            value: 505290270,
        });
        op!(Insert {
            key: 505290270,
            value: 505290270,
        });
        op!(Insert {
            key: 505290270,
            value: 505290270,
        });
        op!(Insert {
            key: 505290270,
            value: 505290270,
        });
        op!(Insert {
            key: 505290270,
            value: 505290270,
        });
        op!(Insert {
            key: 505290270,
            value: 505290270,
        });
        op!(Insert {
            key: 505290270,
            value: 505290270,
        });
        op!(Insert {
            key: 505290270,
            value: 505290270,
        });
        op!(Insert {
            key: 738_205_214,
            value: 462,
        });
        assert_eq!(list.get(&738205214), Some(&462));
    }

    #[test]
    fn flush_gets_entire_segment() {
        let mut list: List<u32, u32> = List::new(10);
        list.assert_structure();

        list.insert(1600085855, 95);
        list.assert_structure();

        list.insert(0, 1600085855);
        list.assert_structure();

        list.insert(1600085855, 24415);
        list.assert_structure();

        list.insert(0, 0);
        list.assert_structure();

        list.insert(0, 238747648);
        list.assert_structure();

        list.insert(0, 0);
        list.assert_structure();

        list.insert(1600085855, 1600085855);
        list.assert_structure();

        list.insert(237373696, 0);
        list.assert_structure();

        list.insert(0, 0);
        list.assert_structure();

        list.insert(0, 0);
        list.assert_structure();

        assert_eq!(list.get(&1600085855), Some(&1600085855));
    }

    #[test]
    fn flush_to_leaves() {
        let mut list: List<u32, u32> = List::new(10);

        list.insert(38, 16779776);
        // println!("{}", list.output_dot());
        list.assert_structure();

        list.insert(505290240, 505290270);
        // println!("{}", list.output_dot());
        list.assert_structure();

        list.insert(505290270, 505290270);
        // println!("{}", list.output_dot());
        list.assert_structure();

        list.insert(505290270, 505290270);
        // println!("{}", list.output_dot());
        list.assert_structure();

        list.insert(505290270, 505290270);
        // println!("{}", list.output_dot());
        list.assert_structure();

        list.insert(505290270, 505290270);
        // println!("{}", list.output_dot());
        list.assert_structure();

        list.insert(1593843230, 1600085855);
        // println!("{}", list.output_dot());
        list.assert_structure();

        list.insert(1593859935, 505290335);
        // println!("{}", list.output_dot());
        list.assert_structure();

        list.insert(0, 503316480);
        // println!("{}", list.output_dot());
        list.assert_structure();

        list.insert(14, 0);
        // println!("{}", list.output_dot());
        list.assert_structure();

        list.insert(8, 0);
        // println!("{}", list.output_dot());
        list.assert_structure();

        list.insert(32, 0);
        // println!("{}", list.output_dot());
        list.assert_structure();

        list.insert(0, 0);
        // println!("{}", list.output_dot());
        list.assert_structure();

        list.insert(505290270, 505290270);
        // println!("{}", list.output_dot());
        list.assert_structure();

        list.insert(1973790, 505290240);
        // println!("{}", list.output_dot());
        list.assert_structure();

        list.insert(118316, 0);
        // println!("{}", list.output_dot());
        list.assert_structure();

        assert_eq!(list.get(&118316), Some(&0));
        println!("{}", list.output_dot());
    }

    #[test]
    fn leaf_iter_no_overrun() {
        let mut list: List<u32, u32> = List::new(10);

        list.insert(0, 655409);
        list.assert_structure();
        list.insert(6119679, 270);
        list.assert_structure();
        list.insert(134221313, 0);
        list.assert_structure();
        list.insert(134154752, 16777262);
        list.assert_structure();
        list.insert(236, 0);
        list.assert_structure();
        list.insert(256, 0);
        list.assert_structure();
        list.insert(168430090, 168430090);
        list.assert_structure();
        list.insert(168430090, 168430090);
        list.assert_structure();
        list.insert(168430090, 168430090);
        list.assert_structure();
        list.insert(2570, 0);
        list.assert_structure();

        list.insert(0, 0);
        list.assert_structure();

        assert_eq!(list.get(&0), Some(&0));
    }

    #[test]
    fn old_leaves_exist() {
        let mut list: List<u32, u32> = List::new(10);

        list.insert(234946816, 2048);
        list.assert_structure();
        list.insert(167772160, 3016448);
        list.assert_structure();
        list.insert(15466496, 0);
        list.assert_structure();
        list.insert(16777216, 0);
        list.assert_structure();
        list.insert(168430080, 168430090);
        list.assert_structure();
        list.insert(168430090, 168430090);
        list.assert_structure();
        list.insert(168430322, 168430090);
        list.assert_structure();
        list.insert(168430090, 0);
        list.assert_structure();
        list.insert(0, 494927872);
        list.assert_structure();
        list.insert(0, 23552);
        list.assert_structure();
        list.insert(0, 2147483648);
        list.assert_structure();
        list.insert(0, 4278257408);
        list.assert_structure();
        list.insert(0, 1280);
        list.assert_structure();
        list.insert(1576449, 0);
        list.assert_structure();
        list.insert(3065402717, 11974326);
        list.assert_structure();
    }

    #[test]
    fn insert_small() {
        let mut list: List<u32, u32> = List::new(3);

        list.insert(4284481550, 4294902015);
        list.assert_structure();
        list.insert(403570945, 8196);
        list.assert_structure();
        list.insert(0, 0);
        list.assert_structure();
        list.insert(4294950911, 1610612736);
        list.assert_structure();
        list.insert(1627324161, 4278255615);
        list.assert_structure();
        list.insert(11776, 11513600);
        list.assert_structure();
        println!("{}", list.output_dot());
        list.insert(1431655765, 791719765);
        println!("{}", list.output_dot());
        list.assert_structure();
    }

    #[test]
    fn insert_stuff() {
        let mut list: List<u32, u32> = List::new(10);

        list.insert(524292, 0);
        list.assert_structure();
        list.insert(134217728, 0);
        list.assert_structure();
        list.insert(8388608, 69402631);
        list.assert_structure();
        list.insert(0, 0);
        list.assert_structure();
        list.insert(0, 0);
        list.assert_structure();
        list.insert(0, 0);
        list.assert_structure();
        list.insert(9764864, 0);
        list.assert_structure();
        list.insert(8192, 256);
        list.assert_structure();
        list.insert(271104, 2498047);
        list.assert_structure();

        list.insert(2304, 0);

        list.assert_structure();
        list.insert(589824, 9764864);
        list.assert_structure();
        list.insert(0, 8192);
        list.assert_structure();
        list.insert(117473280, 271104);
        list.assert_structure();
        list.insert(505290270, 505290270);
        list.assert_structure();
        list.insert(505290270, 505290270);
        list.assert_structure();
        list.insert(505290270, 505290270);
        list.assert_structure();
        list.insert(505290270, 505290270);
        list.assert_structure();
        list.insert(125836830, 4009819905);
        list.assert_structure();
        println!("{}", list.output_dot());
        list.insert(1090584581, 1426063360);
        println!("{}", list.output_dot());
        list.assert_structure();
    }
}
