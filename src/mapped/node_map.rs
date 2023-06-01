#[cfg_attr(nightly, feature(is_sorted))]
use std::rc::Rc;
use std::{
    collections::HashMap,
    mem::replace,
    sync::atomic::{AtomicU64, Ordering::Relaxed},
};

use indexmap::IndexMap;

use super::UpperNode;

#[derive(Debug)]
pub struct NodeMap<K, V> {
    mappings: HashMap<LogicalAddress, Rc<UpperNode<K, V>>>,
    next_addr: AtomicU64,
}

#[derive(Debug)]
pub struct Mapper<'m, K, V> {
    mappings: &'m NodeMap<K, V>,
    updated: IndexMap<LogicalAddress, Rc<UpperNode<K, V>>>,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct LogicalAddress(u64);

impl<K, V> NodeMap<K, V> {
    pub fn new() -> Self {
        Self {
            mappings: HashMap::new(),
            next_addr: AtomicU64::new(1),
        }
    }

    pub fn get(&self, addr: &LogicalAddress) -> &Rc<UpperNode<K, V>> {
        self.mappings.get(addr).unwrap()
    }

    fn get_mut<A>(&mut self, addr: &LogicalAddress) -> &mut Rc<UpperNode<K, V>> {
        self.mappings.get_mut(addr).unwrap()
    }

    fn alloc_addr(&self) -> LogicalAddress {
        let addr = self.next_addr.fetch_add(1, Relaxed);
        LogicalAddress(addr)
    }

    fn set(&mut self, addr: LogicalAddress, node: Rc<UpperNode<K, V>>) {
        self.mappings.insert(addr, node);
    }

    fn add_node(&mut self, new_root: Rc<UpperNode<K, V>>) -> LogicalAddress {
        let addr = self.alloc_addr();
        self.set(addr, new_root);
        addr
    }
}

impl<'m, K, V> Mapper<'m, K, V> {
    fn get(&self, addr: &LogicalAddress) -> &Rc<UpperNode<K, V>> {
        if let Some(node) = self.updated.get(addr) {
            return node;
        }

        self.mappings.get(addr)
    }

    fn get_mut<A>(&mut self, addr: &LogicalAddress) -> Option<&mut Rc<UpperNode<K, V>>> {
        self.updated.get_mut(addr)
    }

    fn take_updated(&mut self) -> IndexMap<LogicalAddress, Rc<UpperNode<K, V>>> {
        replace(&mut self.updated, IndexMap::new())
    }

    fn alloc_addr(&mut self) -> LogicalAddress {
        self.mappings.alloc_addr()
    }

    fn set(&mut self, addr: LogicalAddress, node: Rc<UpperNode<K, V>>) {
        self.updated.insert(addr, node);
    }

    fn add_node(&mut self, new_root: Rc<UpperNode<K, V>>) -> LogicalAddress {
        let addr = self.alloc_addr();
        self.set(addr, new_root);
        addr
    }
}
