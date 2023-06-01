use std::{
    cmp::Ordering,
    ops::{Bound, Index, RangeBounds},
};

use self::RangeBound::*;

#[derive(Debug, Clone)]
pub struct DenseRangeMap<K, V> {
    entries: Vec<(Range<K>, V)>,
}

#[derive(Debug, Clone)]
pub struct SubEntries<'e, K, V> {
    entries: &'e [(Range<K>, V)],
}

#[derive(Debug, Clone, Copy)]
pub struct Range<K> {
    start: RangeBound<K>,
    end: RangeBound<K>,
}

#[derive(Debug, Clone, Copy)]
enum RangeBound<K> {
    NoBound,
    Includes(K),
}

impl<K, V> DenseRangeMap<K, V> {
    pub fn new() -> Self {
        Self { entries: vec![] }
    }

    pub fn get_bounded(&self, key: &K, bound: Range<&K>) -> Option<(Range<&K>, &V)>
    where
        K: PartialOrd,
    {
        self.sub_entries(bound).0.get(key)
    }

    pub fn sub_entries(
        &self,
        bound: Range<&K>,
    ) -> (
        SubEntries<'_, K, V>,
        (SubEntries<'_, K, V>, SubEntries<'_, K, V>),
    )
    where
        K: PartialOrd,
    {
        use RangeBound::*;
        let Range { start, end } = bound;
        let start = match start {
            NoBound => 0,
            Includes(s) => match self.entries.binary_search_by(|(r, _)| r.cmp_point(s)) {
                Ok(i) => i,
                Err(_) => todo!(),
            },
        };
        let end = match end {
            NoBound => self.entries.len(),
            Includes(s) => self
                .entries
                .partition_point(|(r, _)| r.cmp_point(s).is_lt()),
        };
        let before = SubEntries::from_slice(&self.entries.get(..start).unwrap_or(&[]));
        let sub_entires = SubEntries::from_slice(&self.entries[start..end]);
        let after = SubEntries::from_slice(&self.entries.get(end..).unwrap_or(&[]));
        (sub_entires, (before, after))
    }

    pub fn get(&self, key: &K) -> Option<(Range<&K>, &V)>
    where
        K: PartialOrd,
    {
        self.get_bounded(key, Range::everything())
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn first_range(&self) -> Option<Range<&K>> {
        self.entries.first().map(|(r, _)| r.as_refs())
    }
}

impl<'e, K, V> SubEntries<'e, K, V> {
    fn from_slice(entries: &'e [(Range<K>, V)]) -> Self {
        Self { entries }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn get(&self, key: &K) -> Option<(Range<&'e K>, &'e V)>
    where
        K: PartialOrd,
    {
        let idx = self
            .entries
            .binary_search_by(|(range, _)| range.cmp_point(key))
            .expect("index not found");
        self.entries.get(idx).map(|(r, v)| (r.as_refs(), v))
    }

    pub fn iter(&self) -> impl Iterator<Item = (Range<&'e K>, &'e V)> {
        self.entries.iter().map(|(r, v)| (r.as_refs(), v))
    }
}

impl<K, V> Index<&K> for DenseRangeMap<K, V>
where
    K: PartialOrd,
{
    type Output = V;

    fn index(&self, key: &K) -> &Self::Output {
        self.get(key).unwrap().1
    }
}

impl<K> Range<K> {
    pub fn everything() -> Self {
        use RangeBound::*;
        Self {
            start: NoBound,
            end: NoBound,
        }
    }

    pub fn is_everything(&self) -> bool {
        matches!(&self.start, &NoBound) && matches!(&self.end, &NoBound)
    }

    pub fn start(&self) -> &RangeBound<K> {
        &self.start
    }

    pub fn end(&self) -> &RangeBound<K> {
        &self.end
    }

    pub fn as_bounds(&self) -> (Bound<&K>, Bound<&K>) {
        (self.start_bound(), self.end_bound())
    }

    pub fn as_refs(&self) -> Range<&K> {
        Range {
            start: self.start.as_ref(),
            end: self.end.as_ref(),
        }
    }

    pub fn cmp_point(&self, point: &K) -> Ordering
    where
        K: PartialOrd,
    {
        use Ordering::*;
        if self.start > point {
            return Greater;
        }

        if self.end < point {
            return Less;
        }

        return Equal;
    }

    pub fn contract_start(&mut self, start: K)
    where
        K: PartialOrd,
    {
        debug_assert!(self.start <= &start);
        debug_assert!(self.end > &start);
        self.start = Includes(start)
    }

    pub fn contract_end(&mut self, end: K)
    where
        K: PartialOrd,
    {
        debug_assert!(self.start < &end);
        debug_assert!(self.end >= &end);
        self.end = Includes(end)
    }
}

impl<K> RangeBounds<K> for Range<K> {
    fn start_bound(&self) -> Bound<&K> {
        use Bound::*;
        match &self.start {
            Includes(start) => Included(start),
            NoBound => Unbounded,
        }
    }

    fn end_bound(&self) -> Bound<&K> {
        use Bound::*;
        match &self.end {
            Includes(end) => Excluded(end),
            NoBound => Unbounded,
        }
    }
}

impl<K> PartialEq<K> for RangeBound<K>
where
    K: PartialOrd,
{
    fn eq(&self, other: &K) -> bool {
        use RangeBound::*;
        match self {
            NoBound => false,
            Includes(this) => this.eq(other),
        }
    }
}

impl<K> PartialEq<&K> for RangeBound<K>
where
    K: PartialOrd,
{
    fn eq(&self, other: &&K) -> bool {
        use RangeBound::*;
        match self {
            NoBound => false,
            Includes(this) => this.eq(other),
        }
    }
}

impl<K> PartialOrd<&K> for RangeBound<K>
where
    K: PartialOrd,
{
    fn partial_cmp(&self, other: &&K) -> Option<Ordering> {
        use RangeBound::*;
        match self {
            NoBound => Some(Ordering::Less),
            Includes(this) => this.partial_cmp(other),
        }
    }
}

impl<K> RangeBound<K> {
    fn as_ref(&self) -> RangeBound<&K> {
        match &self {
            NoBound => NoBound,
            Includes(k) => Includes(k),
        }
    }
}
