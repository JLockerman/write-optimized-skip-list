use std::{
    cmp::Ordering,
    ops::{Bound, Index, RangeBounds},
};

use itertools::zip_eq;

use self::RangeBound::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseRangeMap<K, V> {
    keys: Vec<RangeBound<K>>,
    values: Vec<V>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct SubEntries<'e, K, V> {
    keys: &'e [RangeBound<K>],
    values: &'e [V],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Range<K> {
    start: RangeBound<K>,
    end: RangeBound<K>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum RangeBound<K> {
    NegInf,
    Includes(K),
    PosInf,
}

impl<K, V> DenseRangeMap<K, V> {
    pub fn new() -> Self {
        Self {
            keys: vec![],
            values: vec![],
        }
    }

    pub fn get_bounded(&self, key: &K, bound: Range<&K>) -> Option<(Range<&K>, &V)>
    where
        K: Ord,
    {
        self.sub_entries(bound).0.get(key)
    }

    pub fn sub_entries(
        &self,
        bound: Range<&K>,
    ) -> (
        SubEntries<'_, K, V>,
        (Option<RangeBound<&K>>, Option<RangeBound<&K>>),
    )
    where
        K: Ord,
    {
        let empty = SubEntries {
            keys: &[],
            values: &[],
        };
        if bound.is_everything() {
            let everything = SubEntries {
                keys: &self.keys,
                values: &self.values,
            };
            return (everything, (None, None));
        }

        if self.keys.is_empty() {
            return (empty, (None, None));
        }

        let Range { start, end } = bound;
        // 1. find the largest range entry <= start
        let after_start_idx = self.keys.partition_point(|k| k.as_ref() <= start);
        // TODO
        // if after_start_idx == 0 {
        //     return (empty, (None, self.keys.first().map(RangeBound::as_ref)));
        // }
        let start_idx = after_start_idx.saturating_sub(1);
        let possible_ends = &self.keys[start_idx..];
        let possible_values = &self.values[start_idx..];

        // 2. find the smallest entry > end
        let end_idx = possible_ends.partition_point(|k| k.as_ref() < end);

        let subrange = SubEntries {
            keys: &possible_ends[..=end_idx],
            values: &possible_values[..end_idx],
        };

        // TODO this is dumb
        let before = subrange.keys.first().map(RangeBound::as_ref);
        let after = subrange.keys.last().map(RangeBound::as_ref);

        (subrange, (before, after))

        // let before_keys = &self.keys[..=start_idx];
        // let before_values = &self.values[..start_idx];
        // let before = SubEntries {
        //     keys: before_keys,
        //     values: before_values,
        // };

        // let possible_keys = &self.keys[start_idx..];
        // let possible_values = &self.values[start_idx..];

        // let end_idx = possible_keys.partition_point(|k| k.as_ref() < end);

        // let range_keys = &possible_keys[..=end_idx];
        // let range_values = &possible_values[..end_idx];
        // let sub_range = SubEntries {
        //     keys: range_keys,
        //     values: range_values,
        // };

        // let after_keys = &possible_keys[end_idx..];
        // let after_values = &possible_values[end_idx..];
        // let after = SubEntries {
        //     keys: after_keys,
        //     values: after_values,
        // };

        // (sub_range, (before, after))
    }

    pub fn get(&self, key: &K) -> Option<(Range<&K>, &V)>
    where
        K: Ord,
    {
        self.get_bounded(key, Range::everything())
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn range(&self) -> Range<&K> {
        Range::new(
            self.keys.first().unwrap().as_ref(),
            self.keys.last().unwrap().as_ref(),
        )
    }

    pub fn iter(&self) -> impl Iterator<Item = (Range<&K>, &V)>
    where
        K: Ord,
    {
        self.sub_entries(Range::everything()).0.iter()
    }
}

impl<K, V> From<(Range<K>, V)> for DenseRangeMap<K, V> {
    fn from((range, value): (Range<K>, V)) -> Self {
        Self {
            keys: vec![range.start, range.end],
            values: vec![value],
        }
    }
}

impl<'e, K, V> SubEntries<'e, K, V> {
    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    pub fn get(&self, key: &K) -> Option<(Range<&'e K>, &'e V)>
    where
        K: PartialOrd,
    {
        if self.is_empty() {
            return None;
        }
        // the entries are logically a list of (low_bound, value, upper_bound)
        let idx = self.keys.partition_point(|k| k <= &key);

        if idx == 0 || idx >= self.keys.len() {
            return None;
        }

        let lower = self.keys[idx - 1].as_ref();
        let upper = self.keys[idx].as_ref();
        let val = &self.values[idx - 1];

        Some((Range::new(lower, upper), val))
    }

    pub fn keys(&self) -> impl Iterator<Item = RangeBound<&'e K>> {
        self.keys.iter().map(RangeBound::as_ref)
    }

    pub fn leads(&self) -> impl Iterator<Item = RangeBound<&'e K>> {
        let end = self.keys.len().saturating_sub(1);
        return self.keys[..end].iter().map(RangeBound::as_ref);
    }

    pub fn iter(&self) -> impl Iterator<Item = (Range<&'e K>, &'e V)> {
        let keys = self
            .keys
            .windows(2)
            .map(|w| Range::new(w[0].as_ref(), w[1].as_ref()));
        zip_eq(keys, self.values)
    }

    pub fn cloned(&self) -> DenseRangeMap<K, V>
    where
        K: Clone,
        V: Clone,
    {
        DenseRangeMap {
            keys: self.keys.to_owned(),
            values: self.values.to_vec(),
        }
    }
}

impl<K, V> Index<&K> for DenseRangeMap<K, V>
where
    K: Ord,
{
    type Output = V;

    fn index(&self, key: &K) -> &Self::Output {
        self.get(key).unwrap().1
    }
}

impl<K, V> Clone for SubEntries<'_, K, V> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, V> Copy for SubEntries<'_, K, V> {}

#[allow(dead_code)]
impl<K> Range<K> {
    fn new(start: RangeBound<K>, end: RangeBound<K>) -> Self {
        Self { start, end }
    }

    pub fn merge(a: Range<K>, b: Range<K>) -> Range<K>
    where
        K: Ord,
    {
        assert!(&a.end == &b.start);
        Self {
            start: a.start,
            end: b.end,
        }
    }

    pub fn everything() -> Self {
        use RangeBound::*;
        Self {
            start: NegInf,
            end: PosInf,
        }
    }

    pub fn is_everything(&self) -> bool {
        matches!(&self.start, &NegInf) && matches!(&self.end, &PosInf)
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

    pub fn inner(self) -> (RangeBound<K>, RangeBound<K>) {
        (self.start, self.end)
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

    fn contains_range(self, bound: Range<K>) -> bool
    where
        K: Ord,
    {
        self.start <= bound.start && self.end >= bound.end
    }

    pub fn contract_start(&mut self, start: RangeBound<K>)
    where
        K: Ord,
    {
        debug_assert!(self.start <= start);
        debug_assert!(self.end > start);
        self.start = start
    }

    pub fn contract_end(&mut self, end: RangeBound<K>)
    where
        K: Ord,
    {
        debug_assert!(self.start < end);
        debug_assert!(self.end >= end);
        self.end = end
    }

    pub fn extend_end(&mut self, end: RangeBound<K>)
    where
        K: Ord,
    {
        debug_assert!(self.end < end);
        self.end = end
    }

    pub fn clamp_to(mut self, bound: Self) -> Self
    where
        K: Ord,
    {
        if self.start < bound.start {
            self.start = bound.start
        }
        if self.end > bound.end {
            self.end = bound.end
        }
        self
    }
}

impl<K> RangeBounds<K> for Range<K> {
    fn start_bound(&self) -> Bound<&K> {
        use Bound::*;
        match &self.start {
            Includes(start) => Included(start),
            NegInf | PosInf => Unbounded,
        }
    }

    fn end_bound(&self) -> Bound<&K> {
        use Bound::*;
        match &self.end {
            Includes(end) => Excluded(end),
            NegInf | PosInf => Unbounded,
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
            NegInf | PosInf => false,
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
            NegInf | PosInf => false,
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
            NegInf => Some(Ordering::Less),
            Includes(this) => this.partial_cmp(other),
            PosInf => Some(Ordering::Greater),
        }
    }
}

impl<K> PartialOrd for RangeBound<K>
where
    K: Ord,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<K> Ord for RangeBound<K>
where
    K: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        use Ordering::*;
        use RangeBound::*;
        match (self, other) {
            (NegInf, NegInf) => Equal,
            (PosInf, PosInf) => Equal,
            (NegInf, _) | (_, PosInf) => Less,
            (PosInf, _) | (_, NegInf) => Greater,
            (Includes(this), Includes(other)) => this.cmp(other),
        }
    }
}

impl<K> RangeBound<K> {
    fn as_ref(&self) -> RangeBound<&K> {
        match &self {
            NegInf => NegInf,
            Includes(k) => Includes(k),
            PosInf => PosInf,
        }
    }
}

impl<K> RangeBound<&K> {
    pub fn cloned(&self) -> RangeBound<K>
    where
        K: Clone,
    {
        match &self {
            NegInf => NegInf,
            Includes(k) => Includes(K::clone(k)),
            PosInf => PosInf,
        }
    }
}

impl<K> From<(RangeBound<K>, RangeBound<K>)> for Range<K> {
    fn from((start, end): (RangeBound<K>, RangeBound<K>)) -> Self {
        Self { start, end }
    }
}

impl<K> From<(K, RangeBound<K>)> for Range<K> {
    fn from((start, end): (K, RangeBound<K>)) -> Self {
        Self {
            start: Includes(start),
            end,
        }
    }
}

impl<K> From<(RangeBound<K>, K)> for Range<K> {
    fn from((start, end): (RangeBound<K>, K)) -> Self {
        Self {
            start,
            end: Includes(end),
        }
    }
}

impl<K> From<(K, K)> for Range<K> {
    fn from((start, end): (K, K)) -> Self {
        Self {
            start: Includes(start),
            end: Includes(end),
        }
    }
}

impl<K> From<K> for RangeBound<K> {
    fn from(value: K) -> Self {
        Includes(value)
    }
}

pub fn map_builder<K, M>() -> KeyBuilder<K, M> {
    KeyBuilder { keys: vec![] }
}

pub struct KeyBuilder<K, M> {
    keys: Vec<(Vec<RangeBound<K>>, M)>,
}

impl<K, M> KeyBuilder<K, M>
where
    K: Clone,
{
    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    pub fn start_new_map_with(&mut self, key: RangeBound<K>, meta: M) -> &mut Self {
        if let Some((prev, _)) = self.keys.last_mut() {
            prev.push(key.clone())
        }
        self.keys.push((vec![key], meta));
        self
    }

    #[track_caller]
    pub fn add_key_to_map(&mut self, key: RangeBound<K>) -> &mut Self {
        self.keys.last_mut().unwrap().0.push(key);
        self
    }

    pub fn finish_with<V>(mut self, key: RangeBound<K>) -> ValueBuilder<K, V, M> {
        self.add_key_to_map(key);
        self.finish()
    }

    pub fn finish<V>(self) -> ValueBuilder<K, V, M> {
        let num_maps = self.keys.len();
        ValueBuilder {
            keys: self.keys,
            values: (0..num_maps).map(|_| vec![]).collect(),
            current_values: 0,
            range_start: 0,
            range_end: 1,
        }
    }
}

pub struct ValueBuilder<K, V, M> {
    keys: Vec<(Vec<RangeBound<K>>, M)>,
    values: Vec<Vec<V>>,
    current_values: usize,
    range_start: usize,
    range_end: usize,
}

impl<K, V, M> ValueBuilder<K, V, M>
where
    K: Ord + Clone,
    V: Clone,
{
    pub fn current_range(&self) -> Option<Range<&K>> {
        if self.current_values >= self.keys.len() {
            return None;
        }
        let keys = &self.keys[self.current_values].0;
        (self.range_end < keys.len()).then(|| {
            Range::new(
                keys[self.range_start].as_ref(),
                keys[self.range_end].as_ref(),
            )
        })
    }

    pub fn next_range_in_map(&self) -> Option<Range<&K>> {
        if self.current_values >= self.keys.len() {
            return None;
        }
        let keys = &self.keys[self.current_values].0;
        (self.range_end + 1 < keys.len()).then(|| {
            Range::new(
                keys[self.range_end].as_ref(),
                keys[self.range_end + 1].as_ref(),
            )
        })
    }

    pub fn increment_range(&mut self) {
        self.range_end += 1;
    }

    pub fn add_value(&mut self, value: V) -> &mut Self {
        self.values[self.current_values]
            .extend((self.range_start..self.range_end).map(|_| value.clone()));

        if self.range_end + 1 < self.keys[self.current_values].0.len() {
            self.range_start = self.range_end;
            self.range_end = self.range_start + 1;
        } else {
            self.current_values += 1;
            self.range_start = 0;
            self.range_end = 1;
        }
        self
    }

    pub fn add_value_for_range(&mut self, range: Range<&K>, value: V) {
        let mut first = true;
        loop {
            let Some(current_range) = self.current_range() else {
                break;
            };

            // TODO double check
            if !range.contains_range(current_range)
                && !current_range.contains_range(range)
                && !(matches!(&current_range.start, &NegInf) && current_range.end == range.start)
            {
                break;
            }

            self.add_value(value.clone());
            first = false;
        }
        debug_assert!(!first);
    }

    pub fn finish(self) -> impl ExactSizeIterator<Item = (DenseRangeMap<K, V>, M)> {
        debug_assert_eq!(self.keys.len(), self.values.len());
        zip_eq(self.keys, self.values).map(|((keys, meta), values)| {
            debug_assert!(
                (keys.len() == 0 && values.len() == 0) || (values.len() + 1 == keys.len()),
                "keys: {}, vals: {}",
                keys.len(),
                values.len()
            );
            (DenseRangeMap { keys, values }, meta)
        })
    }
}

impl<K> std::fmt::Debug for RangeBound<K>
where
    K: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NegInf => write!(f, "-∞"),
            Self::Includes(arg0) => write!(f, "{:?}", arg0),
            Self::PosInf => write!(f, "∞"),
        }
    }
}

#[cfg(test)]
mod test {
    use super::{map_builder, DenseRangeMap, Range, RangeBound, SubEntries};
    use itertools::Itertools;
    use RangeBound::*;

    macro_rules! dense_range_map {
        ( $first_key:expr $(, $val:expr, $key:expr)+  ) => {
            DenseRangeMap {
                keys: {
                    let keys = vec![ $first_key $(, $key )+ ];
                    assert!(keys.windows(2).all(|w| w[0] < w[1]));
                    keys
                },
                values: vec![ $( $val ),+ ]
            }
        };
    }

    macro_rules! sub_entries {
        ( $first_key:expr $(, $val:expr, $key:expr)*  ) => {
            SubEntries {
                keys: {
                    let keys = &[ $first_key $(, $key )* ];
                    assert!(keys.windows(2).all(|w| w[0] < w[1]));
                    keys
                },
                values: &[ $( $val ),* ]
            }
        };
    }

    #[test]
    fn constructor_macro() {
        assert_eq!(
            dense_range_map!(NegInf, 101, PosInf),
            DenseRangeMap {
                keys: vec![NegInf::<u32>, PosInf],
                values: vec![101],
            }
        );

        assert_eq!(
            dense_range_map!(NegInf, 101, Includes(42), 22, PosInf),
            DenseRangeMap {
                keys: vec![NegInf, Includes(42), PosInf],
                values: vec![101, 22],
            }
        );

        assert_eq!(
            dense_range_map!(NegInf, 101, Includes(42), 22, Includes(1000), 0, PosInf),
            DenseRangeMap {
                keys: vec![NegInf, Includes(42), Includes(1000), PosInf],
                values: vec![101, 22, 0],
            }
        );
    }

    #[test]
    fn single_range() {
        let map = dense_range_map!(NegInf, 101, PosInf);
        let range = Range::new(NegInf, PosInf);
        assert_eq!(map.get(&0), Some((range, &101)));
        assert_eq!(map.get(&10), Some((range, &101)));

        for i in 0..102 {
            assert_eq!(map.get(&i), Some((range, &101)));
        }
    }

    #[test]
    fn two_ranges() {
        let map = dense_range_map!(NegInf, 11, Includes(10), 2, PosInf);
        let first_range = Range::new(NegInf, Includes(&10));
        assert_eq!(map.get(&0), Some((first_range, &11)));

        let second_range = Range::new(Includes(&10), PosInf);
        assert_eq!(map.get(&10), Some((second_range, &2)));

        for i in 0..10 {
            assert_eq!(map.get(&i), Some((first_range, &11)));
        }

        for i in 10..100 {
            assert_eq!(map.get(&i), Some((second_range, &2)));
        }
    }

    #[test]
    fn three_ranges() {
        let map = dense_range_map!(NegInf, 11, Includes(10), 2, Includes(57), 333, PosInf);
        let first_range = Range::new(NegInf, Includes(&10));
        assert_eq!(map.get(&0), Some((first_range, &11)));

        let second_range = Range::new(Includes(&10), Includes(&57));
        assert_eq!(map.get(&10), Some((second_range, &2)));

        let third_range = Range::new(Includes(&57), PosInf);
        assert_eq!(map.get(&57), Some((third_range, &333)));

        for i in 0..10 {
            assert_eq!(map.get(&i), Some((first_range, &11)));
        }

        for i in 10..57 {
            assert_eq!(map.get(&i), Some((second_range, &2)));
        }

        for i in 57..201 {
            assert_eq!(map.get(&i), Some((third_range, &333)));
        }
    }

    #[test]
    fn sub_entires() {
        let map = dense_range_map!(NegInf, 11, Includes(10), 2, Includes(57), 333, PosInf);

        let (a, (b, c)) = map.sub_entries((NegInf, Includes(&10)).into());
        assert_eq!(a, sub_entries!(NegInf, 11, Includes(10)));
        assert_eq!(b, Some(NegInf));
        assert_eq!(c, Some(Includes(&10)));

        let first_range = Range::new(NegInf, Includes(&10));
        for i in 0..10 {
            assert_eq!(a.get(&i), Some((first_range, &11)));
        }

        let second_range = Range::new(Includes(&10), Includes(&57));
        for i in 10..57 {
            assert_eq!(a.get(&i), None);
        }

        let third_range = Range::new(Includes(&57), PosInf);
        for i in 57..202 {
            assert_eq!(a.get(&i), None);
        }
    }

    #[test]
    fn builder() {
        let mut key_builder = map_builder();
        key_builder
            .start_new_map_with(Includes(10), 1)
            .add_key_to_map(Includes(21))
            .add_key_to_map(Includes(100));
        let mut value_builder = key_builder.finish_with(Includes(1000));
        value_builder.add_value(101);
        value_builder.add_value(202);
        value_builder.add_value(3);
        let maps = value_builder.finish().collect_vec();
        assert_eq!(
            maps,
            vec![(
                dense_range_map!(
                    Includes(10),
                    101,
                    Includes(21),
                    202,
                    Includes(100),
                    3,
                    Includes(1000)
                ),
                1
            )]
        );
    }

    #[test]
    fn builder2() {
        let mut key_builder = map_builder();
        key_builder
            .start_new_map_with(Includes(10), 2)
            .add_key_to_map(Includes(21))
            .start_new_map_with(Includes(100), 3);
        let mut value_builder = key_builder.finish_with(Includes(1000));
        value_builder.add_value(101);
        value_builder.add_value(202);
        value_builder.add_value(3);
        let maps = value_builder.finish().collect_vec();
        assert_eq!(
            maps,
            vec![
                (
                    dense_range_map!(Includes(10), 101, Includes(21), 202, Includes(100)),
                    2
                ),
                (dense_range_map!(Includes(100), 3, Includes(1000)), 3)
            ]
        );
    }

    #[test]
    fn builder_incremental() {
        let mut key_builder = map_builder();
        key_builder
            .start_new_map_with(Includes(10), true)
            .add_key_to_map(Includes(21))
            .add_key_to_map(Includes(55))
            .start_new_map_with(Includes(100), false)
            .add_key_to_map(Includes(107));
        let mut value_builder = key_builder.finish_with(Includes(1000));
        assert_eq!(
            value_builder.current_range(),
            Some((Includes(&10), Includes(&21)).into())
        );
        assert_eq!(
            value_builder.next_range_in_map(),
            Some((Includes(&21), Includes(&55)).into())
        );

        value_builder.increment_range();

        assert_eq!(
            value_builder.current_range(),
            Some((Includes(&10), Includes(&55)).into())
        );
        assert_eq!(
            value_builder.next_range_in_map(),
            Some((Includes(&55), Includes(&100)).into())
        );

        value_builder.add_value(1);

        assert_eq!(
            value_builder.current_range(),
            Some((Includes(&55), Includes(&100)).into())
        );
        assert_eq!(value_builder.next_range_in_map(), None,);

        value_builder.add_value(2);

        assert_eq!(
            value_builder.current_range(),
            Some((Includes(&100), Includes(&107)).into())
        );
        assert_eq!(
            value_builder.next_range_in_map(),
            Some((Includes(&107), Includes(&1000)).into())
        );

        value_builder.add_value(3);

        assert_eq!(
            value_builder.current_range(),
            Some((Includes(&107), Includes(&1000)).into())
        );

        assert_eq!(value_builder.next_range_in_map(), None);

        value_builder.add_value(444);

        assert_eq!(value_builder.current_range(), None,);
        assert_eq!(value_builder.next_range_in_map(), None);

        let maps = value_builder.finish().collect_vec();
        assert_eq!(
            maps,
            vec![
                (
                    dense_range_map!(
                        Includes(10),
                        1,
                        Includes(21),
                        1,
                        Includes(55),
                        2,
                        Includes(100)
                    ),
                    true
                ),
                (
                    dense_range_map!(Includes(100), 3, Includes(107), 444, Includes(1000)),
                    false
                )
            ]
        );
    }

    #[test]
    fn builder_ranged() {
        let mut key_builder = map_builder();
        key_builder
            .start_new_map_with(Includes(10), false)
            .add_key_to_map(Includes(21))
            .add_key_to_map(Includes(55))
            .start_new_map_with(Includes(100), true)
            .add_key_to_map(Includes(107));
        let mut value_builder = key_builder.finish_with(Includes(1000));
        assert_eq!(
            value_builder.current_range(),
            Some((Includes(&10), Includes(&21)).into())
        );
        assert_eq!(
            value_builder.next_range_in_map(),
            Some((Includes(&21), Includes(&55)).into())
        );

        value_builder.add_value_for_range((Includes(&10), Includes(&55)).into(), 1);

        assert_eq!(
            value_builder.current_range(),
            Some((Includes(&55), Includes(&100)).into())
        );
        assert_eq!(value_builder.next_range_in_map(), None);

        value_builder.add_value_for_range((Includes(&55), Includes(&100)).into(), 2);

        assert_eq!(
            value_builder.current_range(),
            Some((Includes(&100), Includes(&107)).into())
        );
        assert_eq!(
            value_builder.next_range_in_map(),
            Some((Includes(&107), Includes(&1000)).into())
        );

        value_builder.add_value_for_range((Includes(&100), Includes(&107)).into(), 3);

        assert_eq!(
            value_builder.current_range(),
            Some((Includes(&107), Includes(&1000)).into())
        );

        assert_eq!(value_builder.next_range_in_map(), None);

        value_builder.add_value_for_range((Includes(&107), Includes(&1000)).into(), 444);

        assert_eq!(value_builder.current_range(), None,);
        assert_eq!(value_builder.next_range_in_map(), None);

        let maps = value_builder.finish().collect_vec();
        assert_eq!(
            maps,
            vec![
                (
                    dense_range_map!(
                        Includes(10),
                        1,
                        Includes(21),
                        1,
                        Includes(55),
                        2,
                        Includes(100)
                    ),
                    false
                ),
                (
                    dense_range_map!(Includes(100), 3, Includes(107), 444, Includes(1000)),
                    true
                )
            ]
        );
    }
}
