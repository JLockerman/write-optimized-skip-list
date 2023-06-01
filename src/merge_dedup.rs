use std::{
    cmp::{max, Ordering},
    iter::{FusedIterator, Peekable},
};

pub fn dedup_all_but_last_by<T>(buffer: &mut Vec<T>, mut eq: impl FnMut(&T, &T) -> bool) {
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

// based on itertools MergeBy but guarantees that on ties the second iterator's element is taken
#[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
pub struct MergeDedup<I, J, F>
where
    I: Iterator,
    J: Iterator<Item = I::Item>,
{
    a: Peekable<I>,
    b: Peekable<J>,
    fused: Option<Ordering>,
    cmp: F,
}

pub fn merge_dedup<I, J, F>(a: I, b: J, cmp: F) -> MergeDedup<I::IntoIter, J::IntoIter, F>
where
    I: IntoIterator,
    J: IntoIterator<Item = I::Item>,
    F: FnMut(&I::Item, &I::Item) -> Ordering,
{
    MergeDedup {
        a: a.into_iter().peekable(),
        b: b.into_iter().peekable(),
        fused: None,
        cmp,
    }
}

impl<I, J, F> Clone for MergeDedup<I, J, F>
where
    I: Iterator,
    J: Iterator<Item = I::Item>,
    Peekable<I>: Clone,
    Peekable<J>: Clone,
    F: Clone,
{
    fn clone(&self) -> Self {
        Self {
            a: self.a.clone(),
            b: self.b.clone(),
            fused: self.fused.clone(),
            cmp: self.cmp.clone(),
        }
    }
}

impl<I, J, F> Iterator for MergeDedup<I, J, F>
where
    I: Iterator,
    J: Iterator<Item = I::Item>,
    F: FnMut(&I::Item, &I::Item) -> Ordering,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        use Ordering::*;
        let ordering = match self.fused {
            Some(ord) => ord,
            None => match (self.a.peek(), self.b.peek()) {
                (Some(a), Some(b)) => (self.cmp)(a, b),
                (Some(_), None) => {
                    self.fused = Some(Less);
                    Less
                }
                (None, Some(_)) => {
                    self.fused = Some(Greater);
                    Greater
                }
                (None, None) => return None,
            },
        };
        match ordering {
            Equal => {
                _ = self.a.next();
                self.b.next()
            }
            Less => self.a.next(),
            Greater => self.b.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let a = self.a.size_hint();
        let b = self.b.size_hint();
        // Not ExactSizeIterator because size may shrink
        let min = max(a.0, b.0);
        let max = match (a.1, b.1) {
            (Some(x), Some(y)) => x.checked_add(y),
            _ => None,
        };

        (min, max)
    }
}

impl<I, J, F> FusedIterator for MergeDedup<I, J, F>
where
    I: FusedIterator,
    J: FusedIterator<Item = I::Item>,
    F: FnMut(&I::Item, &I::Item) -> Ordering,
{
}
