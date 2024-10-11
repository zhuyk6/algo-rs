//! This module provides the [`SegmentTree`] and [`SegmentTreeBuilder`].
//!
//! This [`SegmentTree`] uses [`B`] as the type of index,
//! and [`Val`] as the type of data.
//!
//! A segment tree maintains the data in 1-D, like an array.
//! Compared with array, the segment tree can update and query
//! data in a interval `[l, r]` in time $O(\log N)$.
//!
//! Here we support:
//!
//! - Modify point: [`SegmentTree::modify_point`]
//! - Segment add: [`SegmentTree::add_segment`]
//! - Segment set: [`SegmentTree::set_segment`]
//! - Segment query: [`SegmentTree::query_sum`], [`SegmentTree::query_max`]
//!
//! # Examples
//!
//! ```
//! # use algo_rs::segment_tree::SegmentTreeBuilder;
//!
//! let mut tree = SegmentTreeBuilder::new()
//!             .interval(0, 3)
//!             .fill(0)
//!             .build()
//!             .unwrap();
//!
//! assert_eq!(tree.query_max(1, 2), 0);
//!
//! tree.modify_point(1, |_| 5);
//! assert_eq!(tree.query_max(1, 3), 5);
//!
//! tree.add_segment(0, 2, 1);
//! assert_eq!(tree.query_sum(1, 2), 7);
//! ```

use std::cell::RefCell;

/// Index type.
pub type B = isize;
/// Value type.
pub type Val = i32;

/// Data type that the inner node stores.
#[derive(Debug, Clone)]
struct Data {
    /// length of the interval
    len: Val,
    /// sum of value in the interval
    sum: Val,
    /// maximum of value in the interval
    max: Val,
    /// whether this interval is added by `delta`
    tag_delta: Option<Val>,
    /// whether this interval is set to `set_val`
    tag_set: Option<Val>,
}

impl Data {
    /// Creates a new [`Data`].
    #[must_use]
    #[inline]
    fn new(left: B, right: B, fill: Val) -> Self {
        let len = (right - left + 1) as Val;
        Data {
            len,
            sum: fill * len,
            max: fill,
            tag_delta: None,
            tag_set: None,
        }
    }

    /// Merge data from left and right segments.
    #[inline]
    fn merge(&mut self, left: &Data, right: &Data) {
        self.clear_tag();

        self.sum = left.sum + right.sum;
        self.max = Val::max(left.max, right.max);
    }

    /// Push down tags to children.
    /// First process [Data::tag_set], then [Data::tag_delta].
    /// Since [Data::set] will clear previous [Data::tag_delta],
    /// but [Data::add] will keep previous [Data::tag_set].
    #[inline]
    fn push_down(&self, node: &mut Node) {
        if let Some(&set_val) = self.tag_set.as_ref() {
            match node {
                Node::Leaf { val, .. } => {
                    *val = set_val;
                }
                Node::Inner { data, .. } => {
                    data.set(set_val);
                }
            }
        }
        if let Some(&delta) = self.tag_delta.as_ref() {
            match node {
                Node::Leaf { val, .. } => {
                    *val += delta;
                }
                Node::Inner { data, .. } => {
                    data.add(delta);
                }
            }
        }
    }

    /// Clear tags.
    #[inline]
    fn clear_tag(&mut self) {
        self.tag_delta.take();
        self.tag_set.take();
    }

    /// Segment add, including set [Data::tag_delta].
    #[inline]
    fn add(&mut self, delta: Val) {
        if let Some(d) = self.tag_delta.take() {
            self.tag_delta = Some(d + delta);
        } else {
            self.tag_delta = Some(delta);
        }

        self.max += delta;
        self.sum += delta * self.len;
    }

    /// Segment set, including set [Data::tag_set].
    #[inline]
    fn set(&mut self, set_val: Val) {
        self.tag_set = Some(set_val);
        self.tag_delta = None;

        self.max = set_val;
        self.sum = set_val * self.len;
    }
}

/// Node type in the segment tree.
#[derive(Debug, Clone)]
enum Node {
    /// Leaf of the segment tree
    Leaf {
        /// position or index
        #[allow(unused)]
        pos: B,
        /// value that stores
        val: Val,
    },
    /// Inner node of the segment tree,
    /// maintains the interval `left..=right`.
    Inner {
        left: B,
        right: B,
        /// left child
        lc: Box<Node>,
        /// right child
        rc: Box<Node>,
        data: Data,
    },
}

#[allow(dead_code)]
impl Node {
    /// Build the segment tree of interval `[left, right]`.
    ///
    /// # Panics
    ///
    /// Panics if `left` > `right`.
    #[must_use]
    fn build(left: B, right: B, fill: Val) -> Box<Node> {
        match left.cmp(&right) {
            std::cmp::Ordering::Less => {
                let mid = (left + right) >> 1;
                Box::new(Node::Inner {
                    left,
                    right,
                    lc: Node::build(left, mid, fill),
                    rc: Node::build(mid + 1, right, fill),
                    data: Data::new(left, right, fill),
                })
            }
            std::cmp::Ordering::Equal => Box::new(Node::Leaf {
                pos: left,
                val: fill,
            }),
            std::cmp::Ordering::Greater => panic!(
                "left should be less than or equal to right, but {} and {} given.",
                left, right
            ),
        }
    }

    /// Returns the data of this [`Node`].
    #[inline]
    fn data(&self) -> Data {
        match self {
            Node::Leaf { val, .. } => Data {
                len: 1,
                sum: *val,
                max: *val,
                tag_delta: None,
                tag_set: None,
            },
            Node::Inner { data, .. } => data.clone(),
        }
    }

    /// Update `data` according to `lc` and `rc`.
    #[inline]
    fn update(data: &mut Data, lc: &Node, rc: &Node) {
        data.merge(&lc.data(), &rc.data());
    }

    /// Push down lazy tags to `lc` and `rc`.
    #[inline]
    fn push_down(data: &mut Data, lc: &mut Node, rc: &mut Node) {
        data.push_down(lc);
        data.push_down(rc);
        data.clear_tag();
    }

    /// Modify `pos` according to `f`.
    fn modify_point<F>(&mut self, pos: B, f: F)
    where
        F: Fn(Val) -> Val,
    {
        match self {
            Node::Leaf { val, .. } => {
                *val = f(*val);
            }
            Node::Inner {
                ref left,
                ref right,
                lc,
                rc,
                data,
            } => {
                Node::push_down(data, lc, rc);

                let mid = (left + right) >> 1;
                if pos <= mid {
                    lc.modify_point(pos, f);
                } else {
                    rc.modify_point(pos, f);
                }

                Node::update(data, lc, rc);
            }
        }
    }

    /// Add `delta` to each value of the interval `l_bound..=r_bound`.
    fn add_segment(&mut self, l_bound: B, r_bound: B, delta: Val) {
        match self {
            Node::Leaf { val, .. } => {
                *val += delta;
            }
            Node::Inner {
                ref left,
                ref right,
                lc,
                rc,
                data,
            } => {
                // [l_bound, r_bound] contains [left, right]
                if l_bound <= *left && *right <= r_bound {
                    data.add(delta);
                    return;
                }

                Node::push_down(data, lc, rc);

                let mid = (left + right) >> 1;
                if l_bound <= mid {
                    lc.add_segment(l_bound, r_bound, delta);
                }
                if mid < r_bound {
                    rc.add_segment(l_bound, r_bound, delta);
                }

                Node::update(data, lc, rc);
            }
        }
    }

    /// Set each value to `set_val` of the interval `l_bound..=r_bound`.
    fn set_segment(&mut self, l_bound: B, r_bound: B, set_val: Val) {
        match self {
            Node::Leaf { val, .. } => {
                *val = set_val;
            }
            Node::Inner {
                ref left,
                ref right,
                lc,
                rc,
                data,
            } => {
                // [l_bound, r_bound] contains [left, right]
                if l_bound <= *left && *right <= r_bound {
                    data.set(set_val);
                    return;
                }

                Node::push_down(data, lc, rc);

                let mid = (left + right) >> 1;
                if l_bound <= mid {
                    lc.set_segment(l_bound, r_bound, set_val);
                }
                if mid < r_bound {
                    rc.set_segment(l_bound, r_bound, set_val);
                }

                Node::update(data, lc, rc);
            }
        }
    }

    /// Query the sum of the interval `l_bound..=r_bound`.
    fn query_sum(&mut self, l_bound: B, r_bound: B) -> Val {
        match self {
            Node::Leaf { val, .. } => *val,
            Node::Inner {
                ref left,
                ref right,
                lc,
                rc,
                data,
            } => {
                if l_bound <= *left && *right <= r_bound {
                    return data.sum;
                }

                Node::push_down(data, lc, rc);

                let mid = (left + right) >> 1;
                let mut ret = Val::default();
                if l_bound <= mid {
                    ret += lc.query_sum(l_bound, r_bound);
                }
                if r_bound > mid {
                    ret += rc.query_sum(l_bound, r_bound);
                }

                Node::update(data, lc, rc);
                ret
            }
        }
    }

    /// Query the maximum of the interval `l_bound..=r_bound`.
    fn query_max(&mut self, l_bound: B, r_bound: B) -> Val {
        match self {
            Node::Leaf { val, .. } => *val,
            Node::Inner {
                ref left,
                ref right,
                lc,
                rc,
                data,
            } => {
                if l_bound <= *left && *right <= r_bound {
                    return data.max;
                }

                Node::push_down(data, lc, rc);

                let mid = (left + right) >> 1;
                let mut ret = Val::MIN;
                if l_bound <= mid {
                    ret = ret.max(lc.query_max(l_bound, r_bound));
                }
                if r_bound > mid {
                    ret = ret.max(rc.query_max(l_bound, r_bound));
                }

                Node::update(data, lc, rc);
                ret
            }
        }
    }
}

/// Segment tree.
#[derive(Debug, Clone)]
pub struct SegmentTree {
    left: B,
    right: B,
    root: RefCell<Box<Node>>,
}

#[allow(unused)]
impl SegmentTree {
    /// Check `pos` in the interval.
    #[inline]
    fn check_bound(&self, pos: B) -> bool {
        (self.left..=self.right).contains(&pos)
    }

    /// Modify value at `pos` according to the function `f`.
    ///
    /// # Panics
    ///
    /// Panics if `pos` not in the interval.
    pub fn modify_point<F>(&mut self, pos: B, f: F)
    where
        F: Fn(Val) -> Val,
    {
        assert!(self.check_bound(pos));
        self.root.borrow_mut().modify_point(pos, f);
    }

    /// Add `delta` to each value in the interval `l_bound..=r_bound`.
    ///
    /// # Panics
    ///
    /// Panics if `l_bound..=r_bound` not in the interval.
    pub fn add_segment(&mut self, l_bound: B, r_bound: B, delta: Val) {
        assert!(l_bound <= r_bound && self.check_bound(l_bound) && self.check_bound(r_bound));
        self.root.borrow_mut().add_segment(l_bound, r_bound, delta);
    }

    /// Set each value of the interval `l_bound..=r_bound` to `set_val`.
    ///
    /// # Panics
    ///
    /// Panics if `l_bound..=r_bound` not in the interval.
    pub fn set_segment(&mut self, l_bound: B, r_bound: B, set_val: Val) {
        assert!(l_bound <= r_bound && self.check_bound(l_bound) && self.check_bound(r_bound));
        self.root
            .borrow_mut()
            .set_segment(l_bound, r_bound, set_val);
    }

    /// Query the maximum of the interval `l_bound..=r_bound`.
    ///
    /// # Panics
    ///
    /// Panics if `l_bound..=r_bound` not in the interval.
    pub fn query_max(&self, l_bound: B, r_bound: B) -> Val {
        assert!(l_bound <= r_bound && self.check_bound(l_bound) && self.check_bound(r_bound));
        self.root.borrow_mut().query_max(l_bound, r_bound)
    }

    /// Query the sum of the interval `l_bound..=r_bound`.
    ///
    /// # Panics
    ///
    /// Panics if `l_bound..=r_bound` not in the interval.
    pub fn query_sum(&self, l_bound: B, r_bound: B) -> Val {
        assert!(l_bound <= r_bound && self.check_bound(l_bound) && self.check_bound(r_bound));
        self.root.borrow_mut().query_sum(l_bound, r_bound)
    }
}

/// Builder of [`SegmentTree`].
///
/// # Examples
///
/// ```
/// # use algo_rs::segment_tree::SegmentTreeBuilder;
///
/// let tree = SegmentTreeBuilder::new()
///     .interval(0, 10)
///     .fill(0)
///     .build()
///     .unwrap();
/// ```
#[derive(Debug, Clone, Default)]
pub struct SegmentTreeBuilder {
    left: Option<B>,
    right: Option<B>,
    fill: Option<Val>,
}

#[allow(unused)]
impl SegmentTreeBuilder {
    /// Creates a new [`SegmentTreeBuilder`].
    #[must_use]
    pub fn new() -> Self {
        Default::default()
    }

    /// Set the interval.
    ///
    /// # Panics
    ///
    /// Panics if `left` is greater than `right`.
    #[must_use]
    pub fn interval(self, left: B, right: B) -> Self {
        assert!(
            left <= right,
            "left should be less than right!, but {left} and {right} given."
        );

        SegmentTreeBuilder {
            left: Some(left),
            right: Some(right),
            ..self
        }
    }

    /// Set the value that fills the interval.
    #[must_use]
    pub fn fill(self, fill: Val) -> Self {
        SegmentTreeBuilder {
            fill: Some(fill),
            ..self
        }
    }

    /// Build the [`SegmentTree`].
    ///
    /// If [`SegmentTreeBuilder::interval`] is not set, return `None`.
    ///
    /// If [`SegmentTreeBuilder::fill`] is not given, use the default value.
    #[must_use]
    pub fn build(self) -> Option<SegmentTree> {
        let left = self.left?;
        let right = self.right?;
        let fill = self.fill.unwrap_or_default();
        let root = RefCell::new(Node::build(left, right, fill));

        Some(SegmentTree { left, right, root })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn test_builder_interval_panic() {
        SegmentTreeBuilder::new().interval(3, 0).build().unwrap();
    }

    #[test]
    #[should_panic]
    fn test_builder_build_panic() {
        SegmentTreeBuilder::new().build().unwrap();
    }

    #[test]
    fn small_tree() {
        let mut tree = SegmentTreeBuilder::new()
            .interval(0, 3)
            .fill(0)
            .build()
            .unwrap();

        assert_eq!(tree.query_max(1, 2), 0);

        tree.modify_point(1, |_| 5);
        assert_eq!(tree.query_max(1, 3), 5);

        tree.add_segment(0, 2, 1);
        assert_eq!(tree.query_sum(1, 2), 7);
    }

    #[test]
    #[should_panic]
    fn test_bound_check_panic_1() {
        let mut tree = SegmentTreeBuilder::new().interval(-1, 1).build().unwrap();

        tree.modify_point(2, |_| 0);
    }

    #[test]
    #[should_panic]
    fn test_bound_check_panic_2() {
        let mut tree = SegmentTreeBuilder::new().interval(-1, 1).build().unwrap();

        tree.add_segment(0, 2, 0);
    }

    #[test]
    #[should_panic]
    fn test_bound_check_panic_3() {
        let mut tree = SegmentTreeBuilder::new().interval(-1, 1).build().unwrap();

        tree.set_segment(0, 2, 0);
    }

    #[test]
    #[should_panic]
    fn test_bound_check_panic_4() {
        let tree = SegmentTreeBuilder::new().interval(-1, 1).build().unwrap();

        tree.query_max(0, 2);
    }
}
