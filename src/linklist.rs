//! This module provides the stack like [`LinkList`].
//!
//! # Examples
//!
//! ```
//! # use algo_rs::linklist::LinkList;
//!
//! let mut list = LinkList::new();
//! list.push(1);
//! list.push(2);
//! list.push(3);
//!
//! assert_eq!(list.pop(), Some(3));
//! assert_eq!(list.pop(), Some(2));
//! assert_eq!(list.pop(), Some(1));
//! assert_eq!(list.pop(), None);
//! ```

use core::fmt;
use std::cmp::Ordering;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Node type in the [`LinkList`].
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
struct Node<T> {
    val: T,
    next: Option<Box<Node<T>>>,
}

type Link<T> = Option<Box<Node<T>>>;

/// Stack like link list.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct LinkList<T> {
    head: Link<T>,
}

#[allow(unused)]
impl<T> LinkList<T> {
    /// Creates a new [`LinkList<T>`].
    #[must_use]
    pub fn new() -> Self {
        LinkList { head: None }
    }

    /// Push `val` into the head.
    pub fn push(&mut self, val: T) {
        self.head = Some(Box::new(Node {
            val,
            next: self.head.take(),
        }));
    }

    /// Pop from the head.
    ///
    /// # Examples
    ///
    /// ```
    /// # use algo_rs::linklist::LinkList;
    /// let mut list = LinkList::new();
    /// list.push(1);
    /// list.push(2);
    /// assert_eq!(list.pop(), Some(2));
    /// assert_eq!(list.pop(), Some(1));
    /// assert_eq!(list.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.head.take().map(|node| {
            self.head = node.next;
            node.val
        })
    }

    /// Get the reference of the value in the head.
    pub fn peek(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.val)
    }

    /// Get the mutable reference of the value in the head.
    pub fn peek_mut(&mut self) -> Option<&mut T> {
        self.head.as_mut().map(|node| &mut node.val)
    }

    /// Returns the iter of this [`LinkList<T>`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use algo_rs::linklist::LinkList;
    /// let mut list = LinkList::new();
    /// list.push(1);
    /// list.push(2);
    /// list.push(3);
    ///
    /// let v: Vec<i32> = list.iter().cloned().collect();
    /// assert_eq!(v, vec![3, 2, 1]);
    /// ```
    pub fn iter(&self) -> Iter<T> {
        Iter {
            cur: self.head.as_deref(),
        }
    }

    /// Returns the mutable iter of this [`LinkList<T>`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use algo_rs::linklist::LinkList;
    /// let mut list = LinkList::new();
    /// list.push(1);
    /// list.push(2);
    /// list.push(3);
    ///
    /// list.iter_mut()
    ///     .for_each(|v| *v += 1);
    ///
    /// let v: Vec<i32> = list.iter().cloned().collect();
    /// assert_eq!(v, vec![4, 3, 2]);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut {
            cur: self.head.as_deref_mut(),
        }
    }
}

impl<T> Default for LinkList<T> {
    fn default() -> Self {
        LinkList::new()
    }
}

impl<T: Clone> Clone for Node<T> {
    fn clone(&self) -> Self {
        Self {
            val: self.val.clone(),
            next: self.next.clone(),
        }
    }
}

impl<T: Clone> Clone for LinkList<T> {
    fn clone(&self) -> Self {
        Self {
            head: self.head.clone(),
        }
    }
}

impl<T, const N: usize> From<[T; N]> for LinkList<T> {
    fn from(value: [T; N]) -> Self {
        Self::from_iter(value)
    }
}

impl<T> FromIterator<T> for LinkList<T> {
    fn from_iter<A: IntoIterator<Item = T>>(iter: A) -> Self {
        let mut list = LinkList::new();
        iter.into_iter().for_each(|v| list.push(v));
        list
    }
}

impl<T> Extend<T> for LinkList<T> {
    fn extend<A: IntoIterator<Item = T>>(&mut self, iter: A) {
        iter.into_iter().for_each(|v| self.push(v));
    }
}

/// An iterator that consumes the [`LinkList`].
pub struct IntoIter<T> {
    linklist: LinkList<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.linklist.pop()
    }
}

impl<T> IntoIterator for LinkList<T> {
    type Item = T;

    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { linklist: self }
    }
}

/// An iterator that iterates over the reference.
pub struct Iter<'a, T> {
    cur: Option<&'a Node<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.cur.take().map(|node| {
            self.cur = node.next.as_deref();
            &node.val
        })
    }
}

impl<'a, T> IntoIterator for &'a LinkList<T> {
    type Item = &'a T;

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// An iterator that iterates over the mutable reference.
pub struct IterMut<'a, T> {
    cur: Option<&'a mut Node<T>>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.cur.take().map(|node| {
            self.cur = node.next.as_deref_mut();
            &mut node.val
        })
    }
}

impl<'a, T> IntoIterator for &'a mut LinkList<T> {
    type Item = &'a mut T;

    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T: fmt::Debug> fmt::Debug for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.val)?;
        match self.next.as_ref() {
            Some(node) => {
                write!(f, " -> ")?;
                node.fmt(f)
            }
            None => Ok(()),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for LinkList<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "LinkList: ")?;
        // f.debug_list().entries(self).finish()

        match self.head.as_ref() {
            Some(node) => node.fmt(f),
            None => write!(f, "[]"),
        }
    }
}

impl<T> Drop for LinkList<T> {
    fn drop(&mut self) {
        let mut cur = self.head.take();
        while let Some(mut node) = cur {
            cur = node.next.take();
        }
    }
}

impl<T: PartialEq> PartialEq for LinkList<T> {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other)
    }
}

impl<T: Eq> Eq for LinkList<T> {}

impl<T: PartialOrd> PartialOrd for LinkList<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T: Ord> Ord for LinkList<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

#[cfg(test)]
mod tests {
    use super::LinkList;

    #[test]
    fn test_push_pop() {
        let mut list = LinkList::<i32>::default();
        list.push(1);
        list.push(2);
        list.push(3);

        assert_eq!(list.pop(), Some(3));
        assert_eq!(list.pop(), Some(2));
        assert_eq!(list.pop(), Some(1));
        assert_eq!(list.pop(), None);
    }

    #[test]
    fn test_peek() {
        let mut list = LinkList::new();
        list.push(1);
        assert_eq!(list.peek(), Some(&1));

        list.push(2);
        if let Some(v) = list.peek_mut() {
            *v += 1;
        }
        assert_eq!(list.peek(), Some(&3));
    }

    #[test]
    fn test_iterator() {
        let mut list = LinkList::<i32>::default();
        list.push(1);
        list.push(2);
        list.push(3);

        println!("iter");
        for &v in &list {
            println!("{v}");
        }

        println!("iter mut");
        for v in &mut list {
            *v += 1;
            println!("{v}");
        }

        println!("into iter");
        for v in list {
            println!("{v}");
        }
    }

    #[test]
    fn test_debug() {
        let mut list = LinkList::default();

        list.push(1);
        list.push(2);
        list.push(3);

        // println!("{list:#?}");
        assert_eq!(format!("{:?}", list), "LinkList: 3 -> 2 -> 1");
    }

    #[test]
    fn test_ord() {
        let list1 = LinkList::from([0, 1, 2]);
        let list2 = LinkList::from([0, 0, 3]);
        let list3 = LinkList::from([1, 2]);

        assert!(list1 < list2);
        assert!(list1 > list3);
    }

    #[test]
    fn test_from() {
        let mut list = LinkList::new();
        list.push(0);
        list.push(1);
        list.push(2);

        let list1 = LinkList::from([0, 1, 2]);
        let list2 = LinkList::from_iter(vec![0, 1, 2]);
        assert_eq!(list, list1);
        assert_eq!(list, list2);
    }

    #[test]
    fn test_extend() {
        let mut list = LinkList::new();

        list.extend([0, 1, 2]);
        list.extend(vec![7, 8, 9, 10]);

        assert_eq!(list, LinkList::from([0, 1, 2, 7, 8, 9, 10]));
        // println!("list = {list:?}");

        let (l1, l2): (LinkList<_>, LinkList<_>) = list.into_iter().partition(|&v| v % 2 == 0);
        assert_eq!(l1, LinkList::from([10, 8, 2, 0]));
        assert_eq!(l2, LinkList::from([9, 7, 1]));
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_serde() {
        let list = LinkList::from([0, 1, 2, 3]);

        let serialized = serde_json::to_string(&list).unwrap();
        println!("Serialized: {}", serialized);

        let list_d: LinkList<i32> = serde_json::from_str(&serialized).unwrap();
        assert_eq!(list, list_d);
    }

    #[test]
    fn test_send() {
        fn assert_send<T: Send>() {}
        assert_send::<LinkList<i32>>();
    }

    #[test]
    fn test_sync() {
        fn assert_sync<T: Sync>() {}
        assert_sync::<LinkList<i32>>();
    }

    #[test]
    fn test_macro() {
        let v = vec![0, 1, 2, 3];

        println!("vec = {:?}, a = {:?}", v, LinkList::from_iter(v.clone()));
    }
}
