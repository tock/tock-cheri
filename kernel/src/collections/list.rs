//! Singly-Linked list implementation.
//! ListLink uses a standard read-only reference to some T as link
//! ListLinkGen uses any reference type as long is it implements Deref<Target=T>.
//!

use crate::grant::PRef;
use core::cell::{Cell, Ref};
use core::ops::Deref;
use misc::take_borrow::TakeBorrow;

/// Ref does not implement Clone, so we need another trait that is really just Clone but can also
/// be implemented for Ref. Would be nice to automatically implement it for all clone types, but
/// min_specialisation does not seem to be enough?
pub trait RefClone {
    fn ref_clone(&self) -> Self;
}

impl<T: RefClone> RefClone for Option<T> {
    #[inline]
    fn ref_clone(&self) -> Self {
        match &self {
            None => None,
            Some(v) => Some(v.ref_clone()),
        }
    }
}

// Like Deref but can panic. Panic is currently on possible for PRef.
pub trait PanicDeref {
    type Target: ?Sized;

    fn panic_deref(&self) -> &Self::Target;
}
// Anything that supports deref supports PanicDeref
impl<T: Deref + ?Sized> PanicDeref for T {
    type Target = <Self as Deref>::Target;

    fn panic_deref(&self) -> &Self::Target {
        self.deref()
    }
}

pub struct ListLinkGen<T: ?Sized, LinkT: PanicDeref<Target = T> + RefClone>(Cell<Option<LinkT>>);

impl<T: ?Sized, LinkT: PanicDeref<Target = T> + RefClone> ListLinkGen<T, LinkT> {
    #[inline]
    pub fn clone_link(&self) -> Option<LinkT> {
        self.0.take_borrow().ref_clone()
    }

    #[inline]
    pub fn points_to(&self, next: &T) -> bool {
        match self.0.take_borrow().as_ref() {
            None => false,
            Some(r) => core::ptr::eq(next as *const T, r.panic_deref() as *const T),
        }
    }

    #[inline]
    pub fn is_some(&self) -> bool {
        self.0.take_borrow().is_some()
    }

    #[inline]
    pub const fn empty() -> Self {
        ListLinkGen(Cell::new(None))
    }

    #[inline]
    pub const fn new(link: LinkT) -> Self {
        ListLinkGen(Cell::new(Some(link)))
    }
}

impl<T: ?Sized, LinkT: PanicDeref<Target = T> + RefClone> Default for ListLinkGen<T, LinkT> {
    fn default() -> Self {
        Self::empty()
    }
}

pub trait GenListNode<T: ?Sized, LinkT: PanicDeref<Target = T> + RefClone> {
    fn next(&self) -> &ListLinkGen<T, LinkT>;
}

#[derive(Default)]
pub struct GenList<T: ?Sized + GenListNode<T, LinkT>, LinkT: PanicDeref<Target = T> + RefClone> {
    head: ListLinkGen<T, LinkT>,
}

#[derive(Default)]
pub struct GenListFastTail<
    T: ?Sized + GenListNode<T, LinkT>,
    LinkT: PanicDeref<Target = T> + RefClone,
> {
    head: GenList<T, LinkT>,
    tail: ListLinkGen<T, LinkT>,
}

pub struct GenListIterator<
    T: ?Sized + GenListNode<T, LinkT>,
    LinkT: PanicDeref<Target = T> + RefClone,
> {
    cur: Option<LinkT>,
}

impl<T: ?Sized + GenListNode<T, LinkT>, LinkT: PanicDeref<Target = T> + RefClone> Iterator
    for GenListIterator<T, LinkT>
{
    type Item = LinkT;

    #[inline(always)]
    fn next(&mut self) -> Option<LinkT> {
        match self.cur.take() {
            Some(res) => {
                self.cur = res.panic_deref().next().clone_link();
                Some(res)
            }
            None => None,
        }
    }
}

impl<T: ?Sized + GenListNode<T, LinkT>, LinkT: PanicDeref<Target = T> + RefClone>
    GenList<T, LinkT>
{
    /// Construct new empty list
    #[inline]
    pub const fn new() -> Self {
        Self {
            head: ListLinkGen::empty(),
        }
    }

    #[inline]
    pub const fn new_with_head(head: ListLinkGen<T, LinkT>) -> Self {
        Self { head }
    }

    /// prefer to head().is_some() as clone may be expensive
    #[inline]
    pub fn is_some(&self) -> bool {
        self.head.0.take_borrow().is_some()
    }

    /// Get a (copy) of a link to the head element
    #[inline]
    pub fn head(&self) -> Option<LinkT> {
        self.head.clone_link()
    }

    #[inline]
    pub fn push_head(&self, node: LinkT) {
        node.panic_deref().next().0.set(self.head.0.take());
        self.head.0.set(Some(node));
    }

    /// Note this may be expensive as it walks the list.
    /// Use the other List type to avoid cost for long lists.
    #[inline]
    pub fn push_tail(&self, node: LinkT) {
        node.panic_deref().next().0.set(None);
        match &self.iter().last() {
            Some(last) => last.panic_deref().next().0.set(Some(node)),
            None => self.push_head(node),
        }
    }

    /// Insert node after node_prev. This is not offered as a method on a link as the list tracking
    /// structure may need to update itself.
    #[inline]
    pub fn insert_after(&self, node_prev: &T, node: LinkT) {
        // node's next is dropped
        let prev_link = &node_prev.next().0;
        let last = prev_link.take();
        // node points to what node_prev did
        node.panic_deref().next().0.set(last);
        // node_prev now points to node
        prev_link.set(Some(node));
    }

    #[inline]
    pub fn remove_after(&self, node_prev: &ListLinkGen<T, LinkT>, node: &T) {
        node_prev.0.set(node.next().0.take())
    }

    /// Apply a function with a reference to the link that points to a node
    #[inline]
    pub fn find_prev(&self, node: &T) -> Option<LinkT> {
        for prev in self.iter() {
            if prev.panic_deref().next().points_to(node) {
                return Some(prev);
            }
        }
        None
    }

    /// Try to remove from the list. Returns a link to the previous element if there was one.
    #[inline]
    pub fn try_remove(&self, node: &T) -> Option<LinkT> {
        if self.head.points_to(node) {
            self.remove_after(&self.head, node);
            None
        } else {
            match self.find_prev(node) {
                None => None,
                Some(prev) => {
                    self.remove_after(prev.panic_deref().next(), node);
                    Some(prev)
                }
            }
        }
    }

    #[inline]
    pub fn pop_head(&self) -> Option<LinkT> {
        let remove = self.head.0.take();
        if let Some(remove) = &remove {
            self.head.0.set(remove.panic_deref().next().0.take());
        }
        remove
    }

    #[inline]
    pub fn peek_head(&self) -> Option<LinkT> {
        self.head.clone_link()
    }

    #[inline]
    pub fn iter(&self) -> GenListIterator<T, LinkT> {
        GenListIterator {
            cur: self.head.clone_link(),
        }
    }

    /// Filter items out of list. Items are removed if f returns true.
    /// Returns a link to the new last item.
    #[inline]
    pub fn filter<F: Fn(&T) -> bool>(&self, f: F) -> Option<LinkT> {
        // This is a link to the node we are finding a successor for.
        // The first link is not in a normal node so this is none
        let mut last_link = None;
        // This is the actual next ptr we will set.
        let mut last_link_next_ptr = &self.head;

        // A link to the current item we are filtering
        let mut cur_item = self.head.0.take();

        while let Some(some_cur_item) = cur_item {
            // Get the next current item
            let cur_item_deref = some_cur_item.panic_deref();
            cur_item = cur_item_deref.next().0.take();
            // Check if we need to filter the current one
            if !f(cur_item_deref) {
                // clone link and place it
                last_link_next_ptr.0.set(Some(some_cur_item.ref_clone()));
                // Set the next link to set
                last_link = Some(some_cur_item);
                last_link_next_ptr = last_link.as_ref().unwrap().panic_deref().next();
            }
        }

        last_link
    }
}

impl<T: ?Sized + GenListNode<T, LinkT>, LinkT: PanicDeref<Target = T> + RefClone>
    GenListFastTail<T, LinkT>
{
    /// Construct new empty list
    #[inline]
    pub const fn new() -> Self {
        Self {
            head: GenList::new(),
            tail: ListLinkGen::empty(),
        }
    }

    #[inline]
    pub const fn new_with_hd_tl(head: ListLinkGen<T, LinkT>, tail: ListLinkGen<T, LinkT>) -> Self {
        Self {
            head: GenList::new_with_head(head),
            tail,
        }
    }

    /// prefer to head().is_some() as clone may be expensive
    #[inline]
    pub fn is_some(&self) -> bool {
        self.head.is_some()
    }

    /// Get a (copy) of a link to the head element
    #[inline]
    pub fn head(&self) -> Option<LinkT> {
        self.head.head()
    }

    #[inline]
    pub fn push_head(&self, node: LinkT) {
        if !self.is_some() {
            self.tail.0.set(Some(node.ref_clone()))
        }
        self.head.push_head(node)
    }

    /// This is O(1)
    #[inline]
    pub fn push_tail(&self, node: LinkT) {
        match self.tail.0.take() {
            None => self.push_head(node),
            Some(old_tail) => {
                self.tail.0.set(Some(node.ref_clone()));
                self.head.insert_after(old_tail.panic_deref(), node);
            }
        }
    }

    /// Insert node after node_prev. This is not offered as a method on a link as the list tracking
    /// structure may need to update itself.
    #[inline]
    pub fn insert_after(&self, node_prev: &T, node: LinkT) {
        if self.tail.points_to(node_prev) {
            self.tail.0.set(Some(node.ref_clone()))
        }
        self.head.insert_after(node_prev, node)
    }

    #[inline]
    pub fn peek_head(&self) -> Option<LinkT> {
        self.head.peek_head()
    }

    /// Try to remove from the list
    #[inline]
    pub fn try_remove(&self, node: &T) {
        let prev = self.head.try_remove(node);
        if self.tail.points_to(node) {
            self.tail.0.set(prev);
        }
    }

    #[inline]
    pub fn pop_head(&self) -> Option<LinkT> {
        let result = self.head.pop_head();
        if !self.head.is_some() {
            self.tail.0.set(None);
        }
        result
    }

    #[inline]
    pub fn iter(&self) -> GenListIterator<T, LinkT> {
        self.head.iter()
    }

    /// Filter items out of list. Items are removed if f returns true.
    #[inline]
    pub fn filter<F: Fn(&T) -> bool>(&self, f: F) {
        self.tail.0.set(self.head.filter(f))
    }
}

// The standard list types that use a reference

pub type ListLink<'a, T> = ListLinkGen<T, &'a T>;
pub type List<'a, T> = GenList<T, &'a T>;
pub type ListIterator<'a, T> = GenListIterator<T, &'a T>;
pub type Queue<'a, T> = GenListFastTail<T, &'a T>;

impl<'a, T: ?Sized> RefClone for &'a T {
    #[inline]
    fn ref_clone(&self) -> Self {
        self.clone()
    }
}

// You can implement the GenListNode rather than this
pub trait ListNode<'a, T: ?Sized> {
    fn next(&self) -> &ListLink<'a, T>;
}
// But in order to provide backwards compat, automatic implementation of the generic interface:
impl<'a, T: 'a + ?Sized + ListNode<'a, T>> GenListNode<T, &'a T> for T {
    #[inline(always)]
    fn next(&self) -> &ListLinkGen<T, &'a T> {
        <Self as ListNode<'a, T>>::next(self)
    }
}

// Using Ref (recall 'b is the lifetime of the borrow of the RefCell)

impl<'a, T: ?Sized> RefClone for Ref<'a, T> {
    #[inline]
    fn ref_clone(&self) -> Self {
        Ref::clone(self)
    }
}

pub type RefListLink<'b, T> = ListLinkGen<T, Ref<'b, T>>;
pub type RefList<'b, T> = GenList<T, Ref<'b, T>>;
pub type RefListIterator<'b, T> = GenListIterator<T, Ref<'b, T>>;
pub type RefQueue<'b, T> = GenListFastTail<T, Ref<'b, T>>;

// Using Pref

impl<T> RefClone for PRef<T> {
    #[inline]
    fn ref_clone(&self) -> Self {
        self.clone()
    }
}

pub type PRefListLink<T> = ListLinkGen<T, PRef<T>>;
pub type PRefList<T> = GenList<T, PRef<T>>;
pub type PRefListIterator<T> = GenListIterator<T, PRef<T>>;
pub type PRefQueue<T> = GenListFastTail<T, PRef<T>>;

#[cfg(test)]
mod tests {
    use crate::collections::list::{
        GenList, GenListFastTail, GenListNode, ListLinkGen, PanicDeref, RefClone,
    };
    use core::cell::{Cell, Ref, RefCell};
    use misc::leak_thread_local;

    trait GetVal {
        fn get_val(&self) -> u8;
    }

    // Macro to declare a few different node types
    macro_rules! declare_list {
        ($node_ty : ident, $link_ty : ty, $list_ty: ident) => {
            // A node with a u8 and any type of link so we can test different ones
            struct $node_ty<'a> {
                next: ListLinkGen<$node_ty<'a>, $link_ty>,
                val: Cell<u8>,
            }

            impl<'a> GenListNode<$node_ty<'a>, $link_ty> for $node_ty<'a> {
                fn next(&self) -> &ListLinkGen<$node_ty<'a>, $link_ty> {
                    &self.next
                }
            }

            impl<'a> $node_ty<'a> {
                const fn new(val: u8) -> Self {
                    Self {
                        next: ListLinkGen::<$node_ty<'a>, $link_ty>(Cell::new(None)),
                        val: Cell::new(val),
                    }
                }
            }

            impl<'a> GetVal for $node_ty<'a> {
                fn get_val(&self) -> u8 {
                    self.val.get()
                }
            }
        };
    }

    // Standard references
    declare_list!(NormalNode, &'a NormalNode<'a>, ANormalList);
    // RefCell based
    declare_list!(RefNode, Ref<'a, RefNode<'a>>, ARefList);

    thread_local! {
        static NODE1: RefCell<RefNode<'static>> = RefCell::new(RefNode::new(1));
        static NODE2: RefCell<RefNode<'static>> = RefCell::new(RefNode::new(2));
        static NODE3: RefCell<RefNode<'static>> = RefCell::new(RefNode::new(3));
    }

    fn get_node1() -> Ref<'static, RefNode<'static>> {
        unsafe { leak_thread_local!(NODE1) }.borrow()
    }
    fn get_node2() -> Ref<'static, RefNode<'static>> {
        unsafe { leak_thread_local!(NODE2) }.borrow()
    }
    fn get_node3() -> Ref<'static, RefNode<'static>> {
        unsafe { leak_thread_local!(NODE3) }.borrow()
    }

    #[test]
    fn test_is_some() {
        // Test for any list
        fn do_test<LinkT: RefClone + PanicDeref<Target = T>, T: GenListNode<T, LinkT> + GetVal>(
            a_node: LinkT,
        ) {
            let new_list = GenList::<T, LinkT>::new();
            assert!(!new_list.is_some());
            new_list.push_head(a_node);
            assert_eq!(new_list.head().unwrap().panic_deref().get_val(), 1);
            assert!(new_list.is_some());

            let a_node = new_list.pop_head().unwrap();

            let new_queue = GenListFastTail::<T, LinkT>::new();
            assert!(!new_queue.is_some());
            new_queue.push_head(a_node);
            assert_eq!(new_queue.head().unwrap().panic_deref().get_val(), 1);
            assert!(new_queue.is_some());
        }

        // Normal lists
        let node = NormalNode::new(1);
        do_test(&node);
        // Ref lists
        do_test(get_node1());
    }

    #[test]
    fn test_push_pop() {
        fn do_test<LinkT: RefClone + PanicDeref<Target = T>, T: GenListNode<T, LinkT> + GetVal>(
            node1: LinkT,
            node2: LinkT,
            node3: LinkT,
        ) {
            let a_list = GenListFastTail::<T, LinkT>::new();
            a_list.push_head(node1);
            a_list.push_head(node2);
            a_list.push_head(node3);

            let node3 = a_list.pop_head().unwrap();
            let node2 = a_list.pop_head().unwrap();
            let node1 = a_list.pop_head().unwrap();

            assert_eq!(node3.panic_deref().get_val(), 3);
            assert_eq!(node2.panic_deref().get_val(), 2);
            assert_eq!(node1.panic_deref().get_val(), 1);
        }

        let node1 = NormalNode::new(1);
        let node2 = NormalNode::new(2);
        let node3 = NormalNode::new(3);

        do_test(&node1, &node2, &node3);
        do_test(get_node1(), get_node2(), get_node3());
    }

    #[test]
    fn test_push_tail() {
        fn do_test<LinkT: RefClone + PanicDeref<Target = T>, T: GenListNode<T, LinkT> + GetVal>(
            node1: LinkT,
            node2: LinkT,
            node3: LinkT,
        ) {
            let node1_clone = node1.ref_clone();

            let a_list = GenListFastTail::<T, LinkT>::new();
            // []
            a_list.push_head(node1);
            // [1]
            a_list.push_tail(node2);
            // [1,2]
            a_list.push_head(node3);
            // [3,1,2]
            a_list.try_remove(node1_clone.panic_deref());
            // [3,2]

            let node3 = a_list.pop_head().unwrap();
            let node2 = a_list.pop_head().unwrap();

            assert_eq!(node3.panic_deref().get_val(), 3);
            assert_eq!(node2.panic_deref().get_val(), 2);
        }

        let node1 = NormalNode::new(1);
        let node2 = NormalNode::new(2);
        let node3 = NormalNode::new(3);

        do_test(&node1, &node2, &node3);
        do_test(get_node1(), get_node2(), get_node3());
    }

    #[test]
    fn test_filter() {
        fn do_test<LinkT: RefClone + PanicDeref<Target = T>, T: GenListNode<T, LinkT> + GetVal>(
            node1: LinkT,
            node2: LinkT,
            node3: LinkT,
        ) {
            let a_list = GenListFastTail::<T, LinkT>::new();
            // []
            a_list.push_head(node1);
            // [1]
            a_list.push_tail(node2);
            // [1,2]
            a_list.push_head(node3);
            // [3,1,2]

            a_list.filter(|item| item.get_val() % 2 == 1);
            // [2]

            assert_eq!(a_list.pop_head().unwrap().panic_deref().get_val(), 2);
            assert!(!a_list.is_some());
        }

        let node1 = NormalNode::new(1);
        let node2 = NormalNode::new(2);
        let node3 = NormalNode::new(3);

        do_test(&node1, &node2, &node3);
        do_test(get_node1(), get_node2(), get_node3());
    }

    #[test]
    fn test_iter() {
        fn do_test<LinkT: RefClone + PanicDeref<Target = T>, T: GenListNode<T, LinkT> + GetVal>(
            node1: LinkT,
            node2: LinkT,
            node3: LinkT,
        ) {
            let a_list = GenListFastTail::<T, LinkT>::new();
            // []
            a_list.push_head(node1);
            // [1]
            a_list.push_tail(node2);
            // [1,2]
            a_list.push_head(node3);
            // [3,1,2]

            let expect = [3, 1, 2];

            // Iterator should work more than once
            for _ in 0..1 {
                let mut ndx = 0;
                for node in a_list.iter() {
                    assert_eq!(node.panic_deref().get_val(), expect[ndx]);
                    ndx += 1;
                }
                assert_eq!(ndx, 3);
            }
        }

        let node1 = NormalNode::new(1);
        let node2 = NormalNode::new(2);
        let node3 = NormalNode::new(3);

        do_test(&node1, &node2, &node3);
        do_test(get_node1(), get_node2(), get_node3());
    }
}
