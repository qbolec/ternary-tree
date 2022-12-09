/*!
A Rust implementation of Ternary Search Trees, with no unsafe blocks and a simplified [Wasm binding](
https://crates.io/crates/ternary-tree-wasm).

[![Build Status]( http://travis-ci.com/julien-montmartin/ternary-tree.svg?branch=master)](
    http://travis-ci.com/julien-montmartin/ternary-tree)
[![Code coverage]( http://codecov.io/gh/julien-montmartin/ternary-tree/branch/master/graph/badge.svg)](
    http://codecov.io/gh/julien-montmartin/ternary-tree)
[![Latest version]( http://img.shields.io/crates/v/ternary-tree.svg)](
    http://crates.io/crates/ternary-tree)
[![API](https://docs.rs/ternary-tree/badge.svg)](
    https://docs.rs/ternary-tree/)

A Ternary Search Tree (TST) is a data structure which stores key/value pairs in a tree. The key is a string, and
its characters are placed in the tree nodes. Each node may have three children (hence the name): a _left_ child, a
_middle_ child and a _right_ child.

A search in a TST compares the current character in the key with the character of the current node:

* If both matches, the search traverses the middle child, and proceed to the next character in the key
* If the key character is less than the node one, the search simply goes through the left child, and keep looking
  for the same key character
* Respectively, if the key character is greater than the node one, the search simply goes through the right child

The data structure and its algorithm are explained very well in [Dr.Dobb's Ternary Search Trees](
http://www.drdobbs.com/database/ternary-search-trees/184410528) article.

The following tree is the TST we get after inserting the following keys in order: "aba", "ab", "bc", "ac", "abc",
"a", "b", "aca", "caa", "cbc", "bac", "c", "cca", "aab", "abb", "aa" (see `tst.dot` produced by code below)

<p align="center"><img alt="An example of a Ternary Search Tree"
src="https://files.jmontmartin.net/tree.svg"></p>

A checked box "☑" denotes a node which stores a value (it corresponds to the last character of a key). An empty box
"☐" means that the node has no value.

A TST can be used as a map, but it allows more flexible ways to retrieve values associated with keys. This crate
provides four ways to iterate over the values of a TST:

* get all values (same as a regular map), with `visit_values` or `iter`
* get all values whose keys begin with some prefix (i.e. _complete_ some prefix), with `visit_complete_values` or
  `iter_complete`
* get all values whose keys are _close_ to some string ([Hamming distance](
  http://en.wikipedia.org/wiki/Hamming_distance)), with `visit_neighbor_values` or `iter_neighbor`
* get all values whose keys match a string with some joker (e.g. "a?c"), with `visit_crossword_values` or
  `iter_crossword`

Visit methods are recursive and apply a closure to found values. They exist in immutable and mutable version
(i.e. `visit_neighbor_values_mut`). But once a value is found (based on its key), they offer no way to know what
the actual key is.

Iterators, on the other hand, save their context in a `Vec` and only work on immutable trees. However they are
double-ended, and support `next` and `next_back` methods to walk the tree from both ends. Moreover, once a value is
found, they offer the `current_key` and `current_key_back` methods to retrieve the associated key.

The following lines may give you a foretaste of this crate and TSTs

```
extern crate ternary_tree;

use ternary_tree::Tst;
use std::fs::File;
use std::error::Error;

const SOME_KEYS : [&str; 16] = ["aba", "ab", "bc", "ac",
"abc", "a", "b", "aca", "caa", "cbc", "bac", "c", "cca",
"aab", "abb", "aa"];

let mut map = Tst::new();

for key in &SOME_KEYS {

    // Say the value is the same as the key,
    // it makes the example easier !
    let some_value = *key;

    map.insert(key, some_value);
}

// Use Graphviz to convert tst.dot to tst.png:
// dot -T png -o tst.png tst.dot
let mut file = File::create("tst.dot").unwrap();
map.pretty_print(&mut file);

let mut v = Vec::new();

// Recursively get all values whose keys match "a?a" pattern
map.visit_crossword_values("a?a", '?', |s| v.push(s.clone()));
assert_eq!(v, ["aba", "aca"]);

v.clear();

// Iterate over all values whose keys are close to "abc"
// (At a Hamming distance of 1 from "abc")
{
    let mut it = map.iter_neighbor("abc", 1);

    while let Some(value) = it.next() {

        v.push(*value);
    }
    assert_eq!(v, ["ab", "aba", "abb", "abc", "cbc"]);

    v.clear();
}

// Mutate all values whose keys begin with "c"
map.visit_complete_values_mut("c", |s| *s = "xxx");

assert_eq!(map.get("caa"), Some(&"xxx"));
assert_eq!(map.get("cbc"), Some(&"xxx"));
assert_eq!(map.get("cca"), Some(&"xxx"));
```
*/

#![forbid(unsafe_code)]

use std::cmp::Ordering::Equal;
use std::cmp::Ordering::Greater;
use std::cmp::Ordering::Less;
use std::fmt;
use std::io::Write;
use std::iter::Peekable;
use std::mem;
use std::mem::replace;
use std::ptr;
use std::str::Chars;

/// A `Tst` is a ternary tree structure which stores key value pairs and roughly behave like a map, but allowing
/// more flexible ways to find and iterate over values.
///
/// See the [module documentation]( ./index.html) for example usage and motivation.

pub struct Tst<T> {
    root: Link<T>,
}
type CharsChain = Option<Box<CharNode>>;
struct CharNode {
    first: char,
    rest: CharsChain,
}

/*
trait AbstractCharsNodeRef<'a> {
    type CharsChainRef : AbstractCharsChainRef<'a, CharsNodeRef=Self>;
    fn unwrap(self) -> (char, Self::CharsChainRef);
}
trait AbstractCharsChainRef<'a> {
    type CharNodeRef : AbstractCharsNodeRef<'a, CharsChainRef=Self>;
    fn unwrap(self) -> Option<Self::CharNodeRef>;
}

impl<'a> AbstractCharsNodeRef<'a> for &'a CharsNode {
    type CharsChainRef = &'a CharsChain;
    fn unwrap(self) -> (char, Self::CharsChainRef) {
        (self.first, &self.rest)
    }
}
impl<'a> AbstractCharsNodeRef<'a> for &'a mut CharsNode {
    type CharsChainRef = &'a mut CharsChain;
    fn unwrap(self) -> (char, Self::CharsChainRef) {
        (self.first, &mut self.rest)
    }
}

impl<'a> AbstractCharsChainRef<'a> for &'a CharsChain {
    type CharsNodeRef = &'a CharsChain;
    fn unwrap(self) -> Option<Self::CharNodeRef> {
        match self {
            None => None,
            Some(boxed_node) => Some(& * boxed_node)
        }
    }
}
impl<'a> AbstractCharsChainRef<'a> for &'a mut CharsChain {
    type CharsNodeRef = &'a mut CharsChain;
    fn unwrap(self) -> Option<Self::CharNodeRef> {
        match self {
            None => None,
            Some(boxed_node) => Some(&mut * boxed_node)
        }
    }
}
*/
type Link<T> = Option<Box<Node<T>>>;
struct Node<T> {
    label: CharNode,
    value: Option<T>,
    left: Link<T>,
    middle: Link<T>,
    right: Link<T>,
    count: usize,
}

trait AbstractLinkRef<'a> {
    type TRef;
    type NodeRef: AbstractNodeRef<'a, TRef = Self::TRef, LinkRef = Self>;
    fn unwrap(self) -> Option<Self::NodeRef>;
}

trait AbstractNodeRef<'a> {
    type TRef;
    type LinkRef: AbstractLinkRef<'a, TRef = Self::TRef, NodeRef = Self>;
    fn unwrap(
        self,
    ) -> (
        &'a CharNode,
        Option<Self::TRef>,
        Self::LinkRef,
        Self::LinkRef,
        Self::LinkRef,
        &'a usize,
    );
}
impl<'a, T> AbstractNodeRef<'a> for &'a Node<T> {
    type TRef = &'a T;
    type LinkRef = &'a Link<T>;
    fn unwrap(
        self,
    ) -> (
        &'a CharNode,
        Option<Self::TRef>,
        Self::LinkRef,
        Self::LinkRef,
        Self::LinkRef,
        &'a usize,
    ) {
        (
            &self.label,
            self.value.as_ref(),
            &self.left,
            &self.middle,
            &self.right,
            &self.count,
        )
    }
}
impl<'a, T> AbstractNodeRef<'a> for &'a mut Node<T> {
    type TRef = &'a mut T;
    type LinkRef = &'a mut Link<T>;
    fn unwrap(
        self,
    ) -> (
        &'a CharNode,
        Option<Self::TRef>,
        Self::LinkRef,
        Self::LinkRef,
        Self::LinkRef,
        &'a usize,
    ) {
        (
            &self.label,
            self.value.as_mut(),
            &mut self.left,
            &mut self.middle,
            &mut self.right,
            &self.count,
        )
    }
}

impl<'a, T> AbstractLinkRef<'a> for &'a Link<T> {
    type TRef = &'a T;
    type NodeRef = &'a Node<T>;
    fn unwrap(self) -> Option<Self::NodeRef> {
        match self {
            None => None,
            Some(boxed_node) => Some(&*boxed_node),
        }
    }
}
impl<'a, T> AbstractLinkRef<'a> for &'a mut Link<T> {
    type TRef = &'a mut T;
    type NodeRef = &'a mut Node<T>;
    fn unwrap(self) -> Option<Self::NodeRef> {
        match self {
            None => None,
            Some(boxed_node) => Some(&mut *boxed_node),
        }
    }
}

fn link_count<T>(link: &Link<T>) -> usize {
    link.as_ref().map_or(0, |v| v.count)
}
impl<T> Node<T> {
    fn verify_count(&self) {
        assert_eq!(
            self.count,
            link_count(&self.left)
                + link_count(&self.middle)
                + link_count(&self.right)
                + (if self.value.is_some() { 1 } else { 0 })
        );
    }
    fn verify_balance(&self) {
        assert!(!needs_rebuild(self.count, link_count(&self.left)));
        assert!(!needs_rebuild(self.count, link_count(&self.right)));
    }
}

impl<T> Default for Node<T> {
    fn default() -> Node<T> {
        Node {
            label: CharNode {
                first: '\0',
                rest: None,
            },
            value: None,
            left: None,
            middle: None,
            right: None,
            count: 0,
        }
    }
}

impl fmt::Debug for CharNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let res = write!(f, "{}", self.first)?;
        match self.rest {
            None => Ok(res),
            Some(ref node) => node.fmt(f),
        }
    }
}

impl<T> fmt::Debug for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let value_box = match self.value {
            None => "☐",
            Some(_) => "☑",
        };

        write!(f, "{}-{:?}", value_box, self.label)
    }
}

fn verify_r<T>(link: &Link<T>) {
    match link {
        None => {}
        Some(ref node) => {
            node.verify_count();
            node.verify_balance();
            verify_r(&node.left);
            verify_r(&node.right);
            verify_r(&node.middle);
        }
    }
}

fn flatten_r<T>(link: &mut Link<T>, nodes_in_order: &mut Vec<Link<T>>) {
    match link {
        None => {}
        Some(_) => {
            let mut me = replace(link, None);
            let ref mut node = me.as_mut().unwrap();
            let mut left = replace(&mut node.left, None);
            let mut right = replace(&mut node.right, None);
            node.count -= link_count(&left);
            node.count -= link_count(&right);
            flatten_r(&mut left, nodes_in_order);
            assert_eq!(
                0 < node.count,
                node.value.is_some() || node.middle.is_some()
            );
            if 0 < node.count {
                //pruning
                nodes_in_order.push(me);
            }
            flatten_r(&mut right, nodes_in_order);
        }
    }
}
fn build<T>(nodes_in_order: &mut [Link<T>], start: usize, prefix_sums: &[usize]) -> Link<T> {
    assert_eq!(nodes_in_order.len(), prefix_sums.len());
    if nodes_in_order.is_empty() {
        return None;
    }
    let end = prefix_sums.last().unwrap_or(&0);
    let center = (start + end) >> 1;
    // if the sizes are [1,1,1], then end==3, center = 1 (well, 1.5),
    // the prefix_sums: [1,2,3], and we want to find the prefix_sums[i-1]<=center<prefix_sums[i]
    let i = prefix_sums.partition_point(|sum| sum <= &center);
    assert!(center < prefix_sums[i]);
    let (left_prefix_sums, non_left_prefix_sums) = prefix_sums.split_at(i);
    let (_, right_prefix_sums) = non_left_prefix_sums.split_at(1);
    let (left_nodes_in_order, non_left_nodes_in_order) = nodes_in_order.split_at_mut(i);
    let (middle_nodes, right_nodes_in_order) = non_left_nodes_in_order.split_at_mut(1);
    let mut middle_node_option = replace(&mut middle_nodes[0], None);
    let ref mut middle_node = middle_node_option.as_mut().unwrap();
    middle_node.left = build(left_nodes_in_order, start, left_prefix_sums);
    middle_node.right = build(right_nodes_in_order, prefix_sums[i], right_prefix_sums);
    middle_node.count += link_count(&middle_node.left) + link_count(&middle_node.right);
    return middle_node_option;
}
fn rebuild<T>(link: &mut Link<T>) {
    let mut nodes_in_order = vec![];
    flatten_r(link, &mut nodes_in_order);
    let mut prefix_sum_of_sizes = vec![];
    for ref node in nodes_in_order.iter() {
        prefix_sum_of_sizes.push(link_count(node) + prefix_sum_of_sizes.last().unwrap_or(&0));
    }
    *link = build(&mut nodes_in_order, 0, &prefix_sum_of_sizes);
}
fn needs_rebuild(total: usize, child: usize) -> bool {
    // needs_rebuild(0,0) must be true
    return total * 3 <= child * 4;
}

impl CharNode {
    fn from_chars(first: char, mut rest: Chars) -> CharNode {
        CharNode {
            first,
            rest: match rest.next() {
                None => None,
                Some(label) => Some(Box::new(CharNode::from_chars(label, rest))),
            },
        }
    }
}
fn split_chain_at_mismatch(
    rest: &mut CharsChain,
    key_tail: &mut Chars,
) -> (CharsChain, Option<char>) {
    match rest {
        None => (None, key_tail.next()),
        Some(char_node) => match key_tail.next() {
            None => (replace(rest, None), None),
            Some(label) => {
                if label == char_node.first {
                    split_chain_at_mismatch(&mut char_node.rest, key_tail)
                } else {
                    (replace(rest, None), Some(label))
                }
            }
        },
    }
}
fn insert_r<T>(
    link: &mut Link<T>,
    label: char,
    mut key_tail: Chars,
    value: T,
    rebuild_allowed: bool,
) -> Option<T> {
    if link.is_none() {
        *link = Some(Box::new(Node::<T> {
            label: CharNode::from_chars(label, key_tail),
            count: 1,
            value: Some(value),
            ..Default::default()
        }));
        return None;
    }
    let ref mut node = link.as_mut().unwrap();
    let rebuild_on_new;
    let old_value = if label == node.label.first {
        rebuild_on_new = false;
        // rest, key_tail
        // ""  , ""       ->  replace(&mut node.value, Some(value))
        // ""  , "ab"     ->  insert_r(&mut node.middle, 'a', "b", value, true)
        // "ab", ""       ->  spawn new Node with left=right=None, middle=node.middle, label={'a',"b"}, count=node.count, value=node.value
        //                    modify self.label.next = None, middle=spawned,
        //                    replace(&mut node.value, Some(value))
        // "azbc", "azde" ->  spawn new Node with left=right=None, middle=node.middle, label={'a',"b"}, count=node.count, value=node.value
        //                    modify self.label.next = None, middle=spawned,
        //
        let (different_suffix, different_label) =
            split_chain_at_mismatch(&mut node.label.rest, &mut key_tail);
        match different_suffix {
            None => match different_label {
                None => replace(&mut node.value, Some(value)),
                Some(label) => insert_r(&mut node.middle, label, key_tail, value, true),
            },
            Some(suffix) => {
                node.verify_count();
                let spawned = Some(Box::new(Node::<T> {
                    label: *suffix,
                    count: node.count - link_count(&node.left) - link_count(&node.right),
                    value: replace(&mut node.value, None),
                    middle: replace(&mut node.middle, None),
                    left: None,
                    right: None,
                }));
                spawned.as_ref().unwrap().verify_count();
                node.middle = spawned;
                match different_label {
                    None => replace(&mut node.value, Some(value)),
                    Some(label) => insert_r(&mut node.middle, label, key_tail, value, true),
                }
            }
        }
    } else {
        let child = if label < node.label.first {
            &mut node.left
        } else {
            &mut node.right
        };
        rebuild_on_new = rebuild_allowed && needs_rebuild(node.count + 1, link_count(child) + 1);
        insert_r(
            child,
            label,
            key_tail,
            value,
            rebuild_allowed && !rebuild_on_new,
        )
    };
    if old_value.is_none() {
        node.count += 1;
        node.verify_count();
        if rebuild_on_new {
            rebuild(link);
        }
    }
    old_value
}

fn traverse_chain<'a>(rest: &'a CharsChain, key: &mut Peekable<Chars>) -> &'a CharsChain {
    match rest {
        None => rest,
        Some(char_node) => match key.peek() {
            Some(label) if label == &char_node.first => {
                key.next();
                traverse_chain(&char_node.rest, key)
            }
            _ => rest,
        },
    }
}

fn get_gen<'a, LinkRef>(link: LinkRef, key: &mut Peekable<Chars>) -> Option<LinkRef::TRef>
where
    LinkRef: AbstractLinkRef<'a>,
{
    match link.unwrap() {
        None => None,
        Some(node) => {
            let (label, value, left, middle, right, _size) = node.unwrap();
            match key.peek() {
                None => None,
                Some(key_letter) => match key_letter.cmp(&label.first) {
                    Less => get_gen(left, key),
                    Equal => {
                        key.next();
                        let ref rest = traverse_chain(&label.rest, key);
                        match rest {
                            None => match key.peek() {
                                None => value,
                                _ => get_gen(middle, key),
                            },
                            _ => None,
                        }
                    }
                    Greater => get_gen(right, key),
                },
            }
        }
    }
}
fn push_chain_to_string(label: &CharNode, path: &mut String) {
    path.push(label.first);
    if let Some(char_node) = label.rest.as_ref() {
        push_chain_to_string(&*char_node, path);
    }
}
fn get_nth_r<'a, T>(link: &'a Link<T>, mut n: usize, mut path: String) -> Option<(String, &'a T)> {
    match *link {
        None => None,
        Some(ref node) => {
            let left_count = link_count(&node.left);
            if n < left_count {
                return get_nth_r(&node.left, n, path);
            }
            n -= left_count;
            if node.value.is_some() {
                if n == 0 {
                    push_chain_to_string(&node.label, &mut path);
                    return Some((path, node.value.as_ref().unwrap()));
                } else {
                    n -= 1;
                }
            }
            let middle_count = link_count(&node.middle);
            if n < middle_count {
                push_chain_to_string(&node.label, &mut path);
                return get_nth_r(&node.middle, n, path);
            }
            n -= middle_count;
            get_nth_r(&node.right, n, path)
        }
    }
}

fn remove_r<T>(link: &mut Link<T>, key: &mut Peekable<Chars>, rebuild_allowed: bool) -> Option<T> {
    match (link.as_mut(), key.peek()) {
        (Some(ref mut node), Some(label)) => {
            assert!(0 < node.count);
            let rebuild_on_removal;
            let removed = match label.cmp(&node.label.first) {
                Less => {
                    rebuild_on_removal =
                        rebuild_allowed && needs_rebuild(node.count - 1, link_count(&node.right));
                    remove_r(&mut node.left, key, rebuild_allowed && !rebuild_on_removal)
                }
                Greater => {
                    rebuild_on_removal =
                        rebuild_allowed && needs_rebuild(node.count - 1, link_count(&node.left));
                    remove_r(&mut node.right, key, rebuild_allowed && !rebuild_on_removal)
                }
                Equal => {
                    rebuild_on_removal = rebuild_allowed
                        && needs_rebuild(
                            node.count - 1,
                            std::cmp::max(link_count(&node.right), link_count(&node.left)),
                        );
                    key.next();
                    let ref rest = traverse_chain(&node.label.rest, key);
                    match rest {
                        None => {
                            let removed = match key.peek() {
                                None => replace(&mut node.value, None),
                                Some(_) => remove_r(&mut node.middle, key, true),
                            };
                            if node.value.is_none() && node.middle.is_some() {
                                let ref mut middle = node.middle.as_mut().unwrap();
                                if middle.left.is_none() && middle.right.is_none() {
                                    assert!(removed.is_some());
                                    let new_middle = mem::take(&mut middle.middle);
                                    let old_middle = replace(&mut node.middle, new_middle).unwrap();
                                    node.value = old_middle.value;
                                    let mut end = &mut node.label.rest;
                                    while end.is_some() {
                                        end = &mut end.as_mut().unwrap().rest;
                                    }
                                    *end = Some(Box::from(old_middle.label));
                                }
                            }
                            removed
                        }
                        _ => None,
                    }
                    // Node is only needed for as long as it is part of some key:
                    //    node.value.is_none() && node.middle.is_none()
                    // We could handle the easy cases, where left or right is None, by lifting the other child.
                    // We might be tempted to handle the case where both are Some, by replacing us with leftmost ancestor of right, but
                    // that could actually destroy the balance along the path to it.
                    // However, we do not actually need to do anything at all here!
                    // All the heavy lifting is done by rebuild() when needs_rebuild() says it is necessary.
                    // If left & right are balanced, then our node is still helpful in providing a comparison which reduces range by 25%.
                    // If any of them is missing, and middle&value are empty, then needs_rebuild(0+|kid|,|kid|) will return true.
                    // If both kids are missing already then needs_rebuild(0,0) should return true as well.
                }
            };
            if removed.is_some() {
                node.count -= 1;
                node.verify_count();
                if rebuild_on_removal {
                    rebuild(link)
                }
            }
            removed
        }
        _ => None,
    }
}

/// How nodes are distributed. See [Stats]( ./struct.Stats.html) for a brief description.

#[derive(Default, PartialEq, Debug)]
pub struct DistStat {
    pub matches: usize,
    pub sides: usize,
    pub depth: usize,
}

/// How long are the keys. See [Stats]( ./struct.Stats.html) for a brief description.

#[derive(Default, PartialEq, Debug)]
pub struct KeyLenStat {
    pub min: usize,
    pub max: usize,
}

/// How many nodes and values are in the tree. See [Stats]( ./struct.Stats.html) for a brief description.

#[derive(Default, PartialEq, Debug)]
pub struct CountStat {
    pub nodes: usize,
    pub char_nodes: usize,
    pub values: usize,
}

/// Memory used by the tree. See [Stats]( ./struct.Stats.html) for a brief description.

#[derive(Default, PartialEq, Debug)]
pub struct BytesStat {
    pub node: usize,
    pub char_node: usize,
    pub total: usize,
}

/// Contains various metrics describing the tree: its nodes, keys and values. Mostly used for tuning and debugging
/// purpose.
/// * `dist[n].matches` number of values reached by traversing _n_ `middle` links (the number of keys of length
/// _n_)
/// * `dist[n].sides` number of values reached by traversing _n_ `left` or `middle` links (those links may indicate
/// that the tree is not well balanced)
/// * `dist[n].depth` number of values whose total depth (`middle`, `left` and `right` links) is _n_
/// * `key_len.min` length of the shortest key inserted in the tree
/// * `key_len.max` length of the longest key inserted in the tree
/// * `count.nodes` total number of nodes in the tree
/// * `count.values` number of nodes which store a value (same as [len]( ./struct.Tst.html#method.len))
/// * `bytes.node` byte size of a node (including the fixed size of a value, but excluding heap allocated memory of
/// this value)
/// * `bytes.char_node` bytes per single CharNode
/// * `bytes.total` total number of bytes allocated for nodes

#[derive(Default, PartialEq, Debug)]
pub struct Stats {
    pub dist: Vec<DistStat>,
    pub key_len: KeyLenStat,
    pub count: CountStat,
    pub bytes: BytesStat,
}

fn stat_r<T>(stats: Stats, link: &Link<T>, matches: usize, sides: usize, depth: usize) -> Stats {
    match *link {
        None => stats,

        Some(ref node) => {
            let mut stats = stat_r(stats, &node.left, matches, sides + 1, depth + 1);

            stats.count.nodes += 1;
            stats.count.char_nodes += 1;
            let mut rest = &node.label.rest;
            while let Some(char_node) = rest {
                stats.count.char_nodes += 1;
                rest = &char_node.rest;
            }

            if node.value.is_some() {
                let matches = matches + 1;
                let depth = depth + 1;

                while stats.dist.len() <= depth {
                    stats.dist.push(DistStat {
                        matches: 0,
                        sides: 0,
                        depth: 0,
                    });
                }

                stats.dist[matches].matches += 1;
                stats.dist[sides].sides += 1;
                stats.dist[depth].depth += 1;

                if stats.key_len.min == 0 || matches < stats.key_len.min {
                    stats.key_len.min = matches;
                }

                if matches > stats.key_len.max {
                    stats.key_len.max = matches;
                }

                stats.count.values += 1;
            }

            let stats = stat_r(stats, &node.middle, matches + 1, sides, depth + 1);
            let stats = stat_r(stats, &node.right, matches, sides + 1, depth + 1);

            stats
        }
    }
}

fn find_complete_root_gen<'a, LinkRef>(
    link: LinkRef,
    key: &mut Peekable<Chars>,
) -> (Option<&'a CharNode>, Option<LinkRef::NodeRef>)
where
    LinkRef: AbstractLinkRef<'a>,
{
    match key.peek() {
        None => (None, link.unwrap()),
        Some(key_letter) => match link.unwrap() {
            None => (None, None),
            Some(node) => {
                let (label, _value, left, middle, right, _count) = node.unwrap();
                match key_letter.cmp(&label.first) {
                    Less => find_complete_root_gen(left, key),
                    Greater => find_complete_root_gen(right, key),
                    Equal => {
                        key.next();
                        let ref rest = traverse_chain(&label.rest, key);
                        match (rest, key.peek()) {
                            (Some(_), Some(_)) => (None, None),
                            (Some(boxed_char_node), None) => {
                                (Some(&*boxed_char_node), middle.unwrap())
                            }
                            _ => find_complete_root_gen(middle, key),
                        }
                    }
                }
            }
        },
    }
}

fn visit_values_gen<'a, LinkRef, C>(optional_node: Option<LinkRef::NodeRef>, callback: &mut C)
where
    C: FnMut(LinkRef::TRef),
    LinkRef: AbstractLinkRef<'a>,
{
    if let Some(node) = optional_node {
        let (_label, value, left, middle, right, _count) = node.unwrap();
        visit_values_gen::<LinkRef, C>(left.unwrap(), callback);

        if let Some(value) = value {
            callback(value);
        }

        visit_values_gen::<LinkRef, C>(middle.unwrap(), callback);
        visit_values_gen::<LinkRef, C>(right.unwrap(), callback);
    }
}

fn traverse_chain_hamming_cost<'a>(
    a: &'a CharNode,
    key: &mut Peekable<Chars>,
    key_len: &mut usize,
) -> usize {
    (match &key.peek() {
        None => 1,
        Some(&c) => {
            key.next();
            *key_len -= 1;
            if c == a.first {
                0
            } else {
                1
            }
        }
    }) + a
        .rest
        .as_ref()
        .map_or(0, |r| traverse_chain_hamming_cost(&*r, key, key_len))
}

fn visit_neighbor_values_gen<'a, LinkRef, C>(
    link: LinkRef,
    key: &mut Peekable<Chars>,
    key_len: usize,
    range: usize,
    callback: &mut C,
) where
    LinkRef: AbstractLinkRef<'a>,
    C: FnMut(LinkRef::TRef),
{
    if range == 0 {
        if let Some(value) = get_gen(link, key) {
            callback(value);
        }
    } else {
        if let Some(node) = link.unwrap() {
            let (label, value, left, middle, right, _count) = node.unwrap();
            visit_neighbor_values_gen(left, key, key_len, range, callback);
            {
                let mut new_key = key.clone();
                let mut new_key_len = key_len;
                let cost = traverse_chain_hamming_cost(label, &mut new_key, &mut new_key_len);
                println!(
                    "label is {:?} key len was {:?} now is {:?} and cost is {:?}",
                    label, key_len, new_key_len, cost
                );
                if cost + new_key_len <= range {
                    if let Some(value) = value {
                        callback(value);
                    }
                }
                if cost <= range {
                    visit_neighbor_values_gen(
                        middle,
                        &mut new_key,
                        new_key_len,
                        range - cost,
                        callback,
                    );
                }
            }
            visit_neighbor_values_gen(right, key, key_len, range, callback);
        }
    }
}
fn can_traverse_chain_with_jokers(
    char_node: &CharNode,
    key: &mut Peekable<Chars>,
    joker: char,
) -> bool {
    match key.peek() {
        Some(label) if label == &char_node.first || label == &joker => {
            key.next();
            match &char_node.rest {
                None => true,
                Some(boxed_char_node) => {
                    can_traverse_chain_with_jokers(&boxed_char_node, key, joker)
                }
            }
        }
        _ => false,
    }
}

fn visit_crossword_values_gen<'a, LinkRef, C>(
    link: LinkRef,
    key: &mut Peekable<Chars>,
    joker: char,
    callback: &mut C,
) where
    LinkRef: AbstractLinkRef<'a>,
    C: FnMut(LinkRef::TRef),
{
    if let (Some(node), Some(&key_letter)) = (link.unwrap(), key.peek()) {
        let (label, value, left, middle, right, _count) = node.unwrap();
        if key_letter == joker || key_letter < label.first {
            visit_crossword_values_gen(left, key, joker, callback);
        }

        let mut new_key = key.clone();
        if can_traverse_chain_with_jokers(label, &mut new_key, joker) {
            match new_key.peek() {
                None => {
                    if let Some(value) = value {
                        callback(value);
                    }
                }

                _ => visit_crossword_values_gen(middle, &mut new_key, joker, callback),
            }
        }

        if key_letter == joker || key_letter > label.first {
            visit_crossword_values_gen(right, key, joker, callback);
        }
    }
}

fn pretty_print_r<'a, T>(link: &'a Link<T>, ids: &mut Tst<usize>, writer: &mut dyn Write) {
    match *link {
        None => return,

        Some(ref node) => {
            let value_box = match node.value {
                None => "☐",
                Some(_) => "☑",
            };

            {
                let mut get_id = |node: &Box<Node<T>>| {
                    let node_addr = format!("{:p}", node);

                    let prev_id = match ids.get(&node_addr) {
                        None => None,

                        Some(id) => Some(*id),
                    };

                    match prev_id {
                        None => {
                            let id = ids.len();
                            ids.insert(&node_addr, id);
                            id
                        }

                        Some(id) => id,
                    }
                };

                let _ = writeln!(
                    writer,
                    r#"N{} [label=<<TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0"><TR><TD COLSPAN="3">{} {:?}</TD></TR><TR><TD PORT="l"></TD><TD PORT="m"></TD><TD PORT="r"></TD></TR></TABLE>>]"#,
                    get_id(node),
                    value_box,
                    node.label
                );

                let mut print_edge = |link, start, style| {
                    if let &Some(ref child) = link {
                        let _ = writeln!(
                            writer,
                            r#"N{}:{} -> N{} [style={}]"#,
                            get_id(node),
                            start,
                            get_id(child),
                            style
                        );
                    }
                };

                print_edge(&node.left, "l", "solid");
                print_edge(&node.middle, "m", "bold");
                print_edge(&node.right, "r", "solid");
            }

            pretty_print_r(&node.left, ids, writer);
            pretty_print_r(&node.middle, ids, writer);
            pretty_print_r(&node.right, ids, writer);
        }
    }
}

impl<T> Tst<T> {
    /// Create a new, empty `Tst`. The key is always a string slice and one needs only to provide a value
    /// type. The following code creates an empty tree which stores `bool` values
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// let mut map: Tst<bool> = Tst::new();
    /// ```
    ///
    /// Although most of the time, type inference and some context allow to simply write
    /// ```
    /// # use ternary_tree::Tst;
    /// let mut map = Tst::new();
    /// # map.insert("foo", true);
    ///
    /// ```
    /// And the exact value type is properly guessed.

    pub fn new() -> Self {
        Tst { root: None }
    }

    /// Inserts `key` and `value` pair in the tree, returning any value previously associated with `key`.
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// let mut map = Tst::new();
    /// assert_eq!(map.len(), 0);
    ///
    /// let old_value = map.insert("foo", "🍄🍄");
    /// assert_eq!(old_value, None);
    /// assert_eq!(map.len(), 1);
    /// ```
    ///
    /// Because `key` represents a node path to `value` in the tree, an empty key is meaningless, and its
    /// associated value cannot be stored in the tree. In such a case, `value` is given back by `insert`
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// # let mut map = Tst::new();
    /// assert_eq!(map.len(), 0);
    ///
    /// let this_value = map.insert("", "woups");
    /// assert_eq!(this_value, Some("woups"));
    /// assert_eq!(map.len(), 0);
    /// ```
    ///
    /// Another consequence of `key` representing a path in the tree is that `key` is not consumed by `insert`:
    /// `key` is only borrowed by the tree which needs to iterate over it, but does not need to store it. Thus once
    /// insertion is done, `key` is given back to the caller.

    pub fn insert(&mut self, key: &str, value: T) -> Option<T> {
        let mut key_tail = key.chars();

        match key_tail.next() {
            None => Some(value),

            Some(label) => insert_r(&mut self.root, label, key_tail, value, true),
        }
    }

    /// Returns an immutable reference to the value associated with `key`, or None.
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// # let mut map = Tst::new();
    /// map.insert("foo", "🍄🍄");
    ///
    /// let v = map.get("foo");
    /// assert_eq!(v, Some(&"🍄🍄"));

    pub fn get(&self, key: &str) -> Option<&T> {
        get_gen(&self.root, &mut key.chars().peekable())
    }

    pub fn get_nth(&self, n: usize) -> Option<(String, &T)> {
        get_nth_r(&self.root, n, String::new())
    }

    /// Returns an mutable reference to the value associated with `key`, or `None`.
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// # let mut map = Tst::new();
    /// map.insert("foo", "🍄".to_string());
    ///
    /// if let Some(v) = map.get_mut("foo") {
    ///     v.push('🍄');
    /// }
    ///
    /// let v = map.get("foo");
    /// assert_eq!(v, Some(&"🍄🍄".to_string()));

    pub fn get_mut(&mut self, key: &str) -> Option<&mut T> {
        get_gen(&mut self.root, &mut key.chars().peekable())
    }

    /// Removes the value associated with `key` from the tree, and returns it. Does nothing if no value is
    /// associated with `key`, and returns `None`.
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// # let mut map = Tst::new();
    /// map.insert("foo", "🍄🍄".to_string());
    ///
    /// let v = map.remove("foo");
    /// assert_eq!(v, Some("🍄🍄".to_string()));
    ///
    /// let v = map.remove("foo");
    /// assert_eq!(v, None);

    pub fn remove(&mut self, key: &str) -> Option<T> {
        remove_r(&mut self.root, &mut key.chars().peekable(), true)
    }

    /// Returns the number of values stored in the tree.
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// let mut map = Tst::new();
    /// assert_eq!(map.len(), 0);
    ///
    /// map.insert("foo", "🍄🍄");
    /// assert_eq!(map.len(), 1);
    /// ```

    pub fn len(&self) -> usize {
        link_count(&self.root)
    }

    /// Walks the tree, gathers various metrics about nodes, keys and values, and returns a [`Stats`](
    /// ./struct.Stats.html) structure to sum it up.
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// let mut map = Tst::new();
    /// assert_eq!(map.len(), 0);
    ///
    /// map.insert("foo", "🍄🍄");
    /// assert_eq!(map.len(), 1);
    ///
    /// let stats = map.stat();
    /// assert_eq!(stats.count.nodes, 1);
    /// ```
    ///
    /// See [Stats]( ./struct.Stats.html) for a detailed description of available fields.

    pub fn stat(&self) -> Stats {
        let empty_stats: Stats = Default::default();

        let mut stats = stat_r(empty_stats, &self.root, 0, 0, 0);

        stats.bytes.node = mem::size_of::<Node<T>>();
        stats.bytes.char_node = mem::size_of::<CharNode>();
        stats.bytes.total = mem::size_of::<Tst<T>>()
            + stats.count.nodes * stats.bytes.node
            + (stats.count.char_nodes - stats.count.nodes) * stats.bytes.char_node;

        stats
    }

    /// Deletes every node and value stored in the tree.
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// let mut map = Tst::new();
    /// assert_eq!(map.len(), 0);
    ///
    /// map.insert("foo", "🍄🍄");
    /// assert_eq!(map.len(), 1);
    ///
    /// map.clear();
    /// assert_eq!(map.len(), 0);

    pub fn clear(&mut self) {
        self.root = None;
    }

    /// Recursively walks the tree and calls `callback` closure on each immutable value. Values are found in
    /// alphabetical order of keys. See also the [`iter`]( ./struct.Tst.html#method.iter) method which produces the
    /// same sequence of values in a non-recursive way.
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// # use ternary_tree::tst;
    /// let map = tst!["foo" => "🍄🍄", "bar" => "🐟", "baz" => "㵅"];
    ///
    /// let mut v = Vec::new();
    /// map.visit_values(|s| v.push(s.clone()));
    /// assert_eq!(v, ["🐟", "㵅", "🍄🍄"]);
    /// ```

    pub fn visit_values<C>(&self, mut callback: C)
    where
        C: FnMut(&T),
    {
        visit_values_gen::<&Link<T>, C>((&self.root).unwrap(), &mut callback);
    }

    /// Recursively walks the tree and calls `callback` closure on each mutable value. The same as
    /// [`visit_values`]( ./struct.Tst.html#method.visit_values), except the `_mut` version works on mutable
    /// values, and does not have an iterator counterpart.

    pub fn visit_values_mut<C>(&mut self, mut callback: C)
    where
        C: FnMut(&mut T),
    {
        visit_values_gen::<&mut Link<T>, C>((&mut self.root).unwrap(), &mut callback);
    }

    /// Recursively walks the tree and calls `callback` closure on each immutable value whose key begins with
    /// `key_prefix`. Values are found in alphabetical order of keys. See also the [`iter_complete`](
    /// ./struct.Tst.html#method.iter_complete) method which produces the same sequence of values in a
    /// non-recursive way.
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// # use ternary_tree::tst;
    /// let map = tst!["foo" => "🍄🍄", "bar" => "🐟", "baz" => "㵅"];
    ///
    /// let mut v = Vec::new();
    /// map.visit_complete_values("ba", |s| v.push(s.clone()));
    /// assert_eq!(v, ["🐟", "㵅"]);
    /// ```
    ///
    /// Some key is not a prefix of itself. In the previous example, `visit_complete_values` called with `foo`
    /// prefix would find no value
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// # use ternary_tree::tst;
    /// # let map = tst!["foo" => "🍄🍄", "bar" => "🐟", "baz" => "㵅"];
    /// let mut v = Vec::new();
    /// map.visit_complete_values("foo", |s| v.push(s.clone()));
    /// assert_eq!(v.is_empty(), true);
    /// ```
    ///
    /// If `key_prefix` is empty, `visit_complete_values` behaves as [`visit_values`](
    /// ./struct.Tst.html#method.visit_values), and all values stored in the tree are found.

    pub fn visit_complete_values<C>(&self, key_prefix: &str, mut callback: C)
    where
        C: FnMut(&T),
    {
        let (_, new_root) =
            find_complete_root_gen::<&Link<T>>(&self.root, &mut key_prefix.chars().peekable());
        visit_values_gen::<&Link<T>, C>(new_root, &mut callback);
    }

    /// Recursively walks the tree and calls `callback` closure on each mutable value whose key begins with
    /// `key_prefix`. The same as [`visit_complete_values`]( ./struct.Tst.html#method.visit_complete_values),
    /// except the `_mut` version works on mutable values, and does not have an iterator counterpart.

    pub fn visit_complete_values_mut<C>(&mut self, key_prefix: &str, mut callback: C)
    where
        C: FnMut(&mut T),
    {
        let (_, new_root) = find_complete_root_gen::<&mut Link<T>>(
            &mut self.root,
            &mut key_prefix.chars().peekable(),
        );
        visit_values_gen::<&mut Link<T>, C>(new_root, &mut callback)
    }

    /// Recursively walks the tree and calls `callback` closure on each immutable value whose key is _close_ to
    /// `key`. A key is considered _close_ to `key` within a [Hamming distance](
    /// http://en.wikipedia.org/wiki/Hamming_distance) of `range` from `key`. Values are found in alphabetical
    /// order of keys. See also the [`iter_neighbor`]( ./struct.Tst.html#method.iter_neighbor) method which
    /// produces the same sequence of values in a non-recursive way.
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// # use ternary_tree::tst;
    /// let map = tst!["fo" => "🍄", "bar" => "🐟", "baz" => "㵅", "fooo" => "🍄🍄🍄"];
    ///
    /// let mut v = Vec::new();
    /// map.visit_neighbor_values("bar", 1, |s| v.push(s.clone()));
    /// assert_eq!(v, ["🐟", "㵅"]);
    /// ```
    ///
    /// An empty `key` is allowed, and with a `range` of _n_, it will find all values whose key length is up to
    /// _n_. In the previous example `visit_neighbor_values` called with `""` key and range `3` would find all
    /// value whose key length is ≤ 3
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// # use ternary_tree::tst;
    /// let map = tst!["fo" => "🍄", "bar" => "🐟", "baz" => "㵅", "fooo" => "🍄🍄🍄"];
    ///
    /// let mut v = Vec::new();
    /// map.visit_neighbor_values("", 3, |s| v.push(s.clone()));
    /// assert_eq!(v, ["🐟", "㵅", "🍄"]);
    /// ```

    pub fn visit_neighbor_values<C>(&self, key: &str, range: usize, mut callback: C)
    where
        C: FnMut(&T),
    {
        visit_neighbor_values_gen::<&Link<T>, C>(
            &self.root,
            &mut key.chars().peekable(),
            key.chars().count(),
            range,
            &mut callback,
        );
    }

    /// Recursively walks the tree and calls `callback` closure on each mutable value whose key is _close_ to `key`
    /// ([Hamming distance]( http://en.wikipedia.org/wiki/Hamming_distance) of `range`). The same as
    /// [`visit_neighbor_values`]( ./struct.Tst.html#method.visit_neighbor_values), except the `_mut` version works
    /// on mutable values, and does not have an iterator counterpart.

    pub fn visit_neighbor_values_mut<C>(&mut self, key: &str, range: usize, mut callback: C)
    where
        C: FnMut(&mut T),
    {
        visit_neighbor_values_gen::<&mut Link<T>, C>(
            &mut self.root,
            &mut key.chars().peekable(),
            key.chars().count(),
            range,
            &mut callback,
        );
    }

    /// Recursively walks the tree and calls `callback` closure on each immutable value whose key _matches_
    /// `pattern`. The `pattern` is a string slice where each `joker` character stands for _any_ character. Values
    /// are found in alphabetical order of keys. See also the [`iter_crossword`](
    /// ./struct.Tst.html#method.iter_crossword) method which produces the same sequence of values in a
    /// non-recursive way.
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// # use ternary_tree::tst;
    /// let map = tst!["fo" => "🍄", "bar" => "🐟", "baz" => "㵅", "fooo" => "🍄🍄🍄"];
    ///
    /// let mut v = Vec::new();
    /// map.visit_crossword_values("?a?", '?', |s| v.push(s.clone()));
    /// assert_eq!(v, ["🐟", "㵅"]);
    /// ```
    ///
    /// A `pattern` of _n_ `joker` characters will find all values whose key length is exactly _n_
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// # use ternary_tree::tst;
    /// let mut v = Vec::new();
    /// let map = tst!["fo" => "🍄", "bar" => "🐟", "baz" => "㵅", "fooo" => "🍄🍄🍄"];
    ///
    /// map.visit_crossword_values("???", '?', |s| v.push(s.clone()));
    /// assert_eq!(v, ["🐟", "㵅"]);
    /// ```
    ///
    /// An empty `pattern` is meaningless, and does not find any value.

    pub fn visit_crossword_values<C>(&self, pattern: &str, joker: char, mut callback: C)
    where
        C: FnMut(&T),
    {
        visit_crossword_values_gen::<&Link<T>, C>(
            &self.root,
            &mut pattern.chars().peekable(),
            joker,
            &mut callback,
        )
    }

    /// Recursively walks the tree and calls `callback` closure on each mutable value whose key _matches_ `pattern`
    /// with `joker` characters. The same as [`visit_crossword_values`](
    /// ./struct.Tst.html#method.visit_crossword_values), except the `_mut` version works on mutable values, and
    /// does not have an iterator counterpart.

    pub fn visit_crossword_values_mut<C>(&mut self, pattern: &str, joker: char, mut callback: C)
    where
        C: FnMut(&mut T),
    {
        visit_crossword_values_gen::<&mut Link<T>, C>(
            &mut self.root,
            &mut pattern.chars().peekable(),
            joker,
            &mut callback,
        )
    }

    /// Dump the tree in `writer` using the _dot_ language of [Graphviz]( http://www.graphviz.org) tools. A checked
    /// box "☑" denotes a node which stores a value (it corresponds to the last character of a key). An empty box
    /// "☐" means that the node has no value. Mostly used for documentation and debugging purpose. See the [module
    /// documentation]( ./index.html) for an example.

    pub fn pretty_print(&self, writer: &mut dyn Write) {
        let _ = writeln!(writer, "digraph {{");
        let _ = writeln!(writer, "node [shape=plaintext]");

        let mut ids = Tst::new();

        pretty_print_r(&self.root, &mut ids, writer);

        let _ = writeln!(writer, "}}");
    }

    /// Create a [double-ended]( http://doc.rust-lang.org/std/iter/trait.DoubleEndedIterator.html) iterator which
    /// successively returns all values of the tree. Values are immutable, and are found in alphabetical order of
    /// keys by [`next`]( ./struct.TstIterator.html#method.next), and in the opposite order by [`next_back`](
    /// ./struct.TstIterator.html#method.next_back). Methods [`current_key`](
    /// ./struct.TstIterator.html#method.current_key) and [`current_key_back`](
    /// ./struct.TstIterator.html#method.current_key_back) regenerate the key associated with the last value
    /// returned by [`next`]( ./struct.TstIterator.html#method.next) or [`next_back`](
    /// struct.TstIterator.html#method.next_back). See also the [`visit_value_mut`](
    /// ./struct.Tst.html#method.visit_values_mut) method which produces the same sequence of mutable values.
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// # use ternary_tree::tst;
    /// let map = tst!["foo" => "🍄🍄", "bar" => "🐟", "baz" => "㵅"];
    ///
    /// let mut it = map.iter();
    ///
    /// let first_value = it.next();
    /// let last_value = it.next_back();
    ///
    /// let first_key = it.current_key();
    /// let last_key = it.current_key_back();
    ///
    /// assert_eq!((first_key, first_value), ("bar".to_string(), Some(&"🐟")));
    /// assert_eq!((last_key, last_value), ("foo".to_string(), Some(&"🍄🍄")));
    /// ```

    pub fn iter(&self) -> TstIterator<T> {
        TstIterator::<T>::new(&self)
    }

    /// Create a [double-ended]( http://doc.rust-lang.org/std/iter/trait.DoubleEndedIterator.html) iterator which
    /// successively returns all values whose key begins with `prefix`. Values are immutable, and are found in
    /// alphabetical order of keys by [`next`]( ./struct.TstCompleteIterator.html#method.next), and in the opposite
    /// order by [`next_back`]( ./struct.TstCompleteIterator.html#method.next_back). Methods [`current_key`](
    /// ./struct.TstCompleteIterator.html#method.current_key) and [`current_key_back`](
    /// ./struct.TstCompleteIterator.html#method.current_key_back) regenerate the key associated with the last
    /// value returned by [`next`]( ./struct.TstCompleteIterator.html#method.next) or [`next_back`](
    /// struct.TstCompleteIterator.html#method.next_back). See also the [`visit_complete_value_mut`](
    /// ./struct.Tst.html#method.visit_complete_values_mut) method which produces the same sequence of mutable
    /// values.
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// # use ternary_tree::tst;
    /// let map = tst!["foo" => "🍄🍄", "bar" => "🐟", "baz" => "㵅"];
    ///
    /// let mut it = map.iter_complete("b");
    ///
    /// let first_value = it.next();
    /// let last_value = it.next_back();
    ///
    /// let first_key = it.current_key();
    /// let last_key = it.current_key_back();
    ///
    /// assert_eq!((first_key, first_value), ("bar".to_string(), Some(&"🐟")));
    /// assert_eq!((last_key, last_value), ("baz".to_string(), Some(&"㵅")));
    /// ```

    pub fn iter_complete(&self, prefix: &str) -> TstCompleteIterator<T> {
        TstCompleteIterator::<T>::new(&self, prefix)
    }

    /// Create a [double-ended]( http://doc.rust-lang.org/std/iter/trait.DoubleEndedIterator.html) iterator which
    /// successively returns all values whose key is _close_ to `key`. A key is considered _close_ to `key` within
    /// a [Hamming distance]( http://en.wikipedia.org/wiki/Hamming_distance) of `range` from `key`. An empty `key`
    /// is allowed, and with a `range` of _n_, it will find all values whose key length is up to _n_. Values are
    /// immutable, and are found in alphabetical order of keys by [`next`](
    /// ./struct.TstNeighborIterator.html#method.next), and in the opposite order by [`next_back`](
    /// ./struct.TstNeighborIterator.html#method.next_back). Methods [`current_key`](
    /// ./struct.TstNeighborIterator.html#method.current_key) and [`current_key_back`](
    /// ./struct.TstNeighborIterator.html#method.current_key_back) regenerate the key associated with the last
    /// value returned by [`next`]( ./struct.TstNeighborIterator.html#method.next) or [`next_back`](
    /// struct.TstNeighborIterator.html#method.next_back). See also the [`visit_neighbor_value_mut`](
    /// ./struct.Tst.html#method.visit_neighbor_values_mut) method which produces the same sequence of mutable
    /// values.
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// # use ternary_tree::tst;
    /// let map = tst!["foo" => "🍄🍄", "bar" => "🐟", "baz" => "㵅"];
    ///
    /// let mut it = map.iter_neighbor("bar", 1);
    ///
    /// let first_value = it.next();
    /// let last_value = it.next_back();
    ///
    /// let first_key = it.current_key();
    /// let last_key = it.current_key_back();
    ///
    /// assert_eq!((first_key, first_value), ("bar".to_string(), Some(&"🐟")));
    /// assert_eq!((last_key, last_value), ("baz".to_string(), Some(&"㵅")));
    /// ```

    pub fn iter_neighbor<'a, 'b>(
        &'a self,
        key: &'b str,
        range: usize,
    ) -> TstNeighborIterator<'a, 'b, T> {
        TstNeighborIterator::<T>::new(&self, key, range)
    }

    /// Create a [double-ended]( http://doc.rust-lang.org/std/iter/trait.DoubleEndedIterator.html) iterator which
    /// successively returns all values whose key _matches_ `pattern`. The `pattern` is a string slice where each
    /// `joker` character stands for _any_ character. A `pattern` of _n_ `joker` characters will find all values
    /// whose key length is exactly _n_. Values are immutable, and are found in alphabetical order of keys by
    /// [`next`]( ./struct.TstCrosswordIterator.html#method.next), and in the opposite order by [`next_back`](
    /// ./struct.TstCrosswordIterator.html#method.next_back). Methods [`current_key`](
    /// ./struct.TstCrosswordIterator.html#method.current_key) and [`current_key_back`](
    /// ./struct.TstCrosswordIterator.html#method.current_key_back) regenerate the key associated with the last
    /// value returned by [`next`]( ./struct.TstCrosswordIterator.html#method.next) or [`next_back`](
    /// struct.TstCrosswordIterator.html#method.next_back). See also the [`visit_crossword_value_mut`](
    /// ./struct.Tst.html#method.visit_crossword_values_mut) method which produces the same sequence of mutable
    /// values.
    ///
    /// ```
    /// # use ternary_tree::Tst;
    /// # use ternary_tree::tst;
    /// let map = tst!["foo" => "🍄🍄", "bar" => "🐟", "baz" => "㵅"];
    ///
    /// let mut it = map.iter_crossword("?a?", '?');
    ///
    /// let first_value = it.next();
    /// let last_value = it.next_back();
    ///
    /// let first_key = it.current_key();
    /// let last_key = it.current_key_back();
    ///
    /// assert_eq!((first_key, first_value), ("bar".to_string(), Some(&"🐟")));
    /// assert_eq!((last_key, last_value), ("baz".to_string(), Some(&"㵅")));
    /// ```

    pub fn iter_crossword<'a, 'b>(
        &'a self,
        pattern: &'b str,
        joker: char,
    ) -> TstCrosswordIterator<'a, 'b, T> {
        TstCrosswordIterator::<T>::new(&self, pattern, joker)
    }

    pub fn verify(&self) {
        verify_r(&self.root);
    }
}

/// A shortcut macro to help create a small tree with a list of known `"key" => value` pairs. Calls [`insert`](
/// ./struct.Tst.html#method.insert) on each pair, in order.
///
/// ```
/// # use ternary_tree::Tst;
/// # use ternary_tree::tst;
/// let map = tst!["fo" => "🍄", "bar" => "🐟", "baz" => "㵅", "fooo" => "🍄🍄🍄"];
/// assert_eq!(map.len(), 4)
/// ````

#[macro_export]
macro_rules! tst {

    () => {{
        $crate::Tst::new()
    }};

    ($($key:expr => $value:expr,)+) => (tst!($($key => $value),+));

    ($($key: expr => $val: expr),*) => {{

        let mut tst = $crate::Tst::new();
        $(
            tst.insert($key, $val);
        )*

        tst
    }};
}

#[derive(Debug, PartialEq)]
enum TstIteratorAction {
    GoLeft,
    Visit,
    GoMiddle,
    GoRight,
}

use self::TstIteratorAction::*;

/// A [double-ended]( http://doc.rust-lang.org/std/iter/trait.DoubleEndedIterator.html) iterator which
/// successively returns all values of the tree. See [`iter`]( struct.Tst.html#method.iter) method for a brief
/// description with a short example.

#[derive(Debug)]
pub struct TstIterator<'a, T: 'a> {
    todo_i: Vec<(&'a Node<T>, TstIteratorAction)>,
    last_i: Option<&'a Node<T>>,

    todo_j: Vec<(&'a Node<T>, TstIteratorAction)>,
    last_j: Option<&'a Node<T>>,
}

macro_rules! gen_it_path {
    ($path_of_x:ident, $todo_x:ident, $a1:expr, $a2:expr) => {
        pub fn $path_of_x(&self) -> String {
            let mut path = String::new();

            for todo in self.$todo_x.iter() {
                if todo.1 == $a1 || todo.1 == $a2 {
                    push_chain_to_string(&todo.0.label, &mut path);
                }
            }

            path
        }
    };
}

impl<'a, T> TstIterator<'a, T> {
    pub fn new(tst: &'a Tst<T>) -> Self {
        TstIterator::new_from_root((&tst.root).unwrap())
    }

    fn new_from_root(root: Option<&'a Node<T>>) -> Self {
        let mut it = TstIterator {
            todo_i: Vec::new(),
            last_i: None,
            todo_j: Vec::new(),
            last_j: None,
        };

        if let Some(node) = root {
            it.todo_i.push((node, GoLeft));
            it.todo_j.push((node, GoRight));
        }

        it
    }

    gen_it_path!(current_key, todo_i, GoMiddle, GoRight);
    gen_it_path!(current_key_back, todo_j, Visit, GoLeft);
}

impl<'a, T> Iterator for TstIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let mut found = None;

        while let Some((node, action)) = self.todo_i.pop() {
            match action {
                GoLeft => {
                    self.todo_i.push((node, Visit));

                    if let Some(ref child) = node.left {
                        self.todo_i.push((child, GoLeft));
                    }
                }

                Visit => {
                    if node.value.is_some() {
                        if let Some(node_j) = self.last_j {
                            if ptr::eq(node, node_j) {
                                self.todo_i.clear();
                                self.todo_j.clear();

                                found = None;
                                break;
                            }
                        }
                    }

                    self.todo_i.push((node, GoMiddle));

                    if let Some(ref value) = node.value {
                        self.last_i = Some(node);
                        found = Some(value);

                        break;
                    }
                }

                GoMiddle => {
                    self.todo_i.push((node, GoRight));

                    if let Some(ref child) = node.middle {
                        self.todo_i.push((child, GoLeft));
                    }
                }

                GoRight => {
                    if let Some(ref child) = node.right {
                        self.todo_i.push((child, GoLeft));
                    }
                }
            }
        }

        found
    }
}

impl<'a, T> IntoIterator for &'a Tst<T> {
    type Item = &'a T;
    type IntoIter = TstIterator<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> DoubleEndedIterator for TstIterator<'a, T> {
    fn next_back(&mut self) -> Option<&'a T> {
        let mut found = None;

        while let Some((node, action)) = self.todo_j.pop() {
            match action {
                GoRight => {
                    self.todo_j.push((node, GoMiddle));

                    if let Some(ref child) = node.right {
                        self.todo_j.push((child, GoRight));
                    }
                }

                Visit => {
                    if node.value.is_some() {
                        if let Some(node_i) = self.last_i {
                            if ptr::eq(node, node_i) {
                                self.todo_i.clear();
                                self.todo_j.clear();

                                found = None;
                                break;
                            }
                        }
                    }

                    self.todo_j.push((node, GoLeft));

                    if let Some(ref value) = node.value {
                        self.last_j = Some(node);
                        found = Some(value);

                        break;
                    }
                }

                GoMiddle => {
                    self.todo_j.push((node, Visit));

                    if let Some(ref child) = node.middle {
                        self.todo_j.push((child, GoRight));
                    }
                }

                GoLeft => {
                    if let Some(ref child) = node.left {
                        self.todo_j.push((child, GoRight));
                    }
                }
            }
        }

        found
    }
}

/// A [double-ended]( http://doc.rust-lang.org/std/iter/trait.DoubleEndedIterator.html) iterator which
/// successively returns all values whose key begins with `prefix`. See [`iter_complete`](
/// struct.Tst.html#method.iter_complete) method for a brief description with a short example.

#[derive(Debug)]
pub struct TstCompleteIterator<'a, T: 'a> {
    it: TstIterator<'a, T>,
    prefix: String,
}

impl<'a, T> TstCompleteIterator<'a, T> {
    pub fn new(tst: &'a Tst<T>, key_prefix: &str) -> Self {
        let (prefix, new_root) =
            find_complete_root_gen::<&Link<T>>(&tst.root, &mut key_prefix.chars().peekable());
        let mut path = key_prefix.to_string();
        if let Some(char_node) = prefix {
            push_chain_to_string(char_node, &mut path)
        }
        TstCompleteIterator {
            it: TstIterator::<T>::new_from_root(new_root),
            prefix: path,
        }
    }

    pub fn current_key(&self) -> String {
        self.prefix.clone() + &self.it.current_key()
    }

    pub fn current_key_back(&self) -> String {
        self.prefix.clone() + &self.it.current_key_back()
    }
}

impl<'a, T> Iterator for TstCompleteIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.it.next()
    }
}

impl<'a, T> DoubleEndedIterator for TstCompleteIterator<'a, T> {
    fn next_back(&mut self) -> Option<&'a T> {
        self.it.next_back()
    }
}

type TstNeighborIteratorTodoItem<'a, 'b, T> = (
    /*node:*/
    &'a Node<T>,
    /*action:*/
    TstIteratorAction,
    /*key:*/
    Peekable<Chars<'b>>,
    /*key_len:*/
    usize,
    /*range:*/
    usize,
);

type TstNeighborIteratorTodo<'a, 'b, T> = Vec<TstNeighborIteratorTodoItem<'a, 'b, T>>;

/// A [double-ended]( http://doc.rust-lang.org/std/iter/trait.DoubleEndedIterator.html) iterator which
/// successively returns all values whose key is _close_ to `key`. See [`iter_neighbor`](
/// struct.Tst.html#method.iter_neighbor) method for a brief description with a short example.

#[derive(Debug)]
pub struct TstNeighborIterator<'a, 'b, T: 'a> {
    todo_i: TstNeighborIteratorTodo<'a, 'b, T>,
    last_i: Option<&'a Node<T>>,

    todo_j: TstNeighborIteratorTodo<'a, 'b, T>,
    last_j: Option<&'a Node<T>>,
}

impl<'a, 'b, T> TstNeighborIterator<'a, 'b, T> {
    pub fn new(tst: &'a Tst<T>, key: &'b str, range: usize) -> Self {
        let mut it = TstNeighborIterator {
            todo_i: Vec::new(),
            last_i: None,
            todo_j: Vec::new(),
            last_j: None,
        };

        if let Some(ref node) = &tst.root {
            let key_len = key.chars().count();
            it.todo_i
                .push((node, GoLeft, key.chars().peekable(), key_len, range));
            it.todo_j
                .push((node, GoRight, key.chars().peekable(), key_len, range));
        }

        it
    }

    gen_it_path!(current_key, todo_i, GoMiddle, GoRight);
    gen_it_path!(current_key_back, todo_j, Visit, GoLeft);
}

impl<'a, 'b, T> Iterator for TstNeighborIterator<'a, 'b, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let mut found = None;

        while let Some((node, action, mut key, mut key_len, range)) = self.todo_i.pop() {
            match action {
                GoLeft => {
                    self.todo_i.push((node, Visit, key.clone(), key_len, range));

                    if 0 < range || key.peek().map_or(false, |label| label < &node.label.first) {
                        if let Some(ref child) = node.left {
                            self.todo_i.push((child, GoLeft, key, key_len, range));
                        }
                    }
                }

                Visit => {
                    if node.value.is_some() {
                        if let Some(node_j) = self.last_j {
                            if ptr::eq(node, node_j) {
                                self.todo_i.clear();
                                self.todo_j.clear();

                                found = None;
                                break;
                            }
                        }
                    }

                    self.todo_i
                        .push((node, GoMiddle, key.clone(), key_len, range));

                    if let Some(ref value) = node.value {
                        let cost = traverse_chain_hamming_cost(&node.label, &mut key, &mut key_len);

                        if cost + key_len <= range {
                            self.last_i = Some(node);
                            found = Some(value);
                            break;
                        }
                    }
                }

                GoMiddle => {
                    self.todo_i
                        .push((node, GoRight, key.clone(), key_len, range));
                    let cost = traverse_chain_hamming_cost(&node.label, &mut key, &mut key_len);

                    if cost <= range {
                        if let Some(ref child) = node.middle {
                            self.todo_i
                                .push((child, GoLeft, key, key_len, range - cost));
                        }
                    }
                }

                GoRight => {
                    if 0 < range || key.peek().map_or(false, |label| label > &node.label.first) {
                        if let Some(ref child) = node.right {
                            self.todo_i.push((child, GoLeft, key, key_len, range));
                        }
                    }
                }
            }
        }

        found
    }
}

impl<'a, 'b, T> DoubleEndedIterator for TstNeighborIterator<'a, 'b, T> {
    fn next_back(&mut self) -> Option<&'a T> {
        let mut found = None;

        while let Some((node, action, mut key, mut key_len, range)) = self.todo_j.pop() {
            match action {
                GoRight => {
                    self.todo_j
                        .push((node, GoMiddle, key.clone(), key_len, range));
                    if 0 < range || key.peek().map_or(false, |label| label > &node.label.first) {
                        if let Some(ref child) = node.right {
                            self.todo_j.push((child, GoRight, key, key_len, range));
                        }
                    }
                }

                Visit => {
                    if node.value.is_some() {
                        if let Some(node_i) = self.last_i {
                            if ptr::eq(node, node_i) {
                                self.todo_i.clear();
                                self.todo_j.clear();

                                found = None;
                                break;
                            }
                        }
                    }

                    self.todo_j
                        .push((node, GoLeft, key.clone(), key_len, range));

                    if let Some(ref value) = node.value {
                        let cost = traverse_chain_hamming_cost(&node.label, &mut key, &mut key_len);

                        if cost + key_len <= range {
                            self.last_j = Some(node);
                            found = Some(value);
                            break;
                        }
                    }
                }

                GoMiddle => {
                    self.todo_j.push((node, Visit, key.clone(), key_len, range));

                    let cost = traverse_chain_hamming_cost(&node.label, &mut key, &mut key_len);
                    if cost <= range {
                        if let Some(ref child) = node.middle {
                            self.todo_j
                                .push((child, GoRight, key, key_len, range - cost));
                        }
                    }
                }

                GoLeft => {
                    if 0 < range || key.peek().map_or(false, |label| label < &node.label.first) {
                        if let Some(ref child) = node.left {
                            self.todo_j.push((child, GoRight, key, key_len, range));
                        }
                    }
                }
            }
        }

        found
    }
}

/// A [double-ended]( http://doc.rust-lang.org/std/iter/trait.DoubleEndedIterator.html) iterator which
/// successively returns all values whose key _matches_ `pattern`. See [`iter_crossword`](
/// struct.Tst.html#method.iter_crossword) method for a brief description with a short example.

#[derive(Debug)]
pub struct TstCrosswordIterator<'a, 'b, T: 'a> {
    todo_i: Vec<(&'a Node<T>, TstIteratorAction, Peekable<Chars<'b>>)>,
    last_i: Option<&'a Node<T>>,

    todo_j: Vec<(&'a Node<T>, TstIteratorAction, Peekable<Chars<'b>>)>,
    last_j: Option<&'a Node<T>>,

    joker: char,
}

impl<'a, 'b, T> TstCrosswordIterator<'a, 'b, T> {
    pub fn new(tst: &'a Tst<T>, key: &'b str, joker: char) -> Self {
        let mut it = TstCrosswordIterator {
            todo_i: Vec::new(),
            last_i: None,
            todo_j: Vec::new(),
            last_j: None,
            joker,
        };

        if let Some(ref node) = &tst.root {
            it.todo_i.push((node, GoLeft, key.chars().peekable()));
            it.todo_j.push((node, GoRight, key.chars().peekable()));
        }

        it
    }

    gen_it_path!(current_key, todo_i, GoMiddle, GoRight);
    gen_it_path!(current_key_back, todo_j, Visit, GoLeft);
}

impl<'a, 'b, T> Iterator for TstCrosswordIterator<'a, 'b, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let mut found = None;

        while let Some((node, action, mut key)) = self.todo_i.pop() {
            match action {
                GoLeft => {
                    self.todo_i.push((node, Visit, key.clone()));
                    if let (Some(&key_letter), Some(ref child)) = (key.peek(), node.left.as_ref()) {
                        if key_letter == self.joker || key_letter < node.label.first {
                            self.todo_i.push((child, GoLeft, key));
                        }
                    }
                }

                Visit => {
                    if node.value.is_some() {
                        if let Some(node_j) = self.last_j {
                            if ptr::eq(node, node_j) {
                                self.todo_i.clear();
                                self.todo_j.clear();

                                found = None;
                                break;
                            }
                        }
                    }
                    self.todo_i.push((node, GoMiddle, key.clone()));

                    if let Some(ref value) = node.value {
                        if can_traverse_chain_with_jokers(&node.label, &mut key, self.joker) {
                            if key.peek().is_none() {
                                self.last_i = Some(node);
                                found = Some(value);
                                break;
                            }
                        }
                    }
                }

                GoMiddle => {
                    self.todo_i.push((node, GoRight, key.clone()));

                    if let Some(ref child) = node.middle {
                        if can_traverse_chain_with_jokers(&node.label, &mut key, self.joker) {
                            self.todo_i.push((child, GoLeft, key));
                        }
                    }
                }

                GoRight => {
                    if let (Some(&key_letter), Some(ref child)) = (key.peek(), node.right.as_ref())
                    {
                        if key_letter == self.joker || key_letter > node.label.first {
                            self.todo_i.push((child, GoLeft, key));
                        }
                    }
                }
            }
        }

        found
    }
}

impl<'a, 'b, T> DoubleEndedIterator for TstCrosswordIterator<'a, 'b, T> {
    fn next_back(&mut self) -> Option<&'a T> {
        let mut found = None;

        while let Some((node, action, mut key)) = self.todo_j.pop() {
            match action {
                GoRight => {
                    self.todo_j.push((node, GoMiddle, key.clone()));
                    if let (Some(&key_letter), Some(ref child)) = (key.peek(), node.right.as_ref())
                    {
                        if key_letter == self.joker || key_letter > node.label.first {
                            self.todo_j.push((child, GoRight, key));
                        }
                    }
                }

                Visit => {
                    if node.value.is_some() {
                        if let Some(node_i) = self.last_i {
                            if ptr::eq(node, node_i) {
                                self.todo_i.clear();
                                self.todo_j.clear();

                                found = None;
                                break;
                            }
                        }
                    }

                    self.todo_j.push((node, GoLeft, key.clone()));

                    if let Some(ref value) = node.value {
                        if can_traverse_chain_with_jokers(&node.label, &mut key, self.joker) {
                            if key.peek().is_none() {
                                self.last_j = Some(node);
                                found = Some(value);
                                break;
                            }
                        }
                    }
                }

                GoMiddle => {
                    self.todo_j.push((node, Visit, key.clone()));

                    if let Some(ref child) = node.middle {
                        if can_traverse_chain_with_jokers(&node.label, &mut key, self.joker) {
                            self.todo_j.push((child, GoRight, key));
                        }
                    }
                }

                GoLeft => {
                    if let (Some(&key_letter), Some(ref child)) = (key.peek(), node.left.as_ref()) {
                        if key_letter == self.joker || key_letter < node.label.first {
                            self.todo_j.push((child, GoRight, key));
                        }
                    }
                }
            }
        }

        found
    }
}
