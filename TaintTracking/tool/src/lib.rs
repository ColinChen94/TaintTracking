extern crate libc;
extern crate bit_vec;

use std::ptr;
use libc::uint32_t;
use bit_vec::BitVec;

pub struct Table {
    record: Vec<*const Node>,
}

pub struct Tree {
    root: Link,
}

type Link = Option<Box<Node>>;

pub struct Node {
    left: Link,
    right: Link,
    parent: *const Node,
    label: Option<usize>,
    pos: Option<bool>, // true means right child of parent while false means left child.
}

impl Table {
    pub fn new() -> Self {
        Table {
            record: Vec::new(),
        }
    }
}

impl Tree {
    pub fn new() -> Self {
        Tree { root: Some(Box::new(Node::new())), }
    }
}

impl Node {
    pub fn new() -> Self {
        Node {
            label: None,
            left: None,
            right: None,
            parent: ptr::null(),
            pos: None,
        }
    }
}

pub fn insert(root: &mut Tree, vector: &mut BitVec, nodes: &mut Table) -> Option<usize> {
    insert_vector(&mut root.root, vector, &mut nodes.record)
}

fn insert_vector(root: &mut Link, vector: &mut BitVec, nodes: &mut Vec<*const Node>) -> Option<usize> {
    let len = vector.len();
    let mut pos = len;

    let root_node = root.as_mut().unwrap();
    let root_point: *const Node = & **root_node;

    vector.iter().rfind(|x| {
        if !*x {
            pos = pos - 1;
        }
        *x
    });
    vector.truncate(pos);

    if vector.is_empty() {
        if root_node.label.is_none() {
            root_node.label = Some(nodes.len());
            let raw_node: *const _ = & **root_node;
            nodes.push(raw_node);
        }
        return root_node.label;
    }

    let mut child;
    if vector[0] == false {
        child = &mut root_node.left;
    } else {
        child = &mut root_node.right;
    }

    if child.is_none() {
        let mut new_node = Box::new(Node::new());
        new_node.pos = Some(vector[0] == true);
        new_node.parent = root_point;
        if vector.len() == 1 {
            new_node.label = Some(nodes.len());
            let raw_node: *const _ = & *new_node;
            nodes.push(raw_node);
        }
        *child = Some(new_node);
    }

    if vector.len() == 1 {
        let child_node = child.as_mut().unwrap();
        if child_node.label.is_none() {
            child_node.label = Some(nodes.len());
            let raw_node: *const _ = & **child_node;
            nodes.push(raw_node);
        }
        return child_node.label;
    } else {
        let mut vector_new = BitVec::new();
        let mut iter = vector.iter().skip(1);
        while let Some(bit) = iter.next() {
            vector_new.push(bit);
        }

        return insert_vector(&mut child, &mut vector_new, nodes);

        // I cannot use vector.split_off(1)
        // I cannot use vector.iter().skip(0).collect()
        // So stupid container the BitVec is!
        // The resulting problem is that a useless bitvec left at each recursion
    }

}

pub fn find(label: usize, nodes: &Table) -> BitVec {
    assert!(label < nodes.record.len());

    let mut node: & Node;
    unsafe {
        node = &*(nodes.record[label]);
    }

    let mut vector_rev = BitVec::new();

    while !node.parent.is_null() {
        vector_rev.push(node.pos.unwrap());
        unsafe {
            node = &*(node.parent);
        }
    }

    let mut vector = BitVec::new();
    let mut iter = vector_rev.iter();

    while let Some(bit) = iter.next_back() {
        vector.push(bit);
    }

    return vector;
}

pub fn union(label1: usize, label2: usize, nodes: &mut Table, root: &mut Tree) -> Option<usize> {
    let mut vector1 = find(label1, &*nodes);
    let mut vector2 = find(label2, &*nodes);
    let len1 = vector1.len();
    let len2 = vector2.len();

    if len1 < len2 {
        vector1.grow(len2-len1, false);
    } else {
        vector2.grow(len1-len2, false);
    }
    vector1.union(&vector2);

    insert_vector(&mut root.root, &mut vector1, &mut nodes.record)
}

#[cfg(test)]
mod test {

    use bit_vec::BitVec;
    use super::*;

    #[test]
    fn test_insert() {
        let mut tree = Tree::new();
        let mut nodes = Table::new();
        let mut bv1 = BitVec::from_elem(1, false);
        let mut bv2 = BitVec::from_elem(2, true);
        let mut bv3 = BitVec::from_elem(3, false);
        let mut bv4 = BitVec::from_elem(1, true);
        let mut bv5 = BitVec::from_bytes(&[0b01110100, 0b10010010]);
        assert_eq!(insert(&mut tree, &mut bv1, &mut nodes), Some(0));
        assert_eq!(insert(&mut tree, &mut bv2, &mut nodes), Some(1));
        assert_eq!(insert(&mut tree, &mut bv3, &mut nodes), Some(0));
        assert_eq!(insert(&mut tree, &mut bv4, &mut nodes), Some(2));
        assert_eq!(insert(&mut tree, &mut bv5, &mut nodes), Some(3));
    }

    #[test]
    fn test_find() {
        let mut tree = Tree::new();
        let mut nodes = Table::new();
        let mut bv1 = BitVec::from_elem(1, false);
        let mut bv2 = BitVec::from_elem(2, true);
        let mut bv3 = BitVec::from_elem(3, false);
        let mut bv4 = BitVec::from_elem(1, true);
        let mut bv5 = BitVec::from_bytes(&[0b01110100, 0b10010010]);

        insert(&mut tree, &mut bv1, &mut nodes);
        insert(&mut tree, &mut bv2, &mut nodes);
        insert(&mut tree, &mut bv3, &mut nodes);
        insert(&mut tree, &mut bv4, &mut nodes);
        insert(&mut tree, &mut bv5, &mut nodes);

        assert_eq!(find(0, &nodes), bv1);
        assert_eq!(find(1, &nodes), bv2);
        assert_eq!(find(0, &nodes), bv3);
        assert_eq!(find(2, &nodes), bv4);
        assert_eq!(find(3, &nodes), bv5);

    }

    #[test]
    fn test_union() {
        let mut tree = Tree::new();
        let mut nodes = Table::new();
        let mut bv1 = BitVec::from_elem(1, false);
        let mut bv2 = BitVec::from_elem(2, true);
        let mut bv3 = BitVec::from_elem(3, false);
        let mut bv4 = BitVec::from_elem(1, true);
        let mut bv5 = BitVec::from_bytes(&[0b01110100, 0b10010010]);

        insert(&mut tree, &mut bv1, &mut nodes);
        insert(&mut tree, &mut bv2, &mut nodes);
        insert(&mut tree, &mut bv3, &mut nodes);
        insert(&mut tree, &mut bv4, &mut nodes);
        insert(&mut tree, &mut bv5, &mut nodes);

        assert_eq!(union(0, 1, &mut nodes, &mut tree), Some(1));
        assert_eq!(union(1, 3, &mut nodes, &mut tree), Some(4));
        assert_eq!(union(0, 4, &mut nodes, &mut tree), Some(4));

    }

}

#[no_mangle]
pub extern fn tree_new() -> *mut Tree {
    Box::into_raw(Box::new(Tree::new()))
}

#[no_mangle]
pub extern fn table_new() -> *mut Table {
    Box::into_raw(Box::new(Table::new()))
}

#[no_mangle]
pub extern fn insert_c(tree_ptr: *mut Tree, vector_ptr: *mut BitVec, table_ptr: *mut Table) -> uint32_t {
    let tree = unsafe {
        assert!(!tree_ptr.is_null());
        &mut *tree_ptr
    };

    let table = unsafe {
        assert!(!table_ptr.is_null());
        &mut *table_ptr
    };

    let vector = unsafe {
        assert!(!vector_ptr.is_null());
        &mut *vector_ptr
    };

    insert(tree, vector, table).unwrap() as uint32_t
}

#[no_mangle]
pub extern fn union_c(label1_c: uint32_t, label2_c: uint32_t, table_ptr: *mut Table, tree_ptr: *mut Tree) -> uint32_t {
    let tree = unsafe {
        assert!(!tree_ptr.is_null());
        &mut *tree_ptr
    };

    let table = unsafe {
        assert!(!table_ptr.is_null());
        &mut *table_ptr
    };

    let label1 = label1_c as usize;
    let label2 = label2_c as usize;

    union(label1, label2, table, tree).unwrap() as uint32_t
}

#[no_mangle]
pub extern fn tree_free(tree_ptr: *mut Tree) {
    if tree_ptr.is_null() { return; }
    unsafe{
        Box::from_raw(tree_ptr);
    }
}

#[no_mangle]
pub extern fn table_free(table_ptr: *mut Table) {
    if table_ptr.is_null() { return; }
    unsafe{
        Box::from_raw(table_ptr);
    }
}

#[no_mangle]
pub extern fn bitvec_new() -> *mut BitVec {
    Box::into_raw(Box::new(BitVec::new()))
}

#[no_mangle]
pub extern fn bitvec_set(vector_ptr: *mut BitVec, length_c: uint32_t, offset_c: uint32_t) {
    let length = length_c as usize;
    let offset = offset_c as usize;

    assert!(!vector_ptr.is_null());
    let vector = unsafe {
        &mut *vector_ptr
    };

    vector.grow(offset, false);
    vector.grow(length, true);
}

#[no_mangle]
pub extern fn bitvec_free(vector_ptr: *mut BitVec) {
    if vector_ptr.is_null() { return; }
    unsafe {
        Box::from_raw(vector_ptr);
    }
}

#[no_mangle]
pub extern fn bitvec_print(table_ptr: *mut Table, label_number_c: uint32_t, total_bits_c: uint32_t, bb_number_c: uint32_t) {
    let label_number = label_number_c as usize;
    let total_bits = total_bits_c as usize;
    let bb_number = bb_number_c as usize;

    assert!(!table_ptr.is_null());
    let table = unsafe {
        &mut *table_ptr
    };

    let mut result = find(label_number, table);
    let len = result.len();
    result.grow(total_bits - len, false);

    println!("Basic Block #{}'s Taints: {:?}", bb_number, result);
}
