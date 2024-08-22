use vstd::prelude::*;
verus! {

pub type Index = i32;
pub const NULL_POINTER: usize = 0;

#[derive(Debug)]
pub struct Node{
    pub value:usize,
    pub next:Index,
    pub prev:Index,
}

}