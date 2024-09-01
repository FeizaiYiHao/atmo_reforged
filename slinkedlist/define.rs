use vstd::prelude::*;
verus! {
use crate::define::SLLIndex;

pub const NULL_POINTER: usize = 0;

#[derive(Debug)]
pub struct Node{
    pub value:usize,
    pub next:SLLIndex,
    pub prev:SLLIndex,
}

}