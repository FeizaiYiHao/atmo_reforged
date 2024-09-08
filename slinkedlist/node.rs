use vstd::prelude::*;
verus! {
use crate::define::SLLIndex;

#[derive(Debug)]
pub struct Node<T>{
    pub value:Option<T>,
    pub next:SLLIndex,
    pub prev:SLLIndex,
}

}