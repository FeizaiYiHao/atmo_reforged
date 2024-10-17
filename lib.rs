use vstd::prelude::verus;

pub mod define;
pub mod trap;
pub mod array;
pub mod array_set;
pub mod array_vec;
pub mod slinkedlist;
// pub mod pagetable;
// pub mod allocator;
pub mod process_manager;
// pub mod pcid_alloc;

pub mod lemma;
pub mod util;

verus! {

global size_of usize == 8;

}

fn main(){

}