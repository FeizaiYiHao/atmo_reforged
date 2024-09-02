use vstd::prelude::*;
verus! {
use crate::slinkedlist::define::*;
use crate::slinkedlist::spec::*;
use crate::define::SLLIndex;
use vstd::seq_lib::lemma_seq_contains_after_push;

    impl<T: Copy, const N: usize> StaticLinkedList<T,N> {
    }
}