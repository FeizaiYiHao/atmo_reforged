use vstd::prelude::*;
verus! {
    use crate::define::*;
    use crate::slinkedlist::spec_impl_u::*;

    pub struct Process{
        pub rev_ptr: SLLIndex,
        pub pcid: Pcid,
        pub ioid: Option<IOid>,
        pub owned_threads: StaticLinkedList<ThreadPtr, MAX_NUM_THREADS_PER_PROC>,
    }
}