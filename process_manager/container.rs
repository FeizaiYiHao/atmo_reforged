use vstd::prelude::*;
verus! {
    use crate::define::*;
    use crate::slinkedlist::spec_impl_u::*;
    use crate::array::*;

    pub struct Container{
        pub proc_list: StaticLinkedList<ProcPtr,CONTAINER_PROC_LIST_LEN>,
        pub parent: Option<ContainerPtr>,
        pub parent_rev_ptr: Option<SLLIndex>,
        
        pub children_list: StaticLinkedList<ContainerPtr,CONTAINER_CHILD_LIST_LEN>,

        pub mem_quota_4k: usize,
        // pub mem_quota_2m: usize,        
        // pub mem_quota_1g: usize,

        pub mem_used_4k: usize,
        // pub mem_used_2m: usize,
        // pub mem_used_1g: usize,

        pub owned_pages_4k: Ghost<Set<PagePtr>>,
        
        pub owned_cpus: Array<bool,NUM_CPUS>,
        pub scheduler: StaticLinkedList<ThreadPtr,CONTAINER_CHILD_LIST_LEN>,
    }
}
