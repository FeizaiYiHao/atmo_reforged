use vstd::prelude::*;
verus! {
    use crate::define::*;
    use crate::slinkedlist::spec_impl_u::*;
    use crate::array_set::*;

    pub struct Container{
        pub owned_procs: StaticLinkedList<ProcPtr,CONTAINER_PROC_LIST_LEN>,
        pub parent: Option<ContainerPtr>,
        pub parent_rev_ptr: Option<SLLIndex>,
        
        pub children: StaticLinkedList<ContainerPtr,CONTAINER_CHILD_LIST_LEN>,

        pub owned_endpoints: StaticLinkedList<EndpointPtr,CONTAINER_ENDPOINT_LIST_LEN>,

        pub mem_quota: usize,
        // pub mem_quota_2m: usize,        
        // pub mem_quota_1g: usize,

        pub mem_used: usize,
        // pub mem_used_2m: usize,
        // pub mem_used_1g: usize,

        pub owned_cpus: ArraySet<NUM_CPUS>,
        pub scheduler: StaticLinkedList<ThreadPtr,CONTAINER_SCHEDULER_LEN>,
    }
}
