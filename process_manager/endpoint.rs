use vstd::prelude::*;
verus! {
    use crate::define::*;
    use crate::slinkedlist::spec_impl_u::*;

    pub struct Endpoint{
        pub queue: StaticLinkedList<ThreadPtr, MAX_NUM_THREADS_PER_ENDPOINT>,
        pub queue_state: EndpointState,
    
        pub rf_counter: usize,
        pub owning_threads: Ghost<Set<ThreadPtr>>,

        pub owning_container: ContainerPtr,
        pub container_rev_ptr: SLLIndex,
    }

    impl Endpoint{
        pub open spec fn rf_counter_is_full(&self) -> bool{
            self.rf_counter == usize::MAX
        }

        pub open spec fn get_owning_threads(&self) -> Set<ThreadPtr>{
            self.owning_threads@
        }
    }
}