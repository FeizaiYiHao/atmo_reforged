use vstd::prelude::*;
verus! {
    use crate::define::*;
    use vstd::simple_pptr::PointsTo;
    use crate::process_manager::endpoint::*;
    use crate::process_manager::process::*;
    use crate::process_manager::container::*;
    use crate::process_manager::thread::*;

pub struct ProcessManager{
    pub root_container: ContainerPtr,

    pub container_perms: Tracked<Map<ContainerPtr, PointsTo<Container>>>,
    pub process_perms: Tracked<Map<ProcPtr, PointsTo<Process>>>,
    pub thread_perms: Tracked<Map<ThreadPtr, PointsTo<Thread>>>,
    pub endpoint_perms: Tracked<Map<EndpointPtr, PointsTo<Endpoint>>>,
}

impl ProcessManager{

    pub closed spec fn container_perms_wf(&self) -> bool{
        &&&
        forall|c_ptr:ContainerPtr| #[trigger self.container_perms@[c_ptr].is_init()]
            self.container_perms@.dom().contains(c_ptr) ==> self.container_perms@[c_ptr].is_init()
        &&&
        forall|c_ptr:ContainerPtr| 
        // #[trigger self.container_perms@[c_ptr].value().children]
            self.container_perms@.dom().contains(c_ptr)
            ==> 
            self.container_perms@[c_ptr].value().children_list.wf()
            &&
            self.container_perms@[c_ptr].value().children_list.unique()
            &&
            self.container_perms@[c_ptr].value().owned_cpus.wf()
            &&
            self.container_perms@[c_ptr].value().scheduler.wf() 
            &&
            self.container_perms@[c_ptr].value().scheduler.unique() 
            &&
            self.container_perms@[c_ptr].value().proc_list.wf()
            &&
            self.container_perms@[c_ptr].value().proc_list.unique()
    }

    pub closed spec fn container_root_wf(&self) -> bool{
        &&&
        self.container_perms@.dom().contains(self.root_container)
        &&&
        forall|c_ptr:ContainerPtr| 
        // #[trigger self.container_perms@[c_ptr].value().children]
            self.container_perms@.dom().contains(c_ptr) 
            ==> 
            c_ptr != self.root_container <==> self.container_perms@[c_ptr].value().parent.is_Some()   
    }

    pub closed spec fn container_tree_wf(&self) -> bool{
        &&&
        forall|c_ptr:ContainerPtr| #[trigger self.container_perms@[c_ptr].value().children]
            self.container_perms@.dom().contains(c_ptr) ==> self.container_perms@[c_ptr].value().children_list@.to_set().subset_of(self.container_perms@.dom())
        &&&
        forall|c_ptr:ContainerPtr| #[trigger self.container_perms@[c_ptr].value().children]
            self.container_perms@.dom().contains(c_ptr) ==> self.container_perms@[c_ptr].value().children_list@.to_set().contains(c_ptr) == false
        &&&
        forall|c_ptr:ContainerPtr, child_c_ptr:ContainerPtr| 
        // #[trigger self.container_perms@[c_ptr].value().children]
            self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().children_list@.to_set().contains(child_c_ptr)
            ==> self.container_perms@.dom().contains(child_c_ptr)
                &&
                self.container_perms@[child_c_ptr].value().parent.unwrap() == c_ptr
        &&&
        forall|c_ptr:ContainerPtr| 
        // #[trigger self.container_perms@[c_ptr].value().children]
            self.container_perms@.dom().contains(c_ptr) && c_ptr != self.root_container 
            ==>
            self.container_perms@.dom().contains(self.container_perms@[c_ptr].value().parent.unwrap())
    }

    pub closed spec fn containers_linkedlist_wf(&self) -> bool{  
        &&&
        forall|c_ptr:ContainerPtr| 
        // #[trigger self.container_perms@[c_ptr].value().children]
            self.container_perms@.dom().contains(c_ptr) && c_ptr != self.root_container 
            ==> self.container_perms@[c_ptr].value().parent_rev_ptr.is_Some()
                && self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children_list@.to_set().contains(c_ptr)
                && self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children_list.node_ref_valid(self.container_perms@[c_ptr].value().parent_rev_ptr.unwrap())
                && self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children_list.node_ref_resolve(self.container_perms@[c_ptr].value().parent_rev_ptr.unwrap()) == c_ptr
        &&&
        forall|c_ptr_i:ContainerPtr, c_ptr_j:ContainerPtr| 
            self.container_perms@.dom().contains(c_ptr_i) && self.container_perms@.dom().contains(c_ptr_j) && c_ptr_i != c_ptr_j 
            &&
            self.container_perms@[c_ptr_i].value().parent.is_Some() && self.container_perms@[c_ptr_j].value().parent.is_Some()
            &&
            self.container_perms@[c_ptr_i].value().parent.unwrap() == self.container_perms@[c_ptr_j].value().parent.unwrap()
            ==>
            self.container_perms@[c_ptr_i].value().parent_rev_ptr != self.container_perms@[c_ptr_j].value().parent_rev_ptr
    }

    pub closed spec fn processes_container_wf(&self) -> bool{
        &&&
        forall|c_ptr:ContainerPtr| 
        // #[trigger self.container_perms@[c_ptr].value().children]
            self.container_perms@.dom().contains(c_ptr)
            ==>
            self.container_perms@[c_ptr].value().proc_list@.to_set().subset_of(self.process_perms@.dom())
        &&&
        forall|p_ptr:ProcPtr| 
            self.process_perms@.dom().contains(p_ptr)
            ==>
            self.container_perms@.dom().contains(self.process_perms@[p_ptr].value().owning_container)
            &&
            self.container_perms@[self.process_perms@[p_ptr].value().owning_container].value().proc_list@.to_set().contains(p_ptr)
            &&
            self.container_perms@[self.process_perms@[p_ptr].value().owning_container].value().proc_list.node_ref_valid(self.process_perms@[p_ptr].value().rev_ptr)
            &&
            self.container_perms@[self.process_perms@[p_ptr].value().owning_container].value().proc_list.node_ref_resolve(self.process_perms@[p_ptr].value().rev_ptr) == p_ptr
        &&&    
        forall|c_ptr:ContainerPtr, p_ptr_i:ProcPtr, p_ptr_j:ProcPtr| 
        // #[trigger self.container_perms@[c_ptr].value().children]
            self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().proc_list@.contains(p_ptr_i) && self.container_perms@[c_ptr].value().proc_list@.contains(p_ptr_j)
            &&
            p_ptr_i != p_ptr_j
            ==>
            self.process_perms@[p_ptr_i].value().rev_ptr != self.process_perms@[p_ptr_j].value().rev_ptr
        }
    
    pub closed spec fn processes_wf(&self) -> bool{
        &&&
        forall|p_ptr:ProcPtr| 
            self.process_perms@.dom().contains(p_ptr)
            ==>
            self.process_perms@[p_ptr].is_init()
    }

    pub closed spec fn threads_process_wf(&self) -> bool{
        &&&
        forall|p_ptr:ProcPtr| 
            self.process_perms@.dom().contains(p_ptr)
            ==>
            self.process_perms@[p_ptr].value().owned_threads.wf()
            &&
            self.process_perms@[p_ptr].value().owned_threads.unique()
        &&&
        forall|t_ptr:ThreadPtr| 
            self.thread_perms@.dom().contains(t_ptr)
            ==>
            self.thread_perms@[t_ptr].is_init()
            &&
            self.container_perms@.dom().contains(self.thread_perms@[t_ptr].value().owning_container)
            &&
            self.process_perms@.dom().contains(self.thread_perms@[t_ptr].value().owning_proc)
            &&
            self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owned_threads@.contains(t_ptr)
            &&
            self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owned_threads.node_ref_valid(self.thread_perms@[t_ptr].value().proc_rev_ptr)
            &&
            self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owned_threads.node_ref_resolve(self.thread_perms@[t_ptr].value().proc_rev_ptr) == t_ptr
            &&
            self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owning_container == self.thread_perms@[t_ptr].value().owning_container
        &&&    
        forall|t_ptr_i:ThreadPtr, t_ptr_j:ThreadPtr| 
        // #[trigger self.container_perms@[c_ptr].value().children]
            self.thread_perms@.dom().contains(t_ptr_i) && self.thread_perms@.dom().contains(t_ptr_j) && 
            self.thread_perms@[t_ptr_i].value().owning_proc == self.thread_perms@[t_ptr_j].value().owning_proc
            &&
            t_ptr_i != t_ptr_j
            ==>
            self.thread_perms@[t_ptr_i].value().proc_rev_ptr != self.thread_perms@[t_ptr_j].value().proc_rev_ptr
    }
    pub closed spec fn threads_wf(&self) -> bool{
        &&&
        forall|t_ptr:ThreadPtr|
        self.thread_perms@.dom().contains(t_ptr) 
        ==>
        self.thread_perms@[t_ptr].is_init()
        &&
        self.thread_perms@[t_ptr].value().endpoint_descriptors.wf()
    }

    pub closed spec fn endpoint_perms_wf(&self) -> bool {
        &&&
        forall|e_ptr:EndpointPtr| 
            self.endpoint_perms@.dom().contains(e_ptr) 
            ==> 
            self.endpoint_perms@[e_ptr].is_init()
            &&
            self.endpoint_perms@[e_ptr].value().queue.wf()
            &&
            self.endpoint_perms@[e_ptr].value().queue.unique()
            &&
            self.endpoint_perms@[e_ptr].value().rf_counter == self.endpoint_perms@[e_ptr].value().owning_threads@.len()
    }

    pub closed spec fn threads_endpoint_descriptors_wf(&self) -> bool {
        &&&
        forall|t_ptr:ThreadPtr, i: usize|
            self.thread_perms@.dom().contains(t_ptr) && 0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS
            &&
            self.thread_perms@[t_ptr].value().endpoint_descriptors@[i as int].is_Some()
            ==>
            self.endpoint_perms@.dom().contains(self.thread_perms@[t_ptr].value().endpoint_descriptors@[i as int].unwrap())
            &&
            self.endpoint_perms@[self.thread_perms@[t_ptr].value().endpoint_descriptors@[i as int].unwrap()].value().owning_threads@.contains(t_ptr)
    }
    pub closed spec fn endpoints_queue_wf(&self) -> bool {
        &&&
        forall|t_ptr:ThreadPtr|
            self.thread_perms@.dom().contains(t_ptr)
            &&
            self.thread_perms@[t_ptr].value().state == ThreadState::BLOCKED
            ==>
            self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.is_Some()
            &&
            self.thread_perms@[t_ptr].value().endpoint_rev_ptr.is_Some()
            &&
            self.endpoint_perms@.dom().contains(self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap())
            &&
            self.endpoint_perms@[self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap()].value().queue@.contains(t_ptr)
            &&
            self.endpoint_perms@[self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap()].value().queue.node_ref_valid(self.thread_perms@[t_ptr].value().endpoint_rev_ptr.unwrap())
            &&
            self.endpoint_perms@[self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap()].value().queue.node_ref_resolve(self.thread_perms@[t_ptr].value().endpoint_rev_ptr.unwrap()) == t_ptr
        &&&
        forall|t_ptr_i:ThreadPtr, t_ptr_j:ThreadPtr|
            self.thread_perms@.dom().contains(t_ptr_i) && self.thread_perms@.dom().contains(t_ptr_j) && t_ptr_i != t_ptr_j
            &&
            self.thread_perms@[t_ptr_i].value().state == ThreadState::BLOCKED && self.thread_perms@[t_ptr_j].value().state == ThreadState::BLOCKED
            &&
            self.thread_perms@[t_ptr_i].value().blocking_endpoint_ptr.unwrap() == self.thread_perms@[t_ptr_j].value().blocking_endpoint_ptr.unwrap()
            ==>
            self.thread_perms@[t_ptr_i].value().endpoint_rev_ptr.unwrap() != self.thread_perms@[t_ptr_j].value().endpoint_rev_ptr.unwrap()
    }

    pub closed spec fn schedulers_wf(&self) -> bool{
        &&&
        forall|t_ptr:ThreadPtr|
            self.thread_perms@.dom().contains(t_ptr)
            &&
            self.thread_perms@[t_ptr].value().state == ThreadState::SCHEDULED
            ==>
            self.container_perms@[self.thread_perms@[t_ptr].value().owning_container].value().scheduler@.contains(t_ptr)
            && 
            self.container_perms@[self.thread_perms@[t_ptr].value().owning_container].value().scheduler.node_ref_valid(self.thread_perms@[t_ptr].value().scheduler_rev_ptr.unwrap())
            && 
            self.container_perms@[self.thread_perms@[t_ptr].value().owning_container].value().scheduler.node_ref_resolve(self.thread_perms@[t_ptr].value().scheduler_rev_ptr.unwrap()) == t_ptr
        &&&
        forall|t_ptr_i:ThreadPtr, t_ptr_j:ThreadPtr|
            self.thread_perms@.dom().contains(t_ptr_i) && self.thread_perms@.dom().contains(t_ptr_j) && t_ptr_i != t_ptr_j
            &&
            self.thread_perms@[t_ptr_i].value().state == ThreadState::SCHEDULED && self.thread_perms@[t_ptr_j].value().state == ThreadState::SCHEDULED
            &&
            self.thread_perms@[t_ptr_i].value().owning_container == self.thread_perms@[t_ptr_j].value().owning_container
            ==>
            self.thread_perms@[t_ptr_i].value().scheduler_rev_ptr.unwrap() != self.thread_perms@[t_ptr_j].value().scheduler_rev_ptr.unwrap()
    }
}


}
