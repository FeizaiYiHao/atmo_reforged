use vstd::prelude::*;
verus! {
    use crate::define::*;
    use vstd::simple_pptr::PointsTo;
    use crate::trap::*;
    use crate::array::Array;
    use crate::process_manager::endpoint::*;
    use crate::process_manager::process::*;
    use crate::process_manager::container::*;
    use crate::process_manager::thread::*;
    use crate::process_manager::cpu::*;
    use vstd::simple_pptr::PPtr;
    use crate::process_manager::thread_util_t::*;
    use crate::process_manager::proc_util_t::*;
    use crate::process_manager::container_util_t::*;
    use crate::lemma::lemma_u::*;

pub struct ProcessManager{
    pub root_container: ContainerPtr,

    pub container_perms: Tracked<Map<ContainerPtr, PointsTo<Container>>>,
    pub process_perms: Tracked<Map<ProcPtr, PointsTo<Process>>>,
    pub thread_perms: Tracked<Map<ThreadPtr, PointsTo<Thread>>>,
    pub endpoint_perms: Tracked<Map<EndpointPtr, PointsTo<Endpoint>>>,

    pub cpu_list: Array<Cpu, NUM_CPUS>,
}

//utils
impl ProcessManager{
    pub open spec fn page_closure(&self) -> Set<PagePtr>
    {
        self.container_perms@.dom() + self.process_perms@.dom() + self.thread_perms@.dom() + self.endpoint_perms@.dom()
    }

    pub open spec fn spec_get_proc(&self, proc_ptr:ProcPtr) -> &Process
        recommends
            self.wf(),
            self.process_perms@.dom().contains(proc_ptr),
    {
        &self.process_perms@[proc_ptr].value()
    }

    #[verifier(when_used_as_spec(spec_get_proc))]
    pub fn get_proc(&self, proc_ptr:ProcPtr) ->(ret:&Process)
        requires
            self.wf(),
            self.process_perms@.dom().contains(proc_ptr),
        ensures
            ret =~= self.spec_get_proc(proc_ptr),
    {
        let tracked proc_perm = self.process_perms.borrow().tracked_borrow(proc_ptr);
        let proc : &Process = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(proc_perm));
        proc
    }

    pub open spec fn spec_get_proc_by_thread_ptr(&self, thread_ptr:ThreadPtr) -> &Process
        recommends
            self.wf(),
            self.thread_perms@.dom().contains(thread_ptr),
    {
        &self.process_perms@[self.get_thread(thread_ptr).owning_proc].value()
    }

    #[verifier(when_used_as_spec(spec_get_proc_by_thread_ptr))]
    pub fn get_proc_by_thread_ptr(&self, thread_ptr:ThreadPtr) ->(ret:&Process)
        requires
            self.wf(),
            self.thread_perms@.dom().contains(thread_ptr),
        ensures
            ret =~= self.spec_get_proc_by_thread_ptr(thread_ptr),
    {
        let proc_ptr = self.get_thread(thread_ptr).owning_proc;
        let tracked proc_perm = self.process_perms.borrow().tracked_borrow(proc_ptr);
        let proc : &Process = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(proc_perm));
        proc
    }

    pub open spec fn spec_get_thread(&self, thread_ptr:ThreadPtr) -> &Thread
        recommends
            self.wf(),
            self.thread_perms@.dom().contains(thread_ptr),
    {
        &self.thread_perms@[thread_ptr].value()
    }

    #[verifier(when_used_as_spec(spec_get_thread))]
    pub fn get_thread(&self, thread_ptr:ThreadPtr) -> (ret:&Thread)
        requires
            self.wf(),
            self.thread_perms@.dom().contains(thread_ptr),
        ensures
            ret == self.get_thread(thread_ptr)
    {
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
        thread
    }

    pub open spec fn spec_get_container(&self, container_ptr:ContainerPtr) -> &Container
        recommends
            self.wf(),
            self.container_perms@.dom().contains(container_ptr),
    {
        &self.container_perms@[container_ptr].value()
    }

    #[verifier(when_used_as_spec(spec_get_container))]
    pub fn get_container(&self, container_ptr:ContainerPtr) -> (ret:&Container)
        requires
            self.wf(),
            self.container_perms@.dom().contains(container_ptr),
        ensures
            self.get_container(container_ptr) == ret,
    {
        let tracked container_perm = self.container_perms.borrow().tracked_borrow(container_ptr);
        let container : &Container = PPtr::<Container>::from_usize(container_ptr).borrow(Tracked(container_perm));
        container
    }

    pub open spec fn spec_get_container_by_proc_ptr(&self, proc_ptr:ProcPtr) -> &Container
        recommends
            self.wf(),
            self.process_perms@.dom().contains(proc_ptr),
    {
        &self.container_perms@[self.get_proc(proc_ptr).owning_container].value()
    }

    #[verifier(when_used_as_spec(spec_get_container_by_proc_ptr))]
    pub fn get_container_by_proc_ptr(&self, proc_ptr:ProcPtr) -> (ret:&Container)
        requires
            self.wf(),
            self.process_perms@.dom().contains(proc_ptr),
        ensures
            self.get_container_by_proc_ptr(proc_ptr) == ret,
    {
        let container_ptr = self.get_proc(proc_ptr).owning_container;
        let tracked container_perm = self.container_perms.borrow().tracked_borrow(container_ptr);
        let container : &Container = PPtr::<Container>::from_usize(container_ptr).borrow(Tracked(container_perm));
        container
    }

    pub open spec fn spec_get_container_by_thread_ptr(&self, thread_ptr:ThreadPtr) -> &Container
        recommends
            self.wf(),
            self.thread_perms@.dom().contains(thread_ptr),
    {
        &self.container_perms@[self.get_proc_by_thread_ptr(thread_ptr).owning_container].value()
    }

    #[verifier(when_used_as_spec(spec_get_container_by_thread_ptr))]
    pub fn get_container_by_thread_ptr(&self, thread_ptr:ThreadPtr) -> (ret:&Container)
        requires
            self.wf(),
            self.thread_perms@.dom().contains(thread_ptr),
        ensures
            self.get_container_by_thread_ptr(thread_ptr) == ret,
    {
        let container_ptr = self.get_proc_by_thread_ptr(thread_ptr).owning_container;
        let tracked container_perm = self.container_perms.borrow().tracked_borrow(container_ptr);
        let container : &Container = PPtr::<Container>::from_usize(container_ptr).borrow(Tracked(container_perm));
        container
    }

    pub open spec fn spec_get_endpoint(&self, endpoint_ptr:EndpointPtr) -> &Endpoint
        recommends
            self.wf(),
            self.endpoint_perms@.dom().contains(endpoint_ptr),
    {
        &self.endpoint_perms@[endpoint_ptr].value()
    }

    #[verifier(when_used_as_spec(spec_get_endpoint))]
    pub fn get_endpoint(&self, endpoint_ptr:EndpointPtr) -> (ret:&Endpoint)
        requires
            self.wf(),
            self.endpoint_perms@.dom().contains(endpoint_ptr),
        ensures
            ret == self.get_endpoint(endpoint_ptr)
    {
        let tracked endpoint_perm = self.endpoint_perms.borrow().tracked_borrow(endpoint_ptr);
        let endpoint : &Endpoint = PPtr::<Endpoint>::from_usize(endpoint_ptr).borrow(Tracked(endpoint_perm));
        endpoint
    }
}

//specs
impl ProcessManager{
    pub closed spec fn cpus_wf(&self) -> bool{
        &&&
        self.cpu_list.wf()
    }
    pub closed spec fn container_cpu_wf(&self) -> bool{
        &&&
        forall|c_ptr:ContainerPtr| 
        #![trigger self.container_perms@.dom().contains(c_ptr)]
            self.container_perms@.dom().contains(c_ptr)
            ==>
            self.container_perms@[c_ptr].value().owned_cpus.wf()
        &&&
        forall|c_ptr_i:ContainerPtr, c_ptr_j:ContainerPtr| 
        #![trigger self.container_perms@[c_ptr_i].value().owned_cpus, self.container_perms@[c_ptr_j].value().owned_cpus]
            self.container_perms@.dom().contains(c_ptr_i) && self.container_perms@.dom().contains(c_ptr_j)
            &&
            c_ptr_i != c_ptr_j
            ==>
            self.container_perms@[c_ptr_i].value().owned_cpus@.disjoint(self.container_perms@[c_ptr_j].value().owned_cpus@)
        &&&
        forall|cpu_i:CpuId|
        #![trigger self.cpu_list@[cpu_i as int].owning_container]
        0 <= cpu_i < NUM_CPUS 
        ==> 
        self.container_perms@.dom().contains(self.cpu_list@[cpu_i as int].owning_container)
        &&
        self.container_perms@[self.cpu_list@[cpu_i as int].owning_container].value().owned_cpus@.contains(cpu_i)
    }

    pub closed spec fn threads_cpu_wf(&self) -> bool {
        &&&
        forall|t_ptr:ThreadPtr|
            #![trigger self.thread_perms@[t_ptr].value().state]
            #![trigger self.thread_perms@[t_ptr].value().running_cpu]
            self.thread_perms@.dom().contains(t_ptr) 
            ==>
            (self.thread_perms@[t_ptr].value().running_cpu.is_Some() 
            <==> self.thread_perms@[t_ptr].value().state == ThreadState::RUNNING)
        &&&
        forall|t_ptr:ThreadPtr|
            #![trigger self.thread_perms@[t_ptr].value().running_cpu]
            self.thread_perms@.dom().contains(t_ptr) && self.thread_perms@[t_ptr].value().running_cpu.is_Some() 
            ==>
            0 <= self.thread_perms@[t_ptr].value().running_cpu.unwrap() < NUM_CPUS
            &&
            self.cpu_list@[self.thread_perms@[t_ptr].value().running_cpu.unwrap() as int].current_thread.is_Some()
            &&
            self.cpu_list@[self.thread_perms@[t_ptr].value().running_cpu.unwrap() as int].current_thread.unwrap() == t_ptr
            &&
            self.cpu_list@[self.thread_perms@[t_ptr].value().running_cpu.unwrap() as int].owning_container ==
                self.thread_perms@[t_ptr].value().owning_container
        &&&        
        forall|cpu_i:CpuId|
            #![trigger self.cpu_list@[cpu_i as int].current_thread]
            0 <= cpu_i < NUM_CPUS && self.cpu_list@[cpu_i as int].current_thread.is_Some()
            ==> 
            self.thread_perms@.dom().contains(self.cpu_list@[cpu_i as int].current_thread.unwrap())
            &&
            self.thread_perms@[self.cpu_list@[cpu_i as int].current_thread.unwrap()].value().running_cpu.is_Some()
            &&
            self.thread_perms@[self.cpu_list@[cpu_i as int].current_thread.unwrap()].value().running_cpu.unwrap() == cpu_i
            &&
            self.cpu_list@[cpu_i as int].owning_container ==
                self.thread_perms@[self.cpu_list@[cpu_i as int].current_thread.unwrap()].value().owning_container
    }

    pub closed spec fn memory_disjoint(&self) -> bool{
        &&&
        self.container_perms@.dom().disjoint(self.process_perms@.dom())
        &&&
        self.container_perms@.dom().disjoint(self.thread_perms@.dom())
        &&&
        self.container_perms@.dom().disjoint(self.endpoint_perms@.dom())
        &&&
        self.process_perms@.dom().disjoint(self.thread_perms@.dom())
        &&&
        self.process_perms@.dom().disjoint(self.endpoint_perms@.dom())
        &&&
        self.thread_perms@.dom().disjoint(self.endpoint_perms@.dom())
    }

    pub closed spec fn container_perms_wf(&self) -> bool{
        &&&
        forall|c_ptr:ContainerPtr| 
        #![trigger self.container_perms@.dom().contains(c_ptr)]
            self.container_perms@.dom().contains(c_ptr)
            ==> 
            self.container_perms@[c_ptr].is_init()
            &&            
            self.container_perms@[c_ptr].addr() == c_ptr
            &&
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
        #![trigger self.container_perms@.dom().contains(c_ptr)]
            self.container_perms@.dom().contains(c_ptr) && c_ptr != self.root_container 
            ==> 
            self.container_perms@[c_ptr].value().parent.is_Some()   
        &&&
        forall|c_ptr:ContainerPtr| 
        #![trigger self.container_perms@.dom().contains(c_ptr)]
            self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().parent.is_Some()   
            ==> 
            c_ptr != self.root_container 
    }

    pub closed spec fn container_tree_wf(&self) -> bool{
        &&&
        forall|c_ptr:ContainerPtr| 
            #![trigger self.container_perms@.dom().contains(c_ptr)]
            self.container_perms@.dom().contains(c_ptr) 
            ==> 
            self.container_perms@[c_ptr].value().children_list@.to_set().subset_of(self.container_perms@.dom())
            &&
            self.container_perms@.dom().contains(c_ptr) ==> self.container_perms@[c_ptr].value().children_list@.contains(c_ptr) == false
        &&&
        forall|c_ptr:ContainerPtr, child_c_ptr:ContainerPtr| 
            // #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().children_list@.contains(child_c_ptr)]
            self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().children_list@.contains(child_c_ptr)
            ==> self.container_perms@.dom().contains(child_c_ptr)
                &&
                self.container_perms@[child_c_ptr].value().parent.unwrap() == c_ptr
        &&&
        forall|c_ptr:ContainerPtr| 
            #![trigger self.container_perms@.dom().contains(c_ptr)]
            self.container_perms@.dom().contains(c_ptr) && c_ptr != self.root_container 
            ==>
            self.container_perms@.dom().contains(self.container_perms@[c_ptr].value().parent.unwrap())
    }

    pub closed spec fn containers_linkedlist_wf(&self) -> bool{  
        &&&
        forall|c_ptr:ContainerPtr| 
        #![trigger self.container_perms@[c_ptr].value().parent]
            self.container_perms@.dom().contains(c_ptr) && c_ptr != self.root_container 
            ==> self.container_perms@[c_ptr].value().parent_rev_ptr.is_Some()
                && self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children_list@.to_set().contains(c_ptr)
                && self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children_list.node_ref_valid(self.container_perms@[c_ptr].value().parent_rev_ptr.unwrap())
                && self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children_list.node_ref_resolve(self.container_perms@[c_ptr].value().parent_rev_ptr.unwrap()) == c_ptr
    }

    pub closed spec fn processes_container_wf(&self) -> bool{
        // &&&
        // forall|c_ptr:ContainerPtr| 
        //     #![trigger self.container_perms@[c_ptr].value().proc_list]
        //     self.container_perms@.dom().contains(c_ptr)
        //     ==>
        //     self.container_perms@[c_ptr].value().proc_list@.to_set().subset_of(self.process_perms@.dom())
        &&&
        forall|c_ptr:ContainerPtr, child_p_ptr:ProcPtr| 
            self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().proc_list@.contains(child_p_ptr)
            ==> self.process_perms@.dom().contains(child_p_ptr)
                &&
                self.process_perms@[child_p_ptr].value().owning_container == c_ptr
        &&&
        forall|p_ptr:ProcPtr| 
            #![trigger self.process_perms@[p_ptr].value().owning_container]
            self.process_perms@.dom().contains(p_ptr)
            ==>
            self.container_perms@.dom().contains(self.process_perms@[p_ptr].value().owning_container)
            &&
            self.container_perms@[self.process_perms@[p_ptr].value().owning_container].value().proc_list@.to_set().contains(p_ptr)
            &&
            self.container_perms@[self.process_perms@[p_ptr].value().owning_container].value().proc_list.node_ref_valid(self.process_perms@[p_ptr].value().rev_ptr)
            &&
            self.container_perms@[self.process_perms@[p_ptr].value().owning_container].value().proc_list.node_ref_resolve(self.process_perms@[p_ptr].value().rev_ptr) == p_ptr
        }
    
    pub closed spec fn processes_wf(&self) -> bool{
        &&&
        forall|p_ptr:ProcPtr| 
            #![trigger self.process_perms@.dom().contains(p_ptr)]
            self.process_perms@.dom().contains(p_ptr)
            ==>
            self.process_perms@[p_ptr].is_init()
            &&            
            self.process_perms@[p_ptr].addr() == p_ptr
    }

    pub closed spec fn threads_process_wf(&self) -> bool{
        &&&
        forall|p_ptr:ProcPtr| 
            #![trigger self.process_perms@.dom().contains(p_ptr)]
            self.process_perms@.dom().contains(p_ptr)
            ==>
            self.process_perms@[p_ptr].value().owned_threads.wf()
            &&
            self.process_perms@[p_ptr].value().owned_threads.unique()
        &&&
        forall|p_ptr:ProcPtr, child_t_ptr:ThreadPtr| 
            #![trigger self.process_perms@.dom().contains(p_ptr), self.thread_perms@[child_t_ptr].value().owning_proc]
            #![trigger self.process_perms@[p_ptr].value().owned_threads@.contains(child_t_ptr)]
            self.process_perms@.dom().contains(p_ptr) && self.process_perms@[p_ptr].value().owned_threads@.contains(child_t_ptr)
            ==> self.thread_perms@.dom().contains(child_t_ptr)
                &&
                self.thread_perms@[child_t_ptr].value().owning_proc == p_ptr
        &&&
        forall|t_ptr:ThreadPtr| 
            #![trigger self.thread_perms@[t_ptr].value().owning_container]
            #![trigger self.thread_perms@[t_ptr].value().owning_proc]
            self.thread_perms@.dom().contains(t_ptr)
            ==>
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
    }
    pub closed spec fn threads_perms_wf(&self) -> bool{
        &&&
        forall|t_ptr:ThreadPtr|
        #![trigger self.thread_perms@.dom().contains(t_ptr) ]
        self.thread_perms@.dom().contains(t_ptr) 
        ==>
        self.thread_perms@[t_ptr].is_init()
        &&
        self.thread_perms@[t_ptr].addr() == t_ptr
        &&
        self.thread_perms@[t_ptr].value().endpoint_descriptors.wf()
    }

    pub closed spec fn endpoint_perms_wf(&self) -> bool {
        &&&
        forall|e_ptr:EndpointPtr| 
            #![trigger self.endpoint_perms@.dom().contains(e_ptr) ]
            self.endpoint_perms@.dom().contains(e_ptr) 
            ==> 
            self.endpoint_perms@[e_ptr].is_init()
            &&
            self.endpoint_perms@[e_ptr].addr() == e_ptr
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
            #![auto]
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
            #![trigger self.thread_perms@[t_ptr].value().state]
            #![trigger self.thread_perms@[t_ptr].value().blocking_endpoint_ptr]
            #![trigger self.thread_perms@[t_ptr].value().endpoint_rev_ptr]
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
    }

    pub closed spec fn endpoints_container_wf(&self) -> bool{
        &&&
        forall|c_ptr:ContainerPtr, child_e_ptr:EndpointPtr| 
            self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().endpoint_list@.contains(child_e_ptr)
            ==> self.endpoint_perms@.dom().contains(child_e_ptr)
                &&
                self.endpoint_perms@[child_e_ptr].value().owning_container == c_ptr
        &&&
        forall|e_ptr:EndpointPtr| 
            #![trigger self.endpoint_perms@[e_ptr].value().owning_container]
            self.endpoint_perms@.dom().contains(e_ptr)
            ==>
            self.container_perms@.dom().contains(self.endpoint_perms@[e_ptr].value().owning_container)
            &&
            self.container_perms@[self.endpoint_perms@[e_ptr].value().owning_container].value().endpoint_list@.to_set().contains(e_ptr)
            &&
            self.container_perms@[self.endpoint_perms@[e_ptr].value().owning_container].value().endpoint_list.node_ref_valid(self.endpoint_perms@[e_ptr].value().container_rev_ptr)
            &&
            self.container_perms@[self.endpoint_perms@[e_ptr].value().owning_container].value().endpoint_list.node_ref_resolve(self.endpoint_perms@[e_ptr].value().container_rev_ptr) == e_ptr
        }

    pub closed spec fn schedulers_wf(&self) -> bool{
        &&&
        forall|t_ptr:ThreadPtr|
            #![trigger self.thread_perms@[t_ptr].value().state]
            #![trigger self.thread_perms@[t_ptr].value().owning_container]
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
        forall|c_ptr:ContainerPtr, t_ptr:ThreadPtr|
            #![trigger self.container_perms@[c_ptr].value().scheduler@.contains(t_ptr)]
            #![trigger self.container_perms@.dom().contains(c_ptr), self.thread_perms@[t_ptr].value().owning_container]
            self.container_perms@.dom().contains(c_ptr) &&  self.container_perms@[c_ptr].value().scheduler@.contains(t_ptr)
            ==>
            self.thread_perms@.dom().contains(t_ptr)
            &&
            self.thread_perms@[t_ptr].value().owning_container == c_ptr
    }

    pub open spec fn pcid_ioid_wf(&self) -> bool{
        &&&
        forall|p_ptr_i:ProcPtr, p_ptr_j:ProcPtr| 
            #![trigger self.process_perms@[p_ptr_i].value().pcid, self.process_perms@[p_ptr_j].value().pcid]
            self.process_perms@.dom().contains(p_ptr_i) && self.process_perms@.dom().contains(p_ptr_j) && p_ptr_i != p_ptr_j
            ==>
            self.process_perms@[p_ptr_i].value().pcid != self.process_perms@[p_ptr_j].value().pcid
        &&&
        forall|p_ptr_i:ProcPtr, p_ptr_j:ProcPtr| 
            #![trigger self.process_perms@[p_ptr_i].value().ioid, self.process_perms@[p_ptr_j].value().ioid]
            self.process_perms@.dom().contains(p_ptr_i) && self.process_perms@.dom().contains(p_ptr_j) && p_ptr_i != p_ptr_j
            &&
            self.process_perms@[p_ptr_i].value().ioid.is_Some() && self.process_perms@[p_ptr_j].value().ioid.is_Some() 
            ==>
            self.process_perms@[p_ptr_i].value().ioid.unwrap() != self.process_perms@[p_ptr_j].value().ioid.unwrap()
    }

    pub open spec fn wf(&self) -> bool{
        &&&
        self.cpus_wf()
        &&&
        self.container_cpu_wf()
        &&&
        self.memory_disjoint()
        &&&
        self.container_perms_wf()
        &&&
        self.container_root_wf()
        &&&
        self.container_tree_wf()
        &&&
        self.containers_linkedlist_wf()
        &&&
        self.processes_container_wf()
        &&&
        self.processes_wf()
        &&&
        self.threads_process_wf()
        &&&
        self.threads_perms_wf()
        &&&
        self.endpoint_perms_wf()
        &&&
        self.threads_endpoint_descriptors_wf()
        &&&
        self.endpoints_queue_wf()
        &&&
        self.endpoints_container_wf()
        &&&
        self.schedulers_wf()
        &&&
        self.pcid_ioid_wf()
    }
}

//proofs
impl ProcessManager{
    pub proof fn wf_imply_container_proc_disjoint(&self)
        requires
            self.wf(),
        ensures
            forall|c_ptr_i:ContainerPtr, c_ptr_j: ContainerPtr|
                self.container_perms@.dom().contains(c_ptr_i) && self.container_perms@.dom().contains(c_ptr_j) && c_ptr_i != c_ptr_j
                ==>
                self.container_perms@[c_ptr_i].value().children_list@.to_set().disjoint(self.container_perms@[c_ptr_j].value().children_list@.to_set()),
            forall|c_ptr_i:ContainerPtr, c_ptr_j: ContainerPtr|
                self.container_perms@.dom().contains(c_ptr_i) && self.container_perms@.dom().contains(c_ptr_j) && c_ptr_i != c_ptr_j
                ==>
                self.container_perms@[c_ptr_i].value().proc_list@.to_set().disjoint(self.container_perms@[c_ptr_j].value().proc_list@.to_set()),
            forall|c_ptr_i:ContainerPtr, c_ptr_j: ContainerPtr|
                self.container_perms@.dom().contains(c_ptr_i) && self.container_perms@.dom().contains(c_ptr_j) && c_ptr_i != c_ptr_j
                ==>
                self.container_perms@[c_ptr_i].value().endpoint_list@.to_set().disjoint(self.container_perms@[c_ptr_j].value().endpoint_list@.to_set()),
            forall|p_ptr_i:ProcPtr, p_ptr_j: ProcPtr|
                self.process_perms@.dom().contains(p_ptr_i) && self.process_perms@.dom().contains(p_ptr_j) && p_ptr_i != p_ptr_j
                ==>
                self.process_perms@[p_ptr_i].value().owned_threads@.to_set().disjoint(self.process_perms@[p_ptr_j].value().owned_threads@.to_set()),
    {
        // assert(false);
    }
}

//exec
impl ProcessManager{
    pub fn new_thread(&mut self, proc_ptr:ProcPtr, pt_regs:Registers, page_ptr: PagePtr, page_perm: Tracked<PagePerm4k>) -> (ret:ThreadPtr)
        requires
            old(self).wf(),
            old(self).process_perms@.dom().contains(proc_ptr),
            old(self).page_closure().contains(page_ptr) == false,
            old(self).get_proc(proc_ptr).owned_threads.len() < MAX_NUM_THREADS_PER_PROC,
            old(self).get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota > 0,
            old(self).get_container(old(self).get_proc(proc_ptr).owning_container).scheduler.len() < CONTAINER_SCHEDULER_LEN,
            page_perm@.is_init(),
            page_perm@.addr() == page_ptr,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure().insert(page_ptr),
            old(self).get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota - 1 == self.get_container(self.get_proc(proc_ptr).owning_container).mem_quota,
    {
        proof{seq_push_lemma::<ThreadPtr>();}
        let container_ptr = self.get_proc(proc_ptr).owning_container;
        let old_mem_quota =  self.get_container(container_ptr).mem_quota;
        let mut proc_perm = Tracked(self.process_perms.borrow_mut().tracked_remove(proc_ptr));
        let proc_node_ref = proc_push_thread(proc_ptr,&mut proc_perm, &page_ptr);
        proof {
            self.process_perms.borrow_mut().tracked_insert(proc_ptr, proc_perm.get());
        }

        let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));
        let scheduler_node_ref = scheduler_push_thread(container_ptr,&mut container_perm, &page_ptr);
        container_set_mem_quota(container_ptr,&mut container_perm, old_mem_quota - 1);
        proof {
            self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
        }

        let (thread_ptr, thread_perm) = page_to_thread(page_ptr, page_perm, &pt_regs, container_ptr, proc_ptr, proc_node_ref, scheduler_node_ref);
        
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }
        // assert(self.cpus_wf());
        // assert(self.container_cpu_wf());
        // assert(self.memory_disjoint());
        // assert(self.container_perms_wf());
        // assert(self.container_root_wf());
        // assert(self.container_tree_wf());
        // assert(self.containers_linkedlist_wf());
        // assert(self.processes_container_wf());
        // assert(self.processes_wf());

        assert(self.threads_process_wf()) by {
            assert(self.process_perms@[proc_ptr].value().owned_threads@ =~= old(self).process_perms@[proc_ptr].value().owned_threads@.push(page_ptr));
            assert(
                forall|child_t_ptr:ThreadPtr| 
                #![auto]
                old(self).process_perms@[proc_ptr].value().owned_threads@.contains(child_t_ptr)
                ==> self.thread_perms@.dom().contains(child_t_ptr)
                    &&
                    self.thread_perms@[child_t_ptr].value().owning_proc == proc_ptr
            );
        };
        // assert(self.threads_perms_wf());
        // assert(self.endpoint_perms_wf());
        // assert(self.threads_endpoint_descriptors_wf());
        // assert(self.endpoints_queue_wf());
        // assert(self.endpoints_container_wf());
        assert(self.schedulers_wf()) by {
            assert(self.container_perms@[container_ptr].value().scheduler@ =~= old(self).container_perms@[container_ptr].value().scheduler@.push(page_ptr));
            assert(
                forall|child_t_ptr:ThreadPtr| 
                #![auto]
                old(self).container_perms@[container_ptr].value().scheduler@.contains(child_t_ptr)
                ==> self.thread_perms@.dom().contains(child_t_ptr)
                    &&
                    self.thread_perms@[child_t_ptr].value().owning_container == container_ptr
            );
        };
        thread_ptr
    }        

}

}

