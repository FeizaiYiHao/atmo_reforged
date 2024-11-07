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
    use crate::process_manager::endpoint_util_t::*;
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
    pub closed spec fn page_closure(&self) -> Set<PagePtr>
    {
        self.container_perms@.dom() + self.process_perms@.dom() + self.thread_perms@.dom() + self.endpoint_perms@.dom()
    }

    pub closed spec fn proc_dom(&self) -> Set<ProcPtr>
    {
        self.process_perms@.dom()
    }

    pub closed spec fn container_dom(&self) -> Set<ContainerPtr>
    {
        self.container_perms@.dom()
    }

    pub closed spec fn thread_dom(&self) -> Set<ThreadPtr>
    {
        self.thread_perms@.dom()
    }

    pub closed spec fn endpoint_dom(&self) -> Set<EndpointPtr>
    {
        self.endpoint_perms@.dom()
    }

    pub closed spec fn spec_get_proc(&self, proc_ptr:ProcPtr) -> &Process
        recommends
            self.wf(),
            self.proc_dom().contains(proc_ptr),
    {
        &self.process_perms@[proc_ptr].value()
    }

    #[verifier(when_used_as_spec(spec_get_proc))]
    pub fn get_proc(&self, proc_ptr:ProcPtr) ->(ret:&Process)
        requires
            self.wf(),
            self.proc_dom().contains(proc_ptr),
        ensures
            ret =~= self.get_proc(proc_ptr),
            ret.owned_threads.wf(),
            self.container_dom().contains(ret.owning_container)
    {
        let tracked proc_perm = self.process_perms.borrow().tracked_borrow(proc_ptr);
        let proc : &Process = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(proc_perm));
        proc
    }

    pub closed spec fn spec_get_proc_by_thread_ptr(&self, thread_ptr:ThreadPtr) -> &Process
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

    pub closed spec fn spec_get_thread(&self, thread_ptr:ThreadPtr) -> &Thread
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
            self.thread_dom().contains(thread_ptr),
        ensures
            ret == self.get_thread(thread_ptr),
            self.proc_dom().contains(ret.owning_proc),
    {
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
        thread
    }

    pub closed spec fn spec_get_cpu(&self, cpu_id:CpuId) -> &Cpu
        recommends
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
    {
        &self.cpu_list@[cpu_id as int]
    }

    #[verifier(when_used_as_spec(spec_get_cpu))]
    pub fn get_cpu(&self, cpu_id:CpuId) -> (ret: &Cpu)
        requires
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
        ensures
            ret == self.get_cpu(cpu_id),
    {
        self.cpu_list.get(cpu_id)
    }

    pub closed spec fn spec_get_is_cpu_running(&self, cpu_i:CpuId) -> bool
        recommends
            self.wf(),
            0 <= cpu_i < NUM_CPUS,
    {
        self.cpu_list@[cpu_i as int].current_thread.is_Some()
    }

    #[verifier(when_used_as_spec(spec_get_is_cpu_running))]
    pub fn get_is_cpu_running(&self, cpu_i:CpuId) -> (ret :bool)
        requires
            self.wf(),
            0 <= cpu_i < NUM_CPUS,
        ensures
            ret == self.get_is_cpu_running(cpu_i),
    {
        self.cpu_list.get(cpu_i).current_thread.is_some()
    }


    pub closed spec fn spec_get_container(&self, container_ptr:ContainerPtr) -> &Container
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
            self.container_dom().contains(container_ptr),
        ensures
            self.get_container(container_ptr) == ret,
    {
        let tracked container_perm = self.container_perms.borrow().tracked_borrow(container_ptr);
        let container : &Container = PPtr::<Container>::from_usize(container_ptr).borrow(Tracked(container_perm));
        container
    }

    pub closed spec fn spec_get_container_by_proc_ptr(&self, proc_ptr:ProcPtr) -> &Container
        recommends
            self.wf(),
            self.proc_dom().contains(proc_ptr),
    {
        &self.container_perms@[self.get_proc(proc_ptr).owning_container].value()
    }

    #[verifier(when_used_as_spec(spec_get_container_by_proc_ptr))]
    pub fn get_container_by_proc_ptr(&self, proc_ptr:ProcPtr) -> (ret:&Container)
        requires
            self.wf(),
            self.proc_dom().contains(proc_ptr),
        ensures
            self.get_container_by_proc_ptr(proc_ptr) == ret,
            self.container_dom().contains(self.get_proc(proc_ptr).owning_container),
            self.get_container(self.get_proc(proc_ptr).owning_container) == ret,
            ret.scheduler.wf(),
    {
        let container_ptr = self.get_proc(proc_ptr).owning_container;
        let tracked container_perm = self.container_perms.borrow().tracked_borrow(container_ptr);
        let container : &Container = PPtr::<Container>::from_usize(container_ptr).borrow(Tracked(container_perm));
        container
    }

    pub closed spec fn spec_get_container_by_thread_ptr(&self, thread_ptr:ThreadPtr) -> &Container
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

    pub closed spec fn spec_get_endpoint(&self, endpoint_ptr:EndpointPtr) -> &Endpoint
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
            self.endpoint_dom().contains(endpoint_ptr),
        ensures
            ret == self.get_endpoint(endpoint_ptr)
    {
        let tracked endpoint_perm = self.endpoint_perms.borrow().tracked_borrow(endpoint_ptr);
        let endpoint : &Endpoint = PPtr::<Endpoint>::from_usize(endpoint_ptr).borrow(Tracked(endpoint_perm));
        endpoint
    }

    pub closed spec fn spec_get_thread_ptr_by_cpu_id(&self, cpu_id:CpuId) -> (ret: Option<ThreadPtr>)
        recommends
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
    {
        self.cpu_list@[cpu_id as int].current_thread
    }

    #[verifier(when_used_as_spec(spec_get_thread_ptr_by_cpu_id))]
    pub fn get_thread_ptr_by_cpu_id(&self, cpu_id:CpuId) -> (ret: Option<ThreadPtr>)
        requires
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
        ensures
            ret == self.get_thread_ptr_by_cpu_id(cpu_id),
            self.get_is_cpu_running(cpu_id) == ret.is_Some(),
            ret.is_Some() ==> 
                self.get_cpu(cpu_id).current_thread.is_Some()
                &&
                self.thread_dom().contains(ret.unwrap()),
            self.get_thread_ptr_by_cpu_id(cpu_id) == ret,
            self.get_cpu(cpu_id).current_thread == ret,
    {
        self.cpu_list.get(cpu_id).current_thread
    }

    pub closed spec fn spec_get_owning_proc_by_thread_ptr(&self, t_ptr:ThreadPtr) -> (ret: ProcPtr)
        recommends
            self.wf(),
            self.thread_dom().contains(t_ptr),
    {
        self.get_thread(t_ptr).owning_proc
    }

    #[verifier(when_used_as_spec(spec_get_owning_proc_by_thread_ptr))]
    pub fn get_owning_proc_by_thread_ptr(&self, t_ptr:ThreadPtr) -> (ret: ProcPtr)
        requires
            self.wf(),
            self.thread_dom().contains(t_ptr),
        ensures
            ret == self.get_owning_proc_by_thread_ptr(t_ptr),
            self.proc_dom().contains(ret),
            self.get_thread(t_ptr).owning_proc == ret,
    {
        self.get_thread(t_ptr).owning_proc
    }

    pub fn get_proc_ptr_by_cpu_id(&self, cpu_id:CpuId) -> (ret: Option<ProcPtr>)
        requires
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
        ensures
            self.get_is_cpu_running(cpu_id) <==> ret.is_Some(),
            ret.is_Some()
                ==> 
                self.get_is_cpu_running(cpu_id)
                &&
                self.cpu_list@[cpu_id as int].current_thread.is_Some()
                &&
                self.get_thread(self.cpu_list@[cpu_id as int].current_thread.unwrap()).owning_proc == ret.unwrap()
                &&
                self.proc_dom().contains(ret.unwrap()),
            ret.is_None()
                ==> 
                self.get_is_cpu_running(cpu_id) == false
                &&
                self.cpu_list@[cpu_id as int].current_thread.is_None()
             
    {
        let thread_ptr_op = self.cpu_list.get(cpu_id).current_thread;
        if thread_ptr_op.is_some(){
            return Some(self.get_thread(thread_ptr_op.unwrap()).owning_proc);
        }else{
            return None;
        }
    }

    pub closed spec fn spec_get_endpoint_ptr_by_endpoint_idx(&self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx) -> Option<EndpointPtr>
        recommends
            self.wf(),
            self.thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
    {
        self.get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int]
    }

    #[verifier(when_used_as_spec(spec_get_endpoint_ptr_by_endpoint_idx))]
    pub fn get_endpoint_ptr_by_endpoint_idx(&self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx) -> (ret: Option<EndpointPtr>)
        requires
            self.wf(),
            self.thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        ensures
            ret == self.get_endpoint_ptr_by_endpoint_idx(thread_ptr,endpoint_index),
            ret.is_Some() ==> self.endpoint_dom().contains(ret.unwrap()),
    {
        *self.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index)
    }

    pub closed spec fn spec_get_endpoint_by_endpoint_idx(&self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx) -> Option<&Endpoint>
        recommends
            self.wf(),
            self.thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
    {
        if self.get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].is_None(){
            None
        }else{
            Some(&self.get_endpoint(self.get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()))
        }
    }

    #[verifier(when_used_as_spec(spec_get_endpoint_by_endpoint_idx))]
    pub fn get_endpoint_by_endpoint_idx(&self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx) -> (ret: Option<&Endpoint>)
        requires
            self.wf(),
            self.thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        ensures
            ret == self.get_endpoint_by_endpoint_idx(thread_ptr,endpoint_index),
    {
        if self.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index).is_none(){
            None
        }else{
            Some(&self.get_endpoint(self.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index).unwrap()))
        } 
    }
}

//specs
impl ProcessManager{
    pub closed spec fn cpus_wf(&self) -> bool{
        &&&
        self.cpu_list.wf()
        // &&&
        // forall|cpu_i:CpuId| 
        //     #![trigger self.cpu_list@[cpu_i as int].active]
        //     #![trigger self.cpu_list@[cpu_i as int].current_thread]
        //     self.cpu_list@[cpu_i as int].active == false ==> self.cpu_list@[cpu_i as int].current_thread.is_None()
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
        #![trigger self.cpu_list@[cpu_i as int].active]
        0 <= cpu_i < NUM_CPUS 
        ==> 
        self.container_perms@.dom().contains(self.cpu_list@[cpu_i as int].owning_container)
        &&
        self.container_perms@[self.cpu_list@[cpu_i as int].owning_container].value().owned_cpus@.contains(cpu_i)
        &&
        self.cpu_list@[cpu_i as int].active == false ==> self.cpu_list@[cpu_i as int].current_thread.is_None()
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
            self.container_perms@[c_ptr].value().children.wf()
            &&
            self.container_perms@[c_ptr].value().children.unique()
            &&
            self.container_perms@[c_ptr].value().owned_cpus.wf()
            &&
            self.container_perms@[c_ptr].value().scheduler.wf() 
            &&
            self.container_perms@[c_ptr].value().scheduler.unique() 
            &&
            self.container_perms@[c_ptr].value().owned_procs.wf()
            &&
            self.container_perms@[c_ptr].value().owned_procs.unique()
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
            self.container_perms@[c_ptr].value().children@.to_set().subset_of(self.container_perms@.dom())
            &&
            self.container_perms@.dom().contains(c_ptr) ==> self.container_perms@[c_ptr].value().children@.contains(c_ptr) == false
        &&&
        forall|c_ptr:ContainerPtr, child_c_ptr:ContainerPtr| 
            // #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().children@.contains(child_c_ptr)]
            self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().children@.contains(child_c_ptr)
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
                && self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children@.to_set().contains(c_ptr)
                && self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children.node_ref_valid(self.container_perms@[c_ptr].value().parent_rev_ptr.unwrap())
                && self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children.node_ref_resolve(self.container_perms@[c_ptr].value().parent_rev_ptr.unwrap()) == c_ptr
    }

    pub closed spec fn processes_container_wf(&self) -> bool{
        // &&&
        // forall|c_ptr:ContainerPtr| 
        //     #![trigger self.container_perms@[c_ptr].value().owned_procs]
        //     self.container_perms@.dom().contains(c_ptr)
        //     ==>
        //     self.container_perms@[c_ptr].value().owned_procs@.to_set().subset_of(self.process_perms@.dom())
        &&&
        forall|c_ptr:ContainerPtr, child_p_ptr:ProcPtr| 
            self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().owned_procs@.contains(child_p_ptr)
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
            self.container_perms@[self.process_perms@[p_ptr].value().owning_container].value().owned_procs@.to_set().contains(p_ptr)
            &&
            self.container_perms@[self.process_perms@[p_ptr].value().owning_container].value().owned_procs.node_ref_valid(self.process_perms@[p_ptr].value().rev_ptr)
            &&
            self.container_perms@[self.process_perms@[p_ptr].value().owning_container].value().owned_procs.node_ref_resolve(self.process_perms@[p_ptr].value().rev_ptr) == p_ptr
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
            self.endpoint_perms@[e_ptr].value().owning_threads@.finite()
            &&
            self.endpoint_perms@[e_ptr].value().rf_counter == self.endpoint_perms@[e_ptr].value().owning_threads@.len()
            &&
            self.endpoint_perms@[e_ptr].value().owning_threads@.subset_of(self.thread_perms@.dom())
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
            #![trigger self.container_perms@[c_ptr].value().owned_endpoints@.contains(child_e_ptr)]
            self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().owned_endpoints@.contains(child_e_ptr)
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
            self.container_perms@[self.endpoint_perms@[e_ptr].value().owning_container].value().owned_endpoints@.to_set().contains(e_ptr)
            &&
            self.container_perms@[self.endpoint_perms@[e_ptr].value().owning_container].value().owned_endpoints.node_ref_valid(self.endpoint_perms@[e_ptr].value().container_rev_ptr)
            &&
            self.container_perms@[self.endpoint_perms@[e_ptr].value().owning_container].value().owned_endpoints.node_ref_resolve(self.endpoint_perms@[e_ptr].value().container_rev_ptr) == e_ptr
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

    pub closed spec fn pcid_ioid_wf(&self) -> bool{
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

    pub closed spec fn wf(&self) -> bool{
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
        &&&
        self.threads_cpu_wf()
    }
}

//proofs
impl ProcessManager{
    pub proof fn pcid_unique(&self, target_proc_ptr:ProcPtr)
        requires
            self.wf(),
            self.proc_dom().contains(target_proc_ptr) 
        ensures
            forall|p_ptr:ProcPtr| #![auto] self.proc_dom().contains(p_ptr) && target_proc_ptr != p_ptr ==> self.get_proc(p_ptr).pcid != self.get_proc(target_proc_ptr).pcid,
    {}

    pub proof fn wf_imply_proc_to_unique_pcid(&self) 
        requires
            self.wf(),
        ensures
            forall|p_ptr_i:ProcPtr, p_ptr_j:ProcPtr|
                #![trigger self.get_proc(p_ptr_i).pcid, self.get_proc(p_ptr_j).pcid]
                self.proc_dom().contains(p_ptr_i) && self.proc_dom().contains(p_ptr_j) 
                &&
                p_ptr_i != p_ptr_j
                ==>
                self.get_proc(p_ptr_i).pcid != self.get_proc(p_ptr_j).pcid
    {
    }

    pub proof fn wf_imply_container_proc_disjoint(&self)
        requires
            self.wf(),
        ensures
            forall|c_ptr_i:ContainerPtr, c_ptr_j: ContainerPtr|
                self.container_perms@.dom().contains(c_ptr_i) && self.container_perms@.dom().contains(c_ptr_j) && c_ptr_i != c_ptr_j
                ==>
                self.container_perms@[c_ptr_i].value().children@.to_set().disjoint(self.container_perms@[c_ptr_j].value().children@.to_set()),
            forall|c_ptr_i:ContainerPtr, c_ptr_j: ContainerPtr|
                self.container_perms@.dom().contains(c_ptr_i) && self.container_perms@.dom().contains(c_ptr_j) && c_ptr_i != c_ptr_j
                ==>
                self.container_perms@[c_ptr_i].value().owned_procs@.to_set().disjoint(self.container_perms@[c_ptr_j].value().owned_procs@.to_set()),
            forall|c_ptr_i:ContainerPtr, c_ptr_j: ContainerPtr|
                self.container_perms@.dom().contains(c_ptr_i) && self.container_perms@.dom().contains(c_ptr_j) && c_ptr_i != c_ptr_j
                ==>
                self.container_perms@[c_ptr_i].value().owned_endpoints@.to_set().disjoint(self.container_perms@[c_ptr_j].value().owned_endpoints@.to_set()),
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
    pub fn set_container_mem_quota(&mut self, container_ptr:ContainerPtr, new_quota:usize)
        requires
            old(self).wf(),
            old(self).container_dom().contains(container_ptr),
        ensures
            self.wf(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.thread_dom() =~= old(self).thread_dom(),
            self.container_dom() =~= old(self).container_dom(),
            self.endpoint_dom() =~= old(self).endpoint_dom(), 
            self.page_closure() =~= old(self).page_closure(),
            forall|p_ptr:ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr)
                ==>
                self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|t_ptr:ThreadPtr|
                #![auto]
                self.thread_dom().contains(t_ptr)
                ==>
                self.get_thread(t_ptr) =~= old(self).get_thread(t_ptr),
            forall|c_ptr:ContainerPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && c_ptr != container_ptr
                ==>
                self.get_container(c_ptr) =~= old(self).get_container(c_ptr),
            forall|e_ptr:EndpointPtr|
                #![auto]
                self.endpoint_dom().contains(e_ptr)
                ==>
                self.get_endpoint(e_ptr) =~= old(self).get_endpoint(e_ptr),
            self.get_container(container_ptr).owned_procs =~= self.get_container(container_ptr).owned_procs,
            self.get_container(container_ptr).parent =~= self.get_container(container_ptr).parent,
            self.get_container(container_ptr).parent_rev_ptr =~= self.get_container(container_ptr).parent_rev_ptr,
            self.get_container(container_ptr).children =~= self.get_container(container_ptr).children,
            self.get_container(container_ptr).owned_endpoints =~= self.get_container(container_ptr).owned_endpoints,
            // self.get_container(container_ptr).mem_quota =~= self.get_container(container_ptr).mem_quota,
            self.get_container(container_ptr).mem_used =~= self.get_container(container_ptr).mem_used,
            self.get_container(container_ptr).owned_cpus =~= self.get_container(container_ptr).owned_cpus,
            self.get_container(container_ptr).scheduler =~= self.get_container(container_ptr).scheduler,
            self.get_container(container_ptr).mem_quota =~= new_quota,
    {
        let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));
        container_set_mem_quota(container_ptr,&mut container_perm, new_quota);
        proof {
            self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
        }
    }

    pub fn new_thread(&mut self, target_proc_ptr:ProcPtr, pt_regs:Registers, page_ptr: PagePtr, page_perm: Tracked<PagePerm4k>) -> (ret:ThreadPtr)
        requires
            old(self).wf(),
            old(self).proc_dom().contains(target_proc_ptr),
            old(self).page_closure().contains(page_ptr) == false,
            old(self).get_proc(target_proc_ptr).owned_threads.len() < MAX_NUM_THREADS_PER_PROC,
            old(self).get_container_by_proc_ptr(target_proc_ptr).mem_quota > 0,
            old(self).get_container_by_proc_ptr(target_proc_ptr).scheduler.len() < MAX_CONTAINER_SCHEDULER_LEN,
            page_perm@.is_init(),
            page_perm@.addr() == page_ptr,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure().insert(page_ptr),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom().insert(ret),
            old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_quota - 1 == self.get_container(self.get_proc(target_proc_ptr).owning_container).mem_quota,
            old(self).get_proc(target_proc_ptr).pcid =~= self.get_proc(target_proc_ptr).pcid,
            old(self).get_proc(target_proc_ptr).ioid =~= self.get_proc(target_proc_ptr).ioid,
            forall|proc_ptr:ProcPtr|
                #![trigger self.get_proc(proc_ptr)]
                self.proc_dom().contains(proc_ptr) && proc_ptr != target_proc_ptr
                ==> 
                self.get_proc(proc_ptr) =~= old(self).get_proc(proc_ptr),
            forall|container_ptr:ContainerPtr|
                #![trigger self.get_container(container_ptr).owned_procs]
                self.container_dom().contains(container_ptr) && container_ptr != self.get_proc(target_proc_ptr).owning_container
                ==> 
                self.get_container(container_ptr).owned_procs =~= old(self).get_container(container_ptr).owned_procs,
    {
        proof{seq_push_lemma::<ThreadPtr>();}
        let container_ptr = self.get_proc(target_proc_ptr).owning_container;
        let old_mem_quota =  self.get_container(container_ptr).mem_quota;
        let mut proc_perm = Tracked(self.process_perms.borrow_mut().tracked_remove(target_proc_ptr));
        let proc_node_ref = proc_push_thread(target_proc_ptr,&mut proc_perm, &page_ptr);
        proof {
            self.process_perms.borrow_mut().tracked_insert(target_proc_ptr, proc_perm.get());
        }

        let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));
        let scheduler_node_ref = scheduler_push_thread(container_ptr,&mut container_perm, &page_ptr);
        container_set_mem_quota(container_ptr,&mut container_perm, old_mem_quota - 1);
        proof {
            self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
        }

        let (thread_ptr, thread_perm) = page_to_thread(page_ptr, page_perm, &pt_regs, container_ptr, target_proc_ptr, proc_node_ref, scheduler_node_ref);
        
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.container_root_wf());
        assert(self.container_tree_wf());
        assert(self.containers_linkedlist_wf());
        assert(self.processes_container_wf());
        assert(self.processes_wf());

        assert(self.threads_process_wf()) by {
            assert(self.process_perms@[target_proc_ptr].value().owned_threads@ =~= old(self).process_perms@[target_proc_ptr].value().owned_threads@.push(page_ptr));
            assert(
                forall|child_t_ptr:ThreadPtr| 
                #![auto]
                old(self).process_perms@[target_proc_ptr].value().owned_threads@.contains(child_t_ptr)
                ==> self.thread_perms@.dom().contains(child_t_ptr)
                    &&
                    self.thread_perms@[child_t_ptr].value().owning_proc == target_proc_ptr
            );
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf());
        assert(self.endpoints_container_wf()) by {
            assert(
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@[c_ptr]]
                    self.container_perms@.dom().contains(c_ptr)
                    ==> 
                    self.container_perms@[c_ptr].value().owned_endpoints =~= old(self).container_perms@[c_ptr].value().owned_endpoints
            );
            assert(
                forall|child_e_ptr:EndpointPtr| 
                    #![trigger self.endpoint_perms@.dom().contains(child_e_ptr)]
                    self.endpoint_perms@.dom().contains(child_e_ptr)
                    ==> 
                    self.endpoint_perms@[child_e_ptr].value() =~= old(self).endpoint_perms@[child_e_ptr].value()
            );
            assert(
                forall|c_ptr:ContainerPtr, child_e_ptr:EndpointPtr| 
                    #![trigger self.container_perms@[c_ptr].value().owned_endpoints@.contains(child_e_ptr)]
                    self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().owned_endpoints@.contains(child_e_ptr)
                    ==> self.endpoint_perms@.dom().contains(child_e_ptr)
                        &&
                        self.endpoint_perms@[child_e_ptr].value().owning_container == c_ptr);
            assert(
                forall|e_ptr:EndpointPtr| 
                    #![trigger self.endpoint_perms@[e_ptr].value().owning_container]
                    self.endpoint_perms@.dom().contains(e_ptr)
                    ==>
                    self.container_perms@.dom().contains(self.endpoint_perms@[e_ptr].value().owning_container)
                    &&
                    self.container_perms@[self.endpoint_perms@[e_ptr].value().owning_container].value().owned_endpoints@.to_set().contains(e_ptr)
                    &&
                    self.container_perms@[self.endpoint_perms@[e_ptr].value().owning_container].value().owned_endpoints.node_ref_valid(self.endpoint_perms@[e_ptr].value().container_rev_ptr)
                    &&
                    self.container_perms@[self.endpoint_perms@[e_ptr].value().owning_container].value().owned_endpoints.node_ref_resolve(self.endpoint_perms@[e_ptr].value().container_rev_ptr) == e_ptr);
        };
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


    pub fn new_thread_with_endpoint(&mut self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx, proc_ptr:ProcPtr, pt_regs:Registers, page_ptr: PagePtr, page_perm: Tracked<PagePerm4k>) -> (ret:ThreadPtr)
        requires
            old(self).wf(),
            old(self).proc_dom().contains(proc_ptr),
            old(self).thread_dom().contains(thread_ptr),
            old(self).page_closure().contains(page_ptr) == false,
            old(self).get_proc(proc_ptr).owned_threads.len() < MAX_NUM_THREADS_PER_PROC,
            old(self).get_container_by_proc_ptr(proc_ptr).mem_quota > 0,
            old(self).get_container_by_proc_ptr(proc_ptr).scheduler.len() < MAX_CONTAINER_SCHEDULER_LEN,
            old(self).get_thread(thread_ptr).owning_proc == proc_ptr,
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_endpoint_by_endpoint_idx(thread_ptr, endpoint_index).is_Some() || old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).is_Some(),
            old(self).get_endpoint_by_endpoint_idx(thread_ptr, endpoint_index).unwrap().rf_counter_is_full() == false || old(self).get_endpoint(old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap()).rf_counter_is_full() == false,
            page_perm@.is_init(),
            page_perm@.addr() == page_ptr,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure().insert(page_ptr),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom().insert(ret),
            old(self).get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota - 1 == self.get_container(self.get_proc(proc_ptr).owning_container).mem_quota,
            old(self).get_proc(proc_ptr).pcid =~= self.get_proc(proc_ptr).pcid,
            old(self).get_proc(proc_ptr).ioid =~= self.get_proc(proc_ptr).ioid,
            forall|p_ptr:ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) && p_ptr != proc_ptr
                ==> 
                self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|container_ptr:ContainerPtr|
                #![trigger self.get_container(container_ptr).owned_procs]
                self.container_dom().contains(container_ptr) && container_ptr != self.get_proc(proc_ptr).owning_container
                ==> 
                self.get_container(container_ptr).owned_procs =~= old(self).get_container(container_ptr).owned_procs,
    {
        proof{seq_push_lemma::<ThreadPtr>();}
        let container_ptr = self.get_proc(proc_ptr).owning_container;
        let old_mem_quota =  self.get_container(container_ptr).mem_quota;
        let endpoint_ptr = self.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index).unwrap();
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

        let (thread_ptr, thread_perm) = page_to_thread_with_endpoint(page_ptr, page_perm, &pt_regs, container_ptr, proc_ptr, proc_node_ref, scheduler_node_ref, endpoint_ptr);
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }

        let mut endpoint_perm = Tracked(self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr));
        endpoint_add_ref(endpoint_ptr,&mut endpoint_perm, page_ptr);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.container_root_wf());
        assert(self.container_tree_wf());
        assert(self.containers_linkedlist_wf());
        assert(self.processes_container_wf());
        assert(self.processes_wf());

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
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf());
        assert(self.endpoints_container_wf()) by {
            assert(
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@[c_ptr]]
                    self.container_perms@.dom().contains(c_ptr)
                    ==> 
                    self.container_perms@[c_ptr].value().owned_endpoints =~= old(self).container_perms@[c_ptr].value().owned_endpoints
            );
            assert(
                forall|child_e_ptr:EndpointPtr| 
                    #![trigger self.endpoint_perms@.dom().contains(child_e_ptr)]
                    self.endpoint_perms@.dom().contains(child_e_ptr) && child_e_ptr != endpoint_ptr
                    ==> 
                    self.endpoint_perms@[child_e_ptr].value() =~= old(self).endpoint_perms@[child_e_ptr].value()
            );
            assert(
                forall|c_ptr:ContainerPtr, child_e_ptr:EndpointPtr| 
                    #![trigger self.container_perms@[c_ptr].value().owned_endpoints@.contains(child_e_ptr)]
                    self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().owned_endpoints@.contains(child_e_ptr)
                    ==> self.endpoint_perms@.dom().contains(child_e_ptr)
                        &&
                        self.endpoint_perms@[child_e_ptr].value().owning_container == c_ptr);
            assert(
                forall|e_ptr:EndpointPtr| 
                    #![trigger self.endpoint_perms@[e_ptr].value().owning_container]
                    self.endpoint_perms@.dom().contains(e_ptr)
                    ==>
                    self.container_perms@.dom().contains(self.endpoint_perms@[e_ptr].value().owning_container)
                    &&
                    self.container_perms@[self.endpoint_perms@[e_ptr].value().owning_container].value().owned_endpoints@.to_set().contains(e_ptr)
                    &&
                    self.container_perms@[self.endpoint_perms@[e_ptr].value().owning_container].value().owned_endpoints.node_ref_valid(self.endpoint_perms@[e_ptr].value().container_rev_ptr)
                    &&
                    self.container_perms@[self.endpoint_perms@[e_ptr].value().owning_container].value().owned_endpoints.node_ref_resolve(self.endpoint_perms@[e_ptr].value().container_rev_ptr) == e_ptr);
        };
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

