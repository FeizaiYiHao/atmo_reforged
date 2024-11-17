use vstd::prelude::*;
verus! {
// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_impl::*;
// use crate::util::page_ptr_util_u::*;
// use crate::lemma::lemma_t::set_lemma;
// use crate::lemma::lemma_u::*;
// use crate::util::page_ptr_util_u::*;
use crate::define::*;
// use crate::trap::*;
// use crate::pagetable::pagemap_util_t::*;
// use crate::pagetable::entry::*;
use crate::kernel::Kernel;
use crate::va_range::VaRange4K;
use crate::trap::Registers;
use crate::pagetable::pagemap_util_t::*;
use crate::process_manager::thread::IPCPayLoad;

pub open spec fn syscall_send_endpoint_endpoint_exists(old:Kernel, target_thread_ptr: ThreadPtr, endpoint_index: EndpointIdx) -> bool{
    &&&
    old.get_endpoint_exists(target_thread_ptr, endpoint_index)
}

pub open spec fn syscall_send_endpoint_spec(old:Kernel, new:Kernel, target_thread_ptr: ThreadPtr, endpoint_index: EndpointIdx, src_endpoint_index:EndpointIdx, ret: SyscallReturnStruct) -> bool {
    let target_endpoint_ptr = old.get_endpoint_ptr_by_endpoint_idx(target_thread_ptr, endpoint_index).unwrap();
    let src_container_ptr = old.get_thread(target_thread_ptr).owning_container;

    &&&
    old.get_endpoint_exists(target_thread_ptr, endpoint_index) == false ==> old =~= new
    &&&
    old.get_endpoint_exists(target_thread_ptr, endpoint_index) && old.receiver_queue_full(target_thread_ptr, endpoint_index) ==> old =~= new
    &&&
    old.get_endpoint_exists(target_thread_ptr, endpoint_index) && old.no_receiver(target_thread_ptr, endpoint_index)
        ==>
        (
            // basically nothing changed 
            old.thread_dom() =~= new.thread_dom()
            &&
            old.proc_dom() =~= new.proc_dom()
            &&
            old.container_dom() =~= new.container_dom()
            &&
            old.endpoint_dom() =~= new.endpoint_dom()
            &&
            forall|t_ptr:ThreadPtr| 
                #![trigger new.get_thread(t_ptr)]
                old.thread_dom().contains(t_ptr) && t_ptr != target_thread_ptr
                ==>
                new.get_thread(t_ptr) =~= old.get_thread(t_ptr)
            &&
            forall|proc_ptr:ProcPtr| 
                #![trigger new.get_proc(proc_ptr)]
                new.proc_dom().contains(proc_ptr)
                ==>
                new.get_proc(proc_ptr) =~= old.get_proc(proc_ptr)
            &&
            forall|c:ContainerPtr| 
                #![trigger new.get_container_owned_pages(c)]
                new.container_dom().contains(c) && c != src_container_ptr
                ==>
                old.get_container(c) =~= new.get_container(c)
            &&
            forall|e_ptr:EndpointPtr| 
                #![trigger new.get_endpoint(e_ptr)]
                new.endpoint_dom().contains(e_ptr) && e_ptr != target_endpoint_ptr
                ==> 
                old.get_endpoint(e_ptr) =~= new.get_endpoint(e_ptr)
            &&
            forall|c:ContainerPtr| 
                #![trigger new.get_container_owned_pages(c)]
                new.container_dom().contains(c)
                ==> 
                old.get_container_owned_pages(c) =~= new.get_container_owned_pages(c)
            &&
            forall|p_ptr:ProcPtr| 
                #![trigger new.get_address_space(p_ptr)]
                new.proc_dom().contains(p_ptr)
                ==>
                new.get_address_space(p_ptr) =~= old.get_address_space(p_ptr)
            &&
            forall|page_ptr:PagePtr|
                #![trigger new.get_physical_page_mapping()[page_ptr]]
                old.get_physical_page_mapping().dom().contains(page_ptr)
                ==> 
                old.get_physical_page_mapping()[page_ptr] == new.get_physical_page_mapping()[page_ptr]
            // Things changed
            &&
            new.get_thread(target_thread_ptr).endpoint_descriptors@ =~= old.get_thread(target_thread_ptr).endpoint_descriptors@
            &&
            new.get_endpoint(target_endpoint_ptr).queue@ =~= old.get_endpoint(target_endpoint_ptr).queue@.push(target_thread_ptr)
            &&
            new.get_endpoint(target_endpoint_ptr).owning_threads@ =~= old.get_endpoint(target_endpoint_ptr).owning_threads@
            &&
            new.get_thread(target_thread_ptr).ipc_payload.get_payload_as_endpoint() == Some(src_endpoint_index)
            &&
            new.get_endpoint(target_endpoint_ptr).queue_state =~= old.get_endpoint(target_endpoint_ptr).queue_state
        )
        &&&
        old.get_endpoint_exists(target_thread_ptr, endpoint_index) && old.receiver_queue_empty(target_thread_ptr, endpoint_index)
            ==>
            (
                // basically nothing changed 
                old.thread_dom() =~= new.thread_dom()
                &&
                old.proc_dom() =~= new.proc_dom()
                &&
                old.container_dom() =~= new.container_dom()
                &&
                old.endpoint_dom() =~= new.endpoint_dom()
                &&
                forall|t_ptr:ThreadPtr| 
                    #![trigger new.get_thread(t_ptr)]
                    old.thread_dom().contains(t_ptr) && t_ptr != target_thread_ptr
                    ==>
                    new.get_thread(t_ptr) =~= old.get_thread(t_ptr)
                &&
                forall|proc_ptr:ProcPtr| 
                    #![trigger new.get_proc(proc_ptr)]
                    new.proc_dom().contains(proc_ptr)
                    ==>
                    new.get_proc(proc_ptr) =~= old.get_proc(proc_ptr)
                &&
                forall|c:ContainerPtr| 
                    #![trigger new.get_container_owned_pages(c)]
                    new.container_dom().contains(c) && c != src_container_ptr
                    ==>
                    old.get_container(c) =~= new.get_container(c)
                &&
                forall|e_ptr:EndpointPtr| 
                    #![trigger new.get_endpoint(e_ptr)]
                    new.endpoint_dom().contains(e_ptr) && e_ptr != target_endpoint_ptr
                    ==> 
                    old.get_endpoint(e_ptr) =~= new.get_endpoint(e_ptr)
                &&
                forall|c:ContainerPtr| 
                    #![trigger new.get_container_owned_pages(c)]
                    new.container_dom().contains(c)
                    ==> 
                    old.get_container_owned_pages(c) =~= new.get_container_owned_pages(c)
                &&
                forall|p_ptr:ProcPtr| 
                    #![trigger new.get_address_space(p_ptr)]
                    new.proc_dom().contains(p_ptr)
                    ==>
                    new.get_address_space(p_ptr) =~= old.get_address_space(p_ptr)
                &&
                forall|page_ptr:PagePtr|
                    #![trigger new.get_physical_page_mapping()[page_ptr]]
                    old.get_physical_page_mapping().dom().contains(page_ptr)
                    ==> 
                    old.get_physical_page_mapping()[page_ptr] == new.get_physical_page_mapping()[page_ptr]
                // Things changed
                &&
                new.get_thread(target_thread_ptr).endpoint_descriptors@ =~= old.get_thread(target_thread_ptr).endpoint_descriptors@
                &&
                new.get_endpoint(target_endpoint_ptr).queue@ =~= old.get_endpoint(target_endpoint_ptr).queue@.push(target_thread_ptr)
                &&
                new.get_endpoint(target_endpoint_ptr).owning_threads@ =~= old.get_endpoint(target_endpoint_ptr).owning_threads@
                &&
                new.get_thread(target_thread_ptr).ipc_payload.get_payload_as_endpoint() == Some(src_endpoint_index)
                &&
                new.get_endpoint(target_endpoint_ptr).queue_state =~= EndpointState::SEND
            )
}

impl Kernel{


pub fn syscall_send_endpoint(&mut self, target_thread_ptr: ThreadPtr, endpoint_index: EndpointIdx, src_endpoint_index:EndpointIdx) ->  (ret: SyscallReturnStruct)
    requires
        old(self).wf(),
        old(self).thread_dom().contains(target_thread_ptr),
        0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        old(self).get_thread(target_thread_ptr).state == ThreadState::RUNNING,
    ensures
        syscall_send_endpoint_spec(*old(self), *self, target_thread_ptr, endpoint_index, src_endpoint_index, ret),
{
    proof{
        self.proc_man.thread_inv();
        self.proc_man.endpoint_inv();
    }

    let sender_container_ptr = self.proc_man.get_thread(target_thread_ptr).owning_container;
    let target_endpoint_ptr_op = self.proc_man.get_thread(target_thread_ptr).endpoint_descriptors.get(endpoint_index);

    if target_endpoint_ptr_op.is_none(){
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);  
    }
    let target_endpoint_ptr = target_endpoint_ptr_op.unwrap();
    if self.proc_man.get_endpoint(target_endpoint_ptr).queue_state.is_send() && self.proc_man.get_endpoint(target_endpoint_ptr).queue.len() < MAX_NUM_THREADS_PER_ENDPOINT{
        // Block
        self.proc_man.block_running_thread(target_thread_ptr, endpoint_index, IPCPayLoad::Endpoint{endpoint_index:src_endpoint_index});
        assert(self.wf());
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    if self.proc_man.get_endpoint(target_endpoint_ptr).queue_state.is_send() && self.proc_man.get_endpoint(target_endpoint_ptr).queue.len() >= MAX_NUM_THREADS_PER_ENDPOINT{
        // return error
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }


    if self.proc_man.get_endpoint(target_endpoint_ptr).queue_state.is_receive() && self.proc_man.get_endpoint(target_endpoint_ptr).queue.len() == 0{
        // change queue state and Block
        self.proc_man.block_running_thread_and_change_queue_state(target_thread_ptr, endpoint_index, IPCPayLoad::Endpoint{endpoint_index:src_endpoint_index}, EndpointState::SEND);
        assert(self.wf());
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    assert(self.can_send_to_receiver(target_thread_ptr, endpoint_index));
    // does stuff
    return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);

    

    return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);

}

}
}