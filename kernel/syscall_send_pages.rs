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
// use crate::va_range::VaRange4K;
// use crate::trap::Registers;
// use crate::pagetable::pagemap_util_t::*;
use crate::process_manager::thread::IPCPayLoad;
use crate::va_range::*;


pub open spec fn syscall_send_pages_spec(old:Kernel, new:Kernel, sender_thread_ptr: ThreadPtr, sender_endpoint_payload: EndpointIdx, sender_va_range:VaRange4K, ret: SyscallReturnStruct) -> bool {
    let blocking_endpoint_ptr = old.get_endpoint_ptr_by_endpoint_idx(sender_thread_ptr, sender_endpoint_payload).unwrap();
    let sender_proc_ptr = old.get_thread(sender_thread_ptr).owning_proc;
    let sender_container_ptr = old.get_thread(sender_thread_ptr).owning_container;
    let receiver_thread_ptr = old.get_endpoint(blocking_endpoint_ptr).queue@[0];
    let receiver_proc_ptr = old.get_thread(receiver_thread_ptr).owning_proc;
    let receiver_container_ptr = old.get_thread(receiver_thread_ptr).owning_container;
    let receiver_endpoint_payload_op = old.get_thread(receiver_thread_ptr).ipc_payload.get_payload_as_va_range();
    let receiver_va_range = old.get_thread(receiver_thread_ptr).ipc_payload.get_payload_as_va_range().unwrap();
    
    if old.get_endpoint_exists(sender_thread_ptr, sender_endpoint_payload) == false{
        old =~= new  
    }
    else if old.get_endpoint_exists(sender_thread_ptr, sender_endpoint_payload) && old.sender_queue_full(sender_thread_ptr, sender_endpoint_payload){
        old =~= new
    }else if old.get_endpoint_exists(sender_thread_ptr, sender_endpoint_payload) && old.no_receiver(sender_thread_ptr, sender_endpoint_payload){
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
            old.thread_dom().contains(t_ptr) && t_ptr != sender_thread_ptr
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
            new.container_dom().contains(c) && c != sender_container_ptr
            ==>
            old.get_container(c) =~= new.get_container(c)
        &&
        forall|e_ptr:EndpointPtr| 
            #![trigger new.get_endpoint(e_ptr)]
            new.endpoint_dom().contains(e_ptr) && e_ptr != blocking_endpoint_ptr
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
        new.get_thread(sender_thread_ptr).endpoint_descriptors@ =~= old.get_thread(sender_thread_ptr).endpoint_descriptors@
        &&
        new.get_endpoint(blocking_endpoint_ptr).queue@ =~= old.get_endpoint(blocking_endpoint_ptr).queue@.push(sender_thread_ptr)
        &&
        new.get_endpoint(blocking_endpoint_ptr).owning_threads@ =~= old.get_endpoint(blocking_endpoint_ptr).owning_threads@
        &&
        new.get_thread(sender_thread_ptr).ipc_payload.get_payload_as_va_range() == Some(sender_va_range)
        &&
        new.get_endpoint(blocking_endpoint_ptr).queue_state =~= old.get_endpoint(blocking_endpoint_ptr).queue_state
    }
    else if old.get_endpoint_exists(sender_thread_ptr, sender_endpoint_payload) && old.receiver_queue_empty(sender_thread_ptr, sender_endpoint_payload){
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
            old.thread_dom().contains(t_ptr) && t_ptr != sender_thread_ptr
            ==>
            new.get_thread(t_ptr) =~= old.get_thread(t_ptr)
        &&
        forall|p_ptr:ProcPtr| 
            #![trigger new.get_proc(p_ptr)]
            new.proc_dom().contains(p_ptr)
            ==>
            new.get_proc(p_ptr) =~= old.get_proc(p_ptr)
        &&
        forall|c:ContainerPtr| 
            #![trigger new.get_container_owned_pages(c)]
            new.container_dom().contains(c) && c != sender_container_ptr
            ==>
            old.get_container(c) =~= new.get_container(c)
        &&
        forall|e_ptr:EndpointPtr| 
            #![trigger new.get_endpoint(e_ptr)]
            new.endpoint_dom().contains(e_ptr) && e_ptr != blocking_endpoint_ptr
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
        new.get_thread(sender_thread_ptr).endpoint_descriptors@ =~= old.get_thread(sender_thread_ptr).endpoint_descriptors@
        &&
        new.get_endpoint(blocking_endpoint_ptr).queue@ =~= old.get_endpoint(blocking_endpoint_ptr).queue@.push(sender_thread_ptr)
        &&
        new.get_endpoint(blocking_endpoint_ptr).owning_threads@ =~= old.get_endpoint(blocking_endpoint_ptr).owning_threads@
        &&
        new.get_thread(sender_thread_ptr).ipc_payload.get_payload_as_va_range() == Some(sender_va_range)
        &&
        new.get_endpoint(blocking_endpoint_ptr).queue_state =~= EndpointState::SEND
    }
    else if old.get_container(receiver_container_ptr).scheduler.len() >= MAX_CONTAINER_SCHEDULER_LEN{
        old =~= new
    }
    else if old.get_thread(receiver_thread_ptr).ipc_payload.get_payload_as_va_range().is_None(){
        old =~= new
    }
    else if sender_va_range.len != receiver_va_range.len {
        old =~= new
    }
    else if old.address_space_range_shareable(sender_proc_ptr, &sender_va_range) == false{
        old =~= new
    }
    else if old.address_space_range_free(receiver_proc_ptr, &receiver_va_range) == false{
        old =~= new
    }
    else if old.get_container(receiver_container_ptr).mem_quota < receiver_va_range.len * 3{
        old =~= new
    }
    else if old.page_alloc.free_pages_4k.len() < receiver_va_range.len * 3 {
        old =~= new
    }
    else if sender_proc_ptr == receiver_proc_ptr{
        old =~= new
    }
    else{
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
            old.thread_dom().contains(t_ptr) && t_ptr != receiver_thread_ptr
            ==>
            new.get_thread(t_ptr) =~= old.get_thread(t_ptr)
        &&
        forall|p_ptr:ProcPtr| 
            #![trigger new.get_proc(p_ptr)]
            new.proc_dom().contains(p_ptr)
            ==>
            new.get_proc(p_ptr) =~= old.get_proc(p_ptr)
        &&
        forall|c:ContainerPtr| 
            #![trigger new.get_container_owned_pages(c)]
            new.container_dom().contains(c) && c != receiver_container_ptr
            ==>
            old.get_container(c) =~= new.get_container(c)
        &&
        forall|e_ptr:EndpointPtr| 
            #![trigger new.get_endpoint(e_ptr)]
            new.endpoint_dom().contains(e_ptr) && e_ptr != blocking_endpoint_ptr
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
            new.proc_dom().contains(p_ptr) && p_ptr != receiver_proc_ptr
            ==>
            new.get_address_space(p_ptr) =~= old.get_address_space(p_ptr)
        &&
        new.get_physical_page_mapping().dom() =~= old.get_physical_page_mapping().dom()
        &&
        forall|page_ptr:PagePtr|
            #![trigger new.get_physical_page_mapping()[page_ptr]]
            old.get_physical_page_mapping().dom().contains(page_ptr) && (forall|i:int|#![auto] 0 <= i < sender_va_range.len  ==> old.get_address_space(sender_proc_ptr)[sender_va_range@[i]].addr != page_ptr)
            ==> 
            old.get_physical_page_mapping()[page_ptr] == new.get_physical_page_mapping()[page_ptr]
        // Things changed
        &&
        new.get_thread(sender_thread_ptr).endpoint_descriptors@ =~= old.get_thread(sender_thread_ptr).endpoint_descriptors@
        &&
        new.get_thread(receiver_thread_ptr).endpoint_descriptors@ =~= old.get_thread(receiver_thread_ptr).endpoint_descriptors@
        &&
        new.get_endpoint(blocking_endpoint_ptr).queue@ =~= old.get_endpoint(blocking_endpoint_ptr).queue@.skip(1)
        &&
        new.get_endpoint(blocking_endpoint_ptr).owning_threads@ =~= old.get_endpoint(blocking_endpoint_ptr).owning_threads@
        &&
        new.get_endpoint(blocking_endpoint_ptr).queue_state =~= old.get_endpoint(blocking_endpoint_ptr).queue_state
        &&
        (forall|page_ptr:PagePtr|
            #![trigger new.get_physical_page_mapping()[page_ptr]]
            old.get_physical_page_mapping().dom().contains(page_ptr) && new.get_physical_page_mapping()[page_ptr] != old.get_physical_page_mapping()[page_ptr]
            ==> 
            (
                forall|p_ptr:Pcid,va:VAddr|
                    #![auto]
                    new.get_physical_page_mapping()[page_ptr].contains((p_ptr,va)) && !old.get_physical_page_mapping()[page_ptr].contains((p_ptr,va))
                    ==>
                    p_ptr == receiver_proc_ptr
                    &&
                    receiver_va_range@.contains(va)
            )
        )
        &&
        forall|i:int|
            #![auto]
            0 <= i < sender_va_range.len 
            ==>
            new.get_address_space(receiver_proc_ptr).dom().contains(receiver_va_range@[i])
            &&
            new.get_address_space(receiver_proc_ptr)[receiver_va_range@[i]] == old.get_address_space(sender_proc_ptr)[sender_va_range@[i]]
        &&
        forall|va:VAddr|
            #![auto]
            receiver_va_range@.contains(va) == false && old.get_address_space(receiver_proc_ptr).dom().contains(va)
            ==>
            new.get_address_space(receiver_proc_ptr)[va] == old.get_address_space(receiver_proc_ptr)[va]
    }
}

impl Kernel{


pub fn syscall_send_pages(&mut self, sender_thread_ptr: ThreadPtr, sender_endpoint_payload: EndpointIdx, sender_va_range:VaRange4K) ->  (ret: SyscallReturnStruct)
    requires
        old(self).wf(),
        old(self).thread_dom().contains(sender_thread_ptr),
        0 <= sender_endpoint_payload < MAX_NUM_ENDPOINT_DESCRIPTORS,
        old(self).get_thread(sender_thread_ptr).state == ThreadState::RUNNING,
        sender_va_range.wf(),
    ensures
        syscall_send_pages_spec(*old(self), *self, sender_thread_ptr, sender_endpoint_payload, sender_va_range, ret),
{
    proof{
        self.proc_man.thread_inv();
        self.proc_man.endpoint_inv();
    }

    let sender_container_ptr = self.proc_man.get_thread(sender_thread_ptr).owning_container;
    let sender_proc_ptr = self.proc_man.get_thread(sender_thread_ptr).owning_proc;
    let blocking_endpoint_ptr_op = self.proc_man.get_thread(sender_thread_ptr).endpoint_descriptors.get(sender_endpoint_payload);

    if blocking_endpoint_ptr_op.is_none(){
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);  
    }
    let blocking_endpoint_ptr = blocking_endpoint_ptr_op.unwrap();
    if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_send() && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len() < MAX_NUM_THREADS_PER_ENDPOINT{
        // Block
        self.proc_man.block_running_thread(sender_thread_ptr, sender_endpoint_payload, IPCPayLoad::Pages{va_range:sender_va_range});
        assert(self.wf());
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_send() && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len() >= MAX_NUM_THREADS_PER_ENDPOINT{
        // sender queue is full return error
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_receive() && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len() == 0{
        // change queue state and Block
        self.proc_man.block_running_thread_and_change_queue_state(sender_thread_ptr, sender_endpoint_payload, IPCPayLoad::Pages{va_range:sender_va_range}, EndpointState::SEND);
        assert(self.wf());
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    assert(self.receiver_exist(sender_thread_ptr, sender_endpoint_payload));

    let receiver_thread_ptr = self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.get_head();
    let receiver_proc_ptr = self.proc_man.get_thread(receiver_thread_ptr).owning_proc;
    let receiver_container_ptr = self.proc_man.get_thread(receiver_thread_ptr).owning_container;
    let receiver_endpoint_payload_op = self.proc_man.get_thread(receiver_thread_ptr).ipc_payload.get_payload_as_va_range();

    
    if self.proc_man.get_container(receiver_container_ptr).scheduler.len() >= MAX_CONTAINER_SCHEDULER_LEN{
        // cannot schedule the receiver
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    if receiver_endpoint_payload_op.is_none(){
        // receiver not receiving pages
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    let receiver_va_range = receiver_endpoint_payload_op.unwrap();

    if receiver_va_range.len != sender_va_range.len {
        // @Xiangdong TODO schedule the threads and return error
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);   
    }

    if self.check_address_space_va_range_shareable(sender_proc_ptr, &sender_va_range) == false{
        // sender pages not shareable
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    if self.check_address_space_va_range_free(receiver_proc_ptr, &receiver_va_range) == false{
        // receiver addresses are in used
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    if self.proc_man.get_container(receiver_container_ptr).mem_quota < receiver_va_range.len * 3{
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    if self.page_alloc.free_pages_4k.len() < receiver_va_range.len * 3 {
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    if receiver_proc_ptr == sender_proc_ptr{
        // @Xiangdong TODO allow sharing between same procs
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    assert(old(self).get_container(old(self).get_thread(old(self).get_endpoint(blocking_endpoint_ptr).queue@[0]).owning_container).scheduler.len() < MAX_CONTAINER_SCHEDULER_LEN);
    self.range_create_and_share_mapping(sender_proc_ptr, &sender_va_range, receiver_proc_ptr, &receiver_va_range);
    self.proc_man.schedule_blocked_thread(blocking_endpoint_ptr);
    return SyscallReturnStruct::NoSwitchNew(RetValueType::Else);
}

}
}