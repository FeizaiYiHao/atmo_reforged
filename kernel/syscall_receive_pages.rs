use vstd::prelude::*;
verus! {
use crate::define::*;
use crate::kernel::Kernel;
use crate::process_manager::thread::IPCPayLoad;
use crate::va_range::*;

pub open spec fn syscall_receive_pages_spec_success(old:Kernel, new:Kernel, receiver_thread_ptr: ThreadPtr, endpoint_idx: EndpointIdx, receiver_va_range:VaRange4K) -> bool 
{
    let blocking_endpoint_ptr = old.get_endpoint_ptr_by_endpoint_idx(receiver_thread_ptr, endpoint_idx).unwrap();
    let receiver_proc_ptr = old.get_thread(receiver_thread_ptr).owning_proc;
    let receiver_container_ptr = old.get_thread(receiver_thread_ptr).owning_container;
    let sender_thread_ptr = old.get_endpoint(blocking_endpoint_ptr).queue@[0];
    let sender_proc_ptr = old.get_thread(sender_thread_ptr).owning_proc;
    let sender_container_ptr = old.get_thread(sender_thread_ptr).owning_container;
    let sender_endpoint_payload_op = old.get_thread(sender_thread_ptr).ipc_payload.get_payload_as_va_range();
    let sender_va_range = old.get_thread(sender_thread_ptr).ipc_payload.get_payload_as_va_range().unwrap();

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
        old.thread_dom().contains(t_ptr) && t_ptr != receiver_thread_ptr && t_ptr != sender_thread_ptr
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
        new.container_dom().contains(c) && c != receiver_container_ptr && c != sender_container_ptr
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

pub open spec fn syscall_receive_pages_spec_fail(old:Kernel, new:Kernel, receiver_thread_ptr: ThreadPtr, endpoint_idx: EndpointIdx, receiver_va_range:VaRange4K) -> bool {
    let blocking_endpoint_ptr = old.get_endpoint_ptr_by_endpoint_idx(receiver_thread_ptr, endpoint_idx).unwrap();
    let receiver_proc_ptr = old.get_thread(receiver_thread_ptr).owning_proc;
    let receiver_container_ptr = old.get_thread(receiver_thread_ptr).owning_container;
    let sender_thread_ptr = old.get_endpoint(blocking_endpoint_ptr).queue@[0];
    let sender_proc_ptr = old.get_thread(sender_thread_ptr).owning_proc;
    let sender_container_ptr = old.get_thread(sender_thread_ptr).owning_container;
    let sender_endpoint_payload_op = old.get_thread(sender_thread_ptr).ipc_payload.get_payload_as_va_range();
    let sender_va_range = old.get_thread(sender_thread_ptr).ipc_payload.get_payload_as_va_range().unwrap();
    
    if old.get_endpoint_exists(receiver_thread_ptr, endpoint_idx) && old.no_sender(receiver_thread_ptr, endpoint_idx){
        // queue state is receive. block receiver thread   
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
            old.thread_dom().contains(t_ptr) && t_ptr != receiver_thread_ptr // blocked, thread state is changed
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
            new.container_dom().contains(c) && c != receiver_container_ptr // due to being blocked
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
        new.get_thread(receiver_thread_ptr).endpoint_descriptors@ =~= old.get_thread(receiver_thread_ptr).endpoint_descriptors@
        &&
        new.get_endpoint(blocking_endpoint_ptr).queue@ =~= old.get_endpoint(blocking_endpoint_ptr).queue@.push(receiver_thread_ptr)
        &&
        new.get_endpoint(blocking_endpoint_ptr).owning_threads@ =~= old.get_endpoint(blocking_endpoint_ptr).owning_threads@
        &&
        new.get_thread(receiver_thread_ptr).ipc_payload.get_payload_as_va_range() == Some(receiver_va_range)
        &&
        new.get_endpoint(blocking_endpoint_ptr).queue_state =~= old.get_endpoint(blocking_endpoint_ptr).queue_state
    }
    else if old.get_endpoint_exists(receiver_thread_ptr, endpoint_idx) && old.sender_queue_empty(receiver_thread_ptr, endpoint_idx){
        // queue type is send, and is empty. change queue state to receive
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
        new.get_thread(receiver_thread_ptr).endpoint_descriptors@ =~= old.get_thread(receiver_thread_ptr).endpoint_descriptors@
        &&
        new.get_endpoint(blocking_endpoint_ptr).queue@ =~= old.get_endpoint(blocking_endpoint_ptr).queue@.push(receiver_thread_ptr)
        &&
        new.get_endpoint(blocking_endpoint_ptr).owning_threads@ =~= old.get_endpoint(blocking_endpoint_ptr).owning_threads@
        &&
        new.get_thread(receiver_thread_ptr).ipc_payload.get_payload_as_va_range() == Some(receiver_va_range)
        &&
        new.get_endpoint(blocking_endpoint_ptr).queue_state =~= EndpointState::RECEIVE
    }
    else{
        old =~= new
    }
}

impl Kernel{


pub fn syscall_receive_pages(&mut self, receiver_thread_ptr: ThreadPtr, endpoint_idx: EndpointIdx, receiver_va_range:VaRange4K) ->  (ret: SyscallReturnStruct)
    requires
        old(self).wf(),
        old(self).thread_dom().contains(receiver_thread_ptr),
        0 <= endpoint_idx < MAX_NUM_ENDPOINT_DESCRIPTORS,
        old(self).get_thread(receiver_thread_ptr).state == ThreadState::RUNNING,
        receiver_va_range.wf(),
    ensures
        !ret.is_error() ==> syscall_receive_pages_spec_success(*old(self), *self, receiver_thread_ptr, endpoint_idx, receiver_va_range),
        ret.is_error() ==> syscall_receive_pages_spec_fail(*old(self), *self, receiver_thread_ptr, endpoint_idx, receiver_va_range),

{
    proof{
        self.proc_man.thread_inv();
        self.proc_man.endpoint_inv();
    }

    let receiver_container_ptr = self.proc_man.get_thread(receiver_thread_ptr).owning_container;
    let receiver_proc_ptr = self.proc_man.get_thread(receiver_thread_ptr).owning_proc;
    let blocking_endpoint_ptr_op = self.proc_man.get_thread(receiver_thread_ptr).endpoint_descriptors.get(endpoint_idx);

    if blocking_endpoint_ptr_op.is_none(){
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);  
    }
    let blocking_endpoint_ptr = blocking_endpoint_ptr_op.unwrap();
    if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_receive() && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len() < MAX_NUM_THREADS_PER_ENDPOINT{
        // Block
        self.proc_man.block_running_thread(receiver_thread_ptr, endpoint_idx, IPCPayLoad::Pages{va_range:receiver_va_range});
        assert(self.wf());
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_receive() && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len() >= MAX_NUM_THREADS_PER_ENDPOINT{
        // queue is full return error
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_send() && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len() == 0{
        // change queue state and Block
        self.proc_man.block_running_thread_and_change_queue_state(receiver_thread_ptr, endpoint_idx, IPCPayLoad::Pages{va_range:receiver_va_range}, EndpointState::RECEIVE);
        assert(self.wf());
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    assert(self.sender_exist(receiver_thread_ptr, endpoint_idx));

    let sender_thread_ptr = self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.get_head();
    let sender_proc_ptr = self.proc_man.get_thread(sender_thread_ptr).owning_proc;
    let sender_container_ptr = self.proc_man.get_thread(sender_thread_ptr).owning_container;
    let sender_endpoint_payload_op = self.proc_man.get_thread(sender_thread_ptr).ipc_payload.get_payload_as_va_range();

    
    if self.proc_man.get_container(sender_container_ptr).scheduler.len() >= MAX_CONTAINER_SCHEDULER_LEN{
        // cannot schedule the sender
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    if sender_endpoint_payload_op.is_none(){
        // sender didn't send any pages
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    let sender_va_range = sender_endpoint_payload_op.unwrap();

    if receiver_va_range.len != sender_va_range.len {
        // @Xiangdong TODO schedule the threads and return error
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);   
    }

    if !self.check_address_space_va_range_shareable(sender_proc_ptr, &sender_va_range) ||
       !self.check_address_space_va_range_free(receiver_proc_ptr, &receiver_va_range) {
        // sender pages not shareable or  receiver pages not free
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