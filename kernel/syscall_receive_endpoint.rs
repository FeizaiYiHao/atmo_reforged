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


impl Kernel{
    pub fn syscall_receive_endpoint(&mut self, receiver_thread_ptr: ThreadPtr, endpoint_index: EndpointIdx, receiver_endpoint_payload:EndpointIdx) ->  (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(receiver_thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(receiver_thread_ptr).state == ThreadState::RUNNING,
            0 <= receiver_endpoint_payload < MAX_NUM_ENDPOINT_DESCRIPTORS
        ensures
            // syscall_receive_endpoint_spec(*old(self), *self, receiver_thread_ptr, endpoint_index, receiver_endpoint_payload, ret),
    {
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Else);
    }

}

}