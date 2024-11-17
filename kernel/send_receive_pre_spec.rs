use vstd::prelude::*;
verus! {
use crate::kernel::Kernel;
use crate::define::*;
use crate::process_manager::process::Process;
use crate::process_manager::thread::Thread;
use crate::process_manager::container::Container;
use crate::process_manager::endpoint::Endpoint;
use crate::process_manager::cpu::*;
use crate::pagetable::entry::MapEntry;

impl Kernel{
    pub open spec fn no_receiver(&self, thread_ptr: ThreadPtr, endpoint_index: EndpointIdx) -> bool{
        let src_endpoint_ptr = self.get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap();
        &&&
        self.get_endpoint(src_endpoint_ptr).queue_state == EndpointState::SEND
        &&&
        self.get_endpoint(src_endpoint_ptr).queue.len() < MAX_NUM_THREADS_PER_ENDPOINT
    }
    pub open spec fn receiver_queue_full(&self, thread_ptr: ThreadPtr, endpoint_index: EndpointIdx) -> bool{
        let src_endpoint_ptr = self.get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap();
        &&&
        self.get_endpoint(src_endpoint_ptr).queue_state == EndpointState::SEND
        &&&
        self.get_endpoint(src_endpoint_ptr).queue.len() >= MAX_NUM_THREADS_PER_ENDPOINT
    }
    pub open spec fn receiver_queue_empty(&self, thread_ptr: ThreadPtr, endpoint_index: EndpointIdx) -> bool{
        let src_endpoint_ptr = self.get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap();
        &&&
        self.get_endpoint(src_endpoint_ptr).queue_state == EndpointState::RECEIVE
        &&&
        self.get_endpoint(src_endpoint_ptr).queue.len() == 0
    }
    pub open spec fn can_send_to_receiver(&self, thread_ptr: ThreadPtr, endpoint_index: EndpointIdx) -> bool{
        let src_endpoint_ptr = self.get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap();
        &&&
        self.get_endpoint(src_endpoint_ptr).queue_state == EndpointState::RECEIVE
        &&&
        self.get_endpoint(src_endpoint_ptr).queue.len() != 0
    }
}
}