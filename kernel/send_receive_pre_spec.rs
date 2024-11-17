use vstd::prelude::*;
verus! {
use crate::kernel::Kernel;
use crate::define::*;
impl Kernel{
    pub open spec fn no_receiver(&self, thread_ptr: ThreadPtr, endpoint_index: EndpointIdx) -> bool{
        let src_endpoint_ptr = self.get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap();
        &&&
        self.get_endpoint(src_endpoint_ptr).queue_state == EndpointState::SEND
        &&&
        self.get_endpoint(src_endpoint_ptr).queue.len() < MAX_NUM_THREADS_PER_ENDPOINT
    }
    pub open spec fn sender_queue_full(&self, thread_ptr: ThreadPtr, endpoint_index: EndpointIdx) -> bool{
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
    pub open spec fn receiver_exist(&self, thread_ptr: ThreadPtr, endpoint_index: EndpointIdx) -> bool{
        let src_endpoint_ptr = self.get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap();
        &&&
        self.get_endpoint(src_endpoint_ptr).queue_state == EndpointState::RECEIVE
        &&&
        self.get_endpoint(src_endpoint_ptr).queue.len() != 0
    }
}
}