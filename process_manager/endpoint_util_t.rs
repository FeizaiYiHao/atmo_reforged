use vstd::prelude::*;
verus! {
use core::mem::MaybeUninit;
use crate::define::*;
use vstd::simple_pptr::PointsTo;
use crate::process_manager::endpoint::*;


#[verifier(external_body)]
pub fn endpoint_add_ref(endpoint_ptr:EndpointPtr, endpoint_perm: &mut Tracked<PointsTo<Endpoint>>, thread_ptr: ThreadPtr)
    requires    
        old(endpoint_perm)@.is_init(),
        old(endpoint_perm)@.addr() == endpoint_ptr,
        old(endpoint_perm)@.value().rf_counter != usize::MAX,
        old(endpoint_perm)@.value().get_owning_threads().contains(thread_ptr) == false,
    ensures
        endpoint_perm@.is_init(),
        endpoint_perm@.addr() == endpoint_ptr, 
        endpoint_perm@.value().queue == old(endpoint_perm)@.value().queue,
        endpoint_perm@.value().queue_state == old(endpoint_perm)@.value().queue_state,
        // endpoint_perm@.value().rf_counter == old(endpoint_perm)@.value().rf_counter,
        // endpoint_perm@.value().owning_threads == old(endpoint_perm)@.value().owning_threads,
        endpoint_perm@.value().owning_container == old(endpoint_perm)@.value().owning_container,
        endpoint_perm@.value().container_rev_ptr == old(endpoint_perm)@.value().container_rev_ptr,
        endpoint_perm@.value().rf_counter == old(endpoint_perm)@.value().rf_counter + 1,
        endpoint_perm@.value().get_owning_threads() == old(endpoint_perm)@.value().get_owning_threads().insert(thread_ptr),
{
    unsafe{
        let uptr = endpoint_ptr as *mut MaybeUninit<Endpoint>;
        let ret = (*uptr).assume_init_mut().rf_counter += 1;
    }
}

}