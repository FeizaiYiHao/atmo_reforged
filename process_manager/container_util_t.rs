use vstd::prelude::*;
verus! {
use core::mem::MaybeUninit;
use crate::define::*;
use vstd::simple_pptr::PointsTo;
use crate::process_manager::container::*;


#[verifier(external_body)]
pub fn scheduler_push_thread(container_ptr:ContainerPtr, container_perm: &mut Tracked<PointsTo<Container>>, thread_ptr: &ThreadPtr) -> (ret: SLLIndex)
    requires    
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().scheduler.wf(),
        old(container_perm)@.value().scheduler.unique(),
        old(container_perm)@.value().scheduler.len() < MAX_CONTAINER_SCHEDULER_LEN,
        old(container_perm)@.value().scheduler@.contains(*thread_ptr) == false,
    ensures
        container_perm@.is_init(),
        container_perm@.addr() == container_ptr, 
        container_perm@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        container_perm@.value().parent =~= old(container_perm)@.value().parent,
        container_perm@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        container_perm@.value().children =~= old(container_perm)@.value().children,
        container_perm@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        container_perm@.value().mem_quota =~= old(container_perm)@.value().mem_quota,
        container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        container_perm@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        container_perm@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        // container_perm@.value().scheduler =~= old(container_perm)@.value().scheduler,

        container_perm@.value().scheduler.wf(),
        container_perm@.value().scheduler@ == old(container_perm)@.value().scheduler@.push(*thread_ptr),
        container_perm@.value().scheduler.len() == old(container_perm)@.value().scheduler.len() + 1,
        forall|index:SLLIndex|
            #![trigger old(container_perm)@.value().scheduler.node_ref_valid(index)]
            #![trigger container_perm@.value().scheduler.node_ref_valid(index)]
            old(container_perm)@.value().scheduler.node_ref_valid(index) ==> container_perm@.value().scheduler.node_ref_valid(index),
        forall|index:SLLIndex| 
            #![trigger old(container_perm)@.value().scheduler.node_ref_valid(index)]
            old(container_perm)@.value().scheduler.node_ref_valid(index) ==> index != ret,
        forall|index:SLLIndex| 
            #![trigger old(container_perm)@.value().scheduler.node_ref_valid(index)]
            #![trigger container_perm@.value().scheduler.node_ref_resolve(index)]
            #![trigger old(container_perm)@.value().scheduler.node_ref_resolve(index)]
            old(container_perm)@.value().scheduler.node_ref_valid(index) ==> container_perm@.value().scheduler.node_ref_resolve(index) == old(container_perm)@.value().scheduler.node_ref_resolve(index),
        container_perm@.value().scheduler.node_ref_valid(ret),
        container_perm@.value().scheduler.node_ref_resolve(ret) == *thread_ptr,
        container_perm@.value().scheduler.unique(),
{
    unsafe{
        let uptr = container_ptr as *mut MaybeUninit<Container>;
        let ret = (*uptr).assume_init_mut().scheduler.push(thread_ptr);
        return ret;
    }
}

#[verifier(external_body)]
pub fn container_set_mem_quota(container_ptr:ContainerPtr, container_perm: &mut Tracked<PointsTo<Container>>, value: usize) 
    requires    
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
    ensures
        container_perm@.is_init(),
        container_perm@.addr() == container_ptr, 
        container_perm@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        container_perm@.value().parent =~= old(container_perm)@.value().parent,
        container_perm@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        container_perm@.value().children =~= old(container_perm)@.value().children,
        container_perm@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        // container_perm@.value().mem_quota =~= old(container_perm)@.value().mem_quota,
        container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        container_perm@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        container_perm@.value().scheduler =~= old(container_perm)@.value().scheduler,
        container_perm@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        container_perm@.value().mem_quota =~= value,
{
    unsafe{
        let uptr = container_ptr as *mut MaybeUninit<Container>;
        (*uptr).assume_init_mut().mem_quota = value;
    }
}

#[verifier(external_body)]
pub fn container_set_owned_threads(container_ptr:ContainerPtr, container_perm: &mut Tracked<PointsTo<Container>>, owned_threads: Ghost<Set<ThreadPtr>>) 
    requires    
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
    ensures
        container_perm@.is_init(),
        container_perm@.addr() == container_ptr, 
        container_perm@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        container_perm@.value().parent =~= old(container_perm)@.value().parent,
        container_perm@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        container_perm@.value().children =~= old(container_perm)@.value().children,
        container_perm@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        container_perm@.value().mem_quota =~= old(container_perm)@.value().mem_quota,
        container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        container_perm@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        container_perm@.value().scheduler =~= old(container_perm)@.value().scheduler,
        // container_perm@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        container_perm@.value().owned_threads =~= owned_threads,
{
}

}