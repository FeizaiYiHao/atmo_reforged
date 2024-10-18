use vstd::prelude::*;
verus! {
use core::mem::MaybeUninit;
use crate::define::*;
use vstd::simple_pptr::PointsTo;
use crate::process_manager::process::*;


#[verifier(external_body)]
pub fn proc_push_thread(proc_ptr:ProcPtr, proc_perm: &mut Tracked<PointsTo<Process>>, thread_ptr: &ThreadPtr) -> (ret: SLLIndex)
    requires    
        old(proc_perm)@.is_init(),
        old(proc_perm)@.addr() == proc_ptr,
        old(proc_perm)@.value().owned_threads.wf(),
        old(proc_perm)@.value().owned_threads.unique(),
        old(proc_perm)@.value().owned_threads.len() < MAX_NUM_THREADS_PER_PROC,
        old(proc_perm)@.value().owned_threads@.contains(*thread_ptr) == false,
    ensures
        proc_perm@.is_init(),
        proc_perm@.addr() == proc_ptr,
        proc_perm@.value().owning_container =~= old(proc_perm)@.value().owning_container,
        proc_perm@.value().rev_ptr =~= old(proc_perm)@.value().rev_ptr,
        proc_perm@.value().pcid =~= old(proc_perm)@.value().pcid,
        proc_perm@.value().ioid =~= old(proc_perm)@.value().ioid,
        // proc_perm@.value().owned_threads =~= old(proc_perm)@.value().owned_threads,

        proc_perm@.value().owned_threads.wf(),
        proc_perm@.value().owned_threads@ =~= old(proc_perm)@.value().owned_threads@.push(*thread_ptr),
        proc_perm@.value().owned_threads.len() == old(proc_perm)@.value().owned_threads.len() + 1,
        forall|index:SLLIndex|
            #![trigger old(proc_perm)@.value().owned_threads.node_ref_valid(index)]
            #![trigger proc_perm@.value().owned_threads.node_ref_valid(index)]
            old(proc_perm)@.value().owned_threads.node_ref_valid(index) ==> proc_perm@.value().owned_threads.node_ref_valid(index),
        forall|index:SLLIndex| 
            #![trigger old(proc_perm)@.value().owned_threads.node_ref_valid(index)]
            old(proc_perm)@.value().owned_threads.node_ref_valid(index) ==> index != ret,
        forall|index:SLLIndex| 
            #![trigger old(proc_perm)@.value().owned_threads.node_ref_valid(index)]
            #![trigger proc_perm@.value().owned_threads.node_ref_resolve(index)]
            #![trigger old(proc_perm)@.value().owned_threads.node_ref_resolve(index)]
            old(proc_perm)@.value().owned_threads.node_ref_valid(index) ==> proc_perm@.value().owned_threads.node_ref_resolve(index) == old(proc_perm)@.value().owned_threads.node_ref_resolve(index),
        proc_perm@.value().owned_threads.node_ref_valid(ret),
        proc_perm@.value().owned_threads.node_ref_resolve(ret) == *thread_ptr,
        proc_perm@.value().owned_threads.unique(),
{
    unsafe{
        let uptr = proc_ptr as *mut MaybeUninit<Process>;
        let ret = (*uptr).assume_init_mut().owned_threads.push(thread_ptr);
        return ret;
    }
}


}