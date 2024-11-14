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

#[verifier(external_body)]
pub fn page_to_proc(page_ptr: PagePtr, page_perm: Tracked<PagePerm4k>, owning_container:ContainerPtr, rev_ptr: SLLIndex, pcid:Pcid, ioid:Option<IOid>) -> (ret:(ProcPtr,Tracked<PointsTo<Process>>))
    requires    
        page_perm@.is_init(),
        page_perm@.addr() == page_ptr,
    ensures
        ret.0 == page_ptr,
        ret.1@.is_init(),
        ret.1@.addr() == ret.0,
        ret.1@.value().owning_container == owning_container,
        ret.1@.value().rev_ptr == rev_ptr,
        ret.1@.value().pcid == pcid,
        ret.1@.value().ioid == ioid,
        ret.1@.value().owned_threads.wf(),
        ret.1@.value().owned_threads@ == Seq::<ThreadPtr>::empty(),
        ret.1@.value().owned_threads.len() == 0,
        forall|index:SLLIndex|
            #![trigger ret.1@.value().owned_threads.node_ref_valid(index)]
            ret.1@.value().owned_threads.node_ref_valid(index) == false
{
    unsafe{
        let uptr = page_ptr as *mut MaybeUninit<Process>;
        (*uptr).assume_init_mut().owning_container = owning_container;
        (*uptr).assume_init_mut().rev_ptr = rev_ptr;
        (*uptr).assume_init_mut().pcid = pcid;
        (*uptr).assume_init_mut().ioid = ioid;
        (*uptr).assume_init_mut().owned_threads.init();
        (page_ptr, Tracked::assume_new())
    }
}

pub fn page_to_proc_with_first_thread(page_ptr: PagePtr, page_perm: Tracked<PagePerm4k>, owning_container:ContainerPtr, rev_ptr: SLLIndex, pcid:Pcid, ioid:Option<IOid>, first_thread:ThreadPtr) -> (ret:(ProcPtr,Tracked<PointsTo<Process>>,SLLIndex))
    requires    
        page_perm@.is_init(),
        page_perm@.addr() == page_ptr,
    ensures
        ret.0 == page_ptr,
        ret.1@.is_init(),
        ret.1@.addr() == ret.0,
        ret.1@.value().owning_container == owning_container,
        ret.1@.value().rev_ptr == rev_ptr,
        ret.1@.value().pcid == pcid,
        ret.1@.value().ioid == ioid,
        ret.1@.value().owned_threads.wf(),
        ret.1@.value().owned_threads@ == Seq::<ThreadPtr>::empty().push(first_thread),
        ret.1@.value().owned_threads.len() == 1,
        // forall|index:SLLIndex|
        //     #![trigger ret.1@.value().owned_threads.node_ref_valid(index)]
        //     index != ret.2
        //     ==>
        //     ret.1@.value().owned_threads.node_ref_valid(index) == false,
        ret.1@.value().owned_threads.node_ref_valid(ret.2),
        ret.1@.value().owned_threads.node_ref_resolve(ret.2) == first_thread,
{
    let (p_ptr, mut p_perm) = page_to_proc(page_ptr, page_perm, owning_container, rev_ptr, pcid, ioid);
    let sll = proc_push_thread(p_ptr, &mut p_perm, &first_thread);
    (p_ptr, p_perm, sll)
}
}