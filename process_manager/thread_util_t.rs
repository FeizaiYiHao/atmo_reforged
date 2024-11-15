use vstd::prelude::*;
verus! {
use core::mem::MaybeUninit;
use crate::define::*;
use vstd::simple_pptr::PointsTo;
use crate::process_manager::thread::*;
use crate::trap::Registers;

#[verifier(external_body)]
pub fn page_to_thread(page_ptr: PagePtr, page_perm: Tracked<PagePerm4k>, pt_regs:&Registers, owning_container:ContainerPtr, owning_proc:ProcPtr, proc_rev_ptr:SLLIndex, scheduler_rev_ptr:SLLIndex) -> (ret:(ThreadPtr,Tracked<PointsTo<Thread>>))
    requires    
        page_perm@.is_init(),
        page_perm@.addr() == page_ptr,
    ensures
        ret.0 == page_ptr,
        ret.1@.is_init(),
        ret.1@.addr() == ret.0,
        ret.1@.value().owning_container == owning_container,
        ret.1@.value().owning_proc == owning_proc,
        ret.1@.value().state == ThreadState::SCHEDULED,
        ret.1@.value().proc_rev_ptr == proc_rev_ptr,
        ret.1@.value().scheduler_rev_ptr == Some(scheduler_rev_ptr),
        ret.1@.value().blocking_endpoint_ptr.is_None(),
        ret.1@.value().endpoint_rev_ptr.is_None(),
        ret.1@.value().running_cpu.is_None(),
        ret.1@.value().endpoint_descriptors@ =~= Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat,|i: int| {None}),
        ret.1@.value().ipc_payload.is_None(),
        ret.1@.value().error_code.is_None(),
        ret.1@.value().trap_frame.unwrap() =~= pt_regs,
{
    unsafe{
        let uptr = page_ptr as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().owning_container = owning_container;
        (*uptr).assume_init_mut().owning_proc = owning_proc;
        (*uptr).assume_init_mut().state = ThreadState::SCHEDULED;
        (*uptr).assume_init_mut().proc_rev_ptr = proc_rev_ptr;
        (*uptr).assume_init_mut().scheduler_rev_ptr = Some(scheduler_rev_ptr);
        (*uptr).assume_init_mut().blocking_endpoint_ptr = None;
        (*uptr).assume_init_mut().endpoint_rev_ptr = None;
        (*uptr).assume_init_mut().running_cpu = None;
        (*uptr).assume_init_mut().endpoint_descriptors.init2none();
        (*uptr).assume_init_mut().ipc_payload = IPCPayLoad::Empty;
        (*uptr).assume_init_mut().error_code = None;
        (*uptr).assume_init_mut().trap_frame.set_self(pt_regs);
        (page_ptr, Tracked::assume_new())
    }
}

#[verifier(external_body)]
pub fn page_to_thread_with_endpoint(page_ptr: PagePtr, page_perm: Tracked<PagePerm4k>, pt_regs:&Registers, owning_container:ContainerPtr, owning_proc:ProcPtr, proc_rev_ptr:SLLIndex, scheduler_rev_ptr:SLLIndex, endpoint_ptr:EndpointPtr) -> (ret:(ThreadPtr,Tracked<PointsTo<Thread>>))
    requires    
        page_perm@.is_init(),
        page_perm@.addr() == page_ptr,
    ensures
        ret.0 == page_ptr,
        ret.1@.is_init(),
        ret.1@.addr() == ret.0,
        ret.1@.value().owning_container == owning_container,
        ret.1@.value().owning_proc == owning_proc,
        ret.1@.value().state == ThreadState::SCHEDULED,
        ret.1@.value().proc_rev_ptr == proc_rev_ptr,
        ret.1@.value().scheduler_rev_ptr == Some(scheduler_rev_ptr),
        ret.1@.value().blocking_endpoint_ptr.is_None(),
        ret.1@.value().endpoint_rev_ptr.is_None(),
        ret.1@.value().running_cpu.is_None(),
        ret.1@.value().endpoint_descriptors@ =~= Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat,|i: int| {None}).update(0, Some(endpoint_ptr)),
        ret.1@.value().ipc_payload.is_None(),
        ret.1@.value().error_code.is_None(),
        ret.1@.value().trap_frame.unwrap() =~= pt_regs,
{
    unsafe{
        let uptr = page_ptr as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().owning_container = owning_container;
        (*uptr).assume_init_mut().owning_proc = owning_proc;
        (*uptr).assume_init_mut().state = ThreadState::SCHEDULED;
        (*uptr).assume_init_mut().proc_rev_ptr = proc_rev_ptr;
        (*uptr).assume_init_mut().scheduler_rev_ptr = Some(scheduler_rev_ptr);
        (*uptr).assume_init_mut().blocking_endpoint_ptr = None;
        (*uptr).assume_init_mut().endpoint_rev_ptr = None;
        (*uptr).assume_init_mut().running_cpu = None;
        (*uptr).assume_init_mut().endpoint_descriptors.init2none();
        (*uptr).assume_init_mut().endpoint_descriptors.set(0, Some(endpoint_ptr));
        (*uptr).assume_init_mut().ipc_payload = IPCPayLoad::Empty;
        (*uptr).assume_init_mut().error_code = None;
        (*uptr).assume_init_mut().trap_frame.set_self(pt_regs);
        (page_ptr, Tracked::assume_new())
    }
}

#[verifier(external_body)]
pub fn thread_set_blocking_endpoint_endpoint_ref_scheduler_ref_state_and_ipc_payload(thread_ptr:ThreadPtr, thread_perm: &mut Tracked<PointsTo<Thread>>, blocking_endpoint_ptr: Option<EndpointPtr>, endpoint_rev_ptr: Option<SLLIndex>,scheduler_rev_ptr: Option<SLLIndex>, state:ThreadState, ipc_payload: IPCPayLoad) 
    requires    
        old(thread_perm)@.is_init(),
        old(thread_perm)@.addr() == thread_ptr,
    ensures
        thread_perm@.is_init(),
        thread_perm@.addr() == thread_ptr,
        thread_perm@.value().owning_container == old(thread_perm)@.value().owning_container,
        thread_perm@.value().owning_proc == old(thread_perm)@.value().owning_proc,
        thread_perm@.value().state == state,
        thread_perm@.value().proc_rev_ptr == old(thread_perm)@.value().proc_rev_ptr,
        thread_perm@.value().scheduler_rev_ptr == scheduler_rev_ptr,
        thread_perm@.value().blocking_endpoint_ptr == blocking_endpoint_ptr,
        thread_perm@.value().endpoint_rev_ptr == endpoint_rev_ptr,
        thread_perm@.value().running_cpu.is_None(),
        thread_perm@.value().endpoint_descriptors == old(thread_perm)@.value().endpoint_descriptors,
        thread_perm@.value().ipc_payload == ipc_payload,
        thread_perm@.value().error_code == old(thread_perm)@.value().error_code,
        thread_perm@.value().trap_frame == old(thread_perm)@.value().trap_frame,
{
    unsafe{
        let uptr = thread_ptr as *mut MaybeUninit<Thread>;
        let ret = (*uptr).assume_init_mut().state = state;
        let ret = (*uptr).assume_init_mut().scheduler_rev_ptr = scheduler_rev_ptr;
        let ret = (*uptr).assume_init_mut().blocking_endpoint_ptr = blocking_endpoint_ptr;
        let ret = (*uptr).assume_init_mut().endpoint_rev_ptr = endpoint_rev_ptr;
        let ret = (*uptr).assume_init_mut().ipc_payload = ipc_payload;
        return ret;
    }
}

}