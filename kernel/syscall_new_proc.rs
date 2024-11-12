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
use crate::va_range::VaRange4K;
use crate::trap::Registers;


impl Kernel{

pub fn syscall_new_proc_with_endpoint(&mut self, target_thread_ptr: ThreadPtr, endpoint_index: EndpointIdx, pt_regs:Registers, va_range:VaRange4K) ->  (ret: SyscallReturnStruct)
    requires
        old(self).wf(),
        old(self).thread_dom().contains(target_thread_ptr),
        va_range.wf(),
        va_range.len * 4 < usize::MAX,
    ensures
{
    let target_proc_ptr = self.proc_man.get_thread(target_thread_ptr).owning_proc;
    let target_pcid = self.proc_man.get_proc(target_proc_ptr).pcid;
    let target_container_ptr = self.proc_man.get_proc(target_proc_ptr).owning_container;

    proof{
        self.proc_man.thread_inv();
    }

    
    return SyscallReturnStruct::NoSwitchNew(RetValueType::Else);
}

}
}