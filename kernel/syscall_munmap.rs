use vstd::prelude::*;
verus! {

use crate::kernel::Kernel;
use crate::va_range::VaRange4K;
use crate::define::*;
use crate::util::page_ptr_util_u::*;


pub open spec fn syscall_munmap_spec_pre(&kernel: Kernel, thread: ThreadPtr, va_range: VaRange4K) -> bool 
{
    kernel.wf() && va_range.wf() 
} 

pub open spec fn syscall_munmap_spec_post(&kernel: Kernel, thread: ThreadPtr, va_range: VaRange4K, ret_success: bool) -> bool
{
    kernel.wf()
} 

impl Kernel {


    /// Kernel needs to make decision about container and pageallocator
    /// Page allocator should effectively be able to reclaim pages that is no longer mapped by any process.
    pub fn syscall_munmap(&mut self, target_thread_ptr: ThreadPtr, va_range: VaRange4K) ->  (ret: SyscallReturnStruct)
    requires
        old(self).wf(),
        
    ensures
        self.wf(),
        
    {
        let target_proc_ptr = self.proc_man.get_thread(target_thread_ptr).owning_proc;
        let target_pcid = self.proc_man.get_proc(target_proc_ptr).pcid;
        let target_container_ptr = self.proc_man.get_proc(target_proc_ptr).owning_container;
        
        let container_free =  self.proc_man.get_container(target_container_ptr).mem_quota;
        let va_kbytes = va_range.len() * 4;

        if self.proc_man.get_container(target_container_ptr).mem_quota < va_range.len{
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }

        let mut page_diff: Ghost<Seq<PagePtr>> = Ghost(Seq::empty());
        for i in 0..va_range.len
        {
            self.mem_man.pagetable_unmap_4k_page(pcid, va)
        }

        return SyscallReturnStruct::NoSwitchNew(RetValueType::SuccessSeqUsize{value: ret});
    } 
}
}