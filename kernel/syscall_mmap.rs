use vstd::prelude::*;
verus! {
// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_impl::*;
// use crate::util::page_ptr_util_u::*;
use crate::util::page_ptr_util_u::*;
use crate::define::*;
use crate::trap::*;
use crate::kernel::Kernel;

impl Kernel{

    pub fn create_entry_and_map(&mut self, proc_ptr:ProcPtr, va:VAddr) -> (ret: usize)
    requires
        old(self).wf(),
        old(self).proc_dom().contains(proc_ptr),
        old(self).get_container_quota(old(self).get_proc_owning_container(proc_ptr)) >= 4,
        old(self).get_num_of_free_pages() >= 4,
        va_4k_valid(va),
    {
        let container_ptr = self.proc_man.get_proc(proc_ptr).owning_container;
        let pcid = self.proc_man.get_proc(proc_ptr).pcid;
        0
    }
}



// pub fn syscall_mmap(&mut self, thread_ptr: ThreadPtr, va_start:VAddr, len: usize) ->  (ret: SyscallReturnStruct)
//     requires
//         old(self).wf(),
//         old(self).thread_dom().contains(thread_ptr),
//         0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
//     {

//     }


}