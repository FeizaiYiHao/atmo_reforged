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
use crate::pagetable::pagemap_util_t::*;

impl Kernel{

pub fn syscall_new_proc_with_endpoint(&mut self, target_thread_ptr: ThreadPtr, endpoint_index: EndpointIdx, pt_regs:Registers, va_range:VaRange4K) ->  (ret: SyscallReturnStruct)
    requires
        old(self).wf(),
        old(self).thread_dom().contains(target_thread_ptr),
        va_range.wf(),
        va_range.len * 3 + 3 < usize::MAX,
        0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS
    ensures
{
    let src_proc_ptr = self.proc_man.get_thread(target_thread_ptr).owning_proc;
    let src_pcid = self.proc_man.get_proc(src_proc_ptr).pcid;
    let src_container_ptr = self.proc_man.get_thread(target_thread_ptr).owning_container;

    if self.proc_man.get_proc(src_proc_ptr).owned_threads.len() >= MAX_NUM_THREADS_PER_PROC{
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }
    if self.proc_man.get_container(src_container_ptr).mem_quota < va_range.len * 3 + 3{
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }
    if self.proc_man.get_container(src_container_ptr).scheduler.len() >= MAX_CONTAINER_SCHEDULER_LEN {
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    } 
    if self.proc_man.get_container(src_container_ptr).owned_procs.len() >= CONTAINER_PROC_LIST_LEN {
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    } 
    assert(self.proc_man.get_container(src_container_ptr).owned_procs.wf());
    assert(self.proc_man.get_container(src_container_ptr).owned_procs.len() < CONTAINER_PROC_LIST_LEN );
    if self.page_alloc.free_pages_4k.len() <= va_range.len * 3  + 3{
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }
    if self.mem_man.free_pcids.len() < 1 {
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }
    
    let endpoint_ptr_op = self.proc_man.get_endpoint_ptr_by_endpoint_idx(target_thread_ptr, endpoint_index);
    if endpoint_ptr_op.is_none(){
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }
    let endpoint_ptr = endpoint_ptr_op.unwrap();
    if self.proc_man.get_endpoint(endpoint_ptr).rf_counter == usize::MAX {
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    if self.check_address_space_va_range_shareable(src_proc_ptr, &va_range) == false{
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }
    
    let (page_ptr_1,mut page_perm_1) = self.page_alloc.alloc_page_4k();
    let (page_ptr_2,page_perm_2) = self.page_alloc.alloc_page_4k();
    let (page_ptr_3,page_perm_3) = self.page_alloc.alloc_page_4k();

    // assert(page_ptr_1 != page_ptr_2);
    // assert(page_ptr_1 != page_ptr_3);
    // assert(page_ptr_2 != page_ptr_3);
    let (page_map_ptr, mut page_map_perm) = page_perm_to_page_map(page_ptr_1,page_perm_1);
    let new_pcid = self.mem_man.new_page_table(page_ptr_2, page_map_ptr, page_map_perm);
    assert(self.proc_man == old(self).proc_man);
    self.proc_man.new_proc_with_endpoint(target_thread_ptr, endpoint_index, pt_regs, page_ptr_2, page_perm_2, page_ptr_3, page_perm_3, new_pcid);

    return SyscallReturnStruct::NoSwitchNew(RetValueType::Else);
}

}
}