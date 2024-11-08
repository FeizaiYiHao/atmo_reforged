use vstd::prelude::*;
verus! {
// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_impl::*;
// use crate::util::page_ptr_util_u::*;
use crate::define::*;
use crate::trap::*;
use crate::kernel::Kernel;

pub open spec fn syscall_new_thread_with_endpoint_requirement(old:Kernel, thread_id: ThreadPtr, endpoint_index: EndpointIdx) -> bool {
    let p_id = old.get_owning_proc_by_thread_ptr(thread_id);
    if old.get_is_process_thread_list_full(p_id){
        false
    }else{
        let c_id = old.get_proc_owning_container(p_id);
        if old.get_container_quota(c_id) < 1 {
            false
        }else{
            if old.get_is_scheduler_full(c_id) {
                false
            }else{
                if old.get_num_of_free_pages() <= 0{
                    false
                }else{
                    if old.get_endpoint_shareable(thread_id, endpoint_index) == false{
                        false
                    }else{
                        true
                    }
                }
            }
        }
    }
}

pub open spec fn syscall_new_thread_with_endpoint_spec(old:Kernel, new:Kernel, thread_id: ThreadPtr, endpoint_index: EndpointIdx, ret: SyscallReturnStruct) -> bool{
    &&&
    syscall_new_thread_with_endpoint_requirement(old, thread_id, endpoint_index) == false ==> new =~= old
    &&&
    syscall_new_thread_with_endpoint_requirement(old, thread_id, endpoint_index) == true ==>
        // things that did not change
        old.proc_dom() =~= new.proc_dom()
        &&
        old.container_dom() =~= new.container_dom()
        &&
        old.endpoint_dom() =~= new.endpoint_dom()
        &&
        forall|t_ptr:ThreadPtr| 
            #![trigger new.get_thread(t_ptr)]
            old.thread_dom().contains(t_ptr)
            ==>
            new.get_thread(t_ptr) =~= old.get_thread(t_ptr)
        &&
        forall|proc_ptr:ProcPtr| 
            #![trigger new.get_address_space(proc_ptr)]
            new.proc_dom().contains(proc_ptr)
            ==>
            new.get_address_space(proc_ptr) =~= old.get_address_space(proc_ptr)
        &&
        forall|proc_ptr:ProcPtr| 
            #![trigger new.get_proc(proc_ptr)]
            new.proc_dom().contains(proc_ptr) && proc_ptr != old.get_thread(thread_id).owning_proc
            ==>
            new.get_proc(proc_ptr) =~= old.get_proc(proc_ptr)
        &&
        forall|c:ContainerPtr| 
            #![trigger new.get_container_owned_pages(c)]
            new.container_dom().contains(c) ==> 
            old.get_container_owned_pages(c) =~= new.get_container_owned_pages(c)
        // things that changed
        &&
        old.thread_dom().insert(ret.get_return_vaule().unwrap()) =~= new.thread_dom()
}

impl Kernel{

    pub fn syscall_new_thread_with_endpoint(&mut self, thread_ptr:ThreadPtr, endpoint_index: EndpointIdx, pt_regs:Registers) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        ensures
            self.wf(),
            // syscall_new_thread_with_endpoint_requirement(*old(self), thread_ptr, endpoint_index) == false <==> ret.is_error(),
            syscall_new_thread_with_endpoint_spec(*old(self),*self,thread_ptr,endpoint_index, ret),
    {
        let proc_ptr = self.proc_man.get_owning_proc_by_thread_ptr(thread_ptr);
        if self.proc_man.get_proc(proc_ptr).owned_threads.len() >= MAX_NUM_THREADS_PER_PROC{
            return SyscallReturnStruct::NoSwitchNew(ErrorCodeType::Error);
        }
        if self.proc_man.get_container_by_proc_ptr(proc_ptr).mem_quota == 0{
            return SyscallReturnStruct::NoSwitchNew(ErrorCodeType::Error);
        }
        if self.proc_man.get_container_by_proc_ptr(proc_ptr).scheduler.len() >= MAX_CONTAINER_SCHEDULER_LEN {
            return SyscallReturnStruct::NoSwitchNew(ErrorCodeType::Error);
        } 
        if self.page_alloc.free_pages_4k.len() <= 0 {
            return SyscallReturnStruct::NoSwitchNew(ErrorCodeType::Error);
        }

        let endpoint_ptr_op = self.proc_man.get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index);
        if endpoint_ptr_op.is_none(){
            return SyscallReturnStruct::NoSwitchNew(ErrorCodeType::Error);
        }

        let endpoint_ptr = endpoint_ptr_op.unwrap();
        if self.proc_man.get_endpoint(endpoint_ptr).rf_counter == usize::MAX {
            return SyscallReturnStruct::NoSwitchNew(ErrorCodeType::Error);
        }

        let (new_page_ptr, new_page_perm) = self.page_alloc.alloc_page_4k();
        let new_thread_ptr = self.proc_man.new_thread_with_endpoint(thread_ptr, endpoint_index, proc_ptr, pt_regs,new_page_ptr, new_page_perm);

        assert(self.memory_wf()) by {
            assert(self.mem_man.page_closure().disjoint(self.proc_man.page_closure()));
            assert(self.mem_man.page_closure() + self.proc_man.page_closure() == self.page_alloc.allocated_pages_4k());
            assert(self.page_alloc.mapped_pages_2m() =~= Set::empty());
            assert(self.page_alloc.mapped_pages_1g() =~= Set::empty());
            assert(self.page_alloc.allocated_pages_2m() =~= Set::empty());
            assert(self.page_alloc.allocated_pages_1g() =~= Set::empty());
        };
        assert(self.mapping_wf());
        assert(self.pcid_ioid_wf()) by {
            assert(
                forall|p_ptr:ProcPtr|
                #![trigger self.proc_man.get_proc(p_ptr).pcid]
                #![trigger self.proc_man.get_proc(p_ptr).ioid]
                self.proc_man.proc_dom().contains(p_ptr) 
                ==>
                self.mem_man.get_free_pcids_as_set().contains(self.proc_man.get_proc(p_ptr).pcid) == false
                &&
                    self.proc_man.get_proc(p_ptr).ioid.is_Some() 
                    ==> 
                    self.mem_man.get_free_ioids_as_set().contains(self.proc_man.get_proc(p_ptr).ioid.unwrap()) == false
            );
        };
        assert(
            forall|c:ContainerPtr| 
            #![trigger self.get_container_owned_pages(c)]
            self.container_dom().contains(c) ==> 
            old(self).page_alloc.get_container_owned_pages(c) =~= self.page_alloc.get_container_owned_pages(c)
        );
        assert(
            forall|c:ContainerPtr| 
            #![trigger self.get_container_owned_pages(c)]
            self.container_dom().contains(c) ==> 
            old(self).get_container_owned_pages(c) =~= self.get_container_owned_pages(c)
        );
        return SyscallReturnStruct::NoSwitchNew(ErrorCodeType::Success{value: new_thread_ptr});
    }
}

}