use vstd::prelude::*;
verus! {
// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_impl::*;
// use crate::util::page_ptr_util_u::*;
use crate::define::*;
use crate::trap::*;
use crate::kernel::Kernel;

pub open spec fn syscall_new_thread_requirement(old:Kernel, thread_id: ThreadPtr) -> bool {
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
                    true
                }
            }
        }
    }
}

pub open spec fn syscall_new_thread_spec(old:Kernel, new:Kernel, thread_id: ThreadPtr) -> bool{
    &&&
    syscall_new_thread_requirement(old, thread_id) == false ==> new =~= old
    &&&
    syscall_new_thread_requirement(old, thread_id) == true ==>
        old.proc_dom() =~= new.proc_dom()
        &&
        old.container_dom() =~= new.container_dom()
        &&
        old.endpoint_dom() =~= new.endpoint_dom()
        &&
        forall|proc_ptr:ProcPtr| 
            #![trigger new.get_address_space(proc_ptr)]
            new.proc_dom().contains(proc_ptr)
            ==>
            new.get_address_space(proc_ptr) =~= old.get_address_space(proc_ptr)
        &&
        forall|c:ContainerPtr| 
            #![trigger new.get_container_owned_pages(c)]
            new.container_dom().contains(c) ==> 
            old.get_container_owned_pages(c) =~= new.get_container_owned_pages(c)
}

impl Kernel{

    pub fn syscall_new_thread(&mut self, thread_ptr:ThreadPtr, pt_regs:Registers) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
        ensures
            self.wf(),
            syscall_new_thread_requirement(*old(self), thread_ptr) == false <==> ret.is_error(),
            // syscall_new_thread_spec(*old(self),*self,cpu_id,pt_regs),
    {
        let proc_ptr = self.proc_man.get_owning_proc_by_thread_ptr(thread_ptr);
        if self.proc_man.get_proc(proc_ptr).owned_threads.len() >= MAX_NUM_THREADS_PER_PROC{
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_container_by_proc_ptr(proc_ptr).mem_quota == 0{
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_container_by_proc_ptr(proc_ptr).scheduler.len() >= MAX_CONTAINER_SCHEDULER_LEN {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        } 
        if self.page_alloc.free_pages_4k.len() <= 0 {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        assert((self.get_num_of_free_pages() <= 0) == false);
        let (new_page_ptr, new_page_perm) = self.page_alloc.alloc_page_4k();
        let new_thread_ptr = self.proc_man.new_thread(proc_ptr, pt_regs,new_page_ptr, new_page_perm);

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
                forall|proc_ptr:ProcPtr|
                #![trigger self.proc_man.get_proc(proc_ptr).pcid]
                #![trigger self.proc_man.get_proc(proc_ptr).ioid]
                self.proc_man.proc_dom().contains(proc_ptr) 
                ==>
                self.mem_man.get_free_pcids_as_set().contains(self.proc_man.get_proc(proc_ptr).pcid) == false
                &&
                    self.proc_man.get_proc(proc_ptr).ioid.is_Some() 
                    ==> 
                    self.mem_man.get_free_ioids_as_set().contains(self.proc_man.get_proc(proc_ptr).ioid.unwrap()) == false
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
        return SyscallReturnStruct::NoSwitchNew(RetValueType::SuccessUsize{value: new_thread_ptr});
    }
}

}