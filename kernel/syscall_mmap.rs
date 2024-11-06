use vstd::prelude::*;
verus! {
// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_impl::*;
// use crate::util::page_ptr_util_u::*;
use crate::util::page_ptr_util_u::*;
use crate::define::*;
use crate::trap::*;
use crate::pagetable::pagemap_util_t::*;
use crate::kernel::Kernel;

impl Kernel{

pub fn create_entry(&mut self, proc_ptr:ProcPtr, va:VAddr) -> (ret: (usize, PageMapPtr))
    requires
        old(self).wf(),
        old(self).proc_dom().contains(proc_ptr),
        old(self).get_container_quota(old(self).get_proc(proc_ptr).owning_container) >= 3,
        old(self).get_num_of_free_pages() >= 3,
        va_4k_valid(va),
        old(self).get_address_space(proc_ptr).dom().contains(va) == false,
    ensures
        self.wf(),
        self.get_num_of_free_pages() == old(self).get_num_of_free_pages() - ret.0,
        forall|p_ptr:ProcPtr|
            #![auto]
            self.proc_dom().contains(p_ptr)
            ==>
            self.get_address_space(p_ptr) =~= old(self).get_address_space(p_ptr),
    {
        let mut ret = 0;
        let container_ptr = self.proc_man.get_proc(proc_ptr).owning_container;
        let target_pcid = self.proc_man.get_proc(proc_ptr).pcid;
        proof{va_lemma();}
        let (l4i, l3i, l2i, l1i) = va2index(va);
        let mut l4_entry_op = self.mem_man.get_pagetable_l4_entry(target_pcid, l4i);
        if l4_entry_op.is_none() {
            proof{
                self.page_alloc.free_pages_are_not_mapped();
            }
            let (new_page_ptr, new_page_perm) = self.page_alloc.alloc_page_4k();
            let (page_map_ptr, page_map_perm) = page_perm_to_page_map(new_page_ptr, new_page_perm);
            self.mem_man.create_pagetable_l4_entry(target_pcid, l4i, page_map_ptr, page_map_perm);
            assert(self.wf()) by {
                assert(self.mem_man.wf());
                assert(self.page_alloc.wf());
                assert(self.proc_man.wf());
                assert(self.memory_wf()) by {
                    assert(self.mem_man.page_closure().disjoint(self.proc_man.page_closure()));
                    assert(self.mem_man.page_closure() + self.proc_man.page_closure() == self.page_alloc.allocated_pages_4k());
                    assert(self.page_alloc.mapped_pages_2m() =~= Set::empty());
                    assert(self.page_alloc.mapped_pages_1g() =~= Set::empty());
                    assert(self.page_alloc.allocated_pages_2m() =~= Set::empty());
                    assert(self.page_alloc.allocated_pages_1g() =~= Set::empty());
                    assert(self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom());
                };
                assert(self.mapping_wf());
                assert(self.pcid_ioid_wf());
            };
            ret = ret + 1;
            l4_entry_op = self.mem_man.get_pagetable_l4_entry(target_pcid, l4i);
        }
        assert(l4_entry_op.is_Some());
        let l4_entry = l4_entry_op.unwrap();
        let mut l3_entry_op = self.mem_man.get_pagetable_l3_entry(target_pcid, l4i, l3i, &l4_entry);
        if l3_entry_op.is_none(){
            proof{
                self.page_alloc.free_pages_are_not_mapped();
            }
            let (new_page_ptr, new_page_perm) = self.page_alloc.alloc_page_4k();
            let (page_map_ptr, page_map_perm) = page_perm_to_page_map(new_page_ptr, new_page_perm);
            self.mem_man.create_pagetable_l3_entry(target_pcid, l4i, l3i, l4_entry.addr, page_map_ptr, page_map_perm);
            assert(self.wf()) by {
                assert(self.mem_man.wf());
                assert(self.page_alloc.wf());
                assert(self.proc_man.wf());
                assert(self.memory_wf()) by {
                    assert(self.mem_man.page_closure().disjoint(self.proc_man.page_closure()));
                    assert(self.mem_man.page_closure() + self.proc_man.page_closure() == self.page_alloc.allocated_pages_4k());
                    assert(self.page_alloc.mapped_pages_2m() =~= Set::empty());
                    assert(self.page_alloc.mapped_pages_1g() =~= Set::empty());
                    assert(self.page_alloc.allocated_pages_2m() =~= Set::empty());
                    assert(self.page_alloc.allocated_pages_1g() =~= Set::empty());
                    assert(self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom());
                };
                assert(self.mapping_wf());
                assert(self.pcid_ioid_wf());
            };
            ret = ret + 1;
            l3_entry_op = self.mem_man.get_pagetable_l3_entry(target_pcid, l4i, l3i, &l4_entry);
        }
        let l3_entry = l3_entry_op.unwrap();
        let mut l2_entry_op = self.mem_man.get_pagetable_l2_entry(target_pcid, l4i, l3i, l2i, &l3_entry);

        if l2_entry_op.is_none(){
            proof{
                self.page_alloc.free_pages_are_not_mapped();
            }
            let (new_page_ptr, new_page_perm) = self.page_alloc.alloc_page_4k();
            let (page_map_ptr, page_map_perm) = page_perm_to_page_map(new_page_ptr, new_page_perm);
            self.mem_man.create_pagetable_l2_entry(target_pcid, l4i, l3i, l2i, l3_entry.addr, page_map_ptr, page_map_perm);
            assert(self.wf()) by {
                assert(self.mem_man.wf());
                assert(self.page_alloc.wf());
                assert(self.proc_man.wf());
                assert(self.memory_wf()) by {
                    assert(self.mem_man.page_closure().disjoint(self.proc_man.page_closure()));
                    assert(self.mem_man.page_closure() + self.proc_man.page_closure() == self.page_alloc.allocated_pages_4k());
                    assert(self.page_alloc.mapped_pages_2m() =~= Set::empty());
                    assert(self.page_alloc.mapped_pages_1g() =~= Set::empty());
                    assert(self.page_alloc.allocated_pages_2m() =~= Set::empty());
                    assert(self.page_alloc.allocated_pages_1g() =~= Set::empty());
                    assert(self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom());
                };
                assert(self.mapping_wf());
                assert(self.pcid_ioid_wf());
            };
            ret = ret + 1;
            l2_entry_op = self.mem_man.get_pagetable_l2_entry(target_pcid, l4i, l3i, l2i, &l3_entry);
        }
        (ret, l2_entry_op.unwrap().addr)
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