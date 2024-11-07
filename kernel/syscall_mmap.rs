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
use crate::pagetable::entry::*;
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
        ret.0 <= 3,
        self.wf(),
        self.proc_dom() == old(self).proc_dom(),
        self.thread_dom() == old(self).thread_dom(),
        self.endpoint_dom() == old(self).endpoint_dom(),
        self.container_dom() == old(self).container_dom(),
        self.get_num_of_free_pages() == old(self).get_num_of_free_pages() - ret.0,
        forall|p_ptr:ProcPtr|
            #![auto]
            self.proc_dom().contains(p_ptr)
            ==>
            self.get_address_space(p_ptr) =~= old(self).get_address_space(p_ptr)
            &&
            self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
        forall|t_ptr:ThreadPtr|
            #![auto]
            self.thread_dom().contains(t_ptr)
            ==>
            self.get_thread(t_ptr) =~= old(self).get_thread(t_ptr),
        forall|c_ptr:ContainerPtr|
            #![auto]
            self.container_dom().contains(c_ptr) && c_ptr != self.get_proc(proc_ptr).owning_container
            ==>
            self.get_container(c_ptr) =~= old(self).get_container(c_ptr),
        forall|e_ptr:EndpointPtr|
            #![auto]
            self.endpoint_dom().contains(e_ptr)
            ==>
            self.get_endpoint(e_ptr) =~= old(self).get_endpoint(e_ptr),
        self.get_container(old(self).get_proc(proc_ptr).owning_container).owned_procs =~= self.get_container(old(self).get_proc(proc_ptr).owning_container).owned_procs,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).parent =~= self.get_container(old(self).get_proc(proc_ptr).owning_container).parent,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).parent_rev_ptr =~= self.get_container(old(self).get_proc(proc_ptr).owning_container).parent_rev_ptr,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).children =~= self.get_container(old(self).get_proc(proc_ptr).owning_container).children,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).owned_endpoints =~= self.get_container(old(self).get_proc(proc_ptr).owning_container).owned_endpoints,
        // self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota =~= self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_used =~= self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_used,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).owned_cpus =~= self.get_container(old(self).get_proc(proc_ptr).owning_container).owned_cpus,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).scheduler =~= self.get_container(old(self).get_proc(proc_ptr).owning_container).scheduler,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota as int =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota - ret.0,
        self.mem_man.get_pagetable_by_pcid(self.get_proc(proc_ptr).pcid).unwrap().spec_resolve_mapping_l2(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2).is_Some(),
        self.mem_man.get_pagetable_by_pcid(self.get_proc(proc_ptr).pcid).unwrap().spec_resolve_mapping_l2(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2).unwrap().addr == ret.1,
    {
        let mut ret = 0;
        let container_ptr = self.proc_man.get_proc(proc_ptr).owning_container;
        let old_quota = self.proc_man.get_container(container_ptr).mem_quota;
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
        self.proc_man.set_container_mem_quota(container_ptr, old_quota - ret);

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

        (ret, l2_entry_op.unwrap().addr)
    }


pub fn alloc_and_map(&mut self, target_proc_ptr:ProcPtr, target_va:VAddr, tagret_l1_p:PageMapPtr)
    requires
        old(self).wf(),
        old(self).proc_dom().contains(target_proc_ptr),
        old(self).get_container_quota(old(self).get_proc(target_proc_ptr).owning_container) >= 1,
        old(self).get_num_of_free_pages() >= 1,
        va_4k_valid(target_va),
        old(self).get_address_space(target_proc_ptr).dom().contains(target_va) == false,
        old(self).mem_man.get_pagetable_by_pcid(old(self).get_proc(target_proc_ptr).pcid).unwrap().spec_resolve_mapping_l2(spec_va2index(target_va).0, spec_va2index(target_va).1, spec_va2index(target_va).2).is_Some(),
        old(self).mem_man.get_pagetable_by_pcid(old(self).get_proc(target_proc_ptr).pcid).unwrap().spec_resolve_mapping_l2(spec_va2index(target_va).0, spec_va2index(target_va).1, spec_va2index(target_va).2).unwrap().addr == tagret_l1_p,
    ensures
        self.wf(),
        self.proc_dom() == old(self).proc_dom(),
        self.thread_dom() == old(self).thread_dom(),
        self.endpoint_dom() == old(self).endpoint_dom(),
        self.container_dom() == old(self).container_dom(),
        self.get_num_of_free_pages() == old(self).get_num_of_free_pages() - 1,
        forall|p_ptr:ProcPtr|
            #![auto]
            self.proc_dom().contains(p_ptr) 
            ==> 
            self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
        forall|p_ptr:ProcPtr|
            #![auto]
            self.proc_dom().contains(p_ptr) && p_ptr != target_proc_ptr
            ==> 
            self.get_address_space(p_ptr) =~= old(self).get_address_space(p_ptr),
        forall|t_ptr:ThreadPtr|
            #![auto]
            self.thread_dom().contains(t_ptr)
            ==>
            self.get_thread(t_ptr) =~= old(self).get_thread(t_ptr),
        forall|c_ptr:ContainerPtr|
            #![auto]
            self.container_dom().contains(c_ptr) && c_ptr != self.get_proc(target_proc_ptr).owning_container
            ==>
            self.get_container(c_ptr) =~= old(self).get_container(c_ptr),
        forall|e_ptr:EndpointPtr|
            #![auto]
            self.endpoint_dom().contains(e_ptr)
            ==>
            self.get_endpoint(e_ptr) =~= old(self).get_endpoint(e_ptr),
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs =~= self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs,
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent =~= self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent,
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent_rev_ptr =~= self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent_rev_ptr,
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).children =~= self.get_container(old(self).get_proc(target_proc_ptr).owning_container).children,
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints =~= self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints,
        // self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota =~= self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota,
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used =~= self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used,
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_cpus =~= self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_cpus,
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).scheduler =~= self.get_container(old(self).get_proc(target_proc_ptr).owning_container).scheduler,
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_quota as int =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_quota - 1,
{
    proof{
        self.proc_man.pcid_unique(target_proc_ptr);
    }
    let target_container_ptr = self.proc_man.get_proc(target_proc_ptr).owning_container;
    let old_quota = self.proc_man.get_container(target_container_ptr).mem_quota;
    let target_pcid = self.proc_man.get_proc(target_proc_ptr).pcid;
    proof{va_lemma();}
    let (l4i, l3i, l2i, l1i) = va2index(target_va);
    let new_page_ptr = self.page_alloc.alloc_and_map_4k(target_pcid, target_va, target_container_ptr);
    self.mem_man.pagetable_map_4k_page(target_pcid, l4i, l3i, l2i, l1i, tagret_l1_p, &MapEntry{addr:new_page_ptr, write:true, execute_disable:false});
    self.proc_man.set_container_mem_quota(target_container_ptr, old_quota - 1);
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
        assert(self.mapping_wf()) by {
        };
        assert(self.pcid_ioid_wf());
    };
}

pub fn create_entry_and_alloc_and_map(&mut self, target_proc_ptr:ProcPtr, target_va:VAddr) -> (ret: usize)
    requires
        old(self).wf(),
        old(self).proc_dom().contains(target_proc_ptr),
        old(self).get_container_quota(old(self).get_proc(target_proc_ptr).owning_container) >= 4,
        old(self).get_num_of_free_pages() >= 4,
        va_4k_valid(target_va),
        old(self).get_address_space(target_proc_ptr).dom().contains(target_va) == false,
    ensures
        ret <= 4,
        self.wf(),
        self.proc_dom() == old(self).proc_dom(),
        self.thread_dom() == old(self).thread_dom(),
        self.endpoint_dom() == old(self).endpoint_dom(),
        self.container_dom() == old(self).container_dom(),
        self.get_num_of_free_pages() == old(self).get_num_of_free_pages() - ret,
        forall|p_ptr:ProcPtr|
            #![auto]
            self.proc_dom().contains(p_ptr) 
            ==> 
            self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
        forall|p_ptr:ProcPtr|
            #![auto]
            self.proc_dom().contains(p_ptr) && p_ptr != target_proc_ptr
            ==> 
            self.get_address_space(p_ptr) =~= old(self).get_address_space(p_ptr),
        forall|t_ptr:ThreadPtr|
            #![auto]
            self.thread_dom().contains(t_ptr)
            ==>
            self.get_thread(t_ptr) =~= old(self).get_thread(t_ptr),
        forall|c_ptr:ContainerPtr|
            #![auto]
            self.container_dom().contains(c_ptr) && c_ptr != self.get_proc(target_proc_ptr).owning_container
            ==>
            self.get_container(c_ptr) =~= old(self).get_container(c_ptr),
        forall|e_ptr:EndpointPtr|
            #![auto]
            self.endpoint_dom().contains(e_ptr)
            ==>
            self.get_endpoint(e_ptr) =~= old(self).get_endpoint(e_ptr),
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs =~= self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs,
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent =~= self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent,
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent_rev_ptr =~= self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent_rev_ptr,
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).children =~= self.get_container(old(self).get_proc(target_proc_ptr).owning_container).children,
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints =~= self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints,
        // self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota =~= self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota,
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used =~= self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used,
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_cpus =~= self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_cpus,
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).scheduler =~= self.get_container(old(self).get_proc(target_proc_ptr).owning_container).scheduler,
        self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_quota as int =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_quota - ret,
{
    let (ret, new_entry) = self.create_entry(target_proc_ptr, target_va);
    self.alloc_and_map(target_proc_ptr, target_va, new_entry);
    ret + 1
}

// pub fn syscall_mmap(&mut self, thread_ptr: ThreadPtr, va_start:VAddr, len: usize) ->  (ret: SyscallReturnStruct)
//     requires
//         old(self).wf(),
//         old(self).thread_dom().contains(thread_ptr),
//         0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
//     {

//     }

}
}