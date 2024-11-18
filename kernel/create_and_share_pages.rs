use vstd::prelude::*;
verus! {
// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_impl::*;
// use crate::util::page_ptr_util_u::*;
// use crate::lemma::lemma_t::set_lemma;
// use crate::lemma::lemma_u::*;
use crate::util::page_ptr_util_u::*;
use crate::define::*;
// use crate::trap::*;
// use crate::pagetable::pagemap_util_t::*;
use crate::pagetable::entry::*;
use crate::kernel::Kernel;
use crate::va_range::VaRange4K;


impl Kernel{
    pub open spec fn address_space_range_exists(&self, target_proc_ptr:ProcPtr, va_range:&VaRange4K) -> bool{
        forall|j:int| #![auto] 0<=j<va_range.len ==> self.get_address_space(target_proc_ptr).dom().contains(va_range@[j])
    }
    
    pub open spec fn address_space_range_shareable(&self, target_proc_ptr:ProcPtr, va_range:&VaRange4K) -> bool{
        &&&
        forall|j:int| #![auto] 0<=j<va_range.len ==> self.get_address_space(target_proc_ptr).dom().contains(va_range@[j])
        &&&
        forall|j:int| #![auto] 0<=j<va_range.len ==> self.get_physical_page_reference_counter(self.get_address_space(target_proc_ptr)[va_range@[j]].addr) <= usize::MAX - va_range.len
    }
    
    pub fn check_address_space_va_range_shareable(&self, target_proc_ptr:ProcPtr, va_range:&VaRange4K) -> (ret:bool)
        requires
            self.wf(),
            self.proc_dom().contains(target_proc_ptr),
            va_range.wf(),
        ensures
            ret == self.address_space_range_shareable(target_proc_ptr, va_range),
    {
        let target_pcid = self.proc_man.get_proc(target_proc_ptr).pcid;
        for i in 0..va_range.len
            invariant
                self.mem_man.pcid_active(target_pcid),
                target_pcid == self.get_proc(target_proc_ptr).pcid,
                0<=i<=va_range.len,
                self.wf(),
                self.proc_dom().contains(target_proc_ptr),
                va_range.wf(),    
                forall|j:int| #![auto] 0<=j<i ==> self.get_address_space(target_proc_ptr).dom().contains(va_range@[j]),
                forall|j:int| #![auto] 0<=j<i ==> self.get_physical_page_reference_counter(self.get_address_space(target_proc_ptr)[va_range@[j]].addr) <= usize::MAX - va_range.len,
        {
            let entry_op = self.mem_man.resolve_pagetable_mapping(target_pcid, va_range.index(i)); 
            if entry_op.is_none() {
                return false;
            }
            assert(self.mem_man.get_pagetable_mapping_by_pcid(target_pcid).dom().contains(va_range@[i as int]));
            let entry = entry_op.unwrap();
            if self.page_alloc.get_page_reference_counter(entry.addr) > usize::MAX - va_range.len {
                return false;
            }
        }
        return true;
    }
    
    
    pub fn share_mapping(&mut self, target_proc_ptr:ProcPtr, target_va:VAddr, tagret_l1_p:PageMapPtr, entry:MapEntry)
        requires
            old(self).wf(),
            old(self).proc_dom().contains(target_proc_ptr),
            va_4k_valid(target_va),
            old(self).page_alloc.page_is_mapped(entry.addr),
            page_ptr_valid(entry.addr),
            old(self).get_address_space(target_proc_ptr).dom().contains(target_va) == false,
            old(self).mem_man.get_pagetable_by_pcid(old(self).get_proc(target_proc_ptr).pcid).unwrap().spec_resolve_mapping_l2(spec_va2index(target_va).0, spec_va2index(target_va).1, spec_va2index(target_va).2).is_Some(),
            old(self).mem_man.get_pagetable_by_pcid(old(self).get_proc(target_proc_ptr).pcid).unwrap().spec_resolve_mapping_l2(spec_va2index(target_va).0, spec_va2index(target_va).1, spec_va2index(target_va).2).unwrap().addr == tagret_l1_p,
            old(self).get_physical_page_reference_counter(entry.addr) <= usize::MAX - 1,
        ensures
            self.wf(),
            self.proc_dom() == old(self).proc_dom(),
            self.thread_dom() == old(self).thread_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.get_num_of_free_pages() == old(self).get_num_of_free_pages(),
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
                self.container_dom().contains(c_ptr)
                ==>
                self.get_container(c_ptr) =~= old(self).get_container(c_ptr)
                &&
                self.get_container_owned_pages(c_ptr) =~= old(self).get_container_owned_pages(c_ptr),
            forall|e_ptr:EndpointPtr|
                #![auto]
                self.endpoint_dom().contains(e_ptr)
                ==>
                self.get_endpoint(e_ptr) =~= old(self).get_endpoint(e_ptr),
            forall|p:Pcid|
                #![trigger self.mem_man.pcid_active(p)]
                #![trigger self.mem_man.pcid_to_proc_ptr(p)]
                self.mem_man.pcid_active(p)
                ==>
                old(self).mem_man.pcid_to_proc_ptr(p) == self.mem_man.pcid_to_proc_ptr(p),
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).parent,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent_rev_ptr =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).parent_rev_ptr,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).children =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).children,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_threads =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_threads,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_quota =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_quota,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_cpus =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_cpus,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).scheduler =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).scheduler,
            self.get_address_space(target_proc_ptr) =~= old(self).get_address_space(target_proc_ptr).insert(target_va,entry),
            forall|p:PagePtr|
                #![trigger self.page_alloc.page_is_mapped(p)] 
                self.page_alloc.page_is_mapped(p) == old(self).page_alloc.page_is_mapped(p),
            forall|p:PagePtr|
                #![trigger self.page_alloc.page_is_mapped(p)] 
                self.page_alloc.page_is_mapped(p) && p != entry.addr
                ==> 
                old(self).get_physical_page_reference_counter(p) == self.get_physical_page_reference_counter(p),
            old(self).get_physical_page_reference_counter(entry.addr) + 1 == self.get_physical_page_reference_counter(entry.addr),
            self.page_mapping@.dom() == old(self).page_mapping@.dom(),
            forall|page_ptr:PagePtr|
                #![trigger self.page_mapping@[page_ptr]]
                old(self).page_mapping@.dom().contains(page_ptr) && page_ptr != entry.addr
                ==> 
                old(self).page_mapping@[page_ptr] == self.page_mapping@[page_ptr],
            self.page_mapping@[entry.addr] == old(self).page_mapping@[entry.addr].insert((target_proc_ptr, target_va)),
        {
        proof{
            self.proc_man.pcid_unique(target_proc_ptr);
        }
        let target_container_ptr = self.proc_man.get_proc(target_proc_ptr).owning_container;
        let target_pcid = self.proc_man.get_proc(target_proc_ptr).pcid;
        proof{
            va_lemma();
            assert(self.page_alloc.mapped_pages_2m().contains(entry.addr) == false);
            assert(self.page_alloc.mapped_pages_1g().contains(entry.addr) == false);
            assert(self.page_alloc.mapped_pages_4k().contains(entry.addr));
            self.page_alloc.mapped_page_are_not_allocated(entry.addr);
        }
        let (l4i, l3i, l2i, l1i) = va2index(target_va);
        self.page_alloc.add_mapping_4k(entry.addr, target_pcid, target_va);
        self.mem_man.pagetable_map_4k_page(target_pcid, l4i, l3i, l2i, l1i, tagret_l1_p, &entry);
        proof{
            self.page_mapping@ = self.page_mapping@.insert(entry.addr, self.page_mapping@[entry.addr].insert((target_proc_ptr, target_va)));
        }
        assert(self.wf()) by {
            assert(self.mem_man.wf());
            assert(self.page_alloc.wf());
            assert(self.proc_man.wf());
            assert(self.memory_wf());
            assert(self.mapping_wf()) by {
            };
            assert(self.pcid_ioid_wf());
            assert(self.page_mapping_wf()) by {
                assert(self.page_mapping@.dom() == self.page_alloc.mapped_pages_4k());
                assert(forall|page_ptr:PagePtr, p_ptr: ProcPtr, va:VAddr|
                    #![trigger self.page_mapping@[page_ptr].contains((p_ptr, va))]
                    #![trigger self.page_alloc.page_mappings(page_ptr).contains((self.proc_man.get_proc(p_ptr).pcid, va))]
                    self.page_mapping@.dom().contains(page_ptr) && self.page_mapping@[page_ptr].contains((p_ptr, va))
                    ==>
                    self.page_alloc.page_is_mapped(page_ptr)
                    &&
                    self.proc_man.proc_dom().contains(p_ptr)
                    &&
                    self.page_alloc.page_mappings(page_ptr).contains((self.proc_man.get_proc(p_ptr).pcid, va)));
                assert(forall|page_ptr:PagePtr, pcid: Pcid, va:VAddr|
                    #![trigger self.page_alloc.page_mappings(page_ptr).contains((pcid, va))]
                    #![trigger self.page_mapping@[page_ptr].contains((self.mem_man.pcid_to_proc_ptr(pcid), va))]
                    self.page_alloc.page_is_mapped(page_ptr) && self.page_alloc.page_mappings(page_ptr).contains((pcid, va))
                    ==>
                    self.page_mapping@.dom().contains(page_ptr) && self.page_mapping@[page_ptr].contains((self.mem_man.pcid_to_proc_ptr(pcid), va)));
            };
        };
        }


    //we forbid share with the same vaddr
    pub fn create_entry_and_share(&mut self, src_proc_ptr:ProcPtr,src_va:VAddr, target_proc_ptr:ProcPtr, target_va:VAddr) -> (ret: usize)
        requires
            old(self).wf(),
            old(self).proc_dom().contains(src_proc_ptr),
            old(self).proc_dom().contains(target_proc_ptr),
            old(self).get_container_quota(old(self).get_proc(target_proc_ptr).owning_container) >= 3,
            old(self).get_num_of_free_pages() >= 3,
            va_4k_valid(src_va),
            va_4k_valid(target_va),
            old(self).get_address_space(target_proc_ptr).dom().contains(target_va) == false,
            old(self).get_address_space(src_proc_ptr).dom().contains(src_va) == true,
            old(self).get_physical_page_reference_counter(old(self).get_address_space(src_proc_ptr)[src_va].addr) <= usize::MAX - 1,
        ensures
            ret <= 3,
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
            forall|c:ContainerPtr|
                #![auto]
                self.container_dom().contains(c)
                ==>
                self.get_container_owned_pages(c) =~= old(self).get_container_owned_pages(c),
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).parent,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent_rev_ptr =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).parent_rev_ptr,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).children =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).children,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_threads =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_threads,
            // self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_cpus =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_cpus,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).scheduler =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).scheduler,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_quota as int =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_quota - ret,
            self.get_address_space(target_proc_ptr).dom() =~= old(self).get_address_space(target_proc_ptr).dom().insert(target_va),
            self.get_address_space(target_proc_ptr) =~= old(self).get_address_space(target_proc_ptr).insert(target_va, old(self).get_address_space(src_proc_ptr)[src_va]),
            forall|va:VAddr|
                #![auto] 
                va != target_va && old(self).get_address_space(target_proc_ptr).dom().contains(va)
                ==>
                self.get_address_space(target_proc_ptr)[va] == old(self).get_address_space(target_proc_ptr)[va],
            forall|p:PagePtr|
                #![trigger self.page_alloc.page_is_mapped(p)] 
                self.page_alloc.page_is_mapped(p) == old(self).page_alloc.page_is_mapped(p),
            self.page_mapping@.dom() == old(self).page_mapping@.dom(),
            forall|page_ptr:PagePtr|
                #![trigger self.page_mapping@[page_ptr]]
                old(self).page_mapping@.dom().contains(page_ptr) && page_ptr != old(self).get_address_space(src_proc_ptr)[src_va].addr
                ==> 
                old(self).page_mapping@[page_ptr] == self.page_mapping@[page_ptr],
            self.page_mapping@[old(self).get_address_space(src_proc_ptr)[src_va].addr] == old(self).page_mapping@[old(self).get_address_space(src_proc_ptr)[src_va].addr].insert((target_proc_ptr, target_va)),
            forall|p:PagePtr|
                #![trigger self.page_alloc.page_is_mapped(p)] 
                self.page_alloc.page_is_mapped(p) && p != old(self).get_address_space(src_proc_ptr)[src_va].addr
                ==> 
                old(self).get_physical_page_reference_counter(p) == self.get_physical_page_reference_counter(p),
            old(self).get_physical_page_reference_counter(old(self).get_address_space(src_proc_ptr)[src_va].addr) + 1 == self.get_physical_page_reference_counter(old(self).get_address_space(src_proc_ptr)[src_va].addr),
    {
        assert(src_proc_ptr != target_proc_ptr || src_va != target_va);
        let src_pcid = self.proc_man.get_proc(src_proc_ptr).pcid;
        let src_entry = page_entry_to_map_entry(&self.mem_man.resolve_pagetable_mapping(src_pcid, src_va).unwrap());
        proof{
            self.page_alloc.mapped_page_imply_page_ptr_valid(src_entry.addr);
        }
        let (ret, new_entry) = self.create_entry(target_proc_ptr, target_va);
        self.share_mapping(target_proc_ptr, target_va, new_entry, src_entry);
        ret
    }

    pub fn range_create_and_share_mapping(&mut self, src_proc_ptr: ProcPtr, src_va_range:&VaRange4K, target_proc_ptr:ProcPtr, target_va_range:&VaRange4K) -> (ret:usize)
        requires
            old(self).wf(),
            old(self).proc_dom().contains(src_proc_ptr),
            old(self).proc_dom().contains(target_proc_ptr),
            src_va_range.wf(),
            target_va_range.wf(),
            src_va_range.len == target_va_range.len,
            old(self).get_container_quota(old(self).get_proc(target_proc_ptr).owning_container) >= 3 * src_va_range.len,
            old(self).get_num_of_free_pages() >= 3 * src_va_range.len,
            old(self).address_space_range_shareable(src_proc_ptr, src_va_range),
            old(self).address_space_range_free(target_proc_ptr, target_va_range),
            src_proc_ptr != target_proc_ptr, // just to make specs easier...
        ensures
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
            forall|c:ContainerPtr|
                #![auto]
                self.container_dom().contains(c)
                ==>
                self.get_container_owned_pages(c) =~= old(self).get_container_owned_pages(c),
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).parent,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent_rev_ptr =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).parent_rev_ptr,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).children =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).children,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_threads =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_threads,
            // self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_cpus =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_cpus,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).scheduler =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).scheduler,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_quota as int =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_quota - ret,
            forall|p:PagePtr|
                #![trigger self.page_alloc.page_is_mapped(p)] 
                self.page_alloc.page_is_mapped(p) == old(self).page_alloc.page_is_mapped(p),
            self.page_mapping@.dom() == old(self).page_mapping@.dom(),
            forall|va:VAddr|
                #![auto]
                old(self).get_address_space(target_proc_ptr).dom().contains(va) 
                ==>
                self.get_address_space(target_proc_ptr).dom().contains(va) 
                &&
                self.get_address_space(target_proc_ptr)[va] =~= old(self).get_address_space(target_proc_ptr)[va],
            forall|i:int|
                #![auto]
                0 <= i < src_va_range.len 
                ==>
                self.get_address_space(target_proc_ptr).dom().contains(target_va_range@[i])
                &&
                self.get_address_space(target_proc_ptr)[target_va_range@[i]] == self.get_address_space(src_proc_ptr)[src_va_range@[i]],

            forall|page_ptr:PagePtr|
                #![trigger self.page_mapping@[page_ptr]]
                old(self).page_mapping@.dom().contains(page_ptr) && (forall|i:int|#![auto] 0 <= i < src_va_range.len  ==> old(self).get_address_space(src_proc_ptr)[src_va_range@[i]].addr != page_ptr)
                ==> 
                old(self).page_mapping@[page_ptr] == self.page_mapping@[page_ptr],

            // forall|page_ptr:PagePtr|
            //     #![trigger self.page_mapping@[page_ptr]]
            //     old(self).page_mapping@.dom().contains(page_ptr) && (forall|i:int|#![auto] 0 <= i < src_va_range.len  ==> old(self).get_address_space(src_proc_ptr)[src_va_range@[i]].addr == page_ptr)
            //     ==> 
            //     (
            //         forall|p_ptr:Pcid,va:VAddr|
            //             #![auto]
            //             self.page_mapping@[page_ptr].contains((p_ptr,va)) && !old(self).page_mapping@[page_ptr].contains((p_ptr,va))
            //             ==>
            //             p_ptr == target_proc_ptr
            //             &&
            //             target_va_range@.contains(va)
            //     ),
            forall|page_ptr:PagePtr|
                #![trigger self.page_mapping@[page_ptr]]
                old(self).page_mapping@.dom().contains(page_ptr) && self.page_mapping@[page_ptr] != old(self).page_mapping@[page_ptr]
                ==> 
                (
                    forall|p_ptr:Pcid,va:VAddr|
                        #![auto]
                        self.page_mapping@[page_ptr].contains((p_ptr,va)) && !old(self).page_mapping@[page_ptr].contains((p_ptr,va))
                        ==>
                        p_ptr == target_proc_ptr
                        &&
                        target_va_range@.contains(va)
                ),
            forall|va:VAddr|
                #![auto]
                target_va_range@.contains(va) == false
                ==>
                self.get_address_space(target_proc_ptr).dom().contains(va) == old(self).get_address_space(target_proc_ptr).dom().contains(va),
            forall|va:VAddr|
                #![auto]
                target_va_range@.contains(va) == false && old(self).get_address_space(target_proc_ptr).dom().contains(va)
                ==>
                self.get_address_space(target_proc_ptr)[va] == old(self).get_address_space(target_proc_ptr)[va]
    {
        let mut ret = 0;
        for index in 0..src_va_range.len    
            invariant
                self.wf(),
                self.proc_dom().contains(src_proc_ptr),
                self.proc_dom().contains(target_proc_ptr),
                src_va_range.wf(),
                target_va_range.wf(),
                src_va_range.len == target_va_range.len,
                self.get_container_quota(self.get_proc(target_proc_ptr).owning_container) >= 3 * (src_va_range.len - index),
                self.get_num_of_free_pages() >= 3 * (src_va_range.len - index),
                forall|j:int| #![auto] 0<=j<src_va_range.len ==> self.get_address_space(src_proc_ptr).dom().contains(src_va_range@[j]),
                forall|j:int| #![auto] 0<=j<src_va_range.len ==> self.get_physical_page_reference_counter(self.get_address_space(src_proc_ptr)[src_va_range@[j]].addr) <= usize::MAX - (src_va_range.len - index),
                forall|j:int| #![auto] index<=j<src_va_range.len ==> self.get_address_space(target_proc_ptr).dom().contains(target_va_range@[j]) == false,
                src_proc_ptr != target_proc_ptr,
                
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
                forall|c:ContainerPtr|
                    #![auto]
                    self.container_dom().contains(c)
                    ==>
                    self.get_container_owned_pages(c) =~= old(self).get_container_owned_pages(c),
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs,
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).parent,
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent_rev_ptr =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).parent_rev_ptr,
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).children =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).children,
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints,
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_threads =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_threads,
                // self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota,
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used,
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_cpus =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_cpus,
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).scheduler =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).scheduler,
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_quota as int =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_quota - ret,
                forall|p:PagePtr|
                    #![trigger self.page_alloc.page_is_mapped(p)] 
                    self.page_alloc.page_is_mapped(p) == old(self).page_alloc.page_is_mapped(p),
                self.page_mapping@.dom() == old(self).page_mapping@.dom(),
                forall|va:VAddr|
                    #![auto]
                    old(self).get_address_space(target_proc_ptr).dom().contains(va) 
                    ==>
                    self.get_address_space(target_proc_ptr).dom().contains(va) 
                    &&
                    self.get_address_space(target_proc_ptr)[va] =~= old(self).get_address_space(target_proc_ptr)[va],
                forall|va:VAddr|
                    #![auto]
                    target_va_range@.contains(va) == false && old(self).get_address_space(target_proc_ptr).dom().contains(va)
                    ==>
                    self.get_address_space(target_proc_ptr)[va] == old(self).get_address_space(target_proc_ptr)[va],
                forall|i:int|
                    #![auto]
                    0 <= i < index 
                    ==>
                    self.get_address_space(target_proc_ptr).dom().contains(target_va_range@[i])
                    &&
                    self.get_address_space(target_proc_ptr)[target_va_range@[i]] == self.get_address_space(src_proc_ptr)[src_va_range@[i]],

                forall|page_ptr:PagePtr|
                    #![trigger self.page_mapping@[page_ptr]]
                    old(self).page_mapping@.dom().contains(page_ptr) && (forall|i:int|#![auto] 0 <= i < index ==> old(self).get_address_space(src_proc_ptr)[src_va_range@[i]].addr != page_ptr)
                    ==> 
                    old(self).page_mapping@[page_ptr] == self.page_mapping@[page_ptr],

                forall|page_ptr:PagePtr|
                    #![trigger self.page_mapping@[page_ptr]]
                    old(self).page_mapping@.dom().contains(page_ptr) && (exists|i:int|#![auto] 0 <= i < index && old(self).get_address_space(src_proc_ptr)[src_va_range@[i]].addr == page_ptr)
                    ==> 
                    (
                        forall|p_ptr:Pcid,va:VAddr|
                            #![auto]
                            self.page_mapping@[page_ptr].contains((p_ptr,va)) && !old(self).page_mapping@[page_ptr].contains((p_ptr,va))
                            ==>
                            p_ptr == target_proc_ptr
                            &&
                            target_va_range@.contains(va)
                    )
        {
            ret = ret + self.create_entry_and_share(src_proc_ptr, src_va_range.index(index), target_proc_ptr, target_va_range.index(index));
            assert(self.wf());
        }
        ret
    }

}
}