use vstd::prelude::*;
verus!{
use vstd::simple_pptr::*;

use crate::pagetable::pagetable_spec_impl::*;
use crate::array::Array;
use crate::define::*;
use crate::pagetable::pagemap::*;
use crate::util::page_ptr_util_u::*;

impl Array<Option<PageTable>,PCID_MAX>{

    #[verifier(external_body)]
    pub fn pagetable_array_create_pagetable_l4_entry_t(&mut self, pcid:Pcid, target_l4i: L4Index, page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<PageMap>>)
        requires
            old(self).wf(),
            old(self)@[pcid as int].unwrap().wf(),
            KERNEL_MEM_END_L4INDEX <= target_l4i < 512,
            old(self)@[pcid as int].unwrap().spec_resolve_mapping_l4(target_l4i).is_None(),
            page_ptr_valid(page_map_ptr),
            old(self)@[pcid as int].unwrap().page_closure().contains(page_map_ptr) == false,
            old(self)@[pcid as int].unwrap().page_not_mapped(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i:usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0<=i<512 ==> page_map_perm.value()[i].is_empty(),
        ensures
            self.wf(),
            forall|p:Pcid| 
                #![trigger self@[p as int]]
                #![trigger old(self)@[p as int]]
                0 <= p < PCID_MAX && p != pcid
                ==> 
                self@[p as int] =~= old(self)@[p as int],
            self@[pcid as int].is_Some(),
            self@[pcid as int].unwrap().wf(),
            self@[pcid as int].unwrap().pcid == old(self)@[pcid as int].unwrap().pcid, 
            self@[pcid as int].unwrap().kernel_l4_end == old(self)@[pcid as int].unwrap().kernel_l4_end,  
            self@[pcid as int].unwrap().page_closure() =~= old(self)@[pcid as int].unwrap().page_closure().insert(page_map_ptr),
            self@[pcid as int].unwrap().mapping_4k() =~= old(self)@[pcid as int].unwrap().mapping_4k(),
            self@[pcid as int].unwrap().mapping_2m() =~= old(self)@[pcid as int].unwrap().mapping_2m(),
            self@[pcid as int].unwrap().mapping_1g() =~= old(self)@[pcid as int].unwrap().mapping_1g(),
            self@[pcid as int].unwrap().mapped_4k_pages() =~= old(self)@[pcid as int].unwrap().mapped_4k_pages(),
            self@[pcid as int].unwrap().mapped_2m_pages() =~= old(self)@[pcid as int].unwrap().mapped_2m_pages(),
            self@[pcid as int].unwrap().mapped_1g_pages() =~= old(self)@[pcid as int].unwrap().mapped_1g_pages(),
            self@[pcid as int].unwrap().spec_resolve_mapping_l4(target_l4i).is_Some(),
            self@[pcid as int].unwrap().spec_resolve_mapping_l4(target_l4i).get_Some_0().addr == page_map_ptr,
            self@[pcid as int].unwrap().kernel_entries =~= old(self)@[pcid as int].unwrap().kernel_entries,
    {
        self.ar[pcid].as_mut().unwrap().create_entry_l4(target_l4i, page_map_ptr, Tracked(page_map_perm));
    }

    #[verifier(external_body)]
    pub fn pagetable_array_create_pagetable_l3_entry_t(&mut self, pcid:Pcid, target_l4i: L4Index, target_l3i: L3Index, target_l3_p:PageMapPtr, page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<PageMap>>)
        requires
            old(self).wf(),
            old(self)@[pcid as int].unwrap().wf(),
            KERNEL_MEM_END_L4INDEX <= target_l4i < 512,
            0 <= target_l3i < 512,
            old(self)@[pcid as int].unwrap().spec_resolve_mapping_l4(target_l4i).is_Some(),
            old(self)@[pcid as int].unwrap().spec_resolve_mapping_l4(target_l4i).unwrap().addr == target_l3_p,
            page_ptr_valid(page_map_ptr),
            old(self)@[pcid as int].unwrap().page_closure().contains(page_map_ptr) == false,
            old(self)@[pcid as int].unwrap().page_not_mapped(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i:usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0<=i<512 ==> page_map_perm.value()[i].is_empty(),
        ensures
            self.wf(),
            forall|p:Pcid| 
                #![trigger self@[p as int]]
                #![trigger old(self)@[p as int]]
                0 <= p < PCID_MAX && p != pcid
                ==> 
                self@[p as int] =~= old(self)@[p as int],
            self@[pcid as int].is_Some(),
            self@[pcid as int].unwrap().wf(),
            self@[pcid as int].unwrap().pcid == old(self)@[pcid as int].unwrap().pcid, 
            self@[pcid as int].unwrap().kernel_l4_end == old(self)@[pcid as int].unwrap().kernel_l4_end,  
            self@[pcid as int].unwrap().page_closure() =~= old(self)@[pcid as int].unwrap().page_closure().insert(page_map_ptr),
            self@[pcid as int].unwrap().mapping_4k() =~= old(self)@[pcid as int].unwrap().mapping_4k(),
            self@[pcid as int].unwrap().mapping_2m() =~= old(self)@[pcid as int].unwrap().mapping_2m(),
            self@[pcid as int].unwrap().mapping_1g() =~= old(self)@[pcid as int].unwrap().mapping_1g(),
            self@[pcid as int].unwrap().mapped_4k_pages() =~= old(self)@[pcid as int].unwrap().mapped_4k_pages(),
            self@[pcid as int].unwrap().mapped_2m_pages() =~= old(self)@[pcid as int].unwrap().mapped_2m_pages(),
            self@[pcid as int].unwrap().mapped_1g_pages() =~= old(self)@[pcid as int].unwrap().mapped_1g_pages(),
            self@[pcid as int].unwrap().spec_resolve_mapping_l4(target_l4i) == old(self)@[pcid as int].unwrap().spec_resolve_mapping_l4(target_l4i),
            self@[pcid as int].unwrap().spec_resolve_mapping_l3(target_l4i,target_l3i).is_Some(),
            self@[pcid as int].unwrap().spec_resolve_mapping_l3(target_l4i,target_l3i).get_Some_0().addr == page_map_ptr,
            self@[pcid as int].unwrap().spec_resolve_mapping_1g_l3(target_l4i,target_l3i).is_None(),
            self@[pcid as int].unwrap().kernel_entries =~= old(self)@[pcid as int].unwrap().kernel_entries,
    {
        self.ar[pcid].as_mut().unwrap().create_entry_l3(target_l4i, target_l3i, target_l3_p, page_map_ptr, Tracked(page_map_perm));
    }

    #[verifier(external_body)]
    pub fn pagetable_array_create_pagetable_l2_entry_t(&mut self, pcid:Pcid, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p:PageMapPtr, page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<PageMap>>)
        requires
            old(self).wf(),
            old(self)@[pcid as int].unwrap().wf(),
            KERNEL_MEM_END_L4INDEX <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            old(self)@[pcid as int].unwrap().spec_resolve_mapping_l3(target_l4i, target_l3i).is_Some(),
            old(self)@[pcid as int].unwrap().spec_resolve_mapping_1g_l3(target_l4i, target_l3i).is_None(),
            old(self)@[pcid as int].unwrap().spec_resolve_mapping_l3(target_l4i, target_l3i).unwrap().addr == target_l2_p,
            page_ptr_valid(page_map_ptr),
            old(self)@[pcid as int].unwrap().page_closure().contains(page_map_ptr) == false,
            old(self)@[pcid as int].unwrap().page_not_mapped(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i:usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0<=i<512 ==> page_map_perm.value()[i].is_empty(),
        ensures
            self.wf(),
            forall|p:Pcid| 
                #![trigger self@[p as int]]
                #![trigger old(self)@[p as int]]
                0 <= p < PCID_MAX && p != pcid
                ==> 
                self@[p as int] =~= old(self)@[p as int],
            self@[pcid as int].is_Some(),
            self@[pcid as int].unwrap().wf(),
            self@[pcid as int].unwrap().pcid == old(self)@[pcid as int].unwrap().pcid, 
            self@[pcid as int].unwrap().kernel_l4_end == old(self)@[pcid as int].unwrap().kernel_l4_end,  
            self@[pcid as int].unwrap().page_closure() =~= old(self)@[pcid as int].unwrap().page_closure().insert(page_map_ptr),
            self@[pcid as int].unwrap().mapping_4k() =~= old(self)@[pcid as int].unwrap().mapping_4k(),
            self@[pcid as int].unwrap().mapping_2m() =~= old(self)@[pcid as int].unwrap().mapping_2m(),
            self@[pcid as int].unwrap().mapping_1g() =~= old(self)@[pcid as int].unwrap().mapping_1g(),
            self@[pcid as int].unwrap().mapped_4k_pages() =~= old(self)@[pcid as int].unwrap().mapped_4k_pages(),
            self@[pcid as int].unwrap().mapped_2m_pages() =~= old(self)@[pcid as int].unwrap().mapped_2m_pages(),
            self@[pcid as int].unwrap().mapped_1g_pages() =~= old(self)@[pcid as int].unwrap().mapped_1g_pages(),
            self@[pcid as int].unwrap().spec_resolve_mapping_1g_l3(target_l4i, target_l3i) == old(self)@[pcid as int].unwrap().spec_resolve_mapping_1g_l3(target_l4i, target_l3i),
            self@[pcid as int].unwrap().spec_resolve_mapping_l3(target_l4i, target_l3i) == old(self)@[pcid as int].unwrap().spec_resolve_mapping_l3(target_l4i, target_l3i),
            self@[pcid as int].unwrap().spec_resolve_mapping_l2(target_l4i,target_l3i, target_l2i).is_Some(),
            self@[pcid as int].unwrap().spec_resolve_mapping_l2(target_l4i,target_l3i, target_l2i).get_Some_0().addr == page_map_ptr,
            self@[pcid as int].unwrap().spec_resolve_mapping_2m_l2(target_l4i,target_l3i, target_l2i).is_None(),
            self@[pcid as int].unwrap().kernel_entries =~= old(self)@[pcid as int].unwrap().kernel_entries,
    {
        self.ar[pcid].as_mut().unwrap().create_entry_l2(target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr, Tracked(page_map_perm));
    }
}
    

}