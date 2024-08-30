use vstd::prelude::*;

verus! {
use crate::define::*;
// use crate::array::*;
use vstd::simple_pptr::*;
use crate::util::page_ptr_util_u::*;

use crate::pagetable::entry::*;
use crate::pagetable::pagemap::*;
use crate::pagetable::pagetable_spec::*;
// use crate::pagetable::pagetable_util::*;
use crate::pagetable::pagemap_util_t::*;
use crate::lemma::lemma_u::*;

impl PageTable{

    // pub fn map_4k_page(&mut self, va:VAddr, dst: MapEntry)
    //     requires
    //         old(self).wf(),
    //         old(self).page_closure().contains(dst.addr) == false,
    //         old(self).mapping_4k()[va].is_None(),
    //         page_ptr_valid(dst.addr),
    // {

    // }

    pub fn create_entry_l4(&mut self, target_l4i: L4Index, page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<PageMap>>)
        requires
            old(self).wf(),
            0<=target_l4i<512,
            old(self).spec_resolve_mapping_l4(target_l4i).is_None(),
            page_ptr_valid(page_map_ptr),
            old(self).page_closure().contains(page_map_ptr) == false,
            old(self).page_not_mapped(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i:usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0<=i<512 ==> page_map_perm.value()[i].is_empty(),
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure().insert(page_map_ptr),
            self.mapping_4K() =~= old(self).mapping_4K(),
            self.mapping_2M() =~= old(self).mapping_2M(),
            self.mapping_1G() =~= old(self).mapping_1G(),
            self.mapped_4K_pages() =~= old(self).mapped_4K_pages(),
            self.mapped_2M_pages() =~= old(self).mapped_2M_pages(),
            self.mapped_1G_pages() =~= old(self).mapped_1G_pages(),
            self.spec_resolve_mapping_l4(target_l4i).is_Some(),
            self.spec_resolve_mapping_l4(target_l4i).get_Some_0().addr == page_map_ptr,
    {
        assert(
            forall|i:usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                #![trigger page_map_perm.value()[i].perm.present]
                0<=i<512 ==> page_map_perm.value()[i].is_empty() && page_map_perm.value()[i].perm.present == false && page_map_perm.value()[i].perm.write == false && page_map_perm.value()[i].perm.execute_disable == false 
        );
        let tracked mut l4_perm = self.l4_table.borrow_mut().tracked_remove(self.cr3);
        proof{
            page_ptr_valid_imply_MEM_valid(page_map_ptr);
        }
        page_map_set(self.cr3, Tracked(&mut l4_perm), target_l4i,
            PageEntry{
                addr: page_map_ptr,
                perm: PageEntryPerm{
                    present: true,
                    ps: false,
                    write: true,
                    execute_disable: false,
                    user: true,
                }
        });
        proof {
            self.l4_table.borrow_mut().tracked_insert(self.cr3, l4_perm);
            assert(self.spec_resolve_mapping_l4(target_l4i).is_Some() && self.spec_resolve_mapping_l4(target_l4i).get_Some_0().addr == page_map_ptr);
            self.l3_tables.borrow_mut().tracked_insert(page_map_ptr, page_map_perm);
            self.l3_rev_map@ = self.l3_rev_map@.insert(page_map_ptr, target_l4i);
        }
        assert(self.wf_l4());
        assert(self.wf_l3()) by {
            assert(self.spec_resolve_mapping_l4(target_l4i).is_Some() && self.spec_resolve_mapping_l4(target_l4i).get_Some_0().addr == page_map_ptr);
            old(self).ps_entries_exist_in_mapped_pages();
        };
        assert(self.wf_l2()) by {
            old(self).ps_entries_exist_in_mapped_pages();
        };
        assert(self.wf_l1()) by {
            old(self).ps_entries_exist_in_mapped_pages();
        };
        assert(self.wf_mapping_4K()) by {
            assert(forall|l4i: L4Index,l3i: L3Index,l2i: L2Index,l1i: L2Index| 
                #![trigger self.spec_resolve_mapping_4K_l1(l4i,l3i,l2i,l1i)]
                #![trigger old(self).spec_resolve_mapping_4K_l1(l4i,l3i,l2i,l1i)]
                0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 ==>
                    old(self).spec_resolve_mapping_4K_l1(l4i,l3i,l2i,l1i) == self.spec_resolve_mapping_4K_l1(l4i,l3i,l2i,l1i));
        };
        assert(self.wf_mapping_2M()) by {
            assert(forall|l4i: L4Index,l3i: L3Index,l2i: L2Index| 
                #![trigger self.spec_resolve_mapping_2M_l2(l4i,l3i,l2i)]
                #![trigger old(self).spec_resolve_mapping_2M_l2(l4i,l3i,l2i)]
                0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 ==>
                    old(self).spec_resolve_mapping_2M_l2(l4i,l3i,l2i) == self.spec_resolve_mapping_2M_l2(l4i,l3i,l2i));
        };
        assert(self.wf_mapping_1G())by {
            assert(forall|l4i: L4Index,l3i: L3Index| 
                #![trigger self.spec_resolve_mapping_1G_l3(l4i,l3i)]
                #![trigger old(self).spec_resolve_mapping_1G_l3(l4i,l3i)]
                0 <= l4i < 512 && 0 <= l3i < 512 ==>
                    old(self).spec_resolve_mapping_1G_l3(l4i,l3i) == self.spec_resolve_mapping_1G_l3(l4i,l3i));
        };
        assert(self.user_only());
        assert(self.rwx_upper_level_entries());
        assert(self.present_or_zero());
        assert(self.table_pages_wf());
    }


    pub fn create_entry_l3(&mut self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p:PageMapPtr, page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<PageMap>>)
        requires
            old(self).wf(),
            0<=target_l4i<512,
            0<=target_l3i<512,
            old(self).spec_resolve_mapping_l4(target_l4i).is_Some(),
            old(self).spec_resolve_mapping_l4(target_l4i).get_Some_0().addr == target_l3_p,
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i).is_None(),
            old(self).spec_resolve_mapping_1G_l3(target_l4i, target_l3i).is_None(),
            page_ptr_valid(page_map_ptr),
            old(self).page_closure().contains(page_map_ptr) == false,
            old(self).page_not_mapped(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i:usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0<=i<512 ==> page_map_perm.value()[i].is_empty(),
        ensures
            self.wf(),
    {
        assert(
            forall|i:usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                #![trigger page_map_perm.value()[i].perm.present]
                0<=i<512 ==> page_map_perm.value()[i].is_empty() && page_map_perm.value()[i].perm.present == false && page_map_perm.value()[i].perm.write == false && page_map_perm.value()[i].perm.execute_disable == false 
        );
        assert(old(self).spec_resolve_mapping_l4(target_l4i).get_Some_0().perm.present && !old(self).spec_resolve_mapping_l4(target_l4i).get_Some_0().perm.ps && old(self).spec_resolve_mapping_l4(target_l4i).get_Some_0().perm.write && ! old(self).spec_resolve_mapping_l4(target_l4i).get_Some_0().perm.execute_disable);
        
        let tracked mut l3_perm = self.l3_tables.borrow_mut().tracked_remove(target_l3_p);
        proof{
            page_ptr_valid_imply_MEM_valid(page_map_ptr);
        }
        page_map_set(target_l3_p, Tracked(&mut l3_perm), target_l3i,
            PageEntry{
                addr: page_map_ptr,
                perm: PageEntryPerm{
                    present: true,
                    ps: false,
                    write: true,
                    execute_disable: false,
                    user: true,
                }
        });
        proof {
            self.l3_tables.borrow_mut().tracked_insert(target_l3_p, l3_perm);
            assert(self.spec_resolve_mapping_l3(target_l4i, target_l3i).is_Some() && 
                    self.spec_resolve_mapping_l3(target_l4i, target_l3i).get_Some_0().addr == page_map_ptr && 
                    !self.spec_resolve_mapping_l3(target_l4i, target_l3i).get_Some_0().perm.ps && 
                    self.spec_resolve_mapping_l3(target_l4i, target_l3i).get_Some_0().perm.write && 
                    !self.spec_resolve_mapping_l3(target_l4i, target_l3i).get_Some_0().perm.execute_disable);
            self.l2_tables.borrow_mut().tracked_insert(page_map_ptr, page_map_perm);
            self.l2_rev_map@ = self.l2_rev_map@.insert(page_map_ptr, (target_l4i,target_l3i));
        }
        assert(self.wf_l4());
        assert(self.wf_l3());

        assert(self.wf_l2()) by
        {
            old(self).ps_entries_exist_in_mapped_pages()
        };
        assert(self.wf_l1()) by {
            old(self).ps_entries_exist_in_mapped_pages();

        };
        assert(self.wf_mapping_4K()) by {
            assert(forall|l4i: L4Index,l3i: L3Index,l2i: L2Index,l1i: L2Index| 
                #![trigger self.spec_resolve_mapping_4K_l1(l4i,l3i,l2i,l1i)]
                #![trigger old(self).spec_resolve_mapping_4K_l1(l4i,l3i,l2i,l1i)]
                0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 ==>
                    old(self).spec_resolve_mapping_4K_l1(l4i,l3i,l2i,l1i) == self.spec_resolve_mapping_4K_l1(l4i,l3i,l2i,l1i));
        };
        assert(self.wf_mapping_2M()) by {
            assert(forall|l4i: L4Index,l3i: L3Index,l2i: L2Index| 
                #![trigger self.spec_resolve_mapping_2M_l2(l4i,l3i,l2i)]
                #![trigger old(self).spec_resolve_mapping_2M_l2(l4i,l3i,l2i)]
                0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 ==>
                    old(self).spec_resolve_mapping_2M_l2(l4i,l3i,l2i) == self.spec_resolve_mapping_2M_l2(l4i,l3i,l2i));
        };
        assert(self.wf_mapping_1G())by {
            assert(forall|l4i: L4Index,l3i: L3Index| 
                #![trigger self.spec_resolve_mapping_1G_l3(l4i,l3i)]
                #![trigger old(self).spec_resolve_mapping_1G_l3(l4i,l3i)]
                0 <= l4i < 512 && 0 <= l3i < 512 && (l4i,l3i) != (target_l4i, target_l3i) ==>
                    old(self).spec_resolve_mapping_1G_l3(l4i,l3i) =~= self.spec_resolve_mapping_1G_l3(l4i,l3i));
        };
        assert(self.user_only());
        assert(self.rwx_upper_level_entries());
        assert(self.present_or_zero());
        assert(self.table_pages_wf());
    }


}
}