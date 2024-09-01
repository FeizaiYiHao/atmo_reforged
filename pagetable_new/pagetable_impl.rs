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
            self.mapping_4k() =~= old(self).mapping_4k(),
            self.mapping_2m() =~= old(self).mapping_2m(),
            self.mapping_1g() =~= old(self).mapping_1g(),
            self.mapped_4k_pages() =~= old(self).mapped_4k_pages(),
            self.mapped_2m_pages() =~= old(self).mapped_2m_pages(),
            self.mapped_1g_pages() =~= old(self).mapped_1g_pages(),
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
        }
        assert(self.wf_l4());

        assert(self.wf_l3()) by {
            assert(self.spec_resolve_mapping_l4(target_l4i).is_Some() && self.spec_resolve_mapping_l4(target_l4i).get_Some_0().addr == page_map_ptr);
            assert(        
                forall|p: PageMapPtr|
                self.l3_tables@.dom().contains(p) && p != page_map_ptr ==>
                    exists|l4i:L4Index|
                        #![trigger self.spec_resolve_mapping_l4(l4i)]
                        0 <= l4i < 512 && 
                        self.spec_resolve_mapping_l4(l4i).is_Some() && self.spec_resolve_mapping_l4(l4i).get_Some_0().addr == p)
                by
                {
                    assert(forall|l4i:L4Index|
                        #![trigger  self.spec_resolve_mapping_l4(l4i)]
                        #![trigger  old(self).spec_resolve_mapping_l4(l4i)]
                        0 <= l4i < 512 && l4i != target_l4i ==>
                        self.spec_resolve_mapping_l4(l4i) =~= old(self).spec_resolve_mapping_l4(l4i)
                    );
                };
    
            //L3 tables unique within);
            assert(forall|p: PageMapPtr, l3i: L3Index, l3j: L3Index| 
                #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[l3i].addr, self.l3_tables@[p].value()[l3j].addr, self.l3_tables@[p].value()[l3i].perm.ps, self.l3_tables@[p].value()[l3j].perm.ps, self.l3_tables@[p].value()[l3i].addr, self.l3_tables@[p].value()[l3j].addr]
                self.l3_tables@.dom().contains(p) && l3i != l3j && 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[p].value()[l3i].perm.present && self.l3_tables@[p].value()[l3j].perm.present 
                    && !self.l3_tables@[p].value()[l3i].perm.ps && !self.l3_tables@[p].value()[l3j].perm.ps 
                    ==> 
                    self.l3_tables@[p].value()[l3i].addr != self.l3_tables@[p].value()[l3j].addr);
            // //L3 tables are disjoint        
            assert(forall|pi: PageMapPtr, pj: PageMapPtr, l3i: L3Index, l3j: L3Index|
                #![trigger self.l3_tables@.dom().contains(pi), self.l3_tables@.dom().contains(pj), self.l3_tables@[pi].value()[l3i].addr, self.l3_tables@[pj].value()[l3j].addr, self.l3_tables@[pi].value()[l3i].perm.ps, self.l3_tables@[pj].value()[l3j].perm.ps, self.l3_tables@[pi].value()[l3i].perm.present, self.l3_tables@[pj].value()[l3j].perm.present]
                pi != pj && self.l3_tables@.dom().contains(pi) && self.l3_tables@.dom().contains(pj) && 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[pi].value()[l3i].perm.present && self.l3_tables@[pj].value()[l3j].perm.present 
                    && !self.l3_tables@[pi].value()[l3i].perm.ps && !self.l3_tables@[pj].value()[l3j].perm.ps
                    ==>
                    self.l3_tables@[pi].value()[l3i].addr != self.l3_tables@[pj].value()[l3j].addr);
            // //L3 tables does not map to L4 or L1        );
            assert(forall|p: PageMapPtr, i: L3Index| 
                #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
                #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
                #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].addr] 
                self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.present ==>
                    self.l3_tables@.dom().contains(self.l3_tables@[p].value()[i].addr) == false
                    &&
                    self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr) == false
                    &&
                    self.cr3 != self.l3_tables@[p].value()[i].addr)
                    
            by {
                old(self).ps_entries_exist_in_mapped_pages();
            };
            // all l3 points to valid l2 tables);
            assert(forall|p: PageMapPtr, i: L3Index| 
                #![trigger self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].perm.ps ] 
                #![trigger self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
                self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.present && !self.l3_tables@[p].value()[i].perm.ps ==>
                    self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr));

        };
        assert(self.wf_l2()) by {
            assert(forall|p: PageMapPtr|
                self.l2_tables@.dom().contains(p) ==>
                    exists|l4i: L4Index, l3i:L3Index|
                        #![trigger self.spec_resolve_mapping_l3(l4i, l3i)]
                        0 <= l4i < 512 && 0 <= l3i < 512 &&
                        self.spec_resolve_mapping_l3(l4i, l3i).is_Some() && self.spec_resolve_mapping_l3(l4i, l3i).get_Some_0().addr == p)
            by
            {
                assert(forall|p: PageMapPtr|
                    self.l2_tables@.dom().contains(p) ==>
                        exists|l4i: L4Index, l3i:L3Index|
                            #![auto]
                            0 <= l4i < 512 && 0 <= l3i < 512 && l4i != target_l4i &&
                            old(self).spec_resolve_mapping_l3(l4i, l3i).is_Some() && old(self).spec_resolve_mapping_l3(l4i, l3i).get_Some_0().addr == p);

                assert(forall|l4i: L4Index, l3i:L3Index|
                            #![auto]
                            0 <= l4i < 512 && 0 <= l3i < 512 && l4i != target_l4i ==>
                            old(self).spec_resolve_mapping_l3(l4i, l3i) =~= self.spec_resolve_mapping_l3(l4i, l3i));
            };
            // L2 does not map to L4, L3, or self);
            assert(forall|p: PageMapPtr, i: L2Index| 
                #![trigger self.l2_tables@[p].value()[i].perm.present, self.l2_tables@.dom().contains(self.l2_tables@[p].value()[i].addr)] 
                #![trigger self.l2_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l2_tables@[p].value()[i].addr)] 
                #![trigger self.l2_tables@[p].value()[i].perm.present, self.l2_tables@[p].value()[i].addr] 
                self.l2_tables@.dom().contains(p) && 0 <= i < 512 && self.l2_tables@[p].value()[i].perm.present ==>
                    self.l2_tables@.dom().contains(self.l2_tables@[p].value()[i].addr) == false
                    &&
                    self.l3_tables@.dom().contains(self.l2_tables@[p].value()[i].addr) == false
                    &&
                    self.cr3 != self.l2_tables@[p].value()[i].addr)
                by {
                    old(self).ps_entries_exist_in_mapped_pages();
                };
        };
        assert(self.wf_l1()) by {
            assert(forall|p: PageMapPtr|
                self.l1_tables@.dom().contains(p) ==>
                    exists|l4i: L4Index, l3i:L3Index, l2i:L2Index|
                        #![trigger self.spec_resolve_mapping_l2(l4i, l3i, l2i)]
                        0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 &&
                        self.spec_resolve_mapping_l2(l4i, l3i, l2i).is_Some() && self.spec_resolve_mapping_l2(l4i, l3i, l2i).get_Some_0().addr == p)
                by
                {
                    assert(forall|p: PageMapPtr|
                        self.l1_tables@.dom().contains(p) ==>
                            exists|l4i: L4Index, l3i:L3Index, l2i:L3Index|
                                #![auto]
                                0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && l4i != target_l4i &&
                                old(self).spec_resolve_mapping_l2(l4i, l3i, l2i).is_Some() && old(self).spec_resolve_mapping_l2(l4i, l3i, l2i).get_Some_0().addr == p);

                    assert(forall|l4i: L4Index, l3i:L3Index, l2i:L3Index|
                                #![auto]
                                0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && l4i != target_l4i ==>
                                old(self).spec_resolve_mapping_l2(l4i, l3i, l2i) =~= self.spec_resolve_mapping_l2(l4i, l3i, l2i));
                };
            // no l1 tables map to other levels
            assert(forall|p: PageMapPtr, i: L1Index| 
                #![trigger self.l1_tables@.dom().contains(p), self.l1_tables@[p].value()[i].perm.present, self.l2_tables@.dom().contains(self.l1_tables@[p].value()[i].addr)] 
                #![trigger self.l1_tables@.dom().contains(p), self.l1_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l1_tables@[p].value()[i].addr)] 
                #![trigger self.l1_tables@.dom().contains(p), self.l1_tables@[p].value()[i].perm.present, self.l1_tables@[p].value()[i].addr] 
                self.l1_tables@.dom().contains(p) && 0 <= i < 512 && self.l1_tables@[p].value()[i].perm.present ==>
                    self.l2_tables@.dom().contains(self.l1_tables@[p].value()[i].addr) == false
                    &&
                    self.l3_tables@.dom().contains(self.l1_tables@[p].value()[i].addr) == false
                    &&
                    self.cr3 != self.l1_tables@[p].value()[i].addr) by {
                        old(self).ps_entries_exist_in_mapped_pages();
                    };
            // no hugepage in l1
            assert(forall|p: PageMapPtr, i: L1Index| 
                #![trigger self.l1_tables@[p].value()[i].perm.ps] 
                self.l1_tables@.dom().contains(p) && 0 <= i < 512 && self.l1_tables@[p].value()[i].perm.present ==>
                    ! self.l1_tables@[p].value()[i].perm.ps);
        };
        assert(self.wf_mapping_4k()) by {
            assert(forall|l4i: L4Index,l3i: L3Index,l2i: L2Index,l1i: L2Index| 
                #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                #![trigger old(self).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 ==>
                    old(self).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i) == self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i));
        };
        assert(self.wf_mapping_2m()) by {
            assert(forall|l4i: L4Index,l3i: L3Index,l2i: L2Index| 
                #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                #![trigger old(self).spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 ==>
                    old(self).spec_resolve_mapping_2m_l2(l4i,l3i,l2i) == self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i));
        };
        assert(self.wf_mapping_1g())by {
            assert(forall|l4i: L4Index,l3i: L3Index| 
                #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
                #![trigger old(self).spec_resolve_mapping_1g_l3(l4i,l3i)]
                0 <= l4i < 512 && 0 <= l3i < 512 ==>
                    old(self).spec_resolve_mapping_1g_l3(l4i,l3i) == self.spec_resolve_mapping_1g_l3(l4i,l3i));
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
            old(self).spec_resolve_mapping_1g_l3(target_l4i, target_l3i).is_None(),
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
            // self.wf(),
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
        }
        assert(self.wf_l4());
        assert(self.wf_l3())
            by
            {
                assert(forall|p: PageMapPtr|
                    self.l3_tables@.dom().contains(p) ==>
                        exists|l4i:L4Index|
                            #![trigger self.spec_resolve_mapping_l4(l4i)]
                            0 <= l4i < 512 && 
                            self.spec_resolve_mapping_l4(l4i).is_Some() && self.spec_resolve_mapping_l4(l4i).get_Some_0().addr == p)
                            by
                            {
                                assert(forall|l4i:L4Index|
                                    #![trigger  self.spec_resolve_mapping_l4(l4i)]
                                    #![trigger  old(self).spec_resolve_mapping_l4(l4i)]
                                    0 <= l4i < 512 ==>
                                    self.spec_resolve_mapping_l4(l4i) =~= old(self).spec_resolve_mapping_l4(l4i)
                                );
                            };
            };
        assert(self.wf_l2()) 
            by
            {
                assert(self.spec_resolve_mapping_l3(target_l4i,target_l3i).is_Some() && self.spec_resolve_mapping_l3(target_l4i,target_l3i).get_Some_0().addr == page_map_ptr);
                assert(forall|p: PageMapPtr|
                    self.l2_tables@.dom().contains(p) ==>
                        exists|l4i: L4Index, l3i:L3Index|
                            #![trigger self.spec_resolve_mapping_l3(l4i, l3i)]
                            0 <= l4i < 512 && 0 <= l3i < 512 &&
                            self.spec_resolve_mapping_l3(l4i, l3i).is_Some() && self.spec_resolve_mapping_l3(l4i, l3i).get_Some_0().addr == p)
                            
                    by{
                        assert(forall|l4i:L4Index, l3i:L3Index|
                            #![trigger  self.spec_resolve_mapping_l3(l4i,l3i)]
                            #![trigger  old(self).spec_resolve_mapping_l3(l4i,l3i)]
                            0 <= l4i < 512 && 0 <= l3i < 512 && (l4i,l3i) != (target_l4i, target_l3i) ==>
                            self.spec_resolve_mapping_l3(l4i,l3i) =~= old(self).spec_resolve_mapping_l3(l4i,l3i)
                        );
                    };
                // L2 does not map to L4, L3, or self
                assert(forall|p: PageMapPtr, i: L2Index| 
                    #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[i].perm.present, self.l2_tables@.dom().contains(self.l2_tables@[p].value()[i].addr)] 
                    #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l2_tables@[p].value()[i].addr)] 
                    #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[i].perm.present, self.l2_tables@[p].value()[i].addr] 
                    self.l2_tables@.dom().contains(p) && 0 <= i < 512 && self.l2_tables@[p].value()[i].perm.present ==>
                        self.l2_tables@.dom().contains(self.l2_tables@[p].value()[i].addr) == false
                        &&
                        self.l3_tables@.dom().contains(self.l2_tables@[p].value()[i].addr) == false
                        &&
                        self.cr3 != self.l2_tables@[p].value()[i].addr) 
                        by{
                            old(self).ps_entries_exist_in_mapped_pages()
                        };
            };
        assert(self.wf_l1()) by {
            assert(forall|p: PageMapPtr|
                self.l1_tables@.dom().contains(p) ==>
                    exists|l4i: L4Index, l3i:L3Index, l2i:L2Index|
                        #![trigger self.spec_resolve_mapping_l2(l4i, l3i, l2i)]
                        0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 &&
                        self.spec_resolve_mapping_l2(l4i, l3i, l2i).is_Some() && self.spec_resolve_mapping_l2(l4i, l3i, l2i).get_Some_0().addr == p)
                by
                {

                    assert(forall|l4i: L4Index, l3i:L3Index, l2i:L3Index|
                                #![auto]
                                0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && (l4i,l3i) != (target_l4i, target_l3i) ==>
                                old(self).spec_resolve_mapping_l2(l4i, l3i, l2i) =~= self.spec_resolve_mapping_l2(l4i, l3i, l2i));
                };
            // no l1 tables map to other levels
            assert(forall|p: PageMapPtr, i: L1Index| 
                #![trigger self.l1_tables@.dom().contains(p), self.l1_tables@[p].value()[i].perm.present, self.l2_tables@.dom().contains(self.l1_tables@[p].value()[i].addr)] 
                #![trigger self.l1_tables@.dom().contains(p), self.l1_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l1_tables@[p].value()[i].addr)] 
                #![trigger self.l1_tables@.dom().contains(p), self.l1_tables@[p].value()[i].perm.present, self.l1_tables@[p].value()[i].addr] 
                self.l1_tables@.dom().contains(p) && 0 <= i < 512 && self.l1_tables@[p].value()[i].perm.present ==>
                    self.l2_tables@.dom().contains(self.l1_tables@[p].value()[i].addr) == false
                    &&
                    self.l3_tables@.dom().contains(self.l1_tables@[p].value()[i].addr) == false
                    &&
                    self.cr3 != self.l1_tables@[p].value()[i].addr) by {
                        old(self).ps_entries_exist_in_mapped_pages();
                    };
        };
        assert(self.wf_mapping_4k()) by {
            assert(forall|l4i: L4Index,l3i: L3Index,l2i: L2Index,l1i: L2Index| 
                #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                #![trigger old(self).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 ==>
                    old(self).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i) == self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i));
        };
        assert(self.wf_mapping_2m()) by {
            assert(forall|l4i: L4Index,l3i: L3Index,l2i: L2Index| 
                #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                #![trigger old(self).spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 ==>
                    old(self).spec_resolve_mapping_2m_l2(l4i,l3i,l2i) == self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i));
        };
        assert(self.wf_mapping_1g())by {
            assert(forall|l4i: L4Index,l3i: L3Index| 
                #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
                #![trigger old(self).spec_resolve_mapping_1g_l3(l4i,l3i)]
                0 <= l4i < 512 && 0 <= l3i < 512 && (l4i,l3i) != (target_l4i, target_l3i) ==>
                    old(self).spec_resolve_mapping_1g_l3(l4i,l3i) =~= self.spec_resolve_mapping_1g_l3(l4i,l3i));
        };
        assert(self.user_only());
        assert(self.rwx_upper_level_entries());
        assert(self.present_or_zero());
        assert(self.table_pages_wf());
    }


}
}