use vstd::prelude::*;

verus! {
use crate::define::*;
use crate::array::*;
use vstd::simple_pptr::*;
use crate::util::page_ptr_util_u::*;

use crate::pagetable::entry::*;
use crate::pagetable::pagemap::*;
use crate::pagetable::pagetable_spec::*;
use crate::pagetable::pagetable_util::*;
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

    pub fn create_4K_entry_l4(&mut self, target_l4i: L4Index, page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<PageMap>>)
        requires
            old(self).wf(),
            0<=target_l4i<512,
            old(self).spec_resolve_mapping_l4(target_l4i).is_None(),
            page_ptr_valid(page_map_ptr),
            old(self).page_closure().contains(page_map_ptr) == false,
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i:usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0<=i<512 ==> page_map_perm.value()[i].is_empty(),
    {
        // proof{
        //     self.outside_of_closure_imply_outside_of_every_level(page_map_ptr);
        // }

        assert(forall|i:usize|
            #![trigger page_map_perm.value()[i].is_empty()]
            #![trigger page_map_perm.value()[i].perm.present]
            0<=i<512 ==> page_map_perm.value()[i].is_empty() && page_map_perm.value()[i].perm.present == false
        );

        // assert(forall|p: PageMapPtr|
        //     #![trigger self.l3_tables@.dom().contains(p)]
        //     self.l3_tables@.dom().contains(p) ==>
        //         exists|l4i:L4Index|
        //             #![trigger self.l4_table@[self.cr3].value()[l4i].addr]
        //             0 <= l4i < 512 && self.l4_table@[self.cr3].value()[l4i].perm.present && !self.l4_table@[self.cr3].value()[l4i].perm.ps && l4i != target_l4i &&
        //             self.l4_table@[self.cr3].value()[l4i].addr == p);


        let tracked mut l4_perm = self.l4_table.borrow_mut().tracked_remove(self.cr3);
        assert(l4_perm.value()@[target_l4i as int].perm.present == false);
        assert(l4_perm.value()@[target_l4i as int].is_empty());
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
            assert(self.l3_tables@.dom().contains(page_map_ptr) == false);
            self.l3_tables.borrow_mut().tracked_insert(page_map_ptr, page_map_perm);
            assert(self.l4_table@[self.cr3].value()[target_l4i].addr == page_map_ptr);
            assert(forall|i:usize| 0 <= i < 512 && i != target_l4i ==> self.l4_table@[self.cr3].value()[i] =~= old(self).l4_table@[self.cr3].value()[i]);
            assert(forall|p: PageMapPtr, i:usize| 0 <= i < 512 && p != page_map_ptr && self.l3_tables@.dom().contains(p) ==> self.l3_tables@[p].value()[i].perm.present =~= old(self).l3_tables@[p].value()[i].perm.present && self.l3_tables@[p].value()[i].addr =~= old(self).l3_tables@[p].value()[i].addr);
            assert(forall|p: PageMapPtr, i:usize| 0 <= i < 512 && p == page_map_ptr  ==> self.l3_tables@[p].value()[i].perm.present == false);
        }
        // assert(
        //     forall|i: L4Index|
        //         #![trigger self.l4_table@[self.cr3].value()[i].perm.present]
        //         0 <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present && i != l4i ==>
        //             self.l4_table@[self.cr3].value()[i].addr == old(self).l4_table@[self.cr3].value()[i].addr
        // );
        assert(self.wf_l4());

        // assert(forall|p: PageMapPtr|
        //     #![trigger self.l3_tables@[p].addr()]
        //     self.l3_tables@.dom().contains(p) ==> self.l3_tables@[p].addr() == p);
        // assert(forall|p: PageMapPtr| 
        //     #![trigger self.l3_tables@[p].is_init()]
        //     self.l3_tables@.dom().contains(p) ==> self.l3_tables@[p].is_init());
        // assert(forall|p: PageMapPtr|
        //     #![trigger self.l3_tables@[p].value().wf()]
        //     self.l3_tables@.dom().contains(p) ==> self.l3_tables@[p].value().wf());
        // // all l3 tables exists in L4    );

        // assert(forall|p: PageMapPtr|
        //     #![trigger self.l3_tables@.dom().contains(p)]
        //     self.l3_tables@.dom().contains(p) && p != page_map_ptr ==>
        //         exists|l4i:L4Index|
        //             #![trigger self.l4_table@[self.cr3].value()[l4i].addr]
        //             0 <= l4i < 512 && self.l4_table@[self.cr3].value()[l4i].perm.present && !self.l4_table@[self.cr3].value()[l4i].perm.ps &&
        //             self.l4_table@[self.cr3].value()[l4i].addr == p);

        // assert(forall|p: PageMapPtr|
        //     #![trigger self.l3_tables@.dom().contains(p)]
        //     self.l3_tables@.dom().contains(p) ==>
        //         exists|l4i:L4Index|
        //             #![trigger self.l4_table@[self.cr3].value()[l4i].addr]
        //             0 <= l4i < 512 && self.l4_table@[self.cr3].value()[l4i].perm.present && !self.l4_table@[self.cr3].value()[l4i].perm.ps &&
        //             self.l4_table@[self.cr3].value()[l4i].addr == p);
        // //L3 tables unique within);
        // assert(forall|p: PageMapPtr, l3i: L3Index, l3j: L3Index| 
        //     #![trigger self.l3_tables@[p].value()[l3i].addr, self.l3_tables@[p].value()[l3j].addr, self.l3_tables@[p].value()[l3i].perm.ps, self.l3_tables@[p].value()[l3j].perm.ps, self.l3_tables@[p].value()[l3i].perm.present , self.l3_tables@[p].value()[l3j].perm.present]
        //     old(self).l3_tables@.dom().contains(p) && l3i != l3j && 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[p].value()[l3i].perm.present && self.l3_tables@[p].value()[l3j].perm.present 
        //         && !self.l3_tables@[p].value()[l3i].perm.ps && !self.l3_tables@[p].value()[l3j].perm.ps 
        //         ==> 
        //         self.l3_tables@[p].value()[l3i].addr != self.l3_tables@[p].value()[l3j].addr);
        assert(forall|p: PageMapPtr, l3i: L3Index, l3j: L3Index| 
            #![trigger self.l3_tables@[p].value()[l3i].addr, self.l3_tables@[p].value()[l3j].addr, self.l3_tables@[p].value()[l3i].perm.ps, self.l3_tables@[p].value()[l3j].perm.ps, self.l3_tables@[p].value()[l3i].perm.present , self.l3_tables@[p].value()[l3j].perm.present]
            self.l3_tables@.dom().contains(p) && l3i != l3j && 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[p].value()[l3i].perm.present && self.l3_tables@[p].value()[l3j].perm.present 
                && !self.l3_tables@[p].value()[l3i].perm.ps && !self.l3_tables@[p].value()[l3j].perm.ps 
                ==> 
                self.l3_tables@[p].value()[l3i].addr != self.l3_tables@[p].value()[l3j].addr);
        //L3 tables are disjoint        
        assert(forall|pi: PageMapPtr, pj: PageMapPtr, l3i: L3Index, l3j: L3Index|
            #![trigger self.l3_tables@.dom().contains(pi), self.l3_tables@[pi].value()[l3i].addr, self.l3_tables@[pj].value()[l3j].addr, self.l3_tables@[pi].value()[l3i].perm.present, self.l3_tables@[pj].value()[l3j].perm.present, self.l3_tables@[pi].value()[l3i].perm.present, self.l3_tables@[pj].value()[l3j].perm.present]
            pi != pj && self.l3_tables@.dom().contains(pi) && self.l3_tables@.dom().contains(pj) && 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[pi].value()[l3i].perm.present && self.l3_tables@[pj].value()[l3j].perm.present 
                && !self.l3_tables@[pi].value()[l3i].perm.ps && !self.l3_tables@[pj].value()[l3j].perm.ps
                ==>
                self.l3_tables@[pi].value()[l3i].addr != self.l3_tables@[pj].value()[l3j].addr);
        assert(forall|p: PageMapPtr, i: L3Index| 
            #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
            #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
            #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].addr] 
            self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.present ==>
                self.l3_tables@.dom().contains(self.l3_tables@[p].value()[i].addr) == false
                &&
                self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr) == false
                &&
                self.cr3 != self.l3_tables@[p].value()[i].addr);
        // // 1G hugepages have no entries in l2);
        // assert(forall|p: PageMapPtr, i: L3Index| 
        //     #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
        //     #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
        //     #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
        //     #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].addr] 
        //     self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.ps ==>
        //         self.l3_tables@.dom().contains(self.l3_tables@[p].value()[i].addr) == false
        //         &&
        //         self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr) == false
        //         &&
        //         self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr) == false
        //         &&
        //         self.cr3 != self.l3_tables@[p].value()[i].addr);
        // // all l3 points to valid l2 tables);
        // assert(forall|p: PageMapPtr, i: L3Index| 
        //     #![trigger self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].perm.ps ] 
        //     #![trigger self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
        //     self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.present && !self.l3_tables@[p].value()[i].perm.ps ==>
        //         self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr));
        // assert(self.wf_l3());
        // assert(self.wf_l2());
        // assert(self.wf_l1());
        // assert(self.wf_mapping_4K());
        // assert(self.wf_mapping_2M());
        // assert(self.wf_mapping_1G());
        // assert(self.user_only());
        // assert(self.rwx_upper_level_entries());
        // assert(self.present_or_zero());
        // assert(self.table_pages_wf());
    }

}

}