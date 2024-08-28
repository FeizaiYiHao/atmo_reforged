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
 
    pub proof fn ps_entries_exist_in_mapped_pages(&self)
        requires
            self.wf(),
        ensures      
            forall|p: PageMapPtr, i: L3Index| 
            #![trigger self.mapped_1G_pages().contains(self.l3_tables@[p].value()[i].addr)]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.present && self.l3_tables@[p].value()[i].perm.ps ==>
                self.mapped_1G_pages().contains(self.l3_tables@[p].value()[i].addr),
            forall|p: PageMapPtr, i: L2Index| 
            #![trigger self.mapped_2M_pages().contains(self.l2_tables@[p].value()[i].addr)]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512 && self.l2_tables@[p].value()[i].perm.present && self.l2_tables@[p].value()[i].perm.ps ==>
                self.mapped_2M_pages().contains(self.l2_tables@[p].value()[i].addr),
            forall|p: PageMapPtr, i: L2Index| 
            #![trigger self.mapped_4K_pages().contains(self.l1_tables@[p].value()[i].addr)]
            self.l1_tables@.dom().contains(p) && 0 <= i < 512 && self.l1_tables@[p].value()[i].perm.present && self.l1_tables@[p].value()[i].perm.ps ==>
                self.mapped_4K_pages().contains(self.l2_tables@[p].value()[i].addr),
    {
        assert(
            forall|p: PageMapPtr, i: L3Index| 
            #![auto]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.present && self.l3_tables@[p].value()[i].perm.ps ==>
                self.mapped_1G_pages().contains(self.l3_tables@[p].value()[i].addr)
        )
            by{
                assert(forall|p: PageMapPtr, i: L3Index| 
                    #![auto]
                    self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.present && self.l3_tables@[p].value()[i].perm.ps ==>
                        exists|l4i:L4Index| 
                            #![auto] 
                            0<=l4i<512 
                            &&
                            self.spec_resolve_mapping_l4(l4i).is_Some() && self.spec_resolve_mapping_l4(l4i).get_Some_0().addr == p 
                            &&
                            self.spec_resolve_mapping_1G_l3(l4i,i).is_Some() && self.spec_resolve_mapping_1G_l3(l4i,i).get_Some_0().addr == self.l3_tables@[p].value()[i].addr 
                            &&
                            self.mapping_1G@.dom().contains(spec_index2va((l4i,i,0,0))) 
                            &&
                            self.mapping_1G@[spec_index2va((l4i,i,0,0))].addr == self.l3_tables@[p].value()[i].addr 
                            &&
                            self.mapping_1G().dom().contains(spec_index2va((l4i,i,0,0))) 
                            &&
                            self.mapping_1G()[spec_index2va((l4i,i,0,0))].addr == self.l3_tables@[p].value()[i].addr 
                            &&
                            self.mapped_1G_pages().contains(self.l3_tables@[p].value()[i].addr)
                );
            };

        assert(
            forall|p: PageMapPtr, i: L2Index| 
            #![auto]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512 && self.l2_tables@[p].value()[i].perm.present && self.l2_tables@[p].value()[i].perm.ps ==>
                self.mapped_2M_pages().contains(self.l2_tables@[p].value()[i].addr)
        ) by {
            assert(forall|p: PageMapPtr, i: L2Index| 
                #![auto]
                self.l2_tables@.dom().contains(p) && 0 <= i < 512 && self.l2_tables@[p].value()[i].perm.present && self.l2_tables@[p].value()[i].perm.ps ==>
                    exists|l4i:L4Index,l3i:L3Index| 
                        #![auto] 
                        0<=l4i<512 && 0<=l3i<512
                        &&
                        self.spec_resolve_mapping_l3(l4i,l3i).is_Some() && self.spec_resolve_mapping_l3(l4i,l3i).get_Some_0().addr == p 
                        &&
                        self.spec_resolve_mapping_2M_l2(l4i,l3i,i).is_Some() && self.spec_resolve_mapping_2M_l2(l4i,l3i,i).get_Some_0().addr == self.l2_tables@[p].value()[i].addr 
                        &&
                        self.mapping_2M@.dom().contains(spec_index2va((l4i,l3i,i,0))) 
                        &&
                        self.mapping_2M@[spec_index2va((l4i,l3i,i,0))].addr == self.l2_tables@[p].value()[i].addr 
                        &&
                        self.mapping_2M().dom().contains(spec_index2va((l4i,l3i,i,0))) 
                        // &&
                        // self.mapping_2M()[spec_index2va((l4i,l3i,i,0))].addr == self.l2_tables@[p].value()[i].addr 
                        // &&
                        // self.mapped_2M_pages().contains(self.l2_tables@[p].value()[i].addr)
            );
        };
        assert(
            forall|p: PageMapPtr, i: L1Index| 
            #![auto]
            self.l1_tables@.dom().contains(p) && 0 <= i < 512 && self.l1_tables@[p].value()[i].perm.present && self.l1_tables@[p].value()[i].perm.ps ==>
                self.mapped_4K_pages().contains(self.l1_tables@[p].value()[i].addr)
        ) by {
            assert(forall|p: PageMapPtr, i: L2Index| 
                #![auto]
                self.l1_tables@.dom().contains(p) && 0 <= i < 512 && self.l1_tables@[p].value()[i].perm.present && self.l1_tables@[p].value()[i].perm.ps ==>
                    exists|l4i:L4Index,l3i:L3Index,l2i:L3Index| 
                        #![auto] 
                        0<=l4i<512 && 0<=l3i<512 && 0<=l2i<512
                        &&
                        self.spec_resolve_mapping_l2(l4i,l3i,l2i).is_Some() && self.spec_resolve_mapping_l2(l4i,l3i,l2i).get_Some_0().addr == p 
                        &&
                        self.spec_resolve_mapping_4K_l1(l4i,l3i,l2i,i).is_Some() && self.spec_resolve_mapping_4K_l1(l4i,l3i,l2i,i).get_Some_0().addr == self.l1_tables@[p].value()[i].addr 
                        &&
                        self.mapping_4K@.dom().contains(spec_index2va((l4i,l3i,i,0))) 
                        &&
                        self.mapping_4K@[spec_index2va((l4i,l3i,l2i,i))].addr == self.l1_tables@[p].value()[i].addr 
                        &&
                        self.mapping_4K().dom().contains(spec_index2va((l4i,l3i,l2i,i))) 
                        // &&
                        // self.mapping_2M()[spec_index2va((l4i,l3i,i,0))].addr == self.l2_tables@[p].value()[i].addr 
                        // &&
                        // self.mapped_2M_pages().contains(self.l2_tables@[p].value()[i].addr)
            );
        };
    }

}
}