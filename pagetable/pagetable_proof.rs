use vstd::prelude::*;

verus! {
use crate::define::*;
// use crate::array::*;
// use vstd::simple_pptr::*;
use crate::util::page_ptr_util_u::*;

// use crate::pagetable::entry::*;
// use crate::pagetable::pagemap::*;
use crate::pagetable::pagetable_spec::*;
// use crate::pagetable::pagetable_util::*;
// use crate::pagetable::pagemap_util_t::*;
// use crate::lemma::lemma_u::*;

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
            self.l1_tables@.dom().contains(p) && 0 <= i < 512 && self.l1_tables@[p].value()[i].perm.present ==>
                self.mapped_4K_pages().contains(self.l1_tables@[p].value()[i].addr),
    {
        assert(
            forall|p: PageMapPtr, i: L3Index| 
            // #![auto]
            #![trigger self.l3_tables@[p].value()[i]]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.present && self.l3_tables@[p].value()[i].perm.ps ==>
                self.mapped_1G_pages().contains(self.l3_tables@[p].value()[i].addr)
        )
            by{
                assert(forall|p: PageMapPtr, i: L3Index| 
                    // #![auto]
                    #![trigger self.l3_tables@[p].value()[i]]
                    self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.present && self.l3_tables@[p].value()[i].perm.ps ==>
                            0 <= self.l3_rev_map@[p] < 512
                            &&
                            self.l3_rev_map@.dom().contains(p)
                            &&
                            self.spec_resolve_mapping_l4(self.l3_rev_map@[p]).is_Some() && self.spec_resolve_mapping_l4(self.l3_rev_map@[p]).get_Some_0().addr == p 
                            &&
                            self.spec_resolve_mapping_1G_l3(self.l3_rev_map@[p],i).is_Some() && self.spec_resolve_mapping_1G_l3(self.l3_rev_map@[p],i).get_Some_0().addr == self.l3_tables@[p].value()[i].addr 
                            &&
                            self.mapping_1G@.dom().contains(spec_index2va((self.l3_rev_map@[p],i,0,0))) 
                            &&
                            self.mapping_1G@[spec_index2va((self.l3_rev_map@[p],i,0,0))].addr == self.l3_tables@[p].value()[i].addr 
                            &&
                            self.mapping_1G().dom().contains(spec_index2va((self.l3_rev_map@[p],i,0,0))) 
                            &&
                            self.mapping_1G()[spec_index2va((self.l3_rev_map@[p],i,0,0))].addr == self.l3_tables@[p].value()[i].addr 
                            &&
                            self.mapped_1G_pages().contains(self.l3_tables@[p].value()[i].addr)
                );
            };

        assert(
            forall|p: PageMapPtr, i: L2Index| 
            #![trigger self.l2_tables@[p].value()[i]]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512 && self.l2_tables@[p].value()[i].perm.present && self.l2_tables@[p].value()[i].perm.ps ==>
                self.mapped_2M_pages().contains(self.l2_tables@[p].value()[i].addr)
        ) by {
            assert(forall|p: PageMapPtr, i: L2Index| 
                #![trigger self.l2_tables@[p].value()[i]]
                self.l2_tables@.dom().contains(p) && 0 <= i < 512 && self.l2_tables@[p].value()[i].perm.present && self.l2_tables@[p].value()[i].perm.ps ==>
                        self.l2_rev_map@.dom().contains(p) 
                        && 
                        0 <= self.l2_rev_map@[p].0 < 512 && 0 <= self.l2_rev_map@[p].1 < 512 
                        &&
                        self.spec_resolve_mapping_l3(self.l2_rev_map@[p].0,self.l2_rev_map@[p].1).is_Some() && self.spec_resolve_mapping_l3(self.l2_rev_map@[p].0,self.l2_rev_map@[p].1).get_Some_0().addr == p
                        &&
                        self.spec_resolve_mapping_l3(self.l2_rev_map@[p].0,self.l2_rev_map@[p].1).is_Some() && self.spec_resolve_mapping_l3(self.l2_rev_map@[p].0,self.l2_rev_map@[p].1).get_Some_0().addr == p 
                        &&
                        self.spec_resolve_mapping_2M_l2(self.l2_rev_map@[p].0,self.l2_rev_map@[p].1,i).is_Some() && self.spec_resolve_mapping_2M_l2(self.l2_rev_map@[p].0,self.l2_rev_map@[p].1,i).get_Some_0().addr == self.l2_tables@[p].value()[i].addr 
                        &&
                        self.mapping_2M@.dom().contains(spec_index2va((self.l2_rev_map@[p].0,self.l2_rev_map@[p].1,i,0))) 
                        &&
                        self.mapping_2M@[spec_index2va((self.l2_rev_map@[p].0,self.l2_rev_map@[p].1,i,0))].addr == self.l2_tables@[p].value()[i].addr 
                        &&
                        self.mapping_2M().dom().contains(spec_index2va((self.l2_rev_map@[p].0,self.l2_rev_map@[p].1,i,0))) 
            );
        };
        assert(
            forall|p: PageMapPtr, i: L1Index| 
            #![trigger self.l1_tables@[p].value()[i]]
            self.l1_tables@.dom().contains(p) && 0 <= i < 512 && self.l1_tables@[p].value()[i].perm.present ==>
                self.mapped_4K_pages().contains(self.l1_tables@[p].value()[i].addr)
        ) by {
            assert(forall|p: PageMapPtr, i: L1Index| 
                #![trigger self.l1_tables@[p].value()[i]]
                        self.l1_tables@.dom().contains(p) && 0 <= i < 512 && self.l1_tables@[p].value()[i].perm.present ==>
                        self.l1_rev_map@.dom().contains(p) && 
                        0<=self.l1_rev_map@[p].0<512 && 0<=self.l1_rev_map@[p].1<512 && 0<=self.l1_rev_map@[p].2<512 &&
                        self.spec_resolve_mapping_l2(self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2).is_Some() && self.spec_resolve_mapping_l2(self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2).get_Some_0().addr == p
                        &&
                        self.spec_resolve_mapping_l2(self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2).is_Some() && self.spec_resolve_mapping_l2(self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2).get_Some_0().addr == p 
                        &&
                        self.spec_resolve_mapping_4K_l1(self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2,i).is_Some() && self.spec_resolve_mapping_4K_l1(self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2,i).get_Some_0().addr == self.l1_tables@[p].value()[i].addr 
                        &&
                        self.mapping_4K@.dom().contains(spec_index2va((self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2,i))) 
                        &&
                        self.mapping_4K@[spec_index2va((self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2,i))].addr == self.l1_tables@[p].value()[i].addr 
                        &&
                        self.mapping_4K().dom().contains(spec_index2va((self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2,i))) 
                        // &&
                        // self.mapping_2M()[spec_index2va((l4i,l3i,l2i,i))].addr == self.l2_tables@[p].value()[i].addr 
                        // &&
                        // self.mapped_2M_pages().contains(self.l2_tables@[p].value()[i].addr)
            );
        };
    }

}
}