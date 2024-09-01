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
            #![trigger self.mapped_1g_pages().contains(self.l3_tables@[p].value()[i].addr)]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.present && self.l3_tables@[p].value()[i].perm.ps ==>
                self.mapped_1g_pages().contains(self.l3_tables@[p].value()[i].addr),
            forall|p: PageMapPtr, i: L2Index| 
            #![trigger self.mapped_2m_pages().contains(self.l2_tables@[p].value()[i].addr)]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512 && self.l2_tables@[p].value()[i].perm.present && self.l2_tables@[p].value()[i].perm.ps ==>
                self.mapped_2m_pages().contains(self.l2_tables@[p].value()[i].addr),
            forall|p: PageMapPtr, i: L2Index| 
            #![trigger self.mapped_4k_pages().contains(self.l1_tables@[p].value()[i].addr)]
            self.l1_tables@.dom().contains(p) && 0 <= i < 512 && self.l1_tables@[p].value()[i].perm.present ==>
                self.mapped_4k_pages().contains(self.l1_tables@[p].value()[i].addr),
    {
        assert(
            forall|p: PageMapPtr, i: L3Index| 
            // #![auto]
            #![trigger self.l3_tables@[p].value()[i]]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.present && self.l3_tables@[p].value()[i].perm.ps ==>
                self.mapped_1g_pages().contains(self.l3_tables@[p].value()[i].addr)
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
                            self.spec_resolve_mapping_1g_l3(self.l3_rev_map@[p],i).is_Some() && self.spec_resolve_mapping_1g_l3(self.l3_rev_map@[p],i).get_Some_0().addr == self.l3_tables@[p].value()[i].addr 
                            &&
                            self.mapping_1g@.dom().contains(spec_index2va((self.l3_rev_map@[p],i,0,0))) 
                            &&
                            self.mapping_1g@[spec_index2va((self.l3_rev_map@[p],i,0,0))].addr == self.l3_tables@[p].value()[i].addr 
                            &&
                            self.mapping_1g().dom().contains(spec_index2va((self.l3_rev_map@[p],i,0,0))) 
                            &&
                            self.mapping_1g()[spec_index2va((self.l3_rev_map@[p],i,0,0))].addr == self.l3_tables@[p].value()[i].addr 
                            &&
                            self.mapped_1g_pages().contains(self.l3_tables@[p].value()[i].addr)
                );
            };

        assert(
            forall|p: PageMapPtr, i: L2Index| 
            #![trigger self.l2_tables@[p].value()[i]]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512 && self.l2_tables@[p].value()[i].perm.present && self.l2_tables@[p].value()[i].perm.ps ==>
                self.mapped_2m_pages().contains(self.l2_tables@[p].value()[i].addr)
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
                        self.spec_resolve_mapping_2m_l2(self.l2_rev_map@[p].0,self.l2_rev_map@[p].1,i).is_Some() && self.spec_resolve_mapping_2m_l2(self.l2_rev_map@[p].0,self.l2_rev_map@[p].1,i).get_Some_0().addr == self.l2_tables@[p].value()[i].addr 
                        &&
                        self.mapping_2m@.dom().contains(spec_index2va((self.l2_rev_map@[p].0,self.l2_rev_map@[p].1,i,0))) 
                        &&
                        self.mapping_2m@[spec_index2va((self.l2_rev_map@[p].0,self.l2_rev_map@[p].1,i,0))].addr == self.l2_tables@[p].value()[i].addr 
                        &&
                        self.mapping_2m().dom().contains(spec_index2va((self.l2_rev_map@[p].0,self.l2_rev_map@[p].1,i,0))) 
            );
        };
        assert(
            forall|p: PageMapPtr, i: L1Index| 
            #![trigger self.l1_tables@[p].value()[i]]
            self.l1_tables@.dom().contains(p) && 0 <= i < 512 && self.l1_tables@[p].value()[i].perm.present ==>
                self.mapped_4k_pages().contains(self.l1_tables@[p].value()[i].addr)
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
                        self.spec_resolve_mapping_4k_l1(self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2,i).is_Some() && self.spec_resolve_mapping_4k_l1(self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2,i).get_Some_0().addr == self.l1_tables@[p].value()[i].addr 
                        &&
                        self.mapping_4k@.dom().contains(spec_index2va((self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2,i))) 
                        &&
                        self.mapping_4k@[spec_index2va((self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2,i))].addr == self.l1_tables@[p].value()[i].addr 
                        &&
                        self.mapping_4k().dom().contains(spec_index2va((self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2,i))) 
                        // &&
                        // self.mapping_2m()[spec_index2va((l4i,l3i,l2i,i))].addr == self.l2_tables@[p].value()[i].addr 
                        // &&
                        // self.mapped_2m_pages().contains(self.l2_tables@[p].value()[i].addr)
            );
        };
    }
    pub proof fn internal_resolve_disjoint(&self)
        requires
            self.wf(),
        ensures
            forall|l4i: L4Index, l4j: L4Index| 
                #![trigger self.spec_resolve_mapping_l4(l4i), self.spec_resolve_mapping_l4(l4j)]
                0 <= l4i < 512 && 0 <= l4j < 512 && l4i != l4j && self.spec_resolve_mapping_l4(l4i).is_Some() && self.spec_resolve_mapping_l4(l4j).is_Some() ==>
                    self.spec_resolve_mapping_l4(l4i).get_Some_0().addr != self.spec_resolve_mapping_l4(l4j).get_Some_0().addr,
            forall|l4i: L4Index, l3i: L3Index, l4j: L4Index, l3j: L3Index| 
                #![trigger self.spec_resolve_mapping_l3(l4i,l3i), self.spec_resolve_mapping_l3(l4j,l3j)]
                0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l4j < 512 && 0 <= l3j < 512 && (l4i,l3i) != (l4j,l3j) && self.spec_resolve_mapping_l3(l4i,l3i).is_Some() && self.spec_resolve_mapping_l3(l4j,l3j).is_Some() ==>
                    self.spec_resolve_mapping_l3(l4i,l3i).get_Some_0().addr != self.spec_resolve_mapping_l3(l4j,l3j).get_Some_0().addr,
            forall|l4i: L4Index, l3i: L3Index, l2i: L3Index, l4j: L4Index, l3j: L3Index, l2j: L2Index| 
            #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i), self.spec_resolve_mapping_l2(l4j,l3j,l2j)]
                0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l4j < 512 && 0 <= l3j < 512 && 0 <= l2j < 512 && (l4i,l3i,l2i) != (l4j,l3j,l2j) && self.spec_resolve_mapping_l2(l4i,l3i,l2i).is_Some() && self.spec_resolve_mapping_l2(l4j,l3j,l2j).is_Some() ==>
                    self.spec_resolve_mapping_l2(l4i,l3i,l2i).get_Some_0().addr != self.spec_resolve_mapping_l2(l4j,l3j,l2j).get_Some_0().addr
    {
        assert(
            forall|l4i: L4Index, l4j: L4Index| 
                #![trigger self.spec_resolve_mapping_l4(l4i), self.spec_resolve_mapping_l4(l4j)]
                0 <= l4i < 512 && 0 <= l4j < 512 && l4i != l4j && self.spec_resolve_mapping_l4(l4i).is_Some() && self.spec_resolve_mapping_l4(l4j).is_Some() ==>
                    self.spec_resolve_mapping_l4(l4i).get_Some_0().addr != self.spec_resolve_mapping_l4(l4j).get_Some_0().addr
        );

        assert(
            forall|l3pi: PageMapPtr, l3i: L3Index,l3pj: PageMapPtr, l3j: L3Index| 
                #![auto]
                self.l3_tables@.dom().contains(l3pi) && 0 <= l3i < 512 && self.l3_tables@.dom().contains(l3pj) && 0 <= l3j < 512 && (l3pi,l3i) != (l3pj,l3j)
                && self.l3_tables@[l3pi].value()[l3i].perm.present && !self.l3_tables@[l3pi].value()[l3i].perm.ps
                && self.l3_tables@[l3pj].value()[l3j].perm.present && !self.l3_tables@[l3pj].value()[l3j].perm.ps
                ==>
                self.l3_tables@[l3pi].value()[l3i].addr != self.l3_tables@[l3pj].value()[l3j].addr
        );

        assert(
            forall|l4i: L4Index, l3i: L3Index, l4j: L4Index, l3j: L3Index| 
                #![auto]
                0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l4j < 512 && 0 <= l3j < 512 && (l4i,l3i) != (l4j,l3j) && self.spec_resolve_mapping_l3(l4i,l3i).is_Some() && self.spec_resolve_mapping_l3(l4j,l3j).is_Some() ==>
                    self.spec_resolve_mapping_l3(l4i,l3i).get_Some_0().addr != self.spec_resolve_mapping_l3(l4j,l3j).get_Some_0().addr
        );
        assert(
            forall|l2pi: PageMapPtr, l2i: L2Index,l2pj: PageMapPtr, l2j: L2Index| 
                #![auto]
                self.l2_tables@.dom().contains(l2pi) && 0 <= l2i < 512 && self.l2_tables@.dom().contains(l2pj) && 0 <= l2j < 512 && (l2pi,l2i) != (l2pj,l2j)
                && self.l2_tables@[l2pi].value()[l2i].perm.present && !self.l2_tables@[l2pi].value()[l2i].perm.ps
                && self.l2_tables@[l2pj].value()[l2j].perm.present && !self.l2_tables@[l2pj].value()[l2j].perm.ps
                ==>
                self.l2_tables@[l2pi].value()[l2i].addr != self.l2_tables@[l2pj].value()[l2j].addr
        );

        assert(
            forall|l4i: L4Index, l3i: L3Index, l2i: L3Index, l4j: L4Index, l3j: L3Index, l2j: L2Index| 
                #![auto]
                0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l4j < 512 && 0 <= l3j < 512 && 0 <= l2j < 512 && (l4i,l3i,l2i) != (l4j,l3j,l2j) && self.spec_resolve_mapping_l2(l4i,l3i,l2i).is_Some() && self.spec_resolve_mapping_l2(l4j,l3j,l2j).is_Some() ==>
                    self.spec_resolve_mapping_l2(l4i,l3i,l2i).get_Some_0().addr != self.spec_resolve_mapping_l2(l4j,l3j,l2j).get_Some_0().addr
        );

    }
}
}