assert(forall|p: PageMapPtr|
    #![trigger self.l1_tables@.dom().contains(p)] 
    self.l1_tables@.dom().contains(p) ==>
        exists|l4i: L4Index, l3i:L3Index, l2i:L2Index|
            #![trigger self.spec_resolve_mapping_l2(l4i, l3i, l2i).is_Some(), self.spec_resolve_mapping_l2(l4i, l3i, l2i).get_Some_0().addr]
            0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 &&
            self.spec_resolve_mapping_l2(l4i, l3i, l2i).is_Some() && self.spec_resolve_mapping_l2(l4i, l3i, l2i).get_Some_0().addr == p);
// no l1 tables map to other levels
assert(forall|p: PageMapPtr, i: L1Index| 
    #![trigger self.l1_tables@[p].value()[i].perm.present, self.l2_tables@.dom().contains(self.l1_tables@[p].value()[i].addr)] 
    #![trigger self.l1_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l1_tables@[p].value()[i].addr)] 
    #![trigger self.l1_tables@[p].value()[i].perm.present, self.l1_tables@[p].value()[i].addr] 
    self.l1_tables@.dom().contains(p) && 0 <= i < 512 && self.l1_tables@[p].value()[i].perm.present ==>
        self.l2_tables@.dom().contains(self.l1_tables@[p].value()[i].addr) == false
        &&
        self.l3_tables@.dom().contains(self.l1_tables@[p].value()[i].addr) == false
        &&
        self.cr3 != self.l1_tables@[p].value()[i].addr);
// no hugepage in l1
assert(forall|p: PageMapPtr, i: L1Index| 
    #![trigger self.l1_tables@[p].value()[i].perm.ps] 
    self.l1_tables@.dom().contains(p) && 0 <= i < 512 && self.l1_tables@[p].value()[i].perm.present ==>
        ! self.l1_tables@[p].value()[i].perm.ps);