assert(forall|p: PageMapPtr|
    self.l2_tables@.dom().contains(p) ==>
        exists|l4i: L4Index, l3i:L3Index|
            #![trigger self.spec_resolve_mapping_l3(l4i, l3i)]
            0 <= l4i < 512 && 0 <= l3i < 512 &&
            self.spec_resolve_mapping_l3(l4i, l3i).is_Some() && self.spec_resolve_mapping_l3(l4i, l3i).get_Some_0().addr == p);
// L2 mappings are unique within);
assert(forall|p: PageMapPtr, l2i: L2Index, l2j: L2Index| 
    #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[l2i].perm.present, self.l2_tables@[p].value()[l2j].perm.present, self.l2_tables@[p].value()[l2i].perm.ps, self.l2_tables@[p].value()[l2j].perm.ps]
    self.l2_tables@.dom().contains(p) && l2i != l2j && 0 <= l2i < 512 && 0 <= l2j < 512 && self.l2_tables@[p].value()[l2i].perm.present && self.l2_tables@[p].value()[l2j].perm.present && 
    !self.l2_tables@[p].value()[l2i].perm.ps && !self.l2_tables@[p].value()[l2j].perm.ps 
        ==>
        self.l2_tables@[p].value()[l2i].addr != self.l2_tables@[p].value()[l2j].addr);
// L2 mappings are unique);
assert(forall|pi: PageMapPtr, pj: PageMapPtr, l2i: L2Index, l2j: L2Index|
    #![trigger self.l2_tables@.dom().contains(pi), self.l2_tables@.dom().contains(pj),
        self.l2_tables@[pi].value()[l2i].perm.present, self.l2_tables@[pj].value()[l2j].perm.present,
        self.l2_tables@[pi].value()[l2i].perm.ps, self.l2_tables@[pj].value()[l2j].perm.ps]
    pi != pj && self.l2_tables@.dom().contains(pi) && self.l2_tables@.dom().contains(pj) && 0 <= l2i < 512 && 0 <= l2j < 512 && self.l2_tables@[pi].value()[l2i].perm.present && self.l2_tables@[pj].value()[l2j].perm.present && 
    !self.l2_tables@[pi].value()[l2i].perm.ps && !self.l2_tables@[pj].value()[l2j].perm.ps
        ==>
        self.l2_tables@[pi].value()[l2i].addr != self.l2_tables@[pj].value()[l2j].addr);
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
        self.cr3 != self.l2_tables@[p].value()[i].addr);
// all l2 points to valid l1 tables);
assert(forall|p: PageMapPtr, i: L2Index| 
    #![trigger self.l2_tables@.dom().contains(p), self.l1_tables@.dom().contains(self.l2_tables@[p].value()[i].addr), self.l2_tables@[p].value()[i].perm.present, self.l2_tables@[p].value()[i].perm.ps] 
    self.l2_tables@.dom().contains(p) && 0 <= i < 512 && self.l2_tables@[p].value()[i].perm.present && !self.l2_tables@[p].value()[i].perm.ps ==>
        self.l1_tables@.dom().contains(self.l2_tables@[p].value()[i].addr));