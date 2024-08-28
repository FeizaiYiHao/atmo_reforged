&&&
forall|p: PageMapPtr|
    #![trigger self.l3_tables@.dom().contains(p)]
    self.l3_tables@.dom().contains(p) ==>
        exists|l4i:L4Index|
            #![trigger self.l4_table@[self.cr3].value()[l4i].addr]
            0 <= l4i < 512 && self.l4_table@[self.cr3].value()[l4i].perm.present && !self.l4_table@[self.cr3].value()[l4i].perm.ps &&
            self.l4_table@[self.cr3].value()[l4i].addr == p
//L3 tables unique within);
assert(forall|p: PageMapPtr, l3i: L3Index, l3j: L3Index| 
    #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[l3i].addr, self.l3_tables@[p].value()[l3j].addr, self.l3_tables@[p].value()[l3i].perm.ps, self.l3_tables@[p].value()[l3j].perm.ps, self.l3_tables@[p].value()[l3i].addr, self.l3_tables@[p].value()[l3j].addr]
    self.l3_tables@.dom().contains(p) && l3i != l3j && 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[p].value()[l3i].perm.present && self.l3_tables@[p].value()[l3j].perm.present 
        && !self.l3_tables@[p].value()[l3i].perm.ps && !self.l3_tables@[p].value()[l3j].perm.ps 
        ==> 
        self.l3_tables@[p].value()[l3i].addr != self.l3_tables@[p].value()[l3j].addr
//L3 tables are disjoint        
&&&        
forall|pi: PageMapPtr, pj: PageMapPtr, l3i: L3Index, l3j: L3Index|
    #![trigger self.l3_tables@.dom().contains(pi), self.l3_tables@.dom().contains(pj), self.l3_tables@[pi].value()[l3i].addr, self.l3_tables@[pj].value()[l3j].addr, self.l3_tables@[pi].value()[l3i].perm.ps, self.l3_tables@[pj].value()[l3j].perm.ps, self.l3_tables@[pi].value()[l3i].perm.present, self.l3_tables@[pj].value()[l3j].perm.present]
    pi != pj && self.l3_tables@.dom().contains(pi) && self.l3_tables@.dom().contains(pj) && 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[pi].value()[l3i].perm.present && self.l3_tables@[pj].value()[l3j].perm.present 
        && !self.l3_tables@[pi].value()[l3i].perm.ps && !self.l3_tables@[pj].value()[l3j].perm.ps
        ==>
        self.l3_tables@[pi].value()[l3i].addr != self.l3_tables@[pj].value()[l3j].addr
//L3 tables does not map to L4 or L1        );
assert(forall|p: PageMapPtr, i: L3Index| 
    #![trigger self.l3_tables@.dom().contains(i), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
    #![trigger self.l3_tables@.dom().contains(i), self.l3_tables@[p].value()[i].perm.present, self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
    #![trigger self.l3_tables@.dom().contains(i), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].addr] 
    self.l3_tables@.dom().contains(i) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.present ==>
        self.l3_tables@.dom().contains(self.l3_tables@[p].value()[i].addr) == false
        &&
        self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr) == false
        &&
        self.cr3 != self.l3_tables@[p].value()[i].addr);
// 1G hugepages have no entries in l2);
assert(forall|p: PageMapPtr, i: L3Index| 
    #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
    #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
    #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
    #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].addr] 
    self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.ps ==>
        self.l3_tables@.dom().contains(self.l3_tables@[p].value()[i].addr) == false
        &&
        self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr) == false
        &&
        self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr) == false
        &&
        self.cr3 != self.l3_tables@[p].value()[i].addr);
// all l3 points to valid l2 tables);
assert(forall|p: PageMapPtr, i: L3Index| 
    #![trigger self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].perm.ps ] 
    #![trigger self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
    self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.present && !self.l3_tables@[p].value()[i].perm.ps ==>
        self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr));