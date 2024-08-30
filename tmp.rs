assert(
    forall|l1pi: PageMapPtr, l1i: L1Index,l1pj: PageMapPtr, l1j: L1Index| 
        #![auto]
        self.l1_tables@.dom().contains(l1pi) && 0 <= l1i < 511 && self.l1_tables@.dom().contains(l1pj) && 0 <= l1j < 511 && (l1pi,l1i) != (l1pj,l1j)
        && self.l1_tables@[l1pi].value()[l1i].perm.present
        && self.l1_tables@[l1pj].value()[l1j].perm.present
        ==>
        self.l1_tables@[l1pi].value()[l1i].addr != self.l1_tables@[l1pj].value()[l1j].addr
);