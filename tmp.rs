assert(forall|va: VAddr| 
    #![trigger va_1G_valid(va), self.mapping_1G@.dom().contains(va)]
        self.mapping_1G@.dom().contains(va) ==> va_1G_valid(va));
assert(forall|l4i: L4Index,l3i: L3Index| 
    #![trigger self.mapping_1G@[spec_index2va((l4i,l3i,0,0))]]
    #![trigger self.spec_resolve_mapping_1G_l3(l4i,l3i)]
    0 <= l4i < 512 && 0 <= l3i < 512 ==>
        self.mapping_1G@.dom().contains(spec_index2va((l4i,l3i,0,0))) == self.spec_resolve_mapping_1G_l3(l4i,l3i).is_Some());
assert(forall|l4i: L4Index,l3i: L3Index| 
    #![trigger self.mapping_1G@[spec_index2va((l4i,l3i,0,0))]]
    #![trigger self.spec_resolve_mapping_1G_l3(l4i,l3i)]
    0 <= l4i < 512 && 0 <= l3i < 512 && self.spec_resolve_mapping_1G_l3(l4i,l3i).is_Some()
        ==> self.mapping_1G@[spec_index2va((l4i,l3i,0,0))].addr == self.spec_resolve_mapping_1G_l3(l4i,l3i).get_Some_0().addr &&
            self.mapping_1G@[spec_index2va((l4i,l3i,0,0))].write == self.spec_resolve_mapping_1G_l3(l4i,l3i).get_Some_0().perm.write &&
            self.mapping_1G@[spec_index2va((l4i,l3i,0,0))].execute_disable == self.spec_resolve_mapping_1G_l3(l4i,l3i).get_Some_0().perm.execute_disable);
assert(forall|va: VAddr| 
    #![trigger self.mapping_1G@.dom().contains(va), page_ptr_1G_valid(self.mapping_1G@[va].addr)]
        self.mapping_1G@.dom().contains(va) ==>
        page_ptr_1G_valid(self.mapping_1G@[va].addr));