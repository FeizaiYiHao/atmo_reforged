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
 
    pub proof fn outside_of_closure_imply_outside_of_every_level(&self, target_p: PageMapPtr)
    requires
        self.wf(),
        self.page_closure().contains(target_p) == false, 
        self.page_not_mapped(target_p),
    ensures       
        forall|i: L4Index|
            #![trigger self.l4_table@[self.cr3].value()[i].addr ] 
            0 <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present ==> 
                self.l4_table@[self.cr3].value()[i].addr != target_p,
        forall|p: PageMapPtr, i: L3Index| 
            #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present ]
            0 <= i < 512 && self.l3_tables@.dom().contains(p) && self.l3_tables@[p].value()[i].perm.present && !self.l3_tables@[p].value()[i].perm.ps ==> 
                self.l3_tables@[p].value()[i].addr != target_p,
{
    assert(
        forall|p: PageMapPtr, i: L3Index| 
            #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present ]
            0 <= i < 512 && self.l3_tables@.dom().contains(p) && self.l3_tables@[p].value()[i].perm.present && self.l3_tables@[p].value()[i].perm.ps ==> 
            exists|l4i: L4Index|
                        #![trigger self.spec_resolve_mapping_1G_l3(l4i, i).is_Some()]
                        0 <= l4i < 512 
                        && 
                        self.spec_resolve_mapping_1G_l3(l4i, i).is_Some()
                        && 
                        self.spec_resolve_mapping_1G_l3(l4i, i).get_Some_0().addr == self.l3_tables@[p].value()[i].addr
                        &&
                        self.mapping_1G().dom().contains(spec_index2va((l4i,i,0,0))) 
                        && 
                        self.mapping_1G()[spec_index2va((l4i,i,0,0))].addr == self.l3_tables@[p].value()[i].addr
    );
}

}
}