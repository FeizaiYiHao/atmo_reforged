use vstd::prelude::*;

verus! {
use crate::define::*;
use crate::array::*;
use vstd::simple_pptr::*;
use crate::util::page_ptr_util_u::*;

use crate::pagetable::entry::*;
use crate::pagetable::pagemap::*;
use crate::pagetable::pagetable_spec::*;

impl PageTable{

    // pub fn map_4k_page(&mut self, va:VAddr, dst: MapEntry)
    //     requires
    //         old(self).wf(),
    //         old(self).page_closure().contains(dst.addr) == false,
    //         old(self).mapping_4k()[va].is_None(),
    //         page_ptr_valid(dst.addr),
    // {

    // }

    pub fn create_4K_entry_l4(&mut self, l4i: L4Index, page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<PageMap>>)
        requires
            old(self).wf(),
            old(self).spec_resolve_mapping_l4(l4i).is_None(),
            page_ptr_valid(page_map_ptr),
            old(self).page_closure().contains(page_map_ptr) == false,
            0<=l4i<512,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i:int|
                #![trigger page_map_perm.value()@[i].is_empty()]
                0<=i<512 ==> page_map_perm.value()@[i].is_empty(),
    {
        let tracked mut l4_perm = self.l4_table.borrow_mut().tracked_remove(self.cr3);
        assert(l4_perm.value()@[l4i as int].perm.present == false);
        assert(l4_perm.value()@[l4i as int].is_empty());
    }

}

}