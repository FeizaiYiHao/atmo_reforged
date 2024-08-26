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

    // pub fn create_4K_entry_l4(&mut self, l4i, page_map_ptr: PAddr Tracked(page_map_perm): Tracked<PointsTo<PageMap>>)


}

}