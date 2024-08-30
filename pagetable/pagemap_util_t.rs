use vstd::prelude::*;

verus! {
use crate::define::*;
// use crate::array::*;
use vstd::simple_pptr::*;
use crate::util::page_ptr_util_u::*;
// use crate::pagetable::pagetable_util::*;
use crate::pagetable::entry::*;
use crate::pagetable::pagemap::*;


#[verifier(external_body)]
pub fn page_map_set(page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>, index:usize, value:PageEntry)
requires
    old(page_map_perm).addr() == page_map_ptr,
    old(page_map_perm).is_init(),
    old(page_map_perm).value().wf(),
    value.perm.present ==> MEM_valid(value.addr),
    value.perm.present == false ==> value.is_empty(),
    0<=index<512,
ensures
    page_map_perm.addr() == page_map_ptr,
    page_map_perm.is_init(),
    page_map_perm.value().wf(),
    forall|i: usize|
        #![trigger page_map_perm.value()[i]]
        0 <= i < 512 && i != index ==>
        page_map_perm.value()[i] =~= old(page_map_perm).value()[i],
    page_map_perm.value()[index] =~= value
{
}

}