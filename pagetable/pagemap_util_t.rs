use vstd::prelude::*;

verus! {
use crate::define::*;
use crate::array::*;
use vstd::simple_pptr::*;
use crate::util::page_ptr_util_u::*;
use crate::pagetable::pagetable_util::*;
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
ensures
    page_map_perm.addr() == page_map_ptr,
    page_map_perm.is_init(),
    page_map_perm.value().wf(),
    page_map_perm.value()@ =~= old(page_map_perm).value()@.update(index as int,value),
{

}

}