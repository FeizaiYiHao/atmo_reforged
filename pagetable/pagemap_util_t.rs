use vstd::prelude::*;

verus! {
use crate::define::*;
// use crate::array::*;
use vstd::simple_pptr::*;
use crate::util::page_ptr_util_u::*;
// use crate::pagetable::pagetable_util::*;
use crate::pagetable::entry::*;
use crate::pagetable::pagemap::*;
use core::mem::MaybeUninit;


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
    unsafe{
        let uptr = page_map_ptr as *mut MaybeUninit<PageMap>;
        (*uptr).assume_init_mut().set(index, value);
    }
}

#[verifier(external_body)]
pub fn page_perm_to_page_map(page_ptr: PagePtr, Tracked(page_perm): Tracked<PagePerm4k>) -> (ret: (PageMapPtr, Tracked<PointsTo<PageMap>>))
requires
    page_perm.is_init(),
    page_perm.addr() == page_ptr,
ensures
    ret.0 == page_ptr,
    ret.1@.addr() == ret.0,
    ret.1@.is_init(),
    ret.1@.value().wf(),
    forall|i:usize|
        #![trigger ret.1@.value()[i].is_empty()]
        0<=i<512 ==> ret.1@.value()[i].is_empty(),
{
    (page_ptr, Tracked::assume_new())
}

}