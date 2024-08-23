use vstd::prelude::*;
verus! {
// use crate::define::*;
use crate::util::page_ptr_util_u::*;

pub proof fn page_ptr_valid_imply_pa_valid(v:usize)
    requires
        page_ptr_valid(v),
    ensures
        pa_valid(v),
{
    assert(v & (!0x0000_ffff_ffff_f000u64) as usize == 0) by (bit_vector) requires     
    ((v % 4096) == 0)
    &&
    ((v / 4096) < 2*1024*1024);
}

}