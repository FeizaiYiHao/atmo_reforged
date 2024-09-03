use vstd::prelude::*;
verus! {
// use crate::define::*;
use crate::util::page_ptr_util_u::*;

pub proof fn page_ptr_valid_imply_MEM_valid(v:usize)
    requires
        page_ptr_valid(v),
    ensures
        MEM_valid(v),
{
    assert(v & (!0x0000_ffff_ffff_f000u64) as usize == 0) by (bit_vector) requires     
    ((v % 4096) == 0)
    &&
    ((v / 4096) < 2*1024*1024);
}

#[verifier(external_body)]
pub proof fn seq_push_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A|
            s.contains(x) ==>  s.push(v).contains(v) && s.push(v).contains(x),
{

}

}