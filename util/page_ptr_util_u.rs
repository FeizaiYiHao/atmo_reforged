use vstd::prelude::*;
verus! {
use crate::define::*;
use crate::lemma::lemma_t::*;

pub fn va_perm_bits_valid(perm:usize) -> (ret:bool)
    ensures
        ret == spec_va_perm_bits_valid(perm),
{
    perm == READ
    ||
    perm == READ_WRITE
    ||
    perm == READ_EXECUTE
    ||
    perm == READ_WRITE_EXECUTE
}


pub open spec fn spec_va_perm_bits_valid(perm:usize) -> bool{
    perm == READ
    ||
    perm == READ_WRITE
    ||
    perm == READ_EXECUTE
    ||
    perm == READ_WRITE_EXECUTE
}


pub open spec fn spec_page_ptr2page_index(ptr: usize) -> usize
    recommends
        page_ptr_valid(ptr),
{
    (ptr/4096usize) as usize
}


pub open spec fn spec_page_index2page_ptr(i:usize) -> usize
    recommends
        page_index_valid(i),
{
    (i * 4096) as usize
}

#[verifier(when_used_as_spec(spec_page_ptr2page_index))]
pub fn page_ptr2page_index(ptr: usize) -> (ret: usize)
    requires
        ptr % 4096 == 0,
    ensures
        ret == spec_page_ptr2page_index(ptr)
{
    return ptr/4096usize;
}

#[verifier(when_used_as_spec(spec_page_index2page_ptr))]
pub fn page_index2page_ptr(i: usize) -> (ret:usize)
    requires
        0<=i<NUM_PAGES,
    ensures
        ret == spec_page_index2page_ptr(i),
{
    proof{
        lemma_usize_u64(MAX_USIZE);
    }
    i * 4096usize
}

pub open spec fn pa_valid(v: PAddr) -> bool
{
    v & (!PA_MASK) as usize == 0
}

pub open spec fn page_ptr_valid(ptr: usize) -> bool
{
    ((ptr % 4096) == 0)
    &&
    ((ptr/4096) < NUM_PAGES)
}

pub open spec fn page_index_valid(index: usize) -> bool
{
    (0<=index<NUM_PAGES)
}


}