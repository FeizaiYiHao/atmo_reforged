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
        forall|s: Seq<A>, v: A| 
            #![auto]
            s.push(v).contains(v),
{

}

#[verifier(external_body)]
pub proof fn seq_skip_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A|
            s.contains(v) && s[0] != v && s.no_duplicates() ==> s.skip(1).contains(v),
        forall|s: Seq<A>|
            #![trigger s[0]]
            s.len() > 0 ==> s.contains(s[0]) ,
        forall|s: Seq<A>|
            #![trigger s[0]]
            s.len() > 0 ==> !s.skip(1).contains(s[0]),
        forall|s: Seq<A>, v: A,|
            s[0] == v && s.no_duplicates() ==> s.skip(1) =~= s.remove_value(v),    
{

}

#[verifier(external_body)]
pub proof fn seq_remove_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.subrange(0,i), s.contains(v)]
            s.contains(v) && s[i] != v && s.no_duplicates() ==> s.subrange(0,i).add(s.subrange(i+1, s.len() as int)).contains(v),        
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.subrange(0,i), s.contains(v)]
            s.contains(v) && s[i] == v && s.no_duplicates() ==> s.subrange(0,i).add(s.subrange(i+1, s.len() as int)).contains(v) == false,
        forall|s: Seq<A>, i: int, j:int|
            #![trigger s.subrange(0,i), s[j]]
            0<=j<i ==> s.subrange(0,i).add(s.subrange(i+1, s.len() as int))[j] == s[j],
        forall|s: Seq<A>, i: int, j:int|
            #![trigger s.subrange(0,i), s[j+1]]
            i<=j<s.len() - 1 ==> s.subrange(0,i).add(s.subrange(i+1, s.len() as int))[j] == s[j+1],
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.remove_value(v), s.subrange(0,i)]
            s.contains(v) && s[i] == v && s.no_duplicates() ==> s.subrange(0,i).add(s.subrange(i+1, s.len() as int)) == s.remove_value(v),        
{

}

#[verifier(external_body)]
pub proof fn seq_remove_lemma_2<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A|
            s.contains(v) && x != v && s.no_duplicates() ==> s.remove_value(x).contains(v),        
        forall|s: Seq<A>, v: A, x: A|
            s.contains(v) && x == v && s.no_duplicates() ==> s.remove_value(x).contains(v) == false,     
{

}

}