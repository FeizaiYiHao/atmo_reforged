use vstd::prelude::*;

verus! {
use crate::define::*;
use crate::util::page_ptr_util_u::*;

#[derive(Clone, Copy)]
pub struct VaRange4K{
    pub start:VAddr,
    pub len:usize,

    pub view: Ghost<Seq<VAddr>>,
}

pub open spec fn spec_va_range_disjoint(va_range_1:&VaRange4K, va_range_2:&VaRange4K) -> bool
{
    forall|i:int, j:int|
        0 <= i < va_range_1.len && 0 <= j < va_range_2.len 
        ==>
        va_range_1@[i] != va_range_2@[j]
}

#[verifier(when_used_as_spec(spec_va_range_disjoint))]
#[verifier(external_body)]
pub fn va_range_disjoint(va_range_1:&VaRange4K, va_range_2:&VaRange4K) -> (ret:bool)
    requires
        va_range_1.wf(),
        va_range_2.wf(),
    ensures
        ret == va_range_disjoint(va_range_1, va_range_2),
{
    proof{
        va_range_lemma();
        va_range_1.va_range_lemma();
        va_range_2.va_range_lemma();
    }
    if va_range_1.start > va_range_2.start{
        if va_range_2.start + va_range_2.len * 4096 < va_range_1.start{
            assert(
                forall|i:usize, j:usize|
                #![auto]
                0 <= i < va_range_1.len && 0 <= j < va_range_2.len 
                ==>
                va_range_2@[j as int] == va_range_2.start + j * 4096
                &&
                va_range_1@[i as int] == va_range_1.start + i * 4096
                &&
                va_range_2.start + j * 4096 < va_range_1.start + i * 4096
            );
            return true;
        }else{
            return false;
        }
    }else if va_range_1.start == va_range_2.start{
        return false;
    }else{
        if va_range_1.start + va_range_1.len < va_range_2.start{
            return true;
        }else{
            return false;
        }
    }
}


impl VaRange4K{
    #[verifier(external_body)]
    pub proof fn va_range_lemma(&self) 
        requires
            self.wf(),
        ensures
        forall|i:usize|
            0 <= i < self.len
            ==>
            self@[i as int] == spec_va_add_range(self.start, i),
        forall|i:usize|
            0 <= i < self.len
            ==>
            self@[i as int] == self.start + i * 4096 //@Xiangdong Prove this 
    {}

    pub closed spec fn view(&self) -> Seq<VAddr>
    {
        self.view@
    }
    pub open spec fn wf(&self) -> bool
    {
        &&&
        self.start + self.len * 4096 < usize::MAX
        &&&
        spec_va_4k_valid(self.start)
        &&&
        self@.len() == self.len
        &&&
        self@.no_duplicates()
        &&&
        forall|i:int|
        #![trigger self@[i]]
        0 <= i < self.len
        ==>
        spec_va_4k_valid(self@[i])
        &&&
        self.view_match_spec()
    } 
    pub closed spec fn view_match_spec(&self) -> bool{
        &&&
        forall|i:usize|
        #![trigger spec_va_add_range(self.start, i)]
        0 <= i < self.len 
        ==>
        spec_va_add_range(self.start, i) == self@[i as int]
    }
    pub fn new(va:VAddr, len:usize) -> (ret:Self)
        requires
            spec_va_4k_valid(va),
            va_4k_range_valid(va,len),
            va < usize::MAX - len * 4096,
        ensures
            ret.wf(),
            ret.start == va,
            ret.len == len,
    {
        proof{
            va_range_lemma();
        }
        let seq = Ghost(Seq::new(len as nat, |i: int| spec_va_add_range(va, i as usize)));
        Self{start:va, len:len, view: seq}
        
    }

    pub fn index(&self, i:usize) -> (ret:VAddr)
        requires
            self.wf(),
            0 <= i < self.len,
        ensures
            ret == self@[i as int]
    {
        va_add_range(self.start, i)
    }
}

}