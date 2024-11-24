use vstd::prelude::*;
verus! {
use crate::array::Array;
use vstd::set_lib::lemma_len_subset;


/// A set of intergers from 0 to N - 1.
pub struct ArraySet<const N: usize> {
    pub data: Array<bool, N>,
    pub len: usize,

    pub set: Ghost<Set<usize>>,
}

impl <const N: usize> ArraySet<N> {

    pub fn new() -> (ret:Self)
        ensures
            ret.wf(),
            ret@ == Set::<usize>::empty(),
    {
        let mut ret = Self{
            data: Array::new(),
            len: 0,
            set:Ghost(Set::<usize>::empty()),
        };
        for i in 0..N
            invariant
                0<=i<=N,
                ret.data.wf(),
                ret.len == 0,
                ret.set@ == Set::<usize>::empty(),
                forall|j:int|
                    0<=j<i ==> ret.data@[j] == false,
        {
            ret.data.set(i,false);
        }
        ret
    }

    pub fn init(&mut self)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self@ == Set::<usize>::empty(),
    {
            self.len = 0;
            self.set = Ghost(Set::<usize>::empty());
        for i in 0..N
            invariant
                0<=i<=N,
                self.data.wf(),
                self.len == 0,
                self.set@ == Set::<usize>::empty(),
                forall|j:int|
                    0<=j<i ==> self.data@[j] == false,
        {
            self.data.set(i,false);
        }
    }

    pub closed spec fn view(&self) -> Set<usize>{
        self.set@
    }

    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (ret:usize)
        requires
            self.wf(),
        ensures
            ret == self.set@.len(),
    {
        self.len
    }

    pub closed spec fn spec_len(&self) -> usize{
        self.set@.len() as usize
    }

    pub closed spec fn wf(&self) -> bool{
        &&&
        self.data.wf()
        &&&
        self.set@.finite()
        &&&
        0 <= self.len <= N
        &&&
        forall|i:usize| 
            #![trigger self.data@[i as int]]
            #![trigger self.set@.contains(i)]
            0 <= i < N && self.data@[i as int] ==> self.set@.contains(i)
        &&&
        forall|i:usize| 
            #![trigger self.data@[i as int]]
            #![trigger self.set@.contains(i)]
            self.set@.contains(i) ==> 0 <= i < N && self.data@[i as int]     
        &&&
        self.len == self.set@.len() 
    }

    pub fn insert(&mut self, v:usize)
        requires
            old(self).wf(),
            old(self)@.contains(v) == false,
            0 <= v < N,
        ensures
            self.wf(),
            self@ == old(self)@.insert(v),
    {
        self.data.set(v, true);
        self.set = Ghost(self.set@.insert(v));
        proof{
            let all_value_set = Set::new(|v: usize| 0 <= v < N);
            assume(all_value_set.finite());
            assume(all_value_set.len() == N); // this should be inferred smh by verus...
            assert(
                forall|v: usize| #![auto]
                    self.set@.contains(v) 
                    ==>
                    all_value_set.contains(v)
            );
            lemma_len_subset::<usize>(self.set@, all_value_set);
            assert(self.set@.len() <= N);
        }
        self.len = self.len + 1;
    }

    pub fn remove(&mut self, v:usize)
        requires
            old(self).wf(),
            old(self)@.contains(v) == true,
        ensures
            self.wf(),
            self@ == old(self)@.remove(v),
    {
        self.data.set(v, false);
        self.len = self.len - 1;
        self.set = Ghost(self.set@.remove(v));
    }
}

}