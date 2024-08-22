use vstd::prelude::*;
verus! {
use crate::array::Array;



/// A preallocated vector.
pub struct ArrayVec<T, const N: usize> {
    pub data: Array<T, N>,
    pub len: usize,
}

impl<T: Copy, const N: usize> ArrayVec<T, N> {
    pub fn new() -> (ret: Self)
        requires
            0 <= N <= usize::MAX, // Verus doesn't know
        ensures
            ret.wf(),
            ret.len() == 0,
            ret.capacity() == N,
    {
        let ret = Self {
            data: Array::new(),
            len: 0,
        };

        ret
    }

    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (ret: usize)
        requires
            self.wf(),
        ensures
            ret == self.spec_len(),
    {
        self.len
    }

    pub closed spec fn spec_len(&self) -> usize {
        self.len
    }

    #[verifier(when_used_as_spec(spec_capacity))]
    pub const fn capacity(&self) -> (ret: usize)
        ensures
            ret == self.spec_capacity(),
    {
        N
    }

    pub open spec fn spec_capacity(&self) -> usize {
        N
    }

    pub open spec fn view(&self) -> Seq<T>
        recommends self.wf(),
    {
        self.view_until(self.len() as nat)
    }

    pub open spec fn view_until(&self, len: nat) -> Seq<T>
        recommends
            0 <= len <= self.len() as nat,
    {
        self.data@.subrange(0,len as int)
    }

    pub closed spec fn wf(&self) -> bool {
        &&& 0 <= N <= usize::MAX
        &&& self.len() <= self.capacity()
        &&& self.data.wf()
    }


    #[verifier(inline)]
    pub open spec fn spec_index(&self, index: int) -> (ret: T) {
        self@[index]
    }

    pub fn get(&self, index: usize) -> (ret: &T)
        requires
            self.wf(),
            index < self.len(),
        ensures
            *ret == self@[index as int],
    {
        self.data.get(index)
    }

    pub fn push(&mut self, value: T)
        requires
            old(self).wf(),
            old(self).len() < old(self).capacity(),
        ensures
            self.wf(),
            self@ =~= old(self)@.push(value),
            self.len() == old(self).len() + 1,
    {
        let index = self.len;
        self.data.set(index, value);

        self.len = self.len + 1;
    }

    pub fn push_unique(&mut self, value: T)
    requires
        old(self).wf(),
        old(self).len() < old(self).capacity(),
        old(self)@.no_duplicates(),
        old(self)@.contains(value) == false,
    ensures
        self.wf(),
        self@ =~= old(self)@.push(value),
        self.len() == old(self).len() + 1,
        self@.no_duplicates(),
    {
        let index = self.len;
        let ret = self.data.set(index, value);

        self.len = self.len + 1;

        assert(self@ =~= old(self)@.push(value));

        assert(forall|t:T| #![auto] !( t =~= value) ==> self@.contains(t) ==> old(self)@.contains(t));
        assert(forall|t:T| #![auto] !( t =~= value) ==> old(self)@.contains(t) ==> self@[old(self)@.index_of(t)] =~= t);
        assert(forall|t:T| #![auto] !( t =~= value) ==> old(self)@.contains(t) ==> self@.contains(t));
        assert(forall|i:int| #![auto] 0<=i<old(self).len() ==> ! (self@[i] =~= value));
        assert(self@[self.len - 1] =~= value);
    }

    pub fn pop(&mut self) -> (ret: T)
        requires
            old(self).wf(),
            old(self).len() > 0,
        ensures
            self.wf(),
            ret == old(self)@[old(self).len() - 1],
            self@ =~= old(self)@.drop_last(),
    {
        let index = self.len() - 1;
        let ret = *self.data.get(index);

        self.len = self.len - 1;

        ret
    }

    pub fn pop_unique(&mut self) -> (ret: &T)
        requires
            old(self).wf(),
            old(self).len() > 0,
            old(self)@.no_duplicates(),
        ensures
            self.wf(),
            ret == old(self)@[old(self).len() - 1],
            self@ =~= old(self)@.drop_last(),
            self@.no_duplicates(),
    {
        let index = self.len() - 1;
        let ret = self.data.get(index);

        self.len = self.len - 1;

        ret
    }

    pub fn set(&mut self, index: usize, value: T)
        requires
            old(self).wf(),
            index < old(self).len(),
        ensures
            self.wf(),
            self@ =~= old(self)@.update(index as int, value),
    {
        self.data.set(index, value);
    }


    /*
    proof fn prove_view_consistency(&self, len: nat)
        requires
            self.wf(),
            len <= self.len(),

            len > 0 ==> (
                forall |i: nat| 0 <= i < len - 1 ==>
                    #[trigger] self@[i as int] == #[trigger] self.data.map()[i]
            ),
        ensures
            forall |i: nat| 0 <= i < len ==>
                #[trigger] self@[i as int] == #[trigger] self.data.map()[i],
        decreases len
    {
        if len > 0 {
            let prev = len - 1;
            self.prove_view_consistency(prev as nat);
        }
    }

    proof fn prove_view_equivalence(&self, other: &Self, len: nat)
        requires
            len <= self.len(),
            len <= other.len(),

            forall |i: nat| 0 <= i < len ==>
                self.data.map()[i] == other.data.map()[i],
        ensures
            self.view_until(len) =~= other.view_until(len),
        decreases len
    {
        if len > 0 {
            let prev = len - 1;
            self.prove_view_equivalence(other, prev as nat);
        }
    }
    */
}

}