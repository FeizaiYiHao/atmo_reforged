use vstd::prelude::*;
verus! {
use crate::slinkedlist::define::*;
use crate::slinkedlist::spec::*;
use crate::define::SLLIndex;
use vstd::seq_lib::lemma_seq_contains_after_push;

    impl<T: Copy, const N: usize> StaticLinkedList<T,N> {

        // pub fn init(&mut self)
        // requires
        //     old(self).arr_seq@.len() == N,
        //     N>2,
        //     N<SLLIndex::MAX,
        // ensures
        //     self.wf(),
        //     self.len() == 0,
        //     self@ =~= Seq::empty(),
        // {
        //     // assume(N>2);
        //     // assume(N<SLLIndex::MAX);
        //     self.value_list = Ghost(Seq::empty());
        //     self.value_list_head = -1;
        //     self.value_list_tail = -1;
        //     self.value_list_len = 0;
        //     self.spec_seq = Ghost(Seq::empty());
        //     self.free_list = Ghost(Seq::empty());
        //     self.free_list_head = -1;
        //     self.free_list_tail = -1;
        //     self.free_list_len = 0;
        //     assert(self.value_list_wf());
        //     assert(self.free_list_wf());

        //     self.size = N;

        //     self.free_list_head = 0;
        //     self.free_list_tail = 0;
        //     self.free_list_len = 1;
        //     proof{self.free_list@ = self.free_list@.push(0);}
        //     self.set_next(0,-1);
        //     self.set_prev(0,-1);
        //     self.set_ptr(0,NULL_POINTER);
        //     // assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
        //     // assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
        //     // assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
        //     // assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
        //     // assert(forall|i: nat, j:nat|  #![auto] i != j && 0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() ==> (self.free_list@[i as int] != self.free_list@[j as int]) );
        //     // assert(self.wf_free_node_head());
        //     // assert(self.wf_free_node_tail());
        //     // assert(self.free_list_len == self.free_list@.len());
        //     assert(self.free_list_wf());
        //     for index in 1..N as SLLIndex
        //         invariant
        //             1<= index <= N,
        //             N<SLLIndex::MAX,
        //             self.value_list@ =~= Seq::empty(),
        //             self.value_list@.len() == 0,
        //             self.spec_seq@.len() == 0,
        //             self.array_wf(),
        //             self.spec_seq_wf(),
        //             self.value_list_wf(),
        //             self.free_list_wf(),
        //             index == self.free_list@.len(),
        //             forall|i: SLLIndex|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] == i),
        //             self.arr_seq@[0].prev == -1,
        //             self.arr_seq@[(index - 1) as int].next == -1,
        //             forall|i: int|  #![auto] 0 <= i < index ==> self.arr_seq@[i].prev == i - 1,
        //             forall|i: int|  #![auto] 0 <= i < index - 1 ==> self.arr_seq@[i].next == i + 1,
        //             forall|i: int|  #![auto] 0 <= i < index ==> self.arr_seq@[i].value == 0,
        //             self.free_list_len == index,
        //             self.free_list_len + self.value_list_len == index,
        //             forall|i: SLLIndex|  #![auto] 0 <= i < index ==> self.free_list@.contains(i),
        //             forall|i: SLLIndex| #![auto] 0 <= i < index ==> self.arr_seq@[i as int].value == NULL_POINTER,
        //         // ensures
        //         //     self.free_list_len == N,
        //         //     self.free_list_wf(),
        //         //     forall|i: SLLIndex|  #![auto] 0 <= i < N ==> (self.free_list@[i as int] == i),
        //         //     self.value_list@ =~= Seq::empty(),
        //         //     self.value_list@.len() == 0,
        //         //     self.spec_seq@.len() == 0,
        //         //     self.array_wf(),
        //         //     self.spec_seq_wf(),
        //         //     self.value_list_wf(),
        //         //     self.free_list_wf(),
        //         //     forall|i: SLLIndex|  #![auto] 0 <= i < N ==> self.free_list@.contains(i) ^ self.value_list@.contains(i),
        //         //     forall|i: SLLIndex| #![auto] 0 <= i < N ==> self.arr_seq@[i as int].value == NULL_POINTER,
        //         //     self.wf(),
        //     {
        //         proof{
        //             assert forall |s: Seq<SLLIndex>, v: SLLIndex, x: SLLIndex| v==x || s.contains(x) implies #[trigger] s.push(v).contains(x) by {
        //                 lemma_seq_contains_after_push(s, v, x);
        //             }
        //         }

        //         self.free_list = Ghost(self.free_list@.push((index as SLLIndex)));
        //         self.set_prev(index,(index - 1));
        //         self.set_next(index,-1);
        //         self.set_next((index - 1), index);
        //         self.set_ptr(index,0);
        //         self.free_list_tail = index;
        //         self.free_list_len = (index + 1) as usize;

        //         assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
        //         assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
        //         assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
        //         assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
        //         assert(forall|i: nat, j:nat|  #![auto] i != j && 0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() ==> (self.free_list@[i as int] != self.free_list@[j as int]) );
        //         assert(self.wf_free_node_head());
        //         assert(self.wf_free_node_tail());
        //         assert(self.free_list_len == self.free_list@.len());
        //     }
        //     // assert(self.free_list@.len() == N);
        //     // assert(forall|i: SLLIndex|  #![auto] 0 <= i < N ==> self.free_list@[i as int] == i);
        //     // assert(forall|i: SLLIndex|  #![auto] 0 <= i < N ==> self.free_list@.index_of(i) == i as int);
        //     // assert(forall|i: SLLIndex|  #![auto] 0 <= i < N ==> self.free_list@.contains(i));
        // }


        pub fn push(&mut self, new_value: &T) -> (free_node_index : SLLIndex)
            requires old(self).wf(),
                    old(self).len() < old(self).size,
                    old(self).unique(),
                    old(self)@.contains(*new_value) == false,
                    N > 2,
            ensures 
                    // self.wf(),
                    // self@ == old(self)@.push(new_ptr),
                    // self.value_list@ == old(self).value_list@.push(free_node_index),
                    // self.len() == old(self).len() + 1,
                    // self.arr_seq@[free_node_index as int].value == new_ptr,
                    // self.node_ref_valid(free_node_index),
                    // self.node_ref_resolve(free_node_index) == new_ptr,
                    // forall|index:SLLIndex| #[trigger] old(self).node_ref_valid(index) ==> self.node_ref_valid(index),
                    // forall|index:SLLIndex| #[trigger] old(self).node_ref_valid(index) ==> index != free_node_index,
                    // forall|index:SLLIndex| #[trigger] old(self).node_ref_valid(index) ==> self.node_ref_resolve(index) == old(self).node_ref_resolve(index),
                    // self.unique(),
                    // forall| ptr: usize| ptr != new_ptr ==> old(self)@.contains(ptr) == #[trigger] self@.contains(ptr),
                    // self@.contains(new_ptr),
        {
            if self.value_list_len == 0 {
                // value list empty
                // assert(self.value_list_head == -1);
                // assert(self.value_list_tail == -1);
                let ret = self.free_list_head;
                // assert(ret != -1);
                // assert(ret != self.free_list_tail);
                let next_free_list_head = self.get_next(self.free_list_head);
                // assert(next_free_list_head == self.free_list@[1]);
                self.free_list_head = next_free_list_head;
                self.set_prev(self.free_list_head, -1);

                self.free_list_len = self.free_list_len - 1;
                proof {self.free_list@ = self.free_list@.skip(1);}
                self.value_list_head = ret;
                self.value_list_tail = ret;
                self.set_prev(ret, -1);
                                
                assert(forall|i: nat|
                    #![trigger old(self).arr_seq@[i as int]]
                    #![trigger self.arr_seq@[i as int]]
                    0 <= i < N && i != ret ==>  old(self).arr_seq@[i as int].next == self.arr_seq@[i as int].next );
                    
                self.set_next(ret, -1);
                proof{
                    self.value_list@ = self.value_list@.push(ret);
                    self.spec_seq@ = self.spec_seq@.push(*new_value);
                }
                self.value_list_len = self.value_list_len + 1;
                self.set_value(ret, Some(*new_value));
                // assert(self.value_list_wf());
                assert(self.wf()) by {
                    assert(self.array_wf());
                    assert(self.free_list_len + self.value_list_len == N);
                    assert(self.value_list_wf());
                    assert(self.free_list_wf()) by {
                        assert(forall|i: nat|
                            #![trigger self.arr_seq@[self.free_list@[i as int] as int].next]
                            #![trigger self.next_free_node_of(i)]
                            0 <= i < self.free_list@.len() ==>  self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i)) by {
                                assert(forall|i: nat|
                                    #![trigger self.free_list@[i as int]]
                                    0 <= i < self.free_list@.len() ==> ret != self.free_list@[i as int]
                                    );
                                assert(forall|i: nat|
                                    #![trigger old(self).arr_seq@[i as int]]
                                    #![trigger self.arr_seq@[i as int]]
                                    0 <= i < N && i != ret ==>  old(self).arr_seq@[i as int].next == self.arr_seq@[i as int].next );
                                assert(forall|i: nat|
                                    #![trigger self.arr_seq@[self.free_list@[i as int] as int].next]
                                    #![trigger self.next_free_node_of(i)]
                                    0 <= i < self.free_list@.len() ==>  old(self).arr_seq@[old(self).free_list@[i as int + 1] as int].next == self.arr_seq@[self.free_list@[i as int] as int].next);
                                assert(forall|i: nat|
                                    #![trigger self.arr_seq@[self.free_list@[i as int] as int].next]
                                    #![trigger self.next_free_node_of(i)]
                                    0 <= i < self.free_list@.len() ==>  old(self).next_free_node_of(i + 1) == self.next_free_node_of(i));

                            };
                        assert(forall|i: nat|
                            #![trigger self.arr_seq@[self.free_list@[i as int] as int].prev]
                            #![trigger self.prev_free_node_of(i)]
                            0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i)) by {
                                assert(forall|i: nat|
                                    #![trigger self.arr_seq@[self.free_list@[i as int] as int].prev]
                                    #![trigger self.prev_free_node_of(i)]
                                    1 <= i < self.free_list@.len() ==> old(self).arr_seq@[old(self).free_list@[i as int + 1] as int].prev == self.arr_seq@[self.free_list@[i as int] as int].prev);
                                assert(forall|i: nat|
                                    #![trigger self.arr_seq@[self.free_list@[i as int] as int].prev]
                                    #![trigger self.prev_free_node_of(i)]
                                    1 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i + 1) == self.prev_free_node_of(i));
                            };
                    };
                    assert(forall|i:SLLIndex|                
                        #![trigger self.free_list@.contains(i)]
                        #![trigger self.value_list@.contains(i)]
                        0<= i < N ==> self.free_list@.contains(i) ^ self.value_list@.contains(i));
                    assert(self.spec_seq_wf());
                    assert(self.free_list_ptr_all_null());
                };
            }

            return 0;
        }

    }

}