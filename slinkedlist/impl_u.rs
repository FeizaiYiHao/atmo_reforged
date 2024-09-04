use vstd::prelude::*;
verus! {
// use crate::slinkedlist::define::*;
use crate::slinkedlist::spec::*;
use crate::define::SLLIndex;
// use vstd::seq_lib::*;
use crate::lemma::lemma_u::*;

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
                    self.wf(),
                    self@ == old(self)@.push(*new_value),
                    self.len() == old(self).len() + 1,
                    self@ == old(self)@.push(*new_value),
                    forall|index:SLLIndex|
                        #![trigger old(self).node_ref_valid(index)]
                        #![trigger self.node_ref_valid(index)]
                        old(self).node_ref_valid(index) ==> self.node_ref_valid(index),
                    forall|index:SLLIndex| 
                        #![trigger old(self).node_ref_valid(index)]
                        old(self).node_ref_valid(index) ==> index != free_node_index,
    
                    forall|index:SLLIndex| 
                        #![trigger old(self).node_ref_valid(index)]
                        #![trigger self.node_ref_resolve(index)]
                        #![trigger old(self).node_ref_resolve(index)]
                        old(self).node_ref_valid(index) ==> self.node_ref_resolve(index) == old(self).node_ref_resolve(index),
                    self.node_ref_valid(free_node_index),
                    self.node_ref_resolve(free_node_index) == *new_value,
                    self.unique(),
        {
            proof{
                seq_push_lemma::<SLLIndex>();
            }
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
                    #![trigger self.arr_seq@[i as int], old(self).arr_seq@[i as int]]
                    0 <= i < N && i != ret ==>  old(self).arr_seq@[i as int].next == self.arr_seq@[i as int].next );
                    
                self.set_next(ret, -1);
                proof{
                    self.value_list@ = self.value_list@.push(ret);
                    self.spec_seq@ = self.spec_seq@.push(*new_value);
                }
                self.value_list_len = self.value_list_len + 1;
                self.set_value(ret, Some(*new_value));
                assert(self.wf());
                assert(self@ == old(self)@.push(*new_value));
                return ret;
            }else if self.free_list_len == 1 {
                let ret = self.free_list_tail;
                self.free_list_len = 0;
                self.free_list_head = -1;
                self.free_list_tail = -1;
                proof{
                    self.free_list@ = self.free_list@.skip(1);
                }

                let old_value_list_tail = self.value_list_tail;
                self.set_prev(ret,old_value_list_tail);
                self.set_next(old_value_list_tail, ret);
                self.value_list_tail = ret;
                proof{
                    self.value_list@ = self.value_list@.push(ret);
                    self.spec_seq@ = self.spec_seq@.push(*new_value);
                }
                self.value_list_len = self.value_list_len + 1;

                self.set_value(ret, Some(*new_value));

                assert(self.wf());
                assert(self@ == old(self)@.push(*new_value));
                return ret;

            }else{
                assert(self.free_list_len > 1 && self.value_list_len > 0);
                let ret = self.free_list_head;
                let old_value_list_tail = self.value_list_tail;

                let new_free_list_head = self.get_next(ret);
                self.set_prev(new_free_list_head, -1);
                self.free_list_head = new_free_list_head;
                self.free_list_len = self.free_list_len - 1;
                proof{
                    self.free_list@ = self.free_list@.skip(1);
                }
                self.set_next(old_value_list_tail, ret);
                self.set_prev(ret, old_value_list_tail);
                self.set_next(ret, -1);
                self.value_list_tail = ret;
                self.value_list_len = self.value_list_len + 1;
                proof{
                    self.value_list@ = self.value_list@.push(ret);
                    self.spec_seq@ = self.spec_seq@.push(*new_value);
                }
                self.set_value(ret, Some(*new_value));
                assert(self.wf());
                return ret;
            }
        }

        pub fn pop(&mut self) -> (ret: (T,SLLIndex))
            requires old(self).wf(),
                    old(self).len() > 0,
                    old(self).unique(),
                    N > 2,
            ensures 
                self.wf(),
                self.len() == old(self).len() - 1,
                self@ == old(self)@.skip(1),
                ret.0 == old(self)@[0],   
                old(self).value_list@[0] == ret.1,
                old(self).node_ref_valid(ret.1),
                old(self).node_ref_resolve(ret.1) == ret.0,
                forall|index:SLLIndex|
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_valid(index)]
                    old(self).node_ref_valid(index) && index != ret.1 ==> self.node_ref_valid(index),
                forall|index:SLLIndex| 
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_resolve(index)]
                    #![trigger old(self).node_ref_resolve(index)]
                    old(self).node_ref_valid(index) && index != ret.1 ==> self.node_ref_resolve(index) == old(self).node_ref_resolve(index),
                self.unique(),
        {
            proof{
                seq_push_lemma::<SLLIndex>();
                seq_skip_lemma::<SLLIndex>();
            }
            if self.free_list_len == 0 {
                let ret_index = self.value_list_head;
                let ret = self.get_value(ret_index).unwrap();

                let new_value_list_head = self.get_next(ret_index);
                self.value_list_head = new_value_list_head;
                self.set_prev(new_value_list_head, -1);
                proof{
                    self.value_list@ = self.value_list@.skip(1);
                    self.spec_seq@ = self.spec_seq@.skip(1);
                }
                self.value_list_len = self.value_list_len - 1;

                self.free_list_head = ret_index;
                self.free_list_tail = ret_index;
                self.set_prev(ret_index, -1);
                self.set_next(ret_index, -1);
                proof{
                    self.free_list@ = self.free_list@.push(ret_index);
                }
                self.free_list_len = self.free_list_len + 1;

                assert(self.wf());
                return (ret,ret_index);
            }else if self.value_list_len == 1 {
                let ret_index = self.value_list_head;
                let ret = self.get_value(ret_index).unwrap();

                let old_free_list_tail = self.free_list_tail;
                self.set_next(old_free_list_tail, ret_index);
                self.set_prev(ret_index, old_free_list_tail);
                self.free_list_tail = ret_index;
                self.free_list_len = self.free_list_len + 1;
                proof{
                    self.free_list@ = self.free_list@.push(ret_index);
                }

                self.value_list_head = -1;
                self.value_list_tail = -1;
                proof{
                    self.value_list@ = self.value_list@.skip(1);
                    self.spec_seq@ = self.spec_seq@.skip(1);
                }
                self.value_list_len = self.value_list_len - 1;

                assert(self.wf());

                return (ret,ret_index);
            }else{
                let ret_index = self.value_list_head;
                let ret = self.get_value(ret_index).unwrap();

                let new_value_list_head = self.get_next(ret_index);
                self.value_list_head = new_value_list_head;
                self.set_prev(new_value_list_head, -1);
                proof{
                    self.value_list@ = self.value_list@.skip(1);
                    self.spec_seq@ = self.spec_seq@.skip(1);
                }
                self.value_list_len = self.value_list_len - 1;

                let old_free_list_tail = self.free_list_tail;
                self.set_next(ret_index, -1);
                self.set_next(old_free_list_tail, ret_index);
                self.set_prev(ret_index, old_free_list_tail);
                self.free_list_tail = ret_index;
                self.free_list_len = self.free_list_len + 1;
                proof{
                    self.free_list@ = self.free_list@.push(ret_index);
                }
                assert(self.wf());
                return (ret,ret_index);
            }
        }

        pub fn remove_helper1(&mut self, remove_index: SLLIndex) -> (ret: T)
            requires
                old(self).wf(),
                old(self).node_ref_valid(remove_index),
                old(self).value_list_len == 1,
            ensures
                self.wf(),
                self.len() == old(self).len() - 1,
                ret == old(self).node_ref_resolve(remove_index), 
                forall|index:SLLIndex|
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_valid(index)]
                    old(self).node_ref_valid(index) && index != remove_index ==> self.node_ref_valid(index),
                forall|index:SLLIndex| 
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_resolve(index)]
                    #![trigger old(self).node_ref_resolve(index)]
                    old(self).node_ref_valid(index) && index != remove_index ==> self.node_ref_resolve(index) == old(self).node_ref_resolve(index),
                self.unique(),
                self@ =~= old(self)@.remove_value(ret),
        {
            proof{
                seq_push_lemma::<SLLIndex>();
                seq_skip_lemma::<SLLIndex>(); 
                seq_skip_lemma::<T>(); 
            }
            let ret = self.get_value(remove_index).unwrap();
            let old_free_list_tail = self.free_list_tail;
            self.set_next(old_free_list_tail, remove_index);
            self.set_prev(remove_index, old_free_list_tail);
            self.free_list_tail = remove_index;
            self.free_list_len = self.free_list_len + 1;
            proof{
                self.free_list@ = self.free_list@.push(remove_index);
            }

            self.value_list_head = -1;
            self.value_list_tail = -1;
            proof{
                self.value_list@ = self.value_list@.skip(1);
                self.spec_seq@ = self.spec_seq@.skip(1);
            }
            self.value_list_len = self.value_list_len - 1;

            assert(self.wf());
            return ret;
        }

        pub fn remove_helper2(&mut self, remove_index: SLLIndex) -> (ret: T)
            requires
                old(self).wf(),
                old(self).node_ref_valid(remove_index),
                old(self).value_list_len != 1,
                old(self).free_list_len == 0 && old(self).value_list_head == remove_index
            ensures
                self.wf(),
                self.len() == old(self).len() - 1,
                ret == old(self).node_ref_resolve(remove_index), 
                forall|index:SLLIndex|
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_valid(index)]
                    old(self).node_ref_valid(index) && index != remove_index ==> self.node_ref_valid(index),
                forall|index:SLLIndex| 
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_resolve(index)]
                    #![trigger old(self).node_ref_resolve(index)]
                    old(self).node_ref_valid(index) && index != remove_index ==> self.node_ref_resolve(index) == old(self).node_ref_resolve(index),
                self.unique(),
                self@ =~= old(self)@.remove_value(ret),
        {
            proof{
                seq_push_lemma::<SLLIndex>();
                seq_skip_lemma::<SLLIndex>(); 
                seq_skip_lemma::<T>(); 
            }
            let ret = self.get_value(remove_index).unwrap();
            let new_value_list_head = self.get_next(remove_index);
            self.value_list_head = new_value_list_head;
            self.set_prev(new_value_list_head, -1);
            proof{
                self.value_list@ = self.value_list@.skip(1);
                self.spec_seq@ = self.spec_seq@.skip(1);
            }
            self.value_list_len = self.value_list_len - 1;

            self.free_list_head = remove_index;
            self.free_list_tail = remove_index;
            self.set_prev(remove_index, -1);
            self.set_next(remove_index, -1);
            proof{
                self.free_list@ = self.free_list@.push(remove_index);
            }
            self.free_list_len = self.free_list_len + 1;

            assert(self.wf());
            return ret;
        }

        pub fn remove_helper3(&mut self, remove_index: SLLIndex) -> (ret: T)
            requires
                old(self).wf(),
                old(self).node_ref_valid(remove_index),
                old(self).value_list_len != 1,
                old(self).free_list_len == 0 && old(self).value_list_tail == remove_index
            ensures
                self.wf(),
                self.len() == old(self).len() - 1,
                ret == old(self).node_ref_resolve(remove_index), 
                forall|index:SLLIndex|
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_valid(index)]
                    old(self).node_ref_valid(index) && index != remove_index ==> self.node_ref_valid(index),
                forall|index:SLLIndex| 
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_resolve(index)]
                    #![trigger old(self).node_ref_resolve(index)]
                    old(self).node_ref_valid(index) && index != remove_index ==> self.node_ref_resolve(index) == old(self).node_ref_resolve(index),
                self.unique(),
                self@ =~= old(self)@.remove_value(ret),
        {
            proof{
                seq_push_lemma::<SLLIndex>();
                seq_remove_lemma::<SLLIndex>(); 
                seq_remove_lemma::<T>(); 
            }
            let ret = self.get_value(remove_index).unwrap();
            let new_value_list_tail = self.get_prev(remove_index);
            self.value_list_tail = new_value_list_tail;
            self.set_next(new_value_list_tail, -1);
            proof{
                self.value_list@ = self.value_list@.subrange(0,self.value_list_len as int - 1).add(self.value_list@.subrange(self.value_list_len as int, self.value_list_len as int));
                self.spec_seq@ = self.spec_seq@.subrange(0,self.value_list_len as int - 1).add(self.spec_seq@.subrange(self.value_list_len as int,self.value_list_len as int));
            }
            self.value_list_len = self.value_list_len - 1;

            self.free_list_head = remove_index;
            self.free_list_tail = remove_index;
            self.set_prev(remove_index, -1);
            self.set_next(remove_index, -1);
            proof{
                self.free_list@ = self.free_list@.push(remove_index);
            }
            self.free_list_len = self.free_list_len + 1;

            assert(self.wf());
            return ret;
        }

        pub fn remove_helper4(&mut self, remove_index: SLLIndex) -> (ret: T)
            requires
                old(self).wf(),
                old(self).node_ref_valid(remove_index),
                old(self).value_list_len != 1,
                old(self).free_list_len == 0 && old(self).value_list_tail != remove_index && old(self).value_list_head != remove_index,
            ensures
                self.wf(),
                self.len() == old(self).len() - 1,
                ret == old(self).node_ref_resolve(remove_index), 
                forall|index:SLLIndex|
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_valid(index)]
                    old(self).node_ref_valid(index) && index != remove_index ==> self.node_ref_valid(index),
                forall|index:SLLIndex| 
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_resolve(index)]
                    #![trigger old(self).node_ref_resolve(index)]
                    old(self).node_ref_valid(index) && index != remove_index ==> self.node_ref_resolve(index) == old(self).node_ref_resolve(index),
                self.unique(),
                self@ =~= old(self)@.remove_value(ret),
        {
            proof{
                seq_push_lemma::<SLLIndex>();
                seq_remove_lemma::<SLLIndex>(); 
                seq_remove_lemma::<T>(); 
            }
            let ret = self.get_value(remove_index).unwrap();
            let prev = self.get_prev(remove_index);
            let next = self.get_next(remove_index);
            self.set_next(prev, next);
            self.set_prev(next, prev);

            let ghost_index = Ghost(self.value_list@.index_of(remove_index));
            assert(0 <= ghost_index@ < self.value_list@.len());
            assert(self.value_list@[ghost_index@] == remove_index);

            proof{
                self.value_list@ = self.value_list@.subrange(0,ghost_index@).add(self.value_list@.subrange(ghost_index@ + 1, self.value_list_len as int));
                self.spec_seq@ = self.spec_seq@.subrange(0,ghost_index@).add(self.spec_seq@.subrange(ghost_index@ + 1,self.value_list_len as int));
            }
            self.value_list_len = self.value_list_len - 1;

            self.free_list_head = remove_index;
            self.free_list_tail = remove_index;
            self.set_prev(remove_index, -1);
            self.set_next(remove_index, -1);
            proof{
                self.free_list@ = self.free_list@.push(remove_index);
            }
            self.free_list_len = self.free_list_len + 1;

            assert(self.wf());
            return ret;
        }

        pub fn remove_helper5(&mut self, remove_index: SLLIndex) -> (ret: T)
            requires
                old(self).wf(),
                old(self).node_ref_valid(remove_index),
                old(self).value_list_len != 1,
                old(self).free_list_len != 0 && old(self).value_list_head == remove_index && old(self).value_list_len != 1,
            ensures
                self.wf(),
                self.len() == old(self).len() - 1,
                ret == old(self).node_ref_resolve(remove_index), 
                forall|index:SLLIndex|
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_valid(index)]
                    old(self).node_ref_valid(index) && index != remove_index ==> self.node_ref_valid(index),
                forall|index:SLLIndex| 
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_resolve(index)]
                    #![trigger old(self).node_ref_resolve(index)]
                    old(self).node_ref_valid(index) && index != remove_index ==> self.node_ref_resolve(index) == old(self).node_ref_resolve(index),
                self.unique(),
                self@ =~= old(self)@.remove_value(ret),
        {
            proof{
                seq_push_lemma::<SLLIndex>();
                seq_skip_lemma::<SLLIndex>(); 
                seq_skip_lemma::<T>(); 
            }
            let ret = self.get_value(remove_index).unwrap();
            let new_value_list_head = self.get_next(remove_index);
            self.value_list_head = new_value_list_head;
            self.set_prev(new_value_list_head, -1);
            proof{
                self.value_list@ = self.value_list@.skip(1);
                self.spec_seq@ = self.spec_seq@.skip(1);
            }
            self.value_list_len = self.value_list_len - 1;

            let old_free_list_tail = self.free_list_tail;
            self.set_next(old_free_list_tail, remove_index);
            self.set_next(remove_index, -1);
            self.set_prev(remove_index, old_free_list_tail);
            self.free_list_tail = remove_index;
            self.free_list_len = self.free_list_len + 1;
            proof{
                self.free_list@ = self.free_list@.push(remove_index);
            }

            assert(self.wf());
            return ret;
        }

        pub fn remove_helper6(&mut self, remove_index: SLLIndex) -> (ret: T)
            requires
                old(self).wf(),
                old(self).node_ref_valid(remove_index),
                old(self).value_list_len != 1,
                old(self).free_list_len != 0 && old(self).value_list_tail == remove_index && old(self).value_list_len != 1,
            ensures
                self.wf(),
                self.len() == old(self).len() - 1,
                ret == old(self).node_ref_resolve(remove_index), 
                forall|index:SLLIndex|
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_valid(index)]
                    old(self).node_ref_valid(index) && index != remove_index ==> self.node_ref_valid(index),
                forall|index:SLLIndex| 
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_resolve(index)]
                    #![trigger old(self).node_ref_resolve(index)]
                    old(self).node_ref_valid(index) && index != remove_index ==> self.node_ref_resolve(index) == old(self).node_ref_resolve(index),
                self.unique(),
                self@ =~= old(self)@.remove_value(ret),
        {
            proof{
                seq_push_lemma::<SLLIndex>();
                seq_remove_lemma::<SLLIndex>(); 
                seq_remove_lemma::<T>(); 
            }
            let ret = self.get_value(remove_index).unwrap();
            let new_value_list_tail = self.get_prev(remove_index);
            self.value_list_tail = new_value_list_tail;
            self.set_next(new_value_list_tail, -1);
            proof{
                self.value_list@ = self.value_list@.subrange(0,self.value_list_len as int - 1).add(self.value_list@.subrange(self.value_list_len as int, self.value_list_len as int));
                self.spec_seq@ = self.spec_seq@.subrange(0,self.value_list_len as int - 1).add(self.spec_seq@.subrange(self.value_list_len as int,self.value_list_len as int));
            }
            self.value_list_len = self.value_list_len - 1;

            let old_free_list_tail = self.free_list_tail;
            self.set_next(old_free_list_tail, remove_index);
            self.set_next(remove_index, -1);
            self.set_prev(remove_index, old_free_list_tail);
            self.free_list_tail = remove_index;
            self.free_list_len = self.free_list_len + 1;
            proof{
                self.free_list@ = self.free_list@.push(remove_index);
            }

            assert(self.wf());
            return ret;
        }

        pub fn remove_helper7(&mut self, remove_index: SLLIndex) -> (ret: T)
            requires
                old(self).wf(),
                old(self).node_ref_valid(remove_index),
                old(self).value_list_len != 1,
                old(self).free_list_len != 0 && old(self).value_list_tail != remove_index && old(self).value_list_head != remove_index && old(self).value_list_len != 1,
            ensures
                self.wf(),
                self.len() == old(self).len() - 1,
                ret == old(self).node_ref_resolve(remove_index), 
                forall|index:SLLIndex|
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_valid(index)]
                    old(self).node_ref_valid(index) && index != remove_index ==> self.node_ref_valid(index),
                forall|index:SLLIndex| 
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_resolve(index)]
                    #![trigger old(self).node_ref_resolve(index)]
                    old(self).node_ref_valid(index) && index != remove_index ==> self.node_ref_resolve(index) == old(self).node_ref_resolve(index),
                self.unique(),
                self@ =~= old(self)@.remove_value(ret),
        {
            proof{
                seq_push_lemma::<SLLIndex>();
                seq_skip_lemma::<SLLIndex>();
                seq_remove_lemma::<SLLIndex>();
                seq_remove_lemma_2::<SLLIndex>();
                seq_remove_lemma::<T>(); 
            }
            let ret = self.get_value(remove_index).unwrap();
            let prev = self.get_prev(remove_index);
            let next = self.get_next(remove_index);
            self.set_next(prev, next);
            self.set_prev(next, prev);

            let ghost_index = Ghost(self.value_list@.index_of(remove_index));
            assert(0 <= ghost_index@ < self.value_list@.len());
            assert(self.value_list@[ghost_index@] == remove_index);

            proof{
                self.value_list@ = self.value_list@.subrange(0,ghost_index@).add(self.value_list@.subrange(ghost_index@ + 1, self.value_list_len as int));
                self.spec_seq@ = self.spec_seq@.subrange(0,ghost_index@).add(self.spec_seq@.subrange(ghost_index@ + 1,self.value_list_len as int));
            }
            self.value_list_len = self.value_list_len - 1;

            let old_free_list_tail = self.free_list_tail;
            self.set_next(old_free_list_tail, remove_index);
            self.set_next(remove_index, -1);
            self.set_prev(remove_index, old_free_list_tail);
            self.free_list_tail = remove_index;
            self.free_list_len = self.free_list_len + 1;
            proof{
                self.free_list@ = self.free_list@.push(remove_index);
            }

            assert(self.wf());
            return ret;
        }

        pub fn remove(&mut self, remove_index: SLLIndex) -> (ret: T)
            requires
                old(self).wf(),
                old(self).node_ref_valid(remove_index),
            ensures
                self.wf(),
                self.len() == old(self).len() - 1,
                ret == old(self).node_ref_resolve(remove_index), 
                forall|index:SLLIndex|
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_valid(index)]
                    old(self).node_ref_valid(index) && index != remove_index ==> self.node_ref_valid(index),
                forall|index:SLLIndex| 
                    #![trigger old(self).node_ref_valid(index)]
                    #![trigger self.node_ref_resolve(index)]
                    #![trigger old(self).node_ref_resolve(index)]
                    old(self).node_ref_valid(index) && index != remove_index ==> self.node_ref_resolve(index) == old(self).node_ref_resolve(index),
                self.unique(),
                self@ =~= old(self)@.remove_value(ret),
        {
            assert(self.value_list_len != 0);
            if self.value_list_len == 1{
                return self.remove_helper1(remove_index);
            }else if self.free_list_len == 0 && self.value_list_head == remove_index {
                return self.remove_helper2(remove_index);
            }else if self.free_list_len == 0 && self.value_list_tail == remove_index {
                return self.remove_helper3(remove_index);
            }else if self.free_list_len == 0{
                return self.remove_helper4(remove_index);
            }else if self.value_list_head == remove_index {
                return self.remove_helper5(remove_index);
            }else if self.value_list_tail == remove_index{
                return self.remove_helper6(remove_index);
            }else{
                return self.remove_helper7(remove_index);
            }
        } 
    }

}