use vstd::prelude::*;
verus! {
// use crate::slinkedlist::define::*;
use crate::slinkedlist::spec_impl_u::*;
use crate::define::SLLIndex;
use core::mem::MaybeUninit;

    impl<T: Copy, const N: usize> StaticLinkedList<T,N> {

        #[verifier(external_body)]
        pub fn new() -> (ret: Self)
            ensures
                ret.arr_seq@.len() == N,
        {
            unsafe{
                let ret = Self {
    
                spec_seq: Ghost(Seq::empty()),
    
                value_list: Ghost(Seq::empty()),
                value_list_head: -1,
                value_list_tail: -1,
                value_list_len: 0,
                free_list: Ghost(Seq::empty()),
                free_list_head: -1,
                free_list_tail: -1,
                free_list_len: 0,
    
                size: N,
    
                arr_seq: Ghost(Seq::empty()),
                ar: MaybeUninit::uninit().assume_init(),
            };
    
            ret
            }
        }

        #[verifier(external_body)]
        pub fn set_value(&mut self, index: SLLIndex, v: Option<T>)
            requires
                old(self).array_wf(),
            ensures
                self.array_wf(),
                forall|i:int| 
                    // #![trigger self.arr_seq@[i], old(self).arr_seq@[i]]
                    #![trigger self.arr_seq@[i]]
                    #![trigger old(self).arr_seq@[i]]
                    0<=i<self.arr_seq@.len() && i != index ==>
                        self.arr_seq@[i] =~= old(self).arr_seq@[i],
                self.arr_seq@[index as int].prev == old(self).arr_seq@[index as int].prev,
                self.arr_seq@[index as int].next == old(self).arr_seq@[index as int].next,
                self.arr_seq@[index as int].value == v,
                self.spec_seq@ == old(self).spec_seq@,
                self.value_list@ == old(self).value_list@,
                self.free_list@ == old(self).free_list@,
                self.value_list_head == old(self).value_list_head,
                self.value_list_tail == old(self).value_list_tail,
                self.value_list_len == old(self).value_list_len,
                self.free_list_head == old(self).free_list_head,
                self.free_list_tail == old(self).free_list_tail,
                self.free_list_len == old(self).free_list_len,
                old(self).free_list_wf() ==> self.free_list_wf(),
                old(self).value_list_wf() ==> self.value_list_wf(),
        {
            self.ar[index as usize].value = v;
        }

        #[verifier(external_body)]
        pub fn set_next(&mut self, index: SLLIndex, v: SLLIndex)
            requires
                old(self).array_wf(),
            ensures
                self.array_wf(),
                forall|i:int| 
                    // #![trigger self.arr_seq@[i], old(self).arr_seq@[i]]
                    #![trigger self.arr_seq@[i]]
                    #![trigger old(self).arr_seq@[i]]
                    0<=i<self.arr_seq@.len() && i != index ==>
                        self.arr_seq@[i] =~= old(self).arr_seq@[i],
                self.arr_seq@[index as int].prev == old(self).arr_seq@[index as int].prev,
                self.arr_seq@[index as int].value == old(self).arr_seq@[index as int].value,
                self.arr_seq@[index as int].next == v,
                self.spec_seq@ == old(self).spec_seq@,
                self.value_list@ == old(self).value_list@,
                self.free_list@ == old(self).free_list@,
                self.value_list_head == old(self).value_list_head,
                self.value_list_tail == old(self).value_list_tail,
                self.value_list_len == old(self).value_list_len,
                self.free_list_head == old(self).free_list_head,
                self.free_list_tail == old(self).free_list_tail,
                self.free_list_len == old(self).free_list_len,
        {
            self.ar[index as usize].next = v;
        }

        #[verifier(external_body)]
        pub fn set_prev(&mut self, index: SLLIndex, v: SLLIndex)
            requires
                old(self).array_wf(),
            ensures
                self.array_wf(),
                forall|i:int| 
                    // #![trigger self.arr_seq@[i], old(self).arr_seq@[i]]
                    #![trigger self.arr_seq@[i]]
                    #![trigger old(self).arr_seq@[i]]
                    0<=i<self.arr_seq@.len() && i != index ==>
                        self.arr_seq@[i] =~= old(self).arr_seq@[i],
                self.arr_seq@[index as int].next == old(self).arr_seq@[index as int].next,
                self.arr_seq@[index as int].value == old(self).arr_seq@[index as int].value,
                self.arr_seq@[index as int].prev == v,
                self.spec_seq@ == old(self).spec_seq@,
                self.value_list@ == old(self).value_list@,
                self.free_list@ == old(self).free_list@,
                self.value_list_head == old(self).value_list_head,
                self.value_list_tail == old(self).value_list_tail,
                self.value_list_len == old(self).value_list_len,
                self.free_list_head == old(self).free_list_head,
                self.free_list_tail == old(self).free_list_tail,
                self.free_list_len == old(self).free_list_len,
        {
            self.ar[index as usize].prev = v;
        }

        // //TODO: prove this
        // #[verifier(external_body)]
        // pub fn put_ptr(&mut self, new_ptr: usize)
        //     requires
        //         old(self).array_wf(),
        //     ensures
        //     self.array_wf(),
        //     forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==>
        //         self.arr_seq@[i].next == old(self).arr_seq@[i].next && self.arr_seq@[i].prev == old(self).arr_seq@[i].prev && self.arr_seq@[i].value == old(self).arr_seq@[i].value,
        //     self.spec_seq@ == old(self).spec_seq@.push(new_ptr),
        //     self.value_list@ == old(self).value_list@,
        //     self.free_list@ == old(self).free_list@,
        //     self.value_list_head == old(self).value_list_head,
        //     self.value_list_tail == old(self).value_list_tail,
        //     self.value_list_len == old(self).value_list_len,
        //     self.free_list_head == old(self).free_list_head,
        //     self.free_list_tail == old(self).free_list_tail,
        //     self.free_list_len == old(self).free_list_len,
        //     old(self).free_list_wf() ==> self.free_list_wf(),
        //     old(self).value_list_wf() ==> self.value_list_wf(),
        // {
        //     //self.spec_seq@ = self.spec_seq@.push(new_ptr);
        // }
    
        #[verifier(external_body)]
        pub fn get_value(&self, index: SLLIndex) -> (ret:Option<T>)
            requires
                0 <= index < N,
                self.array_wf(),
            ensures
                ret == self.arr_seq@[index as int].value,
        {
            self.ar[index as usize].value
        }
    
        #[verifier(external_body)]
        pub fn get_next(&self, index: SLLIndex) -> (next:SLLIndex)
            requires
                0 <= index < N,
                self.array_wf(),
            ensures
                next == self.arr_seq@[index as int].next,
        {
            self.ar[index as usize].next
        }
    
        #[verifier(external_body)]
        pub fn get_prev(&self, index: SLLIndex) -> (prev:SLLIndex)
            requires
                0 <= index < N,
                self.array_wf(),
            ensures
                prev == self.arr_seq@[index as int].prev,
        {
            self.ar[index as usize].prev
        }

    }

}