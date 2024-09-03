use vstd::prelude::*;
verus! {
use crate::slinkedlist::define::*;
use crate::define::SLLIndex;

    pub struct StaticLinkedList<T, const N: usize>{
        pub ar: [Node<T>;N],
        pub spec_seq: Ghost<Seq<T>>,
    
        pub value_list: Ghost<Seq<SLLIndex>>,
        pub value_list_head: SLLIndex,
        pub value_list_tail: SLLIndex,
        pub value_list_len: usize,
        pub free_list: Ghost<Seq<SLLIndex>>,
        pub free_list_head: SLLIndex,
        pub free_list_tail: SLLIndex,
        pub free_list_len: usize,
    
        pub size: usize,
    
    
        pub arr_seq: Ghost<Seq<Node<T>>>,
    }

    impl<T, const N: usize> StaticLinkedList<T, N> {
        pub open spec fn spec_len(&self) -> usize{
            self.value_list_len
        }

        #[verifier(when_used_as_spec(spec_len))]
        pub fn len(&self) -> (l: usize)
            ensures
                l == self.value_list_len,
        {
            self.value_list_len
        }

        pub open spec fn spec_get(&self, index: SLLIndex) -> Option<T>
            recommends
                0 <= index < N,
        {
            self.arr_seq@[index as int].value
        }


        pub open spec fn get_raw_element(&self, i: int) -> Node<T>
            recommends 
                    0 <= i < N,
        {
            self.arr_seq@[i]
        }
    
        pub open spec fn unique(&self) -> bool {
            forall|i:int, j:int| 
                #![trigger self.spec_seq@[i], self.spec_seq@[j]]
                0<=i<self.len() && 0<=j<self.len() && i != j ==> self.spec_seq@[i] =~= self.spec_seq@[j] == false
        }
    
        // #[verifier(inline)]
        pub open spec fn view(&self) -> Seq<T>
        {
            self.spec_seq@
        }
    
        pub open spec fn node_ref_valid(&self, index: SLLIndex) -> bool{
            self.value_list@.contains(index)
        }
    
        pub open spec fn node_ref_resolve(&self, index: SLLIndex) -> T
            recommends 
                self.node_ref_valid(index)
        {
            self.arr_seq@[index as int].value.get_Some_0()
        }
    
        pub open spec fn prev_free_node_of(&self, i: nat) -> int
            recommends i < self.free_list@.len()
        {
            if i == 0{
                -1
            } else {
                self.free_list@[i - 1int] as int
            }
        }
    
        pub open spec fn next_free_node_of(&self, i: nat) -> int
            recommends i < self.free_list@.len()
        {
            if i + 1 == self.free_list@.len() {
                -1
            } else {
                self.free_list@[i + 1int] as int
            }
        }
    
        pub open spec fn wf_free_node_head(&self) -> bool {
            if self.free_list@.len() == 0 {
                self.free_list_head == -1
            } else {
                self.free_list_head == self.free_list@[0]
            }
        }
    
        pub open spec fn wf_free_node_tail(&self) -> bool {
            if self.free_list@.len() == 0 {
                self.free_list_tail == -1
            } else {
                self.free_list_tail  == self.free_list@[self.free_list@.len() - 1]
            }
        }
    
        pub open spec fn free_list_wf(&self) -> bool{
            &&&
            forall|i: nat|
                // #![trigger self.arr_seq@[self.free_list@[i as int] as int].next, self.next_free_node_of(i)]
                #![trigger self.arr_seq@[self.free_list@[i as int] as int].next]
                #![trigger self.next_free_node_of(i)]
                0 <= i < self.free_list@.len() ==>  self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i)
            &&&
            forall|i: nat|
                // #![trigger self.arr_seq@[self.free_list@[i as int] as int].prev, self.prev_free_node_of(i)]
                #![trigger self.arr_seq@[self.free_list@[i as int] as int].prev]
                #![trigger self.prev_free_node_of(i)]
                0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i)
            &&&
            forall|i: nat| #![trigger self.free_list@[i as int]] 0 <= i < self.free_list@.len() ==> 0 <= self.free_list@[i as int] < N
            &&&
            forall|i:int, j:int| 
                #![trigger self.free_list@[i], self.free_list@[j]]
                0<=i<self.free_list_len && 0<=j<self.free_list_len && i != j ==> self.free_list@[i] != self.free_list@[j]
            &&&
            self.wf_free_node_head()
            &&&
            self.wf_free_node_tail()
            &&&
            self.free_list_len == self.free_list@.len()
    
        }
    
        pub open spec fn prev_value_node_of(&self, i: int) -> int
            recommends 0 <= i < self.value_list@.len()
        {
            if i == 0{
                -1
            } else {
                self.value_list@[i - 1int] as int
            }
        }
    
        pub open spec fn next_value_node_of(&self, i: int) -> int
            recommends 0 <= i < self.value_list@.len()
        {
            if i + 1 == self.value_list@.len() {
                -1
            } else {
                self.value_list@[i + 1int] as int
            }
        }
    
        pub open spec fn wf_value_node_head(&self) -> bool {
            if self.value_list@.len() == 0 {
                self.value_list_head == -1
            } else {
                self.value_list_head == self.value_list@[0]
            }
        }
    
        pub open spec fn wf_value_node_tail(&self) -> bool {
        if self.value_list@.len() == 0 {
            self.value_list_tail == -1
        } else {
            self.value_list_tail  == self.value_list@[self.value_list@.len() - 1]
        }
        }
    
        pub open spec fn value_list_wf(&self) -> bool{
            &&&
            forall|i: int|
                #![trigger self.arr_seq@[self.value_list@[i as int] as int].next]
                #![trigger self.next_value_node_of(i)]
                0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == self.next_value_node_of(i)
            &&&
            forall|i: int|
                #![trigger self.arr_seq@[self.value_list@[i as int] as int].prev]
                #![trigger self.prev_value_node_of(i)]
                0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == self.prev_value_node_of(i)
            &&&
            forall|i: int| 
                #![trigger self.value_list@[i as int]] 
                0 <= i < self.value_list@.len() ==> 0 <= self.value_list@[i as int] < N
            &&&
            self.unique()
            &&&
            self.wf_value_node_head()
            &&&
            self.wf_value_node_tail()
            &&&
            self.value_list_len == self.value_list@.len()
        }
    
        pub open spec fn free_list_ptr_all_null(&self) -> bool
        {
            forall|i: SLLIndex|
                #![trigger self.arr_seq@[i as int].value.is_Some(), self.value_list@.contains(i)]
                0 <= i < N && self.arr_seq@[i as int].value.is_Some() ==> self.value_list@.contains(i)
        }
    
        pub open spec fn array_wf(&self) -> bool{
            &&&
            self.arr_seq@.len() == N
            &&&
            self.size == N
        }
    
        pub open spec fn spec_seq_wf(&self) -> bool
        {
            &&&
            self.spec_seq@.len() == self.value_list_len
            &&&
            forall|i:int| 
                #![trigger self.spec_seq@[i as int]]
                #![trigger self.value_list@[i as int]]
                0 <= i < self.value_list_len ==> self.arr_seq@[self.value_list@[i as int] as int].value.is_Some() && self.arr_seq@[self.value_list@[i as int] as int].value.get_Some_0() =~= self.spec_seq@[i as int]
        }
    
        pub open spec fn wf(&self) -> bool{
            &&&
            self.array_wf()
            &&&
            self.free_list_len + self.value_list_len == N
            &&&
            self.value_list_wf()
            &&&
            self.free_list_wf()
            &&&
            self.spec_seq_wf()
            &&&
            forall|i:int, j:int|
                #![trigger self.value_list@[i], self.free_list@[j]]
                0 <= i < self.value_list@.len() && 0 <= j < self.free_list@.len() ==> self.value_list@[i] != self.free_list@[j]
        }
    }
}