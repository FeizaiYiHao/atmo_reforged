use vstd::prelude::*;
verus! {
use crate::slinkedlist::define::*;

    pub struct MarsStaticLinkedList<const N: usize>{
        pub ar: [Node;N],
        pub spec_seq: Ghost<Seq<usize>>,
    
        pub value_list: Ghost<Seq<Index>>,
        pub value_list_head: Index,
        pub value_list_tail: Index,
        pub value_list_len: usize,
        pub free_list: Ghost<Seq<Index>>,
        pub free_list_head: Index,
        pub free_list_tail: Index,
        pub free_list_len: usize,
    
        pub size: usize,
    
    
        pub arr_seq: Ghost<Seq<Node>>,
    }

    impl<const N: usize> MarsStaticLinkedList<N> {
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

        pub open spec fn spec_get_ptr(&self, index: Index) -> (ptr:usize)
            recommends
                self.wf(),
                0 <= index < N,
        {
            self.arr_seq@[index as int].value
        }


        pub open spec fn get_raw_element(&self, i: int) -> Node
            recommends self.arr_seq@.len() == N,
                    0 <= i < N,
        {
            self.arr_seq@[i]
        }
    
        pub open spec fn no_duplicates(&self) -> bool {
            self.spec_seq@.no_duplicates()
        }
    
        pub open spec fn view(&self) -> Seq<usize>
            recommends self.wf(),
        {
            self.spec_seq@
        }
    
        pub open spec fn node_ref_valid(&self, index: Index) -> bool{
            self.value_list@.contains(index)
        }
    
        pub open spec fn node_ref_resolve(&self, index: Index) -> usize
            recommends self.node_ref_valid(index)
        {
            self.arr_seq@[index as int].value
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
            (forall|i: nat|
                #![trigger self.arr_seq@[self.free_list@[i as int] as int].next]
                #![trigger self.next_free_node_of(i)]
                0 <= i < self.free_list@.len() ==>  self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i))
            &&
            (forall|i: nat|
                #![trigger self.arr_seq@[self.free_list@[i as int] as int].prev]
                #![trigger self.prev_free_node_of(i)]
                0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i))
            &&
            (forall|i: nat| 0 <= i < self.free_list@.len() ==> #[trigger] self.free_list@[i as int] < N)
            &&
            (forall|i: nat| 0 <= i < self.free_list@.len() ==> #[trigger] self.free_list@[i as int] >= 0)
            &&
            self.free_list@.no_duplicates()
            &&
            self.wf_free_node_head()
            &&
            self.wf_free_node_tail()
            &&
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
            (forall|i: int|
                #![trigger self.arr_seq@[self.value_list@[i as int] as int].next]
                #![trigger self.next_value_node_of(i)]
                0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == self.next_value_node_of(i))
            &&
            (forall|i: int|
                #![trigger self.arr_seq@[self.value_list@[i as int] as int].prev]
                #![trigger self.prev_value_node_of(i)]
                0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == self.prev_value_node_of(i))
            &&
            (forall|i: int| 0 <= i < self.value_list@.len() ==> #[trigger] self.value_list@[i as int] < N)
            &&
            (forall|i: nat| 0 <= i < self.value_list@.len() ==> #[trigger] self.value_list@[i as int] >= 0)
            &&
            self.value_list@.no_duplicates()
            &&
            self.wf_value_node_head()
            &&
            self.wf_value_node_tail()
            &&
            self.value_list_len == self.value_list@.len()
        }
    
        pub open spec fn free_list_ptr_all_null(&self) -> bool
        {
            forall|i: Index|
                #![trigger self.arr_seq@[i as int].value]
                #![trigger self.value_list@.contains(i)]
                0 <= i < N && #[trigger] self.arr_seq@[i as int].value != NULL_POINTER ==> self.value_list@.contains(i)
        }
    
        pub open spec fn array_wf(&self) -> bool{
            (self.arr_seq@.len() == N)
            &&
            (self.size == N)
        }
    
        pub open spec fn spec_seq_wf(&self) -> bool
        {
            self.spec_seq@.len() == self.value_list_len
            &&
            forall|i:int| 0 <= i < self.value_list_len ==> #[trigger] self.arr_seq@[self.value_list@[i as int] as int].value == self.spec_seq@[i as int]
        }
    
        pub open spec fn wf(&self) -> bool{
            (self.array_wf())
            &&
            (self.free_list_len + self.value_list_len == N)
            &&
            (self.value_list_wf())
            &&
            (self.free_list_wf())
            &&
            (forall|i:Index|                
                #![trigger self.free_list@.contains(i)]
                #![trigger self.value_list@.contains(i)]
                0<= i < N ==> self.free_list@.contains(i) ^ self.value_list@.contains(i))
            &&
            (self.spec_seq_wf())
            &&
            (self.free_list_ptr_all_null())
        }
    }
}