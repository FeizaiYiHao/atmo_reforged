assert(forall|i: int|
    #![trigger self.arr_seq@[self.value_list@[i as int] as int].next]
    #![trigger self.next_value_node_of(i)]
    0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == self.next_value_node_of(i));
assert(forall|i: int|
    #![trigger self.arr_seq@[self.value_list@[i as int] as int].prev]
    #![trigger self.prev_value_node_of(i)]
    0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == self.prev_value_node_of(i));
assert(forall|i: int| 
    #![trigger self.value_list@[i as int]] 
    0 <= i < self.value_list@.len() ==> 0 <= self.value_list@[i as int] < N);
assert(self.unique());
assert(self.wf_value_node_head());
assert(self.wf_value_node_tail());
assert(self.value_list_len == self.value_list@.len());