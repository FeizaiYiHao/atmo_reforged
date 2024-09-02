assert(self.array_wf());
assert(self.free_list_len + self.value_list_len == N);
assert(self.value_list_wf());
assert(self.free_list_wf());
assert(forall|i:SLLIndex|                
    #![trigger self.free_list@.contains(i)]
    #![trigger self.value_list@.contains(i)]
    0<= i < N ==> self.free_list@.contains(i) ^ self.value_list@.contains(i));
assert(self.spec_seq_wf());
assert(self.free_list_ptr_all_null());