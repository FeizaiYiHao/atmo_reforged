assert(self.free_pages_2m.wf());
assert(forall|i:int|
    #![trigger page_ptr_2m_valid(self.free_pages_2m@[i])]
    0<=i<self.free_pages_2m.len() ==> page_ptr_2m_valid(self.free_pages_2m@[i]));
assert(forall|i:int|
    #![trigger self.page_array@[i].rev_pointer]
    #![trigger self.page_array@[i].addr]
    0<=i<NUM_PAGES && self.page_array@[i].state == PageState::Free2m
    ==> 
    self.free_pages_2m@.contains(self.page_array@[i].addr) && self.free_pages_2m.node_ref_valid(self.page_array@[i].rev_pointer));
assert(forall|page_ptr:PagePtr| 
    #![trigger self.page_array@[page_ptr2page_index(page_ptr) as int].state]
    self.free_pages_2m@.contains(page_ptr) 
    ==>
    self.page_array@[page_ptr2page_index(page_ptr) as int].state == PageState::Free2m);
assert(forall|page_ptr:PagePtr| 
    #![trigger self.page_array@[page_ptr2page_index(page_ptr) as int].is_io_page]
    self.free_pages_2m@.contains(page_ptr) 
    ==> 
    self.page_array@[page_ptr2page_index(page_ptr) as int].is_io_page == false);
assert(forall|i:int, j:int|
    #![trigger self.page_array@[i].rev_pointer, self.page_array@[j].rev_pointer]
    0<i<NUM_PAGES && 0<j<NUM_PAGES && i != j && self.page_array@[i].state == PageState::Free2m && self.page_array@[j].state == PageState::Free2m
    ==>
    self.page_array@[i].rev_pointer != self.page_array@[j].rev_pointer);