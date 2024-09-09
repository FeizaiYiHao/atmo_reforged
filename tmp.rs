pub open spec fn free_pages_4k_wf(&self) -> bool{
    &&&
    self.free_pages_4k.wf()            
    &&&
    self.free_pages_4k.unique()
    &&&
    forall|i:int|
        #![trigger self.free_pages_4k@.contains(self.page_array@[i].addr)]
        #![trigger self.free_pages_4k.node_ref_valid(self.page_array@[i].rev_pointer)]
        #![trigger self.free_pages_4k.node_ref_resolve(self.page_array@[i].rev_pointer)]
        0<=i<NUM_PAGES && self.page_array@[i].state == PageState::Free4k
        ==> 
        self.free_pages_4k@.contains(self.page_array@[i].addr) && self.free_pages_4k.node_ref_valid(self.page_array@[i].rev_pointer) && self.free_pages_4k.node_ref_resolve(self.page_array@[i].rev_pointer) == self.page_array@[i].addr
    &&&
    forall|page_ptr:PagePtr| 
        #![trigger page_ptr_4k_valid(page_ptr)]
        #![trigger self.page_array@[page_ptr2page_index(page_ptr) as int].state]
        #![trigger self.page_array@[page_ptr2page_index(page_ptr) as int].is_io_page]
        self.free_pages_4k@.contains(page_ptr) 
        ==>
        page_ptr_4k_valid(page_ptr)
        &&
        self.page_array@[page_ptr2page_index(page_ptr) as int].state == PageState::Free4k
        &&
        self.page_array@[page_ptr2page_index(page_ptr) as int].is_io_page == false
    &&&
    forall|i:int, j:int|
        #![trigger self.page_array@[i].rev_pointer, self.page_array@[j].rev_pointer]
        0<=i<NUM_PAGES && 0<j<NUM_PAGES && i != j && self.page_array@[i].state == PageState::Free4k && self.page_array@[j].state == PageState::Free4k
        ==>
        self.page_array@[i].rev_pointer != self.page_array@[j].rev_pointer
}