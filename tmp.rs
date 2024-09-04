pub open spec fn allocated_pages_1g_wf(&self) -> bool{
    &&&
    self.allocated_pages_1g@.finite()
    &&&
    forall|p:PagePtr|
        #![trigger self.allocated_pages_1g@.contains(p), page_ptr_valid(p)]
        self.allocated_pages_1g@.contains(p) ==> page_ptr_valid(p)
    &&&
    forall|i:int|
        #![trigger self.page_array@[i].addr]
        0<=i<NUM_PAGES && self.page_array@[i].state == PageState::Allocated1g
        ==> 
        self.allocated_pages_1g@.contains(self.page_array@[i].addr) 
    &&&
    forall|p:PagePtr| 
        #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
        self.allocated_pages_1g@.contains(p) 
        ==>
        self.page_array@[page_ptr2page_index(p) as int].state == PageState::Allocated1g
}