assert(self.container_map_4k@.dom().subset_of(self.allocated_pages_4k@));
assert(self.container_map_2m@.dom().subset_of(self.allocated_pages_4k@));
assert(self.container_map_1g@.dom().subset_of(self.allocated_pages_4k@));
assert(forall|i:int|
    #![trigger self.page_array@[i], self.page_array@[i].owning_container.is_Some()]
    0<=i<NUM_PAGES 
    &&
    (
        self.page_array@[i].state == PageState::Mapped4k
        ||
        self.page_array@[i].state == PageState::Mapped2m
        ||
        self.page_array@[i].state == PageState::Mapped1g
    )
    ==> 
    self.page_array@[i].owning_container.is_Some());
assert(forall|i:int|
    #![trigger self.page_array@[i], self.page_array@[i].owning_container.is_Some()]
    0<=i<NUM_PAGES 
    &&
    self.page_array@[i].owning_container.is_Some()
    ==> 
    (
        self.page_array@[i].state == PageState::Mapped4k
        ||
        self.page_array@[i].state == PageState::Mapped2m
        ||
        self.page_array@[i].state == PageState::Mapped1g
    ));
assert(forall|i:usize|
    #![trigger self.page_array@[i as int].state, self.page_array@[i as int].owning_container]
    0<=i<NUM_PAGES && self.page_array@[i as int].state == PageState::Mapped4k
    ==>
    self.container_map_4k@.dom().contains(self.page_array@[i as int].owning_container.unwrap())
    &&
    self.container_map_4k@[self.page_array@[i as int].owning_container.unwrap()].contains(page_index2page_ptr(i)));
assert(forall|i:usize|
    #![trigger self.page_array@[i as int].state, self.page_array@[i as int].owning_container]
    0<=i<NUM_PAGES && self.page_array@[i as int].state == PageState::Mapped2m
    ==>
    self.container_map_2m@.dom().contains(self.page_array@[i as int].owning_container.unwrap())
    &&
    self.container_map_2m@[self.page_array@[i as int].owning_container.unwrap()].contains(page_index2page_ptr(i)));
assert(forall|i:usize|
    #![trigger self.page_array@[i as int].state, self.page_array@[i as int].owning_container]
    0<=i<NUM_PAGES && self.page_array@[i as int].state == PageState::Mapped1g
    ==>
    self.container_map_1g@.dom().contains(self.page_array@[i as int].owning_container.unwrap())
    &&
    self.container_map_1g@[self.page_array@[i as int].owning_container.unwrap()].contains(page_index2page_ptr(i)));
assert(forall|c_ptr:ContainerPtr, page_ptr:PagePtr|
    #![trigger self.container_map_4k@[c_ptr].contains(page_ptr)]
    self.container_map_4k@.dom().contains(c_ptr) && self.container_map_4k@[c_ptr].contains(page_ptr)
    ==>
    page_ptr_valid(page_ptr)
    &&
    self.page_array@[page_ptr2page_index(page_ptr) as int].state == PageState::Mapped4k
    &&
    self.page_array@[page_ptr2page_index(page_ptr) as int].owning_container.unwrap() == c_ptr);
assert(forall|c_ptr:ContainerPtr, page_ptr:PagePtr|
    #![trigger self.container_map_2m@[c_ptr].contains(page_ptr)]
    self.container_map_2m@.dom().contains(c_ptr) && self.container_map_2m@[c_ptr].contains(page_ptr)
    ==>
    page_ptr_2m_valid(page_ptr)
    &&
    self.page_array@[page_ptr2page_index(page_ptr) as int].state == PageState::Mapped2m
    &&
    self.page_array@[page_ptr2page_index(page_ptr) as int].owning_container.unwrap() == c_ptr);
assert(forall|c_ptr:ContainerPtr, page_ptr:PagePtr|
    #![trigger self.container_map_1g@[c_ptr].contains(page_ptr)]
    self.container_map_1g@.dom().contains(c_ptr) && self.container_map_1g@[c_ptr].contains(page_ptr)
    ==>
    page_ptr_1g_valid(page_ptr)
    &&
    self.page_array@[page_ptr2page_index(page_ptr) as int].state == PageState::Mapped1g
    &&
    self.page_array@[page_ptr2page_index(page_ptr) as int].owning_container.unwrap() == c_ptr);