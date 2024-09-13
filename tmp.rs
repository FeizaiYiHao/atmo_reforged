fn remove_io_mapping_4k_helper1(&mut self, target_ptr: PagePtr, ioid: IOid, va: VAddr)
requires
    old(self).wf(),
    old(self).mapped_pages_4k().contains(target_ptr),
    old(self).page_io_mappings(target_ptr).contains((ioid, va)),
    old(self).page_array@[page_ptr2page_index(target_ptr) as int].is_io_page == true,
    old(self).page_array@[page_ptr2page_index(target_ptr) as int].ref_count == 1,
ensures
    self.wf(),
    self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
    self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
    self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
    forall|p:PagePtr| 
        self.page_is_mapped(p) && p != target_ptr ==> 
        self.page_mappings(p) =~= old(self).page_mappings(p)
        &&
        self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
    self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr),
    self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr).remove((ioid,va)),
{
proof{
    page_ptr_lemma();
    seq_push_lemma::<PagePtr>();
    self.free_pages_1g.wf_to_no_duplicates();
    self.free_pages_2m.wf_to_no_duplicates();
    self.free_pages_4k.wf_to_no_duplicates();
}
assert(page_ptr_valid(target_ptr));
self.set_ref_count(page_ptr2page_index(target_ptr), 0);
self.set_io_mapping(page_ptr2page_index(target_ptr), Ghost(Set::empty()));
self.set_state(page_ptr2page_index(target_ptr), PageState::Unavailable4k);
proof{
    self.mapped_pages_4k@ = self.mapped_pages_4k@.remove(target_ptr);
}
let tracked mut removed_perm = self.page_perms_4k.borrow_mut().tracked_remove(target_ptr);
    assert(self.page_array_wf());
    assert(self.free_pages_4k_wf());
    assert(self.free_pages_2m_wf()) by {page_ptr_2m_lemma();};
    assert(self.free_pages_1g_wf()) by {page_ptr_1g_lemma();};
    assert(self.allocated_pages_4k_wf());
    assert(self.allocated_pages_2m_wf()) by {page_ptr_2m_lemma();};
    assert(self.allocated_pages_1g_wf()) by {page_ptr_1g_lemma();};
    assert(self.mapped_pages_4k_wf()) ;
    assert(self.mapped_pages_2m_wf()) by {page_ptr_2m_lemma();};
    assert(self.mapped_pages_1g_wf()) by {page_ptr_1g_lemma();};
    assert(self.merged_pages_wf()) by {
        page_ptr_page_index_truncate_lemma();
    };
    assert(self.hugepages_wf()) by {
        page_index_lemma();
        page_ptr_2m_lemma();
        page_ptr_1g_lemma();
        assert(
            forall|i:usize|
            #![trigger page_index_2m_valid(i)]
            #![trigger self.page_array@[i as int].state]
            #![trigger old(self).page_array@[i as int].state]
            #![trigger self.page_array@[i as int].is_io_page]
            #![trigger old(self).page_array@[i as int].is_io_page]
            0 <= i < NUM_PAGES && i != page_ptr2page_index(target_ptr) 
            ==>
            self.page_array@[i as int].is_io_page == old(self).page_array@[i as int].is_io_page 
            &&
            self.page_array@[i as int].state == old(self).page_array@[i as int].state 
        );
        assert(
            forall|i:usize, j:usize|
            #![trigger page_index_2m_valid(i), page_index_valid(j)]
            #![trigger page_index_2m_valid(i), self.page_array@[i as int].state, self.page_array@[j as int].state]
            #![trigger page_index_2m_valid(i), self.page_array@[i as int].is_io_page, self.page_array@[j as int].is_io_page]
            0 <= i < NUM_PAGES && page_index_2m_valid(i) 
            && i < j < i + 0x200 && j != page_ptr2page_index(target_ptr) && i != page_ptr2page_index(target_ptr) 
            ==>
            self.page_array@[j as int].state == old(self).page_array@[j as int].state
            &&
            self.page_array@[i as int].is_io_page == old(self).page_array@[i as int].is_io_page 
            &&
            self.page_array@[j as int].is_io_page == old(self).page_array@[j as int].is_io_page 
        );           
        assert(
            forall|i:usize, j:usize|
            #![trigger page_index_1g_valid(i), page_index_valid(j)]
            #![trigger page_index_1g_valid(i), self.page_array@[i as int].state, self.page_array@[j as int].state]
            #![trigger page_index_1g_valid(i), self.page_array@[i as int].is_io_page, self.page_array@[j as int].is_io_page]
            0 <= i < NUM_PAGES && page_index_1g_valid(i) 
            && i < j < i + 0x40000 && j != page_ptr2page_index(target_ptr) && i != page_ptr2page_index(target_ptr) 
            ==>
            page_index_valid(j)
            &&
            self.page_array@[j as int].state == old(self).page_array@[j as int].state
            &&
            self.page_array@[i as int].is_io_page == old(self).page_array@[i as int].is_io_page 
            &&
            self.page_array@[j as int].is_io_page == old(self).page_array@[j as int].is_io_page 
        );
    };   
}

fn remove_io_mapping_4k_helper2(&mut self, target_ptr: PagePtr, ioid: IOid, va: VAddr)
requires
    old(self).wf(),
    old(self).mapped_pages_4k().contains(target_ptr),
    old(self).page_io_mappings(target_ptr).contains((ioid, va)),
    old(self).page_array@[page_ptr2page_index(target_ptr) as int].is_io_page == false,
    old(self).page_array@[page_ptr2page_index(target_ptr) as int].ref_count == 1,
ensures
    self.wf(),
    self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
    self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
    self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
    forall|p:PagePtr| 
        self.page_is_mapped(p) && p != target_ptr ==> 
        self.page_mappings(p) =~= old(self).page_mappings(p)
        &&
        self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
    self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr),
    self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr).remove((ioid,va)),
{
proof{
    page_ptr_lemma();
    seq_push_lemma::<PagePtr>();
    self.free_pages_1g.wf_to_no_duplicates();
    self.free_pages_2m.wf_to_no_duplicates();
    self.free_pages_4k.wf_to_no_duplicates();
}
assert(page_ptr_valid(target_ptr));
proof{
    self.free_pages_4k@.unique_seq_to_set();
    self.len_lemma_mapped_4k(target_ptr);
}
let rev_index = self.free_pages_4k.push(&target_ptr);
self.set_rev_pointer(page_ptr2page_index(target_ptr), rev_index);
self.set_ref_count(page_ptr2page_index(target_ptr), 0);
self.set_io_mapping(page_ptr2page_index(target_ptr), Ghost(Set::empty()));
self.set_state(page_ptr2page_index(target_ptr), PageState::Free4k);
proof{
    self.mapped_pages_4k@ = self.mapped_pages_4k@.remove(target_ptr);
}
    assert(self.page_array_wf());
    assert(self.free_pages_4k_wf());
    assert(self.free_pages_2m_wf()) by {page_ptr_2m_lemma();};
    assert(self.free_pages_1g_wf()) by {page_ptr_1g_lemma();};
    assert(self.allocated_pages_4k_wf());
    assert(self.allocated_pages_2m_wf()) by {page_ptr_2m_lemma();};
    assert(self.allocated_pages_1g_wf()) by {page_ptr_1g_lemma();};
    assert(self.mapped_pages_4k_wf()) ;
    assert(self.mapped_pages_2m_wf()) by {page_ptr_2m_lemma();};
    assert(self.mapped_pages_1g_wf()) by {page_ptr_1g_lemma();};
    assert(self.merged_pages_wf()) by {
        page_ptr_page_index_truncate_lemma();
    };
    assert(self.hugepages_wf()) by {
        page_index_lemma();
        page_ptr_2m_lemma();
        page_ptr_1g_lemma();
        assert(
            forall|i:usize|
            #![trigger page_index_2m_valid(i)]
            #![trigger self.page_array@[i as int].state]
            #![trigger old(self).page_array@[i as int].state]
            #![trigger self.page_array@[i as int].is_io_page]
            #![trigger old(self).page_array@[i as int].is_io_page]
            0 <= i < NUM_PAGES && i != page_ptr2page_index(target_ptr) 
            ==>
            self.page_array@[i as int].is_io_page == old(self).page_array@[i as int].is_io_page 
            &&
            self.page_array@[i as int].state == old(self).page_array@[i as int].state 
        );
        assert(
            forall|i:usize, j:usize|
            #![trigger page_index_2m_valid(i), page_index_valid(j)]
            #![trigger page_index_2m_valid(i), self.page_array@[i as int].state, self.page_array@[j as int].state]
            #![trigger page_index_2m_valid(i), self.page_array@[i as int].is_io_page, self.page_array@[j as int].is_io_page]
            0 <= i < NUM_PAGES && page_index_2m_valid(i) 
            && i < j < i + 0x200 && j != page_ptr2page_index(target_ptr) && i != page_ptr2page_index(target_ptr) 
            ==>
            self.page_array@[j as int].state == old(self).page_array@[j as int].state
            &&
            self.page_array@[i as int].is_io_page == old(self).page_array@[i as int].is_io_page 
            &&
            self.page_array@[j as int].is_io_page == old(self).page_array@[j as int].is_io_page 
        );           
        assert(
            forall|i:usize, j:usize|
            #![trigger page_index_1g_valid(i), page_index_valid(j)]
            #![trigger page_index_1g_valid(i), self.page_array@[i as int].state, self.page_array@[j as int].state]
            #![trigger page_index_1g_valid(i), self.page_array@[i as int].is_io_page, self.page_array@[j as int].is_io_page]
            0 <= i < NUM_PAGES && page_index_1g_valid(i) 
            && i < j < i + 0x40000 && j != page_ptr2page_index(target_ptr) && i != page_ptr2page_index(target_ptr) 
            ==>
            page_index_valid(j)
            &&
            self.page_array@[j as int].state == old(self).page_array@[j as int].state
            &&
            self.page_array@[i as int].is_io_page == old(self).page_array@[i as int].is_io_page 
            &&
            self.page_array@[j as int].is_io_page == old(self).page_array@[j as int].is_io_page 
        );
    };
}

fn remove_io_mapping_4k_helper3(&mut self, target_ptr: PagePtr, ioid: IOid, va: VAddr)
requires
    old(self).wf(),
    old(self).mapped_pages_4k().contains(target_ptr),
    old(self).page_io_mappings(target_ptr).contains((ioid, va)),
    old(self).page_array@[page_ptr2page_index(target_ptr) as int].ref_count != 1,
ensures
    self.wf(),
    self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
    self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
    self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
    forall|p:PagePtr| 
        self.page_is_mapped(p) && p != target_ptr ==> 
        self.page_mappings(p) =~= old(self).page_mappings(p)
        &&
        self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
    self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr),
    self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr).remove((ioid,va)),
{
proof{
    page_ptr_lemma();
    seq_push_lemma::<PagePtr>();
    self.free_pages_1g.wf_to_no_duplicates();
    self.free_pages_2m.wf_to_no_duplicates();
    self.free_pages_4k.wf_to_no_duplicates();
}
proof{
    self.len_lemma_mapped_4k(target_ptr);
}
let old_ref_count = self.page_array.get(page_ptr2page_index(target_ptr)).ref_count;
let old_io_mappings = self.page_array.get(page_ptr2page_index(target_ptr)).io_mappings;
self.set_ref_count(page_ptr2page_index(target_ptr), old_ref_count - 1);
self.set_io_mapping(page_ptr2page_index(target_ptr), Ghost(old_io_mappings@.remove((ioid, va))));
    assert(self.page_array_wf());
    assert(self.free_pages_4k_wf());
    assert(self.free_pages_2m_wf()) by {page_ptr_2m_lemma();};
    assert(self.free_pages_1g_wf()) by {page_ptr_1g_lemma();};
    assert(self.allocated_pages_4k_wf());
    assert(self.allocated_pages_2m_wf()) by {page_ptr_2m_lemma();};
    assert(self.allocated_pages_1g_wf()) by {page_ptr_1g_lemma();};
    assert(self.mapped_pages_4k_wf()) ;
    assert(self.mapped_pages_2m_wf()) by {page_ptr_2m_lemma();};
    assert(self.mapped_pages_1g_wf()) by {page_ptr_1g_lemma();};
    assert(self.merged_pages_wf()) by {
        page_ptr_page_index_truncate_lemma();
    };
    assert(self.hugepages_wf()) by {
        page_index_lemma();
        page_ptr_2m_lemma();
        page_ptr_1g_lemma();
        assert(
            forall|i:usize|
            #![trigger page_index_2m_valid(i)]
            #![trigger self.page_array@[i as int].state]
            #![trigger old(self).page_array@[i as int].state]
            #![trigger self.page_array@[i as int].is_io_page]
            #![trigger old(self).page_array@[i as int].is_io_page]
            0 <= i < NUM_PAGES && i != page_ptr2page_index(target_ptr) 
            ==>
            self.page_array@[i as int].is_io_page == old(self).page_array@[i as int].is_io_page 
            &&
            self.page_array@[i as int].state == old(self).page_array@[i as int].state 
        );
        assert(
            forall|i:usize, j:usize|
            #![trigger page_index_2m_valid(i), page_index_valid(j)]
            #![trigger page_index_2m_valid(i), self.page_array@[i as int].state, self.page_array@[j as int].state]
            #![trigger page_index_2m_valid(i), self.page_array@[i as int].is_io_page, self.page_array@[j as int].is_io_page]
            0 <= i < NUM_PAGES && page_index_2m_valid(i) 
            && i < j < i + 0x200 && j != page_ptr2page_index(target_ptr) && i != page_ptr2page_index(target_ptr) 
            ==>
            self.page_array@[j as int].state == old(self).page_array@[j as int].state
            &&
            self.page_array@[i as int].is_io_page == old(self).page_array@[i as int].is_io_page 
            &&
            self.page_array@[j as int].is_io_page == old(self).page_array@[j as int].is_io_page 
        );           
        assert(
            forall|i:usize, j:usize|
            #![trigger page_index_1g_valid(i), page_index_valid(j)]
            #![trigger page_index_1g_valid(i), self.page_array@[i as int].state, self.page_array@[j as int].state]
            #![trigger page_index_1g_valid(i), self.page_array@[i as int].is_io_page, self.page_array@[j as int].is_io_page]
            0 <= i < NUM_PAGES && page_index_1g_valid(i) 
            && i < j < i + 0x40000 && j != page_ptr2page_index(target_ptr) && i != page_ptr2page_index(target_ptr) 
            ==>
            page_index_valid(j)
            &&
            self.page_array@[j as int].state == old(self).page_array@[j as int].state
            &&
            self.page_array@[i as int].is_io_page == old(self).page_array@[i as int].is_io_page 
            &&
            self.page_array@[j as int].is_io_page == old(self).page_array@[j as int].is_io_page 
        );
    };
}
pub fn remove_io_mapping_4k(&mut self, target_ptr: PagePtr, ioid: IOid, va: VAddr)
requires
    old(self).wf(),
    old(self).mapped_pages_4k().contains(target_ptr),
    old(self).page_io_mappings(target_ptr).contains((ioid, va)),
ensures
    self.wf(),
    self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
    self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
    self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
    forall|p:PagePtr| 
        self.page_is_mapped(p) && p != target_ptr ==> 
        self.page_mappings(p) =~= old(self).page_mappings(p)
        &&
        self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
    self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr),
    self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr).remove((ioid,va)),
{
proof{
    page_ptr_lemma();
    seq_push_lemma::<PagePtr>();
    self.free_pages_1g.wf_to_no_duplicates();
    self.free_pages_2m.wf_to_no_duplicates();
    self.free_pages_4k.wf_to_no_duplicates();
}
assert(page_ptr_valid(target_ptr));
let old_ref_count = self.page_array.get(page_ptr2page_index(target_ptr)).ref_count;
let is_io_page = self.page_array.get(page_ptr2page_index(target_ptr)).is_io_page;
let old_io_mappings = self.page_array.get(page_ptr2page_index(target_ptr)).io_mappings;
if old_ref_count == 1 && is_io_page {
    self.remove_io_mapping_4k_helper1(target_ptr, ioid, va);
}
else if old_ref_count == 1 {
    self.remove_io_mapping_4k_helper2(target_ptr, ioid, va);
}
else{
    self.remove_io_mapping_4k_helper3(target_ptr, ioid, va);
}
}