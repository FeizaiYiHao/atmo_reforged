use vstd::prelude::*;
verus! {
    use crate::define::*;
    use crate::allocator::page::*;
    use crate::array::*;
    use crate::slinkedlist::spec::*;
    use crate::util::page_ptr_util_u::*;
    use crate::allocator::page_allocator_spec::*;
    use crate::lemma::lemma_u::*;

    impl PageAllocator{
        pub fn alloc_page_2m(&mut self) 
            // -> (ret:(PagePtr, PagePerm2m))
            requires 
                old(self).wf(),
                old(self).free_pages_2m@.len() > 0,
        {
            proof{
                page_ptr_lemma();
                seq_skip_lemma::<PagePtr>();
                page_ptr_lemma();

            }
            let ret = self.free_pages_2m.pop().0;
            assert(page_ptr_valid(ret));
            assert(page_index_valid(page_ptr2page_index(ret)));
            self.set_state(page_ptr2page_index(ret), PageState::Allocated2m);
            assert(page_index2page_ptr(page_ptr2page_index(ret)) == ret);
            assert(self.page_array@[page_ptr2page_index(ret) as int].addr == page_index2page_ptr(page_ptr2page_index(ret)));
            proof{
                self.allocated_pages_2m@ = self.allocated_pages_2m@.insert(ret);
            }
            let tracked mut ret_perm = self.page_perms_2m.borrow_mut().tracked_remove(ret);
            assert(self.page_array_wf());
            assert(self.free_pages_4k_wf());
            assert(self.free_pages_2m_wf()) by {
                assert(forall|i:int|
                    #![trigger self.page_array@[i].rev_pointer]
                    #![trigger self.page_array@[i]]
                    0<=i<NUM_PAGES && self.page_array@[i].state == PageState::Free2m && self.page_array@[i].addr != ret
                    ==> 
                    self.free_pages_2m@.contains(self.page_array@[i].addr));
                    assert(forall|i:int|
                        #![trigger self.page_array@[i].rev_pointer]
                        #![trigger self.page_array@[i]]
                        0<=i<NUM_PAGES && self.page_array@[i].state == PageState::Free2m
                        ==> 
                        self.free_pages_2m@.contains(self.page_array@[i].addr));
                assert(forall|i:int|
                    #![trigger self.page_array@[i].rev_pointer]
                    #![trigger self.page_array@[i].addr]
                    0<=i<NUM_PAGES && self.page_array@[i].state == PageState::Free2m
                    ==> 
                    self.free_pages_2m@.contains(self.page_array@[i].addr) && self.free_pages_2m.node_ref_valid(self.page_array@[i].rev_pointer));
            };
            // assert(self.free_pages_1g_wf());
            // assert(self.allocated_pages_4k_wf());
            // assert(self.allocated_pages_2m_wf());
            // assert(self.allocated_pages_1g_wf());
            // assert(self.mapped_pages_4k_wf());
            // assert(self.mapped_pages_2m_wf());
            // assert(self.mapped_pages_1g_wf());
            // assert(self.merged_pages_wf());
            // assert(self.hugepages_wf());
            // assert(self.perm_wf());
        }
    }
}