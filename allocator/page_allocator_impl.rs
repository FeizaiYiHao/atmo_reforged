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

            }
            let ret = self.free_pages_2m.pop().0;
            assert(page_ptr_valid(ret));
            self.set_state(page_ptr2page_index(ret), PageState::Allocated2m);
            proof{
                self.allocated_pages_2m@ = self.allocated_pages_2m@.insert(ret);
            }
            let tracked mut ret_perm = self.page_perms_2m.borrow_mut().tracked_remove(ret);
            assert(self.page_array_wf());
            assert(self.free_pages_4k_wf());
            assert(self.free_pages_2m_wf());
            assert(self.free_pages_1g_wf());
            assert(self.allocated_pages_4k_wf());
            assert(self.allocated_pages_2m_wf());
            assert(self.allocated_pages_1g_wf());
            assert(self.mapped_pages_4k_wf()) ;
            assert(self.mapped_pages_2m_wf());
            assert(self.mapped_pages_1g_wf());
            assert(self.merged_pages_wf());
            assert(self.hugepages_wf());
            assert(self.perm_wf());
        }
    }
}