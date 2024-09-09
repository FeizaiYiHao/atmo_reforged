use vstd::prelude::*;
verus! {
    use crate::define::*;
    use crate::allocator::page::*;
    use crate::array::*;
    use crate::slinkedlist::spec_impl_u::*;
    use crate::util::page_ptr_util_u::*;
    // use vstd::simple_pptr::*;
    use crate::lemma::lemma_u::*;
    use vstd::set_lib::*;

    pub struct PageAllocator{
        pub page_array: Array<Page,NUM_PAGES>,

        pub free_pages_4k: StaticLinkedList<PagePtr, NUM_PAGES>,
        pub free_pages_2m: StaticLinkedList<PagePtr, NUM_PAGES>,
        pub free_pages_1g: StaticLinkedList<PagePtr, NUM_PAGES>,
    
        pub allocated_pages_4k: Ghost<Set<PagePtr>>,
        pub allocated_pages_2m: Ghost<Set<PagePtr>>,
        pub allocated_pages_1g: Ghost<Set<PagePtr>>,

        pub mapped_pages_4k: Ghost<Set<PagePtr>>,
        pub mapped_pages_2m: Ghost<Set<PagePtr>>,
        pub mapped_pages_1g: Ghost<Set<PagePtr>>,
    
        // pub available_pages: Ghost<Set<PagePtr>>,
    
        pub page_perms_4k: Tracked<Map<PagePtr,PagePerm4k>>,
        pub page_perms_2m: Tracked<Map<PagePtr,PagePerm2m>>,
        pub page_perms_1g: Tracked<Map<PagePtr,PagePerm1g>>,
    
        // //fields for virtual addresses
        // pub free_pcids: ArrayVec<Pcid,PCID_MAX>,
        // pub page_tables: MarsArray<PageTable,PCID_MAX>,
    }

    impl PageAllocator{
        pub open spec fn page_is_mapped(&self, p:PagePtr) -> bool 
        {
            |||
            self.mapped_pages_4k().contains(p)
            |||
            self.mapped_pages_2m().contains(p)
            |||
            self.mapped_pages_1g().contains(p)
        }
        pub closed spec fn free_pages_4k(&self) -> Set<PagePtr>{
            self.free_pages_4k@.to_set()
        }
        pub closed spec fn free_pages_2m(&self) -> Set<PagePtr>{
            self.free_pages_2m@.to_set()
        }
        pub closed spec fn free_pages_1g(&self) -> Set<PagePtr>{
            self.free_pages_1g@.to_set()
        }
        pub closed spec fn allocated_pages_4k(&self) -> Set<PagePtr>{
            self.allocated_pages_4k@
        }
        pub closed spec fn allocated_pages_2m(&self) -> Set<PagePtr>{
            self.allocated_pages_2m@
        }
        pub closed spec fn allocated_pages_1g(&self) -> Set<PagePtr>{
            self.allocated_pages_1g@
        }
        pub closed spec fn mapped_pages_4k(&self) -> Set<PagePtr>{
            self.mapped_pages_4k@
        }
        pub closed spec fn mapped_pages_2m(&self) -> Set<PagePtr>{
            self.mapped_pages_2m@
        }
        pub closed spec fn mapped_pages_1g(&self) -> Set<PagePtr>{
            self.mapped_pages_1g@
        }
        pub closed spec fn page_mappings(&self, p:PagePtr) -> Set<(Pcid,VAddr)>
            recommends
                self.page_is_mapped(p),
                self.mapped_pages_1g().contains(p) || self.mapped_pages_2m().contains(p) || self.mapped_pages_4k().contains(p),
        {
            self.page_array@[page_ptr2page_index(p) as int].mappings@
        }        
        pub closed spec fn page_io_mappings(&self, p:PagePtr) -> Set<(Pcid,VAddr)>
            recommends
                self.page_is_mapped(p),
                self.mapped_pages_1g().contains(p) || self.mapped_pages_2m().contains(p) || self.mapped_pages_4k().contains(p),
        {
            self.page_array@[page_ptr2page_index(p) as int].io_mappings@
        }


        pub open spec fn page_array_wf(&self) -> bool{
            &&&
            self.page_array.wf()
            &&&
            forall|i:usize| 
                #![trigger self.page_array@[i as int]]
                // #![trigger page_index2page_ptr(i)]
                0<=i<NUM_PAGES ==> self.page_array@[i as int].addr == page_index2page_ptr(i)
            &&&
            forall|i:int| 
                #![trigger self.page_array@[i].mappings]
                0<=i<NUM_PAGES ==> self.page_array@[i].mappings@.finite()
            &&&
            forall|i:int| 
                #![trigger self.page_array@[i].io_mappings]
                0<=i<NUM_PAGES ==> self.page_array@[i].io_mappings@.finite()
        }

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
                #![trigger self.page_array@[i].is_io_page]
                0<=i<NUM_PAGES && self.page_array@[i].state == PageState::Free4k
                ==> 
                self.free_pages_4k@.contains(self.page_array@[i].addr) 
                && 
                self.free_pages_4k.node_ref_valid(self.page_array@[i].rev_pointer)
                && 
                self.free_pages_4k.node_ref_resolve(self.page_array@[i].rev_pointer) == self.page_array@[i].addr
                &&
                self.page_array@[i].is_io_page == false
            &&&
            forall|page_ptr:PagePtr| 
                #![trigger page_ptr_valid(page_ptr)]
                #![trigger self.page_array@[page_ptr2page_index(page_ptr) as int].state]
                self.free_pages_4k@.contains(page_ptr) 
                ==>
                page_ptr_valid(page_ptr)
                &&
                self.page_array@[page_ptr2page_index(page_ptr) as int].state == PageState::Free4k
            &&&
            forall|i:int, j:int|
                #![trigger self.page_array@[i].rev_pointer, self.page_array@[j].rev_pointer]
                0<=i<NUM_PAGES && 0<j<NUM_PAGES && i != j && self.page_array@[i].state == PageState::Free4k && self.page_array@[j].state == PageState::Free4k
                ==>
                self.page_array@[i].rev_pointer != self.page_array@[j].rev_pointer
        }

        pub open spec fn free_pages_2m_wf(&self) -> bool{
            &&&
            self.free_pages_2m.wf()            
            &&&
            self.free_pages_2m.unique()
            &&&
            forall|i:int|
                #![trigger self.free_pages_2m@.contains(self.page_array@[i].addr)]
                #![trigger self.free_pages_2m.node_ref_valid(self.page_array@[i].rev_pointer)]
                #![trigger self.free_pages_2m.node_ref_resolve(self.page_array@[i].rev_pointer)]
                #![trigger self.page_array@[i].is_io_page]
                0<=i<NUM_PAGES && self.page_array@[i].state == PageState::Free2m
                ==> 
                self.free_pages_2m@.contains(self.page_array@[i].addr) 
                && 
                self.free_pages_2m.node_ref_valid(self.page_array@[i].rev_pointer) 
                && 
                self.free_pages_2m.node_ref_resolve(self.page_array@[i].rev_pointer) == self.page_array@[i].addr
                &&
                self.page_array@[i].is_io_page == false
            &&&
            forall|page_ptr:PagePtr| 
                #![trigger page_ptr_2m_valid(page_ptr)]
                #![trigger self.page_array@[page_ptr2page_index(page_ptr) as int].state]
                self.free_pages_2m@.contains(page_ptr) 
                ==>
                page_ptr_2m_valid(page_ptr)
                &&
                self.page_array@[page_ptr2page_index(page_ptr) as int].state == PageState::Free2m
            &&&
            forall|i:int, j:int|
                #![trigger self.page_array@[i].rev_pointer, self.page_array@[j].rev_pointer]
                0<=i<NUM_PAGES && 0<j<NUM_PAGES && i != j && self.page_array@[i].state == PageState::Free2m && self.page_array@[j].state == PageState::Free2m
                ==>
                self.page_array@[i].rev_pointer != self.page_array@[j].rev_pointer
        }

        pub open spec fn free_pages_1g_wf(&self) -> bool{
            &&&
            self.free_pages_1g.wf()            
            &&&
            self.free_pages_1g.unique()
            &&&
            forall|i:int|
                #![trigger self.free_pages_1g@.contains(self.page_array@[i].addr)]
                #![trigger self.free_pages_1g.node_ref_valid(self.page_array@[i].rev_pointer)]
                #![trigger self.free_pages_1g.node_ref_resolve(self.page_array@[i].rev_pointer)]
                #![trigger self.page_array@[i].is_io_page]
                0<=i<NUM_PAGES && self.page_array@[i].state == PageState::Free1g
                ==> 
                self.free_pages_1g@.contains(self.page_array@[i].addr) 
                && 
                self.free_pages_1g.node_ref_valid(self.page_array@[i].rev_pointer) 
                && 
                self.free_pages_1g.node_ref_resolve(self.page_array@[i].rev_pointer) == self.page_array@[i].addr
                &&
                self.page_array@[i].is_io_page == false
            &&&
            forall|page_ptr:PagePtr| 
                #![trigger page_ptr_1g_valid(page_ptr)]
                #![trigger self.page_array@[page_ptr2page_index(page_ptr) as int].state]
                self.free_pages_1g@.contains(page_ptr) 
                ==>
                page_ptr_1g_valid(page_ptr)
                &&
                self.page_array@[page_ptr2page_index(page_ptr) as int].state == PageState::Free1g
            &&&
            forall|i:int, j:int|
                #![trigger self.page_array@[i].rev_pointer, self.page_array@[j].rev_pointer]
                0<=i<NUM_PAGES && 0<j<NUM_PAGES && i != j && self.page_array@[i].state == PageState::Free1g && self.page_array@[j].state == PageState::Free1g
                ==>
                self.page_array@[i].rev_pointer != self.page_array@[j].rev_pointer
        }

        pub open spec fn allocated_pages_4k_wf(&self) -> bool{
            &&&
            self.allocated_pages_4k@.finite()
            &&&
            forall|p:PagePtr|
                #![trigger self.allocated_pages_4k@.contains(p), page_ptr_valid(p)]
                self.allocated_pages_4k@.contains(p) ==> page_ptr_valid(p)
            &&&
            forall|i:int|
                #![trigger self.allocated_pages_4k@.contains(self.page_array@[i].addr)]
                #![trigger self.page_array@[i].is_io_page]
                0<=i<NUM_PAGES && self.page_array@[i].state == PageState::Allocated4k
                ==> 
                self.allocated_pages_4k@.contains(self.page_array@[i].addr)
                &&
                self.page_array@[i].is_io_page == false
            &&&
            forall|p:PagePtr| 
                #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
                self.allocated_pages_4k@.contains(p) 
                ==>
                self.page_array@[page_ptr2page_index(p) as int].state == PageState::Allocated4k
        }
        
        pub open spec fn allocated_pages_2m_wf(&self) -> bool{
            &&&
            self.allocated_pages_2m@.finite()
            &&&
            forall|p:PagePtr|
                #![trigger self.allocated_pages_2m@.contains(p), page_ptr_2m_valid(p)]
                self.allocated_pages_2m@.contains(p) ==> page_ptr_2m_valid(p)
            &&&
            forall|i:int|
                #![trigger self.allocated_pages_2m@.contains(self.page_array@[i].addr)]
                #![trigger self.page_array@[i].is_io_page]
                0<=i<NUM_PAGES && self.page_array@[i].state == PageState::Allocated2m
                ==> 
                self.allocated_pages_2m@.contains(self.page_array@[i].addr) 
                &&
                self.page_array@[i].is_io_page == false
            &&&
            forall|p:PagePtr| 
                #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
                self.allocated_pages_2m@.contains(p) 
                ==>
                self.page_array@[page_ptr2page_index(p) as int].state == PageState::Allocated2m
        }

        pub open spec fn allocated_pages_1g_wf(&self) -> bool{
            &&&
            self.allocated_pages_1g@.finite()
            &&&
            forall|p:PagePtr|
                #![trigger self.allocated_pages_1g@.contains(p), page_ptr_1g_valid(p)]
                self.allocated_pages_1g@.contains(p) ==> page_ptr_1g_valid(p)
            &&&
            forall|i:int|
                #![trigger self.page_array@[i].addr]
                #![trigger self.page_array@[i].is_io_page]
                0<=i<NUM_PAGES && self.page_array@[i].state == PageState::Allocated1g
                ==> 
                self.allocated_pages_1g@.contains(self.page_array@[i].addr)
                &&
                self.page_array@[i].is_io_page == false
            &&&
            forall|p:PagePtr| 
                #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
                self.allocated_pages_1g@.contains(p) 
                ==>
                self.page_array@[page_ptr2page_index(p) as int].state == PageState::Allocated1g
        }

        pub open spec fn mapped_pages_4k_wf(&self) -> bool{
            &&&
            self.mapped_pages_4k@.finite()
            &&&
            forall|p:PagePtr|
                #![trigger self.mapped_pages_4k@.contains(p), page_ptr_valid(p)]
                #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
                #![trigger self.mapped_pages_4k@.contains(p), page_ptr2page_index(p)]
                self.mapped_pages_4k@.contains(p) 
                ==> 
                page_ptr_valid(p)
                &&
                self.page_array@[page_ptr2page_index(p) as int].state == PageState::Mapped4k
                &&
                self.page_array@[page_ptr2page_index(p) as int].ref_count == self.page_array@[page_ptr2page_index(p) as int].mappings@.len() + self.page_array@[page_ptr2page_index(p) as int].io_mappings@.len()
            &&&
            forall|i:int|
                #![trigger self.page_array@[i].addr]
                0<=i<NUM_PAGES && self.page_array@[i].state == PageState::Mapped4k
                ==> 
                self.mapped_pages_4k@.contains(self.page_array@[i].addr) 
        }


        pub open spec fn mapped_pages_2m_wf(&self) -> bool{
            &&&
            self.mapped_pages_2m@.finite()
            &&&
            forall|i:int|
                #![trigger self.page_array@[i].addr]
                0<=i<NUM_PAGES && self.page_array@[i].state == PageState::Mapped2m
                ==> 
                self.mapped_pages_2m@.contains(self.page_array@[i].addr) 
            &&&
            forall|p:PagePtr|
                #![trigger self.mapped_pages_2m@.contains(p), page_ptr_valid(p)]
                #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
                #![trigger self.mapped_pages_2m@.contains(p), page_ptr2page_index(p)]
                self.mapped_pages_2m@.contains(p) 
                ==>
                page_ptr_2m_valid(p)
                &&
                self.page_array@[page_ptr2page_index(p) as int].state == PageState::Mapped2m
                &&
                self.page_array@[page_ptr2page_index(p) as int].ref_count == self.page_array@[page_ptr2page_index(p) as int].mappings@.len() + self.page_array@[page_ptr2page_index(p) as int].io_mappings@.len()
        }
        
        pub open spec fn mapped_pages_1g_wf(&self) -> bool{
            &&&
            self.mapped_pages_1g@.finite()
            &&&
            forall|i:int|
                #![trigger self.page_array@[i].addr]
                0<=i<NUM_PAGES && self.page_array@[i].state == PageState::Mapped1g
                ==> 
                self.mapped_pages_1g@.contains(self.page_array@[i].addr) 
            &&&
            forall|p:PagePtr| 
                #![trigger self.mapped_pages_1g@.contains(p), page_ptr_valid(p)]
                #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
                #![trigger self.mapped_pages_1g@.contains(p), page_ptr2page_index(p)]
                self.mapped_pages_1g@.contains(p) 
                ==>
                page_ptr_1g_valid(p)
                &&
                self.page_array@[page_ptr2page_index(p) as int].state == PageState::Mapped1g
                &&
                self.page_array@[page_ptr2page_index(p) as int].ref_count == self.page_array@[page_ptr2page_index(p) as int].mappings@.len() + self.page_array@[page_ptr2page_index(p) as int].io_mappings@.len()
        }

        pub open spec fn merged_pages_wf(&self) -> bool{
            &&&
            forall|i:int|
                #![trigger page_index_2m_valid(self.page_array@[i].addr)]
                #![trigger spec_page_index_truncate_2m(self.page_array@[i].addr)]
                0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Merged2m
                ==>
                page_index_2m_valid(self.page_array@[i].addr) == false
                &&( 
                    self.page_array@[spec_page_index_truncate_2m(self.page_array@[i].addr) as int].state == PageState::Mapped2m
                    ||   
                    self.page_array@[spec_page_index_truncate_2m(self.page_array@[i].addr) as int].state == PageState::Free2m
                    ||   
                    self.page_array@[spec_page_index_truncate_2m(self.page_array@[i].addr) as int].state == PageState::Allocated2m
                    ||   
                    self.page_array@[spec_page_index_truncate_2m(self.page_array@[i].addr) as int].state == PageState::Unavailable2m
                )        
                &&
                self.page_array@[i].is_io_page == self.page_array@[spec_page_index_truncate_2m(self.page_array@[i].addr) as int].is_io_page    
            &&&
                forall|i:int|
                    #![trigger page_index_1g_valid(self.page_array@[i].addr)]
                    #![trigger spec_page_index_truncate_1g(self.page_array@[i].addr)]
                    0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Merged1g
                    ==>
                    page_index_1g_valid(self.page_array@[i].addr) == false
                    &&( 
                        self.page_array@[spec_page_index_truncate_1g(self.page_array@[i].addr) as int].state == PageState::Mapped1g
                        ||   
                        self.page_array@[spec_page_index_truncate_1g(self.page_array@[i].addr) as int].state == PageState::Free1g
                        ||   
                        self.page_array@[spec_page_index_truncate_1g(self.page_array@[i].addr) as int].state == PageState::Allocated1g
                        ||   
                        self.page_array@[spec_page_index_truncate_1g(self.page_array@[i].addr) as int].state == PageState::Unavailable1g
                    )
                    &&
                    self.page_array@[i].is_io_page == self.page_array@[spec_page_index_truncate_1g(self.page_array@[i].addr) as int].is_io_page
                    
        }

        pub open spec fn hugepages_wf(&self) -> bool {
            // true
            &&&
            forall|i:usize, j:usize|
                #![trigger self.page_array@[i as int].state, self.page_array@[j as int].state]
                #![trigger self.page_array@[i as int].is_io_page, self.page_array@[j as int].is_io_page]
                0 <= i < NUM_PAGES && page_index_1g_valid(i) && (self.page_array@[i as int].state == PageState::Mapped1g || self.page_array@[i as int].state == PageState::Free1g || self.page_array@[i as int].state == PageState::Allocated1g || self.page_array@[i as int].state == PageState::Unavailable1g)
                && i < j < i + 0x40000
                ==>
                self.page_array@[j as int].state == PageState::Merged1g
                &&
                self.page_array@[i as int].is_io_page == self.page_array@[j as int].is_io_page
            &&&
            forall|i:usize, j:usize|
                #![trigger  self.page_array@[i as int].state, self.page_array@[j as int].state]
                #![trigger self.page_array@[i as int].is_io_page, self.page_array@[j as int].is_io_page]
                0 <= i < NUM_PAGES && page_index_2m_valid(i) && (self.page_array@[i as int].state == PageState::Mapped2m || self.page_array@[i as int].state == PageState::Free2m || self.page_array@[i as int].state == PageState::Allocated2m || self.page_array@[i as int].state == PageState::Unavailable2m)
                && i < j < i + 0x200
                ==>
                self.page_array@[j as int].state == PageState::Merged2m
                &&
                self.page_array@[i as int].is_io_page == self.page_array@[j as int].is_io_page
        }

        pub open spec fn perm_wf(&self) -> bool{
            &&&
            self.page_perms_4k@.dom() =~= self.mapped_pages_4k@ + self.free_pages_4k@.to_set()
            &&&
            forall|p:PagePtr| 
                #![trigger self.page_perms_4k@[p].is_init()]
                #![trigger self.page_perms_4k@[p].addr()]
                self.page_perms_4k@.dom().contains(p) 
                ==> 
                self.page_perms_4k@[p].is_init() && self.page_perms_4k@[p].addr() == p
            &&&
            self.page_perms_2m@.dom() =~= self.mapped_pages_2m@ + self.free_pages_2m@.to_set()
            &&&
            forall|p:PagePtr|                 
                #![trigger self.page_perms_2m@[p].is_init()]
                #![trigger self.page_perms_2m@[p].addr()]
                self.page_perms_2m@.dom().contains(p) 
                ==> 
                self.page_perms_2m@[p].is_init() && self.page_perms_2m@[p].addr() == p
            &&&
            self.page_perms_1g@.dom() =~= self.mapped_pages_1g@ + self.free_pages_1g@.to_set()
            &&&
            forall|p:PagePtr| 
                #![trigger self.page_perms_1g@[p].is_init()]
                #![trigger self.page_perms_1g@[p].addr()]
                self.page_perms_1g@.dom().contains(p) 
                ==> 
                self.page_perms_1g@[p].is_init() && self.page_perms_1g@[p].addr() == p
        }

        pub open spec fn wf(&self) -> bool{
            &&&
            self.page_array_wf()
            &&&
            self.free_pages_4k_wf()
            &&&
            self.free_pages_2m_wf()
            &&&
            self.free_pages_1g_wf()
            &&&
            self.allocated_pages_4k_wf()
            &&&
            self.allocated_pages_2m_wf()
            &&&
            self.allocated_pages_1g_wf()
            &&&
            self.mapped_pages_4k_wf()
            &&&
            self.mapped_pages_2m_wf()
            &&&
            self.mapped_pages_1g_wf()
            &&&
            self.merged_pages_wf()
            &&&
            self.hugepages_wf()
            &&&
            self.perm_wf()
        }
    }

    // proof
    impl PageAllocator{
        pub proof fn page_ptr_page_index_lemma(&self)
            requires
                self.wf(),
            ensures
                forall|i:usize|
                    #![trigger self.page_array@[i as int].state]
                    0 <= i < NUM_PAGES && (self.page_array@[i as int].state == PageState::Mapped1g || self.page_array@[i as int].state == PageState::Free1g || self.page_array@[i as int].state == PageState::Allocated1g)
                    ==>
                    page_index_1g_valid(i),
        {
            page_ptr_lemma();            
            assert(
                forall|i:usize|
                    #![trigger self.page_array@[i as int].state]
                    0 <= i < NUM_PAGES && (self.page_array@[i as int].state == PageState::Mapped1g || self.page_array@[i as int].state == PageState::Free1g || self.page_array@[i as int].state == PageState::Allocated1g)
                    ==>
                    page_index_1g_valid(i)
            ) by {
            };
        }
        
        pub proof fn len_lemma(&self, ptr:PagePtr)
            requires
                self.wf(),
            ensures
                self.allocated_pages_2m().contains(ptr) ==> self.free_pages_2m().len() < NUM_PAGES,
                self.allocated_pages_4k().contains(ptr) ==> self.free_pages_4k().len() < NUM_PAGES,
        {
            page_ptr_lemma();
            seq_skip_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
            let all_page_ptrs = Set::new(|page_ptr: PagePtr| page_ptr_valid(page_ptr));
            assume(all_page_ptrs.finite());
            assume(all_page_ptrs.len() == NUM_PAGES); // this should be inferred smh by verus...
            assert(
                forall|page_ptr:PagePtr| #![auto]
                    self.free_pages_2m@.contains(page_ptr) 
                    ==>
                    all_page_ptrs.contains(page_ptr)
            );
            
            if self.allocated_pages_2m().contains(ptr){
                assert(page_ptr_valid(ptr));
                assert(self.page_array@[page_ptr2page_index(ptr) as int].state == PageState::Allocated2m);
                assert(all_page_ptrs.contains(ptr));
                assert(all_page_ptrs.remove(ptr).len() < all_page_ptrs.len());
                assert(self.free_pages_2m().contains(ptr) == false);
                assert(self.free_pages_2m().subset_of(all_page_ptrs.remove(ptr)));
                assert(self.free_pages_2m().len() < NUM_PAGES) by {lemma_len_subset::<PagePtr>(self.free_pages_2m(), all_page_ptrs.remove(ptr))};
            }

            if self.allocated_pages_4k().contains(ptr){
                assert(page_ptr_valid(ptr));
                assert(self.page_array@[page_ptr2page_index(ptr) as int].state == PageState::Allocated4k);
                assert(all_page_ptrs.contains(ptr));
                assert(all_page_ptrs.remove(ptr).len() < all_page_ptrs.len());
                assert(self.free_pages_4k().contains(ptr) == false);
                assert(self.free_pages_4k().subset_of(all_page_ptrs.remove(ptr)));
                assert(self.free_pages_4k().len() < NUM_PAGES) by {lemma_len_subset::<PagePtr>(self.free_pages_4k(), all_page_ptrs.remove(ptr))};
            }
        }
    }

    impl PageAllocator{
        pub fn alloc_page_2m(&mut self) 
            -> (ret:(PagePtr, Tracked<PagePerm2m>))
            requires 
                old(self).wf(),
                old(self).free_pages_2m.len() > 0,
            ensures
                self.wf(),
                self.free_pages_4k() =~= old(self).free_pages_4k(),
                // self.free_pages_2m() =~= old(self).free_pages_2m(),
                self.free_pages_2m() =~= old(self).free_pages_2m().remove(ret.0),
                self.free_pages_1g() =~= old(self).free_pages_1g(),
                self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
                self.allocated_pages_2m() =~= old(self).allocated_pages_2m().insert(ret.0),
                self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
                self.mapped_pages_4k() =~= old(self).mapped_pages_4k(),
                self.mapped_pages_2m() =~= old(self).mapped_pages_2m(),
                self.mapped_pages_1g() =~= old(self).mapped_pages_1g(),
                forall|p:PagePtr| 
                    self.page_is_mapped(p) ==> 
                    self.page_mappings(p) =~= old(self).page_mappings(p)
                    &&
                    self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
                ret.0 == ret.1@.addr(),
                ret.1@.is_init(),
        {
            proof{
                page_ptr_lemma();
                seq_skip_lemma::<PagePtr>();
                self.free_pages_1g.wf_to_no_duplicates();
                self.free_pages_2m.wf_to_no_duplicates();
                self.free_pages_4k.wf_to_no_duplicates();
            }
            let ret = self.free_pages_2m.pop().0;
            assert(page_ptr_valid(ret));
            self.set_state(page_ptr2page_index(ret), PageState::Allocated2m);
            proof{
                self.allocated_pages_2m@ = self.allocated_pages_2m@.insert(ret);
            }
            let tracked mut ret_perm = self.page_perms_2m.borrow_mut().tracked_remove(ret);
            // assert(self.page_array_wf());
            // assert(self.free_pages_4k_wf());
            // assert(self.free_pages_2m_wf());
            // assert(self.free_pages_1g_wf());
            // assert(self.allocated_pages_4k_wf());
            // assert(self.allocated_pages_2m_wf());
            // assert(self.allocated_pages_1g_wf());
            // assert(self.mapped_pages_4k_wf()) ;
            // assert(self.mapped_pages_2m_wf());
            // assert(self.mapped_pages_1g_wf());
            assert(self.merged_pages_wf()) by {
                page_ptr_page_index_truncate_lemma();
            };
            // assert(self.hugepages_wf());
            // assert(self.perm_wf());
            return (ret, Tracked(ret_perm));
        }

        pub fn free_page_2m(&mut self, target_ptr:PagePtr, Tracked(target_perm): Tracked<PagePerm2m>) 
            requires 
                old(self).wf(),
                old(self).allocated_pages_2m().contains(target_ptr),
                target_ptr == target_perm.addr(),
                target_perm.is_init(),
            ensures
                self.wf(),
                self.free_pages_4k() =~= old(self).free_pages_4k(),
                self.free_pages_2m() =~= old(self).free_pages_2m().insert(target_ptr),
                self.free_pages_1g() =~= old(self).free_pages_1g(),
                self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
                self.allocated_pages_2m() =~= old(self).allocated_pages_2m().remove(target_ptr),
                self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
                self.mapped_pages_4k() =~= old(self).mapped_pages_4k(),
                self.mapped_pages_2m() =~= old(self).mapped_pages_2m(),
                self.mapped_pages_1g() =~= old(self).mapped_pages_1g(),
                forall|p:PagePtr| 
                    self.page_is_mapped(p) ==> 
                    self.page_mappings(p) =~= old(self).page_mappings(p)
                    &&
                    self.page_io_mappings(p) =~= old(self).page_io_mappings(p)
        {
            proof{
                page_ptr_lemma();
                seq_push_lemma::<PagePtr>();
                self.free_pages_1g.wf_to_no_duplicates();
                self.free_pages_2m.wf_to_no_duplicates();
                self.free_pages_2m@.unique_seq_to_set();
                self.free_pages_4k.wf_to_no_duplicates();
                self.len_lemma(target_ptr);
            }
            assert(page_ptr_valid(target_ptr));
            let rev_index = self.free_pages_2m.push(&target_ptr);
            self.set_rev_pointer(page_ptr2page_index(target_ptr), rev_index);
            self.set_state(page_ptr2page_index(target_ptr), PageState::Free2m);
            proof{
                self.allocated_pages_2m@ = self.allocated_pages_2m@.remove(target_ptr);
                self.page_perms_2m.borrow_mut().tracked_insert(target_ptr, target_perm);
            }

                // assert(self.page_array_wf());
                // assert(self.free_pages_4k_wf());
                // assert(self.free_pages_2m_wf());
                // assert(self.free_pages_1g_wf());
                // assert(self.allocated_pages_4k_wf());
                // assert(self.allocated_pages_2m_wf());
                // assert(self.allocated_pages_1g_wf());
                // assert(self.mapped_pages_4k_wf()) ;
                // assert(self.mapped_pages_2m_wf());
                // assert(self.mapped_pages_1g_wf());
                assert(self.merged_pages_wf()) by {
                    page_ptr_page_index_truncate_lemma();
                };
        }

        pub fn alloc_page_4k(&mut self) 
            -> (ret:(PagePtr, Tracked<PagePerm4k>))
            requires 
                old(self).wf(),
                old(self).free_pages_4k.len() > 0,
            ensures
                self.wf(),
                // self.free_pages_4k() =~= old(self).free_pages_4k(),
                self.free_pages_2m() =~= old(self).free_pages_2m(),
                self.free_pages_4k() =~= old(self).free_pages_4k().remove(ret.0),
                self.free_pages_1g() =~= old(self).free_pages_1g(),
                self.allocated_pages_4k() =~= old(self).allocated_pages_4k().insert(ret.0),
                self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
                self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
                self.mapped_pages_4k() =~= old(self).mapped_pages_4k(),
                self.mapped_pages_2m() =~= old(self).mapped_pages_2m(),
                self.mapped_pages_1g() =~= old(self).mapped_pages_1g(),
                forall|p:PagePtr| 
                    self.page_is_mapped(p) ==> 
                    self.page_mappings(p) =~= old(self).page_mappings(p)
                    &&
                    self.page_io_mappings(p) =~= old(self).page_io_mappings(p)
        {
            proof{
                page_ptr_lemma();
                seq_skip_lemma::<PagePtr>();
                self.free_pages_1g.wf_to_no_duplicates();
                self.free_pages_2m.wf_to_no_duplicates();
                self.free_pages_4k.wf_to_no_duplicates();
            }
            let ret = self.free_pages_4k.pop().0;
            assert(page_ptr_valid(ret));
            self.set_state(page_ptr2page_index(ret), PageState::Allocated4k);
            assert(self.page_array@[page_ptr2page_index(ret) as int].is_io_page == false);
            proof{
                self.allocated_pages_4k@ = self.allocated_pages_4k@.insert(ret);
            }
            let tracked mut ret_perm = self.page_perms_4k.borrow_mut().tracked_remove(ret);
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
            assert(self.merged_pages_wf()) by {
                page_ptr_page_index_truncate_lemma();
            };
            assert(self.hugepages_wf());
            assert(self.perm_wf());
            return (ret, Tracked(ret_perm));
        }
        pub fn free_page_4k(&mut self, target_ptr:PagePtr, Tracked(target_perm): Tracked<PagePerm4k>) 
            requires 
                old(self).wf(),
                old(self).allocated_pages_4k().contains(target_ptr),
                target_ptr == target_perm.addr(),
                target_perm.is_init(),
            ensures
                self.wf(),
                self.free_pages_4k() =~= old(self).free_pages_4k().insert(target_ptr),
                self.free_pages_2m() =~= old(self).free_pages_2m(),
                self.free_pages_1g() =~= old(self).free_pages_1g(),
                self.allocated_pages_4k() =~= old(self).allocated_pages_4k().remove(target_ptr),
                self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
                self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
                self.mapped_pages_4k() =~= old(self).mapped_pages_4k(),
                self.mapped_pages_2m() =~= old(self).mapped_pages_2m(),
                self.mapped_pages_1g() =~= old(self).mapped_pages_1g(),
                forall|p:PagePtr| 
                    self.page_is_mapped(p) ==> 
                    self.page_mappings(p) =~= old(self).page_mappings(p)
                    &&
                    self.page_io_mappings(p) =~= old(self).page_io_mappings(p)
        {
            proof{
                page_ptr_lemma();
                seq_push_lemma::<PagePtr>();
                self.free_pages_1g.wf_to_no_duplicates();
                self.free_pages_2m.wf_to_no_duplicates();
                self.free_pages_4k.wf_to_no_duplicates();
                self.free_pages_4k@.unique_seq_to_set();
                self.len_lemma(target_ptr);
            }
            assert(page_ptr_valid(target_ptr));
            let rev_index = self.free_pages_4k.push(&target_ptr);
            self.set_rev_pointer(page_ptr2page_index(target_ptr), rev_index);
            self.set_state(page_ptr2page_index(target_ptr), PageState::Free4k);
            proof{
                self.allocated_pages_4k@ = self.allocated_pages_4k@.remove(target_ptr);
                self.page_perms_4k.borrow_mut().tracked_insert(target_ptr, target_perm);
            }

                // assert(self.page_array_wf());
                // assert(self.free_pages_4k_wf());
                // assert(self.free_pages_2m_wf());
                // assert(self.free_pages_1g_wf());
                // assert(self.allocated_pages_4k_wf());
                // assert(self.allocated_pages_2m_wf());
                // assert(self.allocated_pages_1g_wf());
                // assert(self.mapped_pages_4k_wf()) ;
                // assert(self.mapped_pages_2m_wf());
                // assert(self.mapped_pages_1g_wf());
                assert(self.merged_pages_wf()) by {
                    page_ptr_page_index_truncate_lemma();
                };
        }
    }
}