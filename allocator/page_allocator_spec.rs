use vstd::prelude::*;
verus! {
    use crate::define::*;
    use crate::allocator::page::*;
    use crate::array::*;
    use crate::slinkedlist::spec::*;

    pub struct PageAllocator{
        pub page_array: Array<Page,NUM_PAGES>,
        pub free_pages_4k: StaticLinkedList<NUM_PAGES>,
        pub free_pages_2m: StaticLinkedList<NUM_PAGES>,
        pub free_pages_1g: StaticLinkedList<NUM_PAGES>,
    
        pub page_table_pages: Ghost<Set<PagePtr>>,
        pub allocated_pages: Ghost<Set<PagePtr>>,
        pub mapped_pages_4k: Ghost<Set<PagePtr>>,
        pub mapped_pages_2m: Ghost<Set<PagePtr>>,
        pub mapped_pages_1g: Ghost<Set<PagePtr>>,
    
        pub available_pages: Ghost<Set<PagePtr>>,
    
        pub page_perms: Tracked<Map<PagePtr,PagePerm>>,
    
    
        // //fields for virtual addresses
        // pub free_pcids: ArrayVec<Pcid,PCID_MAX>,
        // pub page_tables: MarsArray<PageTable,PCID_MAX>,
    }
}