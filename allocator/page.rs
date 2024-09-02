use vstd::prelude::*;
verus! {
    use crate::define::*;

    pub struct Page{
        pub start: PagePtr,
        pub state: PageState,
        pub is_io_page: bool,
        pub rf_count: usize,
        pub rev_pointer: SLLIndex,
    
        pub mappings: Ghost<Map<(Pcid,VAddr),PageType>>,
        pub io_mappings: Ghost<Map<(IOid,VAddr),PageType>>,
    }
}