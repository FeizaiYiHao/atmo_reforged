use vstd::prelude::*;
verus! {
    use crate::define::*;

    #[derive(Clone, Copy)]
    pub struct Page{
        pub addr: PagePtr,
        pub state: PageState,
        pub is_io_page: bool,
        pub rev_pointer: SLLIndex,
        pub ref_count: usize,
        pub owning_container: Option<ContainerPtr>,

        pub mappings: Ghost<Set<(Pcid,VAddr)>>,
        pub io_mappings: Ghost<Set<(IOid,VAddr)>>,
    }

}