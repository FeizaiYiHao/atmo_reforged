use vstd::prelude::*;
verus! {
    use crate::define::*;
    use crate::allocator::page::*;
    use crate::array::*;
    use crate::slinkedlist::spec::*;
    use crate::util::page_ptr_util_u::*;
    use crate::allocator::page_allocator_spec::*;

    impl PageAllocator{
        
        // pub proof fn page_addr_no_duplicates(&self)
        //     requires 
        //         self.page_array.wf(),
        //     ensures
        //         forall|i:int, j:int|
        //             #![trigger self.page_array@[i].addr, self.page_array@[j].addr]
        //             0<i<NUM_PAGES && 0<j<NUM_PAGES && i != j 
        //             ==>
        //             self.page_array@[i].addr != self.page_array@[j].addr
        // {
        //     assert(forall|i:int, j:int|
        //         #![trigger self.page_array@[i].addr, self.page_array@[j].addr]
        //         0<i<NUM_PAGES && 0<j<NUM_PAGES && i != j 
        //         ==>
        //         self.page_array@[i].addr != self.page_array@[j].addr) by {
        //             assert(forall|i:int, j:int|
        //                 0<i<NUM_PAGES && 0<j<NUM_PAGES && i != j 
        //                 ==> 
        //                 #[trigger] i * 4096 != #[trigger] j * 4096) by (bit_vector);
        //         };
        // }
    }
}