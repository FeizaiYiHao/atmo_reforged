use vstd::prelude::*;
verus! {
use crate::allocator::page_allocator_spec_impl::*;
use crate::memory_manager::spec_impl::*;
use crate::process_manager::spec_impl::*;
use crate::util::page_ptr_util_u::*;
use crate::define::*;
pub struct Kernel{
    pub page_alloc: PageAllocator,
    pub mem_man: MemoryManager,
    pub proc_man: ProcessManager,
}

//spec
impl Kernel{
    //Leakage freedom and memory safety
    pub open spec fn memory_wf(&self) -> bool{
        //Additional safety specs are embedded in page_alloc's specs
        &&&
        self.mem_man.page_closure().disjoint(self.proc_man.page_closure())
        //Leakage freedom. Internel leakage freedom are embedded recursively in mem_man and proc_man
        &&&
        self.mem_man.page_closure() + self.proc_man.page_closure() == self.page_alloc.allocated_pages_4k()
        //We are not using hugepages for now. 
        &&&
        self.page_alloc.mapped_pages_2m() =~= Set::empty()
        &&&
        self.page_alloc.mapped_pages_1g() =~= Set::empty()
        &&&
        self.page_alloc.allocated_pages_2m() =~= Set::empty()
        &&&
        self.page_alloc.allocated_pages_1g() =~= Set::empty()
    }

    pub open spec fn mapping_wf(&self) -> bool{
        &&&
        forall|pcid:Pcid, va:VAddr|
            #![auto]
            0 <= pcid < PCID_MAX && va_4k_valid(va) && self.mem_man.get_free_pcids_as_set().contains(pcid) == false
            &&
            self.mem_man.get_pagetable_mapping_by_pcid(pcid).dom().contains(va)
            ==>
            self.page_alloc.page_mappings(self.mem_man.get_pagetable_mapping_by_pcid(pcid)[va].addr).contains((pcid,va))
        &&&
        forall|page_ptr:PagePtr, pcid:Pcid, va:VAddr|
            #![auto]
            page_ptr_valid(page_ptr) && self.page_alloc.page_mappings(page_ptr).contains((pcid,va))
            ==>
            0 <= pcid < PCID_MAX && va_4k_valid(va) && self.mem_man.get_free_pcids_as_set().contains(pcid) == false
            &&
            self.mem_man.get_pagetable_mapping_by_pcid(pcid).dom().contains(va)
        &&&
        forall|ioid:IOid, va:VAddr|
            #![auto]
            0 <= ioid < IOID_MAX && va_4k_valid(va) && self.mem_man.get_free_ioids_as_set().contains(ioid) == false
            &&
            self.mem_man.get_iommu_table_mapping_by_ioid(ioid).dom().contains(va)
            ==>
            self.page_alloc.page_io_mappings(self.mem_man.get_iommu_table_mapping_by_ioid(ioid)[va].addr).contains((ioid,va))
        &&&
        forall|page_ptr:PagePtr, ioid:IOid, va:VAddr|
            #![auto]
            page_ptr_valid(page_ptr) && self.page_alloc.page_io_mappings(page_ptr).contains((ioid,va))
            ==>
            0 <= ioid < IOID_MAX && va_4k_valid(va) && self.mem_man.get_free_ioids_as_set().contains(ioid) == false
            &&
            self.mem_man.get_iommu_table_mapping_by_ioid(ioid).dom().contains(va)
    }

    pub open spec fn pcid_ioid_wf(&self) -> bool{
        &&&
        forall|proc_ptr:ProcPtr|
        #![trigger self.proc_man.get_proc(proc_ptr).pcid]
        #![trigger self.proc_man.get_proc(proc_ptr).ioid]
        self.proc_man.process_perms@.dom().contains(proc_ptr) 
        ==>
        self.mem_man.get_free_pcids_as_set().contains(self.proc_man.get_proc(proc_ptr).pcid) == false
        &&
            self.proc_man.get_proc(proc_ptr).ioid.is_Some() 
            ==> 
            self.mem_man.get_free_ioids_as_set().contains(self.proc_man.get_proc(proc_ptr).ioid.unwrap()) == false
    }
}

}