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
        &&&
        self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom()
    }

    pub open spec fn mapping_wf(&self) -> bool{
        &&&
        forall|pcid:Pcid, va:VAddr|
            #![auto]
            #![trigger self.mem_man.get_pagetable_mapping_by_pcid(pcid).dom().contains(va)]
            #![trigger self.page_alloc.page_is_mapped(self.mem_man.get_pagetable_mapping_by_pcid(pcid)[va].addr)]
            #![trigger self.page_alloc.page_mappings(self.mem_man.get_pagetable_mapping_by_pcid(pcid)[va].addr).contains((pcid,va))]
            self.mem_man.pcid_active(pcid)
            &&
            self.mem_man.get_pagetable_mapping_by_pcid(pcid).dom().contains(va)
            ==>
            self.page_alloc.page_is_mapped(self.mem_man.get_pagetable_mapping_by_pcid(pcid)[va].addr)
            &&
            self.page_alloc.page_mappings(self.mem_man.get_pagetable_mapping_by_pcid(pcid)[va].addr).contains((pcid,va))
        &&&
        forall|page_ptr:PagePtr, pcid:Pcid, va:VAddr|
            #![trigger self.page_alloc.page_mappings(page_ptr).contains((pcid,va))]
            self.page_alloc.page_is_mapped(page_ptr) && self.page_alloc.page_mappings(page_ptr).contains((pcid,va))
            ==>
            va_4k_valid(va) && self.mem_man.pcid_active(pcid)
            &&
            self.mem_man.get_pagetable_mapping_by_pcid(pcid).dom().contains(va)
            &&
            self.mem_man.get_pagetable_mapping_by_pcid(pcid)[va].addr == page_ptr
        &&&
        forall|ioid:IOid, va:VAddr|
            #![trigger self.mem_man.get_iommu_table_mapping_by_ioid(ioid).dom().contains(va)]
            #![trigger self.page_alloc.page_is_mapped(self.mem_man.get_iommu_table_mapping_by_ioid(ioid)[va].addr)]
            #![trigger self.page_alloc.page_io_mappings(self.mem_man.get_iommu_table_mapping_by_ioid(ioid)[va].addr).contains((ioid,va))]
            self.mem_man.ioid_active(ioid)
            &&
            self.mem_man.get_iommu_table_mapping_by_ioid(ioid).dom().contains(va)
            ==>            
            self.page_alloc.page_is_mapped(self.mem_man.get_iommu_table_mapping_by_ioid(ioid)[va].addr)
            &&
            self.page_alloc.page_io_mappings(self.mem_man.get_iommu_table_mapping_by_ioid(ioid)[va].addr).contains((ioid,va))
        &&&
        forall|page_ptr:PagePtr, ioid:IOid, va:VAddr|
            #![trigger self.page_alloc.page_io_mappings(page_ptr).contains((ioid,va))]
            self.page_alloc.page_is_mapped(page_ptr) && self.page_alloc.page_io_mappings(page_ptr).contains((ioid,va))
            ==>
            va_4k_valid(va) && self.mem_man.ioid_active(ioid)
            &&
            self.mem_man.get_iommu_table_mapping_by_ioid(ioid).dom().contains(va)
    }

    pub open spec fn pcid_ioid_wf(&self) -> bool{
        &&&
        forall|proc_ptr:ProcPtr|
        #![trigger self.proc_man.get_proc(proc_ptr).pcid]
        self.proc_man.proc_dom().contains(proc_ptr) 
        ==>
        self.mem_man.pcid_active(self.proc_man.get_proc(proc_ptr).pcid)
        &&&
        forall|proc_ptr:ProcPtr|
        #![trigger self.proc_man.get_proc(proc_ptr).ioid]
        self.proc_man.proc_dom().contains(proc_ptr) 
        &&
        self.proc_man.get_proc(proc_ptr).ioid.is_Some() 
        ==> 
        self.mem_man.ioid_active(self.proc_man.get_proc(proc_ptr).ioid.unwrap())
    }

    pub open spec fn wf(&self) -> bool{
        &&&
        self.mem_man.wf()
        &&&
        self.page_alloc.wf()
        &&&
        self.proc_man.wf()
        &&&
        self.memory_wf()
        &&&
        self.mapping_wf()
        &&&
        self.pcid_ioid_wf()
    }

}

}