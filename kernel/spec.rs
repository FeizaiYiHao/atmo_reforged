use vstd::prelude::*;
verus! {
use crate::allocator::page_allocator_spec_impl::*;
use crate::memory_manager::spec_impl::*;
use crate::process_manager::spec_impl::*;
use crate::util::page_ptr_util_u::*;
use vstd::simple_pptr::PointsTo;
use crate::pagetable::pagemap::PageMap;
use crate::array_vec::ArrayVec;
use crate::define::*;

pub struct Kernel{
    pub page_alloc: PageAllocator,
    pub mem_man: MemoryManager,
    pub proc_man: ProcessManager,

    pub page_mapping: Ghost<Map<PagePtr, Set<(ProcPtr,VAddr)>>>,
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

    pub open spec fn page_mapping_wf(&self) -> bool{
        &&&
        self.page_mapping@.dom() == self.page_alloc.mapped_pages_4k()
        &&&
        forall|page_ptr:PagePtr, p_ptr: ProcPtr, va:VAddr|
            #![trigger self.page_mapping@[page_ptr].contains((p_ptr, va))]
            #![trigger self.page_alloc.page_mappings(page_ptr).contains((self.proc_man.get_proc(p_ptr).pcid, va))]
            self.page_mapping@.dom().contains(page_ptr) && self.page_mapping@[page_ptr].contains((p_ptr, va))
            ==>
            self.page_alloc.page_is_mapped(page_ptr)
            &&
            self.proc_man.proc_dom().contains(p_ptr)
            &&
            self.page_alloc.page_mappings(page_ptr).contains((self.proc_man.get_proc(p_ptr).pcid, va))
        &&&
        forall|page_ptr:PagePtr, pcid: Pcid, va:VAddr|
            #![trigger self.page_alloc.page_mappings(page_ptr).contains((pcid, va))]
            #![trigger self.page_mapping@[page_ptr].contains((self.mem_man.pcid_to_proc_ptr(pcid), va))]
            self.page_alloc.page_is_mapped(page_ptr) && self.page_alloc.page_mappings(page_ptr).contains((pcid, va))
            ==>
            self.page_mapping@.dom().contains(page_ptr) && self.page_mapping@[page_ptr].contains((self.mem_man.pcid_to_proc_ptr(pcid), va))
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
            &&
            self.mem_man.pcid_to_proc_ptr(self.proc_man.get_proc(proc_ptr).pcid) == proc_ptr
        &&&
        forall|pcid:Pcid|
            #![trigger self.mem_man.pcid_to_proc_ptr(pcid)]
            self.mem_man.pcid_active(pcid)
            ==>
            self.proc_man.proc_dom().contains(self.mem_man.pcid_to_proc_ptr(pcid)) 
            &&
            self.proc_man.get_proc(self.mem_man.pcid_to_proc_ptr(pcid)).pcid == pcid
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
        &&&
        self.page_mapping_wf()
    }

    pub open spec fn total_quota_wf(&self) -> bool{
        &&&
        self.get_num_of_free_pages() ==
            self.container_dom().fold(0, |e:int, a:ContainerPtr| e + self.get_container(a).mem_quota)
    }

    pub open spec fn total_wf(&self) -> bool{
        &&&
        self.wf()
        &&&
        self.total_quota_wf()
    }
}

impl Kernel {
    pub proof fn process_inv(&self)
        requires
            self.wf()
        ensures
            forall|p_ptr:ProcPtr|
                #![trigger self.proc_dom().contains(p_ptr)]
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr)
                ==>
                self.container_dom().contains(self.get_proc(p_ptr).owning_container)
    {
        self.proc_man.process_inv();
    }
    
    // @TODO: prove this
    #[verifier(external_body)]
    pub proof fn fold_change_lemma(&self, old:Kernel, mod_c_ptr:ContainerPtr)
        requires
            self.container_dom() == old.container_dom(),
            self.container_dom().contains(mod_c_ptr),
            forall|c_ptr:ContainerPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && c_ptr != mod_c_ptr
                ==>
                self.get_container(c_ptr).mem_quota == old.get_container(c_ptr).mem_quota
        ensures
            self.container_dom().fold(0, |e:int, a:ContainerPtr| e + self.get_container(a).mem_quota)
            ==
            old.container_dom().fold(0, |e:int, a:ContainerPtr| e + old.get_container(a).mem_quota) - old.get_container(mod_c_ptr).mem_quota + self.get_container(mod_c_ptr).mem_quota
    {}

    // @TODO: prove this
    #[verifier(external_body)]
    pub proof fn fold_lemma(&self)
        ensures
            forall|c_ptr:ContainerPtr|
            #![auto]
            self.container_dom().contains(c_ptr)
            ==>
            self.container_dom().fold(0, |e:int, a:ContainerPtr| e + self.get_container(a).mem_quota) >= self.get_container(c_ptr).mem_quota 
    {}
}


impl Kernel{
    pub fn new() -> (ret:Self)
    {
        Kernel{
            page_alloc: PageAllocator::new(),
            mem_man: MemoryManager::new(),
            proc_man: ProcessManager::new(),
        
            page_mapping: Ghost(Map::<PagePtr, Set<(ProcPtr,VAddr)>>::empty()),
        }
    }

    #[verifier(external_body)]
    pub fn kernel_init(&mut self, dom_0_container_ptr:ContainerPtr, dom_0_proc_ptr:ProcPtr, dom_0_thread_ptr:ThreadPtr, init_quota:usize, 
        boot_pages:&mut ArrayVec::<(PageState, usize), NUM_PAGES>, container_ptr:ContainerPtr,
        dom0_page_map_ptr:PageMapPtr, kernel_entry:PageMapPtr,
        page_perm_0: Tracked<PagePerm4k>, page_perm_1: Tracked<PagePerm4k>, page_perm_2: Tracked<PagePerm4k>, dom0_page_map_perm: Tracked<PointsTo<PageMap>>
    )
    {
        self.page_alloc.init(boot_pages, dom_0_container_ptr);
        self.mem_man.init(dom0_page_map_ptr, kernel_entry, dom_0_proc_ptr, &mut self.page_alloc, dom0_page_map_perm);
        self.proc_man.init(dom_0_container_ptr, dom_0_proc_ptr, dom_0_thread_ptr, init_quota, page_perm_0, page_perm_1, page_perm_2);
    }
}

}