use vstd::prelude::*;
verus! {
// use vstd::ptr::PointsTo;

use crate::pagetable::*;
use crate::array_vec::ArrayVec;
use crate::define::*;
use crate::array::Array;
use crate::mmu::*;
use crate::mmu::mmu_spec::pagetable_spec_impl::PageTable;
use crate::pagetable::entry::*;

pub struct MMUManager{
    pub kernel_entries: Array<usize,KERNEL_MEM_END_L4INDEX>,
    pub kernel_entries_ghost: Ghost<Seq<PageEntry>>,

    pub free_pcids: ArrayVec<Pcid,PCID_MAX>,
    pub page_tables: Array<Option<PageTable>,PCID_MAX>,
    pub page_table_pages: Ghost<Set<PagePtr>>,


    pub free_ioids: ArrayVec<IOid,IOID_MAX>, //actual owners are procs
    pub iommu_tables:  Array<Option<PageTable>,IOID_MAX>,
    pub iommu_table_pages: Ghost<Set<PagePtr>>,

    pub root_table:RootTable,
    pub root_table_cache: Ghost<Seq<Seq<Seq<Option<(IOid,usize)>>>>>,
    // pub device_table:MarsArray<MarsArray<Option<(u8,u8,u8)>,256>,IOID_MAX>,
    // pub ioid_device_table: Ghost<Seq<Set<(u8,u8,u8)>>>,

    pub pci_bitmap: PCIBitMap,
}

impl MMUManager{

    pub open spec fn pagetables_wf(&self) -> bool{
        &&&
        self.free_pcids.wf()
        &&&
        self.free_pcids@.no_duplicates()
        &&&
        forall|i:int| #![trigger self.free_pcids@[i]] 0<=i<self.free_pcids.len()  ==> self.free_pcids@[i]<PCID_MAX
        &&&
        self.page_tables.wf()
        &&&
        forall|pcid:Pcid| 
            #![trigger self.page_tables[pcid as int]] 
            #![trigger self.free_pcids@.contains(pcid)] 
            0 <= pcid < PCID_MAX ==>
            self.page_tables[pcid as int].is_None() <==> !self.free_pcids@.contains(pcid)
        &&&
        forall|pcid:Pcid| 
            #![trigger self.page_tables[pcid as int].unwrap()]
            0 <= pcid < PCID_MAX && self.page_tables[pcid as int].is_Some() 
            ==> 
            self.page_tables[pcid as int].unwrap().wf()
            &&
            self.page_tables[pcid as int].unwrap().page_closure().subset_of(self.page_table_pages@)            
            &&
            self.page_tables[pcid as int].unwrap().kernel_entries@ =~= self.kernel_entries_ghost@     
            &&
            self.page_tables[pcid as int].unwrap().kernel_l4_end == KERNEL_MEM_END_L4INDEX
        &&&
        forall|pcid_i:Pcid, pcid_j:Pcid| 
            #![trigger self.page_tables[pcid_i as int].unwrap().page_closure(), self.page_tables[pcid_j as int].unwrap().page_closure()]
            0 <= pcid_i < PCID_MAX && self.page_tables[pcid_i as int].is_Some() 
            &&
            0 <= pcid_j < PCID_MAX && self.page_tables[pcid_j as int].is_Some() 
            &&
            pcid_i != pcid_j
            ==>
            self.page_tables[pcid_i as int].unwrap().page_closure().disjoint(self.page_tables[pcid_j as int].unwrap().page_closure())
    }

    pub open spec fn iommutables_wf(&self) -> bool{
        &&&
        self.free_ioids.wf()
        &&&
        self.free_ioids@.no_duplicates()
        &&&
        forall|i:int| #![trigger self.free_ioids@[i]] 0<=i<self.free_ioids.len()  ==> self.free_ioids@[i]<IOID_MAX
        &&&
        self.iommu_tables.wf()
        &&&
        forall|ioid:IOid| 
            #![trigger self.iommu_tables[ioid as int]] 
            #![trigger self.free_ioids@.contains(ioid)] 
            0 <= ioid < IOID_MAX ==>
            self.iommu_tables[ioid as int].is_None() <==> !self.free_ioids@.contains(ioid)
        &&&
        forall|ioid:IOid| 
            #![trigger self.iommu_tables[ioid as int].unwrap()]
            0 <= ioid < IOID_MAX && self.iommu_tables[ioid as int].is_Some() 
            ==> 
            self.iommu_tables[ioid as int].unwrap().wf()
            &&
            self.iommu_tables[ioid as int].unwrap().page_closure().subset_of(self.iommu_table_pages@)        
            &&
            self.iommu_tables[ioid as int].unwrap().kernel_l4_end == 0
        &&&
        forall|ioid_i:IOid, ioid_j:IOid| 
            #![trigger self.iommu_tables[ioid_i as int].unwrap().page_closure(), self.iommu_tables[ioid_j as int].unwrap().page_closure()]
            0 <= ioid_i < IOID_MAX && self.iommu_tables[ioid_i as int].is_Some() 
            &&
            0 <= ioid_j < IOID_MAX && self.iommu_tables[ioid_j as int].is_Some() 
            &&
            ioid_i != ioid_j
            ==>
            self.iommu_tables[ioid_i as int].unwrap().page_closure().disjoint(self.iommu_tables[ioid_j as int].unwrap().page_closure())
    }

    pub open spec fn pagetable_iommutable_disjoint(&self) -> bool
    {
        self.page_table_pages@.disjoint(self.iommu_table_pages@)
    }

    pub open spec fn kernel_entries_wf(&self) -> bool
    {
        &&&
        self.kernel_entries.wf()
        &&&
        self.kernel_entries_ghost@.len() == KERNEL_MEM_END_L4INDEX
        &&&
        forall|i:int| 
        #![trigger self.kernel_entries@[i]]
        #![trigger self.kernel_entries_ghost@[i]]
        0 <= i < KERNEL_MEM_END_L4INDEX
        ==>
        self.kernel_entries_ghost@[i] =~= usize2page_entry(self.kernel_entries@[i])
    }

    pub open spec fn root_table_wf(&self) -> bool{
        &&&
        self.root_table.wf()
        &&&
        self.pci_bitmap.wf()
        &&&
        forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 && self.root_table.resolve(bus,dev,fun).is_Some() 
            ==>
            0<=self.root_table.resolve(bus,dev,fun).get_Some_0().0<IOID_MAX
            &&
            self.get_free_ioids_as_set().contains(self.root_table.resolve(bus,dev,fun).get_Some_0().0) == false
            &&
            self.root_table.resolve(bus,dev,fun).get_Some_0().1 == self.get_iommutable_by_ioid(self.root_table.resolve(bus,dev,fun).get_Some_0().0).unwrap().cr3
        &&&
        forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 && self.root_table.resolve(bus,dev,fun).is_Some() 
            ==>
            self.pci_bitmap@[(self.root_table.resolve(bus,dev,fun).get_Some_0().0,bus,dev,fun)]== true
        &&&
        forall|ioid:IOid,bus:u8,dev:u8,fun:u8|#![auto] 0<=ioid<IOID_MAX && self.get_free_ioids_as_set().contains(ioid) && 0<=bus<256 && 0<=dev<32 && 0<=fun<8 
            ==>
            self.pci_bitmap@[(ioid,bus,dev,fun)] == false
        // &&
        // self.ioid_device_table@.len() == IOID_MAX
        // &&
        // forall|ioid:Pcid| #![auto] 0<=ioid<IOID_MAX ==> self.ioid_device_table@[ioid as int].finite()
        // &&
        // forall|ioid:Pcid, i:int| #![auto] 0<=ioid<IOID_MAX && 0<=i<256 && self.device_table@[ioid as int]@[i].is_Some() ==>
        //     (
        //         0<=self.device_table@[ioid as int]@[i].get_Some_0().0<256
        //         &&
        //         0<=self.device_table@[ioid as int]@[i].get_Some_0().1<32
        //         &&
        //         0<=self.device_table@[ioid as int]@[i].get_Some_0().2<8
        //         // &&
        //         // self.ioid_device_table@[ioid as int].contains(self.device_table@[ioid as int]@[i].get_Some_0())
        //     )
        // &&
        // forall|ioid:Pcid, dev:(u8,u8,u8)| #![auto] 0<=ioid<IOID_MAX && self.ioid_device_table@[ioid as int].contains(dev) ==>
        //     (
        //         0<=dev.0<256
        //         &&
        //         0<=dev.1<32
        //         &&
        //         0<=dev.2<8
        //         &&
        //         exists|_ioid:Pcid, _i:int| #![auto] 0<=_ioid<IOID_MAX && 0<=_i<256 && self.device_table@[ioid as int]@[i].is_Some() && dev =~= self.device_table@[ioid as int]@[i].get_Some_0()
        //     )
        // &&
        // forall|ioid:Pcid, i:int, j:int| #![auto] 0<=ioid<IOID_MAX && 0<=i<256 && 0<=j<256 && self.device_table@[ioid as int]@[i].is_Some() && self.device_table@[ioid as int]@[j].is_Some()==>
        // (
        //     self.device_table@[ioid as int]@[i].get_Some_0() =~= self.device_table@[ioid as int]@[j].get_Some_0() == false
        // )
        // &&
        // forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 && self.root_table.resolve(bus,dev,fun).is_Some() ==>
        //     (
        //         exists|i:int|#![auto]  0<i<256 && self.device_table@[self.root_table.resolve(bus,dev,fun).get_Some_0().0 as int][i].is_Some()
        //             && self.device_table@[self.root_table.resolve(bus,dev,fun).get_Some_0().0 as int][i].get_Some_0() =~= (bus,dev,fun)
        //     )
    }

    pub open spec fn root_table_cache_wf(&self) -> bool{
        &&&
        self.root_table_cache@.len() == 256
        &&&
        forall|bus:u8|#![auto] 0<=bus<256 ==> self.root_table_cache@[bus as int].len() == 32
        &&&
        forall|bus:u8,dev:u8|#![auto] 0<=bus<256 && 0<=dev<32 ==> self.root_table_cache@[bus as int][dev as int].len() == 8
        &&&
        forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 && self.root_table_cache@[bus as int][dev as int][fun as int].is_Some() 
            ==>
            self.root_table_cache@[bus as int][dev as int][fun as int] =~= self.root_table.resolve(bus,dev,fun)
    }

    pub open spec fn page_closure(&self) -> Set<PagePtr>
    {
        self.iommu_table_pages@ + self.page_table_pages@
    }

    pub open spec fn get_pagetable_by_pcid(&self, pcid: Pcid) -> Option<PageTable>
        recommends 
            0<=pcid<PCID_MAX,
    {
        self.page_tables[pcid as int]
    }

    pub open spec fn get_pagetable_mapping_by_pcid(&self, pcid: Pcid) -> Map<VAddr,MapEntry>
        recommends 
            0<=pcid<PCID_MAX,
            self.get_pagetable_by_pcid(pcid).is_Some(),
    {
        self.page_tables[pcid as int].unwrap().mapping_4k()
    }
    
    pub open spec fn get_pagetable_page_closure_by_pcid(&self, pcid: Pcid) -> Set<PagePtr>
        recommends 
            0<=pcid<PCID_MAX,
            self.get_pagetable_by_pcid(pcid).is_Some(),
    {
        self.page_tables[pcid as int].unwrap().page_closure()
    }

    pub open spec fn get_free_pcids_as_set(&self) -> Set<IOid>
    {
        self.free_pcids@.to_set()
    }

    pub open spec fn get_free_ioids_as_set(&self) -> Set<IOid>
    {
        self.free_ioids@.to_set()
    }

    pub open spec fn get_iommutable_by_ioid(&self, ioid: IOid) -> Option<PageTable>
        recommends 
            0<=ioid<IOID_MAX,
    {
        self.iommu_tables[ioid as int]
    }

    pub open spec fn get_iommutable_mapping_by_ioid(&self, ioid: IOid) -> Map<VAddr,MapEntry>
        recommends 
            0<=ioid<IOID_MAX,
            self.get_iommutable_by_ioid(ioid).is_Some(),
    {
        self.iommu_tables[ioid as int].unwrap().mapping_4k()
    }

    pub open spec fn get_iommutable_page_closure_by_ioid(&self, ioid: IOid) -> Set<PagePtr>
        recommends 
            0<=ioid<IOID_MAX,
            self.get_iommutable_by_ioid(ioid).is_Some(),
    {
        self.iommu_tables[ioid as int].unwrap().page_closure()
    }

    pub fn get_cr3_by_pcid(&self, pcid:Pcid) -> (ret:usize)
        requires
            self.wf(),
            0<=pcid<PCID_MAX,
            self.get_free_pcids_as_set().contains(pcid) == false,
            self.get_pagetable_by_pcid(pcid).is_Some(),
    {
        return self.page_tables.get(pcid).as_ref().unwrap().cr3;
    }

    pub fn get_cr3_by_ioid(&self, ioid:IOid) -> (ret:usize)
        requires
            self.wf(),
            0<=ioid<IOID_MAX,
            self.get_free_ioids_as_set().contains(ioid) == false,
            self.get_iommutable_by_ioid(ioid).is_Some(),
        ensures
            self.get_iommutable_by_ioid(ioid).unwrap().cr3 == ret,
    {
        return self.iommu_tables.get(ioid).as_ref().unwrap().cr3;
    }

    pub fn get_pci_binding(&self, bus:u8,dev:u8,fun:u8) -> (ret:Option<(IOid,usize)>)
        requires
            0<=bus<256 && 0<=dev<32 && 0<=fun<8,
            self.wf(),
        ensures
            ret =~= self.root_table.resolve(bus,dev,fun),
    {
        return self.root_table.get_ioid(bus,dev,fun);
    }

    // #[verifier(inline)]
    pub open spec fn wf(&self) -> bool
    {
        &&&
        self.pagetables_wf()
        &&&
        self.iommutables_wf()
        &&&
        self.pagetable_iommutable_disjoint()
        &&&
        self.root_table_wf()
        &&&
        self.root_table_cache_wf()
        &&&
        self.kernel_entries_wf()
    }
}
}
