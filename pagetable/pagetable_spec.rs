use vstd::prelude::*;

// pub const KERNEL_PML4_SIG: Option<PageEntry> = None; // hack @Xiangdong

verus! {
// use vstd::ptr::PointsTo;
use crate::define::*;
use crate::array::*;
// use crate::page_alloc::*;
use vstd::simple_pptr::*;
use crate::util::page_ptr_util_u::*;

use crate::pagetable::page_entry::*;
use crate::pagetable::pagemap::*;

pub struct MapEntry{
    pub addr: PAddr,
    pub write: bool,
    pub execute_disable: bool,
}

// pub open spec fn map_entry_equals_to_page_entry_unwrapped(m:MapEntry, p:PageEntry) -> bool{
//     &&&
//     m.addr == p.addr
//     &&&
//     m.write == p.perm.write
//     &&&
//     m.execute_disable == p.perm.execute_disable
// }

// pub open spec fn map_entry_equals_to_page_entry(m:Option<MapEntry>, p:Option<PageEntry>) -> bool {
//     if m.is_Some() != p.is_Some(){
//         return false;
//     }else if m.is_None() && p.is_None() {
//         return true;
//     }else{
//         return map_entry_equals_to_page_entry_unwrapped(m.get_Some_0(), p.get_Some_0());
//     }
// }

pub struct PageTable{
    pub cr3: PAddr,

    pub l4_table: Tracked<Map<PAddr,PointsTo<PageMap>>>,
    pub l3_tables: Tracked<Map<PAddr,PointsTo<PageMap>>>,
    pub l2_tables: Tracked<Map<PAddr,PointsTo<PageMap>>>,
    pub l1_tables: Tracked<Map<PAddr,PointsTo<PageMap>>>,

    pub mapping_4k: Ghost<Map<VAddr,Option<MapEntry>>>,
    pub mapping_2m: Ghost<Map<VAddr,Option<MapEntry>>>,
    pub mapping_1g: Ghost<Map<VAddr,Option<MapEntry>>>,
}


impl PageTable{

    // pub fn new(cr3:usize) -> (ret:Self)
    // {
    //     Self{
    //         cr3 : cr3,
    //         l4_table: Tracked(Map::tracked_empty()),
    //         l3_tables: Tracked(Map::tracked_empty()),
    //         l2_tables: Tracked(Map::tracked_empty()),
    //         l1_tables: Tracked(Map::tracked_empty()),
    //         mapping: Ghost(Map::empty()),
    //     }
    // }

    // pub fn init(&mut self)
    //     requires
    //         old(self).l4_table@ =~= Map::empty(),
    //         old(self).l3_tables@ =~= Map::empty(),
    //         old(self).l2_tables@ =~= Map::empty(),
    //         old(self).l1_tables@ =~= Map::empty(),
    //     ensures
    //         self.wf_mapping(),
    //         self.get_pagetable_page_closure() =~= Set::empty(),
    //         self.l4_table@ =~= Map::empty(),
    //         self.l3_tables@ =~= Map::empty(),
    //         self.l2_tables@ =~= Map::empty(),
    //         self.l1_tables@ =~= Map::empty(),
    //         forall|va:VAddr|#![auto] spec_va_valid(va) ==> self.mapping@.dom().contains(va),
    //         forall|va:VAddr|#![auto] spec_va_valid(va) ==> self.mapping@[va].is_None(),
    //     {
    //         self.cr3 = 0;
    //         proof{
    //             pagetable_virtual_mem_lemma();
    //             self.mapping@ = Map::<VAddr,Option<PageEntry>>::new(
    //                 |va: VAddr| { spec_va_valid(va)
    //                 },
    //                 |va: VAddr| {
    //                     None
    //                 }
    //             );
    //         }
    //     }

    pub open spec fn page_closure(&self) -> Set<PagePtr>{
            self.l3_tables@.dom() + self.l2_tables@.dom() + self.l1_tables@.dom() + self.l4_table@.dom()
    }

    pub open spec fn mapping_4k(&self) -> Map<VAddr,Option<MapEntry>> {
        self.mapping_4k@
    }

    pub open spec fn mapping_2m(&self) -> Map<VAddr,Option<MapEntry>> {
        self.mapping_2m@
    }

    pub open spec fn mapping_1g(&self) -> Map<VAddr,Option<MapEntry>> {
        self.mapping_1g@
    }

    pub open spec fn wf_l4(&self) -> bool{
        &&&
        self.cr3 != 0
        &&&
        self.l4_table@.dom() =~=  Set::<PAddr>::empty().insert(self.cr3)
        &&&
        self.cr3 == self.l4_table@[self.cr3].addr()
        &&&
        self.l4_table@[self.cr3].is_init()
        &&&
        self.l4_table@[self.cr3].value().wf()
        //L4 table only maps to L3
        &&&
        forall|i: L4Index, j: L4Index|
            // #![trigger self.l4_table@[self.cr3].value()[i].perm.present, self.l4_table@[self.cr3].value()[j].perm.present]
            #![trigger self.l4_table@[self.cr3].value()[i].addr, self.l4_table@[self.cr3].value()[j].addr]
            i != j && 0 <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present && 0 <= j < 512 && self.l4_table@[self.cr3].value()[j].perm.present ==>
                self.l4_table@[self.cr3].value()[i].addr != self.l4_table@[self.cr3].value()[j].addr
        &&&
        forall|i: L4Index| 
            // #![trigger self.l4_table@[self.cr3].value()[i].perm.present]
            #![trigger self.l2_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)]
            #![trigger self.l1_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)]
            0 <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present ==> 
                self.l2_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr) == false
                &&
                self.l1_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr) == false
                &&
                self.cr3 != self.l4_table@[self.cr3].value()[i].addr
        // no self mapping        
        &&&
        forall|i: L4Index| 
            // #![trigger self.l4_table@[self.cr3].value()[i].perm.present]
            #![trigger self.l4_table@[self.cr3].value()[i].addr]
            0 <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present ==>
                self.cr3 != self.l4_table@[self.cr3].value()[i].addr
        //all l4 points to valid l3 tables 
        &&&
        forall|i: L4Index|
            #![trigger self.l3_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)]
            0 <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present && !self.l4_table@[self.cr3].value()[i].perm.ps ==>
                self.l3_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)
        //no hugepage in L4 (hardware limit)        
        &&&
        forall|i: L4Index| 
            #![trigger self.l4_table@[self.cr3].value()[i].perm.ps ]
            0 <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present ==> 
                !self.l4_table@[self.cr3].value()[i].perm.ps 
    }

    pub open spec fn wf_l3(&self) -> bool{
        &&&
        self.l3_tables@.dom().contains(0) == false
        &&&
        forall|pa: PAddr|
            #![trigger self.l3_tables@[pa].addr()]
            self.l3_tables@.dom().contains(pa) ==> self.l3_tables@[pa].addr() == pa
        &&&
        forall|pa: PAddr| 
            #![trigger self.l3_tables@[pa].is_init()]
            self.l3_tables@.dom().contains(pa) ==> self.l3_tables@[pa].is_init()
        &&&
        forall|pa: PAddr|
            #![trigger self.l3_tables@[pa].value().wf()]
            self.l3_tables@.dom().contains(pa) ==> self.l3_tables@[pa].value().wf()
        // all l3 tables exists in L4    
        &&&
        forall|pa: PAddr|
            #![trigger self.l3_tables@.dom().contains(pa)]
            self.l3_tables@.dom().contains(pa) ==>
                exists|l4i:L4Index|
                    #![trigger self.l4_table@[self.cr3].value()[l4i].addr]
                    0 <= l4i < 512 && self.l4_table@[self.cr3].value()[l4i].perm.present && !self.l4_table@[self.cr3].value()[l4i].perm.ps &&
                    self.l4_table@[self.cr3].value()[l4i].addr == pa
        //L3 tables unique within
        &&&
        forall|pa: PAddr, l3i: L3Index, l3j: L3Index| 
            #![trigger self.l3_tables@[pa].value()[l3i].perm.present, self.l3_tables@[pa].value()[l3j].perm.present]
            #![trigger self.l3_tables@[pa].value()[l3i].addr, self.l3_tables@[pa].value()[l3j].addr]
            self.l3_tables@.dom().contains(pa) && l3i != l3j && 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[pa].value()[l3i].perm.present && self.l3_tables@[pa].value()[l3j].perm.present ==> 
                self.l3_tables@[pa].value()[l3i].addr != self.l3_tables@[pa].value()[l3j].addr
        //L3 tables are disjoint        
        &&&        
        forall|pai: PAddr, paj: PAddr, l3i: L3Index, l3j: L3Index|  
            #![trigger self.l3_tables@[pai].value()[l3i].perm.present, self.l3_tables@[paj].value()[l3j].perm.present]
            #![trigger self.l3_tables@[pai].value()[l3i].addr, self.l3_tables@[paj].value()[l3j].addr]
            pai != paj && self.l3_tables@.dom().contains(pai) && self.l3_tables@.dom().contains(paj) && 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[pai].value()[l3i].perm.present && self.l3_tables@[paj].value()[l3j].perm.present ==>
                self.l3_tables@[pai].value()[l3i].addr != self.l3_tables@[paj].value()[l3j].addr
        //L3 tables does not map to L4 or L1        
        &&&
        forall|pa: PAddr, i: L3Index| 
            #![trigger self.l3_tables@[pa].value()[i].perm.present] 
            #![trigger self.l3_tables@.dom().contains(self.l3_tables@[pa].value()[i].addr)] 
            #![trigger self.l1_tables@.dom().contains(self.l3_tables@[pa].value()[i].addr)] 
            #![trigger self.l3_tables@[pa].value()[i].addr] 
            self.l3_tables@.dom().contains(i) && 0 <= i < 512 && self.l3_tables@[pa].value()[i].perm.present ==>
                self.l3_tables@.dom().contains(self.l3_tables@[pa].value()[i].addr) == false
                &&
                self.l1_tables@.dom().contains(self.l3_tables@[pa].value()[i].addr) == false
                &&
                self.cr3 != self.l3_tables@[pa].value()[i].addr
        // 1G hugepages have no entries in l2
        &&&
        forall|pa: PAddr, i: L3Index| 
            #![trigger self.l3_tables@[pa].value()[i].perm.present] 
            #![trigger self.l3_tables@.dom().contains(self.l3_tables@[pa].value()[i].addr)] 
            #![trigger self.l2_tables@.dom().contains(self.l3_tables@[pa].value()[i].addr)] 
            #![trigger self.l1_tables@.dom().contains(self.l3_tables@[pa].value()[i].addr)] 
            #![trigger self.l3_tables@[pa].value()[i].addr] 
            self.l3_tables@.dom().contains(pa) && 0 <= i < 512 && self.l3_tables@[pa].value()[i].perm.ps ==>
                self.l3_tables@.dom().contains(self.l3_tables@[pa].value()[i].addr) == false
                &&
                self.l2_tables@.dom().contains(self.l3_tables@[pa].value()[i].addr) == false
                &&
                self.l1_tables@.dom().contains(self.l3_tables@[pa].value()[i].addr) == false
                &&
                self.cr3 != self.l3_tables@[pa].value()[i].addr
        // all l3 points to valid l2 tables
        &&&
        forall|pa: PAddr, i: L3Index| 
            #![trigger self.l3_tables@[pa].value()[i].perm.present, self.l3_tables@[pa].value()[i].perm.ps ] 
            #![trigger self.l2_tables@.dom().contains(self.l3_tables@[pa].value()[i].addr)] 
            self.l3_tables@.dom().contains(pa) && 0 <= i < 512 && self.l3_tables@[pa].value()[i].perm.present && !self.l3_tables@[pa].value()[i].perm.ps ==>
                self.l2_tables@.dom().contains(self.l3_tables@[pa].value()[i].addr)
    }

    pub open spec fn wf_l2(&self) -> bool{
        &&&
        self.l2_tables@.dom().contains(0) == false
        &&&
        forall|pa: PAddr|
            #![trigger self.l2_tables@[pa].addr()] 
            self.l2_tables@.dom().contains(pa) ==> self.l2_tables@[pa].addr() == pa
        &&&
        forall|pa: PAddr|
            #![trigger self.l2_tables@[pa].is_init()] 
            self.l2_tables@.dom().contains(pa) ==> self.l2_tables@[pa].is_init()
        &&&
        forall|pa: PAddr|
            #![trigger self.l2_tables@[pa].value().wf()] 
            self.l2_tables@.dom().contains(pa) ==> self.l2_tables@[pa].value().wf()
        // all l2 tables exist in l3 mapping
        &&&
        forall|pai: PAddr|
            #![trigger self.l2_tables@.dom().contains(pai)]
            self.l2_tables@.dom().contains(pai) ==>
                exists|paj: PAddr, l3i:L3Index|
                    #![trigger self.l3_tables@[paj].value()[l3i].perm.present]
                    #![trigger self.l3_tables@[paj].value()[l3i].perm.ps]
                    #![trigger self.l3_tables@[paj].value()[l3i].addr]
                    0 <= l3i < 512 && self.l3_tables@.dom().contains(paj) && self.l3_tables@[paj].value()[l3i].perm.present && !self.l3_tables@[paj].value()[l3i].perm.ps &&
                    self.l3_tables@[paj].value()[l3i].addr == pai
        // L2 mappings are unique within
        &&&
        forall|pa: PAddr, l2i: L2Index, l2j: L2Index| 
            #![trigger self.l2_tables@[pa].value()[l2i].perm.present, self.l2_tables@[pa].value()[l2j].perm.present]
            #![trigger self.l2_tables@[pa].value()[l2i].addr, self.l2_tables@[pa].value()[l2j].addr]
            self.l2_tables@.dom().contains(pa) && l2i != l2j && 0 <= l2i < 512 && 0 <= l2j < 512 && self.l2_tables@[pa].value()[l2i].perm.present && self.l2_tables@[pa].value()[l2j].perm.present  ==>
                self.l2_tables@[pa].value()[l2i].addr != self.l2_tables@[pa].value()[l2j].addr
        // L2 mappings are unique
        &&&
        forall|pai: PAddr, paj: PAddr, l2i: L2Index, l2j: L2Index|
            #![trigger self.l2_tables@[pai].value()[l2i].perm.present, self.l2_tables@[paj].value()[l2j].perm.present]
            #![trigger self.l2_tables@[pai].value()[l2i].addr, self.l2_tables@[paj].value()[l2j].addr]
            pai != paj && self.l2_tables@.dom().contains(pai) && self.l2_tables@.dom().contains(paj) && 0 <= l2i < 512 && 0 <= l2j < 512 && self.l2_tables@[pai].value()[l2i].perm.present && self.l2_tables@[paj].value()[l2j].perm.present ==>
                self.l2_tables@[pai].value()[l2i].addr != self.l2_tables@[paj].value()[l2j].addr
        // L2 does not map to L4, L3, or self
        &&&
        forall|pa: PAddr, i: L2Index| 
            #![trigger self.l2_tables@[pa].value()[i].perm.present] 
            #![trigger self.l2_tables@.dom().contains(self.l2_tables@[pa].value()[i].addr)] 
            #![trigger self.l3_tables@.dom().contains(self.l2_tables@[pa].value()[i].addr)] 
            #![trigger self.l2_tables@[pa].value()[i].addr] 
            self.l2_tables@.dom().contains(pa) && 0 <= i < 512 && self.l2_tables@[pa].value()[i].perm.present ==>
                self.l2_tables@.dom().contains(self.l2_tables@[pa].value()[i].addr) == false
                &&
                self.l3_tables@.dom().contains(self.l2_tables@[pa].value()[i].addr) == false
                &&
                self.cr3 != self.l2_tables@[pa].value()[i].addr
        // 2M hugepages does not map to L4, L3, L2 or L1
        &&&
        forall|pa: PAddr, i: L2Index| 
            #![trigger self.l2_tables@[pa].value()[i].perm.present] 
            #![trigger self.l2_tables@.dom().contains(self.l2_tables@[pa].value()[i].addr)] 
            #![trigger self.l3_tables@.dom().contains(self.l2_tables@[pa].value()[i].addr)] 
            #![trigger self.l1_tables@.dom().contains(self.l2_tables@[pa].value()[i].addr)] 
            #![trigger self.l2_tables@[pa].value()[i].addr] 
            self.l2_tables@.dom().contains(pa) && 0 <= i < 512 && self.l2_tables@[pa].value()[i].perm.present && self.l2_tables@[pa].value()[i].perm.ps ==>
                self.l2_tables@.dom().contains(self.l2_tables@[pa].value()[i].addr) == false
                &&
                self.l1_tables@.dom().contains(self.l2_tables@[pa].value()[i].addr) == false
                &&
                self.l3_tables@.dom().contains(self.l2_tables@[pa].value()[i].addr) == false
                &&
                self.cr3 != self.l2_tables@[pa].value()[i].addr
        // all l2 points to valid l1 tables
        &&&
        forall|pa: PAddr, i: L2Index| 
            #![trigger self.l2_tables@[pa].value()[i].perm.present, self.l2_tables@[pa].value()[i].perm.ps ] 
            #![trigger self.l1_tables@.dom().contains(self.l2_tables@[pa].value()[i].addr)] 
            self.l2_tables@.dom().contains(pa) && 0 <= i < 512 && self.l2_tables@[pa].value()[i].perm.present && !self.l2_tables@[pa].value()[i].perm.ps ==>
                self.l1_tables@.dom().contains(self.l2_tables@[pa].value()[i].addr)
    }

    pub open spec fn wf_l1(&self) -> bool{
        &&&
        self.l1_tables@.dom().contains(0) == false
        &&&
        forall|pa: PAddr| 
            #![trigger self.l1_tables@[pa].addr()] 
            self.l1_tables@.dom().contains(pa) ==> self.l1_tables@[pa].addr() == pa
        &&&
        forall|pa: PAddr| 
            #![trigger self.l1_tables@[pa].is_init()] 
            self.l1_tables@.dom().contains(pa) ==> self.l1_tables@[pa].is_init()
        &&&
        forall|pa: PAddr| 
            #![trigger self.l1_tables@[pa].value().wf()] 
            self.l1_tables@.dom().contains(pa) ==> self.l1_tables@[pa].value().wf()
        // all l1 tables exist in l2 mapping
        &&&
        forall|pai: PAddr|
            #![trigger self.l1_tables@.dom().contains(pai)] 
            self.l1_tables@.dom().contains(pai) ==>
                exists|paj:PAddr,l2i:L2Index|
                    #![trigger self.l2_tables@[paj].value()[l2i].perm.present] 
                    #![trigger self.l2_tables@[paj].value()[l2i].addr] 
                    0<=l2i<512 && self.l2_tables@.dom().contains(paj) && self.l2_tables@[paj].value()[l2i].perm.present &&
                    self.l2_tables@[paj].value()[l2i].addr == pai
        // l1 does not map to page table
        &&&
        forall|pa: PAddr, i: L1Index| 
            #![trigger self.l1_tables@[pa].value()[i].perm.present] 
            #![trigger self.l1_tables@.dom().contains(self.l1_tables@[pa].value()[i].addr)] 
            #![trigger self.l2_tables@.dom().contains(self.l1_tables@[pa].value()[i].addr)] 
            #![trigger self.l3_tables@.dom().contains(self.l1_tables@[pa].value()[i].addr)] 
            #![trigger self.l1_tables@[pa].value()[i].addr] 
            self.l1_tables@.dom().contains(pa) && 0 <= i < 512 && self.l1_tables@[pa].value()[i].perm.present ==>
                self.l1_tables@.dom().contains(self.l2_tables@[pa].value()[i].addr) == false
                &&
                self.l2_tables@.dom().contains(self.l2_tables@[pa].value()[i].addr) == false
                &&
                self.l3_tables@.dom().contains(self.l2_tables@[pa].value()[i].addr) == false
                &&
                self.cr3 != self.l1_tables@[pa].value()[i].addr
        // no hugepage in l1
        &&&
        forall|pa: PAddr, i: L1Index| 
            #![trigger self.l1_tables@[pa].value()[i].perm.ps] 
            self.l1_tables@.dom().contains(pa) && 0 <= i < 512 && self.l1_tables@[pa].value()[i].perm.present ==>
                ! self.l1_tables@[pa].value()[i].perm.ps
    }

    pub open spec fn resolve_mapping_l4(&self, l4i: L4Index) -> Option<PageEntry>
        recommends
            0 <= l4i < 512,
    {
        if self.cr3 == 0{
            None
        }else if !self.l4_table@[self.cr3].value()[l4i].perm.present{
            None
        }else{
            Some(self.l4_table@[self.cr3].value()[l4i])
        }
    }

    pub open spec fn resolve_mapping_4k_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<PageEntry>
    recommends
        0<= l4i < 512,
        0<= l3i < 512,
    {
        if self.resolve_mapping_l4(l4i).is_None() {
            None
        }else if !self.l3_tables@[self.resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i].perm.present || self.l3_tables@[self.resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i].perm.ps {
            None
        }else{
            Some(self.l3_tables@[self.resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i])
        }
    }

    pub open spec fn resolve_mapping_4k_l2(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> Option<PageEntry>
    recommends
        0<= l4i < 512,
        0<= l3i < 512,
        0<= l2i < 512,
    {
        if self.resolve_mapping_4k_l3(l4i,l3i).is_None() {
            None
        }else if !self.l2_tables@[self.resolve_mapping_4k_l3(l4i,l3i).get_Some_0().addr].value()[l2i].perm.present || self.l2_tables@[self.resolve_mapping_4k_l3(l4i,l3i).get_Some_0().addr].value()[l2i].perm.ps {
            None
        }else{
            Some(self.l2_tables@[self.resolve_mapping_4k_l3(l4i,l3i).get_Some_0().addr].value()[l2i])
        }
    }

    pub open spec fn resolve_mapping_4k_l1(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index) -> Option<PageEntry>
    recommends
        0<= l4i < 512,
        0<= l3i < 512,
        0<= l2i < 512,
        0<= l1i < 512,
    {
        if self.resolve_mapping_4k_l2(l4i,l3i,l2i).is_None() {
            None
        }else if !self.l1_tables@[self.resolve_mapping_4k_l2(l4i,l3i,l2i).get_Some_0().addr].value()[l1i].perm.present {
            None
        }else{
            Some(self.l1_tables@[self.resolve_mapping_4k_l2(l4i,l3i,l2i).get_Some_0().addr].value()[l1i])
        }

    }

    pub open spec fn resolve_mapping_2m_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<PageEntry>
    recommends
        0<= l4i < 512,
        0<= l3i < 512,
    {
        if self.resolve_mapping_l4(l4i).is_None() {
            None
        }else if !self.l3_tables@[self.resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i].perm.present || self.l3_tables@[self.resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i].perm.ps {
            None
        }else{
            Some(self.l3_tables@[self.resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i])
        }
    }

    pub open spec fn resolve_mapping_2m_l2(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> Option<PageEntry>
    recommends
        0<= l4i < 512,
        0<= l3i < 512,
        0<= l2i < 512,
    {
        if self.resolve_mapping_2m_l3(l4i,l3i).is_None() {
            None
        }else if !self.l2_tables@[self.resolve_mapping_2m_l3(l4i,l3i).get_Some_0().addr].value()[l2i].perm.present || !self.l2_tables@[self.resolve_mapping_2m_l3(l4i,l3i).get_Some_0().addr].value()[l2i].perm.ps {
            None
        }else{
            Some(self.l2_tables@[self.resolve_mapping_2m_l3(l4i,l3i).get_Some_0().addr].value()[l2i])
        }
    }

    pub open spec fn resolve_mapping_1g_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<PageEntry>
    recommends
        0<= l4i < 512,
        0<= l3i < 512,
    {
        if self.resolve_mapping_l4(l4i).is_None() {
            None
        }else if !self.l3_tables@[self.resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i].perm.present || !self.l3_tables@[self.resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i].perm.ps {
            None
        }else{
            Some(self.l3_tables@[self.resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i])
        }
    }

    pub open spec fn wf_mapping_4k(&self) -> bool{
        &&&
        forall|va: VAddr| 
            #![trigger va_4k_valid(va), self.mapping_4k@.dom().contains(va)]
            va_4k_valid(va) ==> self.mapping_4k@.dom().contains(va)
        &&&
        forall|l4i: L4Index,l3i: L3Index,l2i: L2Index, l1i: L1Index| 
            #![trigger self.mapping_4k@[spec_index2va((l4i,l3i,l2i,l1i))], self.resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
            0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512
                ==> (self.mapping_4k@[spec_index2va((l4i,l3i,l2i,l1i))].is_None() && self.resolve_mapping_4k_l1(l4i,l3i,l2i,l1i).is_None()) 
                    ||
                    (self.mapping_4k@[spec_index2va((l4i,l3i,l2i,l1i))].get_Some_0().addr == self.resolve_mapping_4k_l1(l4i,l3i,l2i,l1i).get_Some_0().addr &&
                    self.mapping_4k@[spec_index2va((l4i,l3i,l2i,l1i))].get_Some_0().write == self.resolve_mapping_4k_l1(l4i,l3i,l2i,l1i).get_Some_0().perm.write &&
                    self.mapping_4k@[spec_index2va((l4i,l3i,l2i,l1i))].get_Some_0().execute_disable == self.resolve_mapping_4k_l1(l4i,l3i,l2i,l1i).get_Some_0().perm.execute_disable)

    }

    pub open spec fn wf_mapping_2m(&self) -> bool{
        &&&
        forall|va: VAddr| 
            #![trigger va_2m_valid(va), self.mapping_2m@.dom().contains(va)]
            va_2m_valid(va) ==> self.mapping_2m@.dom().contains(va)
        &&&
        forall|l4i: L4Index,l3i: L3Index,l2i: L2Index| 
            #![trigger self.mapping_2m@[spec_index2va((l4i,l3i,l2i,0))], self.resolve_mapping_2m_l2(l4i,l3i,l2i)]
            0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512
                ==> (self.mapping_2m@[spec_index2va((l4i,l3i,l2i,0))].is_None() && self.resolve_mapping_2m_l2(l4i,l3i,l2i).is_None()) 
                    ||
                    (self.mapping_2m@[spec_index2va((l4i,l3i,l2i,0))].get_Some_0().addr == self.resolve_mapping_2m_l2(l4i,l3i,l2i).get_Some_0().addr &&
                    self.mapping_2m@[spec_index2va((l4i,l3i,l2i,0))].get_Some_0().write == self.resolve_mapping_2m_l2(l4i,l3i,l2i).get_Some_0().perm.write &&
                    self.mapping_2m@[spec_index2va((l4i,l3i,l2i,0))].get_Some_0().execute_disable == self.resolve_mapping_2m_l2(l4i,l3i,l2i).get_Some_0().perm.execute_disable)
    }

    pub open spec fn wf_mapping_1g(&self) -> bool{
        &&&
        forall|va: VAddr| 
            #![trigger va_1g_valid(va), self.mapping_1g@.dom().contains(va)]
            va_1g_valid(va) ==> self.mapping_1g@.dom().contains(va)
        &&&
        forall|l4i: L4Index,l3i: L3Index| 
            #![trigger self.mapping_1g@[spec_index2va((l4i,l3i,0,0))], self.resolve_mapping_1g_l3(l4i,l3i)]
            0 <= l4i < 512 && 0 <= l3i < 512
                ==> (self.mapping_2m@[spec_index2va((l4i,l3i,0,0))].is_None() && self.resolve_mapping_1g_l3(l4i,l3i).is_None()) 
                    ||
                    (self.mapping_2m@[spec_index2va((l4i,l3i,0,0))].get_Some_0().addr == self.resolve_mapping_1g_l3(l4i,l3i).get_Some_0().addr &&
                    self.mapping_2m@[spec_index2va((l4i,l3i,0,0))].get_Some_0().write == self.resolve_mapping_1g_l3(l4i,l3i).get_Some_0().perm.write &&
                    self.mapping_2m@[spec_index2va((l4i,l3i,0,0))].get_Some_0().execute_disable == self.resolve_mapping_1g_l3(l4i,l3i).get_Some_0().perm.execute_disable)
    }

    pub open spec fn wf(&self) -> bool
    {
        &&&
        self.wf_l4()
        &&&
        self.wf_l3()
        &&&
        self.wf_l2()
        &&&
        self.wf_l1()
        &&&
        self.wf_mapping_4k()
        &&&
        self.wf_mapping_2m()
        &&&
        self.wf_mapping_1g()
    }

    // pub open spec fn l4_kernel_entries_reserved(&self) -> bool
    //     recommends self.wf_l4(),
    // {
    //     forall|l4i: L4Index| #![auto] 0<=l4i<KERNEL_MEM_END_L4INDEX ==> self.l4_table@[self.cr3]@.value.get_Some_0()[l4i].is_None()
    // }


    pub open spec fn l4_entry_exists(&self, l4i: L4Index) -> bool
        recommends self.wf(),
    {
        self.resolve_mapping_l4(l4i).is_Some()
    }

    pub open spec fn l3_2m_entry_exists(&self, l4i: L4Index, l3i :L3Index) -> bool
        recommends self.wf(),
                    self.l4_entry_exists(l4i)
    {
        self.resolve_mapping_2m_l3(l4i,l3i).is_Some()
    }

    pub open spec fn l3_4k_entry_exists(&self, l4i: L4Index, l3i :L3Index) -> bool
        recommends self.wf(),
                    self.l4_entry_exists(l4i)
    {
        self.resolve_mapping_4k_l3(l4i,l3i).is_Some()
    }

    pub open spec fn l2_4k_entry_exists(&self, l4i: L4Index, l3i :L3Index, l2i :L2Index) -> bool
        recommends self.wf(),
                    self.l3_4k_entry_exists(l4i,l3i)
    {
        self.resolve_mapping_4k_l2(l4i,l3i,l2i).is_Some()
    }

}

}
