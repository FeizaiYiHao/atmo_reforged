use vstd::prelude::*;

verus! {
use crate::define::*;
// use crate::array::*;
use vstd::simple_pptr::*;
use crate::util::page_ptr_util_u::*;
// use crate::pagetable::pagetable_util::*;
use crate::pagetable::entry::*;
use crate::pagetable::pagemap::*;

// pub open spec fn map_entry_equals_to_page_entry_unwrapped(m:MapEntry, p:PageEntry) -> bool{
//     &&&
//     m.addr == p.addr
//     &&&
//     m.write == p.perm.write
//     &&&
//     m.execute_disable == p.perm.execute_disable
// }

// pub open spec fn map_entry_equals_to_page_entry(m:MapEntry, p:Option<PageEntry>) -> bool {
//     if m.is_Some() != p.is_Some(){
//         return false;
//     }else if m.is_None() && p.is_None() {
//         return true;
//     }else{
//         return map_entry_equals_to_page_entry_unwrapped(m.get_Some_0(), p.get_Some_0());
//     }
// }

pub struct PageTable{
    pub cr3: PageMapPtr,

    pub l4_table: Tracked<Map<PageMapPtr,PointsTo<PageMap>>>,
    pub l3_rev_map: Ghost<Map<PageMapPtr, (L4Index)>>,
    pub l3_tables: Tracked<Map<PageMapPtr,PointsTo<PageMap>>>,
    pub l2_rev_map: Ghost<Map<PageMapPtr, (L4Index,L3Index)>>,
    pub l2_tables: Tracked<Map<PageMapPtr,PointsTo<PageMap>>>,
    pub l1_rev_map: Ghost<Map<PageMapPtr, (L4Index,L3Index,L2Index)>>,
    pub l1_tables: Tracked<Map<PageMapPtr,PointsTo<PageMap>>>,

    pub mapping_4k: Ghost<Map<VAddr,MapEntry>>,
    pub mapping_2m: Ghost<Map<VAddr,MapEntry>>,
    pub mapping_1g: Ghost<Map<VAddr,MapEntry>>,
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

    pub open spec fn mapping_4k(&self) -> Map<VAddr,MapEntry> {
        self.mapping_4k@
    }

    pub open spec fn mapping_2m(&self) -> Map<VAddr,MapEntry> {
        self.mapping_2m@
    }

    pub open spec fn mapping_1g(&self) -> Map<VAddr,MapEntry> {
        self.mapping_1g@
    }

    pub open spec fn page_not_mapped(&self, pa: PAddr) -> bool{
        &&&
        self.mapped_4k_pages().contains(pa) == false
        &&&
        self.mapped_2m_pages().contains(pa) == false
        &&&
        self.mapped_1g_pages().contains(pa) == false
    }

    pub open spec fn mapped_4k_pages(&self) -> Set<PAddr>{
        Set::<PAddr>::new(|pa: PAddr| self.is_4k_pa_mapped(pa))
    }

    pub open spec fn is_4k_pa_mapped(&self, pa:PAddr) -> bool
    {
        exists|va:VAddr| #![auto] self.mapping_4k().dom().contains(va) && self.mapping_4k()[va].addr == pa
    }

    pub open spec fn mapped_2m_pages(&self) -> Set<PAddr>{
        Set::<PAddr>::new(|pa: PAddr| self.is_2m_pa_mapped(pa))
    }

    pub open spec fn is_2m_pa_mapped(&self, pa:PAddr) -> bool
    {
        exists|va:VAddr| #![auto] self.mapping_2m().dom().contains(va) && self.mapping_2m()[va].addr == pa
    }
    pub open spec fn mapped_1g_pages(&self) -> Set<PAddr>{
        Set::<PAddr>::new(|pa: PAddr| self.is_1g_pa_mapped(pa))
    }

    pub open spec fn is_1g_pa_mapped(&self, pa:PAddr) -> bool
    {
        exists|va:VAddr| #![auto] self.mapping_1g().dom().contains(va) && self.mapping_1g()[va].addr == pa
    }

    pub open spec fn wf_l4(&self) -> bool{
        // &&&
        // self.cr3 != 0
        &&&
        self.l4_table@.dom() =~=  Set::<PageMapPtr>::empty().insert(self.cr3)
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
            #![trigger self.l4_table@[self.cr3].value()[i].perm.present, self.l4_table@[self.cr3].value()[j].perm.present, self.l4_table@[self.cr3].value()[i].addr, self.l4_table@[self.cr3].value()[j].addr]
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
            #![trigger self.l4_table@[self.cr3].value()[i].perm.ps]
            0 <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present ==> 
                !self.l4_table@[self.cr3].value()[i].perm.ps 
    }

    pub open spec fn wf_l3(&self) -> bool{
        // &&&
        // self.l3_tables@.dom().contains(0) == false
        &&&
        forall|p: PageMapPtr|
            #![trigger self.l3_tables@[p].addr()]
            self.l3_tables@.dom().contains(p) ==> self.l3_tables@[p].addr() == p
        &&&
        forall|p: PageMapPtr| 
            #![trigger self.l3_tables@[p].is_init()]
            self.l3_tables@.dom().contains(p) ==> self.l3_tables@[p].is_init()
        &&&
        forall|p: PageMapPtr|
            #![trigger self.l3_tables@[p].value().wf()]
            self.l3_tables@.dom().contains(p) ==> self.l3_tables@[p].value().wf()
        &&&
        forall|p: PageMapPtr|
            #![trigger self.l3_rev_map@.dom().contains(p)]
            #![trigger self.l3_rev_map@[p]]
            self.l3_tables@.dom().contains(p) ==>
                0 <= self.l3_rev_map@[p] < 512 &&
                self.l3_rev_map@.dom().contains(p) && self.spec_resolve_mapping_l4(self.l3_rev_map@[p]).is_Some() && self.spec_resolve_mapping_l4(self.l3_rev_map@[p]).get_Some_0().addr == p
        //L3 tables unique within
        &&&
        forall|p: PageMapPtr, l3i: L3Index, l3j: L3Index| 
            #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[l3i].addr, self.l3_tables@[p].value()[l3j].addr, self.l3_tables@[p].value()[l3i].perm.ps, self.l3_tables@[p].value()[l3j].perm.ps, self.l3_tables@[p].value()[l3i].addr, self.l3_tables@[p].value()[l3j].addr]
            self.l3_tables@.dom().contains(p) && l3i != l3j && 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[p].value()[l3i].perm.present && self.l3_tables@[p].value()[l3j].perm.present 
                && !self.l3_tables@[p].value()[l3i].perm.ps && !self.l3_tables@[p].value()[l3j].perm.ps 
                ==> 
                self.l3_tables@[p].value()[l3i].addr != self.l3_tables@[p].value()[l3j].addr
        //L3 tables are disjoint        
        &&&        
        forall|pi: PageMapPtr, pj: PageMapPtr, l3i: L3Index, l3j: L3Index|
            #![trigger self.l3_tables@.dom().contains(pi), self.l3_tables@.dom().contains(pj), self.l3_tables@[pi].value()[l3i].addr, self.l3_tables@[pj].value()[l3j].addr, self.l3_tables@[pi].value()[l3i].perm.ps, self.l3_tables@[pj].value()[l3j].perm.ps, self.l3_tables@[pi].value()[l3i].perm.present, self.l3_tables@[pj].value()[l3j].perm.present]
            pi != pj && self.l3_tables@.dom().contains(pi) && self.l3_tables@.dom().contains(pj) && 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[pi].value()[l3i].perm.present && self.l3_tables@[pj].value()[l3j].perm.present 
                && !self.l3_tables@[pi].value()[l3i].perm.ps && !self.l3_tables@[pj].value()[l3j].perm.ps
                ==>
                self.l3_tables@[pi].value()[l3i].addr != self.l3_tables@[pj].value()[l3j].addr
        //L3 tables does not map to L4 or L1        
        &&&
        forall|p: PageMapPtr, i: L3Index| 
            #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
            #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
            #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].addr] 
            self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.present ==>
                self.l3_tables@.dom().contains(self.l3_tables@[p].value()[i].addr) == false
                &&
                self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr) == false
                &&
                self.cr3 != self.l3_tables@[p].value()[i].addr
        // all l3 points to valid l2 tables
        &&&
        forall|p: PageMapPtr, i: L3Index| 
            #![trigger self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].perm.ps, self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
            // #![trigger self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)] 
            self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.present && !self.l3_tables@[p].value()[i].perm.ps ==>
                self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)
    }

    pub open spec fn wf_l2(&self) -> bool{
        // &&&
        // self.l2_tables@.dom().contains(0) == false
        &&&
        forall|p: PageMapPtr|
            #![trigger self.l2_tables@[p].addr()] 
            self.l2_tables@.dom().contains(p) ==> self.l2_tables@[p].addr() == p
        &&&
        forall|p: PageMapPtr|
            #![trigger self.l2_tables@[p].is_init()] 
            self.l2_tables@.dom().contains(p) ==> self.l2_tables@[p].is_init()
        &&&
        forall|p: PageMapPtr|
            #![trigger self.l2_tables@[p].value().wf()] 
            self.l2_tables@.dom().contains(p) ==> self.l2_tables@[p].value().wf()
        // all l2 tables exist in l3 mapping
        &&&
        forall|p: PageMapPtr|
            #![trigger self.l2_rev_map@[p]]
            #![trigger self.l2_rev_map@.dom().contains(p)]
            self.l2_tables@.dom().contains(p) ==>
                self.l2_rev_map@.dom().contains(p) && 
                0 <= self.l2_rev_map@[p].0 < 512 && 0 <= self.l2_rev_map@[p].1 < 512 &&
                self.spec_resolve_mapping_l3(self.l2_rev_map@[p].0,self.l2_rev_map@[p].1).is_Some() && self.spec_resolve_mapping_l3(self.l2_rev_map@[p].0,self.l2_rev_map@[p].1).get_Some_0().addr == p
        // L2 mappings are unique within
        &&&
        forall|p: PageMapPtr, l2i: L2Index, l2j: L2Index| 
            #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[l2i].perm.present, self.l2_tables@[p].value()[l2j].perm.present, self.l2_tables@[p].value()[l2i].perm.ps, self.l2_tables@[p].value()[l2j].perm.ps]
            self.l2_tables@.dom().contains(p) && l2i != l2j && 0 <= l2i < 512 && 0 <= l2j < 512 && self.l2_tables@[p].value()[l2i].perm.present && self.l2_tables@[p].value()[l2j].perm.present && 
            !self.l2_tables@[p].value()[l2i].perm.ps && !self.l2_tables@[p].value()[l2j].perm.ps 
                ==>
                self.l2_tables@[p].value()[l2i].addr != self.l2_tables@[p].value()[l2j].addr
        // L2 mappings are unique
        &&&
        forall|pi: PageMapPtr, pj: PageMapPtr, l2i: L2Index, l2j: L2Index|
            #![trigger self.l2_tables@.dom().contains(pi), self.l2_tables@.dom().contains(pj),
                self.l2_tables@[pi].value()[l2i].perm.present, self.l2_tables@[pj].value()[l2j].perm.present,
                self.l2_tables@[pi].value()[l2i].perm.ps, self.l2_tables@[pj].value()[l2j].perm.ps]
            pi != pj && self.l2_tables@.dom().contains(pi) && self.l2_tables@.dom().contains(pj) && 0 <= l2i < 512 && 0 <= l2j < 512 && self.l2_tables@[pi].value()[l2i].perm.present && self.l2_tables@[pj].value()[l2j].perm.present && 
            !self.l2_tables@[pi].value()[l2i].perm.ps && !self.l2_tables@[pj].value()[l2j].perm.ps
                ==>
                self.l2_tables@[pi].value()[l2i].addr != self.l2_tables@[pj].value()[l2j].addr
        // L2 does not map to L4, L3, or self
        &&&
        forall|p: PageMapPtr, i: L2Index| 
            #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[i].perm.present, self.l2_tables@.dom().contains(self.l2_tables@[p].value()[i].addr)] 
            #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l2_tables@[p].value()[i].addr)] 
            #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[i].perm.present, self.l2_tables@[p].value()[i].addr] 
            self.l2_tables@.dom().contains(p) && 0 <= i < 512 && self.l2_tables@[p].value()[i].perm.present ==>
                self.l2_tables@.dom().contains(self.l2_tables@[p].value()[i].addr) == false
                &&
                self.l3_tables@.dom().contains(self.l2_tables@[p].value()[i].addr) == false
                &&
                self.cr3 != self.l2_tables@[p].value()[i].addr
        // all l2 points to valid l1 tables
        &&&
        forall|p: PageMapPtr, i: L2Index| 
            #![trigger self.l1_tables@.dom().contains(self.l2_tables@[p].value()[i].addr), self.l2_tables@[p].value()[i].perm.present, self.l2_tables@[p].value()[i].perm.ps] 
            self.l2_tables@.dom().contains(p) && 0 <= i < 512 && self.l2_tables@[p].value()[i].perm.present && !self.l2_tables@[p].value()[i].perm.ps ==>
                self.l1_tables@.dom().contains(self.l2_tables@[p].value()[i].addr)
    }

    pub open spec fn wf_l1(&self) -> bool{
        // &&&
        // self.l1_tables@.dom().contains(0) == false
        &&&
        forall|p: PageMapPtr| 
            #![trigger self.l1_tables@[p].addr()] 
            self.l1_tables@.dom().contains(p) ==> self.l1_tables@[p].addr() == p
        &&&
        forall|p: PageMapPtr| 
            #![trigger self.l1_tables@[p].is_init()] 
            self.l1_tables@.dom().contains(p) ==> self.l1_tables@[p].is_init()
        &&&
        forall|p: PageMapPtr| 
            #![trigger self.l1_tables@[p].value().wf()] 
            self.l1_tables@.dom().contains(p) ==> self.l1_tables@[p].value().wf()
        // all l1 tables exist in l2 mapping
        &&&
        forall|p: PageMapPtr|
            #![trigger self.l1_rev_map@.dom().contains(p)]
            #![trigger self.l1_rev_map@[p]]
            self.l1_tables@.dom().contains(p) ==>
                self.l1_rev_map@.dom().contains(p) && 
                0<=self.l1_rev_map@[p].0<512 && 0<=self.l1_rev_map@[p].1<512 && 0<=self.l1_rev_map@[p].2<512 &&
                self.spec_resolve_mapping_l2(self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2).is_Some() && self.spec_resolve_mapping_l2(self.l1_rev_map@[p].0,self.l1_rev_map@[p].1,self.l1_rev_map@[p].2).get_Some_0().addr == p
        // no l1 tables map to other levels
        &&&
        forall|p: PageMapPtr, i: L1Index| 
            #![trigger self.l1_tables@.dom().contains(p), self.l1_tables@[p].value()[i].perm.present, self.l2_tables@.dom().contains(self.l1_tables@[p].value()[i].addr)] 
            #![trigger self.l1_tables@.dom().contains(p), self.l1_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l1_tables@[p].value()[i].addr)] 
            #![trigger self.l1_tables@.dom().contains(p), self.l1_tables@[p].value()[i].perm.present, self.l1_tables@[p].value()[i].addr] 
            self.l1_tables@.dom().contains(p) && 0 <= i < 512 && self.l1_tables@[p].value()[i].perm.present ==>
                self.l2_tables@.dom().contains(self.l1_tables@[p].value()[i].addr) == false
                &&
                self.l3_tables@.dom().contains(self.l1_tables@[p].value()[i].addr) == false
                &&
                self.cr3 != self.l1_tables@[p].value()[i].addr
        // no hugepage in l1
        &&&
        forall|p: PageMapPtr, i: L1Index| 
            #![trigger self.l1_tables@[p].value()[i].perm.ps] 
            self.l1_tables@.dom().contains(p) && 0 <= i < 512 && self.l1_tables@[p].value()[i].perm.present ==>
                ! self.l1_tables@[p].value()[i].perm.ps
    }

    pub open spec fn user_only(&self) -> bool{
        &&&
        forall|i: L4Index| 
            #![trigger self.l4_table@[self.cr3].value()[i].perm.user]
            0 <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present ==> 
                self.l4_table@[self.cr3].value()[i].perm.user
        &&&
        forall|p: PageMapPtr, i: L3Index| 
            #![trigger self.l3_tables@[p].value()[i].perm.user] 
            self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.present ==>
                self.l3_tables@[p].value()[i].perm.user
        &&&
        forall|p: PageMapPtr, i: L2Index| 
            #![trigger self.l2_tables@[p].value()[i].perm.user] 
            self.l2_tables@.dom().contains(p) && 0 <= i < 512 && self.l2_tables@[p].value()[i].perm.present ==>
                self.l2_tables@[p].value()[i].perm.user
        &&&
        forall|p: PageMapPtr, i: L1Index| 
            #![trigger self.l1_tables@[p].value()[i].perm.user] 
            self.l1_tables@.dom().contains(p) && 0 <= i < 512 && self.l1_tables@[p].value()[i].perm.present ==>
                self.l1_tables@[p].value()[i].perm.user
    }

    pub open spec fn present_or_zero(&self) -> bool{
        &&&
        forall|i: L4Index| 
            #![trigger self.l4_table@[self.cr3].value()[i].is_empty()]
            0 <= i < 512 && !self.l4_table@[self.cr3].value()[i].perm.present ==> 
                self.l4_table@[self.cr3].value()[i].is_empty()
        &&&
        forall|p: PageMapPtr, i: L3Index| 
            #![trigger self.l3_tables@[p].value()[i].is_empty()] 
            self.l3_tables@.dom().contains(p) && 0 <= i < 512 && !self.l3_tables@[p].value()[i].perm.present ==>
                self.l3_tables@[p].value()[i].is_empty()
        &&&
        forall|p: PageMapPtr, i: L2Index| 
            #![trigger self.l2_tables@[p].value()[i].is_empty()] 
            self.l2_tables@.dom().contains(p) && 0 <= i < 512 && !self.l2_tables@[p].value()[i].perm.present ==>
                self.l2_tables@[p].value()[i].is_empty()
        &&&
        forall|p: PageMapPtr, i: L1Index| 
            #![trigger self.l1_tables@[p].value()[i].is_empty()] 
            self.l1_tables@.dom().contains(p) && 0 <= i < 512 && !self.l1_tables@[p].value()[i].perm.present ==>
                self.l1_tables@[p].value()[i].is_empty()
    }

    pub open spec fn rwx_upper_level_entries(&self) -> bool{
        &&&
        forall|i: L4Index| 
            #![trigger self.l4_table@[self.cr3].value()[i].perm.write] 
            #![trigger self.l4_table@[self.cr3].value()[i].perm.execute_disable]
            0 <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present ==> 
                self.l4_table@[self.cr3].value()[i].perm.write && !self.l4_table@[self.cr3].value()[i].perm.execute_disable
        &&&
        forall|p: PageMapPtr, i: L3Index| 
            #![trigger self.l3_tables@[p].value()[i].perm.write] 
            #![trigger self.l3_tables@[p].value()[i].perm.execute_disable] 
            self.l3_tables@.dom().contains(p) && 0 <= i < 512 && self.l3_tables@[p].value()[i].perm.present && !self.l3_tables@[p].value()[i].perm.ps ==>
                self.l3_tables@[p].value()[i].perm.write && !self.l3_tables@[p].value()[i].perm.execute_disable
        &&&
        forall|p: PageMapPtr, i: L2Index| 
            #![trigger  self.l2_tables@[p].value()[i].perm.write] 
            #![trigger self.l2_tables@[p].value()[i].perm.execute_disable] 
            self.l2_tables@.dom().contains(p) && 0 <= i < 512 && self.l2_tables@[p].value()[i].perm.present && !self.l2_tables@[p].value()[i].perm.ps ==>
                self.l2_tables@[p].value()[i].perm.write && !self.l2_tables@[p].value()[i].perm.execute_disable
    }

    pub open spec fn table_pages_wf(&self) -> bool{
        &&&
        page_ptr_valid(self.cr3)
        &&&
        forall|p: PageMapPtr| 
            #![trigger self.l3_tables@.dom().contains(p), page_ptr_valid(p)]
            self.l3_tables@.dom().contains(p) ==> 
                page_ptr_valid(p)
        &&&
        forall|p: PageMapPtr| 
            #![trigger self.l2_tables@.dom().contains(p), page_ptr_valid(p)]
            self.l2_tables@.dom().contains(p) ==> 
                page_ptr_valid(p)
        &&&
        forall|p: PageMapPtr| 
            #![trigger self.l1_tables@.dom().contains(p), page_ptr_valid(p)]
            self.l1_tables@.dom().contains(p) ==> 
                page_ptr_valid(p)
    }

    pub open spec fn no_self_mapping(&self)-> bool{
        &&&
        forall|va: VAddr| 
        #![trigger self.mapping_1g@.dom().contains(va), self.page_closure().contains(self.mapping_1g@[va].addr)]
            self.mapping_1g@.dom().contains(va) ==> 
                self.page_closure().contains(self.mapping_1g@[va].addr) == false
        &&&
        forall|va: VAddr| 
        #![trigger self.mapping_2m@.dom().contains(va), self.page_closure().contains(self.mapping_2m@[va].addr)]
            self.mapping_2m@.dom().contains(va) ==> 
                self.page_closure().contains(self.mapping_2m@[va].addr) == false
        &&&
        forall|va: VAddr| 
        #![trigger self.mapping_4k@.dom().contains(va), self.page_closure().contains(self.mapping_4k@[va].addr)]
            self.mapping_4k@.dom().contains(va) ==> 
                self.page_closure().contains(self.mapping_4k@[va].addr) == false
    }

    // #[verifier(inline)]
    pub open spec fn spec_resolve_mapping_l4(&self, l4i: L4Index) -> Option<PageEntry>
        recommends
            0 <= l4i < 512,
    {
        if self.l4_table@[self.cr3].value()[l4i].perm.present{
            Some(self.l4_table@[self.cr3].value()[l4i])
        }else{
            None
        }
    }

    pub open spec fn spec_resolve_mapping_1g_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<PageEntry>
    recommends
        0<= l4i < 512,
        0<= l3i < 512,
    {
        if self.spec_resolve_mapping_l4(l4i).is_None() {
            None
        }else if !self.l3_tables@[self.spec_resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i].perm.present || !self.l3_tables@[self.spec_resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i].perm.ps {
            None
        }else{
            Some(self.l3_tables@[self.spec_resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i])
        }
    }

    pub open spec fn spec_resolve_mapping_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<PageEntry>
        recommends
            0<= l4i < 512,
            0<= l3i < 512,
    {
        if self.spec_resolve_mapping_l4(l4i).is_None() {
            None
        }else if !self.l3_tables@[self.spec_resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i].perm.present || self.l3_tables@[self.spec_resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i].perm.ps {
            None
        }else{
            Some(self.l3_tables@[self.spec_resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i])
        }
    }
    
    pub open spec fn spec_resolve_mapping_2m_l2(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> Option<PageEntry>
        recommends
            0<= l4i < 512,
            0<= l3i < 512,
            0<= l2i < 512,
    {
        if self.spec_resolve_mapping_l3(l4i,l3i).is_None() {
            None
        }else if !self.l2_tables@[self.spec_resolve_mapping_l3(l4i,l3i).get_Some_0().addr].value()[l2i].perm.present || !self.l2_tables@[self.spec_resolve_mapping_l3(l4i,l3i).get_Some_0().addr].value()[l2i].perm.ps {
            None
        }else{
            Some(self.l2_tables@[self.spec_resolve_mapping_l3(l4i,l3i).get_Some_0().addr].value()[l2i])
        }
    }
    pub open spec fn spec_resolve_mapping_l2(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> Option<PageEntry>
    recommends
        0<= l4i < 512,
        0<= l3i < 512,
        0<= l2i < 512,
    {
        if self.spec_resolve_mapping_l3(l4i,l3i).is_None() {
            None
        }else if !self.l2_tables@[self.spec_resolve_mapping_l3(l4i,l3i).get_Some_0().addr].value()[l2i].perm.present || self.l2_tables@[self.spec_resolve_mapping_l3(l4i,l3i).get_Some_0().addr].value()[l2i].perm.ps {
            None
        }else{
            Some(self.l2_tables@[self.spec_resolve_mapping_l3(l4i,l3i).get_Some_0().addr].value()[l2i])
        }
    }

    pub open spec fn spec_resolve_mapping_4k_l1(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index) -> Option<PageEntry>
    recommends
        0<= l4i < 512,
        0<= l3i < 512,
        0<= l2i < 512,
        0<= l1i < 512,
    {
        if self.spec_resolve_mapping_l2(l4i,l3i,l2i).is_None() {
            None
        }else if !self.l1_tables@[self.spec_resolve_mapping_l2(l4i,l3i,l2i).get_Some_0().addr].value()[l1i].perm.present {
            None
        }else{
            Some(self.l1_tables@[self.spec_resolve_mapping_l2(l4i,l3i,l2i).get_Some_0().addr].value()[l1i])
        }

    }

    pub open spec fn wf_mapping_4k(&self) -> bool{
        &&&
        forall|va: VAddr| 
            #![trigger va_4k_valid(va), self.mapping_4k@.dom().contains(va)]
                self.mapping_4k@.dom().contains(va) ==> va_4k_valid(va)
        &&&
        forall|l4i: L4Index,l3i: L3Index,l2i: L2Index,l1i: L2Index| 
            #![trigger self.mapping_4k@[spec_index2va((l4i,l3i,l2i,l1i))]]
            #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
            0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 ==>
                self.mapping_4k@.dom().contains(spec_index2va((l4i,l3i,l2i,l1i))) == self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i).is_Some()
        &&&
        forall|l4i: L4Index,l3i: L3Index,l2i: L2Index,l1i: L2Index| 
            #![trigger self.mapping_4k@[spec_index2va((l4i,l3i,l2i,l1i))]]
            0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 && self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i).is_Some()
                ==> self.mapping_4k@[spec_index2va((l4i,l3i,l2i,l1i))].addr == self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i).get_Some_0().addr &&
                    self.mapping_4k@[spec_index2va((l4i,l3i,l2i,l1i))].write == self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i).get_Some_0().perm.write &&
                    self.mapping_4k@[spec_index2va((l4i,l3i,l2i,l1i))].execute_disable == self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i).get_Some_0().perm.execute_disable
        &&&
        forall|va: VAddr| 
            #![trigger self.mapping_4k@.dom().contains(va), page_ptr_valid(self.mapping_4k@[va].addr)]
                self.mapping_4k@.dom().contains(va) ==>
                page_ptr_valid(self.mapping_4k@[va].addr)
    }

    pub open spec fn wf_mapping_2m(&self) -> bool{
        &&&
        forall|va: VAddr| 
            #![trigger va_2m_valid(va), self.mapping_2m@.dom().contains(va)]
                self.mapping_2m@.dom().contains(va) ==> va_2m_valid(va)
        &&&
        forall|l4i: L4Index,l3i: L3Index,l2i: L2Index| 
            #![trigger self.mapping_2m@[spec_index2va((l4i,l3i,l2i,0))]]
            #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
            0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 ==>
                self.mapping_2m@.dom().contains(spec_index2va((l4i,l3i,l2i,0))) == self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i).is_Some()
        &&&
        forall|l4i: L4Index,l3i: L3Index,l2i: L2Index| 
            #![trigger self.mapping_2m@[spec_index2va((l4i,l3i,l2i,0))]]
            0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i).is_Some()
                ==> self.mapping_2m@[spec_index2va((l4i,l3i,l2i,0))].addr == self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i).get_Some_0().addr &&
                    self.mapping_2m@[spec_index2va((l4i,l3i,l2i,0))].write == self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i).get_Some_0().perm.write &&
                    self.mapping_2m@[spec_index2va((l4i,l3i,l2i,0))].execute_disable == self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i).get_Some_0().perm.execute_disable
        &&&
        forall|va: VAddr| 
            #![trigger self.mapping_2m@.dom().contains(va), page_ptr_2m_valid(self.mapping_2m@[va].addr)]
                self.mapping_2m@.dom().contains(va) ==>
                page_ptr_2m_valid(self.mapping_2m@[va].addr)
    }

    pub open spec fn wf_mapping_1g(&self) -> bool{
        &&&
        forall|va: VAddr| 
            #![trigger va_1g_valid(va), self.mapping_1g@.dom().contains(va)]
                self.mapping_1g@.dom().contains(va) ==> va_1g_valid(va)
        &&&
        forall|l4i: L4Index,l3i: L3Index| 
            #![trigger self.mapping_1g@[spec_index2va((l4i,l3i,0,0))]]
            #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
            0 <= l4i < 512 && 0 <= l3i < 512 ==>
                self.mapping_1g@.dom().contains(spec_index2va((l4i,l3i,0,0))) == self.spec_resolve_mapping_1g_l3(l4i,l3i).is_Some()
        &&&
        forall|l4i: L4Index,l3i: L3Index| 
            #![trigger self.mapping_1g@[spec_index2va((l4i,l3i,0,0))]]
            #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
            0 <= l4i < 512 && 0 <= l3i < 512 && self.spec_resolve_mapping_1g_l3(l4i,l3i).is_Some()
                ==> self.mapping_1g@[spec_index2va((l4i,l3i,0,0))].addr == self.spec_resolve_mapping_1g_l3(l4i,l3i).get_Some_0().addr &&
                    self.mapping_1g@[spec_index2va((l4i,l3i,0,0))].write == self.spec_resolve_mapping_1g_l3(l4i,l3i).get_Some_0().perm.write &&
                    self.mapping_1g@[spec_index2va((l4i,l3i,0,0))].execute_disable == self.spec_resolve_mapping_1g_l3(l4i,l3i).get_Some_0().perm.execute_disable
        &&&
        forall|va: VAddr| 
            #![trigger self.mapping_1g@.dom().contains(va), page_ptr_1g_valid(self.mapping_1g@[va].addr)]
                self.mapping_1g@.dom().contains(va) ==>
                page_ptr_1g_valid(self.mapping_1g@[va].addr)
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
        &&&
        self.user_only()
        &&&
        self.rwx_upper_level_entries()
        &&&
        self.present_or_zero()
        // &&&
        // self.no_self_mapping()
        &&&
        self.table_pages_wf()
    }

    // pub open spec fn l4_kernel_entries_reserved(&self) -> bool
    //     recommends self.wf_l4(),
    // {
    //     forall|l4i: L4Index| #![auto] 0<=l4i<KERNEL_MEM_END_L4INDEX ==> self.l4_table@[self.cr3]@.value.get_Some_0()[l4i].is_None()
    // }


    pub open spec fn l4_entry_exists(&self, l4i: L4Index) -> bool
        recommends self.wf(),
    {
        self.spec_resolve_mapping_l4(l4i).is_Some()
    }

    pub open spec fn l3_2m_entry_exists(&self, l4i: L4Index, l3i :L3Index) -> bool
        recommends self.wf(),
                    self.l4_entry_exists(l4i)
    {
        self.spec_resolve_mapping_l3(l4i,l3i).is_Some()
    }

    pub open spec fn l3_4k_entry_exists(&self, l4i: L4Index, l3i :L3Index) -> bool
        recommends self.wf(),
                    self.l4_entry_exists(l4i)
    {
        self.spec_resolve_mapping_l3(l4i,l3i).is_Some()
    }

    pub open spec fn l2_4k_entry_exists(&self, l4i: L4Index, l3i :L3Index, l2i :L2Index) -> bool
        recommends self.wf(),
                    self.l3_4k_entry_exists(l4i,l3i)
    {
        self.spec_resolve_mapping_l2(l4i,l3i,l2i).is_Some()
    }

}

}
