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

    pub l4_table: Tracked<PointsTo<PageMap>>,
    pub l3_tables: Tracked<Map<L4Index,PointsTo<PageMap>>>,
    pub l2_tables: Tracked<Map<(L4Index,L3Index),PointsTo<PageMap>>>,
    pub l1_tables: Tracked<Map<(L4Index,L3Index,L2Index),PointsTo<PageMap>>>,

    pub mapping_4k: Ghost<Map<VAddr,MapEntry>>,
    pub mapping_2m: Ghost<Map<VAddr,MapEntry>>,
    pub mapping_1g: Ghost<Map<VAddr,MapEntry>>,
}


impl PageTable{
    pub open spec fn wf_l4(&self) -> bool{
        // &&&
        // self.cr3 != 0
        &&&
        self.cr3 == self.l4_table.addr()
        &&&
        self.l4_table.is_init()
        &&&
        self.l4_table.value().wf()
        //L4 table only maps to L3
        &&&
        forall|i: L4Index, j: L4Index|
            #![trigger self.l4_table.value()[i].perm.present, self.l4_table.value()[j].perm.present, self.l4_table.value()[i].addr, self.l4_table.value()[j].addr]
            i != j && 0 <= i < 512 && self.l4_table.value()[i].perm.present && 0 <= j < 512 && self.l4_table.value()[j].perm.present ==>
                self.l4_table.value()[i].addr != self.l4_table.value()[j].addr
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
}

}
