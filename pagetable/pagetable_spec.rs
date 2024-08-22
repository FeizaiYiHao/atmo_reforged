use vstd::prelude::*;

pub const KERNEL_PML4_SIG: Option<PageEntry> = None; // hack @Xiangdong

verus! {
// use vstd::ptr::PointsTo;
use crate::define::*;
use crate::mars_array::*;
// use crate::page_alloc::*;
use vstd::ptr::PointsTo;

use crate::pagetable::*;


pub struct LookUpTable{
    pub table : MarsArray<PAddr,512>,
}
pub struct PageTable{
    pub cr3: PAddr,

    pub l4_table: Tracked<Map<PAddr,PointsTo<PageMap>>>,
    pub l3_tables: Tracked<Map<PAddr,PointsTo<PageMap>>>,
    pub l2_tables: Tracked<Map<PAddr,PointsTo<PageMap>>>,
    pub l1_tables: Tracked<Map<PAddr,PointsTo<PageMap>>>,

    pub mapping: Ghost<Map<VAddr,Option<PageEntry>>>,
}


impl PageTable{

    pub fn new(cr3:usize) -> (ret:Self)
    {
        Self{
            cr3 : cr3,
            l4_table: Tracked(Map::tracked_empty()),
            l3_tables: Tracked(Map::tracked_empty()),
            l2_tables: Tracked(Map::tracked_empty()),
            l1_tables: Tracked(Map::tracked_empty()),
            mapping: Ghost(Map::empty()),
        }
    }

    pub fn init(&mut self)
        requires
            old(self).l4_table@ =~= Map::empty(),
            old(self).l3_tables@ =~= Map::empty(),
            old(self).l2_tables@ =~= Map::empty(),
            old(self).l1_tables@ =~= Map::empty(),
        ensures
            self.wf_mapping(),
            self.get_pagetable_page_closure() =~= Set::empty(),
            self.l4_table@ =~= Map::empty(),
            self.l3_tables@ =~= Map::empty(),
            self.l2_tables@ =~= Map::empty(),
            self.l1_tables@ =~= Map::empty(),
            forall|va:VAddr|#![auto] spec_va_valid(va) ==> self.mapping@.dom().contains(va),
            forall|va:VAddr|#![auto] spec_va_valid(va) ==> self.mapping@[va].is_None(),
        {
            self.cr3 = 0;
            proof{
                pagetable_virtual_mem_lemma();
                self.mapping@ = Map::<VAddr,Option<PageEntry>>::new(
                    |va: VAddr| { spec_va_valid(va)
                    },
                    |va: VAddr| {
                        None
                    }
                );
            }
        }

    #[verifier(inline)]
    pub open spec fn get_pagetable_page_closure(&self) -> Set<PagePtr>{
            self.l3_tables@.dom() + self.l2_tables@.dom() + self.l1_tables@.dom() + self.l4_table@.dom()
    }

    #[verifier(inline)]
    pub open spec fn get_pagetable_mapping(&self) -> Map<VAddr,Option<PageEntry>> {
        self.mapping@
    }

    // #[verifier(inline)]
    pub open spec fn get_pagetable_mapped_pages(&self) -> Set<PagePtr>{
        Set::<PagePtr>::new(|pa: PagePtr| self.is_pa_mapped(pa))
    }

    // #[verifier(inline)]
    pub open spec fn is_pa_mapped(&self, pa:PAddr) -> bool
    {
        exists|va:VAddr| #![auto] spec_va_valid(va) && self.get_pagetable_mapping()[va].is_Some() && self.get_pagetable_mapping()[va].get_Some_0().addr == pa
    }

    pub open spec fn wf_l4(&self) -> bool{
        self.cr3 != 0
        &&
        self.l4_table@.dom() =~=  Set::<PAddr>::empty().insert(self.cr3)
        &&
        self.cr3 == self.l4_table@[self.cr3]@.pptr
        &&
        self.l4_table@[self.cr3]@.value.is_Some()
        &&
        self.l4_table@[self.cr3]@.value.get_Some_0().wf()
        //L4 table only maps to L3
        &&
        (forall|i: L4Index, j: L4Index| #![auto] i != j && KERNEL_MEM_END_L4INDEX <= i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0()[i].is_Some() && KERNEL_MEM_END_L4INDEX <= j < 512 && self.l4_table@[self.cr3]@.value.get_Some_0()[j].is_Some() ==>
            self.l4_table@[self.cr3]@.value.get_Some_0()[i].get_Some_0().addr != self.l4_table@[self.cr3]@.value.get_Some_0()[j].get_Some_0().addr)
        &&
        (forall|i: L4Index| #![auto] KERNEL_MEM_END_L4INDEX <= i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0()[i].is_Some() ==> self.l2_tables@.dom().contains(self.l4_table@[self.cr3]@.value.get_Some_0()[i].get_Some_0().addr) == false)
        &&
        (forall|i: L4Index| #![auto] KERNEL_MEM_END_L4INDEX <= i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0()[i].is_Some() ==> self.l1_tables@.dom().contains(self.l4_table@[self.cr3]@.value.get_Some_0()[i].get_Some_0().addr) == false)
        &&
        (forall|i: L4Index| #![auto] KERNEL_MEM_END_L4INDEX <= i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0()[i].is_Some()  ==> self.cr3 != self.l4_table@[self.cr3]@.value.get_Some_0()[i].get_Some_0().addr)
        //hack @Xiangdong We are just to trying to make sure that the kernel PML4Entry is never changed
        &&
        (forall|i: L4Index| #![auto] 0 <= i < KERNEL_MEM_END_L4INDEX ==> self.l4_table@[self.cr3]@.value.get_Some_0()[i].is_None())
    }

    pub open spec fn wf_l3(&self) -> bool{
        //all l4 mappings exist in l3
        (
            forall|i: L4Index| #![auto] KERNEL_MEM_END_L4INDEX <= i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0()[i].is_Some() ==>
                self.l3_tables@.dom().contains(self.l4_table@[self.cr3]@.value.get_Some_0()[i].get_Some_0().addr)
        )
        &&
        (
            self.l3_tables@.dom().contains(0) == false
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i) ==> self.l3_tables@[i]@.pptr == i
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i) ==> self.l3_tables@[i]@.value.is_Some()
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i) ==> self.l3_tables@[i]@.value.get_Some_0().wf()
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i) ==>
                (
                exists|l4i:L4Index| #![auto] KERNEL_MEM_END_L4INDEX <= l4i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0()[l4i].is_Some() &&
                self.l4_table@[self.cr3]@.value.get_Some_0()[l4i].get_Some_0().addr == i
                )
        )

        //L3 table only maps to L2
        //L3 tables are disjoint
        &&
        (
            forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i)
                ==>
                (
                    forall|l3i: L3Index, l3j: L3Index| #![auto] l3i != l3j && 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[i]@.value.get_Some_0()[l3i].is_Some() && self.l3_tables@[i]@.value.get_Some_0()[l3j].is_Some() ==>
                        self.l3_tables@[i]@.value.get_Some_0()[l3i].get_Some_0().addr != self.l3_tables@[i]@.value.get_Some_0()[l3j].get_Some_0().addr
                )
        )
        &&
        (
            forall|i: PAddr,j: PAddr| #![auto] i != j && self.l3_tables@.dom().contains(i) && self.l3_tables@.dom().contains(j)
                ==>
                (
                    forall|l3i: L3Index, l3j: L3Index| #![auto] 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[i]@.value.get_Some_0()[l3i].is_Some() && self.l3_tables@[j]@.value.get_Some_0()[l3j].is_Some() ==>
                        self.l3_tables@[i]@.value.get_Some_0()[l3i].get_Some_0().addr != self.l3_tables@[j]@.value.get_Some_0()[l3j].get_Some_0().addr
                )
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i) ==>
                forall|j: L3Index| #![auto] 0 <= j < 512 && self.l3_tables@[i]@.value.get_Some_0()[j].is_Some() ==>
                    self.l3_tables@.dom().contains(self.l3_tables@[i]@.value.get_Some_0()[j].get_Some_0().addr) == false
        )
        &&
        (   forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i) ==>
                forall|j: L3Index| #![auto] 0 <= j < 512 && self.l3_tables@[i]@.value.get_Some_0()[j].is_Some() ==>
                    self.l1_tables@.dom().contains(self.l3_tables@[i]@.value.get_Some_0()[j].get_Some_0().addr) == false
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i) ==>
                forall|j: L3Index| #![auto] 0 <= j < 512 && self.l3_tables@[i]@.value.get_Some_0()[j].is_Some() ==>
                    self.cr3 != self.l3_tables@[i]@.value.get_Some_0()[j].get_Some_0().addr
        )
    }

    pub open spec fn wf_l2(&self) -> bool{
      //all l3 mappings exist in l2
        (
            forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i) ==> (
                forall|j: L3Index| #![auto] 0<= j < 512 && self.l3_tables@[i]@.value.get_Some_0()[j].is_Some() ==>
                     self.l2_tables@.dom().contains(self.l3_tables@[i]@.value.get_Some_0()[j].get_Some_0().addr)
            )
        )
        &&
        (
            self.l2_tables@.dom().contains(0) == false
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l2_tables@.dom().contains(i) ==> self.l2_tables@[i]@.pptr == i
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l2_tables@.dom().contains(i) ==> self.l2_tables@[i]@.value.is_Some()
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l2_tables@.dom().contains(i) ==> self.l2_tables@[i]@.value.get_Some_0().wf()
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l2_tables@.dom().contains(i) ==>
                (
                    exists|j:PAddr,l3i:L3Index| #![auto] 0<=l3i<512 && self.l3_tables@.dom().contains(j) && self.l3_tables@[j]@.value.get_Some_0()[l3i].is_Some()
                        && self.l3_tables@[j]@.value.get_Some_0()[l3i].get_Some_0().addr == i
                )
        )



        //L2 table only maps to L1
        //L2 tables are disjoint
        &&
        (
            forall|i: PAddr| #![auto] self.l2_tables@.dom().contains(i) ==>
            (
                forall|l2i: L2Index, l2j: L2Index| #![auto] l2i != l2j && 0 <= l2i < 512 && 0 <= l2j < 512 && self.l2_tables@[i]@.value.get_Some_0()[l2i].is_Some() && self.l2_tables@[i]@.value.get_Some_0()[l2j].is_Some() ==>
                    self.l2_tables@[i]@.value.get_Some_0()[l2i].get_Some_0().addr != self.l2_tables@[i]@.value.get_Some_0()[l2j].get_Some_0().addr
            )
        )
        &&
        (
            forall|i: PAddr,j: PAddr| #![auto] i != j && self.l2_tables@.dom().contains(i) && self.l2_tables@.dom().contains(j) ==>
            (
                forall|l2i: L2Index, l2j: L2Index| #![auto] 0 <= l2i < 512 && 0 <= l2j < 512 && self.l2_tables@[i]@.value.get_Some_0()[l2i].is_Some() && self.l2_tables@[j]@.value.get_Some_0()[l2j].is_Some() ==>
                    self.l2_tables@[i]@.value.get_Some_0()[l2i].get_Some_0().addr != self.l2_tables@[j]@.value.get_Some_0()[l2j].get_Some_0().addr
            )
        )
        &&
        (forall|i: PAddr| #![auto] self.l2_tables@.dom().contains(i) ==>
            forall|j: L2Index| #![auto]  0 <= j < 512 && self.l2_tables@[i]@.value.get_Some_0()[j].is_Some() ==>
                self.l2_tables@.dom().contains(self.l2_tables@[i]@.value.get_Some_0()[j].get_Some_0().addr) == false
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l2_tables@.dom().contains(i) ==>
                forall|j: L2Index| #![auto] 0 <= j < 512 && self.l2_tables@[i]@.value.get_Some_0()[j].is_Some() ==>
                    self.l3_tables@.dom().contains(self.l2_tables@[i]@.value.get_Some_0()[j].get_Some_0().addr) == false
        )
        &&
        (
            forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==>
                forall|j: L2Index| #![auto] 0 <= j < 512 && self.l2_tables@[i]@.value.get_Some_0()[j].is_Some() ==>
                    self.cr3 != self.l2_tables@[i]@.value.get_Some_0()[j].get_Some_0().addr
        )
    }

    pub open spec fn wf_l1(&self) -> bool{
        //all l2 mappings exist in l1
        (
            forall|i: PAddr| #![auto] self.l2_tables@.dom().contains(i) ==> (
                forall|j: L2Index| #![auto] 0<= j < 512 && self.l2_tables@[i]@.value.get_Some_0()[j].is_Some() ==>
                     self.l1_tables@.dom().contains(self.l2_tables@[i]@.value.get_Some_0()[j].get_Some_0().addr)
            )
        )
        &&
        (
            self.l1_tables@.dom().contains(0) == false
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l1_tables@.dom().contains(i) ==> self.l1_tables@[i]@.pptr == i
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l1_tables@.dom().contains(i) ==> self.l1_tables@[i]@.value.is_Some()
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l1_tables@.dom().contains(i) ==> self.l1_tables@[i]@.value.get_Some_0().wf()
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l1_tables@.dom().contains(i) ==>
                (
                    exists|j:PAddr,l2i:L2Index| #![auto] 0<=l2i<512 && self.l2_tables@.dom().contains(j) && self.l2_tables@[j]@.value.get_Some_0()[l2i].is_Some()
                        && self.l2_tables@[j]@.value.get_Some_0()[l2i].get_Some_0().addr == i
                )
        )
    }

    pub open spec fn no_self_mapping(&self) -> bool
    {
        //L1 table only maps to outside of this pagetable
        //L1 tables do not have to be disjoint
        (
            forall|va: VAddr| #![auto] spec_va_valid(va) && self.mapping@[va].is_Some() ==>
                    self.l3_tables@.dom().contains(self.mapping@[va].get_Some_0().addr) == false
        )
        &&
        (
            forall|va: VAddr| #![auto] spec_va_valid(va) && self.mapping@[va].is_Some() ==>
                    self.l2_tables@.dom().contains(self.mapping@[va].get_Some_0().addr) == false
        )
        &&
        (
            forall|va: VAddr| #![auto] spec_va_valid(va) && self.mapping@[va].is_Some() ==>
                    self.l1_tables@.dom().contains(self.mapping@[va].get_Some_0().addr) == false
        )
        &&
        (
            forall|va: VAddr| #![auto] spec_va_valid(va) && self.mapping@[va].is_Some() ==>
                self.cr3 != self.mapping@[va].get_Some_0().addr
        )
    }

    // #[verifier(inline)]
    pub open spec fn resolve_mapping_l4(&self, l4i: L4Index) -> Option<PageEntry>
        recommends
            KERNEL_MEM_END_L4INDEX <= l4i < 512,
    {
        if self.cr3 == 0{
            None
        }else{
            self.l4_table@[self.cr3]@.value.get_Some_0()[l4i]
        }
    }

    pub open spec fn resolve_mapping_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<PageEntry>
    recommends
        KERNEL_MEM_END_L4INDEX<= l4i < 512,
        0<= l3i < 512,
    {
        if self.resolve_mapping_l4(l4i).is_None() {
            None
        }else{
            self.l3_tables@[self.resolve_mapping_l4(l4i).get_Some_0().addr]@.value.get_Some_0()[l3i]
        }
    }

    pub open spec fn resolve_mapping_l2(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> Option<PageEntry>
    recommends
        KERNEL_MEM_END_L4INDEX<= l4i < 512,
        0<= l3i < 512,
        0<= l2i < 512,
    {
        if self.resolve_mapping_l3(l4i,l3i).is_None() {
            None
        }else{
            self.l2_tables@[self.resolve_mapping_l3(l4i,l3i).get_Some_0().addr]@.value.get_Some_0()[l2i]
        }
    }

    pub open spec fn resolve_mapping_l1(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index) -> Option<PageEntry>
    recommends
        KERNEL_MEM_END_L4INDEX<= l4i < 512,
        0<= l3i < 512,
        0<= l2i < 512,
        0<= l1i < 512,
    {
        if self.resolve_mapping_l2(l4i,l3i,l2i).is_None() {
            None
        }else{
            self.l1_tables@[self.resolve_mapping_l2(l4i,l3i,l2i).get_Some_0().addr]@.value.get_Some_0()[l1i]
        }

    }

    pub proof fn wf_to_wf_mapping(&self)
        requires self.wf_l4(),
                 self.wf_l3(),
                 self.wf_l2(),
        ensures
            self.wf_l4_mapping(),
            self.wf_l3_mapping(),
            self.wf_l2_mapping()
    {
        assert(self.wf_l4_mapping());
        assert(self.wf_l3_mapping());
        assert(self.wf_l2_mapping());
    }


    pub open spec fn wf_l4_mapping(&self) -> bool{
        forall|l4i: L4Index, l4j: L4Index| #![auto] (KERNEL_MEM_END_L4INDEX<= l4i < 512) && (KERNEL_MEM_END_L4INDEX<= l4j < 512) && !(l4i == l4j) ==>
        (self.resolve_mapping_l4(l4i).is_None() || self.resolve_mapping_l4(l4j).is_None() || self.resolve_mapping_l4(l4i).get_Some_0().addr != self.resolve_mapping_l4(l4j).get_Some_0().addr)
    }

    pub open spec fn wf_l3_mapping(&self) -> bool{
        forall|l4i: L4Index, l3i: L3Index, l4j: L4Index,l3j: L3Index| #![auto] (KERNEL_MEM_END_L4INDEX<= l4i < 512 && 0<= l3i < 512)
            && (KERNEL_MEM_END_L4INDEX<= l4j < 512 && 0<= l3j < 512)
            && !(l4i == l4j && l3i == l3j) ==>
                (self.resolve_mapping_l3(l4i,l3i).is_None() || self.resolve_mapping_l3(l4j,l3j).is_None() || self.resolve_mapping_l3(l4i,l3i).get_Some_0().addr != self.resolve_mapping_l3(l4j,l3j).get_Some_0().addr)
    }


    pub open spec fn wf_l2_mapping(&self) -> bool{
        forall|l4i: L4Index,l3i: L3Index,l2i: L2Index,l4j: L4Index,l3j: L3Index,l2j: L2Index| #![auto] (KERNEL_MEM_END_L4INDEX<= l4i < 512 && 0<= l3i < 512 && 0<= l2i < 512)
        && (KERNEL_MEM_END_L4INDEX<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512)
        && !(l4i == l4j && l3i == l3j && l2i == l2j ) ==>
        self.resolve_mapping_l2(l4i,l3i,l2i).is_None() || self.resolve_mapping_l2(l4j,l3j,l2j).is_None() || self.resolve_mapping_l2(l4i,l3i,l2i).get_Some_0().addr != self.resolve_mapping_l2(l4j,l3j,l2j).get_Some_0().addr


    }

    pub open spec fn wf_mapping(&self) -> bool{
        (
            forall|va: VAddr| #![auto] spec_va_valid(va) ==> self.mapping@.dom().contains(va)
        )
        // &&
        // (forall|va: usize| #![auto] spec_va_valid(va) ==> self.mapping@[va] == self.resolve_mapping_l1(spec_v2l4index(va),spec_v2l3index(va),spec_v2l2index(va),spec_v2l1index(va)))
        &&
        (forall|l4i: L4Index,l3i: L3Index,l2i: L2Index, l1i: L1Index| #![auto] (KERNEL_MEM_END_L4INDEX<= l4i < 512 && 0<= l3i < 512 && 0<= l2i < 512 && 0<= l1i < 512)
        ==> self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))] == self.resolve_mapping_l1(l4i,l3i,l2i,l1i))

    }

    pub open spec fn l4_l3_l2_rwx(&self) -> bool {
        &&&
        (
                forall|l4i: L4Index| #![auto] KERNEL_MEM_END_L4INDEX <= l4i< 512 && self.l4_table@[self.cr3]@.value.get_Some_0()[l4i].is_Some() ==>
                    self.l4_table@[self.cr3]@.value.get_Some_0()[l4i].get_Some_0().perm == READ_WRITE_EXECUTE
        )
        &&&
        (
            forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i) ==>
                forall|j: L3Index| #![auto] 0 <= j < 512 && self.l3_tables@[i]@.value.get_Some_0()[j].is_Some() ==>
                    self.l3_tables@[i]@.value.get_Some_0()[j].get_Some_0().perm == READ_WRITE_EXECUTE
        )
        &&&
        (
            forall|i: PAddr| #![auto] self.l2_tables@.dom().contains(i) ==>
                forall|j: L2Index| #![auto] 0 <= j < 512 && self.l2_tables@[i]@.value.get_Some_0()[j].is_Some() ==>
                    self.l2_tables@[i]@.value.get_Some_0()[j].get_Some_0().perm == READ_WRITE_EXECUTE
        )
    }
    pub open spec fn wf(&self) -> bool
    {
        self.wf_l4()
        &&
        self.wf_l3()
        &&
        self.wf_l2()
        &&
        self.wf_l1()
        &&
        self.no_self_mapping()
        &&
        self.wf_mapping()
        &&
        self.l4_kernel_entries_reserved()
        &&
        self.l4_l3_l2_rwx()
    }

    pub open spec fn l4_kernel_entries_reserved(&self) -> bool
        recommends self.wf_l4(),
    {
        forall|l4i: L4Index| #![auto] 0<=l4i<KERNEL_MEM_END_L4INDEX ==> self.l4_table@[self.cr3]@.value.get_Some_0()[l4i].is_None()
    }


    pub open spec fn l4_entry_exists(&self, l4i: L4Index) -> bool
        recommends self.wf(),
    {
        self.l4_table@[self.cr3]@.value.get_Some_0()[l4i].is_Some()
    }

    pub open spec fn l3_entry_exists(&self, l4i: L4Index, l3i :L3Index) -> bool
        recommends self.wf(),
                    self.l4_entry_exists(l4i)
    {
        self.l3_tables@[
            self.l4_table@[self.cr3]@.value.get_Some_0()[l4i].get_Some_0().addr
        ]@.value.get_Some_0()[l3i].is_Some()
    }

    pub open spec fn l2_entry_exists(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> bool
    recommends self.wf(),
                self.l4_entry_exists(l4i),
                self.l3_entry_exists(l4i,l3i)
    {
        self.l2_tables@[
            self.l3_tables@[
                self.l4_table@[self.cr3]@.value.get_Some_0()[l4i].get_Some_0().addr
                    ]@.value.get_Some_0()[l3i].get_Some_0().addr
                ]@.value.get_Some_0()[l2i].is_Some()
    }

    pub open spec fn is_va_entry_exist(&self, va:VAddr) -> bool
        recommends spec_va_valid(va),
    {
        let (l4i,l3i,l2i,_) = spec_va2index(va);

        self.l4_entry_exists(l4i)
        &&
        self.l3_entry_exists(l4i,l3i)
        &&
        self.l2_entry_exists(l4i,l3i,l2i)
    }

    pub proof fn l4_empty_derive(&self)
        requires
            self.wf(),
            forall|i: L4Index| #![auto] KERNEL_MEM_END_L4INDEX <= i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0()[i].is_None()
    {
        assert(self.l3_tables@.dom() =~= Set::empty());
        assert(self.l2_tables@.dom() =~= Set::empty());
        assert(self.l1_tables@.dom() =~= Set::empty());
    }


}

}
