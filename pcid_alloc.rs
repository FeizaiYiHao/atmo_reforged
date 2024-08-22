use vstd::prelude::*;
verus!{
// use vstd::ptr::PointsTo;

use crate::pagetable::*;
use crate::array::Array;
use crate::array_vec::ArrayVec;
use crate::define::*;


pub struct PcidAllocator{
    pub free_page_tables: ArrayVec<Pcid,PCID_MAX>,
    pub page_tables: MarsArray<PageTable,PCID_MAX>,

    pub page_table_pages: Ghost<Set<PagePtr>>,
}


///Pcid Allocator allocates, frees pcid and constructs pagetabels
///Spec: 
///For each free pcid, they have no corresponding pagetable, hence no mapping 
///For each allocated pcid, they have one distinct pagetable
impl PcidAllocator {

    #[verifier(external_body)]
    pub fn new() -> (ret: Self)
        ensures
            ret.free_page_tables.wf(),
            ret.free_page_tables@ =~= Seq::empty(),
            ret.page_tables.wf(),
            ret.page_table_pages@ =~= Set::empty(),
    {
        let ret = Self {
            free_page_tables: ArrayVec::<Pcid,PCID_MAX>::new(),
            page_tables: MarsArray::<PageTable,PCID_MAX>::new(),
            page_table_pages:arbitrary(),
        };

        ret
    }

    // #[verifier(external_body)]
    pub fn init(&mut self, dom0_address_space: &PageTable, kernel_pml4_entry: usize)
        requires
            old(self).free_page_tables.wf(),
            old(self).free_page_tables@ =~= Seq::empty(),
            old(self).page_tables.wf(),
            old(self).page_table_pages@ =~= Set::empty(),
            forall|va:VAddr| #![auto] dom0_address_space.get_pagetable_mapping().dom().contains(va) ==> page_ptr_valid(dom0_address_space.get_pagetable_mapping()[va] as usize),
        ensures
            self.wf(),
            self.free_page_tables.unique(),
            self.free_page_tables.len() == PCID_MAX - 1,
            forall|j:usize| #![auto] 1<=j<PCID_MAX ==> self.free_page_tables@.contains(j),
            forall|j:usize| #![auto] 0<=j<self.free_page_tables.len() ==> self.free_page_tables@[j as int]<PCID_MAX,
            self.free_page_tables.wf(),
            self.page_tables.wf(),
            self.free_page_tables@.contains(0) == false,
            forall|j:usize| #![auto] 1<=j<PCID_MAX ==> self.page_tables[j as int].get_pagetable_page_closure() =~= Set::empty(),
            forall|j:usize| #![auto] 1<=j<PCID_MAX ==> self.page_tables[j as int].get_pagetable_mapping() =~= Map::empty(),
            self.page_tables[0].get_pagetable_page_closure() =~= dom0_address_space.get_pagetable_page_closure(),
            self.page_tables[0].get_pagetable_mapping() =~= dom0_address_space.get_pagetable_mapping(),
            self.page_table_pages@ =~= dom0_address_space.get_pagetable_page_closure(),
    {
        let mut i = 1;
        while i != PCID_MAX
            invariant
                self.free_page_tables.unique(),
                self.free_page_tables.len() == i - 1,
                1 <= i <= PCID_MAX,
                self.free_page_tables@.contains(0) == false,
                forall|j:usize| #![auto] 1<=j<i ==> self.free_page_tables@.contains(j),
                forall|j:usize| #![auto] 0<=j<self.free_page_tables.len() ==> self.free_page_tables@[j as int]<i,
                self.free_page_tables.wf(),
                self.page_tables.wf(),
                self.page_table_pages@ =~= Set::empty(),
            ensures
                self.free_page_tables.unique(),
                self.free_page_tables.len() == PCID_MAX - 1,
                i == PCID_MAX,
                self.free_page_tables@.contains(0) == false,
                forall|j:usize| #![auto] 1<=j<PCID_MAX ==> self.free_page_tables@.contains(j),
                forall|j:usize| #![auto] 0<=j<self.free_page_tables.len() ==> self.free_page_tables@[j as int]<PCID_MAX,
                self.free_page_tables.wf(),
                self.page_tables.wf(),
                self.page_table_pages@ =~= Set::empty(),

        {
            self.free_page_tables.push_unique(i);
            i = i + 1;
        }

        i = 0;
        while i != PCID_MAX
        invariant
            0 <= i <= PCID_MAX,
            self.free_page_tables.unique(),
            self.free_page_tables.len() == PCID_MAX - 1,
            forall|j:usize| #![auto] 1<=j<PCID_MAX ==> self.free_page_tables@.contains(j),
            forall|j:usize| #![auto] 0<=j<self.free_page_tables.len() ==> self.free_page_tables@[j as int]<PCID_MAX,
            self.free_page_tables.wf(),
            self.page_tables.wf(),
            self.free_page_tables@.contains(0) == false,
            self.page_table_pages@ =~= Set::empty(),
            forall|j:usize| #![auto] 0<=j<i ==> self.page_tables[j as int].get_pagetable_page_closure() =~= Set::empty(),
            forall|j:usize| #![auto] 0<=j<i ==> self.page_tables[j as int].get_pagetable_mapping() =~= Map::empty(),
        ensures
            self.free_page_tables.unique(),
            self.free_page_tables.len() == PCID_MAX - 1,
            forall|j:usize| #![auto] 1<=j<PCID_MAX ==> self.free_page_tables@.contains(j),
            forall|j:usize| #![auto] 0<=j<self.free_page_tables.len() ==> self.free_page_tables@[j as int]<PCID_MAX,
            self.free_page_tables.wf(),
            self.page_tables.wf(),
            self.free_page_tables@.contains(0) == false,
            self.page_table_pages@ =~= Set::empty(),
            forall|j:usize| #![auto] 0<=j<PCID_MAX ==> self.page_tables[j as int].get_pagetable_page_closure() =~= Set::empty(),
            forall|j:usize| #![auto] 0<=j<PCID_MAX ==> self.page_tables[j as int].get_pagetable_mapping() =~= Map::empty(),
    {  
        self.page_tables.pcid_init(i, kernel_pml4_entry);
        i = i + 1;
    }

    self.page_tables.pcid_adopt(0, dom0_address_space);
    proof{self.page_table_pages@ = dom0_address_space.get_pagetable_page_closure();}
    assert(self.free_page_tables.wf());
    assert(self.free_page_tables@.no_duplicates());

   assert(self.wf());

    }

    pub closed spec fn wf(&self) -> bool{
        &&&
        self.free_page_tables.wf()
        &&&
        self.free_page_tables@.no_duplicates()
        &&&
        (
            forall|i:int| #![auto] 0<=i<self.free_page_tables.len()  ==> self.free_page_tables@[i]<PCID_MAX
        )
        &&&
        self.page_tables.wf()
        &&&
        (
            forall|i:int| #![auto] 0<=i<self.free_page_tables.len() ==> self.page_tables[self.free_page_tables@[i] as int].get_pagetable_mapping() =~= Map::empty()
        )
        &&&
        (
            forall|i:int,va:VAddr| #![auto] 0<=i<PCID_MAX && self.page_tables[i].get_pagetable_mapping().dom().contains(va) ==> page_ptr_valid(self.page_tables[i].get_pagetable_mapping()[va] as usize)
        )
        &&&
        (
            forall|i:int,page_ptr:PagePtr| #![auto] 0<=i<PCID_MAX && self.page_tables[i].get_pagetable_page_closure().contains(page_ptr) ==> self.page_table_pages@.contains(page_ptr)
        )
        &&&
        (
            forall|i:int,j:int| #![auto] 0<=i<PCID_MAX && 0<=j<PCID_MAX && i != j ==> self.page_tables[i].get_pagetable_page_closure().disjoint(self.page_tables[j].get_pagetable_page_closure())
        )
    }

    pub open spec fn free_pcids(&self) -> Set<Pcid>
    {
        self.free_page_tables@.to_set()
    }

    
    pub open spec fn get_page_table_pages(&self) -> Set<PagePtr>
    {
        self.page_table_pages@
    }

    pub open spec fn all_pcids(&self) -> Set<Pcid>
    {
        Set::new(|pcid: Pcid| {0 <= pcid< PCID_MAX})
    }

    pub open spec fn get_address_space(&self,pcid:Pcid) ->  Map<VAddr,PAddr>
        recommends 
            0<=pcid<PCID_MAX,
    {
        self.page_tables@[pcid as int].get_pagetable_mapping()
    }

    pub fn resolve(&self, pcid: Pcid, va: VAddr) -> (ret : Option<PAddr>)
        requires
            self.wf(),
            0<=pcid<PCID_MAX,
            //self.free_pcids().contains(pcid) == false,    
        ensures
            ret.is_None() ==> self.get_address_space(pcid).dom().contains(va) == false,
            ret.is_Some() ==> self.get_address_space(pcid).dom().contains(va),
            ret.is_Some() ==> self.get_address_space(pcid)[va] == ret.unwrap(),
            ret.is_Some() ==> page_ptr_valid(ret.unwrap() as usize),
    {
        return self.page_tables.get(pcid).resolve(va);
    }

    
}
}