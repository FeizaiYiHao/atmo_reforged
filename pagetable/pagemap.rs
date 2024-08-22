use vstd::prelude::*;
verus! {
// use vstd::ptr::PointsTo;
use crate::define::*;
use crate::array::*;

use crate::pagetable::*;


// #[verifier(external_body)]
// fn index_helper(value:usize) -> (ret:bool)
//     ensures
//         ret == ((value & (PAGE_ENTRY_PRESENT_MASK as usize)) != 0 )
// {
//     return (value & (PAGE_ENTRY_PRESENT_MASK as usize)) != 0
// }
#[derive(Clone,Debug)]
pub struct PageEntry{
    pub addr: PAddr,
    pub perm: PageEntryPerm,
}

pub struct PageMap{
    pub ar: MarsArray<usize,512>,
    pub spec_seq: Ghost<Seq<Option<PageEntry>>>,
    pub level: Ghost<usize>, // not used for now.
}
impl PageMap{
    pub open spec fn wf(&self) -> bool{
        self.ar.wf()
        &&
        self.spec_seq@.len() == 512
        &&
        (
            forall|i:int|
                // #![trigger self.ar@[i]]
                #![trigger self.spec_seq@[i].is_None()]
                0<=i<512 ==> ((self.ar@[i] & (PAGE_ENTRY_PRESENT_MASK as usize) == 0) <==> self.spec_seq@[i].is_None())
        )
        &&
        (
            forall|i:int|
                #![trigger self.spec_seq@[i].get_Some_0().addr]
                // #![trigger self.ar@[i]]
                0<=i<512 && self.spec_seq@[i].is_Some() ==>
                self.spec_seq@[i].get_Some_0().addr == (self.ar@[i] & (VA_MASK as usize))
        )
        &&
        (
            forall|i:int|
                #![trigger page_ptr_valid(self.spec_seq@[i].get_Some_0().addr)]
                0<=i<512 && self.spec_seq@[i].is_Some() ==>
                (
                    page_ptr_valid(self.spec_seq@[i].get_Some_0().addr)
                )
        )
        &&
        (
            forall|i:int|
                #![trigger self.spec_seq@[i].get_Some_0().perm]
                0<=i<512 && self.spec_seq@[i].is_Some() ==>
            (
                self.spec_seq@[i].get_Some_0().perm == (self.ar@[i] & (VA_PERM_MASK as usize))
            )
        )
        &&
        (
            forall|i:int|
                #![trigger spec_va_perm_bits_valid(self.spec_seq@[i].get_Some_0().perm)]
                #![trigger self.spec_seq@[i].get_Some_0().perm]
                0<=i<512 && self.spec_seq@[i].is_Some() ==>
            (
                spec_va_perm_bits_valid(self.spec_seq@[i].get_Some_0().perm)
            )
        )
    }

    pub open spec fn view(&self) -> Seq<Option<PageEntry>>
    {
        self.spec_seq@
    }

    pub open spec fn spec_index(&self, index:usize) -> Option<PageEntry>
        recommends
            0<=index<512,
    {
        self.spec_seq@[index as int]
    }

    pub fn set(&mut self, index:usize, value:Option<PageEntry>)
        requires
            old(self).wf(),
            0<=index<512,
            value.is_Some() ==> page_ptr_valid(value.unwrap().addr),
            value.is_Some() ==> spec_va_perm_bits_valid(value.unwrap().perm),
        ensures
            self.wf(),
            self@ =~= self@.update(index as int,value),
        {
            proof{
                pagemap_permission_bits_lemma();
            }
            if value.is_none(){
                self.ar.set(index,0);
                proof{
                    self.spec_seq@ = self.spec_seq@.update(index as int,None);
                }
                return;
            }else{
                let entry = value.unwrap();
                self.ar.set(index, (entry.addr | entry.perm) | (PAGE_ENTRY_PRESENT_MASK as usize));
                proof{
                    self.spec_seq@ = self.spec_seq@.update(index as int,value);
                }

                assert(self.ar.wf());
                assert(self.spec_seq@.len() == 512);
                assert(
                    forall|i:int|#![auto] 0<=i<512 ==> ((self.ar@[i] & (PAGE_ENTRY_PRESENT_MASK as usize) == 0) <==> self.spec_seq@[i].is_None())
                );
                assert(
                    forall|i:int|#![auto] 0<=i<512 && self.spec_seq@[i].is_Some() ==>
                    (
                        self.spec_seq@[i].get_Some_0().addr == (self.ar@[i] & (VA_MASK as usize))
                    )
                );
                assert(
                    forall|i:int|#![auto] 0<=i<512 && self.spec_seq@[i].is_Some() ==>
                    (
                        page_ptr_valid(self.spec_seq@[i].get_Some_0().addr)
                    )
                );
                assert(
                    forall|i:int|#![auto] 0<=i<512 && self.spec_seq@[i].is_Some() ==>
                    (
                        self.spec_seq@[i].get_Some_0().perm == (self.ar@[i] & (VA_PERM_MASK as usize))
                    )
                );
                assert(
                    forall|i:int|#![auto] 0<=i<512 && self.spec_seq@[i].is_Some() ==>
                    (
                        spec_va_perm_bits_valid(self.spec_seq@[i].get_Some_0().perm)
                    )
                );
                return;
            }
        }
    #[verifier(external_body)]
    pub fn set_kernel_pml4_entry(&mut self, index:usize, value:Option<PageEntry>)
        requires
            old(self).wf(),
            0<=index<512,
            value.is_Some() ==> page_ptr_valid(value.unwrap().addr),
            value.is_Some() ==> spec_va_perm_bits_valid(value.unwrap().perm),
        ensures
            self.wf(),
            self@ =~= self@.update(index as int,value),
        {
            proof{
                pagemap_permission_bits_lemma();
            }
            if value.is_none(){
                self.ar.set(index,0);
                proof{
                    self.spec_seq@ = self.spec_seq@.update(index as int,None);
                }
                return;
            }else{
                let entry = value.unwrap();
                self.ar.set(index, (entry.addr | entry.perm) | (0x1 as usize));
                proof{
                    self.spec_seq@ = self.spec_seq@.update(index as int,value);
                }

                return;
            }
        }

    pub fn index(&self, index:usize) -> (ret:Option<PageEntry>)
        requires
            self.wf(),
            0<=index<512,
        ensures
            ret =~= self[index],
    {
       let value = *self.ar.get(index);
       if (value & (PAGE_ENTRY_PRESENT_MASK as usize)) != 0 {
            // assert(value & (VA_MASK as usize) == self.spec_seq@[i].get_Some_0().addr );
            return Some(PageEntry{addr : value & (VA_MASK as usize),perm: value & (VA_PERM_MASK as usize)});
       }
       else{
            return None;
       }
    }

    pub fn get(&self, index:usize) -> (ret:Option<PageEntry>)
        requires
            self.wf(),
            0<=index<512,
        ensures
            ret =~= self[index],
    {
        return self.index(index);
    }
}

}
