use vstd::prelude::*;
verus! {
// use vstd::ptr::PointsTo;
use crate::define::*;
use crate::array::*;
use crate::util::page_ptr_util_u::*;
use crate::lemma::lemma_t::*;
// use crate::pagetable::*;


// #[verifier(external_body)]
// fn index_helper(value:usize) -> (ret:bool)
//     ensures
//         ret == ((value & (PAGE_ENTRY_PRESENT_MASK as usize)) != 0 )
// {
//     return (value & (PAGE_ENTRY_PRESENT_MASK as usize)) != 0
// }

// the idea here is to hide everything that requires bit vector
#[derive(Clone,Debug)]
pub struct PageEntryPerm{
    pub present:bool,
    pub ps:bool,
    pub write:bool,
    pub execute: bool,
    pub user:bool,
}

pub open spec fn usize2present(v:usize) -> bool{
    (v & PAGE_ENTRY_PRESENT_MASK as usize) != 0
}

pub open spec fn usize2ps(v:usize) -> bool{
    (v & PAGE_ENTRY_PS_MASK as usize) != 0
}

pub open spec fn usize2write(v:usize) -> bool{
    (v & PAGE_ENTRY_WRITE_MASK as usize) != 0
}

pub open spec fn usize2execute(v:usize) -> bool{
    (v & PAGE_ENTRY_EXECUTE_MASK as usize) != 1
}

pub open spec fn usize2user(v:usize) -> bool{
    (v & PAGE_ENTRY_USER_MASK as usize) != 0
}

pub open spec fn spec_usize2page_entry_perm(v:usize) -> PageEntryPerm{
    PageEntryPerm{
        present: usize2present(v),
        ps: usize2ps(v),
        write: usize2write(v),
        execute: usize2execute(v),
        user: usize2user(v),
    }
}

#[verifier(when_used_as_spec(spec_usize2page_entry_perm))]
pub fn usize2page_entry_perm(v:usize) -> (ret:PageEntryPerm)
    ensures
        ret =~= spec_usize2page_entry_perm(v),
{
    PageEntryPerm{
        present: (v & PAGE_ENTRY_PRESENT_MASK as usize) != 0,
        ps: (v & PAGE_ENTRY_PS_MASK as usize) != 0,
        write: (v & PAGE_ENTRY_WRITE_MASK as usize) != 0,
        execute: (v & PAGE_ENTRY_EXECUTE_MASK as usize) != 1,
        user: (v & PAGE_ENTRY_USER_MASK as usize) != 0,
    }
}

pub open spec fn spec_usize2pa(v:usize) -> PAddr{
    v & VA_MASK as usize
}

#[verifier(when_used_as_spec(spec_usize2pa))]
pub fn usize2pa(v:usize) -> (ret:PAddr)
    ensures
        ret =~= spec_usize2pa(v),
        (ret & (!VA_MASK) as usize == 0),
{
    let ret = v & VA_MASK as usize;
    assert(  v & 0x0000_ffff_ffff_f000u64 as usize & (!0x0000_ffff_ffff_f000u64) as usize == 0) by (bit_vector);
    return ret;
}

pub fn page_entry2usize(page_entry: &PageEntry) -> usize
    requires
        page_entry.addr & (!VA_MASK) as usize == 0,
{
    let mut ret:usize = page_entry.addr;
    let ghost_addr = Ghost(page_entry.addr);
    assert(ret == ghost_addr@);
    if page_entry.perm.present == true {
        assert(((ret | 0x1u64 as usize) & 0x1u64 as usize) != 0) by (bit_vector);
        assert(((ret | 0x1u64 as usize) & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@) by (bit_vector) requires 
            ghost_addr@ & (!0x0000_ffff_ffff_f000u64) as usize == 0
            && ghost_addr@ == ret;

        ret = ret | 0x1u64 as usize;

        assert((ret & 0x1u64 as usize) != 0); 
        assert(usize2present(ret) == page_entry.perm.present); 

        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == page_entry.addr);
        assert(usize2pa(ret) == page_entry.addr); 

        assert((ghost_addr@ | 0x1u64 as usize) & (!(0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector) requires 
            ghost_addr@ & (!0x0000_ffff_ffff_f000u64) as usize == 0;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | VA_MASK)) as usize == 0);
    }else{
        assert((ret & 0x1u64 as usize) == 0) by (bit_vector) requires ret & (!0x0000_ffff_ffff_f000u64) as usize == 0 ; 
        assert(usize2present(ret) == page_entry.perm.present); 

    
        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == ret) by (bit_vector) requires ret & (!0x0000_ffff_ffff_f000u64) as usize == 0;
        assert(usize2pa(ret) == page_entry.addr); 

        assert(ghost_addr@ & (!(0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector) requires 
            ghost_addr@ & (!0x0000_ffff_ffff_f000u64) as usize == 0;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | VA_MASK)) as usize == 0);
    }

    return ret;
}

#[derive(Clone,Debug)]
pub struct PageEntry{
    pub addr: PAddr,
    pub perm: PageEntryPerm,
    // pub ps: bool,
}

pub struct PageMap{
    pub ar: Array<usize,512>,
    pub spec_seq: Ghost<Seq<Option<PageEntry>>>,
    // pub level: Ghost<usize>, // not used for now.
}

impl PageMap{
    pub open spec fn wf(&self) -> bool{
        self.ar.wf()
        &&
        self.spec_seq@.len() == 512
        &&
        (
            forall|i:int|
                #![trigger usize2page_entry_perm(self.ar@[i])]
                #![trigger self.spec_seq@[i].is_None()]
                0<=i<512 ==> ((usize2page_entry_perm(self.ar@[i]).present == false) <==> self.spec_seq@[i].is_None())
        )
        &&
        (
            forall|i:int|
                #![trigger self.spec_seq@[i].get_Some_0().addr]
                // #![trigger self.ar@[i] & (VA_MASK as usize)]
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
                // #![trigger self.ar@[i] & (VA_PERM_MASK as usize)]
                0<=i<512 && self.spec_seq@[i].is_Some() ==>
            (
                self.spec_seq@[i].get_Some_0().perm == usize2page_entry_perm(self.ar@[i])
            )
        )
    }

    // pub open spec fn view(&self) -> Seq<Option<PageEntry>>
    // {
    //     self.spec_seq@
    // }

    // pub open spec fn spec_index(&self, index:usize) -> Option<PageEntry>
    //     recommends
    //         0<=index<512,
    // {
    //     self.spec_seq@[index as int]
    // }

    // pub fn set(&mut self, index:usize, value:Option<PageEntry>)
    //     requires
    //         old(self).wf(),
    //         0<=index<512,
    //         value.is_Some() ==> page_ptr_valid(value.unwrap().addr),
    //     ensures
    //         self.wf(),
    //         self@ =~= self@.update(index as int,value),
    //     {
    //         proof{
    //             pagemap_permission_bits_lemma();
    //         }
    //         if value.is_none(){
    //             self.ar.set(index,0);
    //             proof{
    //                 self.spec_seq@ = self.spec_seq@.update(index as int,None);
    //             }
    //             return;
    //         }else{
    //             let entry = value.unwrap();
    //             self.ar.set(index, (entry.addr | entry.perm) | (PAGE_ENTRY_PRESENT_MASK as usize));
    //             proof{
    //                 self.spec_seq@ = self.spec_seq@.update(index as int,value);
    //             }

    //             assert(self.ar.wf());
    //             assert(self.spec_seq@.len() == 512);
    //             assert(
    //                 forall|i:int|#![auto] 0<=i<512 ==> ((self.ar@[i] & (PAGE_ENTRY_PRESENT_MASK as usize) == 0) <==> self.spec_seq@[i].is_None())
    //             );
    //             assert(
    //                 forall|i:int|#![auto] 0<=i<512 && self.spec_seq@[i].is_Some() ==>
    //                 (
    //                     self.spec_seq@[i].get_Some_0().addr == (self.ar@[i] & (VA_MASK as usize))
    //                 )
    //             );
    //             assert(
    //                 forall|i:int|#![auto] 0<=i<512 && self.spec_seq@[i].is_Some() ==>
    //                 (
    //                     page_ptr_valid(self.spec_seq@[i].get_Some_0().addr)
    //                 )
    //             );
    //             assert(
    //                 forall|i:int|#![auto] 0<=i<512 && self.spec_seq@[i].is_Some() ==>
    //                 (
    //                     self.spec_seq@[i].get_Some_0().perm == (self.ar@[i] & (VA_PERM_MASK as usize))
    //                 )
    //             );
    //             assert(
    //                 forall|i:int|#![auto] 0<=i<512 && self.spec_seq@[i].is_Some() ==>
    //                 (
    //                     spec_va_perm_bits_valid(self.spec_seq@[i].get_Some_0().perm)
    //                 )
    //             );
    //             return;
    //         }
    //     }
    // #[verifier(external_body)]
    // pub fn set_kernel_pml4_entry(&mut self, index:usize, value:Option<PageEntry>)
    //     requires
    //         old(self).wf(),
    //         0<=index<512,
    //         value.is_Some() ==> page_ptr_valid(value.unwrap().addr),
    //         value.is_Some() ==> spec_va_perm_bits_valid(value.unwrap().perm),
    //     ensures
    //         self.wf(),
    //         self@ =~= self@.update(index as int,value),
    //     {
    //         proof{
    //             pagemap_permission_bits_lemma();
    //         }
    //         if value.is_none(){
    //             self.ar.set(index,0);
    //             proof{
    //                 self.spec_seq@ = self.spec_seq@.update(index as int,None);
    //             }
    //             return;
    //         }else{
    //             let entry = value.unwrap();
    //             self.ar.set(index, (entry.addr | entry.perm) | (0x1 as usize));
    //             proof{
    //                 self.spec_seq@ = self.spec_seq@.update(index as int,value);
    //             }

    //             return;
    //         }
    //     }

    // pub fn index(&self, index:usize) -> (ret:Option<PageEntry>)
    //     requires
    //         self.wf(),
    //         0<=index<512,
    //     ensures
    //         ret =~= self[index],
    // {
    //    let value = *self.ar.get(index);
    //    if (value & (PAGE_ENTRY_PRESENT_MASK as usize)) != 0 {
    //         assert(self.spec_seq@[index as int].is_Some());
    //         assert(value & #[verifier::truncate](VA_MASK as usize) == self.spec_seq@[index as int].get_Some_0().addr );
    //         assert(value & #[verifier::truncate](VA_PERM_MASK as usize) == self.spec_seq@[index as int].get_Some_0().perm );
    //         return Some(PageEntry{addr : value & #[verifier::truncate](VA_MASK as usize),perm: value & #[verifier::truncate](VA_PERM_MASK as usize)});
    //    }
    //    else{
    //         return None;
    //    }
    // }

    // pub fn get(&self, index:usize) -> (ret:Option<PageEntry>)
    //     requires
    //         self.wf(),
    //         0<=index<512,
    //     ensures
    //         ret =~= self[index],
    // {
    //     return self.index(index);
    // }
}

}
