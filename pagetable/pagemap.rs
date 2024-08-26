use vstd::prelude::*;
verus! {
// use vstd::ptr::PointsTo;
// use crate::define::*;
use crate::array::*;
use crate::util::page_ptr_util_u::*;
use crate::lemma::lemma_u::*;
use crate::pagetable::page_entry::*;


pub struct PageMap{
    pub ar: Array<usize,512>,
    pub spec_seq: Ghost<Seq<PageEntry>>,
    // pub level: Ghost<usize>, // not used for now.
}

impl PageMap{
    pub open spec fn wf(&self) -> bool{
        &&&
        self.ar.wf()
        &&&
        self.spec_seq@.len() == 512
        &&&
        forall|i:int|
            #![trigger usize2page_entry(self.ar@[i])]
            0<=i<512 ==> (usize2page_entry(self.ar@[i]) =~= self.spec_seq@[i])
        &&&
        forall|i:int|
            #![trigger usize2page_entry(self.ar@[i]).perm.present]
            0<=i<512 ==> (usize2page_entry(self.ar@[i]).perm.present == false <==> self.ar@[i] == 0)
        
    }

    pub open spec fn view(&self) -> Seq<PageEntry>
    {
        self.spec_seq@
    }

    pub open spec fn spec_index(&self, index:usize) -> PageEntry
        recommends
            0<=index<512,
    {
        self.spec_seq@[index as int]
    }

    pub fn set(&mut self, index:usize, value:PageEntry)
        requires
            old(self).wf(),
            0<=index<512,
            value.perm.present ==> page_ptr_valid(value.addr),
            value.perm.present == false ==> usize2page_entry(0) =~= value,
        ensures
            self.wf(),
            self@ =~= self@.update(index as int,value),
        {
            // proof{
            //     pagemap_permission_bits_lemma();
            // }
            if value.perm.present == false {
                self.ar.set(index,0);
                proof{
                    self.spec_seq@ = self.spec_seq@.update(index as int,usize2page_entry(0));
                }
                return;
            }
            else{
                proof{
                    page_ptr_valid_imply_MEM_valid(value.addr);
                }
                let u = page_entry2usize(&value);
                self.ar.set(index,u);

                assert(usize2present(u) == value.perm.present);
                assert(usize2present(u) == true);
                assert(u != 0) by (bit_vector) requires (u & 0x1u64 as usize) != 0 == true;

                proof{
                    self.spec_seq@ = self.spec_seq@.update(index as int,value);
                }

                return;
            }
        }
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

    pub fn index(&self, index:usize) -> (ret:PageEntry)
        requires
            self.wf(),
            0<=index<512,
        ensures
            ret =~= self[index],
    {
        return usize2page_entry(*self.ar.get(index));
    }

    pub fn get(&self, index:usize) -> (ret:PageEntry)
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
