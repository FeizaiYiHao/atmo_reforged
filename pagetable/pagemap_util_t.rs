use vstd::prelude::*;

verus! {
use crate::define::*;
// use crate::array::*;
use vstd::simple_pptr::*;
use crate::util::page_ptr_util_u::*;
// use crate::pagetable::pagetable_util::*;
use crate::pagetable::entry::*;
use crate::pagetable::pagemap::*;
use core::mem::MaybeUninit;
use crate::array::Array;

pub fn page_map_set_kernel_entry_range(kernel_entries: &Array<usize,KERNEL_MEM_END_L4INDEX>,page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>)
requires
    old(page_map_perm).addr() == page_map_ptr,
    old(page_map_perm).is_init(),
    old(page_map_perm).value().wf(),
    kernel_entries.wf(),
    kernel_entries@.len() == KERNEL_MEM_END_L4INDEX,
ensures
    page_map_perm.addr() == page_map_ptr,
    page_map_perm.is_init(),
    page_map_perm.value().wf(),
    forall|i: usize|
        #![trigger page_map_perm.value()[i]]
        KERNEL_MEM_END_L4INDEX <= i < 512 ==>
        page_map_perm.value()[i] =~= old(page_map_perm).value()[i],
    forall|i: usize|
        #![trigger page_map_perm.value()[i]]
        0 <= i < KERNEL_MEM_END_L4INDEX ==>
        page_map_perm.value()[i] =~= usize2page_entry(kernel_entries@[i as int]),
{
    for index in 0..KERNEL_MEM_END_L4INDEX
        invariant
            0<=index<=KERNEL_MEM_END_L4INDEX,
            kernel_entries.wf(),
            kernel_entries@.len() == KERNEL_MEM_END_L4INDEX,
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value()[i]]
                KERNEL_MEM_END_L4INDEX <= i < 512 ==>
                page_map_perm.value()[i] =~= old(page_map_perm).value()[i],
            forall|i: usize|
                #![trigger page_map_perm.value()[i]]
                0 <= i < index ==>
                page_map_perm.value()[i] =~= usize2page_entry(kernel_entries@[i as int]),
    {
        page_map_set_no_requires(page_map_ptr, Tracked(page_map_perm), index, usize2page_entry(*kernel_entries.get(index)));
    }
}

#[verifier(external_body)]
pub fn page_map_set_no_requires(page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>, index:usize, value:PageEntry)
requires
    old(page_map_perm).addr() == page_map_ptr,
    old(page_map_perm).is_init(),
    old(page_map_perm).value().wf(),
    0<=index<512,
ensures
    page_map_perm.addr() == page_map_ptr,
    page_map_perm.is_init(),
    page_map_perm.value().wf(),
    forall|i: usize|
        #![trigger page_map_perm.value()[i]]
        0 <= i < 512 && i != index ==>
        page_map_perm.value()[i] =~= old(page_map_perm).value()[i],
    page_map_perm.value()[index] =~= value
{
    unsafe{
        let uptr = page_map_ptr as *mut MaybeUninit<PageMap>;
        (*uptr).assume_init_mut().set(index, value);
    }
}

#[verifier(external_body)]
pub fn page_map_set(page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>, index:usize, value:PageEntry)
requires
    old(page_map_perm).addr() == page_map_ptr,
    old(page_map_perm).is_init(),
    old(page_map_perm).value().wf(),
    value.perm.present ==> MEM_valid(value.addr),
    value.perm.present == false ==> value.is_empty(),
    0<=index<512,
ensures
    page_map_perm.addr() == page_map_ptr,
    page_map_perm.is_init(),
    page_map_perm.value().wf(),
    forall|i: usize|
        #![trigger page_map_perm.value()[i]]
        0 <= i < 512 && i != index ==>
        page_map_perm.value()[i] =~= old(page_map_perm).value()[i],
    page_map_perm.value()[index] =~= value
{
    unsafe{
        let uptr = page_map_ptr as *mut MaybeUninit<PageMap>;
        (*uptr).assume_init_mut().set(index, value);
    }
}

#[verifier(external_body)]
pub fn page_perm_to_page_map(page_ptr: PagePtr, Tracked(page_perm): Tracked<PagePerm4k>) -> (ret: (PageMapPtr, Tracked<PointsTo<PageMap>>))
requires
    page_perm.is_init(),
    page_perm.addr() == page_ptr,
ensures
    ret.0 == page_ptr,
    ret.1@.addr() == ret.0,
    ret.1@.is_init(),
    ret.1@.value().wf(),
    forall|i:usize|
        #![trigger ret.1@.value()[i].is_empty()]
        0<=i<512 ==> ret.1@.value()[i].is_empty(),
{
    (page_ptr, Tracked::assume_new())
}



pub fn flush_tlb_4kentry(mut tlbmap_4k: Ghost<Seq<Map<VAddr,MapEntry>>> , va: VAddr) -> (ret: Ghost<Seq<Map<VAddr,MapEntry>>>)
requires
    NUM_CPUS > 0,
    tlbmap_4k@.len() == NUM_CPUS,
ensures
    tlbmap_4k@.len() == NUM_CPUS,
    forall|cpu_id:CpuId| #![auto] 0 <= cpu_id < NUM_CPUS ==> ret@[cpu_id as int].contains_key(va) == false,
{
    let mut cpu_id = 0;


    for cpu_id in 0 .. NUM_CPUS
    invariant
        0 <= cpu_id <= NUM_CPUS,
        tlbmap_4k@.len() == NUM_CPUS,
        forall|cpu_i:CpuId|
        #![auto] 0 <= cpu_i < cpu_id ==> tlbmap_4k@[cpu_i as int].contains_key(va) == false,
    {
        proof {
            assert(cpu_id < tlbmap_4k@.len());
            let tlbmap = tlbmap_4k@[cpu_id as int].remove(va);
            assert(!tlbmap.contains_key(va)); 
            let tlbseq = tlbmap_4k@.update(cpu_id as int, tlbmap);
            assert(tlbseq.index(cpu_id as int) =~= tlbmap);
            assert(tlbseq.contains(tlbmap));
            tlbmap_4k@ = tlbseq;
            assert(!tlbmap_4k@[cpu_id as int].contains_key(va));
        }
    }

    tlbmap_4k 

}


}
