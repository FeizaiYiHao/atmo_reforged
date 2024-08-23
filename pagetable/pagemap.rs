use vstd::prelude::*;
verus! {
// use vstd::ptr::PointsTo;
use crate::define::*;
use crate::array::*;
use crate::util::page_ptr_util_u::*;
use crate::lemma::lemma_u::*;
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
    pub execute_disable: bool,
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

pub open spec fn usize2execute_disable(v:usize) -> bool{
    (v & PAGE_ENTRY_EXECUTE_MASK as usize) != 0
}

pub open spec fn usize2user(v:usize) -> bool{
    (v & PAGE_ENTRY_USER_MASK as usize) != 0
}

pub open spec fn spec_usize2page_entry_perm(v:usize) -> PageEntryPerm{
    PageEntryPerm{
        present: usize2present(v),
        ps: usize2ps(v),
        write: usize2write(v),
        execute_disable: usize2execute_disable(v),
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
        execute_disable: (v & PAGE_ENTRY_EXECUTE_MASK as usize) != 0,
        user: (v & PAGE_ENTRY_USER_MASK as usize) != 0,
    }
}

pub open spec fn spec_usize2page_entry(v:usize) -> PageEntry{
    PageEntry{
        addr: usize2pa(v),
        perm: usize2page_entry_perm(v),
    } 
    
}

#[verifier(when_used_as_spec(spec_usize2page_entry))]
pub fn usize2page_entry(v:usize) -> (ret:PageEntry)
    ensures
        ret =~= spec_usize2page_entry(v),
{
    PageEntry{
        addr: usize2pa(v),
        perm: usize2page_entry_perm(v),
    } 
    
}

pub open spec fn spec_usize2pa(v:usize) -> PAddr{
    v & PA_MASK as usize
}

#[verifier(when_used_as_spec(spec_usize2pa))]
pub fn usize2pa(v:usize) -> (ret:PAddr)
    ensures
        ret =~= spec_usize2pa(v),
        pa_valid(ret),
{
    let ret = v & PA_MASK as usize;
    assert(  v & 0x0000_ffff_ffff_f000u64 as usize & (!0x0000_ffff_ffff_f000u64) as usize == 0) by (bit_vector);
    return ret;
}

pub fn page_entry2usize(page_entry: &PageEntry) -> (ret:usize)
    requires
        pa_valid(page_entry.addr),
    ensures
        usize2present(ret) == page_entry.perm.present,
        usize2ps(ret) == page_entry.perm.ps,
        usize2write(ret) == page_entry.perm.write,
        usize2execute_disable(ret) == page_entry.perm.execute_disable,
        usize2user(ret) == page_entry.perm.user,
        usize2pa(ret) == page_entry.addr,
        usize2page_entry_perm(ret) =~= page_entry.perm,
{
    let mut ret:usize = page_entry.addr;
    
    let mut ghost_addr = Ghost(page_entry.addr);
    let mut ghost_ret = Ghost(page_entry.addr);
    let ghost_present = Ghost(page_entry.perm.present);
    let ghost_ps = Ghost(page_entry.perm.ps);
    let ghost_write = Ghost(page_entry.perm.write);
    let ghost_execute_disable = Ghost(page_entry.perm.execute_disable);
    let ghost_user = Ghost(page_entry.perm.user);
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

        assert((ghost_ret@ | 0x1u64 as usize) & (!(0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector) requires 
            ghost_ret@ & (!0x0000_ffff_ffff_f000u64) as usize == 0;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PA_MASK)) as usize == 0);
    }else{
        assert((ret & 0x1u64 as usize) == 0) by (bit_vector) requires ret & (!0x0000_ffff_ffff_f000u64) as usize == 0 ; 
        assert(usize2present(ret) == page_entry.perm.present); 

    
        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == ret) by (bit_vector) requires ret & (!0x0000_ffff_ffff_f000u64) as usize == 0;
        assert(usize2pa(ret) == page_entry.addr); 

        assert(ghost_addr@ & (!(0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector) requires 
            ghost_addr@ & (!0x0000_ffff_ffff_f000u64) as usize == 0;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PA_MASK)) as usize == 0);
    }

    assert(usize2present(ret) == page_entry.perm.present); 
    assert(usize2pa(ret) == page_entry.addr); 
    assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PA_MASK)) as usize == 0);

    ghost_ret = Ghost(ret);

    if page_entry.perm.ps == true {
        assert(((ret | (0x1u64 << 0x7u64) as usize) & (0x1u64 << 0x7u64) as usize) != 0) by (bit_vector);
        assert(((ret | (0x1u64 << 0x7u64) as usize) & 0x1 as usize) != 0 == ghost_present@) by (bit_vector) requires 
            ghost_ret@ == ret
            && (ret & 0x1u64 as usize) != 0 == ghost_present@;
        assert(((ret | (0x1u64 << 0x7u64) as usize) & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@) by (bit_vector) requires 
            ghost_ret@ == ret
            && (ghost_ret@ & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@;
        ret = ret | (0x1u64 << 0x7u64) as usize;

        assert((ret & 0x1 as usize) != 0 == ghost_present@); 
        assert(usize2present(ret) == page_entry.perm.present); 
        assert((ret & (0x1u64 << 0x7u64) as usize) != 0); 
        assert(usize2ps(ret) == page_entry.perm.ps); 
        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@);
        assert(usize2pa(ret) == page_entry.addr); 

        assert((ghost_ret@ | (0x1u64 << 0x7u64) as usize) & (!(0x1u64 | 0x1u64 << 0x7u64 |0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector) requires 
            ghost_ret@ & (!(0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PA_MASK)) as usize == 0);
    }
    else{
        assert((ret & (0x1u64<<0x7u64) as usize) == 0) by (bit_vector) requires ret & (!(0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0 ; 

        assert(usize2present(ret) == page_entry.perm.present);
        assert(usize2ps(ret) == page_entry.perm.ps); 
        assert(usize2pa(ret) == page_entry.addr); 

        assert(ret & (!(0x1u64 | 0x1u64 << 0x7u64 |0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector) requires 
            ret & (!(0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PA_MASK)) as usize == 0);
    } 

    assert(usize2present(ret) == page_entry.perm.present);
    assert(usize2ps(ret) == page_entry.perm.ps); 
    assert(usize2pa(ret) == page_entry.addr); 
    assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PA_MASK)) as usize == 0);

    ghost_ret = Ghost(ret);

    if page_entry.perm.write == true {
        assert(((ret | (0x1u64 << 0x1u64) as usize) & (0x1u64 << 0x1u64) as usize) != 0) by (bit_vector);
        assert(((ret | (0x1u64 << 0x1u64) as usize) & 0x1 as usize) != 0 == ghost_present@) by (bit_vector) requires 
            ghost_ret@ == ret
            && (ret & 0x1u64 as usize) != 0 == ghost_present@;
        assert(((ret | (0x1u64 << 0x1u64) as usize) & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@) by (bit_vector) requires 
            ghost_ret@ == ret
            && (ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@;
        assert(((ret | (0x1u64 << 0x1u64) as usize) & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@) by (bit_vector) requires 
            ghost_ret@ == ret
            && (ghost_ret@ & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@;
        ret = ret | (0x1u64 << 0x1u64) as usize;

        assert((ret & 0x1 as usize) != 0 == ghost_present@); 
        assert(usize2present(ret) == page_entry.perm.present); 
        assert((ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@); 
        assert(usize2ps(ret) == page_entry.perm.ps); 
        assert((ret & (0x1u64 << 0x1u64) as usize) != 0); 
        assert(usize2write(ret) == page_entry.perm.write); 
        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@);
        assert(usize2pa(ret) == page_entry.addr); 

        assert((ghost_ret@ | (0x1u64 << 0x1u64) as usize) & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 |0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector) requires 
            ghost_ret@ & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK | PA_MASK)) as usize == 0);
    }
    else{
        assert((ret & (0x1u64<<0x1u64) as usize) == 0) by (bit_vector) requires ret & (!(0x1u64 | 0x1u64 << 0x7u64 |0x0000_ffff_ffff_f000u64)) as usize == 0 ; 

        assert(usize2present(ret) == page_entry.perm.present);
        assert(usize2ps(ret) == page_entry.perm.ps); 
        assert(usize2write(ret) == page_entry.perm.write); 
        assert(usize2pa(ret) == page_entry.addr); 

        assert(ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 |0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector) requires 
            ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK | PA_MASK)) as usize == 0);
    } 

    assert(usize2present(ret) == page_entry.perm.present);
    assert(usize2ps(ret) == page_entry.perm.ps); 
    assert(usize2write(ret) == page_entry.perm.write); 
    assert(usize2pa(ret) == page_entry.addr); 
    assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK | PA_MASK)) as usize == 0);

    ghost_ret = Ghost(ret);
    
    if page_entry.perm.execute_disable == true {
        assert(((ret | (0x1u64 << 63u64) as usize) & (0x1u64 << 63u64) as usize) != 0) by (bit_vector);
        assert(((ret | (0x1u64 << 63u64) as usize) & 0x1 as usize) != 0 == ghost_present@) by (bit_vector) requires 
            ghost_ret@ == ret
            && (ret & 0x1u64 as usize) != 0 == ghost_present@;
        assert(((ret | (0x1u64 << 63u64) as usize) & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@) by (bit_vector) requires 
            ghost_ret@ == ret
            && (ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@;
        assert(((ret | (0x1u64 << 63u64) as usize) & (0x1u64 << 0x1u64) as usize) != 0 == ghost_write@) by (bit_vector) requires 
            ghost_ret@ == ret
            && (ret & (0x1u64 << 0x1u64) as usize) != 0 == ghost_write@;
        assert(((ret | (0x1u64 << 63u64) as usize) & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@) by (bit_vector) requires 
            ghost_ret@ == ret
            && (ghost_ret@ & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@;
        ret = ret | (0x1u64 << 63u64) as usize;

        assert((ret & 0x1 as usize) != 0 == ghost_present@); 
        assert(usize2present(ret) == page_entry.perm.present); 
        assert((ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@); 
        assert(usize2ps(ret) == page_entry.perm.ps); 
        assert((ret & (0x1u64 << 0x1u64) as usize) != 0 == ghost_write@); 
        assert(usize2write(ret) == page_entry.perm.write); 
        assert((ret & (0x1u64 << 63u64) as usize) != 0); 
        assert(usize2execute_disable(ret) == page_entry.perm.execute_disable); 
        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@);
        assert(usize2pa(ret) == page_entry.addr); 

        assert((ghost_ret@ | (0x1u64 << 63u64) as usize) & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 | 0x1u64 << 63u64 |0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector) requires 
            ghost_ret@ & (!(0x1u64 | 0x1u64 << 0x7u64 |  0x1u64 << 0x1u64 |0x0000_ffff_ffff_f000u64)) as usize == 0;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK | PAGE_ENTRY_EXECUTE_MASK | PA_MASK)) as usize == 0);
    }
    else{
        assert((ret & (0x1u64<<63u64) as usize) == 0) by (bit_vector) requires ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 |0x0000_ffff_ffff_f000u64)) as usize == 0 ; 

        assert(usize2present(ret) == page_entry.perm.present);
        assert(usize2ps(ret) == page_entry.perm.ps); 
        assert(usize2write(ret) == page_entry.perm.write); 
        assert(usize2execute_disable(ret) == page_entry.perm.execute_disable); 
        assert(usize2pa(ret) == page_entry.addr); 

        assert(ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 | 0x1u64 << 63u64 |0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector) requires 
            ret & (!(0x1u64 | 0x1u64 << 0x7u64 |  0x1u64 << 0x1u64 |0x0000_ffff_ffff_f000u64)) as usize == 0;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK |  PAGE_ENTRY_EXECUTE_MASK | PA_MASK)) as usize == 0);
    } 

    assert(usize2present(ret) == page_entry.perm.present);
    assert(usize2ps(ret) == page_entry.perm.ps); 
    assert(usize2write(ret) == page_entry.perm.write); 
    assert(usize2execute_disable(ret) == page_entry.perm.execute_disable); 
    assert(usize2pa(ret) == page_entry.addr); 
    assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK |  PAGE_ENTRY_EXECUTE_MASK | PA_MASK)) as usize == 0);

    ghost_ret = Ghost(ret);
    
    if page_entry.perm.user == true {
        assert(((ret | (0x1u64 << 2u64) as usize) & (0x1u64 << 2u64) as usize) != 0) by (bit_vector);
        assert(((ret | (0x1u64 << 2u64) as usize) & 0x1 as usize) != 0 == ghost_present@) by (bit_vector) requires 
            ghost_ret@ == ret
            && (ret & 0x1u64 as usize) != 0 == ghost_present@;
        assert(((ret | (0x1u64 << 2u64) as usize) & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@) by (bit_vector) requires 
            ghost_ret@ == ret
            && (ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@;
        assert(((ret | (0x1u64 << 2u64) as usize) & (0x1u64 << 0x1u64) as usize) != 0 == ghost_write@) by (bit_vector) requires 
            ghost_ret@ == ret
            && (ret & (0x1u64 << 0x1u64) as usize) != 0 == ghost_write@;
        assert(((ret | (0x1u64 << 2u64) as usize) & (0x1u64 << 63u64) as usize) != 0 == ghost_execute_disable@) by (bit_vector) requires 
            ghost_ret@ == ret
            && (ret & (0x1u64 << 63u64) as usize) != 0 == ghost_execute_disable@;
        assert(((ret | (0x1u64 << 2u64) as usize) & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@) by (bit_vector) requires 
            ghost_ret@ == ret
            && (ghost_ret@ & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@;
        ret = ret | (0x1u64 << 2u64) as usize;

        assert((ret & 0x1 as usize) != 0 == ghost_present@); 
        assert(usize2present(ret) == page_entry.perm.present); 
        assert((ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@); 
        assert(usize2ps(ret) == page_entry.perm.ps); 
        assert((ret & (0x1u64 << 0x1u64) as usize) != 0 == ghost_write@); 
        assert(usize2write(ret) == page_entry.perm.write); 
        assert((ret & (0x1u64 << 63u64) as usize) != 0 == ghost_execute_disable@); 
        assert(usize2execute_disable(ret) == page_entry.perm.execute_disable); 
        assert((ret & (0x1u64 << 2u64) as usize) != 0); 
        assert(usize2user(ret) == page_entry.perm.user); 
        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@);
        assert(usize2pa(ret) == page_entry.addr); 

        assert((ghost_ret@ | (0x1u64 << 2u64) as usize) & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 | 0x1u64 << 63u64 | 0x1u64 << 2u64 |0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector) requires 
            ghost_ret@ & (!(0x1u64 | 0x1u64 << 0x7u64 |  0x1u64 << 0x1u64 | 0x1u64 << 63u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK | PAGE_ENTRY_EXECUTE_MASK | PAGE_ENTRY_USER_MASK | PA_MASK)) as usize == 0);
    }
    else{
        assert((ret & (0x1u64<<2u64) as usize) == 0) by (bit_vector) requires ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 | 0x1u64 << 63u64 |0x0000_ffff_ffff_f000u64)) as usize == 0 ; 

        assert(usize2present(ret) == page_entry.perm.present);
        assert(usize2ps(ret) == page_entry.perm.ps); 
        assert(usize2write(ret) == page_entry.perm.write); 
        assert(usize2execute_disable(ret) == page_entry.perm.execute_disable); 
        assert(usize2user(ret) == page_entry.perm.user); 
        assert(usize2pa(ret) == page_entry.addr); 

        assert(ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 | 0x1u64 << 63u64 | 0x1u64 << 2u64 |0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector) requires 
            ret & (!(0x1u64 | 0x1u64 << 0x7u64 |  0x1u64 << 0x1u64 | 0x1u64 << 63u64 |0x0000_ffff_ffff_f000u64)) as usize == 0;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK | PAGE_ENTRY_EXECUTE_MASK | PAGE_ENTRY_USER_MASK | PA_MASK)) as usize == 0);
    } 

    assert(usize2present(ret) == page_entry.perm.present);
    assert(usize2ps(ret) == page_entry.perm.ps); 
    assert(usize2write(ret) == page_entry.perm.write); 
    assert(usize2execute_disable(ret) == page_entry.perm.execute_disable); 
    assert(usize2user(ret) == page_entry.perm.user); 
    assert(usize2pa(ret) == page_entry.addr); 

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
                    page_ptr_valid_imply_pa_valid(value.addr);
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
