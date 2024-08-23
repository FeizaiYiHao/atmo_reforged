use vstd::prelude::*;

verus! {
use vstd::ptr::*;
// use crate::trap::Registers;

// -------------------- Begin of Types --------------------
pub type ThreadPtr = usize;
pub type ProcPtr = usize;
pub type EndpointIdx = usize;
pub type EndpointPtr = usize;

pub type PagePPtr = PPtr<[u8; PAGE_SZ]>;
pub type PagePtr = usize;
pub type PagePerm = PointsTo<[u8; PAGE_SZ]>;

pub type VAddr = usize;
pub type PAddr = usize;
// pub type PageEntryPerm = usize;

pub type Pcid = usize;
pub type IOid = usize;

pub type L4Index = usize;
pub type L3Index = usize;
pub type L2Index = usize;
pub type L1Index = usize;

#[derive(Clone, Copy, Debug)]
pub enum ErrorCodeType {
    NoErrorCode,
}

#[derive(Clone, Copy, Debug)]
pub enum ThreadState {
    SCHEDULED,
    BLOCKED,
    RUNNING,
    CALLING,
    TRANSIT,
}

#[derive(Clone, Copy, Debug)]
pub enum EndpointState {
    RECEIVE,
    SEND,
}

#[derive(Clone, Copy, Debug)]
pub enum PageType {
    R,
    RW,
    RX,
    RWX,
}

#[derive(Clone, Copy, Debug)]
pub enum PageState {
    UNAVAILABLE,
    FREE,
    PAGETABLE,
    ALLOCATED,
    MAPPED,
    IO,
}

#[derive(Clone, Copy, Debug)]
pub enum PageSize {
    SZ4K,
    SZ2M,
    SZ1G,
}

// -------------------- End of Types --------------------

// -------------------- Begin of Const --------------------
pub const MAX_NUM_ENDPOINT_DESCRIPTORS:usize = 128;
pub const MAX_NUM_THREADS_PER_PROC:usize = 250;
pub const MAX_NUM_THREADS_PER_ENDPOINT:usize = 250;
pub const MAX_NUM_PROCS:usize = PCID_MAX;
pub const MAX_NUM_THREADS:usize = 500 * 4096;
pub const IPC_MESSAGE_LEN:usize = 1024;
pub const IPC_PAGEPAYLOAD_LEN:usize = 128;

pub const KERNEL_MEM_END_L4INDEX:usize = 1; //1 for now
pub const NUM_PAGES:usize = 2*1024*1024; //8GB
pub const PAGE_SZ:usize = 4096;
pub const MAX_USIZE:u64 = 31*1024*1024*1024;

pub const PCID_MAX:usize = 4096;
pub const IOID_MAX:usize = 4096;

pub const PA_MASK:u64 = 0x0000_ffff_ffff_f000;
pub const VA_PERM_MASK:u64 = 0x8000_0000_0000_0002;
pub const READ:usize = 0x8000_0000_0000_0000u64 as usize;
pub const READ_WRITE:usize = 0x8000_0000_0000_0002u64 as usize;
pub const READ_EXECUTE:usize = 0x0000_0000_0000_0000u64 as usize;
pub const READ_WRITE_EXECUTE:usize = 0x0000_0000_0000_0002u64 as usize;
pub const PCID_ENABLE_MASK:usize = 0x8000_0000_0000_0000u64 as usize;

pub const NUM_CPUS:usize = 32;
pub const PAGE_ENTRY_PRESENT_SHIFT:u64 = 0;
pub const PAGE_ENTRY_WRITE_SHIFT:u64 = 1;
pub const PAGE_ENTRY_USER_SHIFT:u64 = 2;
pub const PAGE_ENTRY_PS_SHIFT:u64 = 7;
pub const PAGE_ENTRY_EXECUTE_SHIFT:u64 = 63;
pub const PAGE_ENTRY_PRESENT_MASK:u64 = 0x1;
pub const PAGE_ENTRY_WRITE_MASK:u64 = 0x1u64<<PAGE_ENTRY_WRITE_SHIFT;
pub const PAGE_ENTRY_USER_MASK:u64 = 0x1u64<<PAGE_ENTRY_USER_SHIFT;
pub const PAGE_ENTRY_PS_MASK:u64 = 0x1u64<<PAGE_ENTRY_PS_SHIFT;
pub const PAGE_ENTRY_EXECUTE_MASK:u64 = 0x1u64<<PAGE_ENTRY_EXECUTE_SHIFT;
// -------------------- End of Const --------------------

// -------------------- Begin of Structs --------------------
#[derive(Clone, Copy, Debug)]
pub struct SyscallReturnStruct{
    pub error_code: ErrorCodeType,
    pub pcid: Pcid,
    pub cr3: usize,
    pub thread_ptr:ThreadPtr,
}

impl SyscallReturnStruct{

    pub fn new(error_code:ErrorCodeType,pcid:Pcid,cr3:usize,thread_ptr:ThreadPtr )->(ret:Self)
        ensures
            ret.error_code == error_code,
            ret.pcid == pcid,
            ret.cr3 == cr3,
            ret.thread_ptr == thread_ptr,
    {
        return Self{
            error_code:error_code,
            pcid:pcid,
            cr3:cr3,
            thread_ptr:thread_ptr,
        };
    }
}

// -------------------- End of Structs --------------------

}