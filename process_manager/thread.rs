use vstd::prelude::*;
verus! {
    use crate::trap::*;
    use crate::define::*;
    use crate::array::*;

    pub struct Thread{
        pub owning_container: ContainerPtr,
        pub owning_proc: ProcPtr,
        pub state: ThreadState,
    
        pub proc_rev_ptr: SLLIndex,
        pub scheduler_rev_ptr: Option<SLLIndex>,
        
        pub blocking_endpoint_ptr: Option<EndpointPtr>,
        pub endpoint_rev_ptr: Option<SLLIndex>,

        pub running_cpu: Option<CpuId>,
        
        pub endpoint_descriptors: Array<Option<EndpointPtr>,MAX_NUM_ENDPOINT_DESCRIPTORS>,
        pub ipc_payload: Option<IPCPayLoad>,
        
        pub error_code: Option<ErrorCodeType>, //this will only be set when it comes out of endpoint and goes to scheduler.
        
        pub trap_frame: TrapFrameOption,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct IPCPayLoad{
        pub message: Option<(VAddr,usize)>,
        pub page_payload: Option<(VAddr, usize)>,
        pub endpoint_payload: Option<EndpointIdx>,
        pub pci_payload: Option<(u8,u8,u8)>,
    }
    impl IPCPayLoad {
        pub fn new_to_none() -> (ret:Self)
            ensures
                ret.message.is_None(),
                ret.page_payload.is_None(),
                ret.endpoint_payload.is_None(),
                ret.pci_payload.is_None(),
        {
            Self{
                message: None,
                page_payload: None,
                endpoint_payload: None,
                pci_payload: None,
            }
        }
    }
}