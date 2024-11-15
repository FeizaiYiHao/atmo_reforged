use vstd::prelude::*;
verus! {
    use crate::trap::*;
    use crate::define::*;
    use crate::array::*;
    use crate::va_range::VaRange4K;

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
        pub ipc_payload: IPCPayLoad,
        
        pub error_code: Option<RetValueType>, //this will only be set when it comes out of endpoint and goes to scheduler.
        
        pub trap_frame: TrapFrameOption,
    }

    #[derive(Clone, Copy)]
    #[allow(inconsistent_fields)]
    pub enum IPCPayLoad{
        Message{va:VAddr,len:usize},
        Pages{va_range: VaRange4K},
        Endpoint{endpoint_index:EndpointIdx},
        Pci{bus:u8,dev:u8,fun:u8},
        Empty,
    }
    impl IPCPayLoad {
        pub open spec fn is_Some(&self) -> bool{
            match self {
                IPCPayLoad::Empty => false,
                _ => true,
            } 
        }
        pub open spec fn is_None(&self) -> bool{
            match self {
                IPCPayLoad::Empty => true,
                _ => false,
            } 
        }
        pub open spec fn spec_get_payload_as_message(&self) -> Option<(VAddr, usize)>{
            match self {
                IPCPayLoad::Message{va: va, len:len} => Some((*va,*len)),
                _ => None,
            } 
        }

        #[verifier(when_used_as_spec(spec_get_payload_as_message))]
        pub fn get_payload_as_message(&self) -> (ret:Option<(VAddr, usize)>)
            ensures
                ret == self.spec_get_payload_as_message(),
        {
            match self {
                IPCPayLoad::Message{va: va, len:len} => Some((*va,*len)),
                _ => None,
            }
        }

        pub open spec fn spec_get_payload_as_va_range(&self) -> Option<VaRange4K>{
            match self {
                IPCPayLoad::Pages{va_range: va_range} => Some(*va_range),
                _ => None,
            } 
        }

        #[verifier(when_used_as_spec(spec_get_payload_as_va_range))]
        pub fn get_payload_as_va_range(&self) -> (ret:Option<VaRange4K>)
            ensures
                ret == self.spec_get_payload_as_va_range(),
        {
            match self {
                IPCPayLoad::Pages{va_range: va_range} => Some(*va_range),
                _ => None,
            } 
        }

        pub open spec fn spec_get_payload_as_endpoint(&self) -> Option<EndpointIdx>{
            match self {
                IPCPayLoad::Endpoint{endpoint_index: endpoint_index} => Some(*endpoint_index),
                _ => None,
            } 
        }

        #[verifier(when_used_as_spec(spec_get_payload_as_endpoint))]
        pub fn get_payload_as_endpoint(&self) -> (ret:Option<EndpointIdx>)
            ensures
                ret == self.spec_get_payload_as_endpoint(),
        {
            match self {
                IPCPayLoad::Endpoint{endpoint_index: endpoint_index} => Some(*endpoint_index),
                _ => None,
            } 
        }
        pub open spec fn spec_get_payload_as_pci(&self) -> Option<(u8,u8,u8)>{
            match self {
                IPCPayLoad::Pci{bus:bus,dev:dev,fun:fun} => Some((*bus,*dev,*fun)),
                _ => None,
            } 
        }

        #[verifier(when_used_as_spec(spec_get_payload_as_pci))]
        pub fn get_payload_as_pci(&self) -> (ret:Option<(u8,u8,u8)>)
            ensures
                ret == self.spec_get_payload_as_pci(),
        {
            match self {
                IPCPayLoad::Pci{bus:bus,dev:dev,fun:fun} => Some((*bus,*dev,*fun)),
                _ => None,
            } 
        }
        
    }
}