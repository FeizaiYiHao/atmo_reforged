use vstd::prelude::*;
verus! {
use crate::kernel::Kernel;
use crate::define::*;
use crate::process_manager::process::Process;
use crate::process_manager::thread::Thread;
use crate::process_manager::container::Container;
use crate::process_manager::endpoint::Endpoint;
use crate::pagetable::entry::MapEntry;

impl Kernel{
    pub open spec fn proc_dom(&self) -> Set<ProcPtr>
    {
        self.proc_man.proc_dom()
    }

    pub open spec fn thread_dom(&self) -> Set<ThreadPtr>
    {
        self.proc_man.thread_dom()
    }

    pub open spec fn container_dom(&self) -> Set<ContainerPtr>
    {
        self.proc_man.container_dom()
    }

    pub open spec fn endpoint_dom(&self) -> Set<EndpointPtr>
    {
        self.proc_man.endpoint_dom()
    }

    pub open spec fn get_proc(&self, p_ptr:ProcPtr) -> &Process
        recommends
            self.wf(),
            self.proc_dom().contains(p_ptr)
    {
        self.proc_man.get_proc(p_ptr)
    }

    pub open spec fn get_thread(&self, t_ptr:ThreadPtr) -> &Thread
        recommends
            self.wf(),
            self.thread_dom().contains(t_ptr)
    {
        self.proc_man.get_thread(t_ptr)
    }

    pub open spec fn get_container(&self, c_ptr:ContainerPtr) -> &Container
        recommends
            self.wf(),
            self.container_dom().contains(c_ptr)
    {
        self.proc_man.get_container(c_ptr)
    }

    pub open spec fn get_endpoint(&self, e_ptr:EndpointPtr) -> &Endpoint
        recommends
            self.wf(),
            self.endpoint_dom().contains(e_ptr)
    {
        self.proc_man.get_endpoint(e_ptr)
    }

    pub open spec fn get_address_space(&self, p_ptr:ProcPtr) -> Map<VAddr,MapEntry>
        recommends
            self.wf(),
            self.proc_dom().contains(p_ptr),
    {
        self.mem_man.get_pagetable_mapping_by_pcid(self.get_proc(p_ptr).pcid)
    }

    pub open spec fn get_container_owned_pages(&self, c_ptr:ContainerPtr) -> Set<PagePtr>
        recommends
            self.wf(),
            self.container_dom().contains(c_ptr),
    {
        self.page_alloc.get_container_owned_pages(c_ptr)
    }
}
}