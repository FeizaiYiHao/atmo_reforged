pub open spec fn get_endpoint(&self, endpoint_ptr:EndpointPtr) -> &Endpoint
recommends
    self.wf(),
    self.endpoint_dom().contains(endpoint_ptr)
{
self.proc_man.get_endpoint(endpoint_ptr)
}