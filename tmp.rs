assert(self.cpus_wf());
assert(self.container_cpu_wf());
assert(self.memory_disjoint());
assert(self.container_perms_wf());
assert(self.container_root_wf());
assert(self.container_tree_wf());
assert(self.containers_linkedlist_wf());
assert(self.processes_container_wf());
assert(self.processes_wf());
assert(self.threads_process_wf());
assert(self.threads_perms_wf());
assert(self.endpoint_perms_wf());
assert(self.threads_endpoint_descriptors_wf());
assert(self.endpoints_queue_wf());
assert(self.endpoints_container_wf());
assert(self.schedulers_wf());