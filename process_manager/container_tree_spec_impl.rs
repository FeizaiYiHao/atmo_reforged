use vstd::prelude::*;
verus! {
    use crate::define::*;
    use crate::slinkedlist::spec_impl_u::*;
    use crate::array_set::*;
    use crate::process_manager::container::Container;
    use vstd::simple_pptr::PointsTo;

    pub struct ContainerTree{
        pub root_container: ContainerPtr,

        pub container_perms: Tracked<Map<ContainerPtr, PointsTo<Container>>>,
    }

    //specs
    impl ContainerTree{
        pub closed spec fn container_perms_wf(&self) -> bool{
            &&&
            forall|c_ptr:ContainerPtr| 
            #![trigger self.container_perms@.dom().contains(c_ptr)]
                self.container_perms@.dom().contains(c_ptr)
                ==> 
                self.container_perms@[c_ptr].is_init()
                &&            
                self.container_perms@[c_ptr].addr() == c_ptr
                &&
                self.container_perms@[c_ptr].value().children.wf()
                &&
                self.container_perms@[c_ptr].value().children.unique()
                &&
                self.container_perms@[c_ptr].value().owned_cpus.wf()
                &&
                self.container_perms@[c_ptr].value().scheduler.wf() 
                &&
                self.container_perms@[c_ptr].value().scheduler.unique() 
                &&
                self.container_perms@[c_ptr].value().owned_procs.wf()
                &&
                self.container_perms@[c_ptr].value().owned_procs.unique()
        }
    
        pub closed spec fn container_root_wf(&self) -> bool{
            &&&
            self.container_perms@.dom().contains(self.root_container)
            &&&
            self.container_perms@[self.root_container].value().depth == 0
            &&&
            forall|c_ptr:ContainerPtr| 
            #![trigger self.container_perms@.dom().contains(c_ptr)]
                self.container_perms@.dom().contains(c_ptr) && c_ptr != self.root_container 
                ==> 
                self.container_perms@[c_ptr].value().parent.is_Some()   
                &&
                self.container_perms@[c_ptr].value().depth != 0
            &&&
            forall|c_ptr:ContainerPtr| 
            #![trigger self.container_perms@.dom().contains(c_ptr)]
                self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().parent.is_Some()   
                ==> 
                c_ptr != self.root_container 
        }
    
        pub closed spec fn container_childern_list_wf(&self) -> bool{
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr)]
                self.container_perms@.dom().contains(c_ptr) 
                ==> 
                self.container_perms@[c_ptr].value().children@.to_set().subset_of(self.container_perms@.dom())
                &&
                self.container_perms@.dom().contains(c_ptr) ==> self.container_perms@[c_ptr].value().children@.contains(c_ptr) == false
            &&&
            forall|c_ptr:ContainerPtr, child_c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().children@.contains(child_c_ptr)]
                self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().children@.contains(child_c_ptr)
                ==> self.container_perms@.dom().contains(child_c_ptr)
                    &&
                    self.container_perms@[child_c_ptr].value().parent.unwrap() == c_ptr
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr)]
                self.container_perms@.dom().contains(c_ptr) && c_ptr != self.root_container 
                ==>
                self.container_perms@.dom().contains(self.container_perms@[c_ptr].value().parent.unwrap())
        }
    
        pub closed spec fn containers_linkedlist_wf(&self) -> bool{  
            &&&
            forall|c_ptr:ContainerPtr| 
            #![trigger self.container_perms@[c_ptr].value().parent]
                self.container_perms@.dom().contains(c_ptr) && c_ptr != self.root_container 
                ==> self.container_perms@[c_ptr].value().parent_rev_ptr.is_Some()
                    && self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children@.to_set().contains(c_ptr)
                    && self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children.node_ref_valid(self.container_perms@[c_ptr].value().parent_rev_ptr.unwrap())
                    && self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children.node_ref_resolve(self.container_perms@[c_ptr].value().parent_rev_ptr.unwrap()) == c_ptr
        }

        pub closed spec fn container_childern_depth_wf(&self) -> bool {
            &&&
            forall|c_ptr:ContainerPtr, child_c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().children@.contains(child_c_ptr)]
                #![trigger self.container_perms@[child_c_ptr].value().depth, self.container_perms@[c_ptr].value().depth]
                self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().children@.contains(child_c_ptr)
                ==> self.container_perms@.dom().contains(child_c_ptr)
                    &&
                    self.container_perms@[child_c_ptr].value().depth == self.container_perms@[c_ptr].value().depth + 1
        }

        pub closed spec fn container_subtree_set_wf(&self) -> bool{
            &&&
            forall|c_ptr:ContainerPtr|
                #![trigger self.container_perms@.dom().contains(c_ptr)]
                #![trigger self.container_perms@[c_ptr].value().subtree_set@.finite()]
                self.container_perms@.dom().contains(c_ptr)
                ==>
                self.container_perms@[c_ptr].value().subtree_set@.finite()
            &&&
            forall|c_ptr:ContainerPtr, sub_c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr)]
                self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr)
                ==>
                self.container_perms@[c_ptr].value().children@.contains(sub_c_ptr)
                ||
                (
                    exists|child_c_ptr:ContainerPtr|
                    #![trigger self.container_perms@[c_ptr].value().children@.contains(child_c_ptr)]
                    #![trigger self.container_perms@[child_c_ptr].value().children@.contains(sub_c_ptr)]
                    self.container_perms@[c_ptr].value().children@.contains(child_c_ptr) && self.container_perms@[child_c_ptr].value().subtree_set@.contains(sub_c_ptr) 
                )
            &&&
            forall|c_ptr:ContainerPtr, sub_c_ptr:ContainerPtr| 
                self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr)
                ==>
                self.container_perms@.dom().contains(sub_c_ptr)
            &&&
            forall|c_ptr:ContainerPtr, sub_c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr)]
                #![trigger self.container_perms@[sub_c_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int]]
                self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr)
                ==> 
                self.container_perms@[sub_c_ptr].value().uppertree_seq@.len() > self.container_perms@[c_ptr].value().depth
                &&
                self.container_perms@[sub_c_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int] == c_ptr
        }

        pub closed spec fn container_uppertree_seq_wf(&self) -> bool{
            &&&
            forall|c_ptr:ContainerPtr|
                #![trigger self.container_perms@.dom().contains(c_ptr)]
                #![trigger self.container_perms@[c_ptr].value().uppertree_seq]
                self.container_perms@.dom().contains(c_ptr)
                ==>
                self.container_perms@[c_ptr].value().uppertree_seq@.no_duplicates()
                &&
                self.container_perms@[c_ptr].value().uppertree_seq@.len() == self.container_perms@[c_ptr].value().depth
                &&
                self.container_perms@[c_ptr].value().uppertree_seq@.to_set().subset_of(self.container_perms@.dom())
            &&&
            forall|c_ptr:ContainerPtr, u_index:int|
                #![trigger self.container_perms@[c_ptr].value().uppertree_seq@[u_index as int]]
                self.container_perms@.dom().contains(c_ptr) && 0 <= u_index < self.container_perms@[c_ptr].value().depth
                ==>
                self.container_perms@[self.container_perms@[c_ptr].value().uppertree_seq@[u_index as int]].value().depth == u_index
                &&
                self.container_perms@[self.container_perms@[c_ptr].value().uppertree_seq@[u_index as int]].value().subtree_set@.contains(c_ptr)
            &&&
            forall|c_ptr:ContainerPtr|
                #![trigger self.container_perms@[c_ptr].value().uppertree_seq]
                #![trigger self.container_perms@[c_ptr].value().parent]
                self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().depth != 0
                ==>
                self.container_perms@[c_ptr].value().uppertree_seq@ =~= self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().uppertree_seq@.push(self.container_perms@[c_ptr].value().parent.unwrap())
        }

        pub closed spec fn container_subtree_set_exclusive(&self) -> bool{
            &&&
            forall|c_ptr:ContainerPtr, sub_c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@.dom().contains(sub_c_ptr) ]
                #![trigger self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr)]
                #![trigger self.container_perms@[sub_c_ptr].value().uppertree_seq@.contains(c_ptr)]
                self.container_perms@.dom().contains(c_ptr) 
                && 
                self.container_perms@.dom().contains(sub_c_ptr) 
                ==> 
                (
                    self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr) == false
                    <==>
                    self.container_perms@[sub_c_ptr].value().uppertree_seq@.contains(c_ptr) == false
                )
        }
    
    }
}
