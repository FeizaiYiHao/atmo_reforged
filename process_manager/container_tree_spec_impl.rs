use vstd::prelude::*;
verus! {
    use crate::define::*;
    use crate::slinkedlist::spec_impl_u::*;
    use crate::array_set::*;
    use crate::process_manager::container::Container;
    use vstd::simple_pptr::*;
    use crate::lemma::lemma_u::*;
    use crate::lemma::lemma_t::*;
    use crate::process_manager::container_util_t::*;

    pub struct ContainerTree{
        pub root_container: ContainerPtr,

        pub container_perms: Tracked<Map<ContainerPtr, PointsTo<Container>>>,
    }

    //specs
    impl ContainerTree{
        pub closed spec fn container_perms_wf(&self) -> bool{
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].is_init()]
                self.container_perms@.dom().contains(c_ptr)
                ==> 
                self.container_perms@[c_ptr].is_init()
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].addr()]
                self.container_perms@.dom().contains(c_ptr)
                ==>        
                self.container_perms@[c_ptr].addr() == c_ptr
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().children.wf()]
                self.container_perms@.dom().contains(c_ptr)
                ==> 
                self.container_perms@[c_ptr].value().children.wf()
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().children.unique()]
                self.container_perms@.dom().contains(c_ptr)
                ==> 
                self.container_perms@[c_ptr].value().children.unique()
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().owned_cpus.wf()]
                self.container_perms@.dom().contains(c_ptr)
                ==> 
                self.container_perms@[c_ptr].value().owned_cpus.wf()
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().scheduler.wf() ]
                self.container_perms@.dom().contains(c_ptr)
                ==> 
                self.container_perms@[c_ptr].value().scheduler.wf() 
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().scheduler.unique()]
                self.container_perms@.dom().contains(c_ptr)
                ==> 
                self.container_perms@[c_ptr].value().scheduler.unique() 
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().owned_procs.wf()]
                self.container_perms@.dom().contains(c_ptr)
                ==> 
                self.container_perms@[c_ptr].value().owned_procs.wf()
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().owned_procs.unique()]
                self.container_perms@.dom().contains(c_ptr)
                ==> 
                self.container_perms@[c_ptr].value().owned_procs.unique()
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().uppertree_seq@.no_duplicates()]
                self.container_perms@.dom().contains(c_ptr)
                ==> 
                self.container_perms@[c_ptr].value().uppertree_seq@.no_duplicates()
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().children@.contains(c_ptr)]
                self.container_perms@.dom().contains(c_ptr)
                ==>
                self.container_perms@[c_ptr].value().children@.contains(c_ptr) == false
                &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().subtree_set@.finite()]
                self.container_perms@.dom().contains(c_ptr)
                ==>
                self.container_perms@[c_ptr].value().subtree_set@.finite()
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().uppertree_seq@.len(), self.container_perms@[c_ptr].value().depth]
                self.container_perms@.dom().contains(c_ptr)
                ==>
                self.container_perms@[c_ptr].value().uppertree_seq@.len() == self.container_perms@[c_ptr].value().depth    
        }
    
        pub closed spec fn container_root_wf(&self) -> bool{
            &&&
            self.container_perms@.dom().contains(self.root_container)
            &&&
            self.container_perms@[self.root_container].value().depth == 0
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().depth ]
                self.container_perms@.dom().contains(c_ptr) 
                &&
                c_ptr != self.root_container 
                ==>
                self.container_perms@[c_ptr].value().depth != 0
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().parent.is_Some() ]
                self.container_perms@.dom().contains(c_ptr) 
                &&
                c_ptr != self.root_container 
                ==>
                self.container_perms@[c_ptr].value().parent.is_Some()  
        }
    
        pub closed spec fn container_childern_list_wf(&self) -> bool{
            &&&
            forall|c_ptr:ContainerPtr, child_c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().children@.contains(child_c_ptr), self.container_perms@[child_c_ptr].value().depth, self.container_perms@[c_ptr].value().depth]
                #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().children@.contains(child_c_ptr), self.container_perms@.dom().contains(child_c_ptr)]
                #![trigger self.container_perms@[c_ptr].value().children@.contains(child_c_ptr), self.container_perms@[child_c_ptr].value().parent.unwrap()]
               //  #![auto]
                self.container_perms@.dom().contains(c_ptr) 
                && 
                self.container_perms@[c_ptr].value().children@.contains(child_c_ptr)
                ==> self.container_perms@.dom().contains(child_c_ptr)
                    &&
                    self.container_perms@[child_c_ptr].value().parent.unwrap() == c_ptr
                    &&
                    self.container_perms@[child_c_ptr].value().depth == self.container_perms@[c_ptr].value().depth + 1
        }
    
        pub closed spec fn containers_linkedlist_wf(&self) -> bool{  
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(self.container_perms@[c_ptr].value().parent.unwrap())]
                self.container_perms@.dom().contains(c_ptr) && c_ptr != self.root_container 
                ==> 
                self.container_perms@.dom().contains(self.container_perms@[c_ptr].value().parent.unwrap())
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().parent_rev_ptr.is_Some()]
                #![trigger self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children@.contains(c_ptr)]
                #![trigger self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children.node_ref_valid(self.container_perms@[c_ptr].value().parent_rev_ptr.unwrap())]
                #![trigger self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children.node_ref_resolve(self.container_perms@[c_ptr].value().parent_rev_ptr.unwrap())]
                self.container_perms@.dom().contains(c_ptr) && c_ptr != self.root_container 
                ==> 
                self.container_perms@[c_ptr].value().parent_rev_ptr.is_Some()
                &&
                self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children@.contains(c_ptr)
                && 
                self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children.node_ref_valid(self.container_perms@[c_ptr].value().parent_rev_ptr.unwrap())
                && 
                self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children.node_ref_resolve(self.container_perms@[c_ptr].value().parent_rev_ptr.unwrap()) == c_ptr
        }

        pub closed spec fn container_childern_depth_wf(&self) -> bool {
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth - 1]]
                self.container_perms@.dom().contains(c_ptr) && c_ptr != self.root_container
                ==>
                self.container_perms@[c_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth - 1] == self.container_perms@[c_ptr].value().parent.unwrap()
        }

        pub closed spec fn container_subtree_set_wf(&self) -> bool{
            &&&
            forall|c_ptr:ContainerPtr, sub_c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr), self.container_perms@[sub_c_ptr].value().uppertree_seq@.len(), self.container_perms@[c_ptr].value().depth]
                #![trigger self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr), self.container_perms@[sub_c_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int]]
                #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr), self.container_perms@.dom().contains(sub_c_ptr)]
                self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr)
                ==> 
                self.container_perms@.dom().contains(sub_c_ptr)
                &&
                self.container_perms@[sub_c_ptr].value().uppertree_seq@.len() > self.container_perms@[c_ptr].value().depth
                &&
                self.container_perms@[sub_c_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int] == c_ptr
        }

        pub closed spec fn container_uppertree_seq_wf(&self) -> bool{
            &&&
            forall|c_ptr:ContainerPtr, u_ptr:ContainerPtr|
                #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().uppertree_seq@.contains(u_ptr), self.container_perms@.dom().contains(u_ptr)]
                #![trigger self.container_perms@[c_ptr].value().uppertree_seq@.subrange(0, self.container_perms@[u_ptr].value().depth as int)]
                #![trigger self.container_perms@[c_ptr].value().uppertree_seq@.index_of(u_ptr)]
                self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().uppertree_seq@.contains(u_ptr)
                ==>
                self.container_perms@.dom().contains(u_ptr)
                &&
                self.container_perms@[c_ptr].value().uppertree_seq@[self.container_perms@[u_ptr].value().depth as int] == u_ptr
                &&
                self.container_perms@[u_ptr].value().depth == self.container_perms@[c_ptr].value().uppertree_seq@.index_of(u_ptr)
                &&
                self.container_perms@[u_ptr].value().subtree_set@.contains(c_ptr)
                &&
                self.container_perms@[u_ptr].value().uppertree_seq@ =~= self.container_perms@[c_ptr].value().uppertree_seq@.subrange(0, self.container_perms@[u_ptr].value().depth as int)
        }

        pub closed spec fn container_subtree_set_exclusive(&self) -> bool{
            &&&
            forall|c_ptr:ContainerPtr, sub_c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr), self.container_perms@[sub_c_ptr].value().uppertree_seq@.contains(c_ptr)]
                self.container_perms@.dom().contains(c_ptr) 
                && 
                self.container_perms@.dom().contains(sub_c_ptr) 
                ==> 
                (
                    self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr)
                    ==
                    self.container_perms@[sub_c_ptr].value().uppertree_seq@.contains(c_ptr)
                )
        }

        pub open spec fn tree_wf(&self) -> bool{
            &&&
            self.container_subtree_set_wf()
            &&&
            self.container_uppertree_seq_wf()
        }

        pub open spec fn linked_list_wf(&self) -> bool{
            &&&
            self.container_childern_list_wf()
            &&&
            self.containers_linkedlist_wf()
        }
        
        pub open spec fn rest_specs(&self) -> bool{
            &&&
            self.container_perms_wf()
            &&&
            self.container_root_wf()
            &&&
            self.container_childern_depth_wf()
            &&&
            self.container_subtree_set_exclusive()
        }

        pub open spec fn wf(&self) -> bool{
            &&&
            self.container_perms_wf()
            &&&
            self.container_root_wf()
            &&&
            self.container_childern_list_wf()
            &&&
            self.containers_linkedlist_wf()
            &&&
            self.container_childern_depth_wf()
            &&&
            self.container_subtree_set_wf()
            &&&
            self.container_uppertree_seq_wf()
            &&&
            self.container_subtree_set_exclusive()
        }
    }

    //proof
    impl ContainerTree{
        pub proof fn same_or_deeper_depth_imply_none_ancestor(&self, a_ptr:ContainerPtr, child_ptr:ContainerPtr)
            requires
                self.wf(),
                self.container_perms@.dom().contains(a_ptr),
                self.container_perms@.dom().contains(child_ptr),
                self.container_perms@[a_ptr].value().depth >= self.container_perms@[child_ptr].value().depth,
            ensures
                self.container_perms@[a_ptr].value().subtree_set@.contains(child_ptr) == false
        {
            assert(self.container_perms@[a_ptr].value().uppertree_seq@.len() == self.container_perms@[a_ptr].value().depth);
            assert(self.container_perms@[child_ptr].value().uppertree_seq@.len() == self.container_perms@[child_ptr].value().depth);
        }

        pub proof fn no_child_imply_no_subtree(&self, c_ptr:ContainerPtr)
            requires
                self.wf(),
                self.container_perms@.dom().contains(c_ptr),
                self.container_perms@[c_ptr].value().children@ =~= Seq::empty(),
            ensures
                self.container_perms@[c_ptr].value().subtree_set@ =~= Set::empty(),
        {
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.contains(c_ptr));
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.subrange(0,self.container_perms@[c_ptr].value().depth as int) == self.container_perms@[c_ptr].value().uppertree_seq@);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> s_ptr != self.root_container);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().parent.unwrap() != c_ptr);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[s_ptr].value().depth - 1] != c_ptr);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int] == c_ptr);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.len() > self.container_perms@[c_ptr].value().depth);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.len() != self.container_perms@[c_ptr].value().depth + 1);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]));
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@.dom().contains(s_ptr));
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@.dom().contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]));
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]));
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.subrange(0,self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().depth as int) 
                    =~= 
                    self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.no_duplicates());
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.index_of(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]) == self.container_perms@[c_ptr].value().depth + 1);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().depth == self.container_perms@[c_ptr].value().depth + 1);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int] == c_ptr);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@[
                    self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().depth - 1] == c_ptr);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().parent.unwrap() == c_ptr);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[c_ptr].value().children@.contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]));
        }

        pub proof fn in_child_impy_in_subtree(&self, c_ptr:ContainerPtr, child_ptr:ContainerPtr, s_ptr:ContainerPtr)
            requires
                self.wf(),
                self.container_perms@.dom().contains(c_ptr),
                self.container_perms@[c_ptr].value().children@.contains(child_ptr),
                self.container_perms@[child_ptr].value().subtree_set@.contains(s_ptr),
            ensures
                self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr),
        {
            assert(self.container_perms@[child_ptr].value().parent.unwrap() == c_ptr);
            assert(self.container_perms@[child_ptr].value().depth == self.container_perms@[c_ptr].value().depth + 1);
            assert(self.container_perms@[child_ptr].value().uppertree_seq@.len() == self.container_perms@[child_ptr].value().depth);
            assert(self.container_perms@[c_ptr].value().uppertree_seq@.len() == self.container_perms@[c_ptr].value().depth);
            assert(self.container_perms@[child_ptr].value().uppertree_seq@[self.container_perms@[child_ptr].value().depth - 1] == c_ptr);
            assert(self.container_perms@[s_ptr].value().uppertree_seq@.subrange(0, self.container_perms@[child_ptr].value().depth as int) == self.container_perms@[child_ptr].value().uppertree_seq@);
            assert(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int] == c_ptr);
            assert(self.container_perms@[s_ptr].value().uppertree_seq@.contains(c_ptr));
        }

        pub proof fn in_subtree_imply_exist_in_child(&self, c_ptr:ContainerPtr, s_ptr:ContainerPtr)
            requires
                self.wf(),
                self.container_perms@.dom().contains(c_ptr),
                self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr),
            ensures
                self.container_perms@[c_ptr].value().children@.contains(s_ptr) 
                || 
                (exists|child_ptr:ContainerPtr| 
                    #![auto]
                    self.container_perms@[c_ptr].value().children@.contains(child_ptr) && self.container_perms@[child_ptr].value().subtree_set@.contains(s_ptr)),
        {
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    self.container_perms@[s_ptr].value().uppertree_seq@.subrange(0,self.container_perms@[c_ptr].value().depth as int) == self.container_perms@[c_ptr].value().uppertree_seq@
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    s_ptr != self.root_container
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    self.container_perms@[s_ptr].value().parent.unwrap() != c_ptr
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    self.container_perms@[s_ptr].value().uppertree_seq@.len() > self.container_perms@[c_ptr].value().depth
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[s_ptr].value().depth - 1] != c_ptr
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int] == c_ptr
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    self.container_perms@[s_ptr].value().uppertree_seq@.len() > self.container_perms@[c_ptr].value().depth
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    self.container_perms@[s_ptr].value().uppertree_seq@.len() != self.container_perms@[c_ptr].value().depth + 1
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    self.container_perms@[s_ptr].value().uppertree_seq@.len() > self.container_perms@[c_ptr].value().depth + 1
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[s_ptr].value().uppertree_seq@.contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]));
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@.dom().contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1])
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[s_ptr].value().uppertree_seq@.subrange(0,self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().depth as int) 
                    =~= self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[s_ptr].value().uppertree_seq@.no_duplicates()
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[s_ptr].value().uppertree_seq@.index_of(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]) == self.container_perms@[c_ptr].value().depth + 1
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().depth == self.container_perms@[c_ptr].value().depth + 1
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@.len() == self.container_perms@[c_ptr].value().depth + 1
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int] == c_ptr
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@[
                    self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().depth - 1] == c_ptr
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().parent.unwrap() == c_ptr
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[c_ptr].value().children@.contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1])
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().subtree_set@.contains(s_ptr)
            );
            assert(                
                self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                (exists|child_ptr:ContainerPtr| 
                #![auto]
                self.container_perms@[c_ptr].value().children@.contains(child_ptr) && self.container_perms@[child_ptr].value().subtree_set@.contains(s_ptr)
                )
            );
        }

        pub proof fn not_in_dom_imply_not_in_any_children_set(&self, s_ptr:ContainerPtr)
            requires
                self.wf(),
                self.container_perms@.dom().contains(s_ptr) == false,
        {
            assert(
                forall|c_ptr:ContainerPtr|
                    #![auto]
                    self.container_perms@.dom().contains(c_ptr)
                    ==>
                    self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false
            );
        }
                
    }

    //exec
    impl ContainerTree{
        pub fn check_is_ancestor(&self, a_ptr:ContainerPtr, child_ptr:ContainerPtr) -> (ret:bool)
            requires
                self.wf(),
                self.container_perms@.dom().contains(a_ptr),
                self.container_perms@.dom().contains(child_ptr),
                self.container_perms@[a_ptr].value().depth < self.container_perms@[child_ptr].value().depth,
                child_ptr != self.root_container,
            ensures
                ret == self.container_perms@[child_ptr].value().uppertree_seq@.contains(a_ptr)
        {
            // assert(false);
            proof{
                seq_push_lemma::<ContainerPtr>();
            }
            assert(self.container_perms@[child_ptr].value().parent.is_Some());
            let tracked child_perm = self.container_perms.borrow().tracked_borrow(child_ptr);
            let child : &Container = PPtr::<Container>::from_usize(child_ptr).borrow(Tracked(child_perm));
            let mut current_parent_ptr = child.parent.unwrap();
            let mut depth = child.depth;
            assert(current_parent_ptr == self.container_perms@[child_ptr].value().uppertree_seq@[depth - 1]);

            if current_parent_ptr == a_ptr{
                return true;
            }

            while depth != 1
                invariant
                    1 <= depth <= self.container_perms@[child_ptr].value().depth,
                    self.wf(),
                    self.container_perms@.dom().contains(a_ptr),
                    self.container_perms@.dom().contains(child_ptr),
                    self.container_perms@[a_ptr].value().depth < self.container_perms@[child_ptr].value().depth,
                    child_ptr != self.root_container,
                    current_parent_ptr == self.container_perms@[child_ptr].value().uppertree_seq@[depth - 1],
                    forall|i:int|
                       //  #![auto]
                        depth - 1 <= i < self.container_perms@[child_ptr].value().depth ==> self.container_perms@[child_ptr].value().uppertree_seq@[i] != a_ptr,
                    ensures
                        depth == 1,
                        forall|i:int|
                           //  #![auto]
                            0 <= i < self.container_perms@[child_ptr].value().depth ==> self.container_perms@[child_ptr].value().uppertree_seq@[i] != a_ptr,
            {
                assert(self.container_perms@[child_ptr].value().uppertree_seq@.contains(current_parent_ptr));
                assert(self.container_perms@.dom().contains(current_parent_ptr));
                assert(self.container_perms@[child_ptr].value().uppertree_seq@.no_duplicates());
                assert(self.container_perms@[child_ptr].value().uppertree_seq@.index_of(current_parent_ptr) == depth - 1);
                assert(self.container_perms@[current_parent_ptr].value().depth == depth - 1);
                assert(self.container_perms@[current_parent_ptr].value().parent.is_Some());
                let tracked current_parent_perm = self.container_perms.borrow().tracked_borrow(current_parent_ptr);
                assert(current_parent_perm.addr() == current_parent_ptr);
                let current_parent : &Container = PPtr::<Container>::from_usize(current_parent_ptr).borrow(Tracked(current_parent_perm));
                let current_parent_ptr_tmp = current_parent.parent.unwrap();
                if current_parent_ptr_tmp == a_ptr{
                    assert(self.container_perms@[current_parent_ptr].value().uppertree_seq@[depth - 1 - 1] == current_parent_ptr_tmp);
                    return true;
                }
                assert(self.container_perms@[current_parent_ptr].value().uppertree_seq@[depth - 1 - 1] == current_parent_ptr_tmp);
                current_parent_ptr = current_parent_ptr_tmp;
                depth = depth - 1;
            }
            false
        }

        #[verifier(external_body)]
        pub fn upper_tree_add_container(&mut self, seq:Ghost<Seq<ContainerPtr>>, subchild_ptr:ContainerPtr)
            requires
                forall|c_ptr:ContainerPtr|
                #![trigger seq@.contains(c_ptr)] 
                seq@.contains(c_ptr) ==> old(self).container_perms@.dom().contains(c_ptr)
            ensures
                self.root_container == old(self).root_container,
                old(self).container_perms@.dom() == self.container_perms@.dom(),
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@[c_ptr]] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) == false 
                    ==> 
                    self.container_perms@[c_ptr] =~= old(self).container_perms@[c_ptr],
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@[c_ptr].is_init()] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) 
                    ==>
                    self.container_perms@[c_ptr].is_init(),
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@[c_ptr].addr()] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) 
                    ==>           
                    self.container_perms@[c_ptr].addr() == old(self).container_perms@[c_ptr].addr(),
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@[c_ptr].value().owned_procs] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) 
                    ==>
                    self.container_perms@[c_ptr].value().owned_procs =~= old(self).container_perms@[c_ptr].value().owned_procs,
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@[c_ptr].value().parent] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) 
                    ==>
                    self.container_perms@[c_ptr].value().parent =~= old(self).container_perms@[c_ptr].value().parent,
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@[c_ptr].value().parent_rev_ptr] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) 
                    ==>
                    self.container_perms@[c_ptr].value().parent_rev_ptr =~= old(self).container_perms@[c_ptr].value().parent_rev_ptr,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().children] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) 
                    ==>
                    self.container_perms@[c_ptr].value().children =~= old(self).container_perms@[c_ptr].value().children,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().owned_endpoints] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) 
                    ==>
                    self.container_perms@[c_ptr].value().owned_endpoints =~= old(self).container_perms@[c_ptr].value().owned_endpoints,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().mem_quota] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) 
                    ==>
                    self.container_perms@[c_ptr].value().mem_quota =~= old(self).container_perms@[c_ptr].value().mem_quota,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().mem_used] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) 
                    ==>
                    self.container_perms@[c_ptr].value().mem_used =~= old(self).container_perms@[c_ptr].value().mem_used,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().owned_cpus] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) 
                    ==>
                    self.container_perms@[c_ptr].value().owned_cpus =~= old(self).container_perms@[c_ptr].value().owned_cpus,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().scheduler] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) 
                    ==>
                    self.container_perms@[c_ptr].value().scheduler =~= old(self).container_perms@[c_ptr].value().scheduler,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().owned_threads] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) 
                    ==>
                    self.container_perms@[c_ptr].value().owned_threads =~= old(self).container_perms@[c_ptr].value().owned_threads,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().depth] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) 
                    ==>
                    self.container_perms@[c_ptr].value().depth =~= old(self).container_perms@[c_ptr].value().depth,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().uppertree_seq] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) 
                    ==>
                    self.container_perms@[c_ptr].value().uppertree_seq =~= old(self).container_perms@[c_ptr].value().uppertree_seq,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().subtree_set@] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) 
                    ==>
                    self.container_perms@[c_ptr].value().subtree_set@ =~= old(self).container_perms@[c_ptr].value().subtree_set@.insert(subchild_ptr),
        {}

        pub fn new_container(&mut self, container_ptr:ContainerPtr, new_quota:usize, page_ptr_1: PagePtr, page_perm_1: Tracked<PagePerm4k>, first_proc_ptr:ProcPtr, first_thread_ptr:ThreadPtr)
            requires
                old(self).wf(),
                old(self).container_perms@.dom().contains(container_ptr),
                old(self).container_perms@.dom().contains(page_ptr_1) == false,
                old(self).container_perms@[container_ptr].value().children.len() < CONTAINER_CHILD_LIST_LEN,
                old(self).container_perms@[container_ptr].value().depth < usize::MAX,
                page_perm_1@.is_init(),
                page_perm_1@.addr() == page_ptr_1,
            ensures
                self.wf(),   
        {
            let tracked container_perm = self.container_perms.borrow().tracked_borrow(container_ptr);
            let container : &Container = PPtr::<Container>::from_usize(container_ptr).borrow(Tracked(container_perm));
            let depth = container.depth;
            let uppertree_seq = container.uppertree_seq;

            let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));
            let child_list_node_ref = container_push_child(container_ptr,&mut container_perm, page_ptr_1);
            proof {
                self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
            }

            let (proc_list_node_ref, scheduler_node_ref, new_container_ptr, container_perm) = 
                page_to_container_tree_version(page_ptr_1, page_perm_1, first_proc_ptr, container_ptr, child_list_node_ref, new_quota, ArraySet::<NUM_CPUS>::new(), first_thread_ptr,
                    depth + 1, Ghost(Set::<ContainerPtr>::empty()), Ghost(uppertree_seq@.push(container_ptr))
                    // depth + 1, Ghost(Set::<ContainerPtr>::empty()), uppertree_seq
                    );
            proof {
                self.container_perms.borrow_mut().tracked_insert(new_container_ptr, container_perm.get());
            }

            assert(
                forall|u_ptr:ContainerPtr|
                #![trigger self.container_perms@[container_ptr].value().uppertree_seq@.contains(u_ptr)]
                self.container_perms@[container_ptr].value().uppertree_seq@.push(container_ptr).contains(u_ptr)
                ==>
                self.container_perms@.dom().contains(u_ptr)
            ) by {
                seq_push_lemma::<ContainerPtr>();
            };
            assert(uppertree_seq@.push(container_ptr) =~= self.container_perms@[container_ptr].value().uppertree_seq@.push(container_ptr));
            assert(
                forall|u_ptr:ContainerPtr|
                #![trigger uppertree_seq@.push(container_ptr).contains(u_ptr)]
                uppertree_seq@.push(container_ptr).contains(u_ptr)
                ==>
                self.container_perms@.dom().contains(u_ptr)
            ) by {
                seq_push_lemma::<ContainerPtr>();
            };


            self.upper_tree_add_container(Ghost(uppertree_seq@.push(container_ptr)), new_container_ptr);
            // self.upper_tree_add_container(uppertree_seq, new_container_ptr);
            
                assert(uppertree_seq@.contains(container_ptr) == false);
                assert(uppertree_seq@.contains(new_container_ptr) == false);
                assert(uppertree_seq@.push(container_ptr).contains(container_ptr)) by {
                    seq_push_lemma::<ContainerPtr>();
                }
                assert(uppertree_seq@.push(container_ptr).contains(new_container_ptr) == false) by {
                    seq_push_lemma::<ContainerPtr>();
                }
                assert(uppertree_seq@.push(container_ptr).no_duplicates()) by {
                    seq_push_lemma::<ContainerPtr>();
                    seq_push_unique_lemma::<ContainerPtr>();
                }

            assert(self.rest_specs()) by {
                assert(self.container_perms_wf()) by {
                    seq_push_unique_lemma::<ContainerPtr>();
                    seq_push_lemma::<ContainerPtr>();
                    assert(forall|c_ptr:ContainerPtr| 
                        #![trigger self.container_perms@[c_ptr].value().uppertree_seq]
                        self.container_perms@.dom().contains(c_ptr) && c_ptr != new_container_ptr
                        ==> 
                        self.container_perms@[c_ptr].value().uppertree_seq@ =~= old(self).container_perms@[c_ptr].value().uppertree_seq@);
                };
                assert(self.container_root_wf()) by {
                };
                assert(self.container_childern_depth_wf()) by {
                    seq_push_lemma::<ContainerPtr>();
                    
                    assert(forall|c_ptr:ContainerPtr| 
                        #![trigger self.container_perms@[c_ptr].value().uppertree_seq@]
                        #![trigger self.container_perms@[c_ptr].value().parent]
                        #![trigger self.container_perms@[c_ptr].value().depth]
                        self.container_perms@.dom().contains(c_ptr) && c_ptr != self.root_container && c_ptr != new_container_ptr
                        ==>
                        self.container_perms@[c_ptr].value().uppertree_seq@ =~= old(self).container_perms@[c_ptr].value().uppertree_seq@
                        &&
                        self.container_perms@[c_ptr].value().parent == old(self).container_perms@[c_ptr].value().parent
                        &&
                        self.container_perms@[c_ptr].value().depth == old(self).container_perms@[c_ptr].value().depth
                    );
                };
                assert(self.container_subtree_set_exclusive())by {
                    seq_push_lemma::<ContainerPtr>();
                    seq_push_unique_lemma::<ContainerPtr>();
                };
            }
            assert(self.tree_wf()) by {
                assert(self.container_subtree_set_wf()) by {
                    seq_push_lemma::<ContainerPtr>();
                    seq_push_unique_lemma::<ContainerPtr>();
                };
                assert(self.container_uppertree_seq_wf()) by {
                    seq_push_lemma::<ContainerPtr>();
                    seq_push_unique_lemma::<ContainerPtr>();
                };
            }

            assert(self.linked_list_wf()) by {
                assert(self.container_childern_list_wf()) by {
                    seq_push_lemma::<ContainerPtr>();
                };
                assert(self.containers_linkedlist_wf()) by {
                    seq_push_lemma::<ContainerPtr>();
                };
            }
        }
    }
}
