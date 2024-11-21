use vstd::prelude::*;
verus! {
    use crate::define::*;
    use crate::slinkedlist::spec_impl_u::*;
    use crate::array_set::*;
    use crate::process_manager::container::Container;
    use vstd::simple_pptr::*;
    use crate::lemma::lemma_u::seq_push_lemma;

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
            #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().parent]
            #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().depth]
                self.container_perms@.dom().contains(c_ptr) && c_ptr != self.root_container 
                ==> 
                self.container_perms@[c_ptr].value().parent.is_Some()   
                &&
                self.container_perms@[c_ptr].value().depth != 0
            &&&
            forall|c_ptr:ContainerPtr| 
            #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().parent]
                self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().parent.is_Some()   
                ==> 
                c_ptr != self.root_container 
        }
    
        pub closed spec fn container_childern_list_wf(&self) -> bool{
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().children]
                self.container_perms@.dom().contains(c_ptr) 
                ==> 
                // self.container_perms@[c_ptr].value().children@.to_set().subset_of(self.container_perms@.dom())
                // &&
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
                #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().parent]
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
                // #![trigger self.container_perms@[c_ptr].value().children@.contains(child_c_ptr)]
                // #![trigger self.container_perms@[child_c_ptr].value().depth, self.container_perms@[c_ptr].value().depth]
                #![trigger self.container_perms@[c_ptr].value().children@.contains(child_c_ptr), self.container_perms@[child_c_ptr].value().depth, self.container_perms@[c_ptr].value().depth]
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
            // &&&
            // forall|c_ptr:ContainerPtr, sub_c_ptr:ContainerPtr| 
            //     #![trigger self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr), self.container_perms@[c_ptr].value().children@.contains(sub_c_ptr)]
            //     self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr)
            //     ==>
            //     self.container_perms@[c_ptr].value().children@.contains(sub_c_ptr)
            //     ||
            //     (
            //         exists|child_c_ptr:ContainerPtr|
            //         #![trigger self.container_perms@[c_ptr].value().children@.contains(child_c_ptr)]
            //         #![trigger self.container_perms@[child_c_ptr].value().children@.contains(sub_c_ptr)]
            //         self.container_perms@[c_ptr].value().children@.contains(child_c_ptr) && self.container_perms@[child_c_ptr].value().subtree_set@.contains(sub_c_ptr) 
            //     )
            &&&
            forall|c_ptr:ContainerPtr, sub_c_ptr:ContainerPtr| 
            #![trigger self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr)]
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
                // #![trigger self.container_perms@.dom().contains(c_ptr)]
                #![trigger self.container_perms@[c_ptr].value().uppertree_seq@.len(), self.container_perms@[c_ptr].value().depth]
                #![trigger self.container_perms@[c_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth - 1]]
                self.container_perms@.dom().contains(c_ptr)
                ==>
                self.container_perms@[c_ptr].value().uppertree_seq@.len() == self.container_perms@[c_ptr].value().depth
                &&
                (self.container_perms@[c_ptr].value().depth != 0 ==> self.container_perms@[c_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth - 1] == self.container_perms@[c_ptr].value().parent.unwrap())
            &&&
            forall|c_ptr:ContainerPtr, u_index:int|
                // #![trigger self.container_perms@[c_ptr].value().uppertree_seq@[u_index as int]]
                #![trigger self.container_perms@.dom().contains(self.container_perms@[c_ptr].value().uppertree_seq@[u_index as int])]
                #![trigger self.container_perms@[self.container_perms@[c_ptr].value().uppertree_seq@[u_index as int]].value().depth]
                #![trigger self.container_perms@[self.container_perms@[c_ptr].value().uppertree_seq@[u_index as int]].value().subtree_set@.contains(c_ptr)]
                #![trigger self.container_perms@[self.container_perms@[c_ptr].value().uppertree_seq@[u_index as int]].value().uppertree_seq]
                // #![trigger self.container_perms@[c_ptr].value().uppertree_seq@[u_index as int]]
                self.container_perms@.dom().contains(c_ptr) && 0 <= u_index < self.container_perms@[c_ptr].value().depth
                ==>
                self.container_perms@.dom().contains(self.container_perms@[c_ptr].value().uppertree_seq@[u_index as int])
                &&
                self.container_perms@[self.container_perms@[c_ptr].value().uppertree_seq@[u_index as int]].value().depth == u_index
                &&
                self.container_perms@[self.container_perms@[c_ptr].value().uppertree_seq@[u_index as int]].value().subtree_set@.contains(c_ptr)
                &&
                self.container_perms@[self.container_perms@[c_ptr].value().uppertree_seq@[u_index as int]].value().uppertree_seq@ =~= self.container_perms@[c_ptr].value().uppertree_seq@.subrange(0, u_index)
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
                    self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr)
                    ==
                    self.container_perms@[sub_c_ptr].value().uppertree_seq@.contains(c_ptr)
                )
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
        {}

        pub proof fn no_child_imply_no_subtree(&self, c_ptr:ContainerPtr)
            requires
                self.wf(),
                self.container_perms@.dom().contains(c_ptr),
                self.container_perms@[c_ptr].value().children@ =~= Seq::empty(),
            ensures
                self.container_perms@[c_ptr].value().subtree_set@ =~= Set::empty(),
        {
            assert(forall|s_ptr:ContainerPtr|
                #![auto]
                self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr)
                ==>
                self.container_perms@[s_ptr].value().uppertree_seq@.subrange(0,self.container_perms@[c_ptr].value().depth as int) == self.container_perms@[c_ptr].value().uppertree_seq@
                &&
                s_ptr != self.root_container
                &&
                self.container_perms@[s_ptr].value().parent.unwrap() != c_ptr
                &&
                self.container_perms@[s_ptr].value().uppertree_seq@.len() > self.container_perms@[c_ptr].value().depth
                &&
                self.container_perms@.dom().contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1])
                &&
                self.container_perms@[s_ptr].value().uppertree_seq@.subrange(0,self.container_perms@[c_ptr].value().depth + 1) =~= self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@
                &&
                self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@.len() == self.container_perms@[c_ptr].value().depth + 1
                &&
                self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int] == c_ptr
                &&
                self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().parent.unwrap() == c_ptr
                &&
                self.container_perms@[c_ptr].value().children@.contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1])
            );
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
            assert(
                self.container_perms@[child_ptr].value().parent.unwrap() == c_ptr
                &&
                self.container_perms@[child_ptr].value().depth == self.container_perms@[c_ptr].value().depth + 1
                &&
                self.container_perms@[child_ptr].value().uppertree_seq@[self.container_perms@[child_ptr].value().depth - 1] == c_ptr
                &&
                self.container_perms@[s_ptr].value().uppertree_seq@.subrange(0, self.container_perms@[child_ptr].value().depth as int) == self.container_perms@[child_ptr].value().uppertree_seq@
                &&
                self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int] == c_ptr
            );
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
            assert(
                self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                (
                    self.container_perms@[s_ptr].value().uppertree_seq@.subrange(0,self.container_perms@[c_ptr].value().depth as int) == self.container_perms@[c_ptr].value().uppertree_seq@
                    &&
                    s_ptr != self.root_container
                    &&
                    self.container_perms@[s_ptr].value().parent.unwrap() != c_ptr
                    &&
                    self.container_perms@[s_ptr].value().uppertree_seq@.len() > self.container_perms@[c_ptr].value().depth
                    &&
                    self.container_perms@.dom().contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1])
                    &&
                    self.container_perms@[s_ptr].value().uppertree_seq@.subrange(0,self.container_perms@[c_ptr].value().depth + 1) =~= self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@
                    &&
                    self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@.len() == self.container_perms@[c_ptr].value().depth + 1
                    &&
                    self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int] == c_ptr
                    &&
                    self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().parent.unwrap() == c_ptr
                    &&
                    self.container_perms@[c_ptr].value().children@.contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1])
                    &&
                    self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().subtree_set@.contains(s_ptr)
                )
                &&
                (exists|child_ptr:ContainerPtr| 
                    #![auto]
                    self.container_perms@[c_ptr].value().children@.contains(child_ptr) && self.container_perms@[child_ptr].value().subtree_set@.contains(s_ptr)
                )
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
                        #![auto]
                        depth - 1 <= i < self.container_perms@[child_ptr].value().depth ==> self.container_perms@[child_ptr].value().uppertree_seq@[i] != a_ptr,
                    ensures
                        depth == 1,
                        forall|i:int|
                            #![auto]
                            0 <= i < self.container_perms@[child_ptr].value().depth ==> self.container_perms@[child_ptr].value().uppertree_seq@[i] != a_ptr,
            {
                assert(self.container_perms@.dom().contains(current_parent_ptr));
                let tracked current_parent_perm = self.container_perms.borrow().tracked_borrow(current_parent_ptr);
                assert(current_parent_perm.addr() == current_parent_ptr);
                let current_parent : &Container = PPtr::<Container>::from_usize(current_parent_ptr).borrow(Tracked(current_parent_perm));
                current_parent_ptr = current_parent.parent.unwrap();
                if current_parent_ptr == a_ptr{
                    return true;
                }
                depth = depth - 1;
            }
            false
        }
    }
}
