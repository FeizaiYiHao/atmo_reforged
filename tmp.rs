assert(ret.l4_table@.dom() =~=  Set::<PageMapPtr>::empty().insert(ret.cr3));
            assert(ret.cr3 == ret.l4_table@[ret.cr3].addr());
            assert(ret.l4_table@[ret.cr3].is_init());
            assert(ret.l4_table@[ret.cr3].value().wf());
            //L4 table only maps to L3
            assert(forall|i: L4Index, j: L4Index|
                // #![trigger ret.l4_table@[ret.cr3].value()[i].perm.present, ret.l4_table@[ret.cr3].value()[j].perm.present]
                #![trigger ret.l4_table@[ret.cr3].value()[i].perm.present, ret.l4_table@[ret.cr3].value()[j].perm.present, ret.l4_table@[ret.cr3].value()[i].addr, ret.l4_table@[ret.cr3].value()[j].addr]
                i != j && 0 <= i < 512 && ret.l4_table@[ret.cr3].value()[i].perm.present && 0 <= j < 512 && ret.l4_table@[ret.cr3].value()[j].perm.present ==>
                    ret.l4_table@[ret.cr3].value()[i].addr != ret.l4_table@[ret.cr3].value()[j].addr);
            assert(forall|i: L4Index| 
                // #![trigger ret.l4_table@[ret.cr3].value()[i].perm.present]
                #![trigger ret.l2_tables@.dom().contains(ret.l4_table@[ret.cr3].value()[i].addr)]
                #![trigger ret.l1_tables@.dom().contains(ret.l4_table@[ret.cr3].value()[i].addr)]
                0 <= i < 512 && ret.l4_table@[ret.cr3].value()[i].perm.present ==> 
                    ret.l2_tables@.dom().contains(ret.l4_table@[ret.cr3].value()[i].addr) == false
                    &&
                    ret.l1_tables@.dom().contains(ret.l4_table@[ret.cr3].value()[i].addr) == false
                    &&
                    ret.cr3 != ret.l4_table@[ret.cr3].value()[i].addr);
            // no ret mapping        
            assert(forall|i: L4Index| 
                // #![trigger ret.l4_table@[ret.cr3].value()[i].perm.present]
                #![trigger ret.l4_table@[ret.cr3].value()[i].addr]
                0 <= i < 512 && ret.l4_table@[ret.cr3].value()[i].perm.present ==>
                    ret.cr3 != ret.l4_table@[ret.cr3].value()[i].addr);
            //all l4 points to valid l3 tables 
            assert(forall|i: L4Index|
                #![trigger ret.l3_tables@.dom().contains(ret.l4_table@[ret.cr3].value()[i].addr)]
                0 <= i < 512 && ret.l4_table@[ret.cr3].value()[i].perm.present && !ret.l4_table@[ret.cr3].value()[i].perm.ps ==>
                    ret.l3_tables@.dom().contains(ret.l4_table@[ret.cr3].value()[i].addr));
            //no hugepage in L4 (hardware limit)        
            assert(forall|i: L4Index| 
                #![trigger ret.l4_table@[ret.cr3].value()[i].perm.ps]
                0 <= i < 512 && ret.l4_table@[ret.cr3].value()[i].perm.present ==> 
                    !ret.l4_table@[ret.cr3].value()[i].perm.ps );