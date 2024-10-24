pub open spec fn iommu_tables_wf(&self) -> bool{
    &&&
    self.free_ioids.wf()
    &&&
    self.free_ioids@.no_duplicates()
    &&&
    forall|i:int| #![trigger self.free_ioids@[i]] 0<=i<self.free_ioids.len()  ==> self.free_ioids@[i]<IOID_MAX
    &&&
    self.iommu_tables.wf()
    &&&
    forall|ioid:IOid| 
        #![trigger self.iommu_tables[ioid as int]] 
        #![trigger self.free_ioids@.contains(ioid)] 
        0 <= ioid < IOID_MAX ==>
        self.iommu_tables[ioid as int].is_None() <==> !self.free_ioids@.contains(ioid)
    &&&
    forall|ioid:IOid| 
        #![trigger self.iommu_tables[ioid as int].unwrap()]
        0 <= ioid < IOID_MAX && self.iommu_tables[ioid as int].is_Some() 
        ==> 
        self.iommu_tables[ioid as int].unwrap().wf()
        &&
        self.iommu_tables[ioid as int].unwrap().page_closure().subset_of(self.iommu_table_pages@)        
        &&
        self.iommu_tables[ioid as int].unwrap().kernel_l4_end == 0
    &&&
    forall|ioid_i:IOid, ioid_j:IOid| 
        #![trigger self.iommu_tables[ioid_i as int].unwrap().page_closure(), self.iommu_tables[ioid_j as int].unwrap().page_closure()]
        0 <= ioid_i < IOID_MAX && self.iommu_tables[ioid_i as int].is_Some() 
        &&
        0 <= ioid_j < IOID_MAX && self.iommu_tables[ioid_j as int].is_Some() 
        &&
        ioid_i != ioid_j
        ==>
        self.iommu_tables[ioid_i as int].unwrap().page_closure().disjoint(self.iommu_tables[ioid_j as int].unwrap().page_closure())
}