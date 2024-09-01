use vstd::prelude::*;
verus! {
use core::mem::MaybeUninit;

use vstd::seq_lib::*;

pub type Index = i32;
pub const NULL_POINTER: usize = 0;

#[derive(Debug)]
pub struct Node{
    pub value:usize,
    pub next:Index,
    pub prev:Index,
}

pub struct StaticLinkedList<const N: usize>{
    pub ar: [Node;N],
    pub spec_seq: Ghost<Seq<usize>>,

    pub value_list: Ghost<Seq<Index>>,
    pub value_list_head: Index,
    pub value_list_tail: Index,
    pub value_list_len: usize,
    pub free_list: Ghost<Seq<Index>>,
    pub free_list_head: Index,
    pub free_list_tail: Index,
    pub free_list_len: usize,

    pub size: usize,


    pub arr_seq: Ghost<Seq<Node>>,
}

impl<const N: usize> StaticLinkedList<N> {

    #[verifier(external_body)]
    pub fn new() -> (ret: Self)
        ensures
            ret.arr_seq@.len() == N,
    {
        unsafe{
            let ret = Self {

            spec_seq: Ghost(Seq::empty()),

            value_list: Ghost(Seq::empty()),
            value_list_head: -1,
            value_list_tail: -1,
            value_list_len: 0,
            free_list: Ghost(Seq::empty()),
            free_list_head: -1,
            free_list_tail: -1,
            free_list_len: 0,

            size: N,

            arr_seq: Ghost(Seq::empty()),
            ar: MaybeUninit::uninit().assume_init(),
        };

        ret
        }
    }

    pub fn init(&mut self)
        requires
            old(self).arr_seq@.len() == N,
            N>2,
            N<Index::MAX,
        ensures
            self.wf(),
            self.len() == 0,
            self@ =~= Seq::empty(),
        {
            // assume(N>2);
            // assume(N<Index::MAX);
            self.value_list = Ghost(Seq::empty());
            self.value_list_head = -1;
            self.value_list_tail = -1;
            self.value_list_len = 0;
            self.spec_seq = Ghost(Seq::empty());
            self.free_list = Ghost(Seq::empty());
            self.free_list_head = -1;
            self.free_list_tail = -1;
            self.free_list_len = 0;
            assert(self.value_list_wf());
            assert(self.free_list_wf());

            self.size = N;

            self.free_list_head = 0;
            self.free_list_tail = 0;
            self.free_list_len = 1;
            proof{self.free_list@ = self.free_list@.push(0);}
            self.set_next(0,-1);
            self.set_prev(0,-1);
            self.set_ptr(0,NULL_POINTER);
            // assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            // assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            // assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            // assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
            // assert(forall|i: nat, j:nat|  #![auto] i != j && 0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() ==> (self.free_list@[i as int] != self.free_list@[j as int]) );
            // assert(self.wf_free_node_head());
            // assert(self.wf_free_node_tail());
            // assert(self.free_list_len == self.free_list@.len());
            assert(self.free_list_wf());
            let mut index:Index = 1;
            while index != N as Index
                invariant
                    1<= index <= N,
                    N<Index::MAX,
                    self.value_list@ =~= Seq::empty(),
                    self.value_list@.len() == 0,
                    self.spec_seq@.len() == 0,
                    self.array_wf(),
                    self.spec_seq_wf(),
                    self.value_list_wf(),
                    self.free_list_wf(),
                    index == self.free_list@.len(),
                    forall|i: Index|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] == i),
                    self.arr_seq@[0].prev == -1,
                    self.arr_seq@[(index - 1) as int].next == -1,
                    forall|i: int|  #![auto] 0 <= i < index ==> self.arr_seq@[i].prev == i - 1,
                    forall|i: int|  #![auto] 0 <= i < index - 1 ==> self.arr_seq@[i].next == i + 1,
                    forall|i: int|  #![auto] 0 <= i < index ==> self.arr_seq@[i].value == 0,
                    self.free_list_len == index,
                    self.free_list_len + self.value_list_len == index,
                    forall|i: Index|  #![auto] 0 <= i < index ==> self.free_list@.contains(i),
                    forall|i: Index| #![auto] 0 <= i < index ==> self.arr_seq@[i as int].value == NULL_POINTER,
                ensures
                    self.free_list_len == N,
                    self.free_list_wf(),
                    forall|i: Index|  #![auto] 0 <= i < N ==> (self.free_list@[i as int] == i),
                    self.value_list@ =~= Seq::empty(),
                    self.value_list@.len() == 0,
                    self.spec_seq@.len() == 0,
                    self.array_wf(),
                    self.spec_seq_wf(),
                    self.value_list_wf(),
                    self.free_list_wf(),
                    forall|i: Index|  #![auto] 0 <= i < N ==> self.free_list@.contains(i) ^ self.value_list@.contains(i),
                    forall|i: Index| #![auto] 0 <= i < N ==> self.arr_seq@[i as int].value == NULL_POINTER,
                    self.wf(),
            {
                proof{
                    assert forall |s: Seq<Index>, v: Index, x: Index| v==x || s.contains(x) implies #[trigger] s.push(v).contains(x) by {
                        lemma_seq_contains_after_push(s, v, x);
                    }
                }

                self.free_list = Ghost(self.free_list@.push((index as Index)));
                self.set_prev(index,(index - 1));
                self.set_next(index,-1);
                self.set_next((index - 1), index);
                self.set_ptr(index,0);
                self.free_list_tail = index;
                index = index + 1;
                self.free_list_len = index as usize;

                assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
                assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
                assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
                assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
                assert(forall|i: nat, j:nat|  #![auto] i != j && 0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() ==> (self.free_list@[i as int] != self.free_list@[j as int]) );
                assert(self.wf_free_node_head());
                assert(self.wf_free_node_tail());
                assert(self.free_list_len == self.free_list@.len());
            }
            // assert(self.free_list@.len() == N);
            // assert(forall|i: Index|  #![auto] 0 <= i < N ==> self.free_list@[i as int] == i);
            // assert(forall|i: Index|  #![auto] 0 <= i < N ==> self.free_list@.index_of(i) == i as int);
            // assert(forall|i: Index|  #![auto] 0 <= i < N ==> self.free_list@.contains(i));


        }

    pub open spec fn spec_len(&self) -> usize{
        self.value_list_len
    }

    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (l: usize)
        ensures
            l == self.value_list_len,
    {
        self.value_list_len
    }

    pub open spec fn unique(&self) -> bool {
        forall|i:int, j:int| #![auto] i != j && 0 <= i < self.spec_seq@.len() && 0 <= j < self.spec_seq@.len()
            ==> self.spec_seq@[i] != self.spec_seq@[j]
    }

    pub open spec fn view(&self) -> Seq<usize>
        recommends self.wf(),
    {
        self.spec_seq@
    }

    pub closed spec fn node_ref_valid(&self, index: Index) -> bool{
        self.value_list@.contains(index)
    }

    pub closed spec fn node_ref_resolve(&self, index: Index) -> usize
        recommends self.node_ref_valid(index)
    {
        self.arr_seq@[index as int].value
    }

    pub open spec fn prev_free_node_of(&self, i: nat) -> int
        recommends i < self.free_list@.len()
    {
        if i == 0{
            -1
        } else {
            self.free_list@[i - 1int] as int
        }
    }

    pub open spec fn next_free_node_of(&self, i: nat) -> int
        recommends i < self.free_list@.len()
    {
        if i + 1 == self.free_list@.len() {
            -1
        } else {
            self.free_list@[i + 1int] as int
        }
    }

    pub open spec fn wf_free_node_head(&self) -> bool {
        if self.free_list@.len() == 0 {
            self.free_list_head == -1
        } else {
            self.free_list_head == self.free_list@[0]
        }
    }

    pub open spec fn wf_free_node_tail(&self) -> bool {
        if self.free_list@.len() == 0 {
            self.free_list_tail == -1
        } else {
            self.free_list_tail  == self.free_list@[self.free_list@.len() - 1]
        }
    }

    pub open spec fn free_list_wf(&self) -> bool{
        (forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i))
        &&
        (forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i))
        &&
        (forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) )
        &&
        (forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) )
        &&
        (forall|i: nat, j:nat|  #![auto] i != j && 0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() ==> (self.free_list@[i as int] != self.free_list@[j as int]) )
        &&
        self.wf_free_node_head()
        &&
        self.wf_free_node_tail()
        &&
        self.free_list_len == self.free_list@.len()

    }

    pub open spec fn prev_value_node_of(&self, i: int) -> int
        recommends 0 <= i < self.value_list@.len()
    {
        if i == 0{
            -1
        } else {
            self.value_list@[i - 1int] as int
        }
    }

    pub open spec fn next_value_node_of(&self, i: int) -> int
        recommends 0 <= i < self.value_list@.len()
    {
        if i + 1 == self.value_list@.len() {
            -1
        } else {
            self.value_list@[i + 1int] as int
        }
    }

    pub open spec fn wf_value_node_head(&self) -> bool {
        if self.value_list@.len() == 0 {
            self.value_list_head == -1
        } else {
            self.value_list_head == self.value_list@[0]
        }
    }

    pub open spec fn wf_value_node_tail(&self) -> bool {
    if self.value_list@.len() == 0 {
        self.value_list_tail == -1
    } else {
        self.value_list_tail  == self.value_list@[self.value_list@.len() - 1]
    }
    }

    pub open spec fn value_list_wf(&self) -> bool{
        (forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == self.next_value_node_of(i))
        &&
        (forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == self.prev_value_node_of(i))
        &&
        (forall|i: int|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] < N) )
        &&
        (forall|i: nat|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] >= 0) )
        &&
        (forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.value_list@.len() && 0 <= j < self.value_list@.len() ==> (self.value_list@[i as int] != self.value_list@[j as int]) )
        &&
        self.wf_value_node_head()
        &&
        self.wf_value_node_tail()
        &&
        self.value_list_len == self.value_list@.len()
    }

    pub open spec fn free_list_ptr_all_null(&self) -> bool
    {
        forall|i: Index| #![auto] 0 <= i < N && self.arr_seq@[i as int].value != NULL_POINTER ==> self.value_list@.contains(i)
    }

    pub open spec fn array_wf(&self) -> bool{
        (self.arr_seq@.len() == N)
        &&
        (self.size == N)
    }

    pub open spec fn spec_seq_wf(&self) -> bool
    {
        self.spec_seq@.len() == self.value_list_len
        &&
        forall|i:int| #![auto] 0<= i < self.value_list_len ==> self.arr_seq@[self.value_list@[i as int] as int].value == self.spec_seq@[i as int]

    }

    pub open spec fn wf(&self) -> bool{
        (self.array_wf())
        &&
        (self.free_list_len + self.value_list_len == N)
        &&
        (self.value_list_wf())
        &&
        (self.free_list_wf())
        &&
        (forall|i:Index| #![auto] 0<= i < N ==> self.free_list@.contains(i) ^ self.value_list@.contains(i))
        &&
        (self.spec_seq_wf())
        &&
        (self.free_list_ptr_all_null())
    }

    #[verifier(external_body)]
    fn set_ptr(&mut self, index: Index, v: usize)
        requires
            old(self).array_wf(),
        ensures
            self.array_wf(),
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==>
                self.arr_seq@[i].next == old(self).arr_seq@[i].next && self.arr_seq@[i].prev == old(self).arr_seq@[i].prev,
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i != index ==>
                self.arr_seq@[i].value == old(self).arr_seq@[i].value,
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i == index ==>
                self.arr_seq@[i].value == v,
            self.spec_seq@ == old(self).spec_seq@,
            self.value_list@ == old(self).value_list@,
            self.free_list@ == old(self).free_list@,
            self.value_list_head == old(self).value_list_head,
            self.value_list_tail == old(self).value_list_tail,
            self.value_list_len == old(self).value_list_len,
            self.free_list_head == old(self).free_list_head,
            self.free_list_tail == old(self).free_list_tail,
            self.free_list_len == old(self).free_list_len,
            old(self).free_list_wf() ==> self.free_list_wf(),
            old(self).value_list_wf() ==> self.value_list_wf(),
    {
        self.ar[index as usize].value = v;
    }

    #[verifier(external_body)]
    fn set_next(&mut self, index: Index, v: Index)
        requires
            old(self).array_wf(),
        ensures
            self.array_wf(),
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==>
                self.arr_seq@[i].value == old(self).arr_seq@[i].value && self.arr_seq@[i].prev == old(self).arr_seq@[i].prev,
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i != index ==>
                self.arr_seq@[i].next == old(self).arr_seq@[i].next,
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i == index ==>
                self.arr_seq@[i].next == v,
            self.spec_seq@ == old(self).spec_seq@,
            self.value_list@ == old(self).value_list@,
            self.free_list@ == old(self).free_list@,
            self.value_list_head == old(self).value_list_head,
            self.value_list_tail == old(self).value_list_tail,
            self.value_list_len == old(self).value_list_len,
            self.free_list_head == old(self).free_list_head,
            self.free_list_tail == old(self).free_list_tail,
            self.free_list_len == old(self).free_list_len,
    {
        self.ar[index as usize].next = v;
    }

    #[verifier(external_body)]
    fn set_prev(&mut self, index: Index, v: Index)
        requires
            old(self).array_wf(),
        ensures
            self.array_wf(),
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==>
                self.arr_seq@[i].value == old(self).arr_seq@[i].value && self.arr_seq@[i].next == old(self).arr_seq@[i].next,
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i != index ==>
                self.arr_seq@[i].prev == old(self).arr_seq@[i].prev,
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i == index ==>
                self.arr_seq@[i].prev == v,
            self.spec_seq@ == old(self).spec_seq@,
            self.value_list@ == old(self).value_list@,
            self.free_list@ == old(self).free_list@,
            self.value_list_head == old(self).value_list_head,
            self.value_list_tail == old(self).value_list_tail,
            self.value_list_len == old(self).value_list_len,
            self.free_list_head == old(self).free_list_head,
            self.free_list_tail == old(self).free_list_tail,
            self.free_list_len == old(self).free_list_len,
    {
        self.ar[index as usize].prev = v;
    }

    //TODO: prove this
    #[verifier(external_body)]
    pub fn put_ptr(&mut self, new_ptr: usize)
        requires
            old(self).array_wf(),
        ensures
        self.array_wf(),
        forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==>
            self.arr_seq@[i].next == old(self).arr_seq@[i].next && self.arr_seq@[i].prev == old(self).arr_seq@[i].prev && self.arr_seq@[i].value == old(self).arr_seq@[i].value,
        self.spec_seq@ == old(self).spec_seq@.push(new_ptr),
        self.value_list@ == old(self).value_list@,
        self.free_list@ == old(self).free_list@,
        self.value_list_head == old(self).value_list_head,
        self.value_list_tail == old(self).value_list_tail,
        self.value_list_len == old(self).value_list_len,
        self.free_list_head == old(self).free_list_head,
        self.free_list_tail == old(self).free_list_tail,
        self.free_list_len == old(self).free_list_len,
        old(self).free_list_wf() ==> self.free_list_wf(),
        old(self).value_list_wf() ==> self.value_list_wf(),
    {
        //self.spec_seq@ = self.spec_seq@.push(new_ptr);
    }


    pub open spec fn spec_get_ptr(&self, index: Index) -> (ptr:usize)
        recommends
            self.wf(),
            0 <= index < N,
    {
        self.arr_seq@[index as int].value
    }

    #[verifier(external_body)]
    pub fn get_ptr(&self, index: Index) -> (ptr:usize)
        requires
            0 <= index < N,
            self.array_wf(),
        ensures
            ptr == self.arr_seq@[index as int].value,
    {
        self.ar[index as usize].value
    }

    #[verifier(external_body)]
    pub fn get_next(&self, index: Index) -> (next:Index)
        requires
            0 <= index < N,
            self.array_wf(),
        ensures
            next == self.arr_seq@[index as int].next,
    {
        self.ar[index as usize].next
    }

    #[verifier(external_body)]
    pub fn get_prev(&self, index: Index) -> (prev:Index)
        requires
            0 <= index < N,
            self.array_wf(),
        ensures
            prev == self.arr_seq@[index as int].prev,
    {
        self.ar[index as usize].prev
    }


    #[verifier(inline)]
    pub open spec fn get_raw_element(&self, i: int) -> Node
        recommends self.arr_seq@.len() == N,
                   0 <= i < N,
    {
        self.arr_seq@[i]
    }

    //getters
    pub fn get_head(&self) -> (ret:usize)
        requires
            self.wf(),
            self.len() != 0,
        ensures
            ret == self@[0],
    {
        return self.get_ptr(self.value_list_head);
    }

    //helper function for push()
    pub fn alloc_node_index(&mut self) -> (index: Index)
        requires old(self).value_list_len < old(self).size,
                 old(self).array_wf(),
                 old(self).free_list_len + old(self).value_list_len == N,
                 old(self).value_list_wf(),
                 old(self).free_list_wf(),
                forall|i:Index| #![auto] 0<= i < N ==> old(self).free_list@.contains(i) ^ old(self).value_list@.contains(i),
                old(self).spec_seq_wf(),
                old(self).free_list_ptr_all_null(),
        ensures self.free_list_len == old(self).free_list_len - 1,
                self.array_wf(),
                self.value_list_len ==  old(self).value_list_len,
                self.value_list_wf(),
                self.free_list_wf(),
                forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.value_list@.contains(i),
                self.free_list@.contains(index) == false,
                self.value_list@.contains(index) == false,
                self.spec_seq_wf(),
                0 <= index < N,
                self.spec_seq == old(self).spec_seq,
                forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==>
                    self.arr_seq@[i].value == old(self).arr_seq@[i].value,
                self.value_list@ == old(self).value_list@,
                self.free_list_ptr_all_null(),
    {
        assert(self.free_list_len > 0);
        assert(self.free_list@.len() > 0);

        //get the free node
        //assert(self.wf_free_node_head());
        assert(self.free_list_head != -1);
        assert(self.free_list_tail != -1);
        let mut node_index:Index = -1;
        if self.free_list_len == 1{
            assert(self.free_list_head == self.free_list_tail);
            node_index = self.free_list_head;
            self.free_list_head = -1;
            self.free_list_tail = -1;
            proof{self.free_list@ = self.free_list@.drop_last();}
            self.free_list_len = 0;
            assert(self.free_list_wf());
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == old(self).arr_seq@[old(self).value_list@[i as int] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> old(self).next_value_node_of(i) == self.next_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == self.next_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == old(self).arr_seq@[old(self).value_list@[i as int] as int].prev);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> old(self).prev_value_node_of(i) == self.prev_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == self.prev_value_node_of(i));
            assert(forall|i: int|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] < N) );
            assert(forall|i: int|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] >= 0) );
            assert(self.wf_value_node_head());
            assert(self.wf_value_node_tail());
            assert(self.value_list_len == self.value_list@.len());
            assert(self.value_list_wf());
        }else{
            assert(self.free_list_len > 1);
            assert(self.wf_free_node_head());
            assert(self.free_list_tail == self.free_list@[self.free_list@.len() - 1]);
            assert(self.prev_free_node_of((self.free_list@.len() - 1) as nat) != -1);
            assert(self.next_free_node_of((self.free_list@.len() - 1) as nat) == -1);
            node_index = self.free_list_tail;
            let next = self.get_next(self.free_list_tail);
            let prev = self.get_prev(self.free_list_tail);
            assert(next == -1);
            assert(prev != -1);
            assert(self.value_list@.contains(prev) == false);
            assert(self.prev_free_node_of((self.free_list@.len() - 1) as nat) == prev);
            assert(self.free_list@[self.free_list@.len() - 2 as int] == prev);
            self.set_next(prev, -1);
            assert(self.arr_seq@[prev as int].next == -1);
            proof{self.free_list@ = self.free_list@.drop_last();}
            self.free_list_len = self.free_list_len - 1;
            self.free_list_tail = prev;
            assert(self.free_list@.len() == self.free_list_len);
            assert((forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) ));
            assert((forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) ));
            assert(self.wf_free_node_head());
            assert(self.wf_free_node_tail());
            assert(self.free_list_len == self.free_list@.len());
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() - 1 ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() - 1 ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.prev_free_node_of(i) == old(self).prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(self.free_list_wf());

            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == old(self).arr_seq@[old(self).value_list@[i as int] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> old(self).next_value_node_of(i) == self.next_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == self.next_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == old(self).arr_seq@[old(self).value_list@[i as int] as int].prev);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> old(self).prev_value_node_of(i) == self.prev_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == self.prev_value_node_of(i));
            assert(forall|i: int|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] < N) );
            assert(forall|i: int|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] >= 0) );
            assert(self.wf_value_node_head());
            assert(self.wf_value_node_tail());
            assert(self.value_list_len == self.value_list@.len());
            assert(self.value_list_wf());
        }
        assert(self.free_list_wf());
        assert(self.value_list_wf());
        assert(self.free_list@.contains(node_index) == false);
        return node_index;
    }

    pub fn put_node_index(&mut self, index: Index, new_ptr:usize)
        requires
            old(self).array_wf(),
            old(self).value_list_wf(),
            old(self).free_list_wf(),
            forall|i:Index| #![auto] 0<= i < N && i != index ==> old(self).free_list@.contains(i) ^ old(self).value_list@.contains(i),
            old(self).free_list@.contains(index) == false,
            old(self).value_list@.contains(index) == false,
            old(self).spec_seq_wf(),
            0 <= index < N,
            old(self).value_list_len < old(self).size,
        ensures
            self.free_list_len == old(self).free_list_len,
            self.array_wf(),
            self.value_list_wf(),
            self.free_list_wf(),
            forall|i:Index| #![auto] 0<= i < N ==> self.free_list@.contains(i) ^ self.value_list@.contains(i),
            self.free_list == old(self).free_list,
            self.value_list@ == old(self).value_list@.push(index),
            self.spec_seq@ == old(self).spec_seq@.push(new_ptr),
            self.free_list_len == old(self).free_list_len,
            self.value_list_len == old(self).value_list_len + 1,
            self.spec_seq_wf(),
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i != index ==>
                self.arr_seq@[i].value == old(self).arr_seq@[i].value,
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() && i == index ==>
                self.arr_seq@[i].value == new_ptr,
    {

        // self.set_ptr(index, new_ptr);

        if self.value_list_len == 0{
            assert(self.value_list_head == -1);
            assert(self.value_list_tail == -1);
            self.value_list_head = index;
            self.value_list_tail = index;
            self.value_list_len = 1;
            self.set_prev(index, -1);
            self.set_next(index, -1);
            proof{self.value_list@ = self.value_list@.push(index);}
            assert(self.value_list@[0] == index);
            assert(self.value_list@.contains(index) == true);

            assert(self.wf_value_node_head());
            assert(self.wf_value_node_tail());
            assert(self.value_list_len == self.value_list@.len());
            assert(self.arr_seq@[index as int].next == -1);
            assert(self.arr_seq@[index as int].prev == -1);
            assert(self.next_value_node_of(0) == -1);
            assert(self.prev_value_node_of(0) == -1);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == self.next_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == self.prev_value_node_of(i));
            assert(forall|i: int|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] < N) );
            assert(forall|i: int|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] >= 0) );

            assert(self.value_list_wf());


            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
            assert(self.free_list_wf());
        }else{
            assert(self.value_list_wf());
            assert(self.value_list@.len() > 0);
            assert(self.value_list_tail != -1);

            assert(self.value_list_tail == self.value_list@[self.value_list@.len() - 1]);
            // assert(self.prev_value_node_of((self.value_list@.len() - 1) as nat) != -1);
            assert(self.next_value_node_of((self.value_list@.len() - 1) as int) == -1);
            assert(self.arr_seq@[self.value_list@[self.value_list@.len() - 1] as int].next == -1);
            let tail_index = self.value_list_tail;
            let prev = self.get_prev(tail_index);
            let next = self.get_next(tail_index);
            assert(next == -1);

            self.set_next(tail_index, index);
            self.set_prev(index, tail_index);
            self.set_next(index, -1);
            proof{self.value_list@ = self.value_list@.push(index);}
            assert(self.value_list@[self.value_list@.len() - 1] == index);
            assert(self.value_list@.contains(index) == true);
            self.value_list_len = self.value_list_len + 1;
            self.value_list_tail = index;


            assert(self.free_list@.contains(tail_index) == false);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
            assert(self.free_list_wf());

            assert(self.wf_value_node_head());
            assert(self.wf_value_node_tail());
            // assert(self.value_list_len == self.value_list@.len());
            // assert(self.arr_seq@[index as int].next == -1);
            // assert(self.arr_seq@[index as int].prev == -1);
            // assert(self.next_value_node_of(0) == -1);
            // assert(self.prev_value_node_of(0) == -1);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() -2 ==> self.arr_seq@[self.value_list@[i as int] as int].next == old(self).arr_seq@[old(self).value_list@[i as int] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() -2 ==> old(self).next_value_node_of(i) == self.next_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == self.next_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() - 1 ==> old(self).arr_seq@[old(self).value_list@[i as int] as int].prev == self.arr_seq@[self.value_list@[i as int] as int].prev);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() - 1 ==> old(self).prev_value_node_of(i) == self.prev_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == self.prev_value_node_of(i));
            assert(forall|i: int|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] < N) );
            assert(forall|i: int|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] >= 0) );
            assert(self.value_list_wf());
        }
        self.set_ptr(index, new_ptr);
        self.put_ptr(new_ptr);
        assert(self.free_list_wf());
        assert(self.value_list_wf());
        assert(self.spec_seq_wf());
        assert(self.free_list@.contains(index) == false);
        assert(self.value_list@.contains(index) == true);
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> old(self).free_list@.contains(i) ^ old(self).value_list@.contains(i));
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.value_list@.contains(i));
        assert(forall|i:Index| #![auto] 0<= i < N ==> self.free_list@.contains(i) ^ self.value_list@.contains(i));
    }


    pub fn push(&mut self, new_ptr: usize) -> (free_node_index : Index)
        requires old(self).wf(),
                 old(self).len() < old(self).size,
                 old(self).unique(),
                 old(self)@.contains(new_ptr) == false,
        ensures self.wf(),
                self@ == old(self)@.push(new_ptr),
                self.value_list@ == old(self).value_list@.push(free_node_index),
                self.len() == old(self).len() + 1,
                self.arr_seq@[free_node_index as int].value == new_ptr,
                self.node_ref_valid(free_node_index),
                self.node_ref_resolve(free_node_index) == new_ptr,
                forall|index:Index| old(self).node_ref_valid(index) ==> self.node_ref_valid(index),
                forall|index:Index| old(self).node_ref_valid(index) ==> index != free_node_index,
                forall|index:Index| old(self).node_ref_valid(index) ==> self.node_ref_resolve(index) == old(self).node_ref_resolve(index),
                self.unique(),
                forall| ptr: usize| ptr != new_ptr ==> old(self)@.contains(ptr) == self@.contains(ptr),
                self@.contains(new_ptr),
    {
        assert(self.spec_seq_wf());
        let free_node_index = self.alloc_node_index();
        assert(self.free_list_len == old(self).free_list_len - 1);
        assert(self.array_wf());
        assert(self.value_list_len ==  old(self).value_list_len);
        assert(self.value_list_wf());
        assert(self.free_list_wf());
        assert(forall|i:Index| #![auto] 0<= i < N && i != free_node_index ==> self.free_list@.contains(i) ^ self.value_list@.contains(i));
        assert(self.free_list@.contains(free_node_index) == false);
        assert(self.value_list@.contains(free_node_index) == false);
        assert(self.spec_seq_wf());
        self.put_node_index(free_node_index, new_ptr);
        assert(self.free_list_len == old(self).free_list_len - 1);
        assert(self.value_list_len ==  old(self).value_list_len + 1);
        assert(self.array_wf());
        assert(self.free_list_len + self.value_list_len == N);
        assert(self.value_list_wf());
        assert(self.free_list_wf());
        assert(forall|i:Index| #![auto] 0<= i < N ==> self.free_list@.contains(i) ^ self.value_list@.contains(i));
        assert(self.spec_seq_wf());
        assert(self.spec_seq@ == old(self).spec_seq@.push(new_ptr));
        assert(old(self).spec_seq@=~=self.spec_seq@.subrange(0,self.spec_seq@.len() - 1));
        assert(forall| ptr: usize| old(self).spec_seq@.contains(ptr) == self.spec_seq@.subrange(0,self.spec_seq@.len() - 1).contains(ptr));
        assert(forall| ptr: usize| ptr != new_ptr ==> old(self).spec_seq@.contains(ptr) == self.spec_seq@.contains(ptr));
        assert(self.spec_seq@[self.spec_seq@.len() as int - 1] == new_ptr);
        assert(self.spec_seq@.contains(new_ptr));
        return free_node_index;
    }

    //helper function for pop()
    pub fn pop_value(&mut self) -> (index: Index)
        requires old(self).value_list_len > 0,
                old(self).array_wf(),
                old(self).free_list_len + old(self).value_list_len == N,
                old(self).value_list_wf(),
                old(self).free_list_wf(),
                forall|i:Index| #![auto] 0<= i < N ==> old(self).free_list@.contains(i) ^ old(self).value_list@.contains(i),
                old(self).spec_seq_wf(),
                //old(self).free_list_ptr_all_null(),
        ensures self.free_list_len == old(self).free_list_len,
                self.array_wf(),
                self.value_list_len ==  old(self).value_list_len - 1,
                self.value_list_wf(),
                self.free_list_wf(),
                forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.value_list@.contains(i),
                self.free_list@.contains(index) == false,
                self.value_list@.contains(index) == false,
                self.spec_seq@ == old(self).spec_seq@.subrange(1,old(self).spec_seq@.len() as int),
                self.spec_seq_wf(),
                0 <= index < N,
                self.value_list@ == old(self).value_list@.subrange(1,old(self).value_list@.len() as int),
                index == old(self).value_list@[0],
                forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==>
                    self.arr_seq@[i].value == old(self).arr_seq@[i].value,
                forall|i:Index| #![auto] i != index ==>
                    old(self).value_list@.contains(i) == self.value_list@.contains(i),
                //self.free_list_ptr_all_null(),
    {
        assert(self.value_list_head != -1);
        assert(self.value_list_tail != -1);
        let mut node_index:Index = -1;
        if self.value_list_len == 1{
            assert(self.value_list_head == self.value_list_tail);
            node_index = self.value_list_head;
            self.value_list_head = -1;
            self.value_list_tail = -1;
            proof{self.value_list@ = self.value_list@.subrange(1,self.value_list@.len() as int);
                  self.spec_seq@ = self.spec_seq@.subrange(1,self.spec_seq@.len() as int);
            }
            self.value_list_len = 0;
            assert(self.value_list_wf());
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
            assert(self.wf_free_node_head());
            assert(self.wf_free_node_tail());
            assert(self.free_list_len == self.free_list@.len());
            assert(self.free_list_wf());

            assert(self.spec_seq_wf());
        }else{
            assert(self.value_list_len > 1);
            assert(self.wf_value_node_head());
            assert(self.value_list_head == self.value_list@[0]);
            assert(self.prev_value_node_of(0) == -1);
            assert(self.next_value_node_of(0) != -1);
            node_index = self.value_list_head;
            let next = self.get_next(self.value_list_head);
            let prev = self.get_prev(self.value_list_head);
            assert(next != -1);
            assert(prev == -1);
            assert(self.free_list@.contains(next) == false);
            assert(self.next_value_node_of(0) == next);
            assert(self.value_list@[1] == next);
            self.set_prev(next, -1);
            assert(self.arr_seq@[next as int].prev == -1);
            proof{self.value_list@ = self.value_list@.subrange(1,self.value_list@.len() as int);
                self.spec_seq@ = self.spec_seq@.subrange(1,self.spec_seq@.len() as int);
            }
            self.value_list_len = self.value_list_len - 1;
            self.value_list_head = next;
            assert(self.value_list@.len() == self.value_list_len);
            assert((forall|i: nat|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] < N) ));
            assert((forall|i: nat|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] >= 0) ));
            assert(self.wf_value_node_head());
            assert(self.wf_value_node_tail());
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == old(self).arr_seq@[old(self).value_list@[i as int + 1] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> old(self).next_value_node_of(i + 1) == self.next_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == self.next_value_node_of(i));
            assert(forall|i: int| #![auto] 1 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == old(self).arr_seq@[old(self).value_list@[i as int + 1] as int].prev);
            assert(forall|i: int| #![auto] 1 <= i < self.value_list@.len() ==> self.prev_value_node_of(i) == old(self).prev_value_node_of(i + 1));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == self.prev_value_node_of(i));
            assert(self.value_list_wf());

            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
            assert(self.wf_free_node_head());
            assert(self.wf_free_node_tail());
            assert(self.free_list_len == self.free_list@.len());
            assert(self.free_list_wf());

            assert(self.spec_seq_wf());
        }
        assert(forall|i:Index| #![auto] 0<= i < N && i != node_index ==> old(self).free_list@.contains(i) ^ old(self).value_list@.contains(i));
        // assert(self.free_list@.contains(node_index) == false);
        // assert(self.value_list@.contains(node_index) == false);
        assert(self.free_list == old(self).free_list);
        assert(self.value_list == old(self).value_list@.subrange(1,old(self).value_list@.len() as int));
        assert(node_index == old(self).value_list@[0]);
        assert(old(self).value_list@.index_of(node_index) == 0);
        assert(0<= node_index < N);
        assert(forall|i:Index| #![auto] 0<= i < N && i != node_index ==> old(self).free_list@.contains(i) == self.free_list@.contains(i));
        assert(forall|i:Index| #![auto] 0<= i < N && i != node_index && !old(self).value_list@.contains(i) ==> !self.value_list@.contains(i));
        assert(old(self).value_list@.contains(node_index) && !self.value_list@.contains(node_index));

        assert(forall|i:Index| #![auto] 0<= i < N && !old(self).value_list@.contains(i) ==> !self.value_list@.contains(i));

        assert(forall|i:int| #![auto] 0<= i <self.value_list@.len() ==> old(self).value_list@.index_of(self.value_list@[i]) == i + 1);
        assert(forall|i:int| #![auto] 1<= i <old(self).value_list@.len() ==> old(self).value_list@[i] == self.value_list@[i - 1]);
        assert(forall|i:int| #![auto] 1<= i <old(self).value_list@.len() ==> self.value_list@.index_of(old(self).value_list@[i]) == i - 1);
        assert(forall|i:int| #![auto] 1<= i <old(self).value_list@.len() ==> self.value_list@.contains(old(self).value_list@[i]));
        assert(forall|i:Index| #![auto] 0<= i < N && i != node_index && old(self).value_list@.contains(i) ==> self.value_list@.contains(i));

        assert(forall|i:Index| #![auto] 0<= i < N && i != node_index ==> self.free_list@.contains(i) ^ self.value_list@.contains(i));
        return node_index;
    }

    fn free_node(&mut self, index: Index)
        requires
            old(self).array_wf(),
            old(self).value_list_wf(),
            old(self).free_list_wf(),
            forall|i:Index| #![auto] 0<= i < N && i != index ==> old(self).free_list@.contains(i) ^ old(self).value_list@.contains(i),
            old(self).free_list@.contains(index) == false,
            old(self).value_list@.contains(index) == false,
            old(self).spec_seq_wf(),
            0 <= index < N,
            old(self).free_list_len < old(self).size,
        ensures
            self.array_wf(),
            self.value_list_wf(),
            self.free_list_wf(),
            forall|i:Index| #![auto] 0<= i < N ==> self.free_list@.contains(i) ^ self.value_list@.contains(i),
            self.spec_seq_wf(),
            self.free_list_len == old(self).free_list_len + 1,
            self.value_list_len == old(self).value_list_len,
            self.spec_seq == old(self).spec_seq,
            self.value_list == old(self).value_list,
            forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==>
                self.arr_seq@[i].value == old(self).arr_seq@[i].value,
    {
        if self.free_list_len == 0{
            assert(self.free_list_head == -1);
            assert(self.free_list_tail == -1);
            self.free_list_head = index;
            self.free_list_tail = index;
            self.free_list_len = 1;
            self.set_prev(index, -1);
            self.set_next(index, -1);
            proof{self.free_list@ = self.free_list@.push(index);}
            assert(self.free_list@[0] == index);
            assert(self.free_list@.contains(index) == true);

            assert(self.wf_value_node_head());
            assert(self.wf_value_node_tail());
            assert(self.free_list_len == self.free_list@.len());
            assert(self.arr_seq@[index as int].next == -1);
            assert(self.arr_seq@[index as int].prev == -1);
            assert(self.next_free_node_of(0) == -1);
            assert(self.prev_free_node_of(0) == -1);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );

            assert(self.free_list_wf());


            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == old(self).arr_seq@[old(self).value_list@[i as int] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> old(self).next_value_node_of(i) == self.next_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == self.next_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == old(self).arr_seq@[old(self).value_list@[i as int] as int].prev);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> old(self).prev_value_node_of(i) == self.prev_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == self.prev_value_node_of(i));
            assert(forall|i: int|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] < N) );
            assert(forall|i: int|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] >= 0) );
            assert(self.value_list_wf());
        }else{
            assert(self.free_list_wf());
            assert(self.free_list@.len() > 0);
            assert(self.free_list_tail != -1);

            assert(self.free_list_tail == self.free_list@[self.free_list@.len() - 1]);
            // assert(self.prev_free_node_of((self.free_list@.len() - 1) as nat) != -1);
            assert(self.next_free_node_of((self.free_list@.len() - 1) as nat) == -1);
            assert(self.arr_seq@[self.free_list@[self.free_list@.len() - 1] as int].next == -1);
            let tail_index = self.free_list_tail;
            let prev = self.get_prev(tail_index);
            let next = self.get_next(tail_index);
            assert(next == -1);

            self.set_next(tail_index, index);
            self.set_prev(index, tail_index);
            self.set_next(index, -1);
            proof{self.free_list@ = self.free_list@.push(index);}
            assert(self.free_list@[self.free_list@.len() - 1] == index);
            assert(self.free_list@.contains(index) == true);
            self.free_list_len = self.free_list_len + 1;
            self.free_list_tail = index;


            assert(self.value_list@.contains(tail_index) == false);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == old(self).arr_seq@[old(self).value_list@[i as int] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> old(self).next_value_node_of(i) == self.next_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == self.next_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == old(self).arr_seq@[old(self).value_list@[i as int] as int].prev);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> old(self).prev_value_node_of(i) == self.prev_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == self.prev_value_node_of(i));
            assert(forall|i: int|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] < N) );
            assert(forall|i: int|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] >= 0) );
            assert(self.value_list_wf());

            assert(self.wf_free_node_head());
            assert(self.wf_free_node_tail());
            // assert(self.free_list_len == self.free_list@.len());
            // assert(self.arr_seq@[index as int].next == -1);
            // assert(self.arr_seq@[index as int].prev == -1);
            // assert(self.next_free_node_of(0) == -1);
            // assert(self.prev_free_node_of(0) == -1);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() -2 ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() -2 ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() - 1 ==> old(self).arr_seq@[old(self).free_list@[i as int] as int].prev == self.arr_seq@[self.free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() - 1 ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
            assert(self.free_list_wf());
        }
        assert(self.free_list_wf());
        assert(self.value_list_wf());
        assert(self.spec_seq_wf());
        assert(self.free_list@.contains(index) == true);
        assert(self.value_list@.contains(index) == false);
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> old(self).free_list@.contains(i) ^ old(self).value_list@.contains(i));
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.value_list@.contains(i));
        assert(forall|i:Index| #![auto] 0<= i < N ==> self.free_list@.contains(i) ^ self.value_list@.contains(i));

    }



    pub fn pop(&mut self) -> (ret: usize)
        requires old(self).wf(),
                 old(self).len() > 0,
                 old(self).unique(),
        ensures
                self.wf(),
                self.value_list_len == old(self).value_list_len - 1,
                self.value_list@ == old(self).value_list@.subrange(1, old(self).value_list@.len() as int),
                self@ == old(self)@.subrange(1, old(self).spec_seq@.len() as int),
                ret == old(self)@[0],
                old(self)@.contains(ret),
                self.unique(),
                forall|index:Index| old(self).node_ref_valid(index) && old(self).node_ref_resolve(index) != ret ==> self.node_ref_valid(index),
                //forall|index:Index| old(self).node_ref_valid(index) && old(self).node_ref_resolve(index) == ret ==> !self.node_ref_valid(index),
                forall|index:Index| old(self).node_ref_valid(index) && old(self).node_ref_resolve(index) != ret ==> self.node_ref_resolve(index) == old(self).node_ref_resolve(index),
                forall| ptr: usize| ptr != ret ==> old(self)@.contains(ptr) == self@.contains(ptr),
                self@.contains(ret) == false,

        {
            assert(self.spec_seq@[0] == self.arr_seq@[self.value_list@[0] as int].value);
            let pop_index = self.pop_value();

            assert(0<=pop_index<N);
            assert(old(self).spec_seq@[0] == self.arr_seq@[pop_index as int].value);
            let ret = self.get_ptr(pop_index);
            assert(ret == old(self).spec_seq@[0]);
            self.set_ptr(pop_index, NULL_POINTER);

            assert(self.free_list_ptr_all_null());

            assert(forall|index:Index| old(self).node_ref_valid(index) && index != pop_index ==> self.node_ref_valid(index));
            assert(old(self).node_ref_resolve(pop_index) == ret);
            assert(forall|index:Index| old(self).node_ref_valid(index) && old(self).node_ref_resolve(index) != ret ==> self.node_ref_resolve(index) == old(self).node_ref_resolve(index));

            self.free_node(pop_index);
            assert(self.free_list_len == old(self).free_list_len + 1);
            assert(self.value_list_len == old(self).value_list_len - 1);
            assert(self.wf());

            assert(self.node_ref_valid(pop_index) == false);
            assert(forall|index:Index| old(self).node_ref_valid(index) && index != pop_index ==> self.node_ref_valid(index));
            assert(old(self).node_ref_resolve(pop_index) == ret);
            assert(forall|index:Index| old(self).node_ref_valid(index) && old(self).node_ref_resolve(index) != ret ==> self.node_ref_resolve(index) == old(self).node_ref_resolve(index));

            assert(old(self).unique());
            assert(ret == old(self).spec_seq@[0]);
            assert(self.spec_seq@ == old(self).spec_seq@.subrange(1, old(self).spec_seq@.len() as int));
            assert(forall| i: int| 0<= i <self.spec_seq@.len() ==> self.spec_seq@[i] == old(self).spec_seq@[i+1]);
            assert(forall| value:usize|  #![auto] self.spec_seq@.contains(value)  ==> self.spec_seq@.index_of(value) == old(self).spec_seq@.index_of(value) - 1);
            assert(forall| value:usize|  #![auto] self.spec_seq@.contains(value)  ==> old(self).spec_seq@.contains(value));
            assert(forall| i: int| 1 <= i <self.spec_seq@.len() + 1 ==>old(self).spec_seq@[i] == self.spec_seq@[i-1] );
            assert(forall| value:usize|  #![auto] old(self).spec_seq@.contains(value) &&  ret != value ==> self.spec_seq@.contains(value));


            // assert(old(self).arr_seq@[old(self).value_list@[ghost_index@ as int] as int].value == old(self).spec_seq@[ghost_index@ as int]);
            // assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.len() && i != ghost_index@ ==> old(self).spec_seq@[i] != ret);
            // assert(ghost_index@ == old(self).spec_seq@.index_of(ret));
            // assert(self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))).add(old(self).spec_seq@.subrange(old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) + 1, old(self).spec_seq@.len() as int)));
            // assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) ==> self.spec_seq@[i] == old(self).spec_seq@[i]);
            // assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) ==> self.spec_seq@.index_of(old(self).spec_seq@[i]) == i);
            // assert(forall|i:int|#![auto] old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))  < i < old(self).spec_seq@.len() ==> self.spec_seq@[i - 1] == old(self).spec_seq@[i]);
            // assert(forall|i:int|#![auto] old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))  < i < old(self).spec_seq@.len() ==> self.spec_seq@.index_of(old(self).spec_seq@[i]) == i - 1);

            assert(forall| value:usize|  #![auto] old(self).spec_seq@.contains(value) &&  ret != value ==> self.spec_seq@.contains(value));
            assert(forall| value:usize|  #![auto] old(self).spec_seq@.contains(value) == false  ==> self.spec_seq@.contains(value) == false);

            assert(forall| value:usize|  #![auto]  ret != value ==> old(self).spec_seq@.contains(value) == self.spec_seq@.contains(value));
            return ret;
        }

    fn remove_value_by_index_helper1(&mut self, index: Index)
        requires old(self).wf(),
                 old(self).value_list@.contains(index),
                 old(self).value_list_head == index,
        ensures self.free_list_len == old(self).free_list_len,
                 self.array_wf(),
                 self.value_list_len ==  old(self).value_list_len - 1,
                 self.value_list_wf(),
                 self.free_list_wf(),
                 forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.value_list@.contains(i),
                 self.free_list@.contains(index) == false,
                 self.value_list@.contains(index) == false,
                 self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).spec_seq@.subrange(old(self).value_list@.index_of(index) + 1, old(self).spec_seq@.len() as int)),
                 self.spec_seq_wf(),
                 0 <= index < N,
                 self.value_list@ == old(self).value_list@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).value_list@.subrange(old(self).value_list@.index_of(index) + 1, old(self).value_list@.len() as int)),
                 forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==>
                     self.arr_seq@[i].value == old(self).arr_seq@[i].value,
    {
        assert(self.value_list_head != -1);
        assert(self.value_list_tail != -1);
        if self.value_list_len == 1{
            assert(self.value_list_head == self.value_list_tail);
            self.value_list_head = -1;
            self.value_list_tail = -1;
            proof{self.value_list@ = self.value_list@.subrange(1,self.value_list@.len() as int);
                  self.spec_seq@ = self.spec_seq@.subrange(1,self.spec_seq@.len() as int);
            }
            self.value_list_len = 0;
            assert(self.value_list_wf());
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
            assert(self.wf_free_node_head());
            assert(self.wf_free_node_tail());
            assert(self.free_list_len == self.free_list@.len());
            assert(self.free_list_wf());

            assert(self.spec_seq_wf());
        }else{
            assert(self.value_list_len > 1);
            assert(self.wf_value_node_head());
            assert(self.value_list_head == self.value_list@[0]);
            assert(self.prev_value_node_of(0) == -1);
            assert(self.next_value_node_of(0) != -1);
            let next = self.get_next(self.value_list_head);
            let prev = self.get_prev(self.value_list_head);
            assert(next != -1);
            assert(prev == -1);
            assert(self.free_list@.contains(next) == false);
            assert(self.next_value_node_of(0) == next);
            assert(self.value_list@[1] == next);
            self.set_prev(next, -1);
            assert(self.arr_seq@[next as int].prev == -1);
            proof{self.value_list@ = self.value_list@.subrange(1,self.value_list@.len() as int);
                self.spec_seq@ = self.spec_seq@.subrange(1,self.spec_seq@.len() as int);
            }
            self.value_list_len = self.value_list_len - 1;
            self.value_list_head = next;
            assert(self.value_list@.len() == self.value_list_len);
            assert((forall|i: nat|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] < N) ));
            assert((forall|i: nat|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] >= 0) ));
            assert(self.wf_value_node_head());
            assert(self.wf_value_node_tail());
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == old(self).arr_seq@[old(self).value_list@[i as int + 1] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> old(self).next_value_node_of(i + 1) == self.next_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == self.next_value_node_of(i));
            assert(forall|i: int| #![auto] 1 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == old(self).arr_seq@[old(self).value_list@[i as int + 1] as int].prev);
            assert(forall|i: int| #![auto] 1 <= i < self.value_list@.len() ==> self.prev_value_node_of(i) == old(self).prev_value_node_of(i + 1));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == self.prev_value_node_of(i));
            assert(self.value_list_wf());

            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
            assert(self.wf_free_node_head());
            assert(self.wf_free_node_tail());
            assert(self.free_list_len == self.free_list@.len());
            assert(self.free_list_wf());

            assert(self.spec_seq_wf());
        }
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> old(self).free_list@.contains(i) ^ old(self).value_list@.contains(i));
        // assert(self.free_list@.contains(node_index) == false);
        // assert(self.value_list@.contains(node_index) == false);
        assert(self.free_list == old(self).free_list);
        assert(self.value_list == old(self).value_list@.subrange(1,old(self).value_list@.len() as int));
        assert(index == old(self).value_list@[0]);
        assert(old(self).value_list@.index_of(index) == 0);
        assert(0<= index < N);
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> old(self).free_list@.contains(i) == self.free_list@.contains(i));
        assert(forall|i:Index| #![auto] 0<= i < N && i != index && !old(self).value_list@.contains(i) ==> !self.value_list@.contains(i));
        assert(old(self).value_list@.contains(index) && !self.value_list@.contains(index));

        assert(forall|i:Index| #![auto] 0<= i < N && !old(self).value_list@.contains(i) ==> !self.value_list@.contains(i));

        assert(forall|i:int| #![auto] 0<= i <self.value_list@.len() ==> old(self).value_list@.index_of(self.value_list@[i]) == i + 1);
        assert(forall|i:int| #![auto] 1<= i <old(self).value_list@.len() ==> old(self).value_list@[i] == self.value_list@[i - 1]);
        assert(forall|i:int| #![auto] 1<= i <old(self).value_list@.len() ==> self.value_list@.index_of(old(self).value_list@[i]) == i - 1);
        assert(forall|i:int| #![auto] 1<= i <old(self).value_list@.len() ==> self.value_list@.contains(old(self).value_list@[i]));
        assert(forall|i:Index| #![auto] 0<= i < N && i != index && old(self).value_list@.contains(i) ==> self.value_list@.contains(i));

        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.value_list@.contains(i));

        assert(self.free_list_len == old(self).free_list_len);
        assert(self.array_wf());
        assert(self.value_list_len ==  old(self).value_list_len - 1);
        assert(self.value_list_wf());
        assert(self.free_list_wf());
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.value_list@.contains(i));
        assert(self.free_list@.contains(index) == false);
        assert(self.value_list@.contains(index) == false);

        assert(old(self).spec_seq@.len() == old(self).value_list@.len());
        assert(self.spec_seq@ == old(self).spec_seq@.subrange(1, old(self).value_list@.len() as int));
        assert(old(self).value_list@.index_of(index) == 0);
        assert(self.spec_seq@ == old(self).spec_seq@.subrange(1,old(self).value_list@.len() as int));
        assert(Seq::<usize>::empty().len() == 0);
        assert(self.spec_seq@=~=Seq::<usize>::empty().add(old(self).spec_seq@.subrange(1,old(self).value_list@.len() as int)));
        assert(old(self).spec_seq@.subrange(0,old(self).value_list@.index_of(index)).len() == 0);
        assert( old(self).spec_seq@.subrange(0,old(self).value_list@.index_of(index))=~=Seq::<usize>::empty());
        assert(self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).spec_seq@.subrange(old(self).value_list@.index_of(index) + 1, old(self).spec_seq@.len() as int)));
        assert(self.spec_seq_wf());
        assert(0 <= index < N);
        assert(self.value_list@ == old(self).value_list@.subrange(1, old(self).value_list@.len() as int));
        assert(old(self).value_list@.index_of(index) == 0);
        assert(self.value_list@ == old(self).value_list@.subrange(1,old(self).value_list@.len() as int));
        assert(Seq::<Index>::empty().len() == 0);
        assert(self.value_list@=~=Seq::<Index>::empty().add(old(self).value_list@.subrange(1,old(self).value_list@.len() as int)));
        assert(old(self).value_list@.subrange(0,old(self).value_list@.index_of(index)).len() == 0);
        assert( old(self).value_list@.subrange(0,old(self).value_list@.index_of(index))=~=Seq::<Index>::empty());
        assert(self.value_list@ == old(self).value_list@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).value_list@.subrange(old(self).value_list@.index_of(index) + 1, old(self).value_list@.len() as int)));
        assert(forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> self.arr_seq@[i].value == old(self).arr_seq@[i].value);
    }

    fn remove_value_by_index_helper2(&mut self, index: Index)
        requires old(self).wf(),
                 old(self).value_list@.contains(index),
                 old(self).value_list_head != index,
                 old(self).value_list_tail == index,
        ensures self.free_list_len == old(self).free_list_len,
                 self.array_wf(),
                 self.value_list_len ==  old(self).value_list_len - 1,
                 self.value_list_wf(),
                 self.free_list_wf(),
                 forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.value_list@.contains(i),
                 self.free_list@.contains(index) == false,
                 self.value_list@.contains(index) == false,
                 self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).spec_seq@.subrange(old(self).value_list@.index_of(index) + 1, old(self).spec_seq@.len() as int)),
                 self.spec_seq_wf(),
                 0 <= index < N,
                 self.value_list@ == old(self).value_list@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).value_list@.subrange(old(self).value_list@.index_of(index) + 1, old(self).value_list@.len() as int)),
                 forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==>
                     self.arr_seq@[i].value == old(self).arr_seq@[i].value,
    {
        assert(self.value_list_tail != self.value_list_head);
        assert(self.value_list_len > 1);

        assert(self.value_list_len > 1);
        assert(self.wf_value_node_head());
        assert(self.value_list_tail == self.value_list@[self.value_list@.len() - 1]);
        assert(self.prev_value_node_of((self.value_list@.len() - 1) as int) != -1);
        assert(self.next_value_node_of((self.value_list@.len() - 1) as int) == -1);
        let next = self.get_next(self.value_list_tail);
        let prev = self.get_prev(self.value_list_tail);
        assert(next == -1);
        assert(prev != -1);
        assert(self.free_list@.contains(prev) == false);
        assert(self.prev_value_node_of((self.value_list@.len() - 1) as int) == prev);
        assert(self.value_list@[self.value_list@.len() - 2 as int] == prev);
        self.set_next(prev, -1);
        assert(self.arr_seq@[prev as int].next == -1);
        proof{self.value_list@ = self.value_list@.drop_last();
            self.spec_seq@ = self.spec_seq@.drop_last();
        }
        self.value_list_len = self.value_list_len - 1;
        assert(self.spec_seq_wf());
        self.value_list_tail = prev;
        assert(self.value_list@.len() == self.value_list_len);
        assert((forall|i: int|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] < N) ));
        assert((forall|i: int|  #![auto] 0 <= i < self.value_list@.len() ==> (self.value_list@[i as int] >= 0) ));
        assert(self.wf_value_node_head());
        assert(self.wf_value_node_tail());
        assert(self.value_list_len == self.value_list@.len());
        assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() - 1 ==> self.arr_seq@[self.value_list@[i as int] as int].next == old(self).arr_seq@[old(self).value_list@[i as int] as int].next);
        assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() - 1 ==> old(self).next_value_node_of(i) == self.next_value_node_of(i));
        assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == self.next_value_node_of(i));
        assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == old(self).arr_seq@[old(self).value_list@[i as int] as int].prev);
        assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.prev_value_node_of(i) == old(self).prev_value_node_of(i));
        assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == self.prev_value_node_of(i));
        assert(self.value_list_wf());

        assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
        assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
        assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
        assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
        assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
        assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
        assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
        assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
        assert(self.wf_free_node_head());
        assert(self.wf_free_node_tail());
        assert(self.free_list_len == self.free_list@.len());
        assert(self.free_list_wf());

        assert(self.free_list@.contains(index) == false);
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.value_list@.contains(i));

        assert(self.free_list_len == old(self).free_list_len);
        assert(self.array_wf());
        assert(self.value_list_len ==  old(self).value_list_len - 1);
        assert(self.value_list_wf());
        assert(self.free_list_wf());
        assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.value_list@.contains(i));
        assert(self.free_list@.contains(index) == false);
        assert(self.value_list@.contains(index) == false);

        assert(old(self).spec_seq@.len() == old(self).value_list@.len());
        assert(self.spec_seq@ == old(self).spec_seq@.drop_last());
        assert(old(self).value_list@.index_of(index) == old(self).value_list@.len() - 1);
        assert(self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).value_list@.index_of(index)));
        assert(Seq::<usize>::empty().len() == 0);
        assert(self.spec_seq@=~=old(self).spec_seq@.subrange(0,old(self).value_list@.index_of(index)).add(Seq::<usize>::empty()));
        assert(old(self).spec_seq@.subrange(old(self).value_list@.index_of(index) + 1, old(self).value_list@.len() as int).len() == 0);
        assert(old(self).spec_seq@.subrange(old(self).value_list@.index_of(index) + 1, old(self).value_list@.len() as int)=~=Seq::<usize>::empty());

        assert(self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).spec_seq@.subrange(old(self).value_list@.index_of(index) + 1, old(self).spec_seq@.len() as int)));

        assert(self.spec_seq_wf());
        assert(0 <= index < N);
        assert(self.value_list@ == old(self).value_list@.drop_last());
        assert(self.value_list@ == old(self).value_list@.subrange(0,old(self).value_list@.index_of(index)));
        assert(Seq::<Index>::empty().len() == 0);
        assert(self.value_list@=~~=old(self).value_list@.subrange(0,old(self).value_list@.index_of(index)).add(Seq::<Index>::empty()));
        assert(old(self).value_list@.subrange(old(self).value_list@.index_of(index) + 1, old(self).value_list@.len() as int).len() == 0);
        assert(old(self).value_list@.subrange(old(self).value_list@.index_of(index) + 1, old(self).value_list@.len() as int)=~=Seq::<Index>::empty());
        assert(self.value_list@ == old(self).value_list@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).value_list@.subrange(old(self).value_list@.index_of(index) + 1, old(self).value_list@.len() as int)));
        assert(forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> self.arr_seq@[i].value == old(self).arr_seq@[i].value);
    }

    fn remove_value_by_index_helper3(&mut self, index: Index)
    requires old(self).wf(),
             old(self).value_list@.contains(index),
             old(self).value_list_head != index,
             old(self).value_list_tail != index,
    ensures self.free_list_len == old(self).free_list_len,
             self.array_wf(),
             self.value_list_len ==  old(self).value_list_len - 1,
             self.value_list_wf(),
             self.free_list_wf(),
             forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.value_list@.contains(i),
             self.free_list@.contains(index) == false,
             self.value_list@.contains(index) == false,
             self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).spec_seq@.subrange(old(self).value_list@.index_of(index) + 1, old(self).spec_seq@.len() as int)),
             self.spec_seq_wf(),
             0 <= index < N,
             self.value_list@ == old(self).value_list@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).value_list@.subrange(old(self).value_list@.index_of(index) + 1, old(self).value_list@.len() as int)),
             forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==>
                 self.arr_seq@[i].value == old(self).arr_seq@[i].value,
    {
        assert(self.value_list_tail != self.value_list_head);
        assert(self.value_list_tail != index);
        assert(self.value_list_head != index);
        assert(self.value_list@.contains(index));
        assert(self.value_list@.contains(self.value_list_head));
        assert(self.value_list@.contains(self.value_list_tail));
        assert(self.value_list@.len() >= 3);

        let prev = self.get_prev(index);
        let next = self.get_next(index);
        let index_in_list:Ghost<int> = Ghost(self.value_list@.index_of(index));
        proof{
            //let index_in_list = self.value_list@.index_of(index);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == self.next_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == self.prev_value_node_of(i));
            assert(prev == self.arr_seq@[self.value_list@[index_in_list@ as int] as int].prev);
            assert(next == self.arr_seq@[self.value_list@[index_in_list@ as int] as int].next);
            assert(self.next_value_node_of(index_in_list@) == next);
            assert(self.prev_value_node_of(index_in_list@) == prev);
        }
        assert(self.free_list@.contains(index) == false);
        assert(self.free_list@.contains(prev) == false);
        assert(self.free_list@.contains(next) == false);
        self.set_next(prev, next);
        self.set_prev(next, prev);
        self.value_list_len = self.value_list_len - 1;
        proof{
            self.value_list@ = self.value_list@.subrange(0,index_in_list@).add(self.value_list@.subrange(index_in_list@ + 1, self.value_list@.len() as int));
            self.spec_seq@ = self.spec_seq@.subrange(0,index_in_list@).add(self.spec_seq@.subrange(index_in_list@ + 1, self.spec_seq@.len() as int));
            assert(self.value_list@[index_in_list@ as int] == next);
            assert(self.value_list@[index_in_list@ as int - 1] == prev);
            assert(self.next_value_node_of(index_in_list@ - 1) == next);
            assert(self.prev_value_node_of(index_in_list@) == prev);
            assert(prev == self.arr_seq@[self.value_list@[index_in_list@ as int] as int].prev);
            assert(next == self.arr_seq@[self.value_list@[index_in_list@ as int - 1] as int].next);
            assert(self.arr_seq@[self.value_list@[index_in_list@ as int] as int].prev == self.prev_value_node_of(index_in_list@));
            assert(self.arr_seq@[self.value_list@[index_in_list@ as int - 1] as int].next == self.next_value_node_of(index_in_list@ as int - 1));
            assert(forall|i: int| #![auto] 0 <= i < index_in_list@ - 1 ==> self.arr_seq@[self.value_list@[i as int] as int].next == old(self).arr_seq@[old(self).value_list@[i as int] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < index_in_list@ - 1 ==> self.next_value_node_of(i) == old(self).next_value_node_of(i));
            assert(forall|i: int| #![auto] index_in_list@ <= i < self.value_list@.len() ==> self.next_value_node_of(i) == old(self).next_value_node_of(i + 1));
            assert(forall|i: int| #![auto] index_in_list@ <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == old(self).arr_seq@[old(self).value_list@[i as int + 1] as int].next);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].next == self.next_value_node_of(i));

            assert(forall|i: int| #![auto] 0 <= i < index_in_list@ ==> self.arr_seq@[self.value_list@[i as int] as int].prev == old(self).arr_seq@[old(self).value_list@[i as int] as int].prev);
            assert(forall|i: int| #![auto] 0 <= i < index_in_list@ ==> self.prev_value_node_of(i) == old(self).prev_value_node_of(i));
            assert(forall|i: int| #![auto] index_in_list@ + 1 <= i < self.value_list@.len() ==> self.prev_value_node_of(i) == old(self).prev_value_node_of(i + 1));
            assert(forall|i: int| #![auto] index_in_list@ + 1 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == old(self).arr_seq@[old(self).value_list@[i as int + 1] as int].prev);
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.arr_seq@[self.value_list@[i as int] as int].prev == self.prev_value_node_of(i));
            assert(self.value_list_wf());

            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == old(self).arr_seq@[old(self).free_list@[i as int] as int].next);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next == self.next_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == old(self).arr_seq@[old(self).free_list@[i as int] as int].prev);
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
            assert(forall|i: nat| #![auto] 0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev == self.prev_free_node_of(i));
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] < N) );
            assert(forall|i: nat|  #![auto] 0 <= i < self.free_list@.len() ==> (self.free_list@[i as int] >= 0) );
            assert(self.wf_free_node_head());
            assert(self.wf_free_node_tail());
            assert(self.free_list_len == self.free_list@.len());
            assert(self.free_list_wf());

            assert(self.spec_seq_wf());

            assert(index == old(self).value_list@[index_in_list@]);
            assert(old(self).value_list@.index_of(index) == index_in_list@);
            assert(0<= index < N);
            assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> old(self).free_list@.contains(i) == self.free_list@.contains(i));
            assert(forall|i:Index| #![auto] 0<= i < N && i != index && !old(self).value_list@.contains(i) ==> !self.value_list@.contains(i));
            assert(old(self).value_list@.contains(index) && !self.value_list@.contains(index));

            assert(forall|i:Index| #![auto] 0<= i < N && !old(self).value_list@.contains(i) ==> !self.value_list@.contains(i));

            assert(forall|i:int| #![auto] 0<= i < index_in_list@ ==> old(self).value_list@.index_of(self.value_list@[i]) == i);
            assert(forall|i:int| #![auto] index_in_list@ <= i < self.value_list@.len() ==> old(self).value_list@.index_of(self.value_list@[i]) == i + 1);
            assert(forall|i:int| #![auto] 0<= i < index_in_list@ ==> old(self).value_list@[i] == self.value_list@[i]);
            assert(forall|i:int| #![auto] index_in_list@ + 1<= i < old(self).value_list@.len() ==> old(self).value_list@[i] == self.value_list@[i - 1]);
            // assert(forall|i:int| #![auto] 1<= i <old(self).value_list@.len() ==> self.value_list@.index_of(old(self).value_list@[i]) == i - 1);
            // assert(forall|i:int| #![auto] 1<= i <old(self).value_list@.len() && i != index_in_list@ ==> self.value_list@.contains(old(self).value_list@[i]));
            assert(forall|i:Index| #![auto] 0<= i < N && i != index && old(self).value_list@.contains(i) ==> self.value_list@.contains(i));

            assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.value_list@.contains(i));
        }
        // assert(self.free_list_len == old(self).free_list_len);
        // assert(self.array_wf());
        // assert(self.value_list_len ==  old(self).value_list_len - 1);
        // assert(self.value_list_wf());
        // assert(self.free_list_wf());
        // assert(forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.value_list@.contains(i));
        // assert(self.free_list@.contains(index) == false);
        // assert(self.value_list@.contains(index) == false);
        // assert(self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).spec_seq@.subrange(old(self).value_list@.index_of(index) + 1, old(self).spec_seq@.len() as int)));
        // assert(self.spec_seq_wf());
        // assert(0 <= index < N);
        // assert(self.value_list@ == old(self).value_list@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).value_list@.subrange(old(self).value_list@.index_of(index) + 1, old(self).value_list@.len() as int)));
        // assert(forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==> self.arr_seq@[i].value == old(self).arr_seq@[i].value);
    }

    pub fn remove_value_by_index(&mut self, index: Index)
        requires old(self).wf(),
                 old(self).value_list@.contains(index),
        ensures self.free_list_len == old(self).free_list_len,
                self.array_wf(),
                self.value_list_len ==  old(self).value_list_len - 1,
                self.value_list_wf(),
                self.free_list_wf(),
                forall|i:Index| #![auto] 0<= i < N && i != index ==> self.free_list@.contains(i) ^ self.value_list@.contains(i),
                self.free_list@.contains(index) == false,
                self.value_list@.contains(index) == false,
                self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).spec_seq@.subrange(old(self).value_list@.index_of(index) + 1, old(self).spec_seq@.len() as int)),
                self.spec_seq_wf(),
                0 <= index < N,
                self.value_list@ == old(self).value_list@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).value_list@.subrange(old(self).value_list@.index_of(index) + 1, old(self).value_list@.len() as int)),
                forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==>
                    self.arr_seq@[i].value == old(self).arr_seq@[i].value,
    {
        assert(self.value_list@.len() > 0);
        assert(self.value_list_len > 0);
        assert(self.value_list_head != -1);
        assert(self.value_list_tail != -1);
        assert(self.free_list@.contains(index) == false);
        if index == self.value_list_head {
            self.remove_value_by_index_helper1(index);
        }else if index == self.value_list_tail{
            self.remove_value_by_index_helper2(index);
        }else{
            self.remove_value_by_index_helper3(index);
        }
    }


    pub fn remove(&mut self, index: Index) -> (ret: usize)
        requires old(self).wf(),
                 old(self).node_ref_valid(index),
                 old(self).unique(),
        ensures self.wf(),
                self.value_list_len == old(self).value_list_len - 1,
                ret == old(self).node_ref_resolve(index),
                //self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).spec_seq@.index_of(old(self).node_ref_resolve(index))).add(old(self).spec_seq@.subrange(old(self).spec_seq@.index_of(old(self).node_ref_resolve(index)) + 1, old(self).spec_seq@.len() as int)),
                self.spec_seq@ == old(self).spec_seq@.remove(old(self).spec_seq@.index_of(old(self).node_ref_resolve(index))),
                forall| value:usize|  #![auto]  ret != value ==> old(self).spec_seq@.contains(value) == self.spec_seq@.contains(value),
                    self.spec_seq@.contains(ret) == false,
                forall|_index:Index| old(self).node_ref_valid(_index) && _index != index ==> self.node_ref_valid(_index),
                forall|_index:Index| old(self).node_ref_valid(_index) && _index != index ==> self.node_ref_resolve(_index) == old(self).node_ref_resolve(_index),
                self.unique(),
        {
            self.remove_value_by_index(index);
            let ret = self.get_ptr(index);
            self.set_ptr(index, NULL_POINTER);
            // assert(self.arr_seq@[index as int].value == NULL_POINTER);
            // assert( forall|i: Index| #![auto] 0 <= i < N && i != index ==> self.arr_seq@[i as int].value == old(self).arr_seq@[i as int].value);
            // assert( forall|i: Index| #![auto] old(self).value_list@.contains(i) && i != index ==> self.value_list@.contains(i));
            // assert( forall|i: Index| #![auto] 0 <= i < N && self.arr_seq@[i as int].value != NULL_POINTER ==> self.value_list@.contains(i));
            let ghost_index:Ghost<int> = Ghost(old(self).value_list@.index_of(index));
            // assert(forall|i:int|#![auto] 0 <= i < old(self).value_list@.len() && i != ghost_index@ ==> old(self).value_list@[i] != index);
            // assert(ghost_index@ == old(self).value_list@.index_of(index));
            // assert(self.value_list@ == old(self).value_list@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).value_list@.subrange(old(self).value_list@.index_of(index) + 1, old(self).value_list@.len() as int)));
            // assert(forall|i:int|#![auto] 0 <= i < old(self).value_list@.index_of(index) ==> self.value_list@[i] == old(self).value_list@[i]);
            // assert(forall|i:int|#![auto] 0 <= i < old(self).value_list@.index_of(index) ==> self.value_list@.index_of(old(self).value_list@[i]) == i);
            // assert(forall|i:int|#![auto] old(self).value_list@.index_of(index)  < i < old(self).value_list@.len() ==> self.value_list@[i - 1] == old(self).value_list@[i]);
            // assert(forall|i:int|#![auto] old(self).value_list@.index_of(index)  < i < old(self).value_list@.len() ==> self.value_list@.index_of(old(self).value_list@[i]) == i - 1);

            // assert(forall| _index:Index|  #![auto] old(self).value_list@.contains(_index) &&  index != _index ==> self.value_list@.contains(_index));
            // assert(forall| _index:Index|  #![auto] old(self).value_list@.contains(_index) == false  ==> self.value_list@.contains(_index) == false);

            // assert(forall| _index:Index|  #![auto]  index != _index ==> old(self).value_list@.contains(_index) == self.value_list@.contains(_index));
            // assert(self.free_list_ptr_all_null());

            // assert(self.value_list_len == old(self).value_list_len - 1);
            // assert(self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).spec_seq@.subrange(old(self).value_list@.index_of(index) + 1, old(self).spec_seq@.len() as int)));
            // assert(self.value_list@ == old(self).value_list@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).value_list@.subrange(old(self).value_list@.index_of(index) + 1, old(self).value_list@.len() as int)));
            assert(ret == old(self).arr_seq@[index as int].value);


            self.free_node(index);

            // let ghost_index:Ghost<int> = ghost(old(self).value_list@.index_of(index));
            // let ghost_ptr:Ghost<usize> = ghost(old(self).spec_seq@[ghost_index@ as int]);
            // assert(old(self).arr_seq@[old(self).value_list@[ghost_index@ as int] as int].value == old(self).spec_seq@[ghost_index@ as int]);
            // assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.len() && i != ghost_index@ ==> old(self).spec_seq@[i] != ghost_ptr@);
            // assert(ghost_index@ == old(self).spec_seq@.index_of(ghost_ptr@));
            // assert(self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))).add(old(self).spec_seq@.subrange(old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) + 1, old(self).spec_seq@.len() as int)));
            // assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) ==> self.spec_seq@[i] == old(self).spec_seq@[i]);
            // assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) ==> self.spec_seq@.index_of(old(self).spec_seq@[i]) == i);
            // assert(forall|i:int|#![auto] old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))  < i < old(self).spec_seq@.len() ==> self.spec_seq@[i - 1] == old(self).spec_seq@[i]);
            // assert(forall|i:int|#![auto] old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))  < i < old(self).spec_seq@.len() ==> self.spec_seq@.index_of(old(self).spec_seq@[i]) == i - 1);

            // assert(forall| value:usize|  #![auto] old(self).spec_seq@.contains(value) &&  ghost_ptr@ != value ==> self.spec_seq@.contains(value));
            assert(old(self).arr_seq@[old(self).value_list@[ghost_index@ as int] as int].value == old(self).spec_seq@[ghost_index@ as int]);
            assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.len() && i != ghost_index@ ==> old(self).spec_seq@[i] != ret);
            assert(ghost_index@ == old(self).spec_seq@.index_of(ret));
            assert(self.spec_seq@ == old(self).spec_seq@.subrange(0,old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))).add(old(self).spec_seq@.subrange(old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) + 1, old(self).spec_seq@.len() as int)));
            assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) ==> self.spec_seq@[i] == old(self).spec_seq@[i]);
            assert(forall|i:int|#![auto] 0 <= i < old(self).spec_seq@.index_of(old(self).spec_get_ptr(index)) ==> self.spec_seq@.index_of(old(self).spec_seq@[i]) == i);
            assert(forall|i:int|#![auto] old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))  < i < old(self).spec_seq@.len() ==> self.spec_seq@[i - 1] == old(self).spec_seq@[i]);
            assert(forall|i:int|#![auto] old(self).spec_seq@.index_of(old(self).spec_get_ptr(index))  < i < old(self).spec_seq@.len() ==> self.spec_seq@.index_of(old(self).spec_seq@[i]) == i - 1);

            assert(forall| value:usize|  #![auto] old(self).spec_seq@.contains(value) &&  ret != value ==> self.spec_seq@.contains(value));
            assert(forall| value:usize|  #![auto] old(self).spec_seq@.contains(value) == false  ==> self.spec_seq@.contains(value) == false);

            assert(forall| value:usize|  #![auto]  ret != value ==> old(self).spec_seq@.contains(value) == self.spec_seq@.contains(value));

            assert(forall|i:int|#![auto] 0 <= i < old(self).value_list@.len() && i != ghost_index@ ==> old(self).value_list@[i] != index);
            assert(ghost_index@ == old(self).value_list@.index_of(index));
            assert(self.value_list@ == old(self).value_list@.subrange(0,old(self).value_list@.index_of(index)).add(old(self).value_list@.subrange(old(self).value_list@.index_of(index) + 1, old(self).value_list@.len() as int)));
            assert(forall|i:int|#![auto] 0 <= i < old(self).value_list@.index_of(index) ==> self.value_list@[i] == old(self).value_list@[i]);
            assert(forall|i:int|#![auto] 0 <= i < old(self).value_list@.index_of(index) ==> self.value_list@.index_of(old(self).value_list@[i]) == i);
            assert(forall|i:int|#![auto] old(self).value_list@.index_of(index)  < i < old(self).value_list@.len() ==> self.value_list@[i - 1] == old(self).value_list@[i]);
            assert(forall|i:int|#![auto] old(self).value_list@.index_of(index)  < i < old(self).value_list@.len() ==> self.value_list@.index_of(old(self).value_list@[i]) == i - 1);

            assert(forall| _index:Index|  #![auto] old(self).value_list@.contains(_index) &&  index != _index ==> self.value_list@.contains(_index));
            assert(self.wf());
            return ret;
        }

    // fn test(sll: &mut StaticLinkedList<2>)
    //     requires
    //         old(sll).wf(),
    //         old(sll).arr_seq@.len() == 2,
    //         old(sll).get_raw_element(0).next == 0,

    // {
    //     assert(sll.get_raw_element(0).next == 0);
    //     sll.set_ptr(0,0x10);
    //     assert(sll.get_raw_element(0).value == 0x10);
    //     assert(sll.get_raw_element(0).next == 0);
    // }

}

}

fn main(){}
