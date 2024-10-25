use crate::define::*;
use core::mem::MaybeUninit;
use vstd::prelude::*;
verus! {
    #[repr(align(4096))]
    pub struct DeviceTable{
        ar:[usize;512],
    }


    // impl DeviceTable{
    //     pub open spec fn wf(&self) {
    //         self.seq_ar@.len() == 256,
    //     }

    //     #[verifier(inline)]
    //     pub fn get(&self, dev:usize, fun:usize) -> (ret:usize)
    //         requires
    //             self.wf(),
    //             0<=dev<32,
    //             0<=fun<8,
    //         ensures
    //             ret == self.seq_ar@[dev*fun]
    //     {
    //         return self.ar[dev*fun];
    //     }

    //     #[verifier(inline)]
    //     pub fn set(&mut self, dev:usize, fun:usize, cr3:usize) -> (ret:usize)
    //         requires
    //             self.wf(),
    //             0<=dev<32,
    //             0<=fun<8,
    //         ensures
    //             ret == self.seq_ar@.update(dev*fun, cr3);
    //             self.wf(),
    //     {
    //         self.ar[dev*fun] = cr3;
    //     }
    // }

    #[repr(align(4096))]
    pub struct RootTable{
        root:[usize;512],
        seq_ar: Ghost<Seq<Seq<Seq<Option<(IOid,usize)>>>>>,

        deviecs:[DeviceTable;256],
    }

    impl RootTable{

        #[verifier(external_body)]
        pub fn new() -> (ret: Self)
        {
            unsafe{
                RootTable{
                    root: MaybeUninit::uninit().assume_init(),
                    seq_ar: Ghost(Seq::empty()),

                    deviecs: MaybeUninit::uninit().assume_init(),
                }
            }
        }

        #[verifier(external_body)]
        pub fn init(&mut self)
            ensures
                self.wf(),
                forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 ==> self.resolve(bus,dev,fun).is_None(),
        {
            let mut i = 0;
            while i != 256 {
                self.root[i*2] = 0;
                self.root[i*2+1] = &self.deviecs[i] as * const DeviceTable as usize | 0x1b;
                i = i + 1;
            }
            let mut i = 0;
            let mut j = 0;
            while i != 256 {
                j = 0;
                while j != 512{
                    self.deviecs[i].ar[j] = 0;
                    j = j + 1;
                }
                i = i + 1;
            }
        }

        pub closed spec fn wf(&self) -> bool{
            self.seq_ar@.len() == 256
            &&
            forall|bus:u8|#![auto] 0<=bus<256 ==> self.seq_ar@[bus as int].len() == 32
            &&
            forall|bus:u8,dev:u8|#![auto] 0<=bus<256 && 0<=dev<32 ==> self.seq_ar@[bus as int][dev as int].len() == 8
        }

        pub closed spec fn resolve(&self, bus:u8, dev:u8, fun:u8) -> Option<(IOid, usize)>
            recommends
                self.wf(),
                0<=bus<256 && 0<=dev<32 && 0<=fun<8,
        {
            None
        }

        #[verifier(external_body)]
        pub fn get_ioid(&self, bus:u8, dev:u8, fun:u8) -> (ret: Option<(IOid, usize)>)
            requires
                self.wf(),
                0<=bus<256 && 0<=dev<32 && 0<=fun<8,
            ensures
                ret =~= self.resolve(bus,dev,fun)
        {
            let p = self.deviecs[bus as usize].ar[((dev*fun)*2 + 1) as usize] & 0x1b;
            if p == 0{
                return None;
            }
            let ioid = self.deviecs[bus as usize].ar[((dev*fun)*2) as usize] & 0x7FFF00 as usize;
            let cr3 = self.deviecs[bus as usize].ar[((dev*fun)*2 + 1) as usize] & 0xFFFFFFFFFFFFF000 as usize;
            return Some((ioid,cr3));
        }

        #[verifier(external_body)]
        pub fn set(&mut self, bus:u8, dev:u8, fun:u8, target:Option<(IOid,usize)>)
            requires
                old(self).wf(),
                0<=bus<256 && 0<=dev<32 && 0<=fun<8,
            ensures
                self.wf(),
                self.resolve(bus,dev,fun) == target,
                forall|_bus:u8,_dev:u8,_fun:u8|#![auto] 0<=_bus<256 && 0<=_dev<32 && 0<=_fun<8 &&
                    (_bus != bus || _dev != dev || _fun != fun)
                    ==> self.resolve(_bus,_dev,_fun) =~= old(self).resolve(_bus,_dev,_fun)
        {
            if target.is_none(){
                self.deviecs[bus as usize].ar[((dev*fun)*2) as usize] = 0;
                self.deviecs[bus as usize].ar[((dev*fun)*2 + 1) as usize] = 0;
            }
            else{
                self.deviecs[bus as usize].ar[((dev*fun)*2) as usize] = ((target.unwrap().0 << 8) & 0x7FFF00) | (0x010b);
                self.deviecs[bus as usize].ar[((dev*fun)*2 + 1) as usize] = (target.unwrap().1 & 0xFFFFFFFFFFFFF000) | (0x1001b);
            }
        }
    }
}
