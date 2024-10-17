use vstd::prelude::*;
verus! {
    use crate::define::*;

    #[derive(Clone, Copy)]
    pub struct Cpu{
        pub owning_container: ContainerPtr,
        pub current_thread: Option<ThreadPtr>,
    }
}