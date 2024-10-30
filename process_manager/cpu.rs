use vstd::prelude::*;
verus! {
    use crate::define::*;

    #[derive(Clone, Copy)]
    pub struct Cpu{
        pub owning_container: ContainerPtr,
        pub active: bool,
        pub current_thread: Option<ThreadPtr>,
    }
}