//! Component for a cooperative scheduler.
//!
//! This provides one Component, CooperativeComponent.
//!
//! Usage
//! -----
//! ```rust
//! let scheduler = components::cooperative::CooperativeComponent::new(&PROCESSES)
//!     .finalize(components::coop_component_helper!(NUM_PROCS));
//! ```

// Author: Hudson Ayers <hayers@stanford.edu>

use core::mem::MaybeUninit;
use kernel::component::Component;
use kernel::scheduler::cooperative::{CoopProcessNode, CooperativeSched};
use kernel::{static_init, static_init_half, ProcEntry};

#[macro_export]
macro_rules! coop_component_helper {
    ($N:expr $(,)?) => {{
        use core::mem::MaybeUninit;
        use kernel::scheduler::cooperative::CoopProcessNode;
        use kernel::static_buf;
        const UNINIT: MaybeUninit<CoopProcessNode<'static>> = MaybeUninit::uninit();
        static mut BUF: [MaybeUninit<CoopProcessNode<'static>>; $N] = [UNINIT; $N];
        &mut BUF
    };};
}

pub struct CooperativeComponent {
    processes: &'static [ProcEntry],
}

impl CooperativeComponent {
    pub fn new(processes: &'static [ProcEntry]) -> CooperativeComponent {
        CooperativeComponent { processes }
    }
}

impl Component for CooperativeComponent {
    type StaticInput = &'static mut [MaybeUninit<CoopProcessNode<'static>>];
    type Output = &'static mut CooperativeSched<'static>;

    unsafe fn finalize(self, proc_nodes: Self::StaticInput) -> Self::Output {
        let scheduler = static_init!(CooperativeSched<'static>, CooperativeSched::new());

        for (i, node) in proc_nodes.iter_mut().enumerate() {
            let init_node = static_init_half!(
                node,
                CoopProcessNode<'static>,
                CoopProcessNode::new(&self.processes[i].proc_ref)
            );
            scheduler.processes.push_head(init_node);
        }
        scheduler
    }
}
