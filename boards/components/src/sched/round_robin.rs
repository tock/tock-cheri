//! Component for a round robin scheduler.
//!
//! This provides one Component, RoundRobinComponent.
//!
//! Usage
//! -----
//! ```rust
//! let scheduler = components::round_robin::RoundRobinComponent::new(&PROCESSES)
//!     .finalize(components::rr_component_helper!(NUM_PROCS));
//! ```

// Author: Hudson Ayers <hayers@stanford.edu>
// Last modified: 03/31/2020

use core::mem::MaybeUninit;
use kernel::collections::list::ListLink;
use kernel::component::Component;
use kernel::new_const_array;
use kernel::scheduler::round_robin::{RoundRobinProcessNode, RoundRobinSched};
use kernel::{simple_static_component, static_init, static_init_half, ProcEntry};

#[macro_export]
macro_rules! rr_component_helper {
    ($N:expr $(,)?) => {{
        use core::mem::MaybeUninit;
        use kernel::scheduler::round_robin::RoundRobinProcessNode;
        use kernel::static_buf;
        const UNINIT: MaybeUninit<RoundRobinProcessNode<'static>> = MaybeUninit::uninit();
        static mut BUF: [MaybeUninit<RoundRobinProcessNode<'static>>; $N] = [UNINIT; $N];
        &mut BUF
    };};
}

pub struct RoundRobinComponent {
    processes: &'static [ProcEntry],
}

impl RoundRobinComponent {
    pub fn new(processes: &'static [ProcEntry]) -> RoundRobinComponent {
        RoundRobinComponent { processes }
    }
}

impl Component for RoundRobinComponent {
    type StaticInput = &'static mut [MaybeUninit<RoundRobinProcessNode<'static>>];
    type Output = &'static mut RoundRobinSched<'static>;

    unsafe fn finalize(self, buf: Self::StaticInput) -> Self::Output {
        let scheduler = static_init!(RoundRobinSched<'static>, RoundRobinSched::new());

        for (i, node) in buf.iter_mut().enumerate() {
            let init_node = static_init_half!(
                node,
                RoundRobinProcessNode<'static>,
                RoundRobinProcessNode::new(&self.processes[i].proc_ref)
            );
            scheduler.processes.push_head(init_node);
        }
        scheduler
    }
}

pub struct RoundRobinSchedWithQueue<const N_PROCS: usize> {
    sched: RoundRobinSched<'static>,
    queue: [RoundRobinProcessNode<'static>; N_PROCS],
}

impl<const N_PROCS: usize> RoundRobinSchedWithQueue<N_PROCS> {
    pub fn get_sched(&self) -> &RoundRobinSched<'static> {
        &self.sched
    }
}

pub struct StaticRoundRobinComponent<const N_PROCS: usize>();

simple_static_component!(impl<{const N_PROCS : usize}> for StaticRoundRobinComponent<N_PROCS>,
    Output = RoundRobinSchedWithQueue<N_PROCS>,
    NewInput =  &'static [ProcEntry],
    FinInput = (),
    | slf, input | {
        let (hd, proc_list) = new_const_array!([RoundRobinProcessNode<'static>; N_PROCS], ListLink::empty(), | link, i | {
            (RoundRobinProcessNode::new_with_next(&input[i].proc_ref, link), ListLink::new(&slf.queue[i]))
        });
        RoundRobinSchedWithQueue{ sched :RoundRobinSched::new_with_head(hd), queue : proc_list }
    },
    | _slf, _input | {}
);
