pub(super) const RESUMING_REQUESTED_MASK: u32 = 1 << 31;
const FLAG_MASK: u32 = RESUMING_REQUESTED_MASK;
const UNRESUMABLE_TASK_COUNT_MASK: u32 = !FLAG_MASK;

pub(super) type ResumabilityState = u32;

pub(super) trait ResumabilityStateTrait {
    fn is_resuming_requested(&self) -> bool;

    fn get_unresumable_task_count(&self) -> u32;
}

impl ResumabilityStateTrait for ResumabilityState {
    fn is_resuming_requested(&self) -> bool {
        *self & RESUMING_REQUESTED_MASK > 0
    }

    fn get_unresumable_task_count(&self) -> u32 {
        *self & UNRESUMABLE_TASK_COUNT_MASK
    }
}
