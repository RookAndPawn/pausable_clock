pub(super) const PAUSING_REQUESTED_MASK: u32 = 1 << 31;
const FLAG_MASK: u32 = PAUSING_REQUESTED_MASK;
const UNPAUSABLE_TASK_COUNT_MASK: u32 = !FLAG_MASK;

pub(super) type PausabilityState = u32;

pub(super) trait PausabilityStateTrait {
    fn is_pausing_requested(&self) -> bool;

    fn get_unpausable_task_count(&self) -> u32;
}

impl PausabilityStateTrait for PausabilityState {
    fn is_pausing_requested(&self) -> bool {
        *self & PAUSING_REQUESTED_MASK > 0
    }

    fn get_unpausable_task_count(&self) -> u32 {
        *self & UNPAUSABLE_TASK_COUNT_MASK
    }
}
