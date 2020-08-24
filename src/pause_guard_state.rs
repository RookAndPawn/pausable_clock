pub(super) const PAUSING_REQUESTED_MASK: u32 = 1 << 31;
const FLAG_MASK: u32 = PAUSING_REQUESTED_MASK;
const PAUSE_GUARD_COUNT_MASK: u32 = !FLAG_MASK;

pub(super) type PauseGuardState = u32;

pub(super) trait PauseGuardStateTrait {
    fn is_pausing_requested(&self) -> bool;

    fn get_pause_guard_count(&self) -> u32;
}

impl PauseGuardStateTrait for PauseGuardState {
    fn is_pausing_requested(&self) -> bool {
        *self & PAUSING_REQUESTED_MASK > 0
    }

    fn get_pause_guard_count(&self) -> u32 {
        *self & PAUSE_GUARD_COUNT_MASK
    }
}
