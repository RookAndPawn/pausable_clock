const PAUSED_MASK: u64 = 1 << 63;
const PAUSING_MASK: u64 = 1 << 62;
const FLAG_MASK: u64 = PAUSED_MASK + PAUSING_MASK;
const ELAPSED_MILLIS_MASK: u64 = !FLAG_MASK;

pub(crate) type PauseState = u64;

pub(crate) trait PauseStateTrait {
    fn new(paused: bool, pausing: bool, millis: u64) -> PauseState;

    fn is_paused(&self) -> bool;

    fn is_pausing(&self) -> bool;

    fn get_millis(&self) -> u64;

    fn is_read_time_frozen(&self) -> bool;
}

impl PauseStateTrait for PauseState {
    fn new(paused: bool, pausing: bool, millis: u64) -> PauseState {
        millis
            + if paused { PAUSED_MASK } else { 0 }
            + if pausing { PAUSING_MASK } else { 0 }
    }

    fn is_paused(&self) -> bool {
        *self & PAUSED_MASK > 0
    }

    fn is_pausing(&self) -> bool {
        *self & PAUSING_MASK > 0
    }

    fn get_millis(&self) -> u64 {
        *self & ELAPSED_MILLIS_MASK
    }

    fn is_read_time_frozen(&self) -> bool {
        *self & FLAG_MASK > 0
    }
}
