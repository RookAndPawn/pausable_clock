const PAUSED_MASK: u64 = 1 << 63;
const PAUSING_MASK: u64 = 1 << 62;
const TIME_FROZEN_MASK: u64 = 1 << 61;
const RESUMING_MASK: u64 = 1 << 60;
const FLAG_MASK: u64 =
    PAUSED_MASK + PAUSING_MASK + TIME_FROZEN_MASK + RESUMING_MASK;
const ELAPSED_MILLIS_MASK: u64 = !FLAG_MASK;

pub(crate) type PauseState = u64;

pub(crate) trait PauseStateTrait {
    fn new(
        paused: bool,
        pausing: bool,
        time_frozen: bool,
        resuming_flag: bool,
        millis: u64,
    ) -> PauseState;

    fn is_paused(&self) -> bool;

    fn is_pausing(&self) -> bool;

    fn is_resuming(&self) -> bool;

    fn is_resumed(&self) -> bool;

    fn get_millis(&self) -> u64;

    fn is_paused_or_pausing(&self) -> bool;

    fn is_resumed_or_resuming(&self) -> bool;

    fn is_time_paused(&self) -> bool;

    fn with_pausing_flag(&self) -> PauseState;
}

impl PauseStateTrait for PauseState {
    fn new(
        paused: bool,
        pausing: bool,
        time_frozen: bool,
        resuming_flag: bool,
        millis: u64,
    ) -> PauseState {
        millis
            + if paused { PAUSED_MASK } else { 0 }
            + if pausing { PAUSING_MASK } else { 0 }
            + if time_frozen { TIME_FROZEN_MASK } else { 0 }
            + if resuming_flag { RESUMING_MASK } else { 0 }
    }

    fn is_paused(&self) -> bool {
        *self & PAUSED_MASK > 0
    }

    fn is_pausing(&self) -> bool {
        *self & PAUSING_MASK > 0
    }

    fn is_resuming(&self) -> bool {
        *self & RESUMING_MASK > 0
    }

    fn is_resumed(&self) -> bool {
        *self & FLAG_MASK == 0
    }

    fn get_millis(&self) -> u64 {
        *self & ELAPSED_MILLIS_MASK
    }

    fn is_paused_or_pausing(&self) -> bool {
        (*self & PAUSED_MASK) + (*self & PAUSING_MASK) > 0
    }

    fn is_resumed_or_resuming(&self) -> bool {
        !self.is_paused_or_pausing()
    }

    fn is_time_paused(&self) -> bool {
        *self & TIME_FROZEN_MASK > 0
    }

    fn with_pausing_flag(&self) -> PauseState {
        *self | PAUSING_MASK
    }
}
