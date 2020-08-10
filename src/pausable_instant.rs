use std::time::{Duration, Instant};

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct PausableInstant {
    zero_instant: Instant,
    pub(crate) elapsed_millis: u64,
}

impl PausableInstant {
    pub(crate) fn new(
        zero_instant: Instant,
        elapsed_millis: u64,
    ) -> PausableInstant {
        PausableInstant {
            zero_instant,
            elapsed_millis,
        }
    }

    pub fn as_std(&self) -> Instant {
        self.zero_instant + Duration::from_millis(self.elapsed_millis)
    }
}
