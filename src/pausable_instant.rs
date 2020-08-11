use std::time::{Duration, Instant};

/// Native representation of a paused instant that contains the reference time
/// and the elapsed time on the clock from the reference time.
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

    /// Get this pausable instant's elapsed millis.
    pub fn elapsed_millis(&self) -> u64 {
        self.elapsed_millis
    }

    /// Get the instant this pausable instant is referenced off of
    pub fn zero_instant(&self) -> Instant {
        self.zero_instant
    }
}

impl From<PausableInstant> for Instant {
    fn from(source: PausableInstant) -> Self {
        source.zero_instant + Duration::from_millis(source.elapsed_millis)
    }
}
