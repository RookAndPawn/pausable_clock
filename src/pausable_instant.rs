use std::convert::TryFrom;
use std::ops::{Add, AddAssign, Sub, SubAssign};
use std::time::{Duration, Instant};

use crate::PausableClock;

/// Native representation of a paused instant that contains the reference time
/// and the elapsed time on the clock from the reference time.
///
/// # Note on PartialOrd/Ord
///
/// The derived Ord and PartialOrd behavior is only valid for PausableInstants
/// from the same clock. While the compare functions from ord and partial_ord
/// can be called on PausableInstants from different clocks without panics, the
/// results will have no guaranteed order
#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
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

    /// Get the elapsed time since this instant according to the given (and
    /// ideally originating) clock.
    ///
    /// #Panics
    ///
    /// This function will panic If the given clock produces a `now()` instant
    /// that is "before" this one. This is guaranteed _not_ to happen if the
    /// given clock is the originating clock
    pub fn elapsed(&self, originating_clock: &PausableClock) -> Duration {
        let now_millis = originating_clock.now();

        if now_millis.elapsed_millis < self.elapsed_millis {
            panic!("Supplied clock's instant is earlier than self");
        }

        Duration::from_millis(now_millis.elapsed_millis - self.elapsed_millis)
    }

    /// Returns the amount of time elapsed from another instant to this one
    /// according to the pausable clock. Ideally the given instant is from the
    /// same pausable clock otherwise the resulting duration is meaningless.
    ///
    /// #Panics
    ///
    /// This function will panic if the given instant is "later" than this one.
    pub fn duration_since(&self, earlier: PausableInstant) -> Duration {
        if earlier.elapsed_millis > self.elapsed_millis {
            panic!("Supplied instant is later than self");
        }

        Duration::from_millis(self.elapsed_millis - earlier.elapsed_millis)
    }

    /// Returns the amount of time elapsed from another instant to this one
    /// according to the pausable clock. Ideally the given instant is from the
    /// same pausable clock otherwise the resulting duration is meaningless.
    ///
    /// This function will return None if the given instant is "later" than this
    /// one.
    pub fn checked_duration_since(
        &self,
        earlier: &PausableInstant,
    ) -> Option<Duration> {
        if earlier.elapsed_millis > self.elapsed_millis {
            None
        } else {
            Some(Duration::from_millis(
                self.elapsed_millis - earlier.elapsed_millis,
            ))
        }
    }

    /// Returns the amount of time elapsed from another instant to this one
    /// according to the pausable clock. Ideally the given instant is from the
    /// same pausable clock otherwise the resulting duration is meaningless.
    ///
    /// This function will return zero if the given instant is "later" than this
    /// one.
    pub fn saturating_duration_since(
        &self,
        earlier: &PausableInstant,
    ) -> Duration {
        if earlier.elapsed_millis > self.elapsed_millis {
            Duration::default()
        } else {
            Duration::from_millis(self.elapsed_millis - earlier.elapsed_millis)
        }
    }

    /// Returns `Some(t)` where `t` is the time `self + duration` if the given
    /// duration can be represented in milliseconds as a u64 and this
    /// pausable instant's elapsed milliseconds plus the duration in millis can
    /// also be represented as a u64.
    ///
    /// Effectively this means the resulting duration since the elapse millis
    /// needs to be less than about 500 million years.
    pub fn checked_add(&self, duration: Duration) -> Option<PausableInstant> {
        Some(PausableInstant {
            zero_instant: self.zero_instant,
            elapsed_millis: self
                .elapsed_millis
                .checked_add(u64::try_from(duration.as_millis()).ok()?)?,
        })
    }

    /// Returns `Some(t)` where `t` is the time `self - duration` if the given
    /// duration can be represented in milliseconds as a u64, and this
    /// pausable instant's elapsed milliseconds >= the duration in milliseconds
    ///
    /// Effectively this means the given duration needs to be less than about
    /// 500 million years, and the resulting instant cannot be before the zero
    /// instant of this pausable instant.
    pub fn checked_sub(&self, duration: Duration) -> Option<PausableInstant> {
        Some(PausableInstant {
            zero_instant: self.zero_instant,
            elapsed_millis: self
                .elapsed_millis
                .checked_sub(u64::try_from(duration.as_millis()).ok()?)?,
        })
    }
}

impl From<PausableInstant> for Instant {
    /// Convert from the given pausable instant to a std instant. This is
    /// helpful for working with other libraries that need time info, but it has
    /// minor risks because once converted to a std instant, functions like
    /// `elapsed()` and `duration_since()` will produce unexpected results
    /// because those functions compare against the actual time and not the
    /// pausable time.
    fn from(source: PausableInstant) -> Self {
        source.zero_instant + Duration::from_millis(source.elapsed_millis)
    }
}

impl Add<Duration> for PausableInstant {
    type Output = PausableInstant;

    /// #Panics
    ///
    /// This function may panic if the resulting point in time cannot be
    /// represented by the underlying data structure. See
    /// [`PausableInstant::checked_add`] for a version without panic.
    fn add(self, other: Duration) -> Self::Output {
        self.checked_add(other)
            .expect("Overflow when adding duration to pausable instant")
    }
}

impl AddAssign<Duration> for PausableInstant {
    fn add_assign(&mut self, other: Duration) {
        *self = *self + other;
    }
}

impl Sub<Duration> for PausableInstant {
    type Output = PausableInstant;

    /// #Panics
    ///
    /// This function may panic if the resulting point in time cannot be
    /// represented by the underlying data structure. See
    /// [`PausableInstant::checked_sub`] for a version without panic.
    fn sub(self, other: Duration) -> PausableInstant {
        self.checked_sub(other)
            .expect("Overflow when subtracting duration from instant")
    }
}

impl SubAssign<Duration> for PausableInstant {
    fn sub_assign(&mut self, other: Duration) {
        *self = *self - other;
    }
}

impl Sub<PausableInstant> for PausableInstant {
    type Output = Duration;

    fn sub(self, other: PausableInstant) -> Duration {
        self.duration_since(other)
    }
}

#[cfg(test)]
mod tests {

    #[cfg(not(loom))]
    use std::thread::sleep;

    #[cfg(loom)]
    use loom::sleep;

    use super::*;
    use crate::PausableClock;

    #[test]
    fn test_elapsed() {
        let clock = PausableClock::default();
        let t1 = clock.now();

        sleep(Duration::from_secs(1));

        clock.pause();
        let expected_elapsed = t1.elapsed(&clock);

        sleep(Duration::from_secs(1));

        // Verify the elapsed time doesn't change while the clock is paused
        assert_eq!(expected_elapsed, t1.elapsed(&clock));

        // Verify the elapsed time is roughly 1s. Sleep is very inaccurate on
        // some platforms, so we are just making sure that the sleep was within
        // 10% of the expected duration
        assert!(expected_elapsed.as_secs_f64() > 1.);
        assert!((expected_elapsed.as_secs_f64() - 1.) <= 0.1);
    }

    #[test]
    #[should_panic(expected = "Supplied clock's instant is earlier than self")]
    fn test_elapsed_fail() {
        let early_clock = PausableClock::new(Duration::from_millis(0), true);
        let late_clock = PausableClock::new(Duration::from_millis(100), true);

        late_clock.now().elapsed(&early_clock);
    }

    #[test]
    fn test_duration_since() {
        let zero_instant = Instant::now();

        let t1 = PausableInstant {
            zero_instant,
            elapsed_millis: 100,
        };
        let t2 = PausableInstant {
            zero_instant,
            elapsed_millis: 300,
        };

        assert_eq!(Duration::from_millis(200), t2.duration_since(t1));
    }

    #[test]
    #[should_panic(expected = "Supplied instant is later than self")]
    fn test_duration_since_fail() {
        let zero_instant = Instant::now();

        let early_time = PausableInstant {
            zero_instant,
            elapsed_millis: 100,
        };
        let late_time = PausableInstant {
            zero_instant,
            elapsed_millis: 300,
        };

        let _ = early_time.duration_since(late_time);
    }

    #[test]
    fn test_checked_add() {
        let zero_instant = Instant::now();

        let t1 = PausableInstant {
            zero_instant,
            elapsed_millis: 200,
        };

        let expected = PausableInstant {
            zero_instant,
            elapsed_millis: 500,
        };

        assert_eq!(Some(expected), t1.checked_add(Duration::from_millis(300)));

        // Check cases the result in None

        assert_eq!(None, t1.checked_add(Duration::from_secs(u64::MAX)));

        let max_instant = PausableInstant {
            zero_instant,
            elapsed_millis: u64::MAX,
        };

        assert_eq!(None, max_instant.checked_add(Duration::from_millis(1)));
    }

    #[test]
    fn test_checked_sub() {
        let zero_instant = Instant::now();

        let t1 = PausableInstant {
            zero_instant,
            elapsed_millis: 500,
        };

        let expected = PausableInstant {
            zero_instant,
            elapsed_millis: 200,
        };

        assert_eq!(Some(expected), t1.checked_sub(Duration::from_millis(300)));

        // Check cases the result in None

        assert_eq!(None, t1.checked_sub(Duration::from_secs(u64::MAX)));

        assert_eq!(None, expected.checked_sub(Duration::from_millis(300)));
    }
}
