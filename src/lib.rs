//! # Pausable Clock
//!
//! This crate provides a clock that can be paused ... (duh?). The provided
//! struct `PausableClock` allows you to get the current time in a way that
//! respects the atomic state and history of the clock.  Put more simply, a
//! pausable clock's elapsed time increases at the same as real time but only
//! when the clock is resumed.
//!
//! ## Features
//! - Thread-Safe: (`Send`/`Sync`) All operations on the clock are atomic or use
//! std mutexes
//! - Resume Notification: the `wait_for_resume` method will block until the
//! clock is resumed (if the clock is paused)
//! - Guarantees: Just like `std::time::Instant::now()` guarantees that [time
//! always increases](https://doc.rust-lang.org/src/std/time.rs.html#238),
//! `PausableClock` guarantees that the time returned by `clock.now()` while the
//! clock is paused is >= any other instant returned before the clock was paused.
//!
//! ## Example
//!
//! ```rust
//! # use std::sync::Arc;
//! # use pausable_clock::PausableClock;
//! # use std::time::{Duration, Instant};
//! # use std::thread;
//!
//! let clock = Arc::new(PausableClock::default());
//!
//! // With the default parameters, there should be no difference
//! // between the real time and the clock's time
//! assert!(clock.now_std().elapsed().as_millis() == 0);
//!
//! // Pause the clock right after creation
//! clock.pause();
//!
//! // Clone the arc of the clock to pass to a new thread
//! let clock_clone = clock.clone();
//!
//! let t = thread::spawn(move || {
//!     // In the new thread, just wait for resume
//!     clock_clone.wait_for_resume();
//! });
//!
//! // Sleep for a sec, then resume the clock
//! let sleep_start = Instant::now();
//! thread::sleep(Duration::from_secs(1));
//! let slept = sleep_start.elapsed().as_secs_f64();
//!
//! clock.resume();
//!
//! // Wait for the spawned thread to unblock
//! t.join().unwrap();
//!
//! // After being paused for a second, the clock is now a second behind
//! assert!((clock.now_std().elapsed().as_secs_f64() - slept).abs() <= 0.001);
//! ```
//!
//! ## Caveats
//! - We use an `AtomicU64` to contain the entire state of the pausable clock,
//! so the granularity of the instant's produced by the clock is milliseconds.
//! This means the maximum time the timer can handle is on the order of hundreds
//! of thousands of years.
//! - Reads of the pause state for `PausableClock::is_paused` is done atomically
//! with `Ordering::Relaxed`. That allows the call to be slightly faster, but it
//! means you shouldn't think it as fencing a operations
#![warn(
    missing_docs,
    rust_2018_idioms,
    missing_debug_implementations,
    intra_doc_link_resolution_failure,
    clippy::all
)]

mod pausable_instant;
mod pause_state;

pub use pausable_instant::PausableInstant;
use pause_state::{PauseState, PauseStateTrait};
use std::sync::atomic::{compiler_fence, AtomicU64, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

/// Source of time information that can be paused and resumed. At its heart it
/// is a reference instant in real time, a record of elapsed time, and an atomic
/// state stored in a u64
#[derive(Debug, Clone)]
pub struct PausableClock(Arc<WrappedPausableClock>);

#[derive(Debug)]
struct Inner {
    zero_instant: Instant,
    pause_state: AtomicU64,
}

#[allow(clippy::mutex_atomic)]
#[derive(Debug)]
pub(crate) struct WrappedPausableClock {
    inner: Inner,
    pause_lock: Mutex<bool>,
    resume_condition: Condvar,
}

/// The default pausable clock is one that is (more or less) identical to real
/// time: Not paused and starting with zero starting offset
impl Default for PausableClock {
    fn default() -> Self {
        PausableClock::new(Default::default(), false)
    }
}

impl Inner {
    fn current_state(&self, ordering: Ordering) -> PauseState {
        self.pause_state.load(ordering)
    }

    /// Get a tuple of the current pausable instant and the associated real
    /// instant that was used to create it.
    fn now(&self) -> (PausableInstant, Instant) {
        let now = Instant::now();
        // Prevent compiler re-ordering here so time is not read after state
        compiler_fence(Ordering::SeqCst);
        let state = self.current_state(Ordering::Relaxed);

        if state.is_read_time_frozen() {
            (
                PausableInstant::new(self.zero_instant, state.get_millis()),
                now,
            )
        } else {
            (
                PausableInstant::new(
                    self.zero_instant,
                    (now - self.zero_instant).as_millis() as u64
                        - state.get_millis(),
                ),
                now,
            )
        }
    }

    fn set_state(&self, new_state: PauseState) {
        self.pause_state.store(new_state, Ordering::SeqCst)
    }

    fn is_paused(&self, ordering: Ordering) -> bool {
        self.current_state(ordering).is_paused()
    }

    fn millis_since_zero(&self, instant: Instant) -> u64 {
        (instant - self.zero_instant).as_millis() as u64
    }
}

impl WrappedPausableClock {
    pub(crate) fn increment_pause_guards(&self) {}

    pub(crate) fn decrement_pause_guards(&self) {}
}

#[allow(clippy::mutex_atomic)]
impl PausableClock {
    /// Create a new pausable clock with the given pause state and the given
    /// elapsed time
    pub fn new(elapsed_time: Duration, paused: bool) -> PausableClock {
        let now = Instant::now();
        let zero_instant = now - elapsed_time;

        let current_state =
            PauseState::new(true, false, elapsed_time.as_millis() as u64);

        let result = PausableClock(Arc::new(WrappedPausableClock {
            inner: Inner {
                zero_instant,
                pause_state: AtomicU64::new(current_state),
            },

            pause_lock: Mutex::new(true),
            resume_condition: Condvar::default(),
        }));

        if !paused {
            result.resume();
        }

        result
    }

    /// Get the current time according to this clock as a std instant
    pub fn now_std(&self) -> Instant {
        self.now().into()
    }

    /// Get the current time according to the clock
    pub fn now(&self) -> PausableInstant {
        self.0.inner.now().0
    }

    /// Pause the pausable clock. This function will set the pause state to
    /// pausing, then to paused. This ensures that no times will be read in
    /// the time between when now is read and when the pause state is set that
    /// is greater than the paused time.
    ///
    /// True will be returned for a successful pause (meaning the clock wasn't
    /// already paused), and false will be returned if the clock was paused when
    /// this method was called.
    pub fn pause(&self) -> bool {
        let mut paused_guard =
            self.0.pause_lock.lock().expect("Failed to get pause lock");

        let starting_state = self.0.inner.current_state(Ordering::SeqCst);

        if starting_state.is_paused() {
            return false;
        }

        if starting_state.is_pausing() {
            panic!("Inconsistent pause state: pausing");
        }

        let (pausing_instant, real_time_at_pausing) = self.0.inner.now();
        let pausing =
            PauseState::new(false, true, pausing_instant.elapsed_millis);
        self.0.inner.set_state(pausing);

        // Pretend to use the stored pausing instant as the input to resuming
        // fake_resume = now - zero - pausing
        let fake_resume_millis =
            self.0.inner.millis_since_zero(real_time_at_pausing)
                - pausing_instant.elapsed_millis;

        let paused_millis = self.0.inner.zero_instant.elapsed().as_millis()
            as u64
            - fake_resume_millis;

        let paused = PauseState::new(true, false, paused_millis);

        *paused_guard = true;
        self.0.inner.set_state(paused);

        true
    }

    /// Resume the clock and notify any threads waiting on for time to resume.
    ///
    /// This will return true if the clock started paused and was successfully
    /// resumed. It will return false if the clock was already resumed
    pub fn resume(&self) -> bool {
        let mut paused_guard =
            self.0.pause_lock.lock().expect("Failed to get pause lock");

        let starting_state = self.0.inner.current_state(Ordering::SeqCst);

        if !starting_state.is_paused() {
            return false;
        }

        if starting_state.is_pausing() {
            panic!("Inconsistent pause state: pausing");
        }

        // now - stored - zero = paused_millis
        // stored = now - paused_millis - zero
        let paused_millis = starting_state.get_millis();
        let stored_millis = self.0.inner.zero_instant.elapsed().as_millis()
            as u64
            - paused_millis;
        let resumed_state = PauseState::new(false, false, stored_millis);

        *paused_guard = false;

        self.0.inner.set_state(resumed_state);
        self.0.resume_condition.notify_all();

        true
    }

    /// Check to see if the clock is paused
    pub fn is_paused(&self) -> bool {
        self.0.inner.is_paused(Ordering::Relaxed)
    }

    /// Block the current thread until the clock resumes. If the clock is not
    /// paused when this method is called, the method will return without
    /// blocking
    pub fn wait_for_resume(&self) {
        if !self.is_paused() {
            return;
        }

        let guard = self.0.pause_lock.lock().expect("Unable to get pause lock");
        let _lock = self.0.resume_condition.wait_while(guard, |p| *p);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicBool, AtomicU64};
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn it_works() {
        let clock = Arc::new(PausableClock::default());

        assert!(clock.now_std().elapsed().as_millis() == 0);

        clock.pause();

        assert!(clock.is_paused());

        let clock_clone = clock.clone();

        let j = thread::spawn(move || {
            let bef_real = Instant::now();
            let bef = clock_clone.now();

            clock_clone.wait_for_resume();

            let aft = clock_clone.now();
            let aft_real = Instant::now();

            let elapsed_clock_millis = aft.elapsed_millis - bef.elapsed_millis;
            let elapsed_real_millis = (aft_real - bef_real).as_millis();

            assert!(elapsed_real_millis >= 1000);
            assert!(elapsed_clock_millis <= 1);
        });

        let now = Instant::now();
        thread::sleep(Duration::from_secs(1));
        let slept_millis = now.elapsed().as_secs_f64();

        clock.resume();

        assert!(!clock.is_paused());

        j.join().expect("Must be an assert fail in spawned thread");

        let elapsed = clock.now_std().elapsed();

        assert!((elapsed.as_secs_f64() - slept_millis).abs() <= 0.001);
    }

    #[test]
    fn test_multiple_pauses() {
        let pause_duration = Duration::from_millis(10);
        let resume_duration = Duration::from_millis(20);
        let pause_count = 100;

        let clock = PausableClock::default();

        let mut resuming_time = Duration::from_millis(0);

        for _ in 0..pause_count {
            assert!(clock.pause());

            thread::sleep(pause_duration);

            assert!(clock.resume());

            let now = Instant::now();
            thread::sleep(resume_duration);
            resuming_time += now.elapsed();
        }

        // Adjust the the actual pause time by subtracting how
        let actual_elapsed_millis = clock.now().elapsed_millis as f64;
        let expected_elapsed_millis = resuming_time.as_millis() as f64;

        assert!(
            (actual_elapsed_millis - expected_elapsed_millis).abs()
                / expected_elapsed_millis
                < 0.005
        );
    }

    #[test]
    fn test_time_max_when_paused() {
        let clock = Arc::new(PausableClock::default());

        let threads = 1000;
        let last_times: Arc<Vec<AtomicU64>> = Arc::new(
            std::iter::repeat_with(|| AtomicU64::default())
                .take(threads)
                .collect(),
        );

        clock.pause();
        let keep_going = Arc::new(AtomicBool::new(true));

        let mut join_handles = Vec::with_capacity(threads);

        for i in 0..threads {
            let clock_clone = clock.clone();
            let last_times_clone = last_times.clone();
            let keep_going_clone = keep_going.clone();

            join_handles.push(thread::spawn(move || {
                clock_clone.wait_for_resume();
                while keep_going_clone.load(Ordering::Relaxed) {
                    last_times_clone.get(i).unwrap().store(
                        clock_clone.now().elapsed_millis,
                        Ordering::Relaxed,
                    );
                }
            }));
        }

        thread::sleep(Duration::from_millis(10));

        // unblock all the reader threads
        clock.resume();

        while last_times
            .iter()
            .filter(|v| v.load(Ordering::Relaxed) == 0)
            .next()
            .is_some()
        {}

        // pause while the clock is under heavy use
        clock.pause();

        let expected_max_elapsed = clock.now().elapsed_millis;

        keep_going.store(false, Ordering::Relaxed);

        // Wait for all worker threads to stop
        join_handles.into_iter().for_each(|j| {
            let _ = j.join();
        });

        for reader_latest in last_times.iter() {
            let actual = reader_latest.load(Ordering::Relaxed);

            println!("Asserting {} > {}", expected_max_elapsed, actual);

            assert!(actual > 0);
            assert!(actual <= expected_max_elapsed);
        }
    }
}
