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

mod pausability_state;
mod pausable_instant;
mod pause_state;
mod unpausable_task_guard;

use pausability_state::{
    PausabilityState, PausabilityStateTrait, PAUSING_REQUESTED_MASK,
};
pub use pausable_instant::PausableInstant;
use pause_state::{PauseState, PauseStateTrait};

#[cfg(loom)]
use loom::sync::atomic::{compiler_fence, AtomicU32, AtomicU64, Ordering};

#[cfg(loom)]
use loom::sync::{Condvar, Mutex, MutexGuard};

#[cfg(not(loom))]
use std::sync::atomic::{compiler_fence, AtomicU32, AtomicU64, Ordering};

#[cfg(not(loom))]
use std::sync::{Condvar, Mutex, MutexGuard};

use std::time::{Duration, Instant};
use unpausable_task_guard::UnpausableTaskGuard;

/// Enumeration of the possible pause states of the system.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum CoursePauseState {
    Paused,
    Pausing,
    Resumed,
}

/// Enumeration of the possible states of pausability. Normally this is
/// Unused. During a pause call it gets set to Pausing, and if there are
/// un-pausable tasks running when the pause call happens, they will set the
/// state to released.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum CoursePausabilityState {
    Unused,
    Pausing,
    Released,
}

/// Source of time information that can be paused and resumed. At its heart it
/// is a reference instant in real time, a record of elapsed time, and an atomic
/// state stored in a u64
#[derive(Debug)]
pub struct PausableClock {
    zero_instant: Instant,

    pause_state: AtomicU64,
    pause_state_lock: Mutex<CoursePauseState>,
    pause_state_condition: Condvar,

    pausability_state: AtomicU32,
    pausability_lock: Mutex<CoursePausabilityState>,
    pausability_condition: Condvar,
}

/// The default pausable clock is one that is (more or less) identical to real
/// time: Not paused and starting with zero starting offset
impl Default for PausableClock {
    fn default() -> Self {
        PausableClock::new(Default::default(), false)
    }
}

impl PausableClock {
    /// Create a new pausable clock with the given pause state and the given
    /// elapsed time
    pub fn new(elapsed_time: Duration, paused: bool) -> PausableClock {
        let now = Instant::now();
        let zero_instant = now - elapsed_time;

        let current_state =
            PauseState::new(true, false, true, elapsed_time.as_millis() as u64);

        let result = PausableClock {
            zero_instant,
            pause_state: AtomicU64::new(current_state),

            pause_state_lock: Mutex::new(CoursePauseState::Paused),
            pause_state_condition: Condvar::default(),

            pausability_state: Default::default(),
            pausability_lock: Mutex::new(CoursePausabilityState::Unused),
            pausability_condition: Default::default(),
        };

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
        self.now_impl().0
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
        let mut paused_guard = self
            .pause_state_lock
            .lock()
            .expect("Failed to get pause lock");

        match *paused_guard {
            CoursePauseState::Paused => return false,
            CoursePauseState::Pausing => {
                panic!("Inconsistent pause state");
            }
            _ => {}
        }

        *paused_guard = CoursePauseState::Pausing;

        {
            let mut pausability_guard = self
                .pausability_lock
                .lock()
                .expect("Failed to get pause guard lock");
            if *pausability_guard != CoursePausabilityState::Unused {
                panic!("Inconsistent pausable state");
            }
            *pausability_guard = CoursePausabilityState::Pausing;
        }

        let starting_state = self.current_state(Ordering::SeqCst);
        let pausing = starting_state.with_pausing_flag();

        self.set_state(pausing);
        let pausability_state = self.set_pausing_flag_on_guard_state();

        if pausability_state.get_unpausable_task_count() > 0 {
            self.wait_for_unpausable_tasks_to_clear();
        }

        let (freeze_instant, real_time_at_freeze) = self.now_impl();

        // Freeze time at the given instant, but to prevent times ahead of pause
        // we don't consider the clock to be paused yet
        self.set_state(PauseState::new(
            false,
            true,
            true,
            freeze_instant.elapsed_millis,
        ));

        // Pretend to use the stored pausing instant as the input to resuming
        // fake_resume = now - zero - pausing
        let fake_resume_millis = self.millis_since_zero(real_time_at_freeze)
            - freeze_instant.elapsed_millis;

        let frozen_millis =
            self.zero_instant.elapsed().as_millis() as u64 - fake_resume_millis;

        let paused = PauseState::new(true, false, true, frozen_millis);

        *paused_guard = CoursePauseState::Paused;
        self.set_state(paused);
        self.unset_pausing_flag_on_guard_state();

        {
            let mut unpausable_task_guard_lock = self
                .pausability_lock
                .lock()
                .expect("Failed to get pause guard lock");

            *unpausable_task_guard_lock = CoursePausabilityState::Unused;
        }

        true
    }

    /// Wait on the pausable guard condition to make sure all valid pause guards
    /// have exited before allowing the pause action to proceed
    fn wait_for_unpausable_tasks_to_clear(&self) {
        let unpausable_task_guard_lock = self
            .pausability_lock
            .lock()
            .expect("Failed to get pause guard lock");

        let _lock = self
            .pausability_condition
            .wait_while(unpausable_task_guard_lock, |s| {
                *s != CoursePausabilityState::Released
            })
            .expect("Expected valid return from pausability lock");
    }

    /// Resume the clock and notify any threads waiting on for time to resume.
    ///
    /// This will return true if the clock started paused and was successfully
    /// resumed. It will return false if the clock was already resumed
    pub fn resume(&self) -> bool {
        let mut paused_guard = self
            .pause_state_lock
            .lock()
            .expect("Failed to get pause lock");

        let starting_state = self.current_state(Ordering::SeqCst);

        if !starting_state.is_paused() {
            return false;
        }

        if starting_state.is_pausing() {
            panic!("Inconsistent pause state: pausing");
        }

        // now - stored - zero = paused_millis
        // stored = now - paused_millis - zero
        let paused_millis = starting_state.get_millis();
        let stored_millis =
            self.zero_instant.elapsed().as_millis() as u64 - paused_millis;
        let resumed_state = PauseState::new(false, false, false, stored_millis);

        *paused_guard = CoursePauseState::Resumed;

        self.set_state(resumed_state);
        self.pause_state_condition.notify_all();

        true
    }

    /// Check to see if the clock is paused using relaxed atomic ordering
    pub fn is_paused(&self) -> bool {
        self.is_paused_ordered(Ordering::Relaxed)
    }

    /// Check to see if the clock is pausing using relaxed atomic ordering. Note
    /// that a clock that is paused will not be pausing
    pub fn is_pausing(&self) -> bool {
        self.is_pausing_ordered(Ordering::Relaxed)
    }

    /// Check to see if the clock is paused or pausing using relaxed atomic
    /// ordering
    pub fn is_paused_or_pausing(&self) -> bool {
        self.is_paused_or_pausing_ordered(Ordering::Relaxed)
    }

    /// Block the current thread until the clock resumes. If the clock is not
    /// paused when this method is called, the method will return without
    /// blocking
    #[allow(clippy::let_underscore_lock)]
    pub fn wait_for_resume(&self) {
        let _ = self.wait_for_resume_impl();
    }

    /// Wait for the clock to resume, or if the clock is already resumed, do
    /// nothing. The return for this function is none if no waiting was done,
    /// and a mutex guard on the pause state if waiting was done.
    fn wait_for_resume_impl(&self) -> Option<MutexGuard<'_, CoursePauseState>> {
        if !self.is_paused_or_pausing_ordered(Ordering::Acquire) {
            return None;
        }

        let guard = self
            .pause_state_lock
            .lock()
            .expect("Failed to get pause-state lock");

        let guard = self
            .pause_state_condition
            .wait_while(guard, |p| *p != CoursePauseState::Resumed)
            .expect("Failed to reacquire lock on pause state after resume");

        Some(guard)
    }

    /// This method provides a way to run in coordination with the pause
    /// functionality of the clock. A task run with this method will prevent
    /// the clock from being paused, and will not be run while the clock is
    /// paused
    pub fn run_unpausable<F, T>(&self, action: F) -> T
    where
        F: FnOnce() -> T,
    {
        // This does a _Acquire_ read and _Relaxed_ write
        let guard_opt = match UnpausableTaskGuard::try_lock(self) {
            Ok(guard) => {
                // Another _Acquire_ read here that definitely happens after the
                // read of the pause guard state
                let pause_state = self.current_state(Ordering::Acquire);
                if pause_state.is_paused() {
                    // Paused means we couldn't get a guard, but no need to
                    // release the pausable lock
                    None
                } else if pause_state.is_pausing() {
                    // Pausing means we interrupted the pausing process. We
                    // can't keep the guard we have, and we need to ensure the
                    // pausing process is notified when this guard is dropped.
                    // we do that by setting the pausing flag on the guard state
                    // ourselves
                    self.set_pausing_flag_on_guard_state();
                    None
                } else {
                    Some(guard)
                }
            }
            _ => None,
        };

        if let Some(_guard) = guard_opt {
            action()
        } else {
            let mut guard_opt = self.wait_for_resume_impl();

            // If wait for pause was able to return a lock on the pause state,
            // we can use that to create an infallible pause guard
            if guard_opt.is_some() {
                let _unpausable_task_guard = {
                    let _active_guard = guard_opt.take();
                    UnpausableTaskGuard::try_lock(self)
                };
                action()
            } else {
                // otherwise we have to start over
                self.run_unpausable(action)
            }
        }
    }

    fn current_state(&self, ordering: Ordering) -> PauseState {
        self.pause_state.load(ordering)
    }

    /// Get a tuple of the current pausable instant and the associated real
    /// instant that was used to create it.
    fn now_impl(&self) -> (PausableInstant, Instant) {
        let now = Instant::now();
        // Prevent compiler re-ordering here so time is not read after state
        compiler_fence(Ordering::SeqCst);
        let state = self.current_state(Ordering::Relaxed);

        if state.is_time_paused() {
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

    fn set_pausing_flag_on_guard_state(&self) -> PausabilityState {
        self.pausability_state
            .fetch_or(PAUSING_REQUESTED_MASK, Ordering::AcqRel)
            | PAUSING_REQUESTED_MASK
    }

    fn unset_pausing_flag_on_guard_state(&self) -> PausabilityState {
        self.pausability_state
            .fetch_and(!PAUSING_REQUESTED_MASK, Ordering::AcqRel)
            & (!PAUSING_REQUESTED_MASK)
    }

    fn set_state(&self, new_state: PauseState) {
        self.pause_state.store(new_state, Ordering::SeqCst)
    }

    /// Check to see if the clock is paused using the given atomic ordering
    pub fn is_paused_ordered(&self, ordering: Ordering) -> bool {
        self.current_state(ordering).is_paused()
    }

    /// Check to see if the clock is pausing using the given atomic ordering.
    /// Note that a clock that is paused will not be pausing
    pub fn is_pausing_ordered(&self, ordering: Ordering) -> bool {
        self.current_state(ordering).is_pausing()
    }

    /// Check to see if the clock is paused or pausing using the given atomic
    /// ordering
    pub fn is_paused_or_pausing_ordered(&self, ordering: Ordering) -> bool {
        self.current_state(ordering).is_paused_or_pausing()
    }

    fn millis_since_zero(&self, instant: Instant) -> u64 {
        (instant - self.zero_instant).as_millis() as u64
    }

    pub(crate) fn increment_unpausable_task_guards(&self) -> PausabilityState {
        self.pausability_state.fetch_add(1, Ordering::Acquire) + 1
    }

    pub(crate) fn decrement_unpausable_task_guards(&self) -> PausabilityState {
        let result = self.pausability_state.fetch_sub(1, Ordering::Acquire) - 1;

        if result.get_unpausable_task_count() == 0
            && result.is_pausing_requested()
        {
            {
                let mut pausability_guard = self
                    .pausability_lock
                    .lock()
                    .expect("Failed to get pause guard lock");
                if *pausability_guard == CoursePausabilityState::Pausing {
                    *pausability_guard = CoursePausabilityState::Released;
                }
            }
            self.pausability_condition.notify_all();
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(not(loom))]
    use std::sync::{
        atomic::{AtomicBool, AtomicU64},
        Arc, Condvar, Mutex,
    };

    #[cfg(not(loom))]
    use std::thread;

    #[cfg(loom)]
    use loom::sync::{
        atomic::{AtomicBool, AtomicU64},
        Arc, Condvar, Mutex,
    };

    #[cfg(loom)]
    use loom::thread;

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

    #[test]
    fn test_unpausable_wont_run_while_paused() {
        let clock = Arc::new(PausableClock::default());

        clock.pause();

        let clock_clone = clock.clone();

        let counter = Arc::new(AtomicU64::default());
        let counter_clone = counter.clone();

        thread::spawn(move || {
            clock_clone.run_unpausable(|| {
                counter_clone.store(1, Ordering::SeqCst);
            });
        });

        thread::sleep(Duration::from_millis(50));

        assert_eq!(0, counter.load(Ordering::SeqCst));

        clock.resume();

        thread::sleep(Duration::from_millis(50));

        assert_eq!(1, counter.load(Ordering::SeqCst));
    }

    #[test]
    fn test_pause_blocks_until_unpausable_exits() {
        let clock = Arc::new(PausableClock::default());

        clock.pause();

        let lock = Arc::new(Mutex::new(true));
        let cond = Arc::new(Condvar::default());
        let clock_clone = clock.clone();
        let lock_clone = lock.clone();
        let cond_clone = cond.clone();

        thread::spawn(move || {
            clock_clone.run_unpausable(|| {
                {
                    let mut lock = lock_clone.lock().unwrap();
                    *lock = false;
                }

                cond_clone.notify_all();
                thread::sleep(Duration::from_millis(1000));
            });
        });

        clock.resume();

        let before = Instant::now();

        {
            let lock = lock.lock().unwrap();
            let _lock = cond.wait_while(lock, |v| *v);
        }

        clock.pause();
        let time_to_pause = before.elapsed();

        assert!((time_to_pause.as_secs_f64() - 1.).abs() < 0.005);
    }
}
