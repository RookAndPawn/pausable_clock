use pausable_instant::PausableInstant;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Condvar, Mutex};
use std::time::{Duration, Instant};

mod pausable_instant;

const PAUSED_MASK: u64 = 1 << 63;
const PAUSING_MASK: u64 = 1 << 62;
const FLAG_MASK: u64 = PAUSED_MASK + PAUSING_MASK;
const ELAPSED_MILLIS_MASK: u64 = !FLAG_MASK;

type PauseState = u64;

trait PauseStateTrait {
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

struct Inner {
    zero_instant: Instant,
    pause_state: AtomicU64,
}

pub struct PausableClock {
    inner: Inner,
    lock: Mutex<()>,

    resume_mutex: Mutex<()>,
    resume_condition: Condvar,
}

impl Default for PausableClock {
    fn default() -> Self {
        PausableClock::new(Default::default(), false)
    }
}

impl Inner {
    fn current_state(&self, ordering: Ordering) -> PauseState {
        self.pause_state.load(ordering)
    }

    fn now(&self) -> (PausableInstant, Option<Instant>) {
        let state = self.current_state(Ordering::Relaxed);

        if state.is_read_time_frozen() {
            (
                PausableInstant::new(self.zero_instant, state.get_millis()),
                None,
            )
        } else {
            let now = Instant::now();

            (
                PausableInstant::new(
                    self.zero_instant,
                    (now - self.zero_instant).as_millis() as u64
                        - state.get_millis(),
                ),
                Some(now),
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

impl PausableClock {
    pub fn new(elapsed_time: Duration, paused: bool) -> PausableClock {
        let now = Instant::now();
        let zero_instant = now - elapsed_time;

        let current_state =
            PauseState::new(true, false, elapsed_time.as_millis() as u64);

        let result = PausableClock {
            inner: Inner {
                zero_instant,
                pause_state: AtomicU64::new(current_state),
            },

            lock: Mutex::new(()),

            resume_mutex: Mutex::new(()),
            resume_condition: Condvar::default(),
        };

        if !paused {
            result.resume();
        }

        result
    }

    pub fn now(&self) -> PausableInstant {
        self.inner.now().0
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
        let _lock = self.lock.lock();

        let starting_state = self.inner.current_state(Ordering::SeqCst);

        if starting_state.is_paused() {
            return false;
        }

        if starting_state.is_pausing() {
            panic!("Inconsistent pause state: pausing");
        }

        let (pausing_instant, real_time_at_pausing_opt) = self.inner.now();
        let pausing =
            PauseState::new(false, true, pausing_instant.elapsed_millis);
        self.inner.set_state(pausing);

        let real_time_at_pausing = real_time_at_pausing_opt
            .expect("Always present for resumed clocks");

        // Pretend to use the stored pausing instant as the input to resuming
        // fake_resume = now - zero - pausing
        let fake_resume_millis =
            self.inner.millis_since_zero(real_time_at_pausing)
                - pausing_instant.elapsed_millis;

        let paused_millis = self.inner.zero_instant.elapsed().as_millis()
            as u64
            - fake_resume_millis;

        let paused = PauseState::new(true, false, paused_millis);

        self.inner.set_state(paused);

        true
    }

    pub fn resume(&self) -> bool {
        let _lock = self.lock.lock();

        let starting_state = self.inner.current_state(Ordering::SeqCst);

        if !starting_state.is_paused() {
            return false;
        }

        if starting_state.is_pausing() {
            panic!("Inconsistent pause state: pausing");
        }

        // now - stored - zero = paused_millis
        // stored = now - paused_millis - zero
        let paused_millis = starting_state.get_millis();
        let stored_millis = self.inner.zero_instant.elapsed().as_millis()
            as u64
            - paused_millis;
        let resumed_state = PauseState::new(false, false, stored_millis);

        self.inner.set_state(resumed_state);
        self.resume_condition.notify_all();

        true
    }

    pub fn is_paused(&self) -> bool {
        self.inner.is_paused(Ordering::Relaxed)
    }

    pub fn wait_for_resume(&self) {
        if !self.is_paused() {
            return;
        }

        while self.inner.is_paused(Ordering::SeqCst) {
            let guard = self
                .resume_mutex
                .lock()
                .expect("Unable to lock resume mutex");
            let _lock = self.resume_condition.wait(guard);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn it_works() {
        let clock = Arc::new(PausableClock::default());

        assert!((Instant::now() - clock.now().as_std()).as_millis() == 0);

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

        thread::sleep(Duration::from_secs(1));

        clock.resume();

        assert!(!clock.is_paused());

        j.join().expect("Must be an assert fail in spawned thread");

        assert!((Instant::now() - clock.now().as_std()).as_millis() > 998);
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
        let expected_elapsed_millis =resuming_time.as_millis() as f64;

        assert!(
            (actual_elapsed_millis - expected_elapsed_millis).abs()
                / expected_elapsed_millis
                < 0.005
        );
    }
}
