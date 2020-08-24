use super::PausableClock;
use super::PauseGuardStateTrait;

pub(super) struct PauseGuard<'a>(&'a PausableClock);

impl<'a> PauseGuard<'a> {
    pub(crate) fn try_lock(
        owner: &'a PausableClock,
    ) -> Result<PauseGuard<'a>, ()> {
        let result = PauseGuard(owner);

        let new_guard_state = owner.increment_pause_guards();

        if new_guard_state.is_pausing_requested() {
            Err(())
        } else {
            Ok(result)
        }
    }
}

impl<'a> Drop for PauseGuard<'a> {
    fn drop(&mut self) {
        let _ = self.0.decrement_pause_guards();
    }
}
