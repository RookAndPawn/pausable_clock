use super::PausableClock;
use super::ResumabilityStateTrait;

pub(super) struct UnresumableTaskGuard<'a>(&'a PausableClock);

impl<'a> UnresumableTaskGuard<'a> {
    pub(crate) fn try_lock(
        owner: &'a PausableClock,
    ) -> Result<UnresumableTaskGuard<'a>, ()> {
        let result = UnresumableTaskGuard(owner);

        let new_guard_state = owner.increment_unresumable_task_guards();

        if new_guard_state.is_resuming_requested() {
            Err(())
        } else {
            Ok(result)
        }
    }
}

impl<'a> Drop for UnresumableTaskGuard<'a> {
    fn drop(&mut self) {
        let _ = self.0.decrement_unresumable_task_guards();
    }
}
