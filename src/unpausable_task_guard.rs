use super::PausabilityStateTrait;
use super::PausableClock;

pub(super) struct UnpausableTaskGuard<'a>(&'a PausableClock);

impl<'a> UnpausableTaskGuard<'a> {
    pub(crate) fn try_lock(
        owner: &'a PausableClock,
    ) -> Result<UnpausableTaskGuard<'a>, ()> {
        let result = UnpausableTaskGuard(owner);

        let new_guard_state = owner.increment_unpausable_task_guards();

        if new_guard_state.is_pausing_requested() {
            Err(())
        } else {
            Ok(result)
        }
    }
}

impl<'a> Drop for UnpausableTaskGuard<'a> {
    fn drop(&mut self) {
        let _ = self.0.decrement_unpausable_task_guards();
    }
}
