use std::sync::{ Weak, Arc };

pub struct PauseGuard {
    owner: Weak<WrappedPausableClock>
}

impl PauseGuard {
    pub(crate) fn new(owner: Arc<WrappedPausableClock>) {
        let result = PauseGuard {
            owner: Arc::downgrade(&owner);
        }

        owner.increment_pause_guards();

        result
    }
}

impl Drop for PauseGuard {
    fn drop(&mut self) {
        if let Some(owner) = self.owner.upgrade() {
            owner.decrement_pause_guards();
        }
    }
}