
pub enum These<T, U> {
    This(T),
    That(U),
    These(T, U)
}

impl<T, U> These<T, U> {
    pub fn map<V, F: FnOnce(U) -> V>(self, op: F) -> These<T, V>
    {
        match self {
            This(t) => This(t),
            That(u) => That(op(u)),
            These(t, u) => These(t, op(u)),
    }
}
