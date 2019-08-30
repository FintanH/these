
#[derive(Debug, Clone, PartialEq)]
pub enum These<T, U> {
    This(T),
    That(U),
    These(T, U)
}

impl<T, U> These<T, U> {
    pub fn these<V, F, G, H>(self, f: F, g: G, h: H) -> V
        where F: FnOnce(T) -> V,
              G: FnOnce(U) -> V,
              H: FnOnce(T, U) -> V,
    {
        match self {
            These::This(t) => f(t),
            These::That(u) => g(u),
            These::These(t, u) => h(t, u)
        }
    }

    pub fn map<V, F>(&self, op: F) -> These<T, V>
        where F: FnOnce(U) -> V + Copy
    {
        self.these(
            |t| These::This(t),
            |u| These::That(op(u)),
            |t, u| These::These(t, op(u)),
        )
    }

    pub fn from_these(self, t_default: T, u_default: U) -> (T, U)
    {
        self.these(
            |t| (t, u_default),
            |u| (t_default, u),
            |t, u| (t, u),
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::These;

    #[test]
    fn it_works() {
        let test_val: These<i8, i8> = These::That(2);
        assert_eq!(test_val.map(|x| x + 1), These::That(3));
    }
}
