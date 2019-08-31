
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

    pub fn map<V, F>(self, op: F) -> These<T, V>
        where F: FnOnce(U) -> V + Copy,
    {
        self.map_both(|x| x, op)
    }

    pub fn map_first<V, F>(self, op: F) -> These<V, U>
        where F: FnOnce(T) -> V + Copy,
    {
        self.map_both(op, |x| x,)
    }

    pub fn map_second<V, F>(self, op: F) -> These<T, V>
        where F: FnOnce(U) -> V + Copy,
    {
        self.map(op)
    }

    pub fn map_both<V, W, F, G>(self, f: F, g: G) -> These<V, W>
        where F: FnOnce(T) -> V + Copy,
              G: FnOnce(U) -> W + Copy,
    {
        self.these(
            |t| These::This(f(t)),
            |u| These::That(g(u)),
            |t, u| These::These(f(t), g(u)),
        )
    }

    pub fn fold_these<V, F>(self, default: V, op: F) -> V
        where F: FnOnce(U, V) -> V + Copy,
              V: Copy
    {
        self.these(
            |_| default,
            |u| op(u, default),
            |_, u| op(u, default),
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

    pub fn swap_these(self) -> These<U, T>
    {
        self.these(
            |t| These::That(t),
            |u| These::This(u),
            |t, u| These::These(u, t),
        )
    }

    pub fn this_option(self) -> Option<T>
    {
        self.these(
            |t| Some(t),
            |_| None,
            |_, _| None,
        )
    }

    pub fn that_option(self) -> Option<U>
    {
        self.these(
            |_| None,
            |u| Some(u),
            |_, _| None,
        )
    }

    pub fn these_option(self) -> Option<(T, U)>
    {
        self.these(
            |_| None,
            |_| None,
            |t, u| Some((t, u)),
        )
    }

    pub fn here_option(self) -> Option<T>
    {
        self.these(
            |t| Some(t),
            |_| None,
            |t, _| Some(t),
        )
    }

    pub fn there_option(self) -> Option<U>
    {
        self.these(
            |_| None,
            |u| Some(u),
            |_, u| Some(u),
        )
    }

    pub fn is_this(self) -> bool
    {
        self.this_option().is_some()
    }

    pub fn is_that(self) -> bool
    {
        self.that_option().is_some()
    }

    pub fn is_these(self) -> bool
    {
        self.these_option().is_some()
    }

    pub fn is_here(self) -> bool
    {
        self.here_option().is_some()
    }

    pub fn is_there(self) -> bool
    {
        self.there_option().is_some()
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
