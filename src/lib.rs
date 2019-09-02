
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

pub fn partition_these<T, U>(xs: Vec<These<T, U>>) -> (Vec<T>, Vec<U>, Vec<(T, U)>)
{
    let mut this: Vec<T> = Vec::new();
    let mut that: Vec<U> = Vec::new();
    let mut these: Vec<(T, U)> = Vec::new();

    for x in xs
    {
        x.these(
            |t| this.push(t),
            |u| that.push(u),
            |t, u| these.push((t, u)),
        )
    }

    (this, that, these)
}

pub fn partition_here_there<T, U>(xs: Vec<These<T, U>>) -> (Vec<T>, Vec<U>)
{
    let mut this: Vec<T> = Vec::new();
    let mut that: Vec<U> = Vec::new();

    for x in xs
    {
        match x {
            These::This(t) => this.push(t),
            These::That(u) => that.push(u),
            These::These(t,u) => {
                this.push(t);
                that.push(u)
            },
        }
    }

    (this, that)
}

#[cfg(test)]
mod tests {
    use crate::These;

    #[cfg(test)]
    mod map {
        use super::*;

        #[test]
        fn this() {
            let test_val: These<i8, i8> = These::This(2);
            assert_eq!(test_val.map(|x| x + 1), These::This(2));
        }

        #[test]
        fn that() {
            let test_val: These<i8, i8> = These::That(2);
            assert_eq!(test_val.map(|x| x + 1), These::That(3));
        }

        #[test]
        fn these() {
            let test_val: These<i8, i8> = These::These(2, 2);
            assert_eq!(test_val.map(|x| x + 1), These::These(2, 3));
        }
    }

    #[cfg(test)]
    mod is_this {
        use super::*;

        #[test]
        fn this() {
            let test_val: These<i8, i8> = These::This(2);
            assert!(test_val.is_this())
        }

        #[test]
        fn not_that() {
            let test_val: These<i8, i8> = These::That(2);
            assert!(!test_val.is_this())
        }

        #[test]
        fn not_these() {
            let test_val: These<i8, i8> = These::These(2, 2);
            assert!(!test_val.is_this())
        }
    }

    #[cfg(test)]
    mod is_that
    {
        use super::*;

        #[test]
        fn not_this() {
            let test_val: These<i8, i8> = These::This(2);
            assert!(!test_val.is_that())
        }

        #[test]
        fn that() {
            let test_val: These<i8, i8> = These::That(2);
            assert!(test_val.is_that())
        }

        #[test]
        fn not_these() {
            let test_val: These<i8, i8> = These::These(2, 2);
            assert!(!test_val.is_that())
        }
    }

    #[cfg(test)]
    mod is_these
    {
        use super::*;

        #[test]
        fn not_this() {
            let test_val: These<i8, i8> = These::This(2);
            assert!(!test_val.is_these())
        }

        #[test]
        fn not_that() {
            let test_val: These<i8, i8> = These::That(2);
            assert!(!test_val.is_these())
        }

        #[test]
        fn these() {
            let test_val: These<i8, i8> = These::These(2, 2);
            assert!(test_val.is_these())
        }
    }
}
