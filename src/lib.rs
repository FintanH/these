
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
pub enum These<T, U> {
    This(T),
    That(U),
    These(T, U)
}

impl<T, U> These<T, U> {

    /// Collapse a `These` value given a set of three functions to
    /// some target type.
    ///
    /// The first function will apply to `This`, the second to `That`,
    /// and the third to `These`.
    ///
    /// This can be thought of as matching on the value and applying the
    /// functions, but removes the need to match.
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// // Functions to use for collapsing
    /// let f = |s: &str| s.len();
    /// let g = |i| i * 42;
    /// let h = |s: &str, i| s.len() + i;
    ///
    /// let this: These<&str, usize> = These::This("Hello");
    /// assert_eq!(this.collapse_these(f, g, h), 5);
    ///
    /// let that: These<&str, usize> = These::That(42);
    /// assert_eq!(that.collapse_these(f, g, h), 1764);
    ///
    /// let these: These<&str, usize> = These::These("Hello", 42);
    /// assert_eq!(these.collapse_these(f, g, h), 47);
    /// ```
    pub fn collapse_these<V, F, G, H>(self, f: F, g: G, h: H) -> V
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

    /// Apply the function to the `U` value if the data is
    /// a `That` or `These`.
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<i8, i8> = These::This(1);
    /// assert_eq!(this.map(|x| x + 1), These::This(1));
    ///
    /// let that: These<i8, i8> = These::That(1);
    /// assert_eq!(that.map(|x| x + 1), These::That(2));
    ///
    /// let these: These<&str, i8> = These::These("Hello", 1);
    /// assert_eq!(these.map(|x| x + 1), These::These("Hello", 2));
    /// ```
    pub fn map<V, F>(self, op: F) -> These<T, V>
        where F: FnOnce(U) -> V + Copy,
    {
        self.map_both(|x| x, op)
    }


    /// Apply the function to the `T` value if the data is
    /// a `This` or `These`.
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<i8, i8> = These::This(1);
    /// assert_eq!(this.map_first(|x| x + 1), These::This(2));
    ///
    /// let that: These<i8, i8> = These::That(1);
    /// assert_eq!(that.map_first(|x| x + 1), These::That(1));
    ///
    /// let these: These<&str, i8> = These::These("Hello", 1);
    /// assert_eq!(these.map_first(|s| s.len()), These::These(5, 1));
    /// ```
    pub fn map_first<V, F>(self, op: F) -> These<V, U>
        where F: FnOnce(T) -> V + Copy,
    {
        self.map_both(op, |x| x,)
    }

    /// Apply the function to the `U` value if the data is
    /// a `That` or `These`. This is the same as `map`.
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<i8, i8> = These::This(1);
    /// assert_eq!(this.map_second(|x| x + 1), These::This(1));
    ///
    /// let that: These<i8, i8> = These::That(1);
    /// assert_eq!(that.map_second(|x| x + 1), These::That(2));
    ///
    /// let these: These<&str, i8> = These::These("Hello", 1);
    /// assert_eq!(these.map_second(|i| i + 1), These::These("Hello", 2));
    /// ```
    pub fn map_second<V, F>(self, op: F) -> These<T, V>
        where F: FnOnce(U) -> V + Copy,
    {
        self.map(op)
    }

    /// Apply both functions to the `T` and `U` values respectively.
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let f = |s: &str| s.len();
    /// let g = |i| i * i;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.map_both(f, g), These::This(5));
    ///
    /// let that: These<&str, i8> = These::That(8);
    /// assert_eq!(that.map_both(f, g), These::That(64));
    ///
    /// let these: These<&str, i8> = These::These("Hello", 9);
    /// assert_eq!(these.map_both(f, g), These::These(5, 81));
    /// ```
    pub fn map_both<V, W, F, G>(self, f: F, g: G) -> These<V, W>
        where F: FnOnce(T) -> V + Copy,
              G: FnOnce(U) -> W + Copy,
    {
        self.collapse_these(
            |t| These::This(f(t)),
            |u| These::That(g(u)),
            |t, u| These::These(f(t), g(u)),
        )
    }

    /// Collapse the `These` value but using a default value
    /// in place of `U` (ignoring any `U` values).
    ///
    /// If `This` is found it will return the default value.
    /// If `That` is found it will use the function with the value
    /// contained in `That` along with the default.
    /// If `These` is found it will use the function with the second element
    /// along with the default, ignoring the first element.
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let f = |v, i| v * i;
    ///
    /// let this: These<&str, i16> = These::This("Hello");
    /// assert_eq!(this.fold_these(42, f), 42);
    ///
    /// let that: These<&str, i16> = These::That(8);
    /// assert_eq!(that.fold_these(42, f), 336);
    ///
    /// let these: These<&str, i16> = These::These("Hello", 9);
    /// assert_eq!(these.fold_these(42, f), 378);
    /// ```
    pub fn fold_these<V, F>(self, default: V, op: F) -> V
        where F: FnOnce(U, V) -> V + Copy,
              V: Copy
    {
        self.collapse_these(
            |_| default,
            |u| op(u, default),
            |_, u| op(u, default),
        )
    }

    /// Create a tuple given some `These` value. In the case of `This`
    /// or `That` it will use the default values provided.
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.from_these("World", 42), ("Hello", 42));
    ///
    /// let that: These<&str, i8> = These::That(42);
    /// assert_eq!(that.from_these("Hello", 100), ("Hello", 42));
    ///
    /// let these: These<&str, i8> = These::These("Hello", 42);
    /// assert_eq!(these.from_these("World", 42), ("Hello", 42));
    /// ```
    pub fn from_these(self, t_default: T, u_default: U) -> (T, U)
    {
        self.collapse_these(
            |t| (t, u_default),
            |u| (t_default, u),
            |t, u| (t, u),
        )
    }

    /// Swap the types of values of a `These` value.
    ///
    /// `This` turns into `That`.
    /// `That` turns into `This`.
    /// `These` values swap their order.
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.swap_these(), These::That("Hello"));
    ///
    /// let that: These<&str, i8> = These::That(42);
    /// assert_eq!(that.swap_these(), These::This(42));
    ///
    /// let these: These<&str, i8> = These::These("Hello", 42);
    /// assert_eq!(these.swap_these(), These::These(42, "Hello"));
    /// ```
    pub fn swap_these(self) -> These<U, T>
    {
        self.collapse_these(
            |t| These::That(t),
            |u| These::This(u),
            |t, u| These::These(u, t),
        )
    }

    /// Produce a `Some` from `This`, otherwise return `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.this_option(), Some("Hello"));
    ///
    /// let that: These<&str, i8> = These::That(42);
    /// assert_eq!(that.this_option(), None);
    ///
    /// let these: These<&str, i8> = These::These("Hello", 42);
    /// assert_eq!(these.this_option(), None);
    /// ```
    pub fn this_option(self) -> Option<T>
    {
        self.collapse_these(
            |t| Some(t),
            |_| None,
            |_, _| None,
        )
    }

    /// Produce a `Some` from `That`, otherwise return `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.that_option(), None);
    ///
    /// let that: These<&str, i8> = These::That(42);
    /// assert_eq!(that.that_option(), Some(42));
    ///
    /// let these: These<&str, i8> = These::These("Hello", 42);
    /// assert_eq!(these.that_option(), None);
    /// ```
    pub fn that_option(self) -> Option<U>
    {
        self.collapse_these(
            |_| None,
            |u| Some(u),
            |_, _| None,
        )
    }

    /// Produce a `Some` from `These`, otherwise return `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.these_option(), None);
    ///
    /// let that: These<&str, i8> = These::That(42);
    /// assert_eq!(that.these_option(), None);
    ///
    /// let these: These<&str, i8> = These::These("Hello", 42);
    /// assert_eq!(these.these_option(), Some(("Hello", 42)));
    /// ```
    pub fn these_option(self) -> Option<(T, U)>
    {
        self.collapse_these(
            |_| None,
            |_| None,
            |t, u| Some((t, u)),
        )
    }

    /// Produce a `Some` if a `This` or `These` is found,
    /// otherwise `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.here_option(), Some("Hello"));
    ///
    /// let that: These<&str, i8> = These::That(42);
    /// assert_eq!(that.here_option(), None);
    ///
    /// let these: These<&str, i8> = These::These("Hello", 42);
    /// assert_eq!(these.here_option(), Some("Hello"));
    /// ```
    pub fn here_option(self) -> Option<T>
    {
        self.collapse_these(
            |t| Some(t),
            |_| None,
            |t, _| Some(t),
        )
    }

    /// Produce a `Some` if a `That` or `These` is found,
    /// otherwise `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.there_option(), None);
    ///
    /// let that: These<&str, i8> = These::That(42);
    /// assert_eq!(that.there_option(), Some(42));
    ///
    /// let these: These<&str, i8> = These::These("Hello", 42);
    /// assert_eq!(these.there_option(), Some(42));
    /// ```
    pub fn there_option(self) -> Option<U>
    {
        self.collapse_these(
            |_| None,
            |u| Some(u),
            |_, u| Some(u),
        )
    }

    /// Is it `This`?
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.is_this(), true);
    ///
    /// let that: These<&str, i8> = These::That(42);
    /// assert_eq!(that.is_this(), false);
    ///
    /// let these: These<&str, i8> = These::These("Hello", 42);
    /// assert_eq!(these.is_this(), false);
    /// ```
    pub fn is_this(self) -> bool
    {
        self.this_option().is_some()
    }

    /// Is it `That`?
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.is_that(), false);
    ///
    /// let that: These<&str, i8> = These::That(42);
    /// assert_eq!(that.is_that(), true);
    ///
    /// let these: These<&str, i8> = These::These("Hello", 42);
    /// assert_eq!(these.is_that(), false);
    /// ```
    pub fn is_that(self) -> bool
    {
        self.that_option().is_some()
    }

    /// Is it `These`?
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.is_these(), false);
    ///
    /// let that: These<&str, i8> = These::That(42);
    /// assert_eq!(that.is_these(), false);
    ///
    /// let these: These<&str, i8> = These::These("Hello", 42);
    /// assert_eq!(these.is_these(), true);
    /// ```
    pub fn is_these(self) -> bool
    {
        self.these_option().is_some()
    }

    /// Is it `Here`, i.e. `This` or `These`?
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.is_here(), true);
    ///
    /// let that: These<&str, i8> = These::That(42);
    /// assert_eq!(that.is_here(), false);
    ///
    /// let these: These<&str, i8> = These::These("Hello", 42);
    /// assert_eq!(these.is_here(), true);
    /// ```
    pub fn is_here(self) -> bool
    {
        self.here_option().is_some()
    }

    /// Is it `There`, i.e. `That` or `These`?
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.is_there(), false);
    ///
    /// let that: These<&str, i8> = These::That(42);
    /// assert_eq!(that.is_there(), true);
    ///
    /// let these: These<&str, i8> = These::These("Hello", 42);
    /// assert_eq!(these.is_there(), true);
    /// ```
    pub fn is_there(self) -> bool
    {
        self.there_option().is_some()
    }

    /// When given a `Vec` of `These` it will split it into three separate `Vec`s, each
    /// containing the `This`, `That`, or `These` inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let xs = vec![These::This(1), These::That("Hello"), These::These(42, "World")];
    /// assert_eq!(These::partition_these(xs), (vec![1], vec!["Hello"], vec![(42, "World")]));
    /// ```
    pub fn partition_these(xs: Vec<These<T, U>>) -> (Vec<T>, Vec<U>, Vec<(T, U)>)
    {
        let mut this: Vec<T> = Vec::new();
        let mut that: Vec<U> = Vec::new();
        let mut these: Vec<(T, U)> = Vec::new();

        for x in xs
        {
            x.collapse_these(
                |t| this.push(t),
                |u| that.push(u),
                |t, u| these.push((t, u)),
            )
        }

        (this, that, these)
    }

    /// When given a `Vec` of `These` it will split it into two separate `Vec`s, each
    /// containing the `T` or `U` inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let xs = vec![These::This(1), These::That("Hello"), These::These(42, "World")];
    /// assert_eq!(These::partition_here_there(xs), (vec![1, 42], vec!["Hello", "World"]));
    /// ```
    pub fn partition_here_there(xs: Vec<These<T, U>>) -> (Vec<T>, Vec<U>)
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
