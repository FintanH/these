
//! # These
//!
//! [`These`] represents a 3-way split of data. Think of it as a [`Result`]
//! except that we have an extra case that can contain both the result `T` and
//! the error `E`. This can be useful for when we can still compute the final result
//! but we have also encountered an error.
//!
//! ```
//! enum These<T, U> {
//!     This(T),
//!     That(U),
//!     These(T, U)
//! }
//! ```
//!
//! We have three constructors [`This`] which holds a `T`, [`That`] which holds a `U`,
//! and [`These`] which holds both.
//!
//! # Here and There
//!
//! If we want to talk about all `T`s we use the terminology `Here`. So this
//! means we either have a [`This`] or [`These`]. Or in code:
//!
//! ```
//! use these::These;
//!
//! fn is_here<T: Copy, U: Copy>(these: &These<T, U>) -> bool {
//!     these.is_this() || these.is_these()
//! }
//! ```
//!
//! If we want to talk about all `U`s we use the terminology `There`. So this
//! means we either have a [`That`] or [`These`]. Or in code
//!
//! ```
//! use these::These;
//!
//! fn is_here<T: Copy, U: Copy>(these: These<T, U>) -> bool {
//!     these.is_that() || these.is_these()
//! }
//! ```
//!
//! # Contrived Example
//!
//! Let us say that we have a function that only allows numbers that are less than
//! 10. We expose a new type `LessThanTen` and expect our users to use `is_less_than_ten`
//! to validate `i8`s into this type. We can use `Result` and model this below:
//!
//! ```
//! #[derive(Debug, PartialEq)]
//! struct LessThanTen(i8);
//!
//! #[derive(Debug, PartialEq)]
//! pub enum Error {
//!     IsGreaterThanOrEqualToTen,
//! }
//!
//! pub fn is_less_than_ten(i: i8) -> Result<LessThanTen, Error> {
//!     if i < 10 {
//!         Ok(LessThanTen(i))
//!     } else {
//!         Err(Error::IsGreaterThanOrEqualToTen)
//!     }
//! }
//!
//! assert_eq!(is_less_than_ten(8), Ok(LessThanTen(8)));
//! assert_eq!(is_less_than_ten(10), Err(Error::IsGreaterThanOrEqualToTen));
//! ```
//!
//! But after a while we realise we can start to support all numbers that are less than 20.
//! We can do a similar approach, but we would like to be backwards compatible, and also keep
//! track of when we encounter numbers that are greater than 10. Maybe we would like to keep
//! statistics on these errors, or convert successful results to `LessThanTen` for backwards
//! compatibility. We can use [`These`] to solve this and can modelled as below:
//!
//! ```
//! use these::These;
//!
//! #[derive(Debug, PartialEq)]
//! struct LessThanTen(i8);
//!
//! #[derive(Debug, PartialEq)]
//! struct LessThanTwenty(i8);
//!
//! #[derive(Debug, PartialEq)]
//! pub enum Error {
//!     IsGreaterThanOrEqualToTen,
//!     IsGreaterThanOrEqualToTwenty,
//! }
//!
//! pub fn is_less_than_ten(i: i8) -> Result<LessThanTen, Error> {
//!     if i < 10 {
//!         Ok(LessThanTen(i))
//!     } else {
//!         Err(Error::IsGreaterThanOrEqualToTen)
//!     }
//! }
//!
//! pub fn is_less_than_twenty(i: i8) -> These<Error, LessThanTwenty> {
//!     if i < 10 {
//!         These::That(LessThanTwenty(i))
//!     } else if i < 20 {
//!         These::These(Error::IsGreaterThanOrEqualToTen, LessThanTwenty(i))
//!     } else {
//!         These::This(Error::IsGreaterThanOrEqualToTwenty)
//!     }
//! }
//!
//! // Convert to the backwards compatible scenario
//! pub fn backwards_compatible(r: These<Error, LessThanTwenty>) -> Result<LessThanTen, Error> {
//!     r.collapse_these(
//!         |e| Err(e),
//!         |LessThanTwenty(i)| Ok(LessThanTen(i)),
//!         |e, _| Err(e),
//!     )
//! }
//!
//! assert_eq!(is_less_than_ten(8), Ok(LessThanTen(8)));
//! assert_eq!(is_less_than_ten(10), Err(Error::IsGreaterThanOrEqualToTen));
//! assert_eq!(is_less_than_twenty(8), These::That(LessThanTwenty(8)));
//! assert_eq!(is_less_than_twenty(10), These::These(Error::IsGreaterThanOrEqualToTen, LessThanTwenty(10)));
//! assert_eq!(is_less_than_twenty(20), These::This(Error::IsGreaterThanOrEqualToTwenty));
//!
//! assert_eq!(backwards_compatible(is_less_than_twenty(8)), Ok(LessThanTen(8)));
//! ```
//!
//! [`These`]: enum.These.html
//! [`This`]: enum.These.html#variant.This
//! [`That`]: enum.These.html#variant.That
//! [`These`]: enum.These.html#variant.These

#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
pub enum These<T, U> {
    This(T),
    That(U),
    These(T, U),
}

impl<T, U> These<T, U> {
    /// Convert from `&These<T, U>` to `These<&T, &U>`.
    /// Produce a new `These`, containing references to the original values.
    ///
    /// # Examples
    /// ```
    /// use these::These;
    ///
    /// let this: These<_, u32> = These::This(String::from("Hello"));
    /// assert_eq!(this.as_ref().this(), Some(&String::from("Hello")));
    /// assert_eq!(this.as_ref().that(), None);
    ///
    /// let that: These<&str, _> = These::That(42);
    /// let forty_two = that.as_ref().that();
    /// assert_eq!(forty_two, Some(&42));
    /// assert_eq!(that.this(), None);
    ///
    /// let these = These::These("Hello", 42);
    /// assert_eq!(these.as_ref().here(), Some(&"Hello"));
    /// assert_eq!(these.as_ref().there(), Some(&42));
    /// ```
    pub fn as_ref(&self) -> These<&T, &U> {
        match *self {
            These::This(ref t) => These::This(t),
            These::That(ref u) => These::That(u),
            These::These(ref t, ref u) => These::These(t, u),
        }
    }

    /// Convert from `&mut These<T, U>` to `These<&mut T, &mut U>`.
    /// Produce a new `These`, containing mutable references to the original values.
    ///
    /// # Examples
    /// ```
    /// use these::These;
    ///
    /// let mut this: These<_, u32> = These::This(String::from("Hello"));
    /// let mut world = this.as_mut().this().unwrap();
    /// world.push_str(" World!");
    /// assert_eq!(this.as_mut().this(), Some(&mut String::from("Hello World!")));
    /// assert_eq!(this.as_mut().that(), None);
    ///
    /// let mut that: These<&str, _> = These::That(42);
    /// let forty_two = that.as_mut().that().unwrap();
    /// *forty_two += 1;
    /// assert_eq!(that.as_ref().that(), Some(&43));
    /// assert_eq!(that.this(), None);
    ///
    /// let mut these = These::These("Hello", 42);
    /// assert_eq!(these.as_mut().here(), Some(&mut "Hello"));
    /// assert_eq!(these.as_mut().there(), Some(&mut 42));
    /// ```
    pub fn as_mut(&mut self) -> These<&mut T, &mut U> {
        match *self {
            These::This(ref mut t) => These::This(t),
            These::That(ref mut u) => These::That(u),
            These::These(ref mut t, ref mut u) => These::These(t, u),
        }
    }

    /// Collapse a [`These`](enum.These.html) value given a set of three functions to
    /// some target type.
    ///
    /// The first function will apply to [`This`], the second to [`That`],
    /// and the third to [`These`].
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
    ///
    /// [`This`]: enum.These.html#variant.This
    /// [`That`]: enum.These.html#variant.That
    /// [`These`]: enum.These.html#variant.These
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
    /// [`That`] or [`These`].
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
    ///
    /// [`That`]: enum.These.html#variant.That
    /// [`These`]: enum.These.html#variant.These
    pub fn map<V, F>(self, op: F) -> These<T, V>
        where F: FnOnce(U) -> V,
    {
        self.map_both(|x| x, op)
    }


    /// Apply the function to the `T` value if the data is
    /// [`This`] or [`These`].
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
    ///
    /// [`This`]: enum.These.html#variant.This
    /// [`These`]: enum.These.html#variant.These
    pub fn map_first<V, F>(self, op: F) -> These<V, U>
        where F: FnOnce(T) -> V,
    {
        self.map_both(op, |x| x)
    }

    /// Apply the function to the `U` value if the data is
    /// [`That`] or [`These`]. This is the same as `map`.
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
    ///
    /// [`That`]: enum.These.html#variant.That
    /// [`These`]: enum.These.html#variant.These
    pub fn map_second<V, F>(self, op: F) -> These<T, V>
        where F: FnOnce(U) -> V,
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
        where F: FnOnce(T) -> V,
              G: FnOnce(U) -> W,
    {
        match self {
            These::This(t) => These::This(f(t)),
            These::That(u) => These::That(g(u)),
            These::These(t, u) => These::These(f(t), g(u)),
        }
    }

    /// Collapse the [`These`](enum.These.hmtl) value but using a default value
    /// in place of `U` (ignoring any `U` values).
    ///
    /// If [`This`] is found it will return the default value.
    /// If [`That`] is found it will use the function with the value
    /// contained in [`That`] along with the default.
    /// If [`These`] is found it will use the function with the second element
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
    ///
    /// [`This`]: enum.These.html#variant.This
    /// [`That`]: enum.These.html#variant.That
    /// [`These`]: enum.These.html#variant.These
    pub fn fold_these<V, F>(self, default: V, op: F) -> V
        where F: FnOnce(U, V) -> V,
    {
        match self {
            These::This(_) => default,
            These::That(u) => op(u, default),
            These::These(_, u) => op(u, default),
        }
    }

    /// Create a tuple given a [`These`] value. In the case of [`This`]
    /// or [`That`] it will use the default values provided.
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
    ///
    /// [`These`]: enum.These.html
    /// [`This`]: enum.These.html#variant.This
    /// [`That`]: enum.These.html#variant.That
    pub fn from_these(self, t_default: T, u_default: U) -> (T, U)
    {
        self.collapse_these(
            |t| (t, u_default),
            |u| (t_default, u),
            |t, u| (t, u),
        )
    }

    /// Swap the types of values of a [`These`](enum.These.html) value.
    ///
    /// [`This`] turns into [`That`].
    /// [`That`] turns into [`This`].
    /// [`These`] values swap their order.
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
    ///
    /// [`This`]: enum.These.html#variant.This
    /// [`That`]: enum.These.html#variant.That
    /// [`These`]: enum.These.html#variant.These
    pub fn swap_these(self) -> These<U, T>
    {
        self.collapse_these(
            These::That,
            These::This,
            |t, u| These::These(u, t),
        )
    }

    /// Produce a [`Some`] from [`This`], otherwise return [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.this(), Some("Hello"));
    ///
    /// let that: These<&str, i8> = These::That(42);
    /// assert_eq!(that.this(), None);
    ///
    /// let these: These<&str, i8> = These::These("Hello", 42);
    /// assert_eq!(these.this(), None);
    /// ```
    ///
    /// [`This`]: enum.These.html#variant.This
    /// [`These`]: enum.These.html#variant.These
    /// [`Some`]: enum.Option.html#variant.Some
    /// [`None`]: enum.Option.html#variant.Some
    pub fn this(self) -> Option<T>
    {
        if let These::This(t) = self {
            Some(t)
        } else {
            None
        }
    }

    /// Produce a [`Some`] from [`That`], otherwise return [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.that(), None);
    ///
    /// let that: These<&str, i8> = These::That(42);
    /// assert_eq!(that.that(), Some(42));
    ///
    /// let these: These<&str, i8> = These::These("Hello", 42);
    /// assert_eq!(these.that(), None);
    /// ```
    ///
    /// [`That`]: enum.These.html#variant.That
    /// [`Some`]: enum.Option.html#variant.Some
    /// [`None`]: enum.Option.html#variant.Some
    pub fn that(self) -> Option<U>
    {
        if let These::That(u) = self {
            Some(u)
        } else {
            None
        }
    }

    /// Produce a [`Some`] from [`These`], otherwise return [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.these(), None);
    ///
    /// let that: These<&str, i8> = These::That(42);
    /// assert_eq!(that.these(), None);
    ///
    /// let these: These<&str, i8> = These::These("Hello", 42);
    /// assert_eq!(these.these(), Some(("Hello", 42)));
    /// ```
    ///
    /// [`These`]: enum.These.html#variant.These
    /// [`Some`]: enum.Option.html#variant.Some
    /// [`None`]: enum.Option.html#variant.Some
    pub fn these(self) -> Option<(T, U)>
    {
        if let These::These(t, u) = self {
            Some((t, u))
        } else {
            None
        }
    }

    /// Produce a [`Some`] if a [`This`] or [`These`] is found,
    /// otherwise [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.here(), Some("Hello"));
    ///
    /// let that: These<&str, i8> = These::That(42);
    /// assert_eq!(that.here(), None);
    ///
    /// let these: These<&str, i8> = These::These("Hello", 42);
    /// assert_eq!(these.here(), Some("Hello"));
    /// ```
    ///
    /// [`This`]: enum.These.html#variant.This
    /// [`These`]: enum.These.html#variant.These
    /// [`Some`]: enum.Option.html#variant.Some
    /// [`None`]: enum.Option.html#variant.Some
    pub fn here(self) -> Option<T>
    {
        match self {
            These::This(t) | These::These(t, _) => Some(t),
            These::That(_) => None,
        }
    }

    /// Produce a [`Some`] if a [`That`] or [`These`] is found,
    /// otherwise [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let this: These<&str, i8> = These::This("Hello");
    /// assert_eq!(this.there(), None);
    ///
    /// let that: These<&str, i8> = These::That(42);
    /// assert_eq!(that.there(), Some(42));
    ///
    /// let these: These<&str, i8> = These::These("Hello", 42);
    /// assert_eq!(these.there(), Some(42));
    /// ```
    ///
    /// [`That`]: enum.These.html#variant.That
    /// [`These`]: enum.These.html#variant.These
    /// [`Some`]: enum.Option.html#variant.Some
    /// [`None`]: enum.Option.html#variant.Some
    pub fn there(self) -> Option<U>
    {
        match self {
            These::That(u) | These::These(_, u) => Some(u),
            These::This(_) => None,
        }
    }

    /// Is it [`This`]?
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
    ///
    /// [`This`]: enum.These.html#variant.This
    pub fn is_this(&self) -> bool
    {
        if let These::This(_) = self {
            true
        } else {
            false
        }
    }

    /// Is it [`That`]?
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
    ///
    /// [`That`]: enum.These.html#variant.That
    pub fn is_that(&self) -> bool
    {
        if let These::That(_) = self {
            true
        } else {
            false
        }
    }

    /// Is it [`These`]?
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
    ///
    /// [`These`]: enum.These.html#variant.These
    pub fn is_these(&self) -> bool
    {
        if let These::These(_, _) = self {
            true
        } else {
            false
        }
    }

    /// Is it `Here`, i.e. [`This`] or [`These`]?
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
    ///
    /// [`This`]: enum.These.html#variant.This
    /// [`These`]: enum.These.html#variant.These
    pub fn is_here(&self) -> bool
    {
        match self {
            These::That(_) => false,
            _ => true,
        }
    }

    /// Is it `There`, i.e. [`That`] or [`These`]?
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
    ///
    /// [`That`]: enum.These.html#variant.That
    /// [`These`]: enum.These.html#variant.These
    pub fn is_there(&self) -> bool
    {
        match self {
            These::This(_) => false,
            _ => true,
        }
    }

    /// When given a [`Vec`] of [`These`](enum.These.hmtl) it will split it into
    /// three separate [`Vec`]s, each containing the [`This`], [`That`], or [`These`]
    /// inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use these::These;
    ///
    /// let xs = vec![These::This(1), These::That("Hello"), These::These(42, "World")];
    /// assert_eq!(These::partition_these(xs), (vec![1], vec!["Hello"], vec![(42, "World")]));
    /// ```
    ///
    /// [`This`]: enum.These.html#variant.This
    /// [`That`]: enum.These.html#variant.That
    /// [`These`]: enum.These.html#variant.These
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

    /// When given a [`Vec`] of [`These`](enum.These.html) it will split it into
    /// two separate `Vec`s, each containing the `T` or `U` inner values.
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
