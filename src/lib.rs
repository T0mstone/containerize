//! A simple crate for a single data structure and related functionality
//!
//! # Example
//! Consider wanting to parse parentheses as well as square brackets.
//! As input, we'll take the string `"abc(d[ef]g[[h]]i)j[kl(m)]n"` (or rather, its chars as a `Vec`)
//!
//! Upon parsing, it is represented as (simplified notation)
//! ```ignore
//! [
//!  'a', 'b', 'c',
//!     C(Par, ['d',
//!         C(Squ, ['e', 'f']),
//!         'g',
//!         C(Squ, [C(Squ, ['h'])]),
//!         'i']
//!     ),
//!  'j',
//!     C(Squ, ['k', 'l',
//!         C(Par, ['m'])
//!     ]),
//!  'n'
//! ]
//! ```
//! (In real code, `C` is called `Contained`, you'd have every single char enclosed in a `Single` and you'd have to create the enum with variants `Squ` and `Par` yourself)

#![warn(missing_docs)]
use apply::*;
use std::iter::{once, FilterMap, FromIterator};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

/// The core data type. It represents grouped pieces of a stream.
///
/// `C` is the container type, `T` is the content type.
///
/// For more info, see the [module level documentation](/)
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Containerized<C, T> {
    /// A single item
    Single(T),
    /// A contained block of items
    Contained(C, ContainerizedVec<C, T>),
}

/// A wrapper type for `Vec<Containerized<C, T>>` with some wrapper methods to shorten code
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ContainerizedVec<C, T>(pub Vec<Containerized<C, T>>);

impl<C, T> Deref for ContainerizedVec<C, T> {
    type Target = Vec<Containerized<C, T>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<C, T> DerefMut for ContainerizedVec<C, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<C, T> IntoIterator for ContainerizedVec<C, T> {
    type Item = Containerized<C, T>;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<C, T> FromIterator<Containerized<C, T>> for ContainerizedVec<C, T> {
    fn from_iter<I: IntoIterator<Item = Containerized<C, T>>>(iter: I) -> Self {
        Self(Vec::from_iter(iter))
    }
}

/// The side of a delimeter, i.e. left or right
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum DelimeterSide {
    #[allow(missing_docs)]
    Left,
    #[allow(missing_docs)]
    Right,
}

impl DelimeterSide {
    /// Decide on left or right based on which of the arguments `t` is equal to
    ///
    /// Returns `None` is `t` is equal to both or neither of the two options
    #[inline]
    pub fn from<T: PartialEq>(t: T, left: T, right: T) -> Option<Self> {
        let left = t == left;
        let right = t == right;
        if left == right {
            None
        } else if left {
            Some(DelimeterSide::Left)
        } else {
            // in this case, `right == true` since `right == false && left == false` is already covered by the first case
            Some(DelimeterSide::Right)
        }
    }

    /// Pick an element from `left` or `right`, depending on the value of `self`
    #[inline]
    pub fn choose<T>(self, left: T, right: T) -> T {
        match self {
            DelimeterSide::Left => left,
            DelimeterSide::Right => right,
        }
    }
}

/// An Error created when there are unmatched delimeters, like in `abc(`
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct UnmatchedDelimeter<C> {
    /// The side of the unmatched delimeter
    pub side: DelimeterSide,
    /// The position of the unmatched delimeter
    pub source_position: usize,
    /// The kind of the unmatched delimeter
    pub kind: C,
}

/// A function for creating `Containerized` data from a linear stream of tokens
///
/// # Unmatched delimeters
/// The second return value is a `Vec` of all unmatched delimeters that were encountered.
/// In the actual result, i.e. the first return value, unmatched delimeters are ignored completely
///
/// Note that in `abc[(def])`, both `[` and `]` would be counted as unmatched delimeters
#[allow(clippy::type_complexity)]
pub fn containerize<
    C: PartialEq,
    I: IntoIterator,
    F: FnMut(&I::Item) -> Option<(DelimeterSide, C)>,
    G: FnMut(&I::Item) -> usize,
>(
    iter: I,
    mut detect_delimeter: F,
    mut get_len: G,
    errs: &mut Vec<UnmatchedDelimeter<C>>,
) -> ContainerizedVec<C, Vec<I::Item>> {
    let mut base: Vec<Containerized<C, Vec<I::Item>>> = vec![];
    let mut stack = vec![];
    let mut source_position = 0;
    for t in iter {
        let delta = get_len(&t);
        match detect_delimeter(&t) {
            Some((s, c)) => match s {
                DelimeterSide::Left => stack.push((source_position, c, vec![])),
                DelimeterSide::Right => match stack.last() {
                    Some((_, cl, _)) if *cl == c => {
                        let (_, c, last) = stack.pop().unwrap();
                        stack
                            .last_mut()
                            .map(|(_, _, v)| v)
                            .unwrap_or(&mut base)
                            .push(Containerized::Contained(c, ContainerizedVec(last)));
                    }
                    _ => {
                        // push an error and ignore it
                        errs.push(UnmatchedDelimeter {
                            side: DelimeterSide::Right,
                            source_position,
                            kind: c,
                        });
                    }
                },
            },
            None => {
                let top = stack.last_mut().map(|(_, _, v)| v).unwrap_or(&mut base);
                if let Some(Containerized::Single(w)) = top.last_mut() {
                    w.push(t)
                } else {
                    top.push(Containerized::Single(vec![t]))
                }
            }
        }
        source_position += delta;
    }
    if !stack.is_empty() {
        // prepend the rest
        let extra = stack.into_iter().map(|(source_position, c, last)| {
            // push an error and ignore the beginning delim
            errs.push(UnmatchedDelimeter {
                side: DelimeterSide::Left,
                source_position,
                kind: c,
            });
            // ignoring means flattening the structure
            last
        });
        for mut ev in extra {
            if ev.is_empty() {
                continue;
            }
            match ev.remove(0) {
                e @ Containerized::Contained(_, _) => base.push(e),
                Containerized::Single(mut sv) => {
                    if let Some(Containerized::Single(w)) = base.last_mut() {
                        w.append(&mut sv);
                    } else {
                        base.push(Containerized::Single(sv))
                    }
                }
            }
        }
        // base.extend(extra);
    }
    ContainerizedVec(base)
}

/// A shortcut that automatically converts a string to chars before containerizing and converts it back to a `String` after containerizing
pub fn containerize_chars<C: PartialEq, F: FnMut(char) -> Option<(DelimeterSide, C)>>(
    s: &str,
    mut detect_delimeter: F,
    errs: &mut Vec<UnmatchedDelimeter<C>>,
) -> ContainerizedVec<C, String> {
    containerize(s.chars(), |&c| detect_delimeter(c), |c| c.len_utf8(), errs)
        .into_iter()
        .map(|c: Containerized<C, Vec<char>>| c.map(|v| v.into_iter().collect()))
        .collect()
}

impl<C, I: IntoIterator<Item = T>, T> Containerized<C, I> {
    /// Convert from a `Containerized` of an `IntoIterator` (e.g. `Single(vec![t1, t2, ...])`)
    /// to a `FromIterator` of `Containerized`s (e.g. `vec![Single(t1), Single(t2), ...].into_iter()`)
    pub fn spread_single<J: FromIterator<Containerized<C, T>>>(self) -> J {
        match self {
            Containerized::Single(v) => v.into_iter().map(Containerized::Single).collect(),
            Containerized::Contained(c, v) => once(Containerized::Contained(
                c,
                v.into_iter()
                    .flat_map(Containerized::spread_single::<Vec<_>>)
                    .collect(),
            ))
            .collect(),
        }
    }
}

impl<C, T> ContainerizedVec<C, T> {
    /// Convert from a `ContainerizedVec` (e.g. `ContainerizedVec(vec![Single(t1), Single(t2), Contained(...), ...])`)
    /// to a `ContainerizedVec` of `Vec`s (e.g. `ContainerizedVec(vec![Single(vec![t1, t2]), Contained(...), ...])`)
    pub fn collapse_single(self) -> ContainerizedVec<C, Vec<T>> {
        self.into_iter()
            .fold(
                vec![],
                |mut res: Vec<Containerized<C, Vec<T>>>, e: Containerized<C, T>| {
                    match e {
                        Containerized::Single(t) => match res.last_mut() {
                            Some(Containerized::Single(v)) => v.push(t),
                            _ => res.push(Containerized::Single(vec![t])),
                        },
                        Containerized::Contained(c, v) => {
                            res.push(Containerized::Contained(c, v.collapse_single()))
                        }
                    }
                    res
                },
            )
            .apply(ContainerizedVec)
    }
}

pub mod visit;

impl<C, T> Containerized<C, T> {
    /// A small helper to avoid having to wrap the second argument of `Contained` in a `ContainerizedVec` manually
    #[inline]
    pub fn contained(c: C, v: Vec<Self>) -> Self {
        Self::Contained(c, ContainerizedVec(v))
    }

    /// Returns the container kind if `self` is `Contained`, `None` otherwise
    #[inline]
    pub fn container_kind(&self) -> Option<&C> {
        if let Containerized::Contained(kind, _) = self {
            Some(kind)
        } else {
            None
        }
    }

    /// Returns the children of `self` by reference
    ///
    /// Returns `&[]` if `self` is a `Single`
    pub fn children(&self) -> &[Self] {
        match self {
            Containerized::Single(_) => &[],
            Containerized::Contained(_, v) => &v,
        }
    }

    /// Returns the children of `self` by mutable references
    ///
    /// Returns `vec![]` if `self` is a `Single`
    pub fn children_mut(&mut self) -> Vec<&mut Self> {
        match self {
            Containerized::Single(_) => Vec::new(),
            Containerized::Contained(_, v) => v.iter_mut().collect(),
        }
    }

    /// Maps the value inside a `Single` using the given function
    #[inline]
    pub fn map<U>(self, f: impl FnMut(T) -> U) -> Containerized<C, U> {
        struct Inner<T, U, F: FnMut(T) -> U>(F, PhantomData<(T, U)>);

        impl<T, U, F: FnMut(T) -> U> Inner<T, U, F> {
            pub fn f<C>(&mut self, c: Containerized<C, T>) -> Containerized<C, U> {
                match c {
                    Containerized::Single(t) => Containerized::Single(self.0(t)),
                    Containerized::Contained(c, v) => {
                        Containerized::Contained(c, v.into_iter().map(|x| self.f(x)).collect())
                    }
                }
            }
        }

        Inner(f, PhantomData).f(self)
    }

    /// Maps the value inside a `Single` using the given function, which can return more than one value
    #[inline]
    pub fn multi_map<
        I: IntoIterator,
        F: FnMut(T) -> I,
        J: FromIterator<Containerized<C, I::Item>>,
    >(
        self,
        f: F,
    ) -> J {
        struct Inner<T, I: IntoIterator, F: FnMut(T) -> I>(F, PhantomData<(T, I)>);

        impl<T, I: IntoIterator, F: FnMut(T) -> I> Inner<T, I, F> {
            pub fn f<C, J: FromIterator<Containerized<C, I::Item>>>(
                &mut self,
                c: Containerized<C, T>,
            ) -> J {
                match c {
                    Containerized::Single(t) => {
                        self.0(t).into_iter().map(Containerized::Single).collect()
                    }
                    Containerized::Contained(c, v) => once(Containerized::Contained(
                        c,
                        v.into_iter().flat_map(|x| self.f::<C, Vec<_>>(x)).collect(),
                    ))
                    .collect(),
                }
            }
        }

        Inner(f, PhantomData).f(self)
    }

    /// Maps the value inside a `Single` using the given function, which returns an `Option`
    #[inline]
    pub fn filter_map<U>(self, f: impl FnMut(T) -> Option<U>) -> Option<Containerized<C, U>> {
        struct Inner<T, U, F: FnMut(T) -> Option<U>>(F, PhantomData<(T, U)>);

        impl<T, U, F: FnMut(T) -> Option<U>> Inner<T, U, F> {
            pub fn f<C>(&mut self, c: Containerized<C, T>) -> Option<Containerized<C, U>> {
                Some(match c {
                    Containerized::Single(t) => Containerized::Single(self.0(t)?),
                    Containerized::Contained(c, v) => Containerized::Contained(
                        c,
                        v.into_iter().filter_map(|x| self.f(x)).collect(),
                    ),
                })
            }
        }

        Inner(f, PhantomData).f(self)
    }

    /// Maps the kind, i.e. the first value inside a `Contained` using the given function
    #[inline]
    pub fn map_kind<K>(self, f: impl FnMut(C) -> K) -> Containerized<K, T> {
        struct Inner<C, K, F: FnMut(C) -> K>(F, PhantomData<(C, K)>);

        impl<C, K, F: FnMut(C) -> K> Inner<C, K, F> {
            pub fn f<T>(&mut self, c: Containerized<C, T>) -> Containerized<K, T> {
                match c {
                    Containerized::Single(t) => Containerized::Single(t),
                    Containerized::Contained(c, v) => Containerized::Contained(
                        self.0(c),
                        v.into_iter().map(|x| self.f(x)).collect(),
                    ),
                }
            }
        }

        Inner(f, PhantomData).f(self)
    }

    /// Flattens the structure to create a linear stream of tokens
    ///
    /// `make_delim` is used to create a pair of delimeters for a container kind
    pub fn uncontainerize(self, make_delim: impl FnMut(C) -> (T, T)) -> Vec<T> {
        struct Inner<C, T, F: FnMut(C) -> (T, T)>(F, PhantomData<(C, T)>);

        impl<C, T, F: FnMut(C) -> (T, T)> Inner<C, T, F> {
            pub fn f(&mut self, c: Containerized<C, T>) -> Vec<T> {
                match c {
                    Containerized::Single(t) => vec![t],
                    Containerized::Contained(c, v) => {
                        let (left, right) = self.0(c);
                        let mut res = vec![left];
                        res.append(&mut v.into_iter().flat_map(|c| self.f(c)).collect());
                        res.push(right);
                        res
                    }
                }
            }
        }

        Inner(make_delim, PhantomData).f(self)
    }
}

impl<C, T> ContainerizedVec<C, T> {
    /// A wrapper for [`Containerized::map`](struct.Containerized.html#method.map)
    #[inline]
    pub fn map<U, F: FnMut(T) -> U>(self, mut f: F) -> ContainerizedVec<C, U> {
        self.0.into_iter().map(|c| c.map(&mut f)).collect()
    }

    /// A wrapper for [`Containerized::multi_map`](struct.Containerized.html#method.multi_map)
    #[inline]
    pub fn multi_map<I: IntoIterator, F: FnMut(T) -> I>(
        self,
        mut f: F,
    ) -> ContainerizedVec<C, I::Item> {
        self.0
            .into_iter()
            .flat_map(|c| c.multi_map::<I, _, Vec<_>>(&mut f))
            .collect()
    }

    /// A wrapper for [`Containerized::filter_map`](struct.Containerized.html#method.filter_map)
    #[inline]
    pub fn filter_map<U, F: FnMut(T) -> Option<U>>(self, mut f: F) -> ContainerizedVec<C, U> {
        self.0
            .into_iter()
            .filter_map(|c| c.filter_map(&mut f))
            .collect()
    }

    /// A wrapper for [`Containerized::map_kind`](struct.Containerized.html#method.map_kind)
    #[inline]
    pub fn map_kind<K, F: FnMut(C) -> K>(self, mut f: F) -> ContainerizedVec<K, T> {
        self.0.into_iter().map(|c| c.map_kind(&mut f)).collect()
    }

    /// A wrapper for [`Containerized::uncontainerize`](struct.Containerized.html#method.uncontainerize)
    #[inline]
    pub fn uncontainerize<F: FnMut(C) -> (T, T)>(self, mut make_delim: F) -> Vec<T> {
        self.0
            .into_iter()
            .flat_map(|c| c.uncontainerize(&mut make_delim))
            .collect()
    }

    /// Split the top-most layer (contents of `Contained` are left untouched) according to `split_single`,
    /// which splits a single element - adjacent elements are joint together using `join_asdjacent`
    pub fn split_inner<I: IntoIterator<Item = T>, F: FnMut(T) -> I, G: FnMut(T, T) -> T>(
        self,
        mut split_single: F,
        mut join_adjacent: G,
    ) -> Vec<ContainerizedVec<C, I::Item>> {
        self.0
            .into_iter()
            .fold(vec![ContainerizedVec(vec![])], |mut acc, c| {
                match c {
                    Containerized::Single(t) => {
                        let mut spl = split_single(t).into_iter();
                        if let Some(Some(Containerized::Single(rx))) =
                            acc.last_mut().map(|v| v.last_mut())
                        {
                            if let Some(y) = spl.next() {
                                // SAFETY: since the original rx isn't touched between the read and the write, this is safe
                                unsafe {
                                    let x = std::ptr::read(rx);
                                    std::ptr::write(rx, join_adjacent(x, y))
                                }
                            }
                        }

                        acc.push(spl.map(Containerized::Single).collect())
                    }
                    Containerized::Contained(..) => acc.last_mut().unwrap().push(c),
                }
                acc
            })
    }
}

fn trim_helper<
    'a,
    C,
    J: IntoIterator,
    I: Iterator<Item = Containerized<C, J>> + 'a,
    F: FnMut(&J::Item) -> bool + 'a,
>(
    iter: I,
    mut f: F,
) -> FilterMap<I, impl FnMut(Containerized<C, J>) -> Option<Containerized<C, Vec<J::Item>>>> {
    let mut start = true;
    iter.filter_map(move |c| {
        if start {
            match c {
                Containerized::Single(v) => {
                    let v = v.into_iter().skip_while(&mut f).collect::<Vec<_>>();
                    if v.is_empty() {
                        None
                    } else {
                        start = false;
                        Some(Containerized::Single(v))
                    }
                }
                Containerized::Contained(..) => {
                    start = false;
                    Some(c.map(|i| i.into_iter().collect()))
                }
            }
        } else {
            Some(c.map(|i| i.into_iter().collect()))
        }
    })
}

impl<C, I: IntoIterator> ContainerizedVec<C, I> {
    /// Split the top-most layer (contents of `Contained` are left untouched) according to `is_sep`,
    /// which determines, whether an item is a separator
    pub fn split<F: FnMut(&I::Item) -> bool>(
        self,
        mut is_sep: F,
        fuse_repeated: bool,
    ) -> Vec<ContainerizedVec<C, Vec<I::Item>>> {
        self.0
            .into_iter()
            .fold(vec![ContainerizedVec(vec![])], |mut acc, c| {
                match c {
                    Containerized::Single(v) => {
                        for t in v {
                            if is_sep(&t) {
                                if !(fuse_repeated && acc.last_mut().unwrap().is_empty()) {
                                    acc.push(ContainerizedVec(vec![]));
                                }
                            } else {
                                // we preserve the boundaries between `Single` items, we only create new ones
                                match acc.last_mut().unwrap().last_mut() {
                                    Some(Containerized::Single(v)) => v.push(t),
                                    _ => {
                                        acc.last_mut().unwrap().push(Containerized::Single(vec![t]))
                                    }
                                }
                            }
                        }
                    }
                    Containerized::Contained(..) => acc
                        .last_mut()
                        .unwrap()
                        .push(c.map(|i| i.into_iter().collect())),
                }
                acc
            })
    }

    /// Removes all items for which `f` returns `true` from the start (contents of `Contained` are left untouched);
    /// stops at the first item where `f` returns `false` (or at the first `Contained`)
    pub fn trim_start_matches<F: FnMut(&I::Item) -> bool>(
        self,
        f: F,
    ) -> ContainerizedVec<C, Vec<I::Item>> {
        trim_helper(self.0.into_iter(), f).collect()
    }

    /// Removes all items for which `f` returns `true` from the end (contents of `Contained` are left untouched);
    /// stops at the first (from the end) item where `f` returns `false` (or at the first `Contained`)
    pub fn trim_end_matches<F: FnMut(&I::Item) -> bool>(
        self,
        f: F,
    ) -> ContainerizedVec<C, Vec<I::Item>> {
        trim_helper(Vec::from_iter(self.0).into_iter().rev(), f)
            .rev()
            .collect()
    }

    /// A combination of [`trim_start_matches`](#method.trim_start_matches) and [`trim_end_matches`](#method.trim_end_matches)
    pub fn trim_matches<F: FnMut(&I::Item) -> bool>(
        self,
        mut f: F,
    ) -> ContainerizedVec<C, Vec<I::Item>> {
        // getting rid of one of the `collect`s here is impossible since that would double-mut-borrow `f`
        self.trim_start_matches(&mut f).trim_end_matches(f)
    }
}

impl<C> ContainerizedVec<C, String> {
    /// Splits according to `char::is_whitespace`, treats multiple whitespaces in a row as a single separator\
    /// Otherwise behaves like [`split`](#method.split)
    pub fn split_whitespace(self) -> Vec<Self> {
        // self.map(|s| s.chars().collect::<Vec<_>>())
        //     .split(|u| u.is_whitespace(), true)
        //     .into_iter()
        //     .map(|v| v.map(String::from_iter))
        //     .collect()
        self.split_inner(
            |s| {
                s.split_whitespace()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
            },
            |a, b| a.also(|a| a.push_str(&b)),
        )
    }

    /// A wrapper for [`trim_start_matches(|c: char| c.is_whitespace())`](#method.trim_start_matches)
    pub fn trim_start(self) -> Self {
        self.map(|s| s.chars().collect::<Vec<_>>())
            .trim_start_matches(|&c| c.is_whitespace())
            .map(String::from_iter)
    }

    /// A wrapper for [`trim_end_matches(|c: char| c.is_whitespace())`](#method.trim_end_matches)
    pub fn trim_end(self) -> Self {
        self.map(|s| s.chars().collect::<Vec<_>>())
            .trim_end_matches(|&c| c.is_whitespace())
            .map(String::from_iter)
    }

    /// A wrapper for [`trim_matches(|c: char| c.is_whitespace())`](#method.trim_matches)
    pub fn trim(self) -> Self {
        self.map(|s| s.chars().collect::<Vec<_>>())
            .trim_matches(|&c| c.is_whitespace())
            .map(String::from_iter)
    }
}

impl<C> ContainerizedVec<C, Vec<u8>> {
    /// Splits according to `u8::is_ascii_whitespace`, treats multiple whitespaces in a row as a single separator\
    /// Otherwise behaves like [`split`](#method.split)
    pub fn split_whitespace(self) -> Vec<Self> {
        self.split(|u| u.is_ascii_whitespace(), true)
    }

    /// A wrapper for [`trim_start_matches(|c: u8| c.is_ascii_whitespace())`](#method.trim_start_matches)
    pub fn trim_start(self) -> Self {
        self.trim_start_matches(|u| u.is_ascii_whitespace())
    }

    /// A wrapper for [`trim_end_matches(|c: u8| c.is_ascii_whitespace())`](#method.trim_end_matches)
    pub fn trim_end(self) -> Self {
        self.trim_end_matches(|u| u.is_ascii_whitespace())
    }

    /// A wrapper for [`trim_matches(|c: u8| c.is_ascii_whitespace())`](#method.trim_matches)
    pub fn trim(self) -> Self {
        self.trim_matches(|u| u.is_ascii_whitespace())
    }
}

/// A macro to simplify creating a `Containerized` by hand
///
/// # Syntax
/// 1.
/// ```
/// # use containerize::{Containerized, containerized};
/// let c = containerized!(3 => [4, 5]);
/// assert_eq!(c, Containerized::contained(3, vec![Containerized::Single(4), Containerized::Single(5)]));
/// ```
/// 2.
/// ```
/// # use containerize::{Containerized, containerized};
/// let c = containerized!("single");
/// assert_eq!(c, Containerized::<(), &str>::Single("single"));
/// ```
#[macro_export]
macro_rules! containerized {
    ($c:expr => [$($e:expr $(=> [$($t:tt)*])?),*$(,)?]) => {
        $crate::Containerized::contained($c, vec![$($crate::containerized!($e $(=> [$($t)*])?)),*])
    };
    ($e:expr) => {
        $crate::Containerized::Single($e)
    };
}

/// A macro to simplify creating a `ContainerizedVec`, building upon [`containerized!`](macro.containerized.html)
///
/// # Syntax
/// ```
/// # use containerize::{Containerized, ContainerizedVec, containerized_vec};
/// let c = containerized_vec![1, 2 => [3, 4 => [5]], 6];
/// assert_eq!(c, ContainerizedVec(vec![
///     Containerized::Single(1),
///     Containerized::contained(2, vec![
///         Containerized::Single(3), Containerized::contained(4, vec![Containerized::Single(5)])
///     ]),
///     Containerized::Single(6)
/// ]));
/// ```
#[macro_export]
macro_rules! containerized_vec {
    ($($e:expr $(=> [$($t:tt)*])?),*$(,)?) => {
        $crate::ContainerizedVec(vec![$($crate::containerized!($e $(=> [$($t)*])?)),*])
    };
}

#[cfg(test)]
mod tests;
