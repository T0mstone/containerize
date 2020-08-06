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
//!

use bi_result::BiResult;
use std::iter::{once, FromIterator};
use std::marker::PhantomData;

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
    Contained(C, Vec<Self>),
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
    pub side: DelimeterSide,
    pub source_position: usize,
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
pub fn containerize<C: PartialEq, I: IntoIterator>(
    iter: I,
    mut detect_delimeter: impl FnMut(&I::Item) -> Option<(DelimeterSide, C)>,
) -> BiResult<Vec<Containerized<C, Vec<I::Item>>>, Vec<UnmatchedDelimeter<C>>> {
    let mut base: Vec<Containerized<C, Vec<I::Item>>> = vec![];
    let mut stack = vec![];
    let mut unmatched = vec![];
    for (i, t) in iter.into_iter().enumerate() {
        match detect_delimeter(&t) {
            Some((s, c)) => match s {
                DelimeterSide::Left => stack.push((i, c, vec![])),
                DelimeterSide::Right => match stack.last() {
                    Some((_, cl, _)) if *cl == c => {
                        let (_, c, last) = stack.pop().unwrap();
                        stack
                            .last_mut()
                            .map(|(_, _, v)| v)
                            .unwrap_or(&mut base)
                            .push(Containerized::Contained(c, last));
                    }
                    _ => {
                        // push an error and ignore it
                        unmatched.push(UnmatchedDelimeter {
                            side: DelimeterSide::Right,
                            source_position: i,
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
    }
    if !stack.is_empty() {
        // prepend the rest
        let extra = stack.into_iter().map(|(i, c, last)| {
            // push an error and ignore the beginning delim
            unmatched.push(UnmatchedDelimeter {
                side: DelimeterSide::Left,
                source_position: i,
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
    BiResult(base, unmatched)
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

impl<C, T> Containerized<C, T> {
    /// Convert from an `IntoIterator` of a `Containerized` (e.g. `vec![Single(t1), Single(t2), Contained(...), ...]`)
    /// to a `Vec` of `Containerized`s of `Vec`s (e.g. `vec![Single(vec![t1, t2]), Contained(...), ...]`)
    pub fn collect_single<I: IntoIterator<Item = Self>>(v: I) -> Vec<Containerized<C, Vec<T>>> {
        v.into_iter().fold(vec![], |mut res, e: Self| {
            match e {
                Containerized::Single(t) => match res.last_mut() {
                    Some(Containerized::Single(v)) => v.push(t),
                    _ => res.push(Containerized::Single(vec![t])),
                },
                Containerized::Contained(c, v) => {
                    res.push(Containerized::Contained(c, Self::collect_single(v)))
                }
            }
            res
        })
    }
}

pub mod visit;

impl<C, T> Containerized<C, T> {
    /// returns the container kind if `self` is `Contained`, `None` otherwise
    #[inline]
    pub fn container_kind(&self) -> Option<&C> {
        if let Containerized::Contained(kind, _) = self {
            Some(kind)
        } else {
            None
        }
    }

    pub fn children(&self) -> &[Self] {
        match self {
            Containerized::Single(_) => &[],
            Containerized::Contained(_, v) => &v,
        }
    }

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
        U,
        I: IntoIterator<Item = U>,
        F: FnMut(T) -> I,
        J: FromIterator<Containerized<C, U>>,
    >(
        self,
        f: F,
    ) -> J {
        struct Inner<T, U, I: IntoIterator<Item = U>, F: FnMut(T) -> I>(F, PhantomData<(T, U, I)>);

        impl<T, U, I: IntoIterator<Item = U>, F: FnMut(T) -> I> Inner<T, U, I, F> {
            pub fn f<C, J: FromIterator<Containerized<C, U>>>(
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

#[cfg(test)]
mod tests {
    use crate::visit::*;
    use crate::*;

    #[test]
    fn containerized() {
        let v = vec![b'(', 2, b')', 2, b')', b'(', 2];
        let BiResult(c, e) = containerize(v, |&t| {
            if t == b'(' {
                Some((DelimeterSide::Left, ()))
            } else if t == b')' {
                Some((DelimeterSide::Right, ()))
            } else {
                None
            }
        });
        assert_eq!(
            c,
            vec![
                Containerized::Contained((), vec![Containerized::Single(vec![2])]),
                Containerized::Single(vec![2, 2])
            ]
        );
        assert_eq!(
            e,
            vec![
                UnmatchedDelimeter {
                    side: DelimeterSide::Right,
                    source_position: 4,
                    kind: ()
                },
                UnmatchedDelimeter {
                    side: DelimeterSide::Left,
                    source_position: 5,
                    kind: ()
                }
            ]
        );
    }

    #[test]
    fn spread_collect() {
        let c = Containerized::<(), _>::Single(vec![2, 3, 4]);
        let cs = c.clone().spread_single::<Vec<_>>();
        assert_eq!(
            cs,
            vec![
                Containerized::Single(2),
                Containerized::Single(3),
                Containerized::Single(4)
            ]
        );
        assert_eq!(Containerized::collect_single(cs), vec![c]);
    }

    #[test]
    fn visit() {
        let mut c = Containerized::<(), _>::Contained(
            (),
            vec![
                Containerized::Single(3),
                Containerized::Contained(
                    (),
                    vec![Containerized::Single(4), Containerized::Single(5)],
                ),
                Containerized::Single(6),
            ],
        );
        let mut sum = 0;
        c.visit(|x| {
            if let Containerized::Single(n) = *x {
                sum += n
            }
        });
        assert_eq!(sum, 3 + 4 + 5 + 6);
        let mut c2 = c.clone();
        c.visit(|x| match x {
            Containerized::Single(n) => {
                *n += 1;
            }
            Containerized::Contained(_, v) => {
                v.push(Containerized::Single(1));
            }
        });
        let ctrl = Containerized::<(), _>::Contained(
            (),
            vec![
                Containerized::Single(4),
                Containerized::Contained(
                    (),
                    vec![
                        Containerized::Single(5),
                        Containerized::Single(6),
                        Containerized::Single(2),
                    ],
                ),
                Containerized::Single(7),
                Containerized::Single(2),
            ],
        );
        assert_eq!(c, ctrl);
        c2.visit_with_config(
            |x| match x {
                Containerized::Single(n) => {
                    *n += 1;
                }
                Containerized::Contained(_, v) => {
                    v.push(Containerized::Single(1));
                }
            },
            VisitConfig {
                order: TraversalOrder::ParentLast,
                ..Default::default()
            },
        );
        let ctrl = Containerized::<(), _>::Contained(
            (),
            vec![
                Containerized::Single(4),
                Containerized::Contained(
                    (),
                    vec![
                        Containerized::Single(5),
                        Containerized::Single(6),
                        Containerized::Single(1),
                    ],
                ),
                Containerized::Single(7),
                Containerized::Single(1),
            ],
        );
        assert_eq!(c2, ctrl);
    }

    #[test]
    fn map() {
        let c = Containerized::<(), u8>::Single(3);
        assert_eq!(c.map(|x| x + 1), Containerized::Single(4));
        let c = Containerized::<(), u8>::Contained(
            (),
            vec![Containerized::Single(2), Containerized::Single(3)],
        );
        let ctrl = Containerized::<(), u8>::Contained(
            (),
            vec![Containerized::Single(3), Containerized::Single(4)],
        );
        assert_eq!(c.map(|x| x + 1), ctrl);
        let c = Containerized::<u8, u8>::Contained(
            1,
            vec![Containerized::Single(2), Containerized::Single(3)],
        );
        let ctrl = Containerized::<u8, u8>::Contained(
            2,
            vec![Containerized::Single(2), Containerized::Single(3)],
        );
        assert_eq!(c.map_kind(|x| x + 1), ctrl);
    }

    #[test]
    fn join() {
        let c = Containerized::<(), _>::Contained(
            (),
            vec![
                Containerized::Contained(
                    (),
                    vec![
                        Containerized::Contained((), vec![]),
                        Containerized::Contained((), vec![Containerized::Single(3)]),
                    ],
                ),
                Containerized::Single(3),
                Containerized::Single(4),
            ],
        );
        assert_eq!(
            c.uncontainerize(|_| (b'(', b')')),
            vec![b'(', b'(', b'(', b')', b'(', 3, b')', b')', 3, 4, b')']
        );
    }
}
