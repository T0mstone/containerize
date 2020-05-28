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

use std::fmt::Debug;

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

/// An Error created when there are unmatched delimeters, like in `abc(`
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct UnmatchedDelimeter<C>(DelimeterSide, usize, C);

/// A function for creating `Containerized` data from a linear stream of tokens
///
/// # Unmatched delimeters
/// The second return value is a `Vec` of all unmatched delimeters that were encountered.
/// In the actual result, i.e. the first return value, unmatched delimeters are ignored completely
///
/// Note that in `abc[(def])`, both `[` and `]` would be counted as unmatched delimeters
#[allow(clippy::type_complexity)]
pub fn containerize<C: PartialEq + Debug, T: Debug>(
    v: Vec<T>,
    mut detect_delimeter: impl FnMut(&T) -> Option<(DelimeterSide, C)>,
) -> (Vec<Containerized<C, Vec<T>>>, Vec<UnmatchedDelimeter<C>>) {
    let mut base: Vec<Containerized<C, Vec<T>>> = vec![];
    let mut stack = vec![];
    let mut unmatched = vec![];
    for (i, t) in v.into_iter().enumerate() {
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
                        unmatched.push(UnmatchedDelimeter(DelimeterSide::Right, i, c));
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
            unmatched.push(UnmatchedDelimeter(DelimeterSide::Left, i, c));
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
    (base, unmatched)
}

impl<C, T> Containerized<C, Vec<T>> {
    /// Convert from `Single(vec![t1, t2, ...])` to `vec![Single(t1), Single(t2), ...]`
    pub fn spread_single(self) -> Vec<Containerized<C, T>> {
        match self {
            Containerized::Single(v) => v.into_iter().map(Containerized::Single).collect(),
            Containerized::Contained(c, v) => vec![Containerized::Contained(
                c,
                v.into_iter()
                    .flat_map(Containerized::spread_single)
                    .collect(),
            )],
        }
    }

    /// Convert from `vec![Single(t1), Single(t2), Contained(...), ...]` to `vec![Single(vec![t1, t2]), Contained(...), ...]`
    pub fn collect_single(v: Vec<Containerized<C, T>>) -> Vec<Self> {
        v.into_iter().fold(vec![], |mut res, e| {
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

impl<C, T> Containerized<C, T> {
    /// works like [visit] but passes `self` mutably, allowing the function to mutate `self`
    #[inline]
    pub fn visit_mut(&mut self, mut f: impl FnMut(&mut Self), reverse: bool) {
        self.visit_mut_inner(&mut f, reverse)
    }

    fn visit_mut_inner(&mut self, f: &mut impl FnMut(&mut Self), reverse: bool) {
        if !reverse {
            f(self);
        }
        match self {
            Containerized::Single(_) => (),
            Containerized::Contained(_, v) => {
                for e in v {
                    e.visit_mut_inner(f, reverse)
                }
            }
        }
        if reverse {
            f(self);
        }
    }

    /// Call a function with every recursive leaf of the tree
    ///
    /// When `reverse` is `false`, the function is called on parents before their children.
    /// When it is `true`, the opposite is the case.
    #[inline]
    pub fn visit(&self, mut f: impl FnMut(&Self), reverse: bool) {
        self.visit_inner(&mut f, reverse)
    }

    fn visit_inner(&self, f: &mut impl FnMut(&Self), reverse: bool) {
        if !reverse {
            f(self);
        }
        match self {
            Containerized::Single(_) => (),
            Containerized::Contained(_, v) => {
                for e in v {
                    e.visit_inner(f, reverse)
                }
            }
        }
        if reverse {
            f(self);
        }
    }

    /// Maps the value inside a `Single` using the given function
    #[inline]
    pub fn map_single<U>(self, mut f: impl FnMut(T) -> U) -> Containerized<C, U> {
        self.map_single_inner(&mut f as _)
    }

    fn map_single_inner<U>(self, f: &mut impl FnMut(T) -> U) -> Containerized<C, U> {
        match self {
            Containerized::Single(t) => Containerized::Single(f(t)),
            Containerized::Contained(c, v) => {
                Containerized::Contained(c, v.into_iter().map(|x| x.map_single_inner(f)).collect())
            }
        }
    }

    /// Maps the kind, i.e. the first value inside a `Contained` using the given function
    #[inline]
    pub fn map_kind<K>(self, mut f: impl FnMut(C) -> K) -> Containerized<K, T> {
        self.map_kind_inner(&mut f)
    }

    fn map_kind_inner<K>(self, f: &mut impl FnMut(C) -> K) -> Containerized<K, T> {
        match self {
            Containerized::Single(t) => Containerized::Single(t),
            Containerized::Contained(c, v) => {
                Containerized::Contained(f(c), v.into_iter().map(|x| x.map_kind_inner(f)).collect())
            }
        }
    }

    /// Flattens the structure to create a linear stream of tokens
    ///
    /// `make_delim` is used to create a pair of delimeters for a container kind
    pub fn flatten(self, mut make_delim: impl FnMut(C) -> (T, T)) -> Vec<T> {
        self.flatten_inner(&mut make_delim)
    }

    fn flatten_inner(self, make_delim: &mut impl FnMut(C) -> (T, T)) -> Vec<T> {
        match self {
            Containerized::Single(t) => vec![t],
            Containerized::Contained(c, v) => {
                let (left, right) = make_delim(c);
                let mut res = vec![left];
                res.append(
                    &mut v
                        .into_iter()
                        .flat_map(|c| c.flatten_inner(make_delim))
                        .collect(),
                );
                res.push(right);
                res
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn containerized() {
        let v = vec![b'(', 2, b')', 2, b')', b'(', 2];
        let (c, e) = containerize(v, |&t| {
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
                UnmatchedDelimeter(DelimeterSide::Right, 4, ()),
                UnmatchedDelimeter(DelimeterSide::Left, 5, ())
            ]
        );
    }

    #[test]
    fn spread_collect() {
        let c = Containerized::<(), _>::Single(vec![2, 3, 4]);
        let cs = c.clone().spread_single();
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
        c.visit(
            |x| {
                if let Containerized::Single(n) = *x {
                    sum += n
                }
            },
            false,
        );
        assert_eq!(sum, 3 + 4 + 5 + 6);
        let mut c2 = c.clone();
        c.visit_mut(
            |x| match x {
                Containerized::Single(n) => {
                    *n += 1;
                }
                Containerized::Contained(_, v) => {
                    v.push(Containerized::Single(1));
                }
            },
            false,
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
                        Containerized::Single(2),
                    ],
                ),
                Containerized::Single(7),
                Containerized::Single(2),
            ],
        );
        assert_eq!(c, ctrl);
        println!();
        c2.visit_mut(
            |x| match x {
                Containerized::Single(n) => {
                    *n += 1;
                }
                Containerized::Contained(_, v) => {
                    v.push(Containerized::Single(1));
                }
            },
            true,
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
        assert_eq!(c.map_single(|x| x + 1), Containerized::Single(4));
        let c = Containerized::<(), u8>::Contained(
            (),
            vec![Containerized::Single(2), Containerized::Single(3)],
        );
        let ctrl = Containerized::<(), u8>::Contained(
            (),
            vec![Containerized::Single(3), Containerized::Single(4)],
        );
        assert_eq!(c.map_single(|x| x + 1), ctrl);
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
            c.flatten(|_| (b'(', b')')),
            vec![b'(', b'(', b'(', b')', b'(', 3, b')', b')', 3, 4, b')']
        );
    }
}
