use crate::*;

mod private {
    pub trait Sealed {}

    impl Sealed for super::PreOrder {}
    impl Sealed for super::PostOrder {}
}

pub trait VisitOrder: self::private::Sealed {
    const PARENT_FIRST: bool;
}
impl VisitOrder for PreOrder {
    const PARENT_FIRST: bool = true;
}
impl VisitOrder for PostOrder {
    const PARENT_FIRST: bool = false;
}

pub enum PreOrder {}
pub type ParentFirst = PreOrder;
pub type ChildrenLast = PreOrder;
pub enum PostOrder {}
pub type ParentLast = PostOrder;
pub type ChildrenFirst = PostOrder;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TraversalStrategy {
    DepthFirst,
    BreadthFirst,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TraversalOrder {
    PreOrder,
    PostOrder,
}

#[allow(non_upper_case_globals)]
impl TraversalOrder {
    pub const ParentFirst: Self = Self::PreOrder;
    pub const ChildrenLast: Self = Self::PreOrder;
    pub const ParentLast: Self = Self::PostOrder;
    pub const ChildrenFirst: Self = Self::PostOrder;
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct VisitConfig {
    // todo: add a field to determine iterative/recursive
    pub order: TraversalOrder,
    pub strategy: TraversalStrategy,
}

impl Default for VisitConfig {
    fn default() -> Self {
        VisitConfig {
            order: TraversalOrder::PreOrder,
            strategy: TraversalStrategy::DepthFirst,
        }
    }
}

impl VisitConfig {
    #[inline]
    fn exec<C, T, F: FnMut(&mut Containerized<C, T>)>(self, f: F, x: &mut Containerized<C, T>) {
        match self.order {
            TraversalOrder::PreOrder => {
                let mut visitor = RecursiveVisitor::<C, T, F, PreOrder>(f, PhantomData);

                match self.strategy {
                    TraversalStrategy::DepthFirst => visitor.visit_dfs(x),
                    TraversalStrategy::BreadthFirst => visitor.visit_bfs(x),
                }
            }
            TraversalOrder::PostOrder => {
                let mut visitor = RecursiveVisitor::<C, T, F, PostOrder>(f, PhantomData);

                match self.strategy {
                    TraversalStrategy::DepthFirst => visitor.visit_dfs(x),
                    TraversalStrategy::BreadthFirst => visitor.visit_bfs(x),
                }
            }
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct RecursiveVisitor<C, T, F: FnMut(&mut Containerized<C, T>), O: VisitOrder>(
    F,
    PhantomData<(C, T, O)>,
);

impl<C, T, F: FnMut(&mut Containerized<C, T>), O: VisitOrder> RecursiveVisitor<C, T, F, O> {
    pub fn visit_dfs(&mut self, x: &mut Containerized<C, T>) {
        if O::PARENT_FIRST {
            (self.0)(x);
            for c in x.children_mut() {
                self.visit_dfs(c);
            }
        } else {
            for c in x.children_mut() {
                self.visit_dfs(c);
            }
            (self.0)(x);
        }
    }

    fn visit_bfs_inner(&mut self, x: &mut Containerized<C, T>) {
        if O::PARENT_FIRST {
            for c in x.children_mut() {
                (self.0)(c);
            }
            for c in x.children_mut() {
                self.visit_bfs_inner(c);
            }
        } else {
            for c in x.children_mut() {
                self.visit_bfs_inner(c);
            }
            for c in x.children_mut() {
                (self.0)(c);
            }
        }
    }

    pub fn visit_bfs(&mut self, x: &mut Containerized<C, T>) {
        if O::PARENT_FIRST {
            (self.0)(x);
            self.visit_bfs_inner(x);
        } else {
            self.visit_bfs_inner(x);
            (self.0)(x);
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct IterativeVisitor<C, T, F: FnMut(&mut Containerized<C, T>), O: VisitOrder> {
    f: F,
    stack: Vec<Containerized<C, T>>,
    _marker: PhantomData<O>,
}

impl<C, T, F: FnMut(&mut Containerized<C, T>), O: VisitOrder> IterativeVisitor<C, T, F, O> {
    // TODO
}

impl<C, T> Containerized<C, T> {
    #[inline]
    pub fn visit_with_config<F: FnMut(&mut Self)>(&mut self, f: F, config: VisitConfig) {
        config.exec(f, self)
    }

    #[inline]
    pub fn visit<F: FnMut(&mut Self)>(&mut self, f: F) {
        self.visit_with_config(f, VisitConfig::default())
    }

    //
    //
    // /// works like [visit] but passes `self` mutably, allowing the function to mutate `self`
    // #[inline]
    // pub fn visit_mut(&mut self, mut f: impl FnMut(&mut Self), reverse: bool) {
    //     // implementation: stack of stacks
    //     //      stack[_]: (?, sub_stack)
    //     //
    //     //      the top-most sub-stack gets handled first
    //     let mut stack = vec![(0, vec![])];
    //
    //     if !reverse {
    //         f(self);
    //     }
    //     match self {
    //         Containerized::Single(_) => {
    //             if reverse {
    //                 f(self);
    //             }
    //             return;
    //         }
    //         Containerized::Contained(_, v) => {
    //             let vt = std::mem::take(v);
    //             stack.push((0, vt));
    //         }
    //     }
    //
    //     loop {
    //         let (i, last) = stack.last_mut().unwrap();
    //         match last.get_mut(*i) {
    //             Some(cont) => {
    //                 if !reverse {
    //                     f(cont);
    //                 }
    //                 match cont {
    //                     Containerized::Single(_) => {
    //                         if reverse {
    //                             f(cont)
    //                         }
    //                     }
    //                     Containerized::Contained(_, v) => {
    //                         let vt = std::mem::take(v);
    //                         stack.push((0, vt));
    //                     }
    //                 }
    //             }
    //             None => {
    //                 let (_, last) = stack.pop().unwrap();
    //                 let curr = match stack.last_mut() {
    //                     Some((ix, sup)) => &mut sup[*ix],
    //                     None => self,
    //                 };
    //                 match curr {
    //                     Containerized::Single(_) => unreachable!(),
    //                     Containerized::Contained(_, v) => *v = last,
    //                 }
    //                 if reverse {
    //                     f(curr);
    //                 }
    //                 if stack.is_empty() {
    //                     break;
    //                 }
    //             }
    //         }
    //     }
    // }
    //
    // // #[inline]
    // // fn visit_mut_reverse(&mut self, mut f: impl FnMut(&mut Self)) {
    // //     #[derive(Copy, Clone)]
    // //     enum Action {
    // //         Visit,
    // //         Call,
    // //     }
    // //
    // //     let mut to_visit = std::iter::once((Action::Visit, self)).collect::<VecDeque<_>>();
    // //     while let Some((act, cont)) = to_visit.pop_front() {
    // //         if let Action::Call = act {
    // //             f(cont);
    // //             continue;
    // //         }
    // //
    // //         match cont {
    // //             Containerized::Contained(_, v) => {
    // //                 to_visit.extend(v.into_iter().map(|c| (Action::Visit, c)));
    // //                 to_visit.push_back((Action::Call, cont));
    // //             }
    // //             Containerized::Single(_) => f(cont),
    // //         }
    // //     }
    // // }
    // //
    // // #[inline]
    // // fn visit_mut_noreverse(&mut self, mut f: impl FnMut(&mut Self)) {
    // //     #[derive(Copy, Clone)]
    // //     enum Action {
    // //         Visit,
    // //         Call,
    // //     }
    // //
    // //     let mut to_visit = std::iter::once((Action::Visit, self)).collect::<VecDeque<_>>();
    // //     while let Some((act, cont)) = to_visit.pop_front() {
    // //         if let Action::Call = act {
    // //             f(cont);
    // //             continue;
    // //         }
    // //
    // //         f(cont);
    // //         if let Containerized::Contained(_, v) = cont {
    // //             to_visit.extend(v.into_iter().map(|c| (Action::Visit, c)));
    // //         }
    // //     }
    // // }
    //
    // // fn visit_mut_inner(&mut self, f: &mut impl FnMut(&mut Self), reverse: bool) {
    // //     if !reverse {
    // //         f(self);
    // //     }
    // //     match self {
    // //         Containerized::Single(_) => (),
    // //         Containerized::Contained(_, v) => {
    // //             for e in v {
    // //                 e.visit_mut_inner(f, reverse)
    // //             }
    // //         }
    // //     }
    // //     if reverse {
    // //         f(self);
    // //     }
    // // }
    //
    // /// Call a function with every recursive leaf of the tree
    // ///
    // /// When `reverse` is `false`, the function is called on parents before their children (breadth-first traversal).
    // /// When it is `true`, the opposite is the case (depth-first traversal).
    // #[inline]
    // pub fn visit(&self, mut f: impl FnMut(&Self), reverse: bool) {
    //     let mut to_visit = vec_deque![(false, self)];
    //     while let Some((only_call, cont)) = to_visit.pop_front() {
    //         if only_call {
    //             f(cont);
    //             continue;
    //         }
    //
    //         match cont {
    //             Containerized::Contained(_, ref v) => {
    //                 to_visit.extend(v.iter().map(|c| (false, c)));
    //                 if reverse {
    //                     to_visit.push_back((true, cont));
    //                 } else {
    //                     f(cont);
    //                 }
    //             }
    //             Containerized::Single(_) => f(cont),
    //         }
    //     }
    // }
}
