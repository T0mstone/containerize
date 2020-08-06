//! Functionality related to visiting a `Containerized` structure
//!
//! ("visiting" is jargon for applying a function to every node, i.e. the top value, all its children, all their children, etc.)
//!
//! # Order
//! When traversing the structure, the function is either applied to the node (parent) before (preorder) or after (postorder) its children
//!
//! # Depth-/Breadth-first traversal
//! Say we have the following structure
//! ```ignore
//!     A
//!    /|\
//!   B C D
//!  / \   \
//! E   F   G
//! ```
//! Using depth-first traversal, all children are handled before moving on to the next node, in our example (using preorder):
//! ```ignore
//! A, B, E, F, C, D, G
//! ```
//! Using breadth-first traversal, all nodes on one level are handled after each other, and _then_ their children, in our example (also using preorder):
//! ```ignores
//! A, B, C, D, E, F, G
//! ```

use crate::*;

mod private {
    pub trait Sealed {}

    impl Sealed for super::PreOrder {}
    impl Sealed for super::PostOrder {}
}

/// The order in which to visit
///
/// This is a trait in order to work similar to the [typestate](http://cliffle.com/blog/rust-typestate/) pattern;
/// It enables monomorphising the functions and thus eliminates a lot of runtime checks for the order
pub trait VisitOrder: self::private::Sealed {
    /// If the function is applied to the parent before its children
    const PARENT_FIRST: bool;
}
impl VisitOrder for PreOrder {
    const PARENT_FIRST: bool = true;
}
impl VisitOrder for PostOrder {
    const PARENT_FIRST: bool = false;
}

/// Pre-Order means applying the function to the parent, and then to its children
pub enum PreOrder {}
#[allow(missing_docs)]
pub type ParentFirst = PreOrder;
#[allow(missing_docs)]
pub type ChildrenLast = PreOrder;
/// Post-Order means applying the function to the children before their parent
pub enum PostOrder {}
#[allow(missing_docs)]
pub type ParentLast = PostOrder;
#[allow(missing_docs)]
pub type ChildrenFirst = PostOrder;

#[allow(missing_docs)]
/// See the [module level documentation](/)
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TraversalStrategy {
    DepthFirst,
    BreadthFirst,
}

#[allow(missing_docs)]
/// A runtime value corresponding to [`VisitOrder`](trait.VisitOrder.html)
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TraversalOrder {
    PreOrder,
    PostOrder,
}

#[allow(missing_docs)]
#[allow(non_upper_case_globals)]
impl TraversalOrder {
    pub const ParentFirst: Self = Self::PreOrder;
    pub const ChildrenLast: Self = Self::PreOrder;
    pub const ParentLast: Self = Self::PostOrder;
    pub const ChildrenFirst: Self = Self::PostOrder;
}

/// A config structure that stores all info about the details of the `visit` algorithm in one place
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[allow(missing_docs)]
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
    /// Visit `self` and all children with the specified config
    #[inline]
    pub fn visit_with_config<F: FnMut(&mut Self)>(&mut self, f: F, config: VisitConfig) {
        config.exec(f, self)
    }

    /// Visit `self` and all children with the default config (depth-first, preorder)
    #[inline]
    pub fn visit<F: FnMut(&mut Self)>(&mut self, f: F) {
        self.visit_with_config(f, VisitConfig::default())
    }
}
