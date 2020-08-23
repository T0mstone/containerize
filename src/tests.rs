use crate::visit::*;
use crate::*;

#[test]
fn r#macro() {
    let v = containerized_vec![() => [1u8, 2, 3], 4, () => [() => [() => [5]]]];
    let ctrl = vec![
        Containerized::contained(
            (),
            vec![
                Containerized::Single(1u8),
                Containerized::Single(2),
                Containerized::Single(3),
            ],
        ),
        Containerized::Single(4),
        Containerized::contained(
            (),
            vec![Containerized::contained(
                (),
                vec![Containerized::contained((), vec![Containerized::Single(5)])],
            )],
        ),
    ];
    assert_eq!(v.0, ctrl);
}

#[test]
fn containerized() {
    let v = vec![b'(', 2, b')', 2, b')', b'(', 2];
    let mut e = Vec::new();
    let c = containerize(
        v,
        |&t| {
            if t == b'(' {
                Some((DelimeterSide::Left, ()))
            } else if t == b')' {
                Some((DelimeterSide::Right, ()))
            } else {
                None
            }
        },
        &mut e,
    );
    assert_eq!(
        c.0,
        vec![
            Containerized::contained((), vec![Containerized::Single(vec![2])]),
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
    let c = Containerized::<(), Vec<u8>>::Single(vec![2, 3, 4]);
    let cs = c.clone().spread_single::<ContainerizedVec<(), u8>>();
    assert_eq!(
        cs.0,
        vec![
            Containerized::Single(2),
            Containerized::Single(3),
            Containerized::Single(4)
        ]
    );
    assert_eq!(cs.collapse_single().0, vec![c]);
}

#[test]
fn visit() {
    let mut c = containerized![() => [3, () => [4, 5], 6]];
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
    let ctrl = containerized!(() => [4, () => [5, 6, 2], 7, 2]);
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
    let ctrl = containerized!(() => [4, () => [5, 6, 1], 7, 1]);
    assert_eq!(c2, ctrl);
}

#[test]
fn map() {
    let c = Containerized::<(), u8>::Single(3);
    assert_eq!(c.map(|x| x + 1), Containerized::Single(4));
    let c = Containerized::<(), u8>::contained(
        (),
        vec![Containerized::Single(2), Containerized::Single(3)],
    );
    let ctrl = Containerized::<(), u8>::contained(
        (),
        vec![Containerized::Single(3), Containerized::Single(4)],
    );
    assert_eq!(c.map(|x| x + 1), ctrl);
    let c = Containerized::<u8, u8>::contained(
        1,
        vec![Containerized::Single(2), Containerized::Single(3)],
    );
    let ctrl = Containerized::<u8, u8>::contained(
        2,
        vec![Containerized::Single(2), Containerized::Single(3)],
    );
    assert_eq!(c.map_kind(|x| x + 1), ctrl);
}

#[test]
fn join() {
    let c = containerized!(() => [() => [() => [], () => [b'3']], b'3', b'4']);
    assert_eq!(
        c.uncontainerize(|_| (b'(', b')')),
        b"((()(3))34)".to_vec(),
        // vec![b'(', b'(', b'(', b')', b'(', 3, b')', b')', 3, 4, b')']
    );
}

#[test]
fn filter_map() {
    let c = containerized_vec![() => [() => [Some('a'), None], None], None, Some('b')];
    let ctrl = containerized_vec![() => [() => ['a']], 'b'];
    assert_eq!(c.filter_map(|opt| opt), ctrl);
}
