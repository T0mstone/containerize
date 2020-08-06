# Containerize
`containerize` is a library that provides tooling around a single type: `Containerized`.

This type represents streams of data that can have sections of linear data (`Containerized::Single`)
and different kinds of recursive blocks each containing more of the same type of data streams.

## Use Cases
`containerize` was designed for a parser, to act as an intermediate between a token stream and an AST
(The blocks here are parenthesized expressions, such as `a(b)c`, which could be stored as
`[Single("a"), Contained(Round, [Single("b")]), Single("c")]`)

If you find other use-cases, feel free to let me know, and they can be added to this list.

## Example
```rust
/// use containerize::{Containerized::{self, Single, Contained}, DelimeterSide, containerize};
use self::ContainerType::*;
///
#[derive(Debug, PartialEq)]
pub enum ContainerType {
    Round,
    Spiky
}
///
fn main() {
    let s = "a<b>c(d<e<f>(g)>h)";
    let v: Vec<Containerized<ContainerType, Vec<char>>> = containerize(s.chars(), |&c: &char| -> Option<(DelimeterSide, ContainerType)> {
        match c {
            '<' => Some((DelimeterSide::Left, Spiky)),
            '>' => Some((DelimeterSide::Right, Spiky)),
            '(' => Some((DelimeterSide::Left, Round)),
            ')' => Some((DelimeterSide::Right, Round)),
            _ => None
        }
    }).unwrap();
    let v: Vec<Containerized<ContainerType, String>> = v.into_iter().map(|c| c.map(|v| v.into_iter().collect())).collect();
    assert_eq!(v, vec![
        Single("a".to_string()),
        Contained(Spiky, vec![Single("b".to_string())]),
        Single("c".to_string()),
        Contained(Round, vec![
            Single("d".to_string()),
            Contained(Spiky, vec![
                Single("e".to_string()),
                Contained(Spiky, vec![Single("f".to_string())]),
                Contained(Round, vec![Single("g".to_string())]),
            ]),
            Single("h".to_string())
        ])
    ]);
}
```

Note that `containerize` returns a [`BiResult`](https://github.com/T0mstone/tlibs/tree/master/bi_result), not a `Result`