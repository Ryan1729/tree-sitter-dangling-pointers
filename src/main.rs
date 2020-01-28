use tree_sitter::{Parser, Language, LanguageError, Node, Query, QueryCursor, QueryError, Tree};

#[derive(Clone, Debug)]
pub enum SpanKind {
    Plain,
    Comment,
    String,
}

#[derive(Clone, Debug)]
pub struct SpanView {
    pub end_byte_index: usize,
    pub kind: SpanKind,
}

#[derive(Clone, Copy, Debug)]
pub enum ParserKind {
    Plaintext,
    Rust
}

#[derive(Debug)]
pub enum Parsers {
    NotInitializedYet,
    Initialized(InitializedParsers),
    FailedToInitialize(InitializationError)
}

pub struct InitializationError(String);
impl std::fmt::Debug for InitializationError {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        let InitializationError(e) = self;
        write!(fmt, "{:?}", e)
    }
}

impl From<LanguageError> for InitializationError {
    fn from(error: LanguageError) -> Self {
        dbg!(&error);
        InitializationError(format!("{:?}", error))
    }
}

impl From<QueryError> for InitializationError {
    fn from(error: QueryError) -> Self {
        dbg!(&error);
        InitializationError(format!("{:?}", error))
    }
}

pub struct InitializedParsers {
    rust: Parser,
    rust_tree: Option<Tree>,
    rust_comment_query: Query,
    rust_string_query: Query,
}
impl std::fmt::Debug for InitializedParsers {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        fmt.debug_struct("InitializedParsers")
           .field("rust", &("TODO rust: Parser Debug".to_string()))
           .field("rust_tree", &self.rust_tree)
           .field("rust_comment_query", &self.rust_comment_query)
           .field("rust_string_query", &self.rust_string_query)
           .finish()
    }
}

type Spans = Vec<SpanView>;

/// How many times more common plain nodes are than the other typs of nodes.
const PLAIN_NODES_RATIO: usize = 4;

impl Parsers {
    pub fn get_spans(&mut self, to_parse: &str, kind: ParserKind) -> Spans {
        use Parsers::*;
        self.attempt_init();

        match self {
            Initialized(p) => p.get_spans(to_parse, kind),
            NotInitializedYet | FailedToInitialize(_) => {
                plaintext_spans_for(to_parse)
            }
        }
    }
}
impl InitializedParsers {
    fn get_spans(&mut self, to_parse: &str, kind: ParserKind) -> Spans {
        use ParserKind::*;
        use SpanKind::*;

        match kind {
            Plaintext => {
                plaintext_spans_for(to_parse)
            }
            Rust => {
                let SpanNodes {
                    comment_nodes,
                    string_nodes,
                } = self.get_span_nodes(to_parse);
                dbg!("SpanNodes");
                let mut comment_nodes = comment_nodes.iter();
                let mut string_nodes = string_nodes.iter();


                let mut spans = Vec::with_capacity(
                    (comment_nodes.len() + string_nodes.len())
                    * (PLAIN_NODES_RATIO + 1)
                );

                let mut comment = comment_nodes.next();
                let mut string = string_nodes.next();
                let mut previous_end_byte_index = 0;
                loop {
                    if let Some(s) = string.as_ref() {
                        dbg!("before s.kind_id()");
                        s.kind_id();
                        dbg!("after s.kind_id()");
                        println!("{{Node {} {} - {}}}", s.kind(), s.kind(), s.kind());
                        dbg!(s);
                    }
                    
                    //dbg!(&string, &comment);
                    let (node, kind) = {
                        macro_rules! handle_previous_chunk {
                            ($node: ident) => {
                                let start = $node.start_byte();
                                let extra = start.saturating_sub(previous_end_byte_index);
                                if extra > 0 {
                                    spans.push(SpanView {
                                        kind: SpanKind::Plain,
                                        end_byte_index: start,
                                    });
                                    previous_end_byte_index = start;
                                }   
                            }
                        }
                        match (comment, string) {
                            (Some(c), Some(s)) => {
                                // TODO reformulate to make adding in the minimum of n node types easier.
                                if c.start_byte() < s.start_byte() {
                                    handle_previous_chunk!(c);

                                    comment = comment_nodes.next();

                                    (c, Comment)
                                } else {
                                    handle_previous_chunk!(s);
                                    
                                    string = string_nodes.next();
                                    
                                    (s, String)
                                }
                            }
                            (Some(c), None) => {
                                comment = comment_nodes.next();

                                (c, Comment)
                            }
                            (None, Some(s)) => {
                                string = string_nodes.next();

                                (s, String)
                            }
                            (None, None) => break,
                        }
                    };

                    // this is briefly the current index
                    previous_end_byte_index = node.end_byte();
                    spans.push(SpanView {
                        kind,
                        end_byte_index: previous_end_byte_index,
                    });
                }

                if previous_end_byte_index < to_parse.len() {
                    spans.push(plaintext_end_span_for(to_parse));
                }

                spans
            }
        }
    }
}

#[derive(Debug)]
struct SpanNodes<'tree> {
    comment_nodes: Vec<&'tree Node<'tree>>,
    string_nodes: Vec<&'tree Node<'tree>>,
}

impl InitializedParsers {
    fn get_span_nodes<'to_parse>(&'to_parse mut self, to_parse: &'to_parse str) -> SpanNodes<'to_parse> {
        dbg!({
            let sub: String = to_parse.chars().take(60).collect();
            sub
        });
        self.rust_tree = dbg!(self.rust.parse(to_parse, self.rust_tree.as_ref()));

        let mut comment_nodes = Vec::new();

        let mut string_nodes = Vec::new();

        if let Some(r_t) = &self.rust_tree {
            let text_callback = move |n: Node| {
                let r = n.range();
                &to_parse[r.start_byte..r.end_byte]
            };

            let mut query_cursor = QueryCursor::new();

            let (_, _): (Vec<_>, Vec<_>) = dbg!(
                query_cursor.matches(
                    &self.rust_comment_query,
                    r_t.root_node(),
                    text_callback,
                ).map(|m: tree_sitter::QueryMatch| m.pattern_index).collect(),
                query_cursor.matches(
                    &self.rust_string_query,
                    r_t.root_node(),
                    text_callback,
                ).map(|m: tree_sitter::QueryMatch| m.pattern_index).collect(),
            );

            comment_nodes = query_cursor.matches(
                &self.rust_comment_query,
                r_t.root_node(),
                text_callback,
            ).flat_map(|q_match| 
                q_match.captures.iter().map(|q_capture| &q_capture.node)
            ).collect();

            string_nodes = query_cursor.matches(
                &self.rust_string_query,
                r_t.root_node(),
                text_callback,
            ).flat_map(|q_match| {
                dbg!(q_match.pattern_index);
                q_match.captures.iter().map(|q_capture| &q_capture.node)
            }).collect();

            dbg!(&string_nodes);
        }
        dbg!(&string_nodes);
        SpanNodes {
            comment_nodes,
            string_nodes,
        }
    }
}

fn plaintext_spans_for(s: &str) -> Spans {
    vec![plaintext_end_span_for(s)]
}

fn plaintext_end_span_for(s: &str) -> SpanView {
    SpanView { kind: SpanKind::Plain, end_byte_index: s.len()}
}

extern "C" { fn tree_sitter_rust() -> Language; }

impl Parsers {
    fn attempt_init(&mut self) {
        use Parsers::*;
        match self {
            NotInitializedYet => {
                match InitializedParsers::new() {
                    Ok(p) => { *self = Initialized(p); }
                    Err(e) => { *self = FailedToInitialize(e); }
                }
            },
            Initialized(_) | FailedToInitialize(_) => {}
        }
    }
}

impl InitializedParsers {
    fn new() -> Result<Self, InitializationError> {
        let mut rust = Parser::new();
        let rust_lang = unsafe { tree_sitter_rust() };
        rust.set_language(
            rust_lang
        )?;

        let rust_tree: Option<Tree> = None;

        let rust_comment_query = Query::new(
            rust_lang,
            "(line_comment) @c1
            (block_comment) @c2"
        )?;

        let rust_string_query = Query::new(
            rust_lang,
            "(string_literal) @s"
        )?;

        Ok(InitializedParsers {
            rust,
            rust_tree,
            rust_comment_query,
            rust_string_query,
        })
    }
}

fn main() {
    let mut parsers = Parsers::NotInitializedYet;

    let code = "fn main() {\n    let hi = \"hi\";\n    // TODO\n}\n\nconst SIGN_BIT: u32 = 0x8000_0000;\nconst ALL_BUT_SIGN_BIT: u32
 = 0x7fff_ffff;\n\n/// Assumes x is one of the \"usual\" `f32`s, AKA not sub/denormal, Infinity or NaN.\n/// So normal numbers or 0. This does not imply that the output is
a usual f32.\npub fn usual_f32_minimal_increase(x: f32) -> f32 {\n    let non_sign_bits = x.to_bits() & ALL_BUT_SIGN_BIT;\n    // if is 0 or -0\n    if non_sign_bits == 0
 {\n        std::f32::MIN_POSITIVE\n    } else {\n        let sign_bit = x.to_bits() & SIGN_BIT;\n        let sign = if sign_bit == 0 { 1 } else { -1 };\n        f32::f
rom_bits(sign_bit | (non_sign_bits as i32 + sign) as u32)\n    }\n}\n\n/// Assumes x is one of the \"usual\" `f32`s, AKA not sub/denormal, Infinity or NaN.\n/// So norm
al numbers or 0. This does not imply that the output is a usual f32.\npub fn usual_f32_minimal_decrease(x: f32) -> f32 {\n    let non_sign_bits = x.to_bits() & ALL_BUT_SIGN_B
IT;\n    // if is 0 or -0\n    if non_sign_bits == 0 {\n        -std::f32::MIN_POSITIVE\n    } else {\n        let sign_bit = x.to_bits() & SIGN_BIT;\n        let sig
n = if sign_bit == 0 { 1 } else { -1 };\n        f32::from_bits(sign_bit | (non_sign_bits as i32 - sign) as u32)\n    }\n}\n\npub fn is_normal_or_0(x: f32) -> bool {\
n    use std::num::FpCategory::{Normal, Zero};\n    let category = x.classify();\n    category == Zero || category == Normal\n}\n\n/// returns the next largest floating
 point number if the input is normal or 0\n/// and the ouput would be normal or 0. Otherwise, the input is returned.\npub fn next_largest_f32_if_normal_or_0(x: f32) -> f32 {\
r\n    if is_normal_or_0(x) {\n        let larger = usual_f32_minimal_increase(x);\n        if is_normal_or_0(larger) {\n            return larger;\n        }\n    }\
n    x\n}\n\n/// returns the next smallest floating point number if the input is normal or 0\n/// and the ouput would be normal or 0. Otherwise, the input is returned.\
npub fn next_smallest_f32_if_normal_or_0(x: f32) -> f32 {\n    if is_normal_or_0(x) {\n        let smaller = usual_f32_minimal_decrease(x);\n        if is_normal_or_0(small
er) {\n            return smaller;\n        }\n    }\n    x\n}\n\n#[cfg(test)]\nmod floating_point_tests {\n    use super::*;\n    use crate::tests::arb;\n
   use proptest::proptest;\n    use std::f32::{MAX, MIN, MIN_POSITIVE};\n    use std::num::FpCategory::{Infinite, Normal, Zero};\n    // note, the following tests demostate
s that prop testing is not the same thing as testing every\n    // case!\n    proptest! {\n        #[test]\n        fn usual_f32_minimal_increase_outputs_usual_f32s(\n
           x in arb::usual(),\n        ) {\n            let category = usual_f32_minimal_increase(x).classify();\n            assert!(\n                category == Zero |
| category == Normal,\n                \"category was {:?}, not Zero or Normal\",\n                category\n            );\n        }\n    }\n    proptest! {\n
    #[test]\n        fn usual_f32_minimal_decrease_outputs_usual_f32s(\n            x in arb::usual(),\n        ) {\n            let category = usual_f32_minimal_decrease
(x).classify();\n            assert!(\n                category == Zero || category == Normal,\n                \"category was {:?}, not Zero or Normal\",\n
  category\n            );\n        }\n    }\n    proptest! {\n        #[test]\n        fn usual_f32_minimal_increase_increases(\n            old in arb::usual(),
\n        ) {\n            let new = usual_f32_minimal_increase(old);\n            assert!(\n                new > old,\n                \"{:?} <= {:?}\\n{:b} <= {:b}\",\
r\n                new,\n                old,\n                new.to_bits(),\n                old.to_bits()\n            );\n        }\n    }\n    proptest! {\n
       #[test]\n        fn usual_f32_minimal_decrease_decreases(\n            old in arb::usual(),\n        ) {\n            let new = usual_f32_minimal_decrease(old);\
n            assert!(\n                new < old,\n                \"{:?} >= {:?}\\n{:b} >= {:b}\",\n                new,\n                old,\n                new.to_
bits(),\n                old.to_bits()\n            );\n        }\n    }\n    #[test]\n    fn how_usual_f32_minimal_decrease_works_at_the_edge() {\n        // preco
ndition\n        assert_eq!(Normal, MIN.classify());\n        let category = usual_f32_minimal_decrease(MIN).classify();\n        assert_eq!(Infinite, category);\n    }
\n    #[test]\n    fn how_usual_f32_minimal_increase_works_at_the_edge() {\n        // precondition\n        assert_eq!(Normal, MAX.classify());\n        let category = u
sual_f32_minimal_increase(MAX).classify();\n        assert_eq!(Infinite, category);\n    }\n\n    #[test]\n    fn how_usual_f32_minimal_decrease_works_around_zero() {
\n        assert_eq!(usual_f32_minimal_decrease(0.0), -MIN_POSITIVE);\n    }\n    #[test]\n    fn how_usual_f32_minimal_increase_works_around_zero() {\n        assert_eq!
(usual_f32_minimal_increase(0.0), MIN_POSITIVE);\n    }\n}\n";

    dbg!(parsers.get_spans(code, ParserKind::Rust));
}