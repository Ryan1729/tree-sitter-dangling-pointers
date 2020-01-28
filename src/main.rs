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

impl InitializedParsers {
    fn get_spans(&mut self, to_parse: &str) -> Spans {
        use SpanKind::*;
   
        let SpanNodes {
            comment_nodes,
            string_nodes,
        } = {
            self.rust_tree = dbg!(self.rust.parse(to_parse, None));
    
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
        };
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

#[derive(Debug)]
struct SpanNodes<'tree> {
    comment_nodes: Vec<&'tree Node<'tree>>,
    string_nodes: Vec<&'tree Node<'tree>>,
}

fn plaintext_end_span_for(s: &str) -> SpanView {
    SpanView { kind: SpanKind::Plain, end_byte_index: s.len()}
}

extern "C" { fn tree_sitter_rust() -> Language; }

impl InitializedParsers {
    fn new() -> Self {
        let mut rust = Parser::new();
        let rust_lang = unsafe { tree_sitter_rust() };
        rust.set_language(
            rust_lang
        ).unwrap();

        let rust_tree: Option<Tree> = None;

        let rust_comment_query = Query::new(
            rust_lang,
            "(line_comment) @c1
            (block_comment) @c2"
        ).unwrap();

        let rust_string_query = Query::new(
            rust_lang,
            "(string_literal) @s"
        ).unwrap();

        InitializedParsers {
            rust,
            rust_tree,
            rust_comment_query,
            rust_string_query,
        }
    }
}

fn main() {
    let mut parsers = InitializedParsers::new();

    let del = "fn foo() {\n    let hi = \"hi\";\n    // TODO\n}\n\n";
    let code = "const ALL_BUT_SIGN_BIT: u32 = 0x7fff_ffff;\n\n\n\n/// Assumes x is one of the \"usual\" `f32`s, AKA not sub/denormal, Infinity or NaN.\n/// So norm
al numbers or 0. This does not imply that the output is a usual f32.\npub fn usual_f32_minimal_decrease(x: f32) -> f32 {\n    let non_sign_bits = x.to_bits() & ALL_BUT_SIGN_B
IT;\nif non_sign_bits == 0 {\n        -std::f32::MIN_POSITIVE\n} else {\n        let sign_bit = x.to_bits() & SIGN_BIT;\n        let sig
n = if sign_bit == 0 { 1\n        f32::from_bits(sign_bit)\n}\n}\n\npub fn is_normal_or_0(x: f32) -> bool {\
n    use std::num::FpCategory::{Normal, Zero};\n    let category = x.classify();\n    category == Zero || category == Normal\n}\n\n/// returns the next largest floating
 point number if the input is normal or 0\n/// and the ouput would be normal or 0. Otherwise, the input is returned.\npub fn next_largest_f32_if_normal_or_0(x: f32) -> f32 {\
r\n    if is_normal_or_0(x) {\n        let larger = usual_f32_minimal_increase(x);\n        if is_normal_or_0(larger) {\n            return larger;\n        }\n    }\
n    x\n}\n\n/// returns the next smallest floating point number if the input is normal or 0\n/// and the ouput would be normal or 0. Otherwise, the input is returned.\
npub fn next_smallest_f32_if_normal_or_0(x: f32) -> f32 {\nif is_normal_or_0(x) {\n        let smaller = usual_f32_minimal_decrease(x);\n        if is_normal_or_0(small
er) {\nreturn smaller;\n}\n}\nx\n}\n\n#[cfg(test)]\nmod floating_point_tests {\n    use super::*;\n    use crate::tests::arb;\n
   use proptest::proptest;\n    use std::f32::{MAX, MIN, MIN_POSITIVE};\n    use std::num::FpCategory::{Infinite, Normal, Zero};\n    // note, the following tests demostate
s that prop testing is not the same thing as testing every\n    // case!\n    proptest! {\n        #[test]\n        fn usual_f32_minimal_increase_outputs_usual_f32s(\n
           x in arb::usual(),\n        ) {\n            let category = usual_f32_minimal_increase(x).classify();\n            assert!(\n                category == Zero |
| category == Normal,\n                \"category was {:?}, not Zero or Normal\",\n                category\n            );\n        }\n    }\n    proptest! {\n
    #[test]\n        fn usual_f32_minimal_decrease_outputs_usual_f32s(\n            x in arb::usual(),\n        ) {\n            let category = usual_f32_minimal_decrease
(x).classify();\n            assert!(\n                category == Zero || category == Normal,\n                \"category was {:?}, not Zero or Normal\",\n
  category\n);\n}\n}\nproptest! {\n#[test]\nfn usual_f32_minimal_increase_increases(\nold in arb::usual(),\n) {}}\nproptest!{}\n}";

    dbg!(code.len());

    for _ in 0..10 {
        dbg!(parsers.get_spans(&code));
    }
}