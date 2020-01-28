use tree_sitter::{Parser, Language, Node, Query, QueryCursor, Tree};

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

extern "C" { fn tree_sitter_rust() -> Language; }

fn main() {
    let to_parse = "
        #[cfg(test)]\n
        mod floating_point_tests {\n
        use std::f32::{MAX, MIN, MIN_POSITIVE};\n
        // note, the following tests\n
        \"category was {:?}, not Zero or Normal\"
    ";

    let mut rust = Parser::new();
    let rust_lang = unsafe { tree_sitter_rust() };
    rust.set_language(
        rust_lang
    ).unwrap();

    let mut rust_tree: Option<Tree> = None;

    let rust_comment_query = Query::new(
        rust_lang,
        "(line_comment) @c1
        (block_comment) @c2"
    ).unwrap();

    let rust_string_query = Query::new(
        rust_lang,
        "(string_literal) @s"
    ).unwrap();

    let text_callback = |n: Node| {
        let r = n.range();
        &to_parse[r.start_byte..r.end_byte]
    };

    for _ in 0..20 {
        use SpanKind::*;
   
        rust_tree = rust.parse(to_parse, rust_tree.as_ref());

        let mut comment_nodes = Vec::new();

        let mut string_nodes = Vec::new();
        
        if let Some(r_t) = rust_tree.as_ref() {
            // Move this into the outer scope to make the assertion be true
            let mut query_cursor = QueryCursor::new();

            comment_nodes = query_cursor.matches(
                &rust_comment_query,
                r_t.root_node(),
                text_callback,
            ).flat_map(|q_match| 
                q_match.captures.iter().map(|q_capture| &q_capture.node)
            ).collect();

            string_nodes = query_cursor.matches(
                &rust_string_query,
                r_t.root_node(),
                text_callback,
            ).flat_map(|q_match| {
                q_match.captures.iter().map(|q_capture| &q_capture.node)
            }).collect();
        }

        let mut comment_nodes = comment_nodes.iter();
        let mut string_nodes = string_nodes.iter();

        let mut spans = Vec::new();

        let mut comment = comment_nodes.next();
        let mut string = string_nodes.next();
        let mut previous_end_byte_index = 0;
        loop {
            let (node, kind) = {
                macro_rules! handle_previous_chunk {
                    ($node: ident) => {
                        let start = $node.start_byte();
                        let extra = start.saturating_sub(previous_end_byte_index);
                        if extra > 0 {
                            previous_end_byte_index = start;
                            spans.push(SpanView {
                                kind: SpanKind::Plain,
                                end_byte_index: previous_end_byte_index,
                            });
                        }   
                    }
                }
                match (comment, string) {
                    (Some(c), Some(s)) => {
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

            previous_end_byte_index = node.end_byte();
            spans.push(SpanView {
                kind,
                end_byte_index: previous_end_byte_index,
            });
        }

        if previous_end_byte_index < to_parse.len() {
            spans.push(SpanView { kind: SpanKind::Plain, end_byte_index: to_parse.len()});
        }

        for s in spans {
            assert!(s.end_byte_index <= to_parse.len(), "{} > {}", s.end_byte_index, to_parse.len());
        }
    }
}