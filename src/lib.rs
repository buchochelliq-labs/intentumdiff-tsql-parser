//! T-SQL parser plugin, full-parse mode.
//!
//! This compact dialect parser handles query/procedure level structure without
//! requiring a host tree-sitter package.

use intentumdiff_plugin_sdk::tree::{SemanticNode, SemanticNodeBuilder};

wit_bindgen::generate!({
    path: "wit/plugin.wit",
    world: "parser-plugin",
});

use crate::exports::intentdiff::plugin::parser::ExamplePair;
use crate::exports::intentdiff::plugin::parser::Guest;
use crate::exports::intentdiff::plugin::parser::LanguageInfoRecord;
use crate::exports::intentdiff::plugin::parser::ParserMode;

const PLUGIN_METADATA: &str = include_str!("../plugin_metadata.info");

fn language_info_for(ids: Vec<String>) -> Vec<LanguageInfoRecord> {
    let metadata = intentumdiff_plugin_sdk::metadata::parse_plugin_metadata(PLUGIN_METADATA);
    ids.into_iter()
        .map(|language_id| {
            let info = metadata.language_or_default(&language_id);
            LanguageInfoRecord {
                language_id: info.language_id,
                language_name: info.language_name,
                language_short_name: info.language_short_name,
                monaco_language: info.monaco_language,
                default_filename: info.default_filename,
                language_file_extensions: info.language_file_extensions,
                author: metadata.author().to_string(),
                plugin_version: metadata.plugin_version().to_string(),
                last_updated: metadata.last_updated().to_string(),
            }
        })
        .collect()
}

struct TsqlParser;

#[derive(Debug, Clone)]
struct SourceLine {
    number: u32,
    text: String,
    /// Normalised code: comments removed, layout whitespace outside string
    /// literals and quoted identifiers collapsed, trailing `;` dropped.
    trimmed: String,
    /// The line begins inside a literal/quoted identifier opened on an
    /// earlier line, so even an empty `trimmed` is literal content.
    starts_in_quote: bool,
    /// The line ends inside a literal/quoted identifier, so the line break
    /// after it is literal content.
    ends_in_quote: bool,
}

impl SourceLine {
    /// True when the line carries neither code nor literal content.
    fn is_blank(&self) -> bool {
        self.trimmed.is_empty() && !self.starts_in_quote
    }

    /// True for a `GO` batch separator line (not a `GO` inside a literal).
    fn is_batch_separator(&self) -> bool {
        !self.starts_in_quote && self.trimmed.eq_ignore_ascii_case("GO")
    }
}

/// Blank out T-SQL comments (`-- ...` to end of line and nestable
/// `/* ... */`) while keeping every other byte in place, so line/column
/// positions computed on the result still address the original source.
/// Comment markers inside string literals (`'...'`, `N'...'`), quoted
/// identifiers (`"..."`) and bracketed identifiers (`[...]`) are data and are
/// kept. Comment bytes are replaced by ASCII spaces (one per byte), which keeps
/// the result valid UTF-8 with identical byte offsets; newlines are kept.
fn strip_comments(source: &str) -> String {
    #[derive(Clone, Copy, PartialEq)]
    enum State {
        Code,
        Line,
        Block(u32),
        Quoted(u8),
    }
    let bytes = source.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut state = State::Code;
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        let next = bytes.get(i + 1).copied();
        match state {
            State::Code => match (b, next) {
                (b'-', Some(b'-')) => {
                    state = State::Line;
                    out.extend_from_slice(b"  ");
                    i += 2;
                    continue;
                }
                (b'/', Some(b'*')) => {
                    state = State::Block(1);
                    out.extend_from_slice(b"  ");
                    i += 2;
                    continue;
                }
                (b'\'', _) => state = State::Quoted(b'\''),
                (b'"', _) => state = State::Quoted(b'"'),
                (b'[', _) => state = State::Quoted(b']'),
                _ => {}
            },
            State::Line => {
                if b == b'\n' || b == b'\r' {
                    state = State::Code;
                    out.push(b);
                } else {
                    out.push(b' ');
                }
                i += 1;
                continue;
            }
            State::Block(depth) => {
                if b == b'*' && next == Some(b'/') {
                    state = if depth > 1 {
                        State::Block(depth - 1)
                    } else {
                        State::Code
                    };
                    out.extend_from_slice(b"  ");
                    i += 2;
                } else if b == b'/' && next == Some(b'*') {
                    state = State::Block(depth + 1);
                    out.extend_from_slice(b"  ");
                    i += 2;
                } else {
                    out.push(if b == b'\n' || b == b'\r' { b } else { b' ' });
                    i += 1;
                }
                continue;
            }
            State::Quoted(close) => {
                if b == close {
                    // A doubled delimiter ('' or ]] or "") is an escaped literal one.
                    if next == Some(close) {
                        out.extend_from_slice(&[b, close]);
                        i += 2;
                        continue;
                    }
                    state = State::Code;
                }
            }
        }
        out.push(b);
        i += 1;
    }
    // Only ASCII bytes were substituted for whole UTF-8 sequences byte by
    // byte (comment content) or copied verbatim, so this cannot fail.
    String::from_utf8(out).unwrap_or_default()
}

/// Closing delimiter for a quote opener: string literals (`'...'`, also the
/// `N'...'` form, whose `N` prefix is ordinary code), double-quoted
/// identifiers (`"..."`) and bracketed identifiers (`[...]`).
fn quote_close(c: char) -> Option<char> {
    match c {
        '\'' => Some('\''),
        '"' => Some('"'),
        '[' => Some(']'),
        _ => None,
    }
}

/// Normalise one comment-free code line so layout changes do not leak into
/// labels: outside string literals and quoted identifiers, leading/trailing
/// whitespace is dropped, runs of whitespace collapse to one space and a
/// trailing `;` is removed. Inside them every character is literal content
/// and is copied verbatim (a doubled delimiter `''`, `""`, `]]` is an escape
/// and does not close). `quote` carries an unterminated literal across lines.
fn normalize_line(code: &str, quote: &mut Option<char>) -> String {
    let mut out = String::with_capacity(code.len());
    // Byte length of `out` that is literal content and must not be trimmed.
    let mut protected = 0;
    let mut pending_space = false;
    let mut chars = code.chars().peekable();
    while let Some(c) = chars.next() {
        match *quote {
            Some(close) => {
                out.push(c);
                if c == close {
                    if chars.peek() == Some(&close) {
                        chars.next();
                        out.push(close);
                    } else {
                        *quote = None;
                    }
                }
                protected = out.len();
            }
            None if c.is_whitespace() => pending_space = true,
            None => {
                if pending_space && !out.is_empty() {
                    out.push(' ');
                }
                pending_space = false;
                out.push(c);
                if let Some(close) = quote_close(c) {
                    *quote = Some(close);
                    protected = out.len();
                }
            }
        }
    }
    while out.len() > protected && (out.ends_with(';') || out.ends_with(' ')) {
        out.pop();
    }
    out
}

fn lines(source: &str) -> Vec<SourceLine> {
    let code = strip_comments(source);
    let mut quote = None;
    source
        .lines()
        .zip(code.lines())
        .enumerate()
        .map(|(i, (text, code))| {
            let starts_in_quote = quote.is_some();
            let trimmed = normalize_line(code, &mut quote);
            SourceLine {
                number: i as u32,
                text: text.to_string(),
                trimmed,
                starts_in_quote,
                ends_in_quote: quote.is_some(),
            }
        })
        .collect()
}

/// Split a select list on top-level commas; commas inside string literals
/// and quoted identifiers are data. Whitespace around an item is layout
/// unless it lies inside an (unterminated) literal.
fn split_select_list(label: &str) -> Vec<&str> {
    let mut items = Vec::new();
    let mut quote: Option<char> = None;
    let mut start = 0;
    let mut chars = label.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        match quote {
            Some(close) if c == close => {
                if chars.peek().map(|&(_, n)| n) == Some(close) {
                    chars.next();
                } else {
                    quote = None;
                }
            }
            Some(_) => {}
            None if c == ',' => {
                items.push(label[start..i].trim());
                start = i + 1;
            }
            None => quote = quote_close(c),
        }
    }
    let last = label[start..].trim_start();
    items.push(if quote.is_some() {
        last
    } else {
        last.trim_end()
    });
    items
}

/// If `text` starts with the keyword sequence `words` (case-insensitive,
/// separated by whitespace, each word ending at a non-identifier character),
/// return the byte length of the matched prefix.
fn keyword_prefix(text: &str, words: &[&str]) -> Option<usize> {
    let mut pos = 0;
    for (n, word) in words.iter().enumerate() {
        if n > 0 {
            let rest = &text[pos..];
            let skipped = rest.len() - rest.trim_start().len();
            if skipped == 0 {
                return None;
            }
            pos += skipped;
        }
        let rest = &text[pos..];
        if rest.len() < word.len()
            || !rest.as_bytes()[..word.len()].eq_ignore_ascii_case(word.as_bytes())
        {
            return None;
        }
        pos += word.len();
        if let Some(c) = text[pos..].chars().next() {
            if c.is_alphanumeric() || c == '_' || c == '@' || c == '#' || c == '$' {
                return None;
            }
        }
    }
    Some(pos)
}

/// Join operator forms recognised at the start of a clause line. The flavor is
/// semantic (LEFT keeps unmatched rows, INNER drops them) so it is retained in
/// the clause label exactly as written (keyword case/spacing normalised).
const JOIN_FORMS: &[&[&str]] = &[
    &["LEFT", "OUTER", "JOIN"],
    &["RIGHT", "OUTER", "JOIN"],
    &["FULL", "OUTER", "JOIN"],
    &["LEFT", "JOIN"],
    &["RIGHT", "JOIN"],
    &["FULL", "JOIN"],
    &["INNER", "LOOP", "JOIN"],
    &["INNER", "HASH", "JOIN"],
    &["INNER", "MERGE", "JOIN"],
    &["INNER", "REMOTE", "JOIN"],
    &["INNER", "JOIN"],
    &["CROSS", "JOIN"],
    &["CROSS", "APPLY"],
    &["OUTER", "APPLY"],
    &["OUTER", "JOIN"],
    &["JOIN"],
];

fn join_prefix(text: &str) -> Option<(usize, String)> {
    JOIN_FORMS
        .iter()
        .find_map(|words| keyword_prefix(text, words).map(|len| (len, words.join(" "))))
}

fn clean_name(raw: &str) -> String {
    raw.trim_matches(|c: char| {
        !(c.is_ascii_alphanumeric() || c == '_' || c == '@' || c == '#' || c == '.')
    })
    .to_string()
}

fn object_name(header: &str, keyword: &str) -> String {
    let upper = header.to_ascii_uppercase();
    if let Some(pos) = upper.find(keyword) {
        let rest = header[pos + keyword.len()..].trim_start();
        return clean_name(
            rest.split(|c: char| c == '(' || c.is_whitespace())
                .next()
                .unwrap_or(""),
        );
    }
    "(anonymous)".to_string()
}

fn leaf(id: &str, node_type: &str, label: &str, line: &SourceLine) -> SemanticNode {
    SemanticNodeBuilder::new(
        id,
        node_type,
        label,
        line.number,
        0,
        line.number,
        line.text.len() as u32,
        "",
    )
    .build()
}

const CLAUSES: &[(&str, &[&str])] = &[
    ("select_clause", &["SELECT"]),
    ("from_clause", &["FROM"]),
    ("where_clause", &["WHERE"]),
    ("group_by_clause", &["GROUP", "BY"]),
    ("having_clause", &["HAVING"]),
    ("order_by_clause", &["ORDER", "BY"]),
];

fn clause_kind(trimmed: &str) -> Option<&'static str> {
    if join_prefix(trimmed).is_some() {
        return Some("join_clause");
    }
    CLAUSES
        .iter()
        .find(|(_, words)| keyword_prefix(trimmed, words).is_some())
        .map(|(kind, _)| *kind)
}

/// Clause label: the clause body with the leading clause keyword removed
/// (the node type carries it). For joins the join flavor is semantic and is
/// kept as the label prefix, e.g. `LEFT JOIN orders o ON o.user_id = u.id`.
fn clause_label(lines: &[&SourceLine], node_type: &str) -> String {
    let mut label = String::new();
    let mut prev_ends_in_quote = false;
    for (n, line) in lines.iter().enumerate() {
        // `trimmed` is already normalised, so whitespace right after the
        // clause keyword is layout; anything at the end is literal content.
        let mut text = line.trimmed.clone();
        if n == 0 {
            if node_type == "join_clause" {
                if let Some((len, flavor)) = join_prefix(&text) {
                    let rest = text[len..].trim_start();
                    text = if rest.is_empty() {
                        flavor
                    } else {
                        format!("{} {}", flavor, rest)
                    };
                }
            } else if let Some((_, words)) = CLAUSES.iter().find(|(kind, _)| *kind == node_type) {
                if let Some(len) = keyword_prefix(&text, words) {
                    text = text[len..].trim_start().to_string();
                }
            }
        }
        // A trailing list comma is layout, but not one inside an open literal.
        let text = if line.ends_in_quote {
            text.as_str()
        } else {
            text.trim_end_matches(',')
        };
        if prev_ends_in_quote {
            // The line break is part of a multi-line literal.
            label.push('\n');
            label.push_str(text);
        } else if !text.is_empty() {
            if !label.is_empty() {
                label.push(' ');
            }
            label.push_str(text);
        }
        prev_ends_in_quote = line.ends_in_quote;
    }
    label
}

fn select_items(id: &str, label: &str, line: &SourceLine) -> Vec<SemanticNode> {
    split_select_list(label)
        .into_iter()
        .enumerate()
        .filter(|(_, item)| !item.is_empty())
        .map(|(i, item)| leaf(&format!("{}.{}", id, i), "select_item", item, line))
        .collect()
}

fn parse_select_statement(id: &str, source_lines: &[SourceLine]) -> SemanticNode {
    let nonempty: Vec<&SourceLine> = source_lines
        .iter()
        .filter(|line| !line.is_blank() && !line.is_batch_separator())
        .collect();
    let first = nonempty
        .first()
        .copied()
        .unwrap_or_else(|| &source_lines[0]);
    let last = nonempty.last().copied().unwrap_or(first);

    let mut groups: Vec<(&'static str, Vec<&SourceLine>)> = Vec::new();
    let mut current_kind: Option<&'static str> = None;
    let mut current_lines: Vec<&SourceLine> = Vec::new();

    for line in &nonempty {
        if let Some(kind) = clause_kind(&line.trimmed) {
            if let Some(prev) = current_kind.take() {
                groups.push((prev, current_lines));
                current_lines = Vec::new();
            }
            current_kind = Some(kind);
        }
        current_lines.push(*line);
    }
    if let Some(prev) = current_kind {
        groups.push((prev, current_lines));
    }

    let mut children = Vec::new();
    for (i, (node_type, clause_lines)) in groups.iter().enumerate() {
        let label = clause_label(clause_lines, node_type);
        let line = clause_lines.first().copied().unwrap_or(first);
        let clause_id = format!("{}.{}", id, i);
        let clause_children = if *node_type == "select_clause" {
            select_items(&clause_id, &label, line)
        } else {
            Vec::new()
        };
        children.push(
            SemanticNodeBuilder::new(
                &clause_id,
                *node_type,
                label,
                line.number,
                0,
                clause_lines.last().copied().unwrap_or(line).number,
                clause_lines.last().copied().unwrap_or(line).text.len() as u32,
                "",
            )
            .children(clause_children)
            .build(),
        );
    }

    SemanticNodeBuilder::new(
        id,
        "select_statement",
        "SELECT",
        first.number,
        0,
        last.number,
        last.text.len() as u32,
        "",
    )
    .children(children)
    .build()
}

fn parse_routine(
    id: &str,
    source_lines: &[SourceLine],
    node_type: &'static str,
    keyword: &str,
) -> SemanticNode {
    let first = source_lines
        .iter()
        .find(|line| !line.is_blank())
        .unwrap_or(&source_lines[0]);
    let last = source_lines
        .iter()
        .rev()
        .find(|line| !line.is_blank())
        .unwrap_or(first);
    let label = object_name(&first.trimmed, keyword);
    let children = source_lines
        .iter()
        .enumerate()
        .filter(|(_, line)| !line.is_blank() && !line.is_batch_separator())
        .map(|(i, line)| leaf(&format!("{}.{}", id, i), "statement", &line.trimmed, line))
        .collect();
    SemanticNodeBuilder::new(
        id,
        node_type,
        label,
        first.number,
        0,
        last.number,
        last.text.len() as u32,
        "",
    )
    .children(children)
    .build()
}

/// Unmodeled statements (INSERT, UPDATE, DECLARE, ...) are kept
/// conservatively: one `statement` leaf per non-empty code line, so a change
/// to any of them is never certified as formatting.
fn parse_statement_lines(id: &str, source_lines: &[SourceLine]) -> Vec<SemanticNode> {
    source_lines
        .iter()
        .filter(|line| !line.is_blank())
        .enumerate()
        .map(|(i, line)| leaf(&format!("{}.{}", id, i), "statement", &line.trimmed, line))
        .collect()
}

/// Exact end of the source: the row is the number of LFs and the column the
/// UTF-8 byte length after the last LF, so the endpoint always exists in the
/// LF-split source (empty source ends at (0, 0)).
fn source_end(source: &str) -> (u32, u32) {
    let row = source.bytes().filter(|&b| b == b'\n').count() as u32;
    let col = match source.rfind('\n') {
        Some(pos) => source.len() - pos - 1,
        None => source.len(),
    } as u32;
    (row, col)
}

fn parse_source(source: &str) -> SemanticNode {
    let source_lines = lines(source);
    // Dispatch on the first line that holds code; comment-only and blank
    // lines (already blanked by `strip_comments`) are skipped.
    let first_nonempty = source_lines
        .iter()
        .find(|line| !line.is_blank())
        .map(|line| line.trimmed.as_str())
        .unwrap_or_default();
    let starts = |words: &[&str]| keyword_prefix(first_nonempty, words).is_some();

    let children: Vec<SemanticNode> = if source_lines.is_empty() || first_nonempty.is_empty() {
        Vec::new()
    } else if starts(&["CREATE", "OR", "ALTER", "PROCEDURE"])
        || starts(&["CREATE", "OR", "ALTER", "PROC"])
        || starts(&["CREATE", "PROCEDURE"])
        || starts(&["CREATE", "PROC"])
        || starts(&["ALTER", "PROCEDURE"])
        || starts(&["ALTER", "PROC"])
    {
        let keyword = if first_nonempty.to_ascii_uppercase().contains("PROCEDURE") {
            "PROCEDURE"
        } else {
            "PROC"
        };
        vec![parse_routine(
            "0.0",
            &source_lines,
            "create_or_alter_procedure_statement",
            keyword,
        )]
    } else if starts(&["CREATE", "OR", "ALTER", "FUNCTION"])
        || starts(&["CREATE", "FUNCTION"])
        || starts(&["ALTER", "FUNCTION"])
    {
        vec![parse_routine(
            "0.0",
            &source_lines,
            "create_or_alter_function_statement",
            "FUNCTION",
        )]
    } else if starts(&["SELECT"]) {
        vec![parse_select_statement("0.0", &source_lines)]
    } else {
        parse_statement_lines("0", &source_lines)
    };

    let (end_row, end_col) = source_end(source);
    SemanticNodeBuilder::new(
        "0",
        "source_file",
        "source_file",
        0,
        0,
        end_row,
        end_col,
        "",
    )
    .children(children)
    .build()
}

fn process_impl(source: &str) -> String {
    match serde_json::to_string(&parse_source(source)) {
        Ok(s) => s,
        Err(e) => format!(r#"{{"error":"Serialisation error: {}"}}"#, e),
    }
}

impl Guest for TsqlParser {
    fn get_parser_mode() -> ParserMode {
        ParserMode::FullParse
    }
    fn grammar_id() -> String {
        "tsql".to_string()
    }
    fn detect_language(filename: String, content: String) -> String {
        let lower = filename.to_lowercase();
        if lower.ends_with(".tsql") {
            return "tsql".to_string();
        }
        if !lower.ends_with(".sql") {
            return String::new();
        }
        let upper = content.to_uppercase();
        let indicators = [
            upper.contains("DECLARE @"),
            upper.contains("\nGO\n")
                || upper.ends_with("\nGO")
                || upper.contains("\r\nGO\r\n")
                || upper.ends_with("\r\nGO"),
            upper.contains("BEGIN TRY"),
            upper.contains("BEGIN CATCH"),
            upper.contains("EXEC SP_"),
            upper.contains("EXECUTE SP_"),
            upper.contains("@@"),
        ];
        if indicators.iter().any(|&b| b) {
            "tsql".to_string()
        } else {
            String::new()
        }
    }
    fn preprocess_source(source: String) -> String {
        source
    }
    fn example(_language: String) -> ExamplePair {
        ExamplePair {
            old: "SELECT id, name, email\nFROM users\nWHERE active = 1;\n".to_string(),
            new: "SELECT\n    u.id,\n    u.name,\n    u.email,\n    COUNT(o.id) AS order_count\nFROM users u\nLEFT JOIN orders o ON o.user_id = u.id\nWHERE u.active = 1\nGROUP BY u.id, u.name, u.email\nORDER BY order_count DESC;\n".to_string(),
        }
    }
    fn process(input: String, _language: String, _filename: String) -> String {
        process_impl(&input)
    }
    fn trivia_node_types() -> Vec<String> {
        Vec::new()
    }
    fn language_ids() -> Vec<String> {
        vec!["tsql".to_string()]
    }
    fn language_info() -> Vec<LanguageInfoRecord> {
        language_info_for(Self::language_ids())
    }
    fn priority() -> i32 {
        10
    }
}

export!(TsqlParser);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exports::intentdiff::plugin::parser::Guest;
    use intentumdiff_plugin_sdk::testing as t;

    #[test]
    fn grammar_id_nonempty() {
        assert!(!TsqlParser::grammar_id().is_empty());
    }

    #[test]
    fn parser_mode_is_full_parse() {
        assert!(matches!(
            TsqlParser::get_parser_mode(),
            ParserMode::FullParse
        ));
    }

    #[test]
    fn language_ids_contain_grammar_id() {
        assert!(TsqlParser::language_ids().contains(&TsqlParser::grammar_id()));
    }

    #[test]
    fn detect_language_known_ext() {
        assert_eq!(
            TsqlParser::detect_language("test.tsql".to_string(), "".to_string()),
            "tsql"
        );
    }

    #[test]
    fn detect_language_unknown_ext() {
        assert_eq!(
            TsqlParser::detect_language("test.xyz_notareal_ext_9z8y".to_string(), "".to_string()),
            ""
        );
    }

    #[test]
    fn process_impl_empty_returns_valid_json() {
        t::assert_valid_json(&process_impl(""), "process(empty)");
    }

    #[test]
    fn process_impl_whitespace_returns_valid_json() {
        t::assert_valid_json(&process_impl("   \n  "), "process(whitespace)");
    }

    #[test]
    fn playground_example_produces_select_clauses() {
        let example = <TsqlParser as Guest>::example("tsql".to_string());
        let out = process_impl(&example.new);
        t::assert_valid_json(&out, "tsql example");
        t::assert_no_error(&out, "tsql example");
        assert!(out.contains("select_statement"));
        assert!(out.contains("join_clause"));
        assert!(out.contains("order_by_clause"));
    }

    // ---- helpers for the regression tests below ----

    fn tree(source: &str) -> serde_json::Value {
        let out = process_impl(source);
        t::assert_valid_json(&out, "tsql tree");
        t::assert_no_error(&out, "tsql tree");
        serde_json::from_str(&out).expect("tree json")
    }

    /// Position-free semantic projection: depth, node type and label.
    fn projection(source: &str) -> Vec<String> {
        fn walk(node: &serde_json::Value, depth: usize, out: &mut Vec<String>) {
            out.push(format!(
                "{}{}|{}",
                "  ".repeat(depth),
                node["node_type"].as_str().unwrap_or(""),
                node["label"].as_str().unwrap_or("")
            ));
            if let Some(children) = node["children"].as_array() {
                for child in children {
                    walk(child, depth + 1, out);
                }
            }
        }
        let mut out = Vec::new();
        walk(&tree(source), 0, &mut out);
        out
    }

    fn labels_of(source: &str, node_type: &str) -> Vec<String> {
        projection(source)
            .into_iter()
            .filter_map(|row| {
                let (ty, label) = row.trim_start().split_once('|')?;
                (ty == node_type).then(|| label.to_string())
            })
            .collect()
    }

    const PLAYGROUND: &str = "SELECT\n    u.id,\n    u.name,\n    u.email,\n    COUNT(o.id) AS order_count\nFROM users u\nLEFT JOIN orders o ON o.user_id = u.id\nWHERE u.active = 1\nGROUP BY u.id, u.name, u.email\nORDER BY order_count DESC;\n";

    // ---- #4: JOIN flavor is retained ----

    #[test]
    fn join_flavor_change_is_semantic_multiline() {
        let new = PLAYGROUND.replace("LEFT JOIN", "INNER JOIN");
        assert_eq!(
            labels_of(PLAYGROUND, "join_clause"),
            vec!["LEFT JOIN orders o ON o.user_id = u.id"]
        );
        assert_eq!(
            labels_of(&new, "join_clause"),
            vec!["INNER JOIN orders o ON o.user_id = u.id"]
        );
        assert_ne!(projection(PLAYGROUND), projection(&new));
    }

    #[test]
    fn join_flavor_change_is_semantic_issue_pair() {
        let old = "SELECT a.id\nFROM a\nLEFT JOIN b ON a.id = b.id;\n";
        let new = "SELECT a.id\nFROM a\nINNER JOIN b ON a.id = b.id;\n";
        assert_eq!(
            labels_of(old, "join_clause"),
            vec!["LEFT JOIN b ON a.id = b.id"]
        );
        assert_eq!(
            labels_of(new, "join_clause"),
            vec!["INNER JOIN b ON a.id = b.id"]
        );
    }

    #[test]
    fn join_flavor_change_is_semantic_single_line() {
        let old = "SELECT u.id FROM users u LEFT JOIN orders o ON o.user_id = u.id;\n";
        let new = "SELECT u.id FROM users u INNER JOIN orders o ON o.user_id = u.id;\n";
        assert_ne!(projection(old), projection(new));
    }

    #[test]
    fn join_flavors_are_distinct_and_kept() {
        let flavors = [
            "JOIN",
            "INNER JOIN",
            "LEFT JOIN",
            "LEFT OUTER JOIN",
            "RIGHT JOIN",
            "RIGHT OUTER JOIN",
            "FULL JOIN",
            "FULL OUTER JOIN",
            "CROSS JOIN",
            "CROSS APPLY",
            "OUTER APPLY",
            "INNER HASH JOIN",
        ];
        let mut seen = Vec::new();
        for flavor in flavors {
            let src = format!("SELECT a.id\nFROM a\n{} b ON a.id = b.id\n", flavor);
            let labels = labels_of(&src, "join_clause");
            assert_eq!(
                labels,
                vec![format!("{} b ON a.id = b.id", flavor)],
                "{}",
                flavor
            );
            seen.push(labels);
        }
        seen.dedup();
        assert_eq!(seen.len(), flavors.len());
    }

    #[test]
    fn join_keyword_case_and_spacing_is_layout() {
        let old = "SELECT a.id\nFROM a\nLEFT JOIN b ON a.id = b.id\n";
        let new = "SELECT a.id\nFROM a\nleft   join b  ON a.id = b.id\n";
        assert_eq!(projection(old), projection(new));
    }

    #[test]
    fn join_condition_on_next_line_is_kept() {
        let old = "SELECT a.id\nFROM a\nLEFT JOIN b\n    ON a.id = b.id\n";
        let new = "SELECT a.id\nFROM a\nLEFT JOIN b\n    ON a.id <> b.id\n";
        assert_eq!(
            labels_of(old, "join_clause"),
            vec!["LEFT JOIN b ON a.id = b.id"]
        );
        assert_ne!(projection(old), projection(new));
    }

    #[test]
    fn clause_keywords_need_a_word_boundary() {
        // `JOINED_AT` / `FROMAGE` are identifiers continuing the SELECT list,
        // not new clauses.
        let src = "SELECT\n    joined_at,\n    fromage\nFROM t\n";
        assert!(labels_of(src, "join_clause").is_empty());
        assert_eq!(labels_of(src, "from_clause"), vec!["t"]);
        assert_eq!(labels_of(src, "select_clause"), vec!["joined_at fromage"]);
    }

    #[test]
    fn identity_and_whitespace_controls_are_unchanged() {
        assert_eq!(projection(PLAYGROUND), projection(PLAYGROUND));
        let reindented = PLAYGROUND.replace("    u.", "\tu.");
        assert_eq!(projection(PLAYGROUND), projection(&reindented));
    }

    // ---- #5: statements after leading comments are retained ----

    #[test]
    fn leading_line_comment_keeps_select_tree() {
        // Exact pair from data_config.tsql.safe_preservation.
        let new = format!("-- ordinary assessment comment\n{}", PLAYGROUND);
        assert_eq!(projection(PLAYGROUND), projection(&new));
        assert!(labels_of(&new, "select_statement").len() == 1);
    }

    #[test]
    fn leading_block_comment_and_blank_lines_keep_select_tree() {
        let new = format!(
            "\n/* header\n   -- nested marker\n*/\n\n-- second\n{}",
            PLAYGROUND
        );
        assert_eq!(projection(PLAYGROUND), projection(&new));
    }

    #[test]
    fn leading_comment_before_procedure_keeps_routine() {
        let old = "CREATE OR ALTER PROCEDURE dbo.GetUser\n    @id INT\nAS\nBEGIN\n    SELECT * FROM users WHERE id = @id;\nEND\nGO\n";
        let new = format!("-- procedure header\n\n{}", old);
        assert_eq!(projection(old), projection(&new));
        assert_eq!(
            labels_of(&new, "create_or_alter_procedure_statement"),
            vec!["dbo.GetUser"]
        );
    }

    #[test]
    fn trailing_and_inline_comments_are_layout() {
        let old = "SELECT a.id\nFROM a\nWHERE a.x = 1\n";
        let new = "SELECT a.id -- the id\nFROM a /* source */\nWHERE a.x = 1 -- filter\n";
        assert_eq!(projection(old), projection(new));
    }

    #[test]
    fn quoted_comment_markers_are_string_data() {
        let old = "SELECT '--a' AS x, N'/*b*/' AS y, [c--d] AS z\n";
        let new = "SELECT '--A' AS x, N'/*b*/' AS y, [c--d] AS z\n";
        assert_eq!(
            labels_of(old, "select_item"),
            vec!["'--a' AS x", "N'/*b*/' AS y", "[c--d] AS z"]
        );
        assert_ne!(projection(old), projection(new));
        // Escaped quote does not end the literal early.
        assert_eq!(
            labels_of("SELECT 'it''s -- not a comment' AS s\n", "select_item"),
            vec!["'it''s -- not a comment' AS s"]
        );
    }

    #[test]
    fn unmodeled_statements_are_kept_conservatively() {
        let old = "-- update\nUPDATE users SET active = 1 WHERE id = 7;\n";
        let new = "-- update\nUPDATE users SET active = 0 WHERE id = 7;\n";
        assert_eq!(
            labels_of(old, "statement"),
            vec!["UPDATE users SET active = 1 WHERE id = 7"]
        );
        assert_ne!(projection(old), projection(new));
    }

    // ---- #6: root range is bounded to the actual source ----

    fn root_range(source: &str) -> (u64, u64, u64, u64) {
        let pos = &tree(source)["position"];
        let get = |k: &str| pos[k].as_u64().expect(k);
        (
            get("start_line"),
            get("start_col"),
            get("end_line"),
            get("end_col"),
        )
    }

    fn assert_endpoint_in_source(source: &str) {
        let (sl, sc, el, ec) = root_range(source);
        assert_eq!((sl, sc), (0, 0), "root starts at origin");
        let rows: Vec<&str> = source.split('\n').collect();
        let row = rows
            .get(el as usize)
            .unwrap_or_else(|| panic!("row {} missing", el));
        assert!(
            (ec as usize) <= row.len(),
            "col {} beyond row {:?}",
            ec,
            row
        );
        assert!(row.is_char_boundary(ec as usize));
        assert_eq!(el as usize, rows.len() - 1, "root ends on the last row");
        assert_eq!(ec as usize, rows[rows.len() - 1].len(), "root ends at EOF");
    }

    #[test]
    fn root_range_is_bounded_for_partial_input() {
        // Exact new side of data_config.tsql.incomplete (no final LF).
        let partial = "SELECT\n    u.id,\n    u.name,\n    u.email,\n    COUNT(o.id) AS order_";
        assert_eq!(root_range(partial), (0, 0, 4, 25));
        assert_endpoint_in_source(partial);
    }

    #[test]
    fn root_range_is_bounded_for_boundary_inputs() {
        assert_eq!(root_range(""), (0, 0, 0, 0));
        for src in [
            "",
            "\n",
            "   \n  ",
            PLAYGROUND,
            "SELECT 1",
            "SELECT 1\r\nFROM t\r\n",
            "SELECT 1\r\nFROM t",
            "SELECT N'λ' AS label;\n",
            "SELECT N'λμ'",
            "-- only a comment",
        ] {
            assert_endpoint_in_source(src);
        }
    }

    #[test]
    fn non_ascii_routine_header_does_not_panic() {
        // `ß` upper-cases to `SS` under full Unicode rules; name lookup must
        // stay on byte offsets of the original header.
        let src = "CREATE PROCEDURE ßßß.dbo_x AS SELECT 1\n";
        let out = process_impl(src);
        t::assert_valid_json(&out, "non-ascii routine");
        assert_endpoint_in_source(src);
    }

    #[test]
    fn output_is_deterministic() {
        let src = format!("-- c\n{}", PLAYGROUND);
        assert_eq!(process_impl(&src), process_impl(&src));
    }

    // ---- PR #7 review: whitespace inside literals/quoted identifiers is data ----

    fn assert_semantic(old: &str, new: &str) {
        assert_ne!(projection(old), projection(new), "\nold: {old}\nnew: {new}");
    }

    fn assert_style_only(old: &str, new: &str) {
        assert_eq!(projection(old), projection(new), "\nold: {old}\nnew: {new}");
    }

    #[test]
    fn whitespace_inside_string_literal_is_semantic() {
        // Exact pair from the review comment.
        assert_semantic("SELECT 'a  b' AS value;\n", "SELECT 'a b' AS value;\n");
        assert_eq!(
            labels_of("SELECT 'a  b' AS value;\n", "select_item"),
            vec!["'a  b' AS value"]
        );
        assert_semantic("SELECT 'a\tb' AS v\n", "SELECT 'a b' AS v\n");
        assert_semantic("SELECT ' a' AS v\n", "SELECT 'a' AS v\n");
        assert_semantic("SELECT 'a ' AS v\n", "SELECT 'a' AS v\n");
    }

    #[test]
    fn whitespace_inside_unicode_literal_is_semantic() {
        assert_semantic("SELECT N'a  b' AS v\n", "SELECT N'a b' AS v\n");
        assert_eq!(
            labels_of("SELECT N'a  b' AS v\n", "select_item"),
            vec!["N'a  b' AS v"]
        );
    }

    #[test]
    fn whitespace_after_escaped_quote_stays_inside_literal() {
        // `''` is an escaped quote, not the end of the literal.
        assert_semantic("SELECT 'it''s  x' AS v\n", "SELECT 'it''s x' AS v\n");
        assert_semantic("SELECT '''  ''' AS v\n", "SELECT ''' ''' AS v\n");
    }

    #[test]
    fn whitespace_inside_bracketed_identifier_is_semantic() {
        // Exact pair from the review comment.
        assert_semantic(
            "SELECT [first  name] FROM t\n",
            "SELECT [first name] FROM t\n",
        );
        assert_eq!(
            labels_of("SELECT [first  name]\nFROM t\n", "select_item"),
            vec!["[first  name]"]
        );
        // `]]` is an escaped bracket, not the end of the identifier.
        assert_semantic("SELECT [a]]  b] FROM t\n", "SELECT [a]] b] FROM t\n");
        assert_semantic("SELECT x FROM [my  table]\n", "SELECT x FROM [my table]\n");
    }

    #[test]
    fn whitespace_inside_double_quoted_identifier_is_semantic() {
        assert_semantic("SELECT \"my  col\" FROM t\n", "SELECT \"my col\" FROM t\n");
        assert_semantic(
            "SELECT \"a\"\"  b\" FROM t\n",
            "SELECT \"a\"\" b\" FROM t\n",
        );
    }

    #[test]
    fn whitespace_inside_literal_in_unmodeled_statement_is_semantic() {
        assert_semantic(
            "UPDATE t SET name = 'a  b' WHERE id = 1;\n",
            "UPDATE t SET name = 'a b' WHERE id = 1;\n",
        );
        assert_semantic(
            "CREATE PROCEDURE dbo.p AS\nBEGIN\n    SELECT 'x  y';\nEND\n",
            "CREATE PROCEDURE dbo.p AS\nBEGIN\n    SELECT 'x y';\nEND\n",
        );
    }

    #[test]
    fn whitespace_inside_multiline_literal_is_semantic() {
        // The literal spans lines: leading/trailing whitespace on the inner
        // lines and the line break itself are literal content.
        assert_semantic("SELECT 'a\n  b' AS v\n", "SELECT 'a\nb' AS v\n");
        assert_semantic("SELECT 'a  \nb' AS v\n", "SELECT 'a\nb' AS v\n");
        assert_semantic("SELECT 'a\nb' AS v\n", "SELECT 'a b' AS v\n");
        // A `;` inside the literal at a line end is data.
        assert_semantic("SELECT 'a;\nb' AS v\n", "SELECT 'a\nb' AS v\n");
        // Blank and `GO` lines inside the literal are content, not layout.
        assert_semantic("SELECT 'a\n\nb' AS v\n", "SELECT 'a\nb' AS v\n");
        assert_semantic("SELECT 'a\nGO\nb' AS v\n", "SELECT 'a\nb' AS v\n");
    }

    #[test]
    fn comma_inside_literal_does_not_split_select_items() {
        assert_eq!(
            labels_of("SELECT 'a,  b' AS v, c\n", "select_item"),
            vec!["'a,  b' AS v", "c"]
        );
        assert_semantic("SELECT 'a,  b' AS v\n", "SELECT 'a, b' AS v\n");
    }

    #[test]
    fn layout_outside_literals_stays_style_only() {
        assert_style_only(
            "SELECT 'a  b' AS value, [first  name], N'x  y', \"q  r\" FROM t;\n",
            "SELECT   'a  b'   AS\tvalue,   [first  name],\tN'x  y',  \"q  r\"   FROM   t ;  \n",
        );
        assert_style_only(
            "SELECT 'a  b' AS v\nFROM [my  t]\nWHERE x = 'p  q'\n",
            "SELECT   'a  b'  AS  v\n   FROM  [my  t]\n\tWHERE  x  =  'p  q'   \n",
        );
        assert_style_only(
            "UPDATE t SET name = 'a  b' WHERE id = 1;\n",
            "  UPDATE   t SET  name =  'a  b'   WHERE id = 1 ;\n",
        );
        assert_style_only(
            "SELECT 'it''s  x' AS v, [a]]  b]\n",
            "SELECT    'it''s  x'   AS v,   [a]]  b]\n",
        );
        // Multi-line literal: layout after the literal closes is still layout.
        assert_style_only("SELECT 'a\n  b' AS v\n", "SELECT 'a\n  b'    AS   v  \n");
    }
}
