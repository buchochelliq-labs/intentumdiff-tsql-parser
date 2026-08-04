//! T-SQL parser plugin, full-parse mode.
//!
//! This compact dialect parser handles query/procedure level structure without
//! requiring a host tree-sitter package.

use intentumdiff_plugin_sdk::tree::{SemanticNode, SemanticNodeBuilder};

wit_bindgen::generate!({
    path: "wit/plugin.wit",
    world: "parser-plugin",
});

use crate::exports::intentumdiff::plugin::parser::ExamplePair;
use crate::exports::intentumdiff::plugin::parser::Guest;
use crate::exports::intentumdiff::plugin::parser::LanguageInfoRecord;
use crate::exports::intentumdiff::plugin::parser::ParserMode;

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
    trimmed: String,
}

fn lines(source: &str) -> Vec<SourceLine> {
    source
        .lines()
        .enumerate()
        .map(|(i, text)| SourceLine {
            number: i as u32,
            text: text.to_string(),
            trimmed: text.trim().trim_end_matches(';').to_string(),
        })
        .collect()
}

fn clean_name(raw: &str) -> String {
    raw.trim_matches(|c: char| {
        !(c.is_ascii_alphanumeric() || c == '_' || c == '@' || c == '#' || c == '.')
    })
    .to_string()
}

fn object_name(header: &str, keyword: &str) -> String {
    let upper = header.to_uppercase();
    if let Some(pos) = upper.find(keyword) {
        let rest = &header[pos + keyword.len()..];
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

fn clause_kind(trimmed: &str) -> Option<(&'static str, &'static str)> {
    let upper = trimmed.to_uppercase();
    if upper.starts_with("SELECT") {
        Some(("select_clause", "SELECT"))
    } else if upper.starts_with("FROM") {
        Some(("from_clause", "FROM"))
    } else if upper.starts_with("WHERE") {
        Some(("where_clause", "WHERE"))
    } else if upper.starts_with("GROUP BY") {
        Some(("group_by_clause", "GROUP BY"))
    } else if upper.starts_with("ORDER BY") {
        Some(("order_by_clause", "ORDER BY"))
    } else if upper.starts_with("LEFT JOIN")
        || upper.starts_with("RIGHT JOIN")
        || upper.starts_with("INNER JOIN")
        || upper.starts_with("OUTER JOIN")
        || upper.starts_with("FULL JOIN")
        || upper.starts_with("JOIN")
    {
        Some(("join_clause", "JOIN"))
    } else {
        None
    }
}

fn clause_label(lines: &[&SourceLine], keyword: &str) -> String {
    let mut parts = Vec::new();
    for line in lines {
        let mut text = line.trimmed.as_str();
        let upper = text.to_uppercase();
        if upper.starts_with(keyword) {
            text = text[keyword.len()..].trim();
        } else if keyword == "JOIN" {
            for join_kw in [
                "LEFT JOIN",
                "RIGHT JOIN",
                "INNER JOIN",
                "OUTER JOIN",
                "FULL JOIN",
                "JOIN",
            ] {
                if upper.starts_with(join_kw) {
                    text = text[join_kw.len()..].trim();
                    break;
                }
            }
        }
        if !text.is_empty() {
            parts.push(text.trim_end_matches(',').to_string());
        }
    }
    parts.join(" ")
}

fn select_items(id: &str, label: &str, line: &SourceLine) -> Vec<SemanticNode> {
    label
        .split(',')
        .enumerate()
        .filter_map(|(i, item)| {
            let trimmed = item.trim();
            if trimmed.is_empty() {
                None
            } else {
                Some(leaf(&format!("{}.{}", id, i), "select_item", trimmed, line))
            }
        })
        .collect()
}

fn parse_select_statement(id: &str, source_lines: &[SourceLine]) -> SemanticNode {
    let nonempty: Vec<&SourceLine> = source_lines
        .iter()
        .filter(|line| !line.trimmed.is_empty() && !line.trimmed.eq_ignore_ascii_case("GO"))
        .collect();
    let first = nonempty
        .first()
        .copied()
        .unwrap_or_else(|| &source_lines[0]);
    let last = nonempty.last().copied().unwrap_or(first);

    let mut groups: Vec<(&'static str, &'static str, Vec<&SourceLine>)> = Vec::new();
    let mut current_kind: Option<(&'static str, &'static str)> = None;
    let mut current_lines: Vec<&SourceLine> = Vec::new();

    for line in &nonempty {
        if let Some(kind) = clause_kind(&line.trimmed) {
            if let Some(prev) = current_kind.take() {
                groups.push((prev.0, prev.1, current_lines));
                current_lines = Vec::new();
            }
            current_kind = Some(kind);
        }
        current_lines.push(*line);
    }
    if let Some(prev) = current_kind {
        groups.push((prev.0, prev.1, current_lines));
    }

    let mut children = Vec::new();
    for (i, (node_type, keyword, clause_lines)) in groups.iter().enumerate() {
        let label = clause_label(clause_lines, keyword);
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
        .find(|line| !line.trimmed.is_empty())
        .unwrap_or(&source_lines[0]);
    let last = source_lines
        .iter()
        .rev()
        .find(|line| !line.trimmed.is_empty())
        .unwrap_or(first);
    let label = object_name(&first.trimmed, keyword);
    let children = source_lines
        .iter()
        .enumerate()
        .filter(|(_, line)| !line.trimmed.is_empty() && !line.trimmed.eq_ignore_ascii_case("GO"))
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

fn parse_source(source: &str) -> SemanticNode {
    let source_lines = lines(source);
    let first_nonempty = source_lines
        .iter()
        .find(|line| !line.trimmed.is_empty())
        .map(|line| line.trimmed.to_uppercase())
        .unwrap_or_default();

    let child = if first_nonempty.starts_with("CREATE OR ALTER PROCEDURE")
        || first_nonempty.starts_with("CREATE PROCEDURE")
        || first_nonempty.starts_with("ALTER PROCEDURE")
    {
        Some(parse_routine(
            "0.0",
            &source_lines,
            "create_or_alter_procedure_statement",
            "PROCEDURE",
        ))
    } else if first_nonempty.starts_with("CREATE OR ALTER FUNCTION")
        || first_nonempty.starts_with("CREATE FUNCTION")
        || first_nonempty.starts_with("ALTER FUNCTION")
    {
        Some(parse_routine(
            "0.0",
            &source_lines,
            "create_or_alter_function_statement",
            "FUNCTION",
        ))
    } else if first_nonempty.starts_with("SELECT") {
        Some(parse_select_statement("0.0", &source_lines))
    } else {
        None
    };

    let children = child.into_iter().collect();
    let end_line = source.lines().count().max(1) as u32;
    SemanticNodeBuilder::new("0", "source_file", "source_file", 1, 0, end_line, 0, "")
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
    use crate::exports::intentumdiff::plugin::parser::Guest;
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
}
