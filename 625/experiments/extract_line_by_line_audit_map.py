#!/usr/bin/env python3
"""Extract a deterministic line-by-line audit map from the Erdős 625 TeX.

The script is standard-library only.  It does not judge mathematical truth.
It identifies the exact source ranges of sections, boxed statements, proofs,
tagged displays, labels, and selected audit-risk patterns so that a human audit
cannot silently skip a theorem or proof transition.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


STATEMENT_BEGIN_RE = re.compile(
    r"\\begin\{(?P<kind>resultbox|lemmabox|propositionbox)\}"
    r"\{(?P<title>.*)\}\s*$"
)
SECTION_RE = re.compile(r"\\(?P<kind>section\*?|subsection\*?)\{(?P<title>.*)\}")
DISPLAY_HEADING_RE = re.compile(r"\\displayheading\{(?P<title>.*)\}")
PARAGRAPH_RE = re.compile(r"\\paragraph\{(?P<title>.*)\}")
TAG_RE = re.compile(r"\\tag\{(?P<tag>[^}]+)\}")
LABEL_RE = re.compile(r"\\label\{(?P<label>[^}]+)\}")
REFERENCE_RE = re.compile(r"\\(?:eqref|ref|autoref)\{(?P<label>[^}]+)\}")
CITATION_RE = re.compile(r"\\cite[tp]?\s*(?:\[[^]]*\])?\{(?P<keys>[^}]+)\}")


@dataclass(frozen=True)
class RangeItem:
    kind: str
    title: str
    start_line: int
    end_line: int


@dataclass(frozen=True)
class Statement:
    kind: str
    title: str
    start_line: int
    end_line: int
    label: str | None
    proof_start: int | None
    proof_end: int | None


@dataclass(frozen=True)
class Equation:
    tag: str
    start_line: int
    end_line: int
    preview: str


def normalize_tex(text: str) -> str:
    text = re.sub(r"%.*", "", text)
    text = re.sub(r"\\(?:textup|textbf|emph|texorpdfstring)\{([^{}]*)\}", r"\1", text)
    text = re.sub(r"\\[A-Za-z@]+\*?(?:\[[^]]*\])?", " ", text)
    text = text.replace("{", " ").replace("}", " ")
    text = re.sub(r"\s+", " ", text)
    return text.strip()


def display_start_at(lines: list[str], tag_index: int) -> int:
    depth = 0
    for index in range(tag_index, -1, -1):
        line = lines[index]
        if "\\]" in line:
            depth += line.count("\\]")
        if "\\[" in line:
            if depth == 0:
                return index + 1
            depth -= line.count("\\[")
        if re.search(r"\\begin\{(?:equation\*?|align\*?|gather\*?|multline\*?)\}", line):
            return index + 1
    return tag_index + 1


def display_end_at(lines: list[str], tag_index: int) -> int:
    for index in range(tag_index, len(lines)):
        line = lines[index]
        if "\\]" in line or re.search(
            r"\\end\{(?:equation\*?|align\*?|gather\*?|multline\*?)\}", line
        ):
            return index + 1
        if index > tag_index and STATEMENT_BEGIN_RE.search(line):
            break
    return tag_index + 1


def next_nonempty_preview(lines: list[str], start: int, end: int) -> str:
    pieces: list[str] = []
    for line in lines[start - 1 : end]:
        cleaned = normalize_tex(line)
        if cleaned:
            pieces.append(cleaned)
        if sum(len(piece) for piece in pieces) >= 150:
            break
    preview = " ".join(pieces)
    return preview[:180]


def find_end_environment(lines: list[str], start_index: int, environment: str) -> int:
    token = f"\\end{{{environment}}}"
    for index in range(start_index + 1, len(lines)):
        if token in lines[index]:
            return index + 1
    raise RuntimeError(f"unclosed environment {environment} at line {start_index + 1}")


def find_statement_label(lines: list[str], start_line: int, end_line: int) -> str | None:
    lower = max(0, start_line - 8)
    upper = min(len(lines), end_line)
    labels: list[str] = []
    for line in lines[lower:upper]:
        labels.extend(match.group("label") for match in LABEL_RE.finditer(line))
    return labels[-1] if labels else None


def find_proof_range(
    lines: list[str], statement_end: int, next_statement_start: int | None
) -> tuple[int | None, int | None]:
    search_end = (next_statement_start - 1) if next_statement_start else len(lines)
    proof_start: int | None = None
    for index in range(statement_end, search_end):
        line = lines[index]
        paragraph = PARAGRAPH_RE.search(line)
        if paragraph and paragraph.group("title").lower().startswith("proof"):
            proof_start = index + 1
            break
        if "\\begin{proof}" in line:
            proof_start = index + 1
            break
        if SECTION_RE.search(line) or STATEMENT_BEGIN_RE.search(line):
            break
    if proof_start is None:
        return None, None
    for index in range(proof_start - 1, search_end):
        line = lines[index]
        if "\\square" in line or "\\end{proof}" in line:
            return proof_start, index + 1
        if index + 1 > proof_start and SECTION_RE.search(line):
            return proof_start, index
    return proof_start, search_end


def collect_ranges(lines: list[str]) -> list[RangeItem]:
    starts: list[tuple[str, str, int]] = []
    for index, line in enumerate(lines, start=1):
        section = SECTION_RE.search(line)
        if section:
            starts.append((section.group("kind"), normalize_tex(section.group("title")), index))
            continue
        heading = DISPLAY_HEADING_RE.search(line)
        if heading:
            starts.append(("displayheading", normalize_tex(heading.group("title")), index))
            continue
        paragraph = PARAGRAPH_RE.search(line)
        if paragraph:
            starts.append(("paragraph", normalize_tex(paragraph.group("title")), index))
    result: list[RangeItem] = []
    for pos, (kind, title, start) in enumerate(starts):
        end = starts[pos + 1][2] - 1 if pos + 1 < len(starts) else len(lines)
        result.append(RangeItem(kind, title, start, end))
    return result


def collect_statements(lines: list[str]) -> list[Statement]:
    raw: list[tuple[str, str, int, int]] = []
    for index, line in enumerate(lines):
        match = STATEMENT_BEGIN_RE.search(line)
        if not match:
            continue
        kind = match.group("kind")
        title = normalize_tex(match.group("title"))
        end = find_end_environment(lines, index, kind)
        raw.append((kind, title, index + 1, end))
    statements: list[Statement] = []
    for pos, (kind, title, start, end) in enumerate(raw):
        next_start = raw[pos + 1][2] if pos + 1 < len(raw) else None
        proof_start, proof_end = find_proof_range(lines, end, next_start)
        statements.append(
            Statement(
                kind=kind,
                title=title,
                start_line=start,
                end_line=end,
                label=find_statement_label(lines, start, end),
                proof_start=proof_start,
                proof_end=proof_end,
            )
        )
    return statements


def collect_equations(lines: list[str]) -> list[Equation]:
    equations: list[Equation] = []
    for index, line in enumerate(lines):
        for match in TAG_RE.finditer(line):
            start = display_start_at(lines, index)
            end = display_end_at(lines, index)
            equations.append(
                Equation(
                    tag=match.group("tag"),
                    start_line=start,
                    end_line=end,
                    preview=next_nonempty_preview(lines, start, end),
                )
            )
    return equations


def collect_labels(lines: list[str]) -> dict[str, list[int]]:
    result: dict[str, list[int]] = {}
    for index, line in enumerate(lines, start=1):
        for match in LABEL_RE.finditer(line):
            result.setdefault(match.group("label"), []).append(index)
    return result


def collect_references(lines: list[str]) -> dict[str, list[int]]:
    result: dict[str, list[int]] = {}
    for index, line in enumerate(lines, start=1):
        for match in REFERENCE_RE.finditer(line):
            result.setdefault(match.group("label"), []).append(index)
    return result


def collect_citations(lines: list[str]) -> dict[str, list[int]]:
    result: dict[str, list[int]] = {}
    for index, line in enumerate(lines, start=1):
        for match in CITATION_RE.finditer(line):
            for key in match.group("keys").split(","):
                result.setdefault(key.strip(), []).append(index)
    return result


def risk_flags(lines: list[str], statements: list[Statement]) -> list[tuple[str, int, str]]:
    flags: list[tuple[str, int, str]] = []
    patterns: tuple[tuple[str, re.Pattern[str]], ...] = (
        ("UNCONDITIONAL_CLAIM", re.compile(r"\bWe prove\b")),
        ("KNOWN_TEX_TYPO", re.compile(r"2\^\\ell_\\bullet")),
        ("DECIMAL_CERTIFICATE", re.compile(r"\b0\.\d{3,}")),
        ("IMPRECISE_RANGE", re.compile(r"[+\-]O\(1\)")),
        ("ASYMPTOTIC_PLACEHOLDER", re.compile(r"\bo\(1\)\b")),
    )
    for index, line in enumerate(lines, start=1):
        stripped = re.sub(r"%.*", "", line)
        for name, pattern in patterns:
            if pattern.search(stripped):
                flags.append((name, index, normalize_tex(stripped)))
    for statement in statements:
        if statement.proof_start is None:
            flags.append(
                ("NO_LOCAL_PROOF", statement.start_line, f"{statement.title}: no following proof block")
            )
    return flags


def duplicate_values(mapping: dict[str, list[int]]) -> dict[str, list[int]]:
    return {key: value for key, value in mapping.items() if len(value) > 1}


def render_markdown(
    source: Path,
    lines: list[str],
    ranges: list[RangeItem],
    statements: list[Statement],
    equations: list[Equation],
    labels: dict[str, list[int]],
    references: dict[str, list[int]],
    citations: dict[str, list[int]],
    flags: list[tuple[str, int, str]],
) -> str:
    missing_references = sorted(set(references) - set(labels))
    duplicate_labels = duplicate_values(labels)
    duplicate_tags = duplicate_values(
        {tag: [eq.start_line for eq in equations if eq.tag == tag] for tag in {eq.tag for eq in equations}}
    )

    out: list[str] = []
    out.append("# Generated source map for the Erdős 625 canonical TeX")
    out.append("")
    out.append(f"- Source: `{source.as_posix()}`")
    out.append(f"- Lines: `{len(lines)}`")
    out.append(f"- Boxed statements: `{len(statements)}`")
    out.append(f"- Tagged displays: `{len(equations)}`")
    out.append(f"- Labels: `{len(labels)}`")
    out.append(f"- Citation keys used: `{len(citations)}`")
    out.append("")
    out.append("> This file is a mechanical coverage map, not a mathematical verdict.")
    out.append("")

    out.append("## Section and paragraph ranges")
    out.append("")
    out.append("| Kind | Lines | Heading |")
    out.append("|---|---:|---|")
    for item in ranges:
        out.append(f"| `{item.kind}` | {item.start_line}–{item.end_line} | {item.title or '—'} |")
    out.append("")

    out.append("## Boxed theorem/lemma/proposition ledger")
    out.append("")
    out.append("| # | Kind | Statement lines | Proof lines | Label | Title |")
    out.append("|---:|---|---:|---:|---|---|")
    for number, statement in enumerate(statements, start=1):
        proof = (
            f"{statement.proof_start}–{statement.proof_end}"
            if statement.proof_start is not None and statement.proof_end is not None
            else "—"
        )
        out.append(
            f"| {number} | `{statement.kind}` | {statement.start_line}–{statement.end_line} "
            f"| {proof} | `{statement.label or '—'}` | {statement.title} |"
        )
    out.append("")

    out.append("## Tagged-display ledger")
    out.append("")
    out.append("| Tag | Lines | Preview |")
    out.append("|---|---:|---|")
    for equation in equations:
        preview = equation.preview.replace("|", "\\|")
        out.append(f"| `{equation.tag}` | {equation.start_line}–{equation.end_line} | {preview} |")
    out.append("")

    out.append("## Mechanical consistency checks")
    out.append("")
    out.append(f"- Duplicate labels: `{json.dumps(duplicate_labels, sort_keys=True)}`")
    out.append(f"- Duplicate equation tags: `{json.dumps(duplicate_tags, sort_keys=True)}`")
    out.append(f"- References to missing labels: `{json.dumps(missing_references)}`")
    out.append("")

    out.append("## Audit-risk flags")
    out.append("")
    out.append("| Class | Line | Source preview |")
    out.append("|---|---:|---|")
    for name, line, preview in flags:
        out.append(f"| `{name}` | {line} | {preview.replace('|', '\\|')} |")
    out.append("")

    out.append("## Machine-readable statement manifest")
    out.append("")
    out.append("```json")
    out.append(json.dumps([asdict(statement) for statement in statements], indent=2, sort_keys=True))
    out.append("```")
    out.append("")
    return "\n".join(out)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "source",
        nargs="?",
        type=Path,
        default=Path("625/arxiv/main.tex"),
    )
    parser.add_argument("--output", type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    source: Path = args.source
    lines = source.read_text(encoding="utf-8").splitlines()
    ranges = collect_ranges(lines)
    statements = collect_statements(lines)
    equations = collect_equations(lines)
    labels = collect_labels(lines)
    references = collect_references(lines)
    citations = collect_citations(lines)
    flags = risk_flags(lines, statements)
    rendered = render_markdown(
        source,
        lines,
        ranges,
        statements,
        equations,
        labels,
        references,
        citations,
        flags,
    )
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    else:
        print(rendered)


if __name__ == "__main__":
    main()
