#!/usr/bin/env python3
"""Generate a mechanical source map for the canonical Erdős 625 TeX.

This standard-library script inventories boxed statements, proof ranges,
tagged displays, labels, references, and known audit-risk patterns. It does not
make mathematical truth judgments.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path


BOX_RE = re.compile(
    r"\\begin\{(?P<kind>resultbox|lemmabox|propositionbox)\}"
    r"\{(?P<title>[^}]*)\}"
)
TAG_RE = re.compile(r"\\tag\{([^}]+)\}")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
REF_RE = re.compile(r"\\(?:eqref|ref|autoref)\{([^}]+)\}")
PROOF_RE = re.compile(r"\\(?:paragraph\{Proof[^}]*\}|begin\{proof\})")
SECTION_RE = re.compile(r"\\(?:section\*?|subsection\*?)\{")


@dataclass(frozen=True)
class Statement:
    kind: str
    title: str
    statement_start: int
    statement_end: int
    proof_start: int | None
    proof_end: int | None


@dataclass(frozen=True)
class Display:
    tag: str
    line: int
    preview: str


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def strip_tex(line: str) -> str:
    line = re.sub(r"%.*", "", line)
    line = re.sub(r"\\[A-Za-z@]+\*?(?:\[[^]]*\])?", " ", line)
    line = line.replace("{", " ").replace("}", " ")
    return re.sub(r"\s+", " ", line).strip()


def find_environment_end(lines: list[str], start: int, kind: str) -> int:
    token = f"\\end{{{kind}}}"
    for index in range(start, len(lines)):
        if token in lines[index]:
            return index + 1
    raise RuntimeError(f"unclosed {kind} environment at line {start + 1}")


def find_proof(
    lines: list[str], statement_end: int, next_statement_start: int | None
) -> tuple[int | None, int | None]:
    limit = next_statement_start - 1 if next_statement_start else len(lines)
    proof_start: int | None = None
    for index in range(statement_end, limit):
        if PROOF_RE.search(lines[index]):
            proof_start = index + 1
            break
        if SECTION_RE.search(lines[index]) or BOX_RE.search(lines[index]):
            break
    if proof_start is None:
        return None, None
    for index in range(proof_start - 1, limit):
        if "\\square" in lines[index] or "\\end{proof}" in lines[index]:
            return proof_start, index + 1
    return proof_start, limit


def collect_statements(lines: list[str]) -> list[Statement]:
    raw: list[tuple[str, str, int, int]] = []
    for index, line in enumerate(lines):
        match = BOX_RE.search(line)
        if match:
            kind = match.group("kind")
            raw.append(
                (
                    kind,
                    match.group("title").strip(),
                    index + 1,
                    find_environment_end(lines, index, kind),
                )
            )
    result: list[Statement] = []
    for position, (kind, title, start, end) in enumerate(raw):
        next_start = raw[position + 1][2] if position + 1 < len(raw) else None
        proof_start, proof_end = find_proof(lines, end, next_start)
        result.append(Statement(kind, title, start, end, proof_start, proof_end))
    return result


def collect_displays(lines: list[str]) -> list[Display]:
    displays: list[Display] = []
    for index, line in enumerate(lines, start=1):
        for match in TAG_RE.finditer(line):
            lo = max(0, index - 4)
            hi = min(len(lines), index + 3)
            preview = " ".join(
                part for part in (strip_tex(item) for item in lines[lo:hi]) if part
            )[:180]
            displays.append(Display(match.group(1), index, preview))
    return displays


def collect_occurrences(lines: list[str], pattern: re.Pattern[str]) -> dict[str, list[int]]:
    result: dict[str, list[int]] = {}
    for index, line in enumerate(lines, start=1):
        for match in pattern.finditer(line):
            result.setdefault(match.group(1), []).append(index)
    return result


def collect_flags(lines: list[str], statements: list[Statement]) -> list[dict[str, object]]:
    patterns = (
        ("UNCONDITIONAL_CLAIM", re.compile(r"\bWe prove\b")),
        ("KNOWN_TEX_TYPO", re.compile(r"2\^\\ell_\\bullet")),
        ("DECIMAL_CERTIFICATE", re.compile(r"\b0\.\d{3,}")),
        ("IMPRECISE_FINITE_RANGE", re.compile(r"[+\-]O\(1\)")),
        ("ASYMPTOTIC_PLACEHOLDER", re.compile(r"o\(1\)")),
    )
    flags: list[dict[str, object]] = []
    for index, line in enumerate(lines, start=1):
        visible = re.sub(r"%.*", "", line)
        for name, pattern in patterns:
            if pattern.search(visible):
                flags.append({"kind": name, "line": index, "preview": strip_tex(visible)})
    for statement in statements:
        if statement.proof_start is None:
            flags.append(
                {
                    "kind": "NO_LOCAL_PROOF",
                    "line": statement.statement_start,
                    "preview": statement.title,
                }
            )
    return flags


def render(
    source: Path,
    lines: list[str],
    statements: list[Statement],
    displays: list[Display],
    labels: dict[str, list[int]],
    references: dict[str, list[int]],
    flags: list[dict[str, object]],
) -> str:
    duplicate_labels = {key: value for key, value in labels.items() if len(value) > 1}
    missing_references = sorted(set(references) - set(labels))
    tag_counts: dict[str, int] = {}
    for display in displays:
        tag_counts[display.tag] = tag_counts.get(display.tag, 0) + 1
    duplicate_tags = sorted(tag for tag, count in tag_counts.items() if count > 1)

    out = [
        "# Generated source map for the Erdős 625 canonical TeX",
        "",
        f"- Source: `{source.as_posix()}`",
        f"- Lines: `{len(lines)}`",
        f"- Boxed statements: `{len(statements)}`",
        f"- Tagged displays: `{len(displays)}`",
        "",
        "> Mechanical coverage only; mathematical verdicts are in the human audit.",
        "",
        "## Boxed statement ledger",
        "",
        "| # | Kind | Statement lines | Proof lines | Title |",
        "|---:|---|---:|---:|---|",
    ]
    for number, statement in enumerate(statements, start=1):
        proof = (
            f"{statement.proof_start}–{statement.proof_end}"
            if statement.proof_start and statement.proof_end
            else "—"
        )
        out.append(
            f"| {number} | `{statement.kind}` | "
            f"{statement.statement_start}–{statement.statement_end} | {proof} | "
            f"{statement.title} |"
        )

    out.extend(["", "## Tagged-display ledger", "", "| Tag | Line | Preview |", "|---|---:|---|"])
    for display in displays:
        out.append(f"| `{display.tag}` | {display.line} | {display.preview.replace('|', '/') } |")

    out.extend(
        [
            "",
            "## Mechanical consistency",
            "",
            f"- Duplicate labels: `{json.dumps(duplicate_labels, sort_keys=True)}`",
            f"- Duplicate tags: `{json.dumps(duplicate_tags)}`",
            f"- References to missing labels: `{json.dumps(missing_references)}`",
            "",
            "## Audit-risk flags",
            "",
            "| Kind | Line | Preview |",
            "|---|---:|---|",
        ]
    )
    for flag in flags:
        preview = str(flag["preview"]).replace("|", "/")
        out.append(f"| `{flag['kind']}` | {flag['line']} | {preview} |")

    out.extend(
        [
            "",
            "## Machine-readable statement manifest",
            "",
            "```json",
            json.dumps([asdict(statement) for statement in statements], indent=2),
            "```",
            "",
        ]
    )
    return "\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", nargs="?", type=Path, default=Path("625/arxiv/main.tex"))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    lines = args.source.read_text(encoding="utf-8").splitlines()
    statements = collect_statements(lines)
    displays = collect_displays(lines)
    labels = collect_occurrences(lines, LABEL_RE)
    references = collect_occurrences(lines, REF_RE)
    flags = collect_flags(lines, statements)
    output = render(args.source, lines, statements, displays, labels, references, flags)

    require(len(statements) >= 14, "too few boxed statements found")
    require(any(statement.title == "Theorem 1" for statement in statements), "Theorem 1 absent")
    require(any(statement.title.startswith("Proposition 9.2") for statement in statements), "Proposition 9.2 absent")

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output, encoding="utf-8")
    else:
        print(output)


if __name__ == "__main__":
    main()
