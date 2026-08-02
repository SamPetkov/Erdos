#!/usr/bin/env python3
"""Validate the copy-ready AMS-style Erdős 625 manuscript fragments.

The checks are editorial and structural. They do not validate any theorem.
"""

from __future__ import annotations

import re
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
ARXIV = ROOT / "625" / "arxiv"

FILES = {
    "driver": ARXIV / "AMS_EDITORIAL_DRAFT_V2.tex",
    "theorems": ARXIV / "AMS_THEOREM_ENVIRONMENTS_V2.tex",
    "frontmatter": ARXIV / "FRONTMATTER_INTRODUCTION_POSTCLOSURE_V2.tex",
    "roadmap": ARXIV / "PROOF_ROADMAP_INSERT_V2.tex",
    "section8": ARXIV / "SECTION8_ALL_DEFICIT_AMS_V2.tex",
    "section9": ARXIV / "SECTION9_Q_ONLY_AMS_V2.tex",
    "canonical": ARXIV / "main.tex",
}

BANNED_PROSE = {
    "exquisitely": "replace promotional language by a quantitative statement",
    "delicate point": "state the precise mathematical obstruction instead",
    "obviously": "cite the reason",
    "clearly": "cite the reason",
    "normalised": "use American spelling: normalized",
    "colouring": "use American spelling: coloring",
    "cocolouring": "use American spelling: cocoloring",
}

REQUIRED_FRONTMATTER = (
    "All graphs in this paper are finite, simple, and undirected.",
    "\\emph{cocoloring} of a graph",
    "with high probability",
    "The proof has three stages.",
    "Exact finite identities, deterministic inequalities, asymptotic estimates",
)

REQUIRED_SECTION8 = (
    "Aggregate high-skeleton weight",
    "Exact local ratio",
    "Aggregate deficit comparison",
    "Finite optional-choice identity",
    "Weighted reference regrouping",
    "The order of this argument is important",
)

REQUIRED_SECTION9 = (
    "Restriction-product bound",
    "One activity controls both residual factors",
    "Uniform residual attachment bound",
    "Attained attachment sum",
    "does not require a choice of cycle decomposition",
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def read(path: Path) -> str:
    require(path.is_file(), f"missing file: {path}")
    return path.read_text(encoding="utf-8")


def strip_comments(text: str) -> str:
    return "\n".join(line.split("%", 1)[0] for line in text.splitlines())


def normalize_source_whitespace(text: str) -> str:
    """Collapse TeX source whitespace without altering commands or braces."""

    return re.sub(r"\s+", " ", strip_comments(text)).strip()


def strip_tex_for_words(text: str) -> str:
    text = strip_comments(text)
    text = re.sub(r"\\\[[\s\S]*?\\\]", " ", text)
    text = re.sub(r"\$[^$]*\$", " ", text)
    text = re.sub(r"\\[A-Za-z@]+\*?(?:\[[^]]*\])?", " ", text)
    text = text.replace("{", " ").replace("}", " ")
    text = re.sub(r"[^A-Za-z0-9'-]+", " ", text)
    return re.sub(r"\s+", " ", text).strip()


def abstract_word_count(frontmatter: str) -> int:
    match = re.search(
        r"\\begin\{abstract\}(.*?)\\end\{abstract\}",
        frontmatter,
        flags=re.DOTALL,
    )
    require(match is not None, "abstract environment missing")
    words = strip_tex_for_words(match.group(1)).split()
    return len(words)


def check_environment_balance(name: str, text: str) -> None:
    begins = Counter(re.findall(r"\\begin\{([^}]+)\}", strip_comments(text)))
    ends = Counter(re.findall(r"\\end\{([^}]+)\}", strip_comments(text)))
    require(begins == ends, f"{name}: unmatched environments: {begins} != {ends}")


def check_group_braces(name: str, text: str) -> None:
    """Check grouping braces, ignoring the printed delimiters ``\{`` and ``\}``."""

    source = strip_comments(text).replace(r"\{", "").replace(r"\}", "")
    depth = 0
    for line_number, line in enumerate(source.splitlines(), start=1):
        for character in line:
            if character == "{":
                depth += 1
            elif character == "}":
                depth -= 1
                require(depth >= 0, f"{name}: unmatched closing brace at line {line_number}")
    require(depth == 0, f"{name}: {depth} unmatched opening grouping brace(s)")


def check_labels(texts: dict[str, str]) -> None:
    labels: dict[str, list[str]] = {}
    for name, text in texts.items():
        for label in re.findall(r"\\label\{([^}]+)\}", strip_comments(text)):
            labels.setdefault(label, []).append(name)
    duplicates = {label: owners for label, owners in labels.items() if len(owners) > 1}
    require(not duplicates, f"duplicate labels in editorial draft: {duplicates}")


def check_prose(texts: dict[str, str]) -> None:
    joined = "\n".join(strip_comments(text) for text in texts.values()).lower()
    for phrase, advice in BANNED_PROSE.items():
        require(phrase not in joined, f"banned phrase {phrase!r}: {advice}")


def check_no_manual_tags(texts: dict[str, str]) -> None:
    for name, text in texts.items():
        require("\\tag{" not in strip_comments(text), f"{name}: manual equation tag present")


def check_required(text: str, markers: tuple[str, ...], label: str) -> None:
    normalized_text = normalize_source_whitespace(text)
    missing = [
        marker
        for marker in markers
        if normalize_source_whitespace(marker) not in normalized_text
    ]
    require(not missing, f"{label}: missing clarity markers {missing}")


def main() -> None:
    texts = {name: read(path) for name, path in FILES.items()}
    draft_texts = {name: text for name, text in texts.items() if name != "canonical"}

    count = abstract_word_count(texts["frontmatter"])
    require(80 <= count <= 150, f"abstract word count {count} is outside 80--150")

    theorem_text = texts["theorems"]
    require("\\theoremstyle{plain}" in theorem_text, "plain theorem style missing")
    require("\\theoremstyle{definition}" in theorem_text, "definition theorem style missing")
    require("\\theoremstyle{remark}" in theorem_text, "remark theorem style missing")
    require("resultbox" not in theorem_text, "custom result boxes remain in theorem file")
    require("xcolor" not in texts["driver"], "editorial driver should not color theorem statements")

    check_required(texts["frontmatter"], REQUIRED_FRONTMATTER, "front matter")
    check_required(texts["section8"], REQUIRED_SECTION8, "Section VIII rewrite")
    check_required(texts["section9"], REQUIRED_SECTION9, "Section IX rewrite")

    check_prose(draft_texts)
    check_no_manual_tags(draft_texts)
    check_labels(draft_texts)

    for name, text in draft_texts.items():
        check_environment_balance(name, text)
        check_group_braces(name, text)
        require("TODO" not in text and "TBD" not in text, f"{name}: unresolved placeholder")

    canonical = texts["canonical"]
    for filename in (
        "FRONTMATTER_INTRODUCTION_POSTCLOSURE_V2",
        "PROOF_ROADMAP_INSERT_V2",
        "SECTION8_ALL_DEFICIT_AMS_V2",
        "SECTION9_Q_ONLY_AMS_V2",
    ):
        require(filename not in canonical, f"canonical main.tex already imports {filename}")

    driver = texts["driver"]
    for filename in (
        "AMS_THEOREM_ENVIRONMENTS_V2",
        "FRONTMATTER_INTRODUCTION_POSTCLOSURE_V2",
        "PROOF_ROADMAP_INSERT_V2",
        "SECTION8_ALL_DEFICIT_AMS_V2",
        "SECTION9_Q_ONLY_AMS_V2",
    ):
        require(f"\\input{{{filename}}}" in driver, f"driver omits {filename}")

    print("ERDOS 625 AMS MANUSCRIPT CLARITY CHECK: PASS")
    print(f"  abstract words: {count}")
    print(f"  draft fragments: {len(draft_texts)}")
    print("  standard theorem hierarchy: present")
    print("  manual equation tags: none")
    print("  duplicate labels: none")
    print("  canonical main.tex: unchanged and does not import post-closure text")
    print("  scope: editorial structure only; no theorem validation")


if __name__ == "__main__":
    main()
