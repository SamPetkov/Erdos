#!/usr/bin/env python3
"""Generate the complete AMS Version 3 manuscript body.

The canonical TeX remains frozen while the proof is incomplete. This script
extracts the complete Sections 1--7 and 10 from that source, normalizes their
legacy statement environments, and inserts the audited replacement Sections 8,
9, and 11. The exact canonical Git-blob SHA is checked before line-independent
section markers are used.
"""

from __future__ import annotations

import argparse
import hashlib
import re
from pathlib import Path


EXPECTED_CANONICAL_BLOB = "c4d090b73cd5efcdb98cc30f79bb5f53c6c9bc97"

START_SECTION_1 = r"\section{Notation and elementary"
START_SECTION_8 = r"\section{Canonical high cells and dense endpoint"
START_SECTION_10 = r"\section{Rare-event amplification}"
START_SECTION_11 = r"\section{Completion of the proof}"


def git_blob_sha(raw: bytes) -> str:
    header = f"blob {len(raw)}\0".encode("ascii")
    return hashlib.sha1(header + raw).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def slice_between(text: str, start: str, end: str) -> str:
    begin = text.find(start)
    finish = text.find(end)
    require(begin >= 0, f"missing start marker: {start}")
    require(finish >= 0, f"missing end marker: {end}")
    require(begin < finish, f"reversed markers: {start!r}, {end!r}")
    return text[begin:finish]


def normalize_legacy_section(text: str) -> str:
    # Remove navigation-only commands that are redundant in the generated AMS
    # draft. Labels immediately following them are retained.
    text = re.sub(r"(?m)^\\phantomsection\s*$\n?", "", text)
    text = re.sub(
        r"(?m)^\\addcontentsline\{toc\}\{subsection\}\{[^\n]*\}\s*$\n?",
        "",
        text,
    )

    # Convert the ruled legacy boxes to the ordinary amsthm hierarchy. The
    # source labels occur immediately before the environments and remain valid.
    text = re.sub(
        r"\\begin\{lemmabox\}\{Lemma\s+[0-9.]+\s+\(([^{}]*)\)\}",
        r"\\begin{lemma}[\1]",
        text,
    )
    text = re.sub(
        r"\\begin\{propositionbox\}\{Proposition\s+[0-9.]+\s+\(([^{}]*)\)\}",
        r"\\begin{proposition}[\1]",
        text,
    )
    text = re.sub(
        r"\\begin\{resultbox\}\{Theorem\s+[0-9.]+\}",
        r"\\begin{theorem}",
        text,
    )
    text = text.replace(r"\end{lemmabox}", r"\end{lemma}")
    text = text.replace(r"\end{propositionbox}", r"\end{proposition}")
    text = text.replace(r"\end{resultbox}", r"\end{theorem}")

    # Normalize the mathematical English and notation without altering any
    # finite identity, hypothesis, or summation domain.
    replacements = {
        r"\ln": r"\log",
        "colouring": "coloring",
        "colourings": "colorings",
        "coloured": "colored",
        "colour": "color",
        "cocolouring": "cocoloring",
        "cocolourings": "cocolorings",
        "cocolourable": "cocolorable",
        "fibre": "fiber",
        "fibres": "fibers",
        "neighbourhood": "neighborhood",
        "neighbourhoods": "neighborhoods",
        "catalogued": "cataloged",
    }
    for old, new in replacements.items():
        text = text.replace(old, new)

    text = text.replace(
        "\\section{Notation and elementary\nfacts}",
        "\\section{Phase notation and elementary estimates}",
    )

    # Section 10 must point to the replacement normalized-second-moment
    # proposition rather than to the legacy proposition number.
    text = text.replace(
        "Proposition 9.2",
        "Proposition~\\ref{prop:normalized-second-moment-v3}",
    )
    return text


def generate(source: Path, output: Path) -> None:
    raw = source.read_bytes()
    blob = git_blob_sha(raw)
    require(
        blob == EXPECTED_CANONICAL_BLOB,
        f"canonical source drift: expected {EXPECTED_CANONICAL_BLOB}, found {blob}",
    )
    text = raw.decode("utf-8")

    sections_1_to_7 = normalize_legacy_section(
        slice_between(text, START_SECTION_1, START_SECTION_8)
    )
    section_10 = normalize_legacy_section(
        slice_between(text, START_SECTION_10, START_SECTION_11)
    )

    generated = "\n".join(
        [
            "% GENERATED FILE: do not edit directly.",
            f"% Canonical source Git blob: {blob}",
            "% Generator: 625/scripts/build_self_contained_ams_v3.py",
            "",
            sections_1_to_7.rstrip(),
            "",
            r"\input{SECTION8_SELF_CONTAINED_V3}",
            "",
            r"\input{SECTION9_SELF_CONTAINED_V3}",
            "",
            section_10.rstrip(),
            "",
            r"\input{FINAL_ASSEMBLY_SELF_CONTAINED_V3}",
            "",
        ]
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(generated, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    root = Path(__file__).resolve().parents[1]
    parser.add_argument(
        "--source",
        type=Path,
        default=root / "arxiv" / "main.tex",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=root / "arxiv" / "AMS_SELF_CONTAINED_BODY_V3.generated.tex",
    )
    args = parser.parse_args()
    generate(args.source, args.output)
    print(f"generated {args.output}")


if __name__ == "__main__":
    main()
