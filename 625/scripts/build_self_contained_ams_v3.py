#!/usr/bin/env python3
"""Generate the complete AMS Version 3 manuscript body.

The canonical TeX remains frozen while the proof is incomplete. This script
extracts the complete Sections 1--7 and 10 from that source, converts their
legacy theorem and proof markup to the ordinary AMS hierarchy, applies a small
set of line-audited prose normalizations, and inserts the replacement Sections
8, 9, and 11. The canonical Git-blob SHA is checked before line-independent
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
    # draft. Labels immediately following theorem statements are retained.
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

    # Convert the legacy paragraph proofs to genuine amsthm proof environments.
    # Section 7 has one proof divided into three named ranges, so it is handled
    # separately before the generic proof conversion.
    text = re.sub(
        r"\\paragraph\{Proof: the empty corner\.\}\\label\{[^}]+\}\s*",
        r"\\begin{proof}\n\\displayheading{Empty corner}\n",
        text,
    )
    text = re.sub(
        r"\\paragraph\{Proof: the central range\.\}\\label\{[^}]+\}\s*",
        r"\\displayheading{Central range}\n",
        text,
    )
    text = re.sub(
        r"\\paragraph\{Proof: the full corner\.\}\\label\{[^}]+\}\s*",
        r"\\displayheading{Full corner}\n",
        text,
    )
    text = re.sub(
        r"\\paragraph\{Proof\.\}\\label\{[^}]+\}\s*",
        r"\\begin{proof}\n",
        text,
    )
    text = text.replace(r"\(\square\)", r"\end{proof}")

    # Normalize mathematical English and notation without changing any finite
    # identity, hypothesis, quantifier, or summation domain.
    replacements = {
        r"\ln": r"\log",
        r"\log2": r"\log 2",
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

    prose_replacements = {
        (
            "The profile optimization has two jobs. It must locate the zero of the\n"
            "first-moment exponent, and it must compare two different supports at the\n"
            "same average class size. The affine part of the deficit weight cancels under\n"
            "the fixed-mean constraint; only the curved part distinguishes the supports.\n"
            "The following lemma packages both facts, together with the uniform derivative\n"
            "needed to convert an entropy advantage into a root displacement."
        ): (
            "The profile optimization serves two purposes: it locates the first-moment\n"
            "root and compares two supports at the same mean class size. Under the\n"
            "fixed-mean constraint the affine deficit term cancels, so only the curved\n"
            "term distinguishes the supports. The next lemma collects the root corridor,\n"
            "the uniform slope, and the support comparison used below."
        ),
        (
            "It is proved directly for the four-size signed profile, including both\n"
            "corners and every intermediate mass, and no tame-profile theorem is invoked."
        ): (
            "We prove it directly for the four-size signed profile, uniformly at both\n"
            "corners and throughout the intermediate range; no external tame-profile\n"
            "theorem is used."
        ),
        (
            "The proof has three ranges, classified by the vertex mass occupied by the\n"
            "marked common classes."
        ): (
            "We split the common-subprofile sum according to the vertex mass occupied by\n"
            "the marked classes."
        ),
        (
            "We use the same seed-to-typical strategic principle, but not that theorem as a black box:\n"
            "Lemma 10.2 proves the quantitative implication needed here for an arbitrary\n"
            "seed exponent \\(\\Lambda_n\\), and Lemma 10.1 supplies the simultaneous\n"
            "leftover coloring that controls the added parts."
        ): (
            "The amplification follows the same seed-to-typical principle, but the form\n"
            "needed here is proved inside the paper. Lemma 10.2 treats an arbitrary seed\n"
            "exponent \\(\\Lambda_n\\), and Lemma 10.1 supplies a simultaneous coloring\n"
            "bound for every leftover vertex set."
        ),
    }
    for old, new in prose_replacements.items():
        text = text.replace(old, new)

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
