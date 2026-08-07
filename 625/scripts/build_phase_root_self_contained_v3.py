#!/usr/bin/env python3
"""Assemble the theorem-facing Version 3 manuscript.

The canonical source remains frozen. This wrapper first invokes the existing
Version 3 generator, replaces the legacy phase and root sections by auditable
sources, and inserts the explicit Section 8--9 logarithmic ledger before the
amplification section.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEGACY_GENERATOR = ROOT / "scripts" / "build_self_contained_ams_v3.py"
DEFAULT_SOURCE = ROOT / "arxiv" / "main.tex"
DEFAULT_OUTPUT = ROOT / "arxiv" / "AMS_SELF_CONTAINED_BODY_V3.generated.tex"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def replace_once(text: str, start: str, end: str, replacement: str) -> str:
    """Replace the unique marker-delimited block and retain the end marker."""
    require(text.count(start) == 1, f"expected one start marker {start!r}")
    require(text.count(end) == 1, f"expected one end marker {end!r}")
    begin = text.index(start)
    finish = text.index(end, begin + len(start))
    require(begin < finish, f"reversed replacement markers: {start!r}, {end!r}")
    return text[:begin] + replacement + text[finish:]


def generate(source: Path, output: Path) -> None:
    for path in (
        LEGACY_GENERATOR,
        ROOT / "arxiv" / "SECTION2_PHASE_PACKAGE_V3.tex",
        ROOT / "arxiv" / "SECTION3_ROOT_GEOMETRY_V3.tex",
        ROOT / "arxiv" / "SECTION9_EXPLICIT_GLOBAL_LEDGER_V3.tex",
    ):
        require(path.is_file(), f"missing theorem-facing source: {path}")

    subprocess.run(
        [
            sys.executable,
            str(LEGACY_GENERATOR),
            "--source",
            str(source),
            "--output",
            str(output),
        ],
        cwd=ROOT.parent,
        check=True,
    )
    text = output.read_text(encoding="utf-8")

    text = replace_once(
        text,
        r"\section{The complete independence-number phase}",
        r"\section{Continuous profile roots}",
        r"\input{SECTION2_PHASE_PACKAGE_V3}" + "\n\n",
    )
    text = replace_once(
        text,
        r"\section{Continuous profile roots}",
        r"\input{SECTION4_CHROMATIC_LOWER_TAIL_V3}",
        r"\input{SECTION3_ROOT_GEOMETRY_V3}" + "\n\n",
    )

    section9_anchor = r"\input{SECTION9_SELF_CONTAINED_V3}"
    require(
        text.count(section9_anchor) == 1,
        "expected one Section 9 source marker",
    )
    text = text.replace(
        section9_anchor,
        section9_anchor
        + "\n\n"
        + r"\input{SECTION9_EXPLICIT_GLOBAL_LEDGER_V3}",
        1,
    )

    require(
        text.count(r"\input{SECTION2_PHASE_PACKAGE_V3}") == 1,
        "Section 2 replacement was not inserted exactly once",
    )
    require(
        text.count(r"\input{SECTION3_ROOT_GEOMETRY_V3}") == 1,
        "Section 3 replacement was not inserted exactly once",
    )
    require(
        text.count(r"\input{SECTION9_EXPLICIT_GLOBAL_LEDGER_V3}") == 1,
        "global second-moment ledger was not inserted exactly once",
    )
    require(
        r"\section{The complete independence-number phase}" not in text,
        "legacy Section 2 remains in the generated body",
    )
    require(
        r"\section{Continuous profile roots}" not in text,
        "legacy Section 3 remains in the generated body",
    )

    output.write_text(text, encoding="utf-8")
    print(f"generated theorem-facing manuscript body: {output}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    generate(args.source, args.output)


if __name__ == "__main__":
    main()
