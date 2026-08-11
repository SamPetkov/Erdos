#!/usr/bin/env python3
"""Assemble the near-root Version 4 theorem-facing manuscript body.

The Version 3/PR59 body remains a frozen fallback. This wrapper invokes that
complete generator, replaces only the midpoint-profile block, the full-corner
adapter, and the final assembly, and writes a separate Version 4 body.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE_GENERATOR = ROOT / "scripts" / "build_phase_root_self_contained_v3.py"
DEFAULT_SOURCE = ROOT / "arxiv" / "main.tex"
DEFAULT_OUTPUT = ROOT / "arxiv" / "AMS_NEAR_ROOT_BODY_V4.generated.tex"

PROFILE_SOURCE = ROOT / "arxiv" / "SECTION5_NEAR_ROOT_PROFILE_V4.tex"
FULL_SOURCE = ROOT / "arxiv" / "SECTION7_FULL_CORNER_NEAR_ROOT_V4.tex"
FINAL_SOURCE = ROOT / "arxiv" / "FINAL_ASSEMBLY_NEAR_ROOT_V4.tex"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def replace_once(text: str, start: str, end: str, replacement: str) -> str:
    require(text.count(start) == 1, f"expected one start marker {start!r}")
    require(text.count(end) == 1, f"expected one end marker {end!r}")
    begin = text.index(start)
    finish = text.index(end, begin + len(start))
    require(begin < finish, f"reversed replacement markers: {start!r}, {end!r}")
    return text[:begin] + replacement + text[finish:]


def generate(source: Path, output: Path) -> None:
    for path in (BASE_GENERATOR, PROFILE_SOURCE, FULL_SOURCE, FINAL_SOURCE):
        require(path.is_file(), f"missing near-root source: {path}")

    subprocess.run(
        [
            sys.executable,
            str(BASE_GENERATOR),
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
        "Choose the midpoint integer",
        r"\section{Exact signed second-moment representation}",
        r"\input{SECTION5_NEAR_ROOT_PROFILE_V4}" + "\n\n",
    )

    stale_profile_reference = "For the exact midpoint profile,"
    require(
        text.count(stale_profile_reference) == 1,
        "expected one inherited midpoint reference in the partial-diagonal setup",
    )
    text = text.replace(
        stale_profile_reference,
        "For the exact one-part-buffer profile,",
        1,
    )

    old_full = r"\input{SECTION7_FULL_CORNER_V3}"
    new_full = r"\input{SECTION7_FULL_CORNER_NEAR_ROOT_V4}"
    require(text.count(old_full) == 1, "expected one Version 3 full-corner input")
    text = text.replace(old_full, new_full, 1)

    old_final = r"\input{FINAL_ASSEMBLY_SELF_CONTAINED_V3}"
    new_final = r"\input{FINAL_ASSEMBLY_NEAR_ROOT_V4}"
    require(text.count(old_final) == 1, "expected one Version 3 final assembly input")
    text = text.replace(old_final, new_final, 1)

    for marker in (
        r"\input{SECTION5_NEAR_ROOT_PROFILE_V4}",
        r"\input{SECTION7_FULL_CORNER_NEAR_ROOT_V4}",
        r"\input{SECTION9_SHARPENED_TRANSPORT_ATTACHMENT_V4}",
        r"\input{FINAL_ASSEMBLY_NEAR_ROOT_V4}",
    ):
        require(text.count(marker) == 1, f"near-root marker drift: {marker}")

    for forbidden in (
        "Choose the midpoint integer",
        "exact midpoint profile",
        old_full,
        old_final,
    ):
        require(forbidden not in text, f"stale Version 3 placement remains: {forbidden}")

    require(
        text.index(r"\input{SECTION5_NEAR_ROOT_PROFILE_V4}")
        < text.index(r"\section{Exact signed second-moment representation}"),
        "near-root profile is not placed before the overlap section",
    )
    require(
        text.index(r"\input{SECTION9_SHARPENED_TRANSPORT_ATTACHMENT_V4}")
        < text.index(r"\section{Rare-event amplification}")
        < text.index(r"\input{FINAL_ASSEMBLY_NEAR_ROOT_V4}"),
        "near-root assembly order is incorrect",
    )

    output.write_text(text, encoding="utf-8")
    print(f"generated near-root theorem-facing body: {output}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    generate(args.source, args.output)


if __name__ == "__main__":
    main()
