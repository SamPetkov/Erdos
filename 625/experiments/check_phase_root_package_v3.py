#!/usr/bin/env python3
"""Fail-closed checks for the theorem-facing Sections 2 and 3 package."""

from __future__ import annotations

import re
import subprocess
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARXIV = ROOT / "arxiv"
BUILDER = ROOT / "scripts" / "build_phase_root_self_contained_v3.py"
GENERATED = ARXIV / "AMS_SELF_CONTAINED_BODY_V3.generated.tex"
SECTION2 = ARXIV / "SECTION2_PHASE_PACKAGE_V3.tex"
SECTION3 = ARXIV / "SECTION3_ROOT_GEOMETRY_V3.tex"
SECTION4 = ARXIV / "SECTION4_CHROMATIC_LOWER_TAIL_V3.tex"
SECTION5 = ARXIV / "SECTION5_ROOT_TRANSPORT_V3.tex"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def flatten(text: str) -> str:
    return re.sub(r"\s+", " ", text)


def check_balanced_environments(text: str, name: str) -> None:
    begins = Counter(re.findall(r"\\begin\{([^}]+)\}", text))
    ends = Counter(re.findall(r"\\end\{([^}]+)\}", text))
    require(
        begins == ends,
        f"{name}: unbalanced environments: {begins - ends}, {ends - begins}",
    )


def check_control_characters(text: str, name: str) -> None:
    bad = [
        (index, ord(character))
        for index, character in enumerate(text)
        if ord(character) < 32 and character not in "\n\r\t"
    ]
    require(not bad, f"{name}: hidden control characters: {bad[:8]}")


def main() -> None:
    for path in (BUILDER, SECTION2, SECTION3, SECTION4, SECTION5):
        require(path.is_file(), f"missing phase-root package file: {path}")

    subprocess.run(["python", str(BUILDER)], cwd=ROOT.parent, check=True)
    require(GENERATED.is_file(), "phase-root builder did not create the body")

    generated = GENERATED.read_text(encoding="utf-8")
    section2 = SECTION2.read_text(encoding="utf-8")
    section3 = SECTION3.read_text(encoding="utf-8")
    section4 = SECTION4.read_text(encoding="utf-8")
    section5 = SECTION5.read_text(encoding="utf-8")
    section2_flat = flatten(section2)
    section3_flat = flatten(section3)

    for token in (
        r"\input{SECTION2_PHASE_PACKAGE_V3}",
        r"\input{SECTION3_ROOT_GEOMETRY_V3}",
        r"\input{SECTION4_CHROMATIC_LOWER_TAIL_V3}",
        r"\input{SECTION5_ROOT_TRANSPORT_V3}",
    ):
        require(generated.count(token) == 1, f"generated body marker drift: {token}")

    for token in (
        r"\section{The complete independence-number phase}",
        r"\section{Continuous profile roots}",
        "Expanding \\(\\log \\alpha\\) at",
        "This proves (3.9), and on the finite support",
    ):
        require(token not in generated, f"legacy phase-root prose remains: {token}")

    for token in (
        "Uniform phase expansion and adjacent-size control",
        r"\varepsilon_n^{\mathrm{ph}}",
        r"|E_n(\delta)|\le\varepsilon_n^{\mathrm{ph}}",
        r"2^\alpha",
        r"\exp(2C+qb)\frac{n^2}{L^2}",
        r"\delta(L-\ell)",
        r"\varepsilon_n^{\mathrm{cap}}",
        "one eventuality threshold valid for the complete phase",
    ):
        require(token in section2_flat, f"Section 2 package missing: {token}")

    for token in (
        "Uniform root, slope, and finite-dual package",
        r"S_+^{(n)}",
        r"\varepsilon_{n,A}^{\mathrm{slope}}",
        r"\varepsilon_n^{\mathrm{dual}}",
        r"M'_{n,S}\to M'_S",
        r"v_*:=\frac12",
        "remaining Gaussian tail uniformly small",
        "No limiting replacement is used in this cancellation",
        r"\Psi_{n,S,c}(s)",
        "one eventuality threshold for the complete phase",
    ):
        require(token in section3_flat, f"Section 3 package missing: {token}")

    require(
        r"\varepsilon_n^{\mathrm{cap}}" in section4,
        "Section 4 no longer consumes the Section 2 cap error",
    )
    require(
        r"\varepsilon_n^{\mathrm{dual}}" in section3
        and r"\omega_n^{\mathrm{root}}" in section5,
        "the finite-dual to root-transport error chain is incomplete",
    )

    for name, text in {
        "Section 2": section2,
        "Section 3": section3,
    }.items():
        check_control_characters(text, name)
        check_balanced_environments(text, name)
        require(text.count("{") == text.count("}"), f"{name}: unbalanced braces")
        require(
            r"\begin{equation}" not in text,
            f"{name}: numbered equation environment combined with manual tags",
        )
        for forbidden in (
            "TODO",
            "TBD",
            "proof omitted",
            "details are standard",
            r"\ln",
            r"\log2",
        ):
            require(forbidden not in text, f"{name}: forbidden marker {forbidden}")

    tags = re.findall(r"\\tag\{([^}]+)\}", section2 + "\n" + section3)
    tag_counts = Counter(tags)
    duplicate_tags = sorted(tag for tag, count in tag_counts.items() if count > 1)
    require(not duplicate_tags, f"duplicate phase-root equation tags: {duplicate_tags}")

    expected_tags = {
        "2.1", "2.2", "2.3", "2.4", "2.5", "2.6", "2.7", "2.8", "2.8a", "2.9",
        "3.1", "3.2", "3.3", "3.4", "3.5", "3.6", "3.7", "3.8", "3.8a",
        "3.9a", "3.9", "3.9b", "3.10", "3.11", "3.12", "3.13", "3.14",
        "3.15", "3.15a", "3.16", "3.17", "3.18", "3.19",
    }
    missing_tags = sorted(expected_tags - set(tags))
    require(not missing_tags, f"phase-root package missing equation tags: {missing_tags}")

    require(
        len(section2.splitlines()) >= 190,
        f"Section 2 source unexpectedly short: {len(section2.splitlines())} lines",
    )
    require(
        len(section3.splitlines()) >= 340,
        f"Section 3 source unexpectedly short: {len(section3.splitlines())} lines",
    )

    print("ERDOS 625 PHASE-ROOT PACKAGE CHECK: PASS")
    print(f"  Section 2 source lines: {len(section2.splitlines())}")
    print(f"  Section 3 source lines: {len(section3.splitlines())}")
    print(f"  equation tags guarded: {len(tag_counts)}")
    print("  deterministic interfaces: phase, cap, dual, slope, and root transport")
    print("  publication status: fail-closed")


if __name__ == "__main__":
    main()
