#!/usr/bin/env python3
"""Fail-closed checks for the theorem-facing Erdős 625 manuscript package."""

from __future__ import annotations

import re
import subprocess
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARXIV = ROOT / "arxiv"
BUILDER = ROOT / "scripts" / "build_phase_root_self_contained_v3.py"
GENERATED = ARXIV / "AMS_SELF_CONTAINED_BODY_V3.generated.tex"
MASTER = ARXIV / "AMS_SELF_CONTAINED_DRAFT_V3.tex"
SECTION2 = ARXIV / "SECTION2_PHASE_PACKAGE_V3.tex"
SECTION3 = ARXIV / "SECTION3_ROOT_GEOMETRY_V3.tex"
SECTION4 = ARXIV / "SECTION4_CHROMATIC_LOWER_TAIL_V3.tex"
SECTION5 = ARXIV / "SECTION5_ROOT_TRANSPORT_V3.tex"
GLOBAL_LEDGER = ARXIV / "SECTION9_EXPLICIT_GLOBAL_LEDGER_V3.tex"
STATUS_ADDENDUM = ARXIV / "FORMALIZATION_STATUS_ADDENDUM_2026_08_07_V3.tex"


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
    for path in (
        BUILDER,
        MASTER,
        SECTION2,
        SECTION3,
        SECTION4,
        SECTION5,
        GLOBAL_LEDGER,
        STATUS_ADDENDUM,
    ):
        require(path.is_file(), f"missing theorem-facing package file: {path}")

    subprocess.run(["python", str(BUILDER)], cwd=ROOT.parent, check=True)
    require(GENERATED.is_file(), "theorem-facing builder did not create the body")

    generated = GENERATED.read_text(encoding="utf-8")
    master = MASTER.read_text(encoding="utf-8")
    section2 = SECTION2.read_text(encoding="utf-8")
    section3 = SECTION3.read_text(encoding="utf-8")
    section4 = SECTION4.read_text(encoding="utf-8")
    section5 = SECTION5.read_text(encoding="utf-8")
    global_ledger = GLOBAL_LEDGER.read_text(encoding="utf-8")
    status_addendum = STATUS_ADDENDUM.read_text(encoding="utf-8")
    section2_flat = flatten(section2)
    section3_flat = flatten(section3)
    ledger_flat = flatten(global_ledger)
    addendum_flat = flatten(status_addendum)

    for token in (
        r"\input{SECTION2_PHASE_PACKAGE_V3}",
        r"\input{SECTION3_ROOT_GEOMETRY_V3}",
        r"\input{SECTION4_CHROMATIC_LOWER_TAIL_V3}",
        r"\input{SECTION5_ROOT_TRANSPORT_V3}",
        r"\input{SECTION9_SELF_CONTAINED_V3}",
        r"\input{SECTION9_EXPLICIT_GLOBAL_LEDGER_V3}",
    ):
        require(generated.count(token) == 1, f"generated body marker drift: {token}")

    require(
        r"\input{FORMALIZATION_STATUS_ADDENDUM_2026_08_07_V3}" in master,
        "master file does not include the theorem-facing status addendum",
    )
    require(
        master.index(r"\input{FORMALIZATION_STATUS_APPENDIX_V3}")
        < master.index(r"\input{FORMALIZATION_STATUS_ADDENDUM_2026_08_07_V3}"),
        "status addendum is not placed after the original formalization map",
    )

    require(
        generated.index(r"\input{SECTION9_SELF_CONTAINED_V3}")
        < generated.index(r"\input{SECTION9_EXPLICIT_GLOBAL_LEDGER_V3}")
        < generated.index(r"\section{Rare-event amplification}"),
        "global ledger is not placed between Sections 9 and 10",
    )

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
        r"\exp(2C+qb)",
        r"\frac{n^2}{L^2}",
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

    for token in (
        "Explicit global logarithmic ledger",
        r"\varepsilon_n^{\mathrm{pd}}",
        r"1+3\tau_n^{\mathrm{end}}",
        r"\Gamma_n^{\mathrm{skel}}",
        r"\varepsilon_n^{\mathrm{skel}}",
        r"\Gamma_n^{\mathrm{att}}",
        r"\varepsilon_n^{\mathrm{att}}",
        r"\Lambda_n",
        r"\eqref{eq:exact-attachment-decomposition-v3}",
        "No factor is charged in both ledgers",
    ):
        require(token in ledger_flat, f"global second-moment ledger missing: {token}")

    for token in (
        "Theorem-facing closure addendum",
        "Current candidate interfaces",
        "Deterministic error chain",
        "Exact formalization targets",
        "The arrows denote theorem dependency, not equality",
        "Unchanged publication gate",
        "status of the main theorem remains fail-closed",
    ):
        require(token in addendum_flat, f"status addendum missing: {token}")

    require(
        r"\varepsilon_n^{\mathrm{cap}}" in section4,
        "Section 4 no longer consumes the Section 2 cap error",
    )
    require(
        r"\varepsilon_n^{\mathrm{dual}}" in section3
        and r"\varepsilon_n^{\mathrm{target}}" in section5
        and r"\omega_n^{\mathrm{root}}" in section5,
        "the finite-dual to root-transport error chain is incomplete",
    )

    checked_sources = {
        "Section 2": section2,
        "Section 3": section3,
        "global ledger": global_ledger,
        "status addendum": status_addendum,
    }
    for name, text in checked_sources.items():
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

    tagged_sources = section2 + "\n" + section3 + "\n" + global_ledger
    tags = re.findall(r"\\tag\{([^}]+)\}", tagged_sources)
    tag_counts = Counter(tags)
    duplicate_tags = sorted(tag for tag, count in tag_counts.items() if count > 1)
    require(not duplicate_tags, f"duplicate theorem-facing equation tags: {duplicate_tags}")

    expected_tags = {
        "2.1", "2.2", "2.3", "2.4", "2.5", "2.6", "2.7", "2.8", "2.8a", "2.9",
        "3.1", "3.2", "3.3", "3.4", "3.5", "3.6", "3.7", "3.8", "3.8a",
        "3.9a", "3.9", "3.9b", "3.10", "3.11", "3.12", "3.13", "3.14",
        "3.15", "3.15a", "3.16", "3.17", "3.18", "3.19",
        "9.31", "9.32", "9.33", "9.34", "9.35", "9.36",
        "9.37", "9.38", "9.39", "9.40", "9.41", "9.42",
    }
    missing_tags = sorted(expected_tags - set(tags))
    require(not missing_tags, f"theorem-facing package missing equation tags: {missing_tags}")

    require(
        len(section2.splitlines()) >= 190,
        f"Section 2 source unexpectedly short: {len(section2.splitlines())} lines",
    )
    require(
        len(section3.splitlines()) >= 340,
        f"Section 3 source unexpectedly short: {len(section3.splitlines())} lines",
    )
    require(
        len(global_ledger.splitlines()) >= 180,
        f"global ledger unexpectedly short: {len(global_ledger.splitlines())} lines",
    )
    require(
        len(status_addendum.splitlines()) >= 110,
        f"status addendum unexpectedly short: {len(status_addendum.splitlines())} lines",
    )

    print("ERDOS 625 THEOREM-FACING PACKAGE CHECK: PASS")
    print(f"  Section 2 source lines: {len(section2.splitlines())}")
    print(f"  Section 3 source lines: {len(section3.splitlines())}")
    print(f"  global ledger source lines: {len(global_ledger.splitlines())}")
    print(f"  status addendum source lines: {len(status_addendum.splitlines())}")
    print(f"  equation tags guarded: {len(tag_counts)}")
    print("  deterministic interfaces: phase, cap, dual, slope, root, skeleton, attachment")
    print("  publication status: fail-closed")


if __name__ == "__main__":
    main()
