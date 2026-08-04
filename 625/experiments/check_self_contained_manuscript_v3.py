#!/usr/bin/env python3
"""Fail-closed structural checks for the Erdős 625 Version 3 manuscript."""

from __future__ import annotations

import re
import subprocess
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARXIV = ROOT / "arxiv"
GENERATOR = ROOT / "scripts" / "build_self_contained_ams_v3.py"
GENERATED = ARXIV / "AMS_SELF_CONTAINED_BODY_V3.generated.tex"
MASTER = ARXIV / "AMS_SELF_CONTAINED_DRAFT_V3.tex"

SOURCE_FILES = [
    ARXIV / "FRONTMATTER_INTRODUCTION_SELF_CONTAINED_V3.tex",
    ARXIV / "CONVENTIONS_AND_PROOF_OBJECTS_V3.tex",
    ARXIV / "PROOF_ARCHITECTURE_SELF_CONTAINED_V3.tex",
    ARXIV / "SECTION8_SELF_CONTAINED_V3.tex",
    ARXIV / "SECTION9_SELF_CONTAINED_V3.tex",
    ARXIV / "FINAL_ASSEMBLY_SELF_CONTAINED_V3.tex",
    ARXIV / "FORMALIZATION_STATUS_APPENDIX_V3.tex",
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def flatten(text: str) -> str:
    """Normalize TeX source whitespace without changing control sequences."""
    return re.sub(r"\s+", " ", text)


def strip_tex(text: str) -> str:
    text = re.sub(r"%.*", " ", text)
    text = re.sub(r"\\[A-Za-z@]+\*?(?:\[[^]]*\])?", " ", text)
    text = text.replace("{", " ").replace("}", " ")
    text = re.sub(r"\$[^$]*\$", " ", text)
    return re.sub(r"\s+", " ", text)


def check_balanced_environments(text: str, name: str) -> None:
    begins = Counter(re.findall(r"\\begin\{([^}]+)\}", text))
    ends = Counter(re.findall(r"\\end\{([^}]+)\}", text))
    require(
        begins == ends,
        f"{name}: unbalanced environments: {begins - ends}, {ends - begins}",
    )


def main() -> None:
    for path in [MASTER, GENERATOR, *SOURCE_FILES]:
        require(path.is_file(), f"missing file: {path}")

    subprocess.run(["python", str(GENERATOR)], cwd=ROOT.parent, check=True)
    require(GENERATED.is_file(), "generator did not create the manuscript body")

    master = MASTER.read_text(encoding="utf-8")
    generated = GENERATED.read_text(encoding="utf-8")
    sources = {path.name: path.read_text(encoding="utf-8") for path in SOURCE_FILES}
    combined = "\n".join([master, generated, *sources.values()])

    require(r"\ErdosProofClosedfalse" in master, "publication switch is not fail-closed")
    require(r"\ErdosProofClosedtrue" not in master, "publication mode was enabled")
    require(
        "Verification draft"
        in sources["FRONTMATTER_INTRODUCTION_SELF_CONTAINED_V3.tex"],
        "visible verification status is missing",
    )

    required_master_inputs = (
        "AMS_THEOREM_ENVIRONMENTS_V3",
        "FRONTMATTER_INTRODUCTION_SELF_CONTAINED_V3",
        "CONVENTIONS_AND_PROOF_OBJECTS_V3",
        "PROOF_ARCHITECTURE_SELF_CONTAINED_V3",
        "AMS_SELF_CONTAINED_BODY_V3.generated",
        "FORMALIZATION_STATUS_APPENDIX_V3",
    )
    missing_inputs = [token for token in required_master_inputs if token not in master]
    require(not missing_inputs, f"master file missing inputs: {missing_inputs}")

    required_body_markers = (
        r"\section{Phase notation and elementary estimates}",
        r"\input{SECTION8_SELF_CONTAINED_V3}",
        r"\input{SECTION9_SELF_CONTAINED_V3}",
        r"\section{Rare-event amplification}",
        r"\input{FINAL_ASSEMBLY_SELF_CONTAINED_V3}",
        "Canonical source Git blob: c4d090b73cd5efcdb98cc30f79bb5f53c6c9bc97",
    )
    missing_body = [token for token in required_body_markers if token not in generated]
    require(not missing_body, f"generated body missing markers: {missing_body}")
    require(
        generated.count(r"\section{") >= 8,
        "generated body does not contain the canonical numbered sections",
    )

    section8 = sources["SECTION8_SELF_CONTAINED_V3.tex"]
    section8_flat = flatten(section8)
    for token in (
        "Completion-free aggregate weight",
        "Exact one-cell deficit ratio",
        "Aggregate deficit comparison",
        "Optional-choice product",
        "Reference grouping",
        "Endpoint-table sum",
        "Phase smallness of the common charge",
        r"\rho_{16}",
        "canonical finite Lean reduction",
    ):
        require(token in section8_flat, f"Section 8 missing: {token}")

    section9 = sources["SECTION9_SELF_CONTAINED_V3.tex"]
    section9_flat = flatten(section9)
    for token in (
        r"\theta_{ab}",
        r"\lambda_{ab}",
        r"q_{ab}",
        "Fixed even-set expansion",
        "Restriction-product bound",
        "The intrinsic residual regime",
        "The complementary residual regime",
        "Normalized signed second moment",
    ):
        require(token in section9_flat, f"Section 9 missing: {token}")

    final = sources["FINAL_ASSEMBLY_SELF_CONTAINED_V3.tex"]
    final_flat = flatten(final)
    for token in (
        r"\frac{(\log2)^2}{8}A_4(\delta_n)",
        r"\log\!\left(\frac{1000}{639}\right)",
        "Exact four-support certificate",
        "Simultaneous complement form",
    ):
        require(token in final_flat, f"final assembly missing: {token}")

    appendix = sources["FORMALIZATION_STATUS_APPENDIX_V3.tex"]
    appendix_flat = flatten(appendix)
    for token in (
        "Welded",
        "Running",
        "Needs review",
        "eventually\\_fourEndpointThreeQuarterRho\\_le\\_one",
        "Publication gate",
        "Recommended theorem-facing Lean organization",
    ):
        require(token in appendix_flat, f"formalization appendix missing: {token}")

    forbidden = (
        "TODO",
        "TBD",
        "proof omitted",
        "details are standard",
        "The endpoint transportation estimate absorbs",
        r"\exp\!left",
        r"\begin{lemmabox}",
        r"\begin{propositionbox}",
        r"\begin{resultbox}",
        r"\ln",
    )
    offenders = [token for token in forbidden if token in combined]
    require(not offenders, f"forbidden manuscript markers: {offenders}")

    labels = re.findall(r"\\label\{([^}]+)\}", combined)
    duplicates = sorted(label for label, count in Counter(labels).items() if count > 1)
    require(not duplicates, f"duplicate labels: {duplicates}")

    for name, text in {"master": master, "generated": generated, **sources}.items():
        check_balanced_environments(text, name)
        require(text.count("{") == text.count("}"), f"{name}: unbalanced braces")

    words = re.findall(r"[A-Za-z][A-Za-z'-]+", strip_tex(combined))
    require(
        len(words) >= 18000,
        f"manuscript is still synopsis-length: {len(words)} words",
    )

    print("ERDOS 625 SELF-CONTAINED MANUSCRIPT CHECK: PASS")
    print(f"  generated body lines: {len(generated.splitlines())}")
    print(f"  approximate prose words: {len(words)}")
    print(f"  unique labels: {len(labels)}")
    print("  publication switch: disabled")


if __name__ == "__main__":
    main()
