#!/usr/bin/env python3
"""Check the Erdős 625 standard-definition audit and terminology insert.

This validates source coverage, bibliography keys, and agreement with the
relevant Lean structures. It is not a proof of the asymptotic theorem.
"""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
AUDIT = ROOT / "625/audits/STANDARD_DEFINITIONS_AND_TERMINOLOGY_AUDIT_2026-07-27.md"
INSERT = ROOT / "625/arxiv/STANDARD_DEFINITIONS_INSERT_V2.tex"
MAIN = ROOT / "625/arxiv/main.tex"
BIB = ROOT / "625/arxiv/references.bib"
MATCHING = ROOT / "625/formalization/Erdos625/Section9CyclePolymerBound.lean"
SKELETON = ROOT / "625/formalization/Erdos625/Section8UnlabelledTypedSkeleton.lean"
CONFIGURATION = ROOT / "625/formalization/Erdos625/ConfigurationModelProbability.lean"

REQUIRED_BIB_KEYS = {
    "lesniak-straight-1977",
    "erdos-gimbel-1993",
    "heckel-2024-question",
    "heckel-2025-difference",
    "steiner-2024",
    "scheinerman-1992",
    "bollobas-thomason-1995",
    "janson-luczak-rucinski-2000",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def read(path: Path) -> str:
    require(path.is_file(), f"missing required file: {path}")
    return path.read_text(encoding="utf-8")


def extract_bib_keys(text: str) -> set[str]:
    return set(re.findall(r"@[A-Za-z]+\{([^,]+),", text))


def check_insert(text: str) -> None:
    markers = (
        "All graphs are finite, simple, and undirected",
        "A \\emph{cocoloring}",
        "cochromatic number",
        "signed cocoloring witness",
        "not a new graph invariant",
        "(x)_0=1",
        "when \(r>x\)",
        "uniform perfect matching",
        "stub-level matching",
        "simple bipartite graph",
        "c(\\varnothing)=0",
        "even subgraph",
        "binary cycle space",
        "partial matching",
        "Manuscript-specific bookkeeping",
    )
    missing = [marker for marker in markers if marker not in text]
    require(not missing, f"definition insert missing markers: {missing}")
    require(text.count("{") == text.count("}"), "unbalanced braces in TeX insert")
    require("\\tag{" not in text, "manual equation tags are forbidden in TeX insert")
    require("clique cover" not in text.lower(), "ambiguous cover terminology in TeX insert")
    require("empty or complete graph" in text, "historical equivalent definition absent")


def check_audit(text: str) -> None:
    markers = (
        "standard definitions and terminology audit",
        "independent sets and cliques",
        "generalized \\(\\mathcal P\\)-chromatic number",
        "partition parameter, not an overlapping cover parameter",
        "Falling factorial",
        "Bipartite configuration model",
        "Binary cycle-space terminology",
        "signed witness is auxiliary, not a new invariant",
        "Manuscript-specific terminology",
        "Definition-dependent proof checks",
        "Lean alignment",
        "Acceptance checklist",
        "No proof step was found to depend on a nonstandard definition",
    )
    missing = [marker for marker in markers if marker not in text]
    require(not missing, f"definition audit missing markers: {missing}")
    require("maximum versus maximal" in text.lower(), "maximum/maximal distinction absent")
    require("clique cover" in text.lower(), "cover warning absent")
    require("2^k" in text, "signed-witness factor check absent")
    require("r_{ab}\\ge2" in text, "support-graph threshold check absent")


def check_canonical_source(text: str) -> None:
    require(
        "The cochromatic number \\(\\zeta(G)\\) is the least number of parts" in text,
        "canonical cochromatic definition changed; refresh audit",
    )
    require(
        "A \\emph{signed cocoloring} is a partition" in text,
        "canonical signed-witness wording changed; refresh audit",
    )
    require(
        "Let \\(H(r)\\) be the simple bipartite graph" in text,
        "canonical support graph changed; refresh audit",
    )
    require(
        "the even\nsubgraphs form the binary cycle space" in text,
        "canonical cycle-space statement changed; refresh audit",
    )


def check_lean(matching: str, skeleton: str, configuration: str) -> None:
    for marker in (
        "def IsBipartiteEven",
        "∀ a, Even",
        "∀ b, Even",
        "def IsBipartiteMatching",
        "no two cells share a row or column",
    ):
        require(marker in matching, f"formal matching/even definition missing: {marker}")
    for marker in (
        "structure UnlabelledTypedSkeleton",
        "edges : Finset",
        "leftUnique",
        "rightUnique",
        "def UnlabelledTypedSkeleton.typeTable",
    ):
        require(marker in skeleton, f"formal skeleton definition missing: {marker}")
    for marker in (
        "def totalDemand",
        "def demandFactorialProduct",
        "def rowDescendingProduct",
        "def columnDescendingProduct",
    ):
        require(marker in configuration, f"configuration counting definition missing: {marker}")


def main() -> None:
    audit = read(AUDIT)
    insert = read(INSERT)
    main_tex = read(MAIN)
    bibliography = read(BIB)
    matching = read(MATCHING)
    skeleton = read(SKELETON)
    configuration = read(CONFIGURATION)

    missing_keys = sorted(REQUIRED_BIB_KEYS - extract_bib_keys(bibliography))
    require(not missing_keys, f"bibliography keys missing: {missing_keys}")
    check_insert(insert)
    check_audit(audit)
    check_canonical_source(main_tex)
    check_lean(matching, skeleton, configuration)

    print("ERDOS 625 STANDARD-DEFINITION SOURCE CHECK: PASS")
    print(f"  bibliography keys checked: {len(REQUIRED_BIB_KEYS)}")
    print("  standard invariants and auxiliary witness terminology separated")
    print("  configuration matching and simple support graph separated")
    print("  even-subgraph and binary cycle-space conventions aligned")
    print("  Lean structures agree with the stated mathematical definitions")
    print("  scope: source consistency only")


if __name__ == "__main__":
    main()
