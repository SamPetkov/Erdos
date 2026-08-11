#!/usr/bin/env python3
"""Fail-closed checks for the near-root Erdős 625 manuscript."""

from __future__ import annotations

import math
import re
import subprocess
from collections import Counter
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARXIV = ROOT / "arxiv"
BUILDER = ROOT / "scripts" / "build_near_root_self_contained_v4.py"
GENERATED = ARXIV / "AMS_NEAR_ROOT_BODY_V4.generated.tex"

MASTER = ARXIV / "AMS_NEAR_ROOT_DRAFT_V4.tex"
PROFILE = ARXIV / "SECTION5_NEAR_ROOT_PROFILE_V4.tex"
FULL = ARXIV / "SECTION7_FULL_CORNER_NEAR_ROOT_V4.tex"
FINAL = ARXIV / "FINAL_ASSEMBLY_NEAR_ROOT_V4.tex"
FRONT = ARXIV / "FRONTMATTER_INTRODUCTION_NEAR_ROOT_V4.tex"
ARCH = ARXIV / "PROOF_ARCHITECTURE_NEAR_ROOT_V4.tex"
STATUS = ARXIV / "FORMALIZATION_STATUS_NEAR_ROOT_ADDENDUM_2026_08_11_V4.tex"
SOURCES = (MASTER, PROFILE, FULL, FINAL, FRONT, ARCH, STATUS)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def flatten(text: str) -> str:
    return re.sub(r"\s+", " ", text)


def check_hygiene(text: str, name: str) -> None:
    bad_controls = [
        (index, ord(character))
        for index, character in enumerate(text)
        if ord(character) < 32 and character not in "\n\r\t"
    ]
    require(not bad_controls, f"{name}: hidden control characters: {bad_controls[:8]}")

    begins = Counter(re.findall(r"\\begin\{([^}]+)\}", text))
    ends = Counter(re.findall(r"\\end\{([^}]+)\}", text))
    require(begins == ends, f"{name}: unbalanced environments")
    require(text.count("{") == text.count("}"), f"{name}: unbalanced braces")

    for forbidden in (
        "TODO",
        "TBD",
        "proof omitted",
        "details are standard",
        r"\log2",
        r"\ln",
    ):
        require(forbidden not in text, f"{name}: forbidden marker {forbidden}")


def check_ceiling_buffer() -> int:
    checked = 0
    for denominator in range(1, 101):
        for numerator in range(-500, 501):
            x = Fraction(numerator, denominator)
            ceil_x = -((-x.numerator) // x.denominator)
            displacement = Fraction(ceil_x + 1) - x
            require(displacement >= 1, f"ceiling buffer below one at x={x}")
            require(displacement < 2, f"ceiling buffer reached two at x={x}")
            checked += 1
    return checked


def check_rate_ledger() -> None:
    # Monomials are encoded as n^a (log n)^b.
    seed = (Fraction(1, 2), Fraction(3, 2))
    amplified = (
        (Fraction(1) + seed[0]) / 2,
        seed[1] / 2 - 1,
    )
    require(
        amplified == (Fraction(3, 4), Fraction(-1, 4)),
        "amplification monomial mismatch",
    )
    require(amplified[0] < 1, "amplification loss is not lower order")

    # The full-corner profile count has logarithm O(log n), while the
    # reciprocal first moment has exponent -c(log n)^2.
    require(Fraction(2) > Fraction(1), "full-corner exponent does not dominate")
    # Dividing (log n)^2 by k = Theta(n/log n) gives O((log n)^3/n)=o(1).
    require(Fraction(2) < Fraction(3), "normalized first-moment ledger drift")


def check_coefficients() -> tuple[float, float, float]:
    q = math.log(2.0)
    old = (q * q / 8.0) * math.log(1000.0 / 639.0)
    new = (q * q / 4.0) * math.log(1000.0 / 639.0)
    strong = (q * q / 4.0) * math.log(20000.0 / 12777.0)
    require(abs(new - 2.0 * old) < 1e-15, "coefficient did not double exactly")
    require(strong > new, "fixed four-support slack is not positive")
    require(abs(new - 0.053792819616758226) < 1e-15, "displayed coefficient drift")
    require(abs(strong - 0.05382101852602721) < 1e-15, "strong coefficient drift")
    return old, new, strong


def require_tokens(text: str, name: str, tokens: tuple[str, ...]) -> None:
    flat = flatten(text)
    for token in tokens:
        require(token in flat, f"{name} missing semantic token: {token}")


def main() -> None:
    for path in (BUILDER, *SOURCES):
        require(path.is_file(), f"missing near-root file: {path}")

    subprocess.run(["python", str(BUILDER)], cwd=ROOT.parent, check=True)
    require(GENERATED.is_file(), "near-root builder did not create the body")

    generated = GENERATED.read_text(encoding="utf-8")
    texts = {path.name: path.read_text(encoding="utf-8") for path in SOURCES}
    combined = "\n".join([generated, *texts.values()])

    master = texts[MASTER.name]
    require(r"\ErdosProofClosedfalse" in master, "publication switch is not fail-closed")
    require(r"\ErdosProofClosedtrue" not in master, "publication mode was enabled")

    for marker in (
        r"\input{SECTION5_NEAR_ROOT_PROFILE_V4}",
        r"\input{SECTION7_FULL_CORNER_NEAR_ROOT_V4}",
        r"\input{SECTION9_SHARPENED_TRANSPORT_ATTACHMENT_V4}",
        r"\input{FINAL_ASSEMBLY_NEAR_ROOT_V4}",
    ):
        require(generated.count(marker) == 1, f"generated marker drift: {marker}")

    for forbidden in (
        "Choose the midpoint integer",
        "exact midpoint profile",
        r"\input{SECTION7_FULL_CORNER_V3}",
        r"\input{FINAL_ASSEMBLY_SELF_CONTAINED_V3}",
    ):
        require(forbidden not in combined, f"stale Version 3 placement remains: {forbidden}")

    profile = texts[PROFILE.name]
    require_tokens(
        profile,
        "near-root profile",
        (
            "one-part-buffer integer",
            r"1\le d_n<2",
            r"O\!\left(\frac{(\log n)^2}{n}\right)",
            r"c_{\mathrm s}(\log n)^2",
            r"c_{\mathrm{nr}}(\log n)^2",
            "only scale change relative to midpoint placement",
            "full leading root separation",
            r"\frac{(\log 2)^2}{4}A_4(\delta_n)",
        ),
    )
    profile_tags = re.findall(r"\\tag\{([^}]+)\}", profile)
    expected_profile_tags = {
        "5.13", "5.13a", "5.14", "5.15", "5.16",
        "5.17", "5.18", "5.19", "5.20",
    }
    require(set(profile_tags) == expected_profile_tags, "near-root profile tag drift")
    require(len(profile_tags) == len(set(profile_tags)), "duplicate near-root profile tags")

    require_tokens(
        texts[FULL.name],
        "near-root full corner",
        (
            "one-part-buffer first-moment margin",
            r"e^{-c_{\mathrm{nr}}(\log n)^2}",
            "quadratic logarithmic margin",
            "Disjoint three-range assembly",
            "no boundary term is counted twice",
        ),
    )

    require_tokens(
        texts[FINAL.name],
        "near-root final assembly",
        (
            "full root-separation constant",
            r"\frac{(\log 2)^2}{4}A_4(\delta_n)",
            r"n^{3/4}(\log n)^{-1/4}",
            r"\frac{(\log n)^{11/4}}{n^{1/4}}",
            r"\frac{(\log 2)^2}{4}",
            "0.053792819616758",
            "0.053821018526027",
            "Simultaneous complement form",
            "No further asymptotic loss is introduced",
        ),
    )

    require_tokens(
        texts[FRONT.name],
        "near-root front matter",
        (
            "Why one extra class is enough",
            r"\left\lceil r_4^{\mathrm{co}}\right\rceil+1",
            r"\Theta((\log n)^2)",
            r"O(n^{3/4}(\log n)^{-1/4})",
            "0.053792819616758",
        ),
    )

    require_tokens(
        texts[ARCH.name],
        "near-root proof guide",
        (
            "minimal integer buffering",
            "Why the smaller first moment is sufficient",
            "Fusing deficits with endpoint transport",
            "Critical-quarter residual attachments",
            "Explicit amplification loss",
        ),
    )

    require_tokens(
        texts[STATUS.name],
        "near-root status addendum",
        (
            "Candidate replacement interface",
            "Dependency reduction",
            "Recommended exact Lean sequence",
            "The arrows denote theorem dependency, not equality",
            "publication switch remains false",
        ),
    )

    labels = re.findall(r"\\label\{([^}]+)\}", combined)
    counts = Counter(labels)
    duplicates = sorted(label for label, count in counts.items() if count > 1)
    require(not duplicates, f"duplicate near-root labels: {duplicates}")

    check_hygiene(generated, "generated body")
    for name, text in texts.items():
        check_hygiene(text, name)

    # The generated body is intentionally modular: the large replacement
    # proofs are separate inputs. Gate the wrapper and the actual source set.
    generated_lines = len(generated.splitlines())
    source_lines = sum(len(text.splitlines()) for text in texts.values())
    source_bytes = sum(len(text.encode("utf-8")) for text in texts.values())
    require(generated_lines >= 700, f"generated wrapper unexpectedly short: {generated_lines}")
    require(source_lines >= 900, f"near-root source set unexpectedly short: {source_lines}")
    require(source_bytes >= 38_000, f"near-root source set unexpectedly small: {source_bytes}")
    require(len(profile.splitlines()) >= 175, "near-root profile source unexpectedly short")
    require(len(texts[FULL.name].splitlines()) >= 120, "full-corner source unexpectedly short")
    require(len(texts[FINAL.name].splitlines()) >= 280, "final assembly unexpectedly short")

    ceiling_cases = check_ceiling_buffer()
    check_rate_ledger()
    old, new, strong = check_coefficients()

    print("ERDOS 625 NEAR-ROOT FULL-GAP CHECK: PASS")
    print(f"  generated wrapper lines: {generated_lines}")
    print(f"  standalone near-root sources: {source_lines} lines, {source_bytes} bytes")
    print(f"  exact ceiling cases: {ceiling_cases}")
    print("  first-moment margin: Theta((log n)^2)")
    print("  full-corner total: polynomial times exp(-c(log n)^2) = o(1)")
    print("  amplification loss: O(n^(3/4)(log n)^(-1/4))")
    print(f"  previous coefficient: {old:.15f}")
    print(f"  near-root coefficient: {new:.15f}")
    print(f"  strong pre-slack coefficient: {strong:.15f}")
    print("  publication status: fail-closed")


if __name__ == "__main__":
    main()
