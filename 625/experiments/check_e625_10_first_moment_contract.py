#!/usr/bin/env python3
"""Exact structural and arithmetic checks for the E625-10 design package.

This script is a regression layer for the theorem contract. It is not a Lean
proof and does not promote E625-10. All load-bearing mathematical statements
remain subject to exact Lean replay and independent review.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import math


ROOT = Path(__file__).resolve().parents[2]
PACKAGE = ROOT / "625/formalization/E625_10_SIGNED_FOUR_SIZE_FIRST_MOMENT_PACKAGE_2026-08-19.md"
AUDIT = ROOT / "625/audits/E625_10_SIGNED_FIRST_MOMENT_ADVERSARIAL_AUDIT_2026-08-19.md"
CONTRACTS = ROOT / "625/audits/PROOF_CLOSURE_CONTRACTS_2026-08-05.md"


def fail(message: str) -> None:
    raise RuntimeError(message)


def require(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def read(path: Path) -> str:
    if not path.is_file():
        fail(f"missing required file: {path.relative_to(ROOT)}")
    return path.read_text(encoding="utf-8")


def require_once(text: str, marker: str, where: str) -> None:
    count = text.count(marker)
    require(count == 1, f"expected one occurrence of {marker!r} in {where}, found {count}")


def extract_top_declaration(package: str) -> str:
    start_marker = "theorem e625_10_signedFourSizeFirstMoment :"
    start = package.find(start_marker)
    require(start >= 0, "top-level theorem declaration is missing")
    fence = package.find("```", start)
    require(fence >= 0, "top-level theorem code fence is unterminated")
    return package[start:fence]


def check_structure(package: str, audit: str, contracts: str) -> None:
    package_markers = [
        "theorem e625_10_signedFourSizeFirstMoment :",
        "theorem eventually_signedFourMidpointRoundingAdmissible :",
        "signedProfileExpectation_toReal_eq_partialSignedFirstMoment_fourDeficit",
        "theorem midpointRoundedFourSizeEntropy_loss_le",
        "(50 / 7 : ℝ)",
        "theorem eventually_abs_log_signedFourMidpointFirstMoment_sub_objective_le",
        "theorem tendsto_phaseSignedFourMidpointObjective_normalized",
        "Real.log (200 / 153 : ℝ) / 2",
        "midpointOptimizer n (phaseNat n) K",
        "partialSignedFirstMoment",
        "The factor is `4`, not `phaseNat n + 1`",
    ]
    for marker in package_markers:
        require(marker in package, f"package is missing required marker: {marker}")

    require_once(
        package,
        "theorem e625_10_signedFourSizeFirstMoment :",
        str(PACKAGE.relative_to(ROOT)),
    )

    audit_markers = [
        "Exact rounded-optimizer loss",
        "0 <= K_n * KL(r_n || p_n) <= 50/7",
        "Closed endpoint margin — REJECTED",
        "Circular second-moment input — REJECTED",
    ]
    for marker in audit_markers:
        require(marker in audit, f"audit is missing required marker: {marker}")

    contract_markers = [
        "E625_10_SIGNED_FOUR_SIZE_FIRST_MOMENT_PACKAGE_2026-08-19.md",
        "log M_n / K_n - A_4(delta_n)/2 -> 0",
        "50/7",
        "partialSignedFirstMoment",
    ]
    for marker in contract_markers:
        require(marker in contracts, f"closure contract is missing required marker: {marker}")

    forbidden_placeholders = ["TODO", "TBD", "FIXME", "INSERT PROOF", "PLACEHOLDER"]
    for path, text in ((PACKAGE, package), (AUDIT, audit)):
        for marker in forbidden_placeholders:
            require(marker not in text, f"forbidden placeholder {marker!r} in {path.relative_to(ROOT)}")

    declaration = extract_top_declaration(package)
    forbidden_top_level_terms = [
        "chromaticNumber",
        "partialDiagonal",
        "skeleton",
        "secondMoment",
        "Paley",
        "Erdos625Statement",
    ]
    for marker in forbidden_top_level_terms:
        require(
            marker not in declaration,
            f"top-level E625-10 declaration improperly contains downstream term {marker!r}",
        )


def check_exact_constant_ledger() -> None:
    rounding = Fraction(4 * 5 * 5, 14)
    require(rounding == Fraction(50, 7), "rounding ledger 4*25/14 != 50/7")

    public_ratio = Fraction(2, 1) / Fraction(153, 100)
    require(public_ratio == Fraction(200, 153), "public entropy ratio identity failed")
    require(public_ratio > 1, "public entropy margin is not positive")

    stronger_ratio = Fraction(20000, 12777) / Fraction(1000, 639)
    require(
        stronger_ratio == Fraction(12780, 12777),
        "stronger fixed-slack ratio identity failed",
    )
    require(stronger_ratio > 1, "stronger fixed slack is not positive")

    half_public_margin = 0.5 * math.log(200.0 / 153.0)
    require(half_public_margin > 0.0, "half public logarithmic margin is not positive")


def ceil_fraction(x: Fraction) -> int:
    return -((-x.numerator) // x.denominator)


def check_midpoint_ceiling() -> int:
    values = {
        Fraction(num, den)
        for den in range(1, 9)
        for num in range(-32, 33)
    }
    checked = 0
    for r_co in values:
        for r_plus in values:
            midpoint = (r_co + r_plus) / 2
            k = ceil_fraction(midpoint)
            error = Fraction(k, 1) - midpoint
            require(Fraction(0, 1) <= error, "ceiling midpoint error became negative")
            require(error < Fraction(1, 1), "ceiling midpoint error reached one")
            require(
                Fraction(k, 1) - r_co
                == (r_plus - r_co) / 2 + error,
                "midpoint displacement identity failed",
            )
            checked += 1
    return checked


def check_tangent_correction() -> int:
    checked = 0
    deficits = (2, 3, 4, 5)
    raw_values = range(-2, 4)
    for k in range(-2, 5):
        for d in range(-2, 5):
            for a0 in raw_values:
                for a1 in raw_values:
                    for a2 in raw_values:
                        for a3 in raw_values:
                            raw = (a0, a1, a2, a3)
                            e0 = sum(raw) - k
                            e1 = sum(s * a for s, a in zip(deficits, raw)) - d
                            c0 = e1 - 3 * e0
                            c1 = 2 * e0 - e1
                            corrected = (a0 + c0, a1 + c1, a2, a3)
                            require(sum(corrected) == k, "tangent count conservation failed")
                            require(
                                sum(s * a for s, a in zip(deficits, corrected)) == d,
                                "tangent deficit conservation failed",
                            )
                            checked += 1
    return checked


def check_rounding_envelope() -> None:
    coordinate_bound = Fraction(5 * 5, 14)
    require(coordinate_bound == Fraction(25, 14), "coordinate rounding bound failed")
    total_bound = 4 * coordinate_bound
    require(total_bound == Fraction(50, 7), "four-coordinate rounding bound failed")

    # Exact monotonicity audit: decreasing the allowed denominator or
    # increasing the displacement can only worsen the bound.
    for displacement in range(0, 6):
        for denominator in range(14, 41):
            term = Fraction(displacement * displacement, denominator)
            require(term <= Fraction(25, 14), "coordinate envelope was violated")


def main() -> None:
    package = read(PACKAGE)
    audit = read(AUDIT)
    contracts = read(CONTRACTS)

    check_structure(package, audit, contracts)
    check_exact_constant_ledger()
    midpoint_cases = check_midpoint_ceiling()
    tangent_cases = check_tangent_correction()
    check_rounding_envelope()

    print("ERDOS 625 E625-10 FIRST-MOMENT CONTRACT: PASS")
    print(f"  midpoint ceiling cases: {midpoint_cases}")
    print(f"  tangent conservation cases: {tangent_cases}")
    print("  exact rounding loss: 50/7")
    print("  public rate endpoint: (1/2) log(200/153)")
    print("  theorem status: design-frozen only; Lean proof not claimed")


if __name__ == "__main__":
    main()
