#!/usr/bin/env python3
"""Exact rational ledger for the partial-diagonal scalar rate split.

This script checks only the finite rational inequalities used after the
analytic logarithmic and four-deficit structural reductions.  It does not
prove those reductions, the uniform Stirling estimate, or the final
empty/central/full-corner assembly.
"""

from __future__ import annotations

from fractions import Fraction


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def main() -> None:
    # With z = 1/3,
    # log 2 = 2 * sum_{m >= 0} z^(2m+1)/(2m+1).
    # The first two positive terms give the lower certificate.  Bounding every
    # denominator in the tail m >= 1 below by 3 gives the upper certificate.
    q_lower = 2 * (Fraction(1, 3) + Fraction(1, 81))
    q_upper = 2 * (Fraction(1, 3) + Fraction(1, 72))
    require(q_lower == Fraction(56, 81), "unexpected lower certificate for log 2")
    require(q_upper == Fraction(25, 36), "unexpected upper certificate for log 2")
    require(q_lower > Fraction(2, 3), "lower bound log 2 > 2/3 failed")
    require(q_upper < Fraction(7, 10), "upper bound log 2 < 7/10 failed")

    # Small-R range: R in [1/64, 3/4].
    # The logarithmic estimate contributes 2/(1+R), whose minimum on this
    # range is 8/7.  The q-term contributes at most 21/20.
    split = Fraction(3, 4)
    log_coefficient = Fraction(2, 1) / (1 + split)
    reward_coefficient = Fraction(7, 10) * Fraction(3, 2)
    coefficient_gap = log_coefficient - reward_coefficient
    small_range_margin = coefficient_gap * Fraction(1, 64)
    require(log_coefficient == Fraction(8, 7), "small-range log coefficient drifted")
    require(reward_coefficient == Fraction(21, 20), "small-range reward coefficient drifted")
    require(coefficient_gap == Fraction(13, 140), "small-range coefficient gap drifted")
    require(small_range_margin == Fraction(13, 8960), "small-range margin drifted")
    require(
        small_range_margin > Fraction(1, 5000),
        "small-range 1/5000 margin failed",
    )

    # Large-R range: R in [3/4, 1].  The phase corridor gives T < 4, so the
    # right structural bound contributes at most q(1-R).  Hence q-R is at most
    # 7/10 - 3/4 = -1/20.
    large_range_margin = split - Fraction(7, 10)
    require(large_range_margin == Fraction(1, 20), "large-range margin drifted")
    require(
        large_range_margin > Fraction(1, 5000),
        "large-range 1/5000 margin failed",
    )

    print("ERDOS 625 PARTIAL-DIAGONAL SCALAR LEDGER: PASS")
    print(f"  log 2 lower: {q_lower}")
    print(f"  log 2 upper: {q_upper}")
    print(f"  split point: {split}")
    print(f"  small-range coefficient gap: {coefficient_gap}")
    print(f"  small-range uniform margin: {small_range_margin}")
    print(f"  large-range uniform margin: {large_range_margin}")
    print("  scope: rational ledger only; analytic and asymptotic reductions are external")


if __name__ == "__main__":
    main()
