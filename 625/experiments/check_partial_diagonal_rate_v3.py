#!/usr/bin/env python3
"""Exact rational endpoint certificate for the partial-diagonal rate split.

This script checks only the finite rational arithmetic used at the endpoints of
the two convex ranges.  The analytic convexity argument and the uniform
Stirling reduction remain mathematical proof obligations; the script is not a
substitute for either one.
"""

from __future__ import annotations

from fractions import Fraction


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def main() -> None:
    # With z = 1/3,
    # log 2 = 2 * sum_{m >= 0} z^(2m+1)/(2m+1).
    q_lower = 2 * (Fraction(1, 3) + Fraction(1, 81))
    q_upper = 2 * (Fraction(1, 3) + Fraction(1, 72))
    require(q_lower == Fraction(56, 81), "unexpected lower certificate for log 2")
    require(q_upper == Fraction(25, 36), "unexpected upper certificate for log 2")
    require(q_lower > Fraction(69, 100), "lower bound for log 2 failed")
    require(q_lower > Fraction(2, 3), "coarse lower bound for log 2 failed")
    require(q_upper < Fraction(7, 10), "upper bound for log 2 failed")

    # For x = 100/47, the same atanh expansion has
    # z = (x - 1)/(x + 1) = 53/147.
    z = Fraction(53, 147)
    log_100_over_47_lower = 2 * (z + z**3 / 3)
    require(
        log_100_over_47_lower == Fraction(7169416, 9529569),
        "displayed lower certificate for log(100/47) drifted",
    )
    require(
        log_100_over_47_lower > Fraction(3, 4),
        "lower bound for log(100/47) failed",
    )

    split_left = Fraction(1, 64)
    split_middle = Fraction(47, 100)
    split_right = Fraction(1)
    require(split_left < split_middle < split_right, "rate split is not ordered")

    # First convex range.  After adding (1-R)/5000, the coefficient of R is
    # largest at T = 2/q.  The bounds q >= 2/3 and q < 7/10 give the following
    # two rational endpoint majorants.
    first_left_endpoint = (
        -(Fraction(7, 2) * Fraction(2, 3) + 1) / 64
        + Fraction(63, 320000)
    )
    first_right_endpoint = (
        -Fraction(47, 100) * log_100_over_47_lower
        + Fraction(141, 400)
        + Fraction(53, 500000)
    )
    require(
        first_left_endpoint == Fraction(-49811, 960000),
        "first endpoint R=1/64 arithmetic drifted",
    )
    require(
        first_right_endpoint == Fraction(-4721156593, 4764784500000),
        "first endpoint R=47/100 arithmetic drifted",
    )

    # Second convex range.  After adding (1-R)/200, q > 69/100 bounds the
    # coefficient by 33/50.  The right endpoint is exactly zero.
    second_left_endpoint = (
        -Fraction(47, 100) * log_100_over_47_lower
        + Fraction(53, 100) * Fraction(33, 50)
    )
    second_right_endpoint = Fraction(0)
    require(
        second_left_endpoint == Fraction(-180911419, 47647845000),
        "second endpoint R=47/100 arithmetic drifted",
    )
    require(second_right_endpoint == 0, "second endpoint R=1 arithmetic drifted")

    require(first_left_endpoint < 0, "first rate bound failed at R=1/64")
    require(first_right_endpoint < 0, "first rate bound failed at R=47/100")
    require(second_left_endpoint < 0, "second rate bound failed at R=47/100")

    print("ERDOS 625 PARTIAL-DIAGONAL ENDPOINT CERTIFICATE: PASS")
    print(f"  log 2 lower: {q_lower}")
    print(f"  log 2 upper: {q_upper}")
    print(f"  log(100/47) lower: {log_100_over_47_lower}")
    print(f"  first endpoint R=1/64: {first_left_endpoint}")
    print(f"  first endpoint R=47/100: {first_right_endpoint}")
    print(f"  second endpoint R=47/100: {second_left_endpoint}")
    print("  scope: endpoint arithmetic only; convexity and uniform asymptotics are external")


if __name__ == "__main__":
    main()
