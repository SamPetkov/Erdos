#!/usr/bin/env python3
"""Exact rational endpoint checks for the partial-diagonal rate function."""

from __future__ import annotations

from fractions import Fraction


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def main() -> None:
    # With z=1/3,
    # log 2 = 2 * sum_{m>=0} z^(2m+1)/(2m+1).
    q_lower = 2 * (Fraction(1, 3) + Fraction(1, 81))
    q_upper = 2 * (Fraction(1, 3) + Fraction(1, 72))
    require(q_lower > Fraction(69, 100), "lower bound for log 2 failed")
    require(q_upper < Fraction(7, 10), "upper bound for log 2 failed")

    # For x=100/47, the same atanh expansion has z=(x-1)/(x+1)=53/147.
    z = Fraction(53, 147)
    log_100_over_47_lower = 2 * (z + z**3 / 3)
    require(
        log_100_over_47_lower > Fraction(3, 4),
        "lower bound for log(100/47) failed",
    )

    # First convex rate bound, after adding (1-R)/5000.
    first_left_endpoint = (
        -(Fraction(7, 2) * Fraction(2, 3) + 1) / 64
        + Fraction(63, 320000)
    )
    first_right_endpoint = (
        -Fraction(47, 100) * log_100_over_47_lower
        + Fraction(47, 100) * Fraction(3, 4)
        + Fraction(53, 500000)
    )

    # Second convex rate bound, after adding (1-R)/200.
    second_left_endpoint = (
        -Fraction(47, 100) * log_100_over_47_lower
        + Fraction(53, 100) * Fraction(33, 50)
    )
    second_right_endpoint = Fraction(0)

    require(first_left_endpoint < 0, "first rate bound failed at R=1/64")
    require(first_right_endpoint < 0, "first rate bound failed at R=47/100")
    require(second_left_endpoint < 0, "second rate bound failed at R=47/100")
    require(second_right_endpoint == 0, "second rate bound failed at R=1")

    print("ERDOS 625 PARTIAL-DIAGONAL RATE CERTIFICATE: PASS")
    print(f"  log 2 lower: {q_lower} = {float(q_lower):.15f}")
    print(f"  log 2 upper: {q_upper} = {float(q_upper):.15f}")
    print(
        "  log(100/47) lower: "
        f"{log_100_over_47_lower} = {float(log_100_over_47_lower):.15f}"
    )
    print(f"  first endpoint R=1/64: {first_left_endpoint}")
    print(f"  first endpoint R=47/100: {first_right_endpoint}")
    print(f"  second endpoint R=47/100: {second_left_endpoint}")


if __name__ == "__main__":
    main()
