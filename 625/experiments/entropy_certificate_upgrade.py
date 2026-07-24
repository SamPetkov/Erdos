#!/usr/bin/env python3
"""Exact rational checks and numerical support scans for Erdős 625.

The exact checks certify the proposed strengthening
    D_4(delta) < log(33/25),
    log(2) - D_4(delta) > log(50/33),
conditional only on the displayed elementary weight comparison argument.

The support scans are diagnostics, not proofs.
"""

from __future__ import annotations

from fractions import Fraction
import math
from typing import Sequence


# Rational intervals used in the exact certificate.
Q_LO = Fraction(693147, 10**6)
Q_HI = Fraction(693148, 10**6)
X_LO = Fraction(1071773, 10**6)
X_HI = Fraction(1071774, 10**6)


def certify_log_two_interval(terms: int = 8) -> None:
    """Certify Q_LO < log(2) < Q_HI using log(2)=2*atanh(1/3)."""
    a = Fraction(1, 3)
    partial = sum(
        (2 * a ** (2 * k + 1)) / (2 * k + 1)
        for k in range(terms)
    )
    # For k >= terms, 1/(2k+1) <= 1/(2*terms+1).
    tail = (
        Fraction(2, 2 * terms + 1)
        * a ** (2 * terms + 1)
        / (1 - a * a)
    )
    assert Q_LO < partial
    assert partial + tail < Q_HI


def certify_tenth_root_interval() -> None:
    """Certify X_LO < 2^(1/10) < X_HI by exact integer arithmetic."""
    assert X_LO**10 < 2 < X_HI**10


def certify_tilt_bracket() -> None:
    """Certify the four-support mean brackets at 12q/5 and 21q/5."""
    # At lambda=(12/5)q, after dividing the four weights by x^(-5),
    # their exponents are 33, 32, 21, 0 for deficits 2,3,4,5.
    numerator_hi = 2 * X_HI**33 + 3 * X_HI**32 + 4 * X_HI**21 + 5
    denominator_lo = X_LO**33 + X_LO**32 + X_LO**21 + 1
    assert Q_HI * numerator_hi < 2 * denominator_lo

    # At lambda=(21/5)q, the unnormalised exponents are 64,81,88,85.
    # The desired inequality mean > 1+2/q is equivalent to the positive
    # sum of (q(i-1)-2)w_i. Bound negative terms downward with X_HI and
    # positive terms downward with X_LO.
    lower_sum = Fraction(0)
    for i, exponent in ((2, 64), (3, 81), (4, 88), (5, 85)):
        coefficient = Q_LO * (i - 1) - 2
        x_power = X_HI**exponent if coefficient < 0 else X_LO**exponent
        lower_sum += coefficient * x_power
    assert lower_sum > 0


def certify_omitted_weight_bounds() -> None:
    """Certify L(12q/5)<3/10 and H(21q/5)<1/5."""
    # At 12q/5, after dividing by the deficit -1 weight, the low numerator
    # has exponents 0,29,48 and the retained denominator 57,56,45,24.
    low_num_hi = 1 + X_HI**29 + X_HI**48
    kept_den_lo = X_LO**57 + X_LO**56 + X_LO**45 + X_LO**24
    assert 10 * low_num_hi < 3 * kept_den_lo

    # At 21q/5, the first omitted high weight (deficit 6) has exponent 72.
    # Subsequent ratios are at most x^(-23), so the whole tail is bounded by
    # x^72/(1-x^(-23)).
    high_tail_hi = X_HI**72 / (1 - X_LO**(-23))
    kept_den_lo = X_LO**64 + X_LO**81 + X_LO**88 + X_LO**85
    assert 5 * high_tail_hi < kept_den_lo

    # Recheck the two existing lambda=3q estimates with 0.7 < 2^(-1/2) < 0.71.
    b_lo = Fraction(7, 10)
    b_hi = Fraction(71, 100)
    denominator_lo = Fraction(5, 4) + 2 * b_lo
    low_num_hi = Fraction(1, 256) + b_hi / 16 + Fraction(1, 4)
    high_num_hi = b_hi / 16 + Fraction(1, 256) + Fraction(1, 3968)
    assert 25 * low_num_hi < 3 * denominator_lo   # L(3q) < 3/25
    assert 50 * high_num_hi < denominator_lo      # H(3q) < 1/50


def value_function(support: Sequence[int], target: float) -> tuple[float, float]:
    """Return (tilt, entropy-quadratic value) for a finite support."""
    def moments(lam: float) -> tuple[float, float]:
        scores = [lam * i - math.log(2) * i * i / 2 for i in support]
        maximum = max(scores)
        weights = [math.exp(score - maximum) for score in scores]
        total = sum(weights)
        mean = sum(i * weight for i, weight in zip(support, weights)) / total
        return mean, maximum + math.log(total)

    low, high = -16.0, 16.0
    for _ in range(100):
        mid = (low + high) / 2
        mean, _ = moments(mid)
        if mean < target:
            low = mid
        else:
            high = mid
    lam = (low + high) / 2
    _, log_partition = moments(lam)
    return lam, log_partition - lam * target


def scan_supports() -> None:
    """Numerically compare selected finite supports over the full phase interval."""
    q = math.log(2)
    target_lo = 2 / q
    target_hi = 1 + 2 / q
    infinite_proxy = tuple(range(-1, 80))
    supports: dict[str, tuple[int, ...]] = {
        "{2,3,4,5}": (2, 3, 4, 5),
        "{2,3,4,5,6}": (2, 3, 4, 5, 6),
        "{2,3,5}": (2, 3, 5),
        "{2,4,5}": (2, 4, 5),
        "{1,2,3,4,5}": (1, 2, 3, 4, 5),
    }

    print("\nNumerical diagnostics (not proof):")
    for name, support in supports.items():
        minimum = float("inf")
        argmin = None
        for step in range(2001):
            target = target_lo + (target_hi - target_lo) * step / 2000
            _, full_value = value_function(infinite_proxy, target)
            _, finite_value = value_function(support, target)
            advantage = q - (full_value - finite_value)
            if advantage < minimum:
                minimum = advantage
                argmin = target
        print(f"  {name:15s} min(q-D)={minimum:.12f} at T={argmin:.12f}")

    old_gamma = math.log(200 / 153)
    new_gamma = math.log(50 / 33)
    actual_s4 = 0.5207013354912283
    print("\nConstants:")
    print(f"  old certificate gamma       = {old_gamma:.12f}")
    print(f"  proposed certificate gamma  = {new_gamma:.12f}")
    print(f"  numerical S4 minimum         = {actual_s4:.12f}")
    print(f"  current displayed constant   = {q*q*old_gamma/32:.12f}")
    print(f"  carry-(5.11)+new certificate = {q*q*new_gamma/8:.12f}")


def main() -> None:
    certify_log_two_interval()
    certify_tenth_root_interval()
    certify_tilt_bracket()
    certify_omitted_weight_bounds()
    print("EXACT CERTIFICATE CHECKS: PASS")
    scan_supports()


if __name__ == "__main__":
    main()
