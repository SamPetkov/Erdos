#!/usr/bin/env python3
"""Exact rational certificate for the Erdős 625 four-support constant."""

from __future__ import annotations

from fractions import Fraction


DEN = 10**15
R_LO = Fraction(1035264923841377, DEN)
R_HI = Fraction(1035264923841378, DEN)
LOG_SERIES_TERMS = 200

# These slightly sharper rational cutoffs leave a visible fixed margin in the
# final theorem rather than relying on an unspecified strict inequality.
L49_MAX = Fraction(2629, 10000)
H58_MAX = Fraction(37, 2500)
L58_MAX = Fraction(329, 2500)
H83_MAX = Fraction(357, 2500)
UNIFORM_OMITTED_MAX = Fraction(2777, 10000)
STRONG_RATIO = Fraction(20000, 12777)
TARGET_RATIO = Fraction(1000, 639)
SLACK_RATIO = Fraction(12780, 12777)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def power_bounds(exponent: int) -> tuple[Fraction, Fraction]:
    """Bounds for r**exponent, where r = 2**(1/20)."""
    if exponent >= 0:
        return R_LO**exponent, R_HI**exponent
    return 1 / (R_HI ** (-exponent)), 1 / (R_LO ** (-exponent))


def weight_exponent(p: int, i: int) -> int:
    """Exponent of r at lambda = (p/20) log 2."""
    return p * i - 10 * i * i


def sum_bounds(
    p: int,
    indices: range | list[int],
    coefficients: list[int] | None = None,
) -> tuple[Fraction, Fraction]:
    indices = list(indices)
    if coefficients is None:
        coefficients = [1] * len(indices)
    require(len(indices) == len(coefficients), "coefficient length mismatch")
    lower = Fraction(0)
    upper = Fraction(0)
    for i, coefficient in zip(indices, coefficients):
        lo, hi = power_bounds(weight_exponent(p, i))
        lower += coefficient * lo
        upper += coefficient * hi
    return lower, upper


def quotient_bounds(
    numerator: tuple[Fraction, Fraction],
    denominator: tuple[Fraction, Fraction],
) -> tuple[Fraction, Fraction]:
    n_lo, n_hi = numerator
    d_lo, d_hi = denominator
    require(d_lo > 0, "nonpositive denominator")
    return n_lo / d_hi, n_hi / d_lo


def mean_bounds(p: int) -> tuple[Fraction, Fraction]:
    indices = list(range(2, 6))
    return quotient_bounds(
        sum_bounds(p, indices, indices),
        sum_bounds(p, indices),
    )


def low_tail_bounds(p: int) -> tuple[Fraction, Fraction]:
    return quotient_bounds(
        sum_bounds(p, [-1, 0, 1]),
        sum_bounds(p, range(2, 6)),
    )


def high_tail_upper(p: int) -> Fraction:
    """Bound H by summing w_6 and then using a geometric tail from w_7."""
    denominator_lower, _ = sum_bounds(p, range(2, 6))
    _, w6_upper = power_bounds(weight_exponent(p, 6))
    _, w7_upper = power_bounds(weight_exponent(p, 7))
    # For i >= 7, w_{i+1}/w_i is at most w_8/w_7.
    _, ratio_upper = power_bounds(p - 20 * 7 - 10)
    require(ratio_upper < 1, "tail ratio is not contractive")
    return (w6_upper + w7_upper / (1 - ratio_upper)) / denominator_lower


def log_two_bounds() -> tuple[Fraction, Fraction]:
    partial = sum(
        Fraction(1, k * 2**k)
        for k in range(1, LOG_SERIES_TERMS + 1)
    )
    remainder = Fraction(
        1,
        (LOG_SERIES_TERMS + 1) * 2**LOG_SERIES_TERMS,
    )
    return partial, partial + remainder


def main() -> None:
    require(
        R_LO**20 < 2 < R_HI**20,
        "invalid rational enclosure for 2**(1/20)",
    )

    q_lo, q_hi = log_two_bounds()
    _, m49_hi = mean_bounds(49)
    m83_lo, _ = mean_bounds(83)

    require(q_hi * m49_hi < 2, "lower tilt does not lie below 2/log 2")
    require(
        q_lo * (m83_lo - 1) > 2,
        "upper tilt does not lie above 1+2/log 2",
    )

    _, l49_hi = low_tail_bounds(49)
    _, l58_hi = low_tail_bounds(58)
    h58_hi = high_tail_upper(58)
    h83_hi = high_tail_upper(83)

    require(
        l49_hi < L49_MAX,
        "L(49 log 2 / 20) sharpened certificate failed",
    )
    require(
        h58_hi < H58_MAX,
        "H(29 log 2 / 10) sharpened certificate failed",
    )
    require(
        l58_hi < L58_MAX,
        "L(29 log 2 / 10) sharpened certificate failed",
    )
    require(
        h83_hi < H83_MAX,
        "H(83 log 2 / 20) sharpened certificate failed",
    )

    first_split = L49_MAX + H58_MAX
    second_split = L58_MAX + H83_MAX
    require(
        first_split == UNIFORM_OMITTED_MAX,
        "first split ledger failed",
    )
    require(
        second_split < UNIFORM_OMITTED_MAX,
        "second split ledger failed",
    )
    require(
        1 + UNIFORM_OMITTED_MAX == Fraction(12777, 10000),
        "partition-ratio ledger failed",
    )
    require(
        Fraction(2, 1 + UNIFORM_OMITTED_MAX) == STRONG_RATIO,
        "strong entropy-ratio ledger failed",
    )
    require(
        STRONG_RATIO / TARGET_RATIO == SLACK_RATIO > 1,
        "fixed final-constant slack failed",
    )

    print("ERDOS 625 CONSTANT LEDGER: PASS")
    print(f"  M(49 log 2 / 20) upper: {float(m49_hi):.15f}")
    print(f"  M(83 log 2 / 20) lower: {float(m83_lo):.15f}")
    print(f"  L(49 log 2 / 20) upper: {float(l49_hi):.15f}")
    print(f"  L(29 log 2 / 10) upper: {float(l58_hi):.15f}")
    print(f"  H(29 log 2 / 10) upper: {float(h58_hi):.15f}")
    print(f"  H(83 log 2 / 20) upper: {float(h83_hi):.15f}")
    print(f"  uniform omitted-mass cap: {UNIFORM_OMITTED_MAX}")
    print(f"  strong entropy ratio: {STRONG_RATIO}")
    print(f"  fixed slack ratio over target: {SLACK_RATIO}")


if __name__ == "__main__":
    main()
