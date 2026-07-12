"""Exact-rational certificates used in CONSTRAINED_PROFILE_AUDIT.md.

This is deliberately narrower than constrained_profile.py.  It does not scan
the phase interval.  Instead it proves, with Fraction arithmetic and explicit
Taylor/tail remainders, the coarse endpoint bounds needed by the analytic
prefix argument:

* mean(2.61) < 3.85, mean(2.64) < 3.88 and mean(2.68) > 3.92;
* on the capped family, 0.10 < y_2 < 0.11 and 0.26 < y_3 < 0.28;
  on the larger family needed for every slack 0 <= d <= c, the respective
  upper bounds are 0.12 and 0.29 (interpolation uses monotonicity from the
  audit note);
* the resulting elementary lower bounds for the s=2 and s=3 prefix rates are
  positive.

No floating-point number is used in an assertion.
"""

from __future__ import annotations

from decimal import Decimal, localcontext
from fractions import Fraction
from math import isqrt


F = Fraction
TAYLOR_TERMS = 70
TAIL_START = 21
SQRT_SCALE = 10**60


def exp_interval(x: Fraction) -> tuple[Fraction, Fraction]:
    """Rigorous rational enclosure of exp(x), for 0 < x < 4.

    Expand exp(x/4), bound its positive Taylor tail by a geometric series,
    and then take fourth powers.  Every operation is exact in Fraction.
    """

    y = x / 4
    term = F(1)
    partial = term
    for k in range(1, TAYLOR_TERMS + 1):
        term *= y / k
        partial += term
    next_term = term * y / (TAYLOR_TERMS + 1)
    ratio_bound = y / (TAYLOR_TERMS + 2)
    upper = partial + next_term / (1 - ratio_bound)
    return partial**4, upper**4


_sqrt_floor = isqrt(2 * SQRT_SCALE**2)
SQRT2_LO = F(_sqrt_floor, SQRT_SCALE)
SQRT2_HI = F(_sqrt_floor + 1, SQRT_SCALE)


def two_to_half_integer_interval(
    twice_exponent: int,
) -> tuple[Fraction, Fraction]:
    integer_part, odd = divmod(twice_exponent, 2)
    power = F(2**integer_part)
    if not odd:
        return power, power
    return power * SQRT2_LO, power * SQRT2_HI


def family_statistics(
    mu: Fraction,
) -> dict[str, tuple[Fraction, Fraction]]:
    """Enclose mean, y_2 and y_3 for weights exp(mu*i) 2^(-i^2/2)."""

    exp_lo, exp_hi = exp_interval(mu)

    # Relative to the i=2 weight, put j=i-2.  The relative weight is
    # exp(mu*j) 2^[-(j^2+4j)/2].
    relative: list[tuple[Fraction, Fraction]] = []
    for j in range(TAIL_START + 1):
        den_lo, den_hi = two_to_half_integer_interval(j * j + 4 * j)
        relative.append((exp_lo**j / den_hi, exp_hi**j / den_lo))

    # Sum j=0,...,TAIL_START-1 exactly by intervals.  Bound the remaining
    # tail by a geometric series.  From j onward, the ratio to the next term
    # is exp(mu)/2^(j+5/2), and hence decreases by a factor two each step.
    z_lo = sum(item[0] for item in relative[:TAIL_START])
    z_hi = sum(item[1] for item in relative[:TAIL_START])
    d_lo = sum(F(j) * relative[j][0] for j in range(TAIL_START))
    d_hi = sum(F(j) * relative[j][1] for j in range(TAIL_START))

    first_tail_hi = relative[TAIL_START][1]
    ratio_den_lo, _ = two_to_half_integer_interval(2 * TAIL_START + 5)
    ratio = exp_hi / ratio_den_lo
    tail_mass = first_tail_hi / (1 - ratio)
    tail_first_moment = first_tail_hi * (
        F(TAIL_START) / (1 - ratio) + ratio / (1 - ratio) ** 2
    )
    z_hi += tail_mass
    d_hi += tail_first_moment

    return {
        "mean": (F(2) + d_lo / z_hi, F(2) + d_hi / z_lo),
        "y2": (1 / z_hi, 1 / z_lo),
        "y3": (relative[1][0] / z_hi, relative[1][1] / z_lo),
    }


def decimal_string(value: Fraction, places: int = 18) -> str:
    with localcontext() as context:
        context.prec = places + 10
        return format(Decimal(value.numerator) / Decimal(value.denominator), f".{places}f")


def show(name: str, interval: tuple[Fraction, Fraction]) -> None:
    print(
        f"{name}: [{decimal_string(interval[0])}, "
        f"{decimal_string(interval[1])}]"
    )


def main() -> None:
    very_low = family_statistics(F(261, 100))
    low = family_statistics(F(264, 100))
    high = family_statistics(F(268, 100))

    # These are exact comparisons of rational numbers.
    assert very_low["mean"][1] < F(385, 100)
    assert low["mean"][1] < F(388, 100)
    assert high["mean"][0] > F(392, 100)
    assert high["y2"][0] > F(10, 100)
    assert low["y2"][1] < F(11, 100)
    assert high["y3"][0] > F(26, 100)
    assert low["y3"][1] < F(28, 100)
    assert very_low["y2"][1] < F(12, 100)
    assert very_low["y3"][1] < F(29, 100)

    # Use -ln(1-z) >= z, ln(2)/2 < 0.347, R < 3.92 and the
    # certified coordinate bounds.  These are conservative rate bounds.
    phi2_lower = F(10, 100) * F(90, 100) - F(347, 1000) * F(
        11, 100
    ) * F(192, 100)
    phi3_lower = F(36, 100) * F(64, 100) - F(347, 1000) * (
        F(192, 100) * F(11, 100) + F(92, 100) * F(28, 100)
    )
    assert phi2_lower == F(5223, 312500) > 0
    assert phi3_lower == F(42329, 625000) > 0

    slack_phi2_lower = F(9, 100) - F(347, 1000) * F(12, 100) * F(
        192, 100
    )
    slack_phi3_lower = F(36, 100) * F(64, 100) - F(347, 1000) * (
        F(192, 100) * F(12, 100) + F(92, 100) * F(29, 100)
    )
    assert slack_phi2_lower == F(3141, 312500) > 0
    assert slack_phi3_lower == F(144679, 2500000) > 0

    print("mu = 2.61")
    for key, value in very_low.items():
        show(key, value)
    print("mu = 2.64")
    for key, value in low.items():
        show(key, value)
    print("mu = 2.68")
    for key, value in high.items():
        show(key, value)
    print(f"certified phi_2 lower bound: {decimal_string(phi2_lower)}")
    print(f"certified phi_3 lower bound: {decimal_string(phi3_lower)}")
    print(
        "certified slack-family phi_2 lower bound: "
        f"{decimal_string(slack_phi2_lower)}"
    )
    print(
        "certified slack-family phi_3 lower bound: "
        f"{decimal_string(slack_phi3_lower)}"
    )
    print("all exact-rational assertions passed")


if __name__ == "__main__":
    main()
