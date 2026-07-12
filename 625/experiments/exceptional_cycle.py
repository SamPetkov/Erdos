"""Numerics for the oscillatory exceptional regime in Erdos problem 625.

This script uses only the Python standard library.  It independently computes
the limiting partial-profile transition x_0 from the equations in Heckel and
Panagiotou, and prints the natural-density and nearby-n constants.
"""

from __future__ import annotations

import math


LOG2 = math.log(2.0)
SQRT2 = math.sqrt(2.0)


def limiting_zeta1(x: float, cutoff: int = 80) -> tuple[float, float]:
    """Return (zeta_1, mu) for the limiting i_0=1 optimal profile.

    The weights are proportional to exp(mu*i - log(2)*i^2/2), i >= 1,
    and mu is selected so their mean is 1 + 2/log(2) - x.  The omitted
    tail at cutoff=80 is far below double precision.
    """

    target_mean = 1.0 + 2.0 / LOG2 - x

    def mean_and_zeta1(mu: float) -> tuple[float, float]:
        log_weights = [mu * i - LOG2 * i * i / 2.0 for i in range(1, cutoff)]
        maximum = max(log_weights)
        weights = [math.exp(value - maximum) for value in log_weights]
        total = sum(weights)
        mean = sum(i * weight for i, weight in enumerate(weights, start=1)) / total
        return mean, weights[0] / total

    lower, upper = -20.0, 20.0
    for _ in range(160):
        midpoint = (lower + upper) / 2.0
        mean, _ = mean_and_zeta1(midpoint)
        if mean < target_mean:
            lower = midpoint
        else:
            upper = midpoint

    mu = (lower + upper) / 2.0
    _, zeta1 = mean_and_zeta1(mu)
    return zeta1, mu


def partial_profile_rate(x: float) -> float:
    """The rate phi(1,x,1) whose zero defines x_0."""

    zeta1, _ = limiting_zeta1(x)
    return -(1.0 - zeta1) * math.log(1.0 - zeta1) + zeta1 * (
        LOG2 * x / 2.0 - 1.0
    )


def transition_x0() -> float:
    lower, upper = 0.0, 0.1
    assert partial_profile_rate(lower) < 0.0 < partial_profile_rate(upper)
    for _ in range(160):
        midpoint = (lower + upper) / 2.0
        if partial_profile_rate(midpoint) < 0.0:
            lower = midpoint
        else:
            upper = midpoint
    return (lower + upper) / 2.0


def density_bounds(a: float, epsilon: float = 0.0) -> tuple[float, float]:
    """Natural lower/upper densities for a+eps <= x <= 1-eps."""

    phase_width = 1.0 - a - 2.0 * epsilon
    if not 0.0 < phase_width <= 1.0:
        raise ValueError("need 0 < 1-a-2*epsilon <= 1")
    lower = (2.0 ** (phase_width / 2.0) - 1.0) / (SQRT2 - 1.0)
    upper = (1.0 - 2.0 ** (-phase_width / 2.0)) / (
        1.0 - 2.0 ** (-0.5)
    )
    return lower, upper


def transfer_constants(a: float, epsilon: float = 0.0) -> tuple[float, float]:
    """Return maximum half-gap/B_next and its relative distance at midpoint."""

    lower_phase = a + epsilon
    upper_phase = 1.0 - epsilon
    u = 2.0 ** (lower_phase / 2.0)
    v = 2.0 ** (upper_phase / 2.0)
    half_gap_over_next_cycle_start = (u - v / SQRT2) / 2.0
    relative_midpoint_distance = (SQRT2 * u - v) / (SQRT2 * u + v)
    return half_gap_over_next_cycle_start, relative_midpoint_distance


def expansion_constant(delta: float) -> float:
    """K(delta) in log mu_alpha = delta*N + A(delta)*log N + K + o(1)."""

    c = 1.0 + math.log(LOG2) - LOG2
    return (
        delta * c
        + LOG2 * delta * (1.0 - delta) / 2.0
        - 2.0 * c / LOG2
        - (1.0 - delta)
        - math.log(2.0 * math.pi) / 2.0
        - LOG2 / 2.0
        + math.log(LOG2) / 2.0
    )


def main() -> None:
    x0 = transition_x0()
    zeta1, mu = limiting_zeta1(x0)
    print(f"x0 = {x0:.15f}")
    print(f"phi(x0) = {partial_profile_rate(x0):.3e}")
    print(f"zeta_1(x0) = {zeta1:.15f}, mu(x0) = {mu:.15f}")

    for a in (0.05, x0):
        lower, upper = density_bounds(a)
        half_gap, relative = transfer_constants(a)
        print(
            f"a={a:.15f}: density liminf={lower:.15f}, "
            f"limsup={upper:.15f}, half-gap/B={half_gap:.15f}, "
            f"midpoint relative distance={relative:.15f}"
        )

    print("\nK(delta) and logarithmic-power coefficient:")
    for delta in (0.0, 0.05, 0.5, 1.0):
        coefficient = 2.0 / LOG2 - 0.5 - delta
        print(
            f"delta={delta:.2f}: A(delta)={coefficient:.15f}, "
            f"K(delta)={expansion_constant(delta):.15f}"
        )


if __name__ == "__main__":
    main()
