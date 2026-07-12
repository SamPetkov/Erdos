"""Numerics for the candidate exceptional-profile phase below x0.

Only the Python standard library is used.  The calculation is at the limiting
profile level; it is not a proof of a finite-n random-graph statement.
"""

from __future__ import annotations

import math


Q = math.log(2.0)
X0 = 0.0290543918664065
IMAX = 120


def single_prefix_rate(x: float, z: float) -> float:
    """Rate for a partial profile containing only i=1 classes."""
    if z == 1.0:
        return z * (Q * x / 2.0 - 1.0)
    return -(1.0 - z) * math.log1p(-z) + z * (Q * x / 2.0 - 1.0)


def feasibility_cap(x: float) -> float:
    """Positive root of the single-prefix rate; cap(0) is defined as zero."""
    if x <= 0.0:
        return 0.0
    lo = 0.0
    hi = min(0.5, 2.0 * Q * x + 0.01)
    while single_prefix_rate(x, hi) > 0.0:
        hi = min(0.999, 1.5 * hi + 0.001)
    for _ in range(100):
        mid = (lo + hi) / 2.0
        if single_prefix_rate(x, mid) > 0.0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2.0


def tilted_mean(mu: float, first: int = 2, last: int = IMAX) -> float:
    logs = [mu * i - Q * i * i / 2.0 for i in range(first, last + 1)]
    shift = max(logs)
    weights = [math.exp(value - shift) for value in logs]
    normalizer = sum(weights)
    return sum(i * w for i, w in zip(range(first, last + 1), weights)) / normalizer


def constrained_profile(x: float) -> tuple[float, float, list[float]]:
    """Return (T, mu, zeta), with zeta indexed by i and zeta[0] unused."""
    cap = feasibility_cap(x)
    target_mean = 1.0 + 2.0 / Q - x
    residual_mean = (target_mean - cap) / (1.0 - cap)

    lo, hi = -20.0, 20.0
    while tilted_mean(lo) > residual_mean:
        lo *= 2.0
    while tilted_mean(hi) < residual_mean:
        hi *= 2.0
    for _ in range(100):
        mid = (lo + hi) / 2.0
        if tilted_mean(mid) < residual_mean:
            lo = mid
        else:
            hi = mid
    mu = (lo + hi) / 2.0

    logs = [mu * i - Q * i * i / 2.0 for i in range(2, IMAX + 1)]
    shift = max(logs)
    weights = [math.exp(value - shift) for value in logs]
    normalizer = sum(weights)
    zeta = [0.0, cap]
    zeta.extend((1.0 - cap) * weight / normalizer for weight in weights)
    return target_mean, mu, zeta


def prefix_rates(x: float) -> list[tuple[int, float, float]]:
    target_mean, _, zeta = constrained_profile(x)
    mass = 0.0
    moment = 0.0
    answer: list[tuple[int, float, float]] = []
    for i in range(1, len(zeta)):
        mass += zeta[i]
        moment += zeta[i] * (i - target_mean)
        if 1.0 - mass > 1e-14:
            entropy = -(1.0 - mass) * math.log1p(-mass)
        else:
            entropy = 0.0
        answer.append((i, mass, entropy + Q * moment / 2.0))
    return answer


def main() -> None:
    sample_x = [0.0, 1e-6, 1e-4, 0.001, 0.005, 0.01, 0.02, X0]
    print("x, cap, cap/(q*x), mu, min_prefix_rate_for_mass_[.001,.999]")
    for x in sample_x:
        target_mean, mu, _ = constrained_profile(x)
        cap = feasibility_cap(x)
        candidates = [
            (rate, i, mass)
            for i, mass, rate in prefix_rates(x)
            if i >= 2 and 0.001 <= mass <= 0.999
        ]
        minimum = min(candidates)
        ratio = cap / (Q * x) if x > 0.0 else 1.0
        print(
            f"{x:.12g}, {cap:.12g}, {ratio:.9f}, {mu:.9f}, "
            f"{minimum[0]:.12g} (i={minimum[1]}, mass={minimum[2]:.9f}, "
            f"T={target_mean:.9f})"
        )

    global_minimum = (float("inf"), 0.0, 0, 0.0)
    negative = []
    for step in range(1001):
        x = X0 * step / 1000.0
        for i, mass, rate in prefix_rates(x):
            if i >= 2 and 0.001 <= mass <= 0.999:
                if rate < global_minimum[0]:
                    global_minimum = (rate, x, i, mass)
                if rate < -1e-10:
                    negative.append((x, i, mass, rate))

    rate, x, i, mass = global_minimum
    print(
        "grid minimum: "
        f"rate={rate:.12g}, x={x:.12g}, i={i}, mass={mass:.12g}"
    )
    print(f"negative grid values below -1e-10: {len(negative)}")


if __name__ == "__main__":
    main()
