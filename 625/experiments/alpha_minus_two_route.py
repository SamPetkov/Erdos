"""Reproduce the limiting entropy calculations for the alpha-2 route.

Only the Python standard library is used.  This is a numerical diagnostic;
the uniform inequalities used in ALPHA_MINUS_TWO_ROUTE.md are proved there
by elementary bounds on the partition-function tails.
"""

from __future__ import annotations

import math


Q = math.log(2.0)
T_MIN = 2.0 / Q
T_MAX = 1.0 + 2.0 / Q


def tilted_value(indices: range, target_mean: float) -> tuple[float, float]:
    """Return (tilt, max entropy-energy value) on ``indices``.

    The value is

        max_p {-sum p_i log p_i - (log 2)/2 sum i^2 p_i},

    subject to sum i p_i = target_mean.
    """

    def mean_and_log_z(mu: float) -> tuple[float, float]:
        exponents = [mu * i - Q * i * i / 2.0 for i in indices]
        maximum = max(exponents)
        weights = [math.exp(value - maximum) for value in exponents]
        total = sum(weights)
        mean = sum(i * weight for i, weight in zip(indices, weights)) / total
        return mean, maximum + math.log(total)

    lower, upper = -20.0, 20.0
    for _ in range(90):
        middle = (lower + upper) / 2.0
        if mean_and_log_z(middle)[0] < target_mean:
            lower = middle
        else:
            upper = middle
    mu = (lower + upper) / 2.0
    _, log_z = mean_and_log_z(mu)
    return mu, log_z - mu * target_mean


def omitted_ratio(mu: float, retained: range) -> tuple[float, float, float]:
    """Low, high, and total omitted partition mass relative to retained mass."""

    denominator = sum(math.exp(mu * i - Q * i * i / 2.0) for i in retained)
    low = sum(math.exp(mu * i - Q * i * i / 2.0) for i in range(-1, retained.start))
    high = sum(
        math.exp(mu * i - Q * i * i / 2.0)
        for i in range(retained.stop, 80)
    )
    return low / denominator, high / denominator, (low + high) / denominator


def main() -> None:
    full = range(-1, 40)
    alpha_minus_two = range(2, 40)
    four_type = range(2, 6)

    extrema = {
        "i>=2": [[math.inf, None], [-math.inf, None]],
        "2<=i<=5": [[math.inf, None], [-math.inf, None]],
    }

    print("delta,T,D_i>=2,D_2..5,margin_i>=2,margin_2..5")
    for step in range(1001):
        delta = step / 1000.0
        target = T_MAX - delta
        _, full_value = tilted_value(full, target)
        _, tail_value = tilted_value(alpha_minus_two, target)
        _, four_value = tilted_value(four_type, target)
        losses = (full_value - tail_value, full_value - four_value)

        for name, loss in zip(extrema, losses):
            if loss < extrema[name][0][0]:
                extrema[name][0] = [loss, delta]
            if loss > extrema[name][1][0]:
                extrema[name][1] = [loss, delta]

        if step % 100 == 0:
            print(
                f"{delta:.1f},{target:.12f},{losses[0]:.12f},"
                f"{losses[1]:.12f},{Q-losses[0]:.12f},{Q-losses[1]:.12f}"
            )

    print("\n1001-point diagnostics")
    for name, (minimum, maximum) in extrema.items():
        print(
            f"{name}: min loss={minimum[0]:.12f} at delta={minimum[1]:.3f}; "
            f"max loss={maximum[0]:.12f} at delta={maximum[1]:.3f}; "
            f"min signed margin={Q-maximum[0]:.12f}"
        )

    print("\nAnalytic-certificate checkpoints")
    for multiple in (2.0, 3.0, 4.5):
        mu = multiple * Q
        low, high, total = omitted_ratio(mu, four_type)
        print(
            f"mu={multiple:g} ln2: low={low:.12f}, high={high:.12f}, "
            f"total={total:.12f}"
        )

    gamma_tail = math.log(4.0 / 3.0)
    gamma_four = math.log(200.0 / 153.0)
    print("\nCertified margins and safe all-large-n root-gap constants")
    print(
        f"i>=2: gamma={gamma_tail:.12f}, "
        f"safe c=(ln2)^2 gamma/8={Q*Q*gamma_tail/8.0:.12f}"
    )
    print(
        f"2<=i<=5: gamma={gamma_four:.12f}, "
        f"safe c=(ln2)^2 gamma/8={Q*Q*gamma_four/8.0:.12f}; "
        f"midpoint witness keeps c/2={Q*Q*gamma_four/16.0:.12f}"
    )


if __name__ == "__main__":
    main()
