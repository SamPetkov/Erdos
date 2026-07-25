#!/usr/bin/env python3
"""Exact and high-precision regression checks for the Erdős 625 full audit.

This script is deliberately standard-library only. It checks finite arithmetic
claims used by the audit and prints diagnostic asymptotic scale comparisons.
It does not claim to prove the manuscript's missing Section 8/9 integration.
"""

from __future__ import annotations

from decimal import Decimal, getcontext
from fractions import Fraction
from itertools import combinations
from math import comb


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def floor_fraction(x: Fraction) -> int:
    return x.numerator // x.denominator


def ceil_fraction(x: Fraction) -> int:
    return -((-x.numerator) // x.denominator)


def check_rounding_lemma() -> int:
    """Exhaust a rational grid for the deterministic midpoint inequality."""

    checked = 0
    denominator = 12
    values = [Fraction(i, denominator) for i in range(-24, 61)]
    losses = [Fraction(i, denominator) for i in range(0, 37)]

    for x in values:
        for y in values:
            if x <= y:
                continue
            for loss in losses:
                lhs = (
                    floor_fraction(x)
                    - ceil_fraction(loss)
                    - ceil_fraction((x + y) / 2)
                )
                rhs = (x - y) / 2 - loss - 3
                require(
                    Fraction(lhs, 1) > rhs,
                    f"rounding lemma failed for x={x}, y={y}, L={loss}",
                )
                checked += 1
    return checked


def check_balanced_binomial_penalty(limit: int = 600) -> int:
    """Check 2^k / C(k,floor(k/2)) <= k+1 exactly."""

    for k in range(1, limit + 1):
        central = comb(k, k // 2)
        require(
            central * (k + 1) >= 2**k,
            f"central-binomial average bound failed at k={k}",
        )
    return limit


def even_edge_sets(edges: list[tuple[int, int]], vertices: list[int]) -> list[int]:
    result: list[int] = []
    for mask in range(1 << len(edges)):
        parity = {v: 0 for v in vertices}
        for index, (u, v) in enumerate(edges):
            if (mask >> index) & 1:
                parity[u] ^= 1
                parity[v] ^= 1
        if all(value == 0 for value in parity.values()):
            result.append(mask)
    return result


def check_matching_restriction() -> tuple[int, int]:
    """Exhaust small complete bipartite graphs and matching restrictions."""

    instances = 0
    even_sets_checked = 0
    for left_size, right_size in ((2, 2), (2, 3), (3, 3)):
        left = list(range(left_size))
        right = list(range(left_size, left_size + right_size))
        vertices = left + right
        edges = [(u, v) for u in left for v in right]
        even_sets = even_edge_sets(edges, vertices)
        edge_index = {edge: i for i, edge in enumerate(edges)}

        matchings: list[tuple[tuple[int, int], ...]] = [tuple()]
        for size in range(1, min(left_size, right_size) + 1):
            for chosen in combinations(edges, size):
                used_left = {u for u, _ in chosen}
                used_right = {v for _, v in chosen}
                if len(used_left) == size and len(used_right) == size:
                    matchings.append(chosen)

        for matching in matchings:
            matching_mask = 0
            for edge in matching:
                matching_mask |= 1 << edge_index[edge]

            images: dict[int, int] = {}
            for mask in even_sets:
                residual = mask & ~matching_mask
                require(
                    residual not in images,
                    (
                        "matching restriction is not injective: "
                        f"K_{{{left_size},{right_size}}}, M={matching}"
                    ),
                )
                images[residual] = mask
                even_sets_checked += 1

            # One exact weighted inequality with rational edge activities.
            weights = [Fraction(i + 1, i + 3) for i in range(len(edges))]
            lhs = Fraction(0, 1)
            for mask in even_sets:
                term = Fraction(1, 1)
                residual = mask & ~matching_mask
                for index, weight in enumerate(weights):
                    if (residual >> index) & 1:
                        term *= weight
                lhs += term

            rhs = Fraction(1, 1)
            for index, weight in enumerate(weights):
                if not ((matching_mask >> index) & 1):
                    rhs *= 1 + weight
            require(lhs <= rhs, "weighted matching-restriction product bound failed")
            instances += 1

    return instances, even_sets_checked


def check_two_thirds_budget(max_m: int = 800) -> int:
    checked = 0
    for m in range(1, max_m + 1):
        for e in range(1, m + 1):
            if 2 * e >= m:
                continue
            lhs = e * ((2 * m) // 3)
            rhs = e * m - (e * (e + 1)) // 2
            require(lhs <= rhs, f"two-thirds exponent budget failed at m={m}, e={e}")
            checked += 1
    return checked


def coefficient_ledger() -> dict[str, Decimal]:
    getcontext().prec = 80
    q = Decimal(2).ln()
    current = q * q * (Decimal(200) / Decimal(153)).ln() / Decimal(32)
    propagated = q * q * (Decimal(200) / Decimal(153)).ln() / Decimal(8)
    entropy_only = q * q * (Decimal(1000) / Decimal(639)).ln() / Decimal(32)
    combined = q * q * (Decimal(1000) / Decimal(639)).ln() / Decimal(8)

    require(propagated == current * 4, "factor-four coefficient identity failed")
    require(combined == entropy_only * 4, "combined factor-four identity failed")
    require(combined > propagated > entropy_only > current > 0, "coefficient ordering failed")

    return {
        "canonical": current,
        "factor_four": propagated,
        "entropy_only": entropy_only,
        "combined": combined,
        "combined_over_canonical": combined / current,
    }


def asymptotic_diagnostics() -> list[tuple[int, Decimal, Decimal]]:
    """Evaluate logarithms of the two subcritical exponent ratios.

    all_high ratio prototype:
      n^(2/3) N^(4/3) / (n/N^4) = exp(-N/3) N^(16/3).

    intrinsic-small-power prototype after the midpoint log correction:
      exp(-N/3) N^(13/3).

    These values are diagnostics for the stated scale comparison, not a proof
    of the profile asymptotics that produce the prototypes.
    """

    getcontext().prec = 80
    rows: list[tuple[int, Decimal, Decimal]] = []
    previous_all: Decimal | None = None
    previous_small: Decimal | None = None
    for nlog in (120, 240, 480, 960, 1920):
        x = Decimal(nlog)
        log_all = -x / 3 + (Decimal(16) / 3) * x.ln()
        log_small = -x / 3 + (Decimal(13) / 3) * x.ln()
        if previous_all is not None:
            require(log_all < previous_all, "all-high log ratio is not decreasing on audit grid")
            require(log_small < previous_small, "small-power log ratio is not decreasing on audit grid")
        previous_all = log_all
        previous_small = log_small
        rows.append((nlog, log_all, log_small))

    require(rows[-1][1] < -100, "all-high diagnostic has not entered a strongly subcritical range")
    require(rows[-1][2] < -100, "small-power diagnostic has not entered a strongly subcritical range")
    return rows


def main() -> None:
    rounding_cases = check_rounding_lemma()
    binomial_cases = check_balanced_binomial_penalty()
    matching_instances, even_sets = check_matching_restriction()
    budget_cases = check_two_thirds_budget()
    coefficients = coefficient_ledger()
    diagnostics = asymptotic_diagnostics()

    print("ERDOS 625 FULL PROOF AUDIT REGRESSION: PASS")
    print(f"  midpoint rounding cases: {rounding_cases}")
    print(f"  balanced central-binomial cases: {binomial_cases}")
    print(f"  matching-restriction instances: {matching_instances}")
    print(f"  even edge sets inspected: {even_sets}")
    print(f"  two-thirds exponent cases: {budget_cases}")
    print("  coefficient ledger:")
    for name, value in coefficients.items():
        print(f"    {name}: {value}")
    print("  asymptotic diagnostic log-ratios (N, all-high, small-power):")
    for nlog, all_high, small_power in diagnostics:
        print(f"    {nlog}: {all_high}, {small_power}")
    print("  scope: finite arithmetic/regression only; Section 8/9 global bridges remain proof obligations")


if __name__ == "__main__":
    main()
