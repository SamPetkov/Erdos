#!/usr/bin/env python3
"""Exact and high-precision regression checks for the Erdős 625 full audit.

This script is deliberately standard-library only. It checks finite arithmetic
claims used by the audit and prints diagnostic asymptotic scale comparisons.
It does not claim to formalize the remaining global Section 8
completion/decorations equivalence.
"""

from __future__ import annotations

from decimal import Decimal, getcontext
from fractions import Fraction
from itertools import combinations, product
from math import comb, factorial


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def floor_fraction(x: Fraction) -> int:
    return x.numerator // x.denominator


def ceil_fraction(x: Fraction) -> int:
    return -((-x.numerator) // x.denominator)


def falling(n: int, k: int) -> int:
    require(0 <= k <= n, f"invalid falling factorial ({n})_{{{k}}}")
    value = 1
    for offset in range(k):
        value *= n - offset
    return value


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
        for h in range(1, m + 1):
            if 2 * h >= m:
                continue
            lhs = h * ((2 * m) // 3)
            rhs = h * m - (h * (h + 1)) // 2
            require(lhs <= rhs, f"two-thirds exponent budget failed at m={m}, h={h}")
            checked += 1
    return checked


def local_high_deficit_ratio(m: int, d: int, h: int) -> Fraction:
    """Formula R_{m,d}(h) from the global decoration bridge."""

    denominator = 1
    for t in range(1, h + 1):
        denominator *= d + t
    binary_exponent = h * m - h * (h + 1) // 2
    return Fraction(comb(m, h), denominator * 2**binary_exponent)


def check_local_high_deficit_ratio(max_m: int = 80) -> int:
    """Verify the exact local falling-factorial/reward ratio."""

    checked = 0
    for m in range(3, max_m + 1):
        for d in range(4):
            for h in range((m - 1) // 2 + 1):
                j = m - h
                decorated_local = Fraction(
                    falling(m, j) * falling(m + d, j), factorial(j)
                ) * Fraction(2 ** comb(j, 2), 2)
                full_local = Fraction(
                    falling(m, m) * falling(m + d, m), factorial(m)
                ) * Fraction(2 ** comb(m, 2), 2)
                exact_ratio = decorated_local / full_local
                formula = local_high_deficit_ratio(m, d, h)
                require(
                    exact_ratio == formula,
                    f"local ratio failed at m={m}, d={d}, h={h}",
                )
                checked += 1
    return checked


def check_global_falling_ratio(max_n: int = 100) -> int:
    """Verify (n)_{J+H}/(n)_J=(n-J)_H<=n^H exactly."""

    checked = 0
    for n in range(max_n + 1):
        for j in range(n + 1):
            for h in range(n - j + 1):
                ratio = Fraction(falling(n, j + h), falling(n, j))
                require(
                    ratio == falling(n - j, h),
                    f"falling ratio identity failed at n={n}, J={j}, H={h}",
                )
                require(
                    ratio <= n**h,
                    f"falling ratio bound failed at n={n}, J={j}, H={h}",
                )
                checked += 1
    return checked


def check_global_decoration_product() -> int:
    """Exhaust small matching fibres for the global product comparison."""

    options = [
        (m, d, h)
        for m in range(3, 9)
        for d in range(4)
        for h in range((m - 1) // 2 + 1)
    ]
    checked = 0
    for cell_count in (1, 2, 3):
        for cells in product(options, repeat=cell_count):
            j_total = sum(m - h for m, _d, h in cells)
            full_total = sum(m for m, _d, _h in cells)
            n = full_total + 3
            h_total = full_total - j_total

            denominator_ratio = Fraction(
                falling(n, full_total), falling(n, j_total)
            )
            local_ratio = Fraction(1, 1)
            charged_product = Fraction(1, 1)
            for m, d, h in cells:
                ratio = local_high_deficit_ratio(m, d, h)
                local_ratio *= ratio
                charged_product *= n**h * ratio

            exact_global_ratio = denominator_ratio * local_ratio
            require(
                denominator_ratio == falling(n - j_total, h_total),
                f"global denominator identity failed for cells={cells}",
            )
            require(
                exact_global_ratio <= charged_product,
                f"global decoration product bound failed for cells={cells}",
            )
            checked += 1
    return checked


def check_geometric_decoration_sum() -> int:
    """Check finite deficit fibres against rho/(1-rho) and 2rho."""

    checked = 0
    for denominator in range(2, 31):
        for numerator in range(1, denominator // 2 + 1):
            rho = Fraction(numerator, denominator)
            for max_h in range(1, 31):
                finite_sum = sum((rho**h for h in range(1, max_h + 1)), Fraction())
                require(finite_sum <= rho / (1 - rho), "geometric majorant failed")
                require(finite_sum <= 2 * rho, "two-rho geometric bound failed")
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


def asymptotic_diagnostics() -> list[tuple[int, Decimal, Decimal, Decimal]]:
    """Evaluate logarithms of three subcritical exponent ratios.

    sharp all-high ratio prototype:
      n^(2/3) N^(4/3) / (n/N^4) = exp(-N/3) N^(16/3).

    current formal all-high ratio prototype (one extra factor N):
      n^(2/3) N^(7/3) / (n/N^4) = exp(-N/3) N^(19/3).

    intrinsic-small-power prototype after the midpoint log correction:
      exp(-N/3) N^(13/3).

    These values are diagnostics for the stated scale comparisons, not proofs
    of the profile asymptotics that produce the prototypes.
    """

    getcontext().prec = 80
    rows: list[tuple[int, Decimal, Decimal, Decimal]] = []
    previous_sharp: Decimal | None = None
    previous_formal: Decimal | None = None
    previous_small: Decimal | None = None
    for nlog in (120, 240, 480, 960, 1920):
        x = Decimal(nlog)
        log_sharp = -x / 3 + (Decimal(16) / 3) * x.ln()
        log_formal = -x / 3 + (Decimal(19) / 3) * x.ln()
        log_small = -x / 3 + (Decimal(13) / 3) * x.ln()
        if previous_sharp is not None:
            require(log_sharp < previous_sharp, "sharp all-high ratio is not decreasing")
            require(log_formal < previous_formal, "formal all-high ratio is not decreasing")
            require(log_small < previous_small, "small-power ratio is not decreasing")
        previous_sharp = log_sharp
        previous_formal = log_formal
        previous_small = log_small
        rows.append((nlog, log_sharp, log_formal, log_small))

    require(rows[-1][1] < -100, "sharp all-high diagnostic is not strongly subcritical")
    require(rows[-1][2] < -100, "formal all-high diagnostic is not strongly subcritical")
    require(rows[-1][3] < -100, "small-power diagnostic is not strongly subcritical")
    return rows


def main() -> None:
    rounding_cases = check_rounding_lemma()
    binomial_cases = check_balanced_binomial_penalty()
    matching_instances, even_sets = check_matching_restriction()
    budget_cases = check_two_thirds_budget()
    local_ratio_cases = check_local_high_deficit_ratio()
    falling_ratio_cases = check_global_falling_ratio()
    decoration_product_cases = check_global_decoration_product()
    geometric_cases = check_geometric_decoration_sum()
    coefficients = coefficient_ledger()
    diagnostics = asymptotic_diagnostics()

    print("ERDOS 625 FULL PROOF AUDIT REGRESSION: PASS")
    print(f"  midpoint rounding cases: {rounding_cases}")
    print(f"  balanced central-binomial cases: {binomial_cases}")
    print(f"  matching-restriction instances: {matching_instances}")
    print(f"  even edge sets inspected: {even_sets}")
    print(f"  two-thirds exponent cases: {budget_cases}")
    print(f"  exact local high-deficit ratios: {local_ratio_cases}")
    print(f"  global falling-factorial ratios: {falling_ratio_cases}")
    print(f"  global decoration product cases: {decoration_product_cases}")
    print(f"  geometric decoration sums: {geometric_cases}")
    print("  coefficient ledger:")
    for name, value in coefficients.items():
        print(f"    {name}: {value}")
    print("  asymptotic diagnostic log-ratios (N, sharp all-high, formal all-high, small-power):")
    for nlog, sharp, formal, small_power in diagnostics:
        print(f"    {nlog}: {sharp}, {formal}, {small_power}")
    print("  scope: exact finite arithmetic/regression; the global Section 8 equivalence remains a Lean obligation")


if __name__ == "__main__":
    main()
