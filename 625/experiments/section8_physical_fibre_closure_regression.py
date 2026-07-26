#!/usr/bin/env python3
"""Exact finite regression for the Section VIII physical-fibre closure.

The script checks the arithmetic identities used after the finite reindexing:
local partial-matching cardinalities, aggregate deficit ratios, the single
global falling-factorial loss, and the all-high geometric budget.  It does not
prove the Lean equivalence or the random-graph asymptotics.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import comb, factorial


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def falling(n: int, k: int) -> int:
    require(0 <= k <= n, f"invalid falling factorial ({n})_{k}")
    value = 1
    for offset in range(k):
        value *= n - offset
    return value


def local_reward(j: int) -> int:
    if j <= 2:
        return 1
    return 2 ** (comb(j, 2) - 1)


def local_matching_count(u: int, v: int, j: int) -> int:
    """Number of unlabelled size-j partial matchings in one u-by-v cell."""

    return comb(u, j) * comb(v, j) * factorial(j)


def local_aggregate_weight(u: int, v: int, j: int) -> Fraction:
    return Fraction(falling(u, j) * falling(v, j), factorial(j)) * local_reward(j)


def deficit_ratio_formula(m: int, d: int, h: int) -> Fraction:
    denominator = 1
    for t in range(1, h + 1):
        denominator *= d + t
    exponent = h * m - h * (h + 1) // 2
    return Fraction(comb(m, h), denominator * 2**exponent)


def check_single_cell_cardinality(max_u: int = 40) -> int:
    checked = 0
    for u in range(max_u + 1):
        for v in range(max_u + 1):
            for j in range(min(u, v) + 1):
                count = local_matching_count(u, v, j)
                require(
                    count * factorial(j) == falling(u, j) * falling(v, j),
                    f"single-cell cardinality failed: u={u}, v={v}, j={j}",
                )
                checked += 1
    return checked


def check_product_fibre_cardinality() -> int:
    """Check products of independent selected-cell fibres."""

    cells = [(5, 7, 4), (6, 6, 5), (8, 9, 6), (7, 10, 3)]
    checked = 0
    for length in range(5):
        for chosen in product(cells, repeat=length):
            card = 1
            factorial_product = 1
            selection_product = 1
            for u, v, j in chosen:
                card *= local_matching_count(u, v, j)
                factorial_product *= factorial(j)
                selection_product *= falling(u, j) * falling(v, j)
            require(
                card * factorial_product == selection_product,
                f"product fibre identity failed: {chosen}",
            )
            checked += 1
    return checked


def check_exact_local_deficit_ratio(max_m: int = 100) -> int:
    checked = 0
    for m in range(5, max_m + 1):
        for d in range(4):
            for h in range(m):
                if 2 * h >= m:
                    continue
                j = m - h
                require(j >= 3, "high multiplicity left the signed-reward range")
                actual = local_aggregate_weight(m, m + d, j) / local_aggregate_weight(
                    m, m + d, m
                )
                expected = deficit_ratio_formula(m, d, h)
                require(
                    actual == expected,
                    f"local deficit ratio failed: m={m}, d={d}, h={h}",
                )
                checked += 1
    return checked


def check_global_denominator(max_n: int = 150) -> int:
    checked = 0
    for n in range(max_n + 1):
        for j in range(n + 1):
            for h in range(n - j + 1):
                ratio = Fraction(falling(n, j + h), falling(n, j))
                require(
                    ratio == falling(n - j, h),
                    f"global denominator identity failed: n={n}, J={j}, H={h}",
                )
                require(
                    ratio <= n**h,
                    f"global denominator bound failed: n={n}, J={j}, H={h}",
                )
                checked += 1
    return checked


def check_multi_cell_aggregate_comparison() -> int:
    """Exhaust small matching supports and verify the charged product bound."""

    options = [
        (m, d, h)
        for m in range(5, 11)
        for d in range(4)
        for h in range(m)
        if 2 * h < m
    ]
    checked = 0
    for cell_count in range(1, 4):
        for cells in product(options, repeat=cell_count):
            full_total = sum(m for m, _d, _h in cells)
            actual_total = sum(m - h for m, _d, h in cells)
            total_deficit = full_total - actual_total
            n = full_total + 7

            local_ratio = Fraction(1, 1)
            charged_product = Fraction(1, 1)
            for m, d, h in cells:
                ratio = deficit_ratio_formula(m, d, h)
                local_ratio *= ratio
                charged_product *= n**h * ratio

            denominator_ratio = Fraction(
                falling(n, full_total), falling(n, actual_total)
            )
            exact_global_ratio = denominator_ratio * local_ratio
            require(
                denominator_ratio == falling(n - actual_total, total_deficit),
                f"multi-cell denominator factorization failed: {cells}",
            )
            require(
                exact_global_ratio <= charged_product,
                f"multi-cell charged comparison failed: {cells}",
            )
            checked += 1
    return checked


def check_two_thirds_budget(max_m: int = 2000) -> int:
    checked = 0
    for m in range(1, max_m + 1):
        for h in range(1, m + 1):
            if 2 * h >= m:
                continue
            lhs = h * ((2 * m) // 3)
            rhs = h * m - h * (h + 1) // 2
            require(lhs <= rhs, f"two-thirds budget failed: m={m}, h={h}")
            checked += 1
    return checked


def check_geometric_fibre() -> int:
    checked = 0
    for denominator in range(2, 101):
        for numerator in range(1, denominator // 2 + 1):
            rho = Fraction(numerator, denominator)
            for cutoff in range(1, 80):
                finite_sum = sum((rho**h for h in range(1, cutoff + 1)), Fraction())
                require(finite_sum <= rho / (1 - rho), "geometric majorant failed")
                require(finite_sum <= 2 * rho, "two-rho majorant failed")
                checked += 1
    return checked


def main() -> None:
    single = check_single_cell_cardinality()
    products = check_product_fibre_cardinality()
    local_ratios = check_exact_local_deficit_ratio()
    denominators = check_global_denominator()
    aggregate = check_multi_cell_aggregate_comparison()
    budgets = check_two_thirds_budget()
    geometric = check_geometric_fibre()

    print("ERDOS 625 SECTION 8 PHYSICAL-FIBRE CLOSURE REGRESSION: PASS")
    print(f"  single-cell cardinalities: {single}")
    print(f"  product-fibre cardinalities: {products}")
    print(f"  exact local deficit ratios: {local_ratios}")
    print(f"  global denominator cases: {denominators}")
    print(f"  multi-cell aggregate comparisons: {aggregate}")
    print(f"  two-thirds exponent cases: {budgets}")
    print(f"  geometric-fibre cases: {geometric}")
    print("  scope: exact finite arithmetic; the Lean global reindexing remains separate")


if __name__ == "__main__":
    main()
