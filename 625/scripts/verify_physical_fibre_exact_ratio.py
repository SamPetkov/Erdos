#!/usr/bin/env python3
"""Exact finite audit of the Erdős 625 physical-fibre weight identities.

This script checks the local partial-matching cardinality, the exact weighted
deficit ratio, the one-global-denominator identity, and the finite geometric
majorant used in the corrected Section VIII route.  It does not claim the
remaining global reindexing of every attained canonical high skeleton.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, factorial, floor
import json


def falling(value: int, length: int) -> int:
    if value < 0 or length < 0 or length > value:
        raise ValueError("invalid falling factorial")
    result = 1
    for offset in range(length):
        result *= value - offset
    return result


def rising(value: int, length: int) -> int:
    if value <= 0 or length < 0:
        raise ValueError("invalid rising factorial")
    result = 1
    for offset in range(length):
        result *= value + offset
    return result


def power_two(exponent: int) -> Fraction:
    if exponent >= 0:
        return Fraction(2**exponent, 1)
    return Fraction(1, 2 ** (-exponent))


def cell_factor(size: int) -> Fraction:
    """The exact signed-overlap cell factor g(size)=2^(C(size,2)-1)."""
    if size < 0:
        raise ValueError("negative cell size")
    return power_two(size * (size - 1) // 2 - 1)


def partial_matching_count(left_size: int, right_size: int, size: int) -> int:
    if size < 0 or size > min(left_size, right_size):
        return 0
    return (
        falling(left_size, size)
        * falling(right_size, size)
        // factorial(size)
    )


def brute_partial_matching_count(left_size: int, right_size: int, size: int) -> int:
    """Enumerate literal partial bijections between two labelled blocks."""
    if size < 0 or size > min(left_size, right_size):
        return 0
    count = 0
    for left_subset in combinations(range(left_size), size):
        for right_subset in combinations(range(right_size), size):
            for right_order in permutations(right_subset):
                # Pair the sorted left subset with an ordered right subset.
                tuple(zip(left_subset, right_order))
                count += 1
    return count


def weighted_local_fibre(left_size: int, right_size: int, size: int) -> Fraction:
    return Fraction(
        partial_matching_count(left_size, right_size, size), 1
    ) * cell_factor(size)


def local_deficit_ratio(m: int, d: int, h: int) -> Fraction:
    if m < 0 or d < 0 or h < 0 or h > m:
        raise ValueError("invalid deficit parameters")
    denominator = rising(d + 1, h) if h else 1
    exponent = -h * m + h * (h + 1) // 2
    return Fraction(comb(m, h), denominator) * power_two(exponent)


def support_weight(
    n: int,
    endpoint_sizes: tuple[tuple[int, int], ...],
    multiplicities: tuple[int, ...],
) -> Fraction:
    if len(endpoint_sizes) != len(multiplicities):
        raise ValueError("support and multiplicity lengths differ")
    total = sum(multiplicities)
    if total > n:
        raise ValueError("global multiplicity exceeds n")
    numerator = Fraction(1, 1)
    for (left_size, right_size), size in zip(endpoint_sizes, multiplicities):
        numerator *= weighted_local_fibre(left_size, right_size, size)
    return numerator / falling(n, total)


def verify_brute_local_counts(max_block_size: int = 6) -> int:
    checks = 0
    for left_size in range(max_block_size + 1):
        for right_size in range(max_block_size + 1):
            for size in range(min(left_size, right_size) + 1):
                actual = brute_partial_matching_count(left_size, right_size, size)
                expected = partial_matching_count(left_size, right_size, size)
                if actual != expected:
                    raise AssertionError(
                        "partial matching count failed for "
                        f"{(left_size, right_size, size)}"
                    )
                checks += 1
    return checks


def verify_local_ratio(max_m: int = 24, max_d: int = 3) -> int:
    checks = 0
    for m in range(1, max_m + 1):
        for d in range(max_d + 1):
            full = weighted_local_fibre(m, m + d, m)
            for h in range(m + 1):
                partial = weighted_local_fibre(m, m + d, m - h)
                expected = local_deficit_ratio(m, d, h)
                if partial / full != expected:
                    raise AssertionError(
                        f"local weighted ratio failed for {(m, d, h)}"
                    )
                checks += 1
    return checks


def verify_global_ratio() -> dict[str, int]:
    """Check the exact one-global-denominator identity on support products."""
    support_families = (
        ((2, 2),),
        ((3, 4),),
        ((4, 6),),
        ((2, 3), (3, 3)),
        ((3, 5), (4, 4)),
        ((2, 4), (3, 5), (5, 6)),
    )
    checks = equality_cases = 0
    for endpoints in support_families:
        full_multiplicities = tuple(min(left, right) for left, right in endpoints)
        deficit_ranges = tuple(range(m + 1) for m in full_multiplicities)
        full_total = sum(full_multiplicities)
        for deficits in product(*deficit_ranges):
            partial_multiplicities = tuple(
                m - h for m, h in zip(full_multiplicities, deficits)
            )
            partial_total = sum(partial_multiplicities)
            total_deficit = sum(deficits)
            for slack in range(5):
                n = full_total + slack
                partial_weight = support_weight(
                    n, endpoints, partial_multiplicities
                )
                full_weight = support_weight(n, endpoints, full_multiplicities)
                exact_global = Fraction(
                    falling(n - partial_total, total_deficit), 1
                )
                exact_local = Fraction(1, 1)
                for (left, right), h in zip(endpoints, deficits):
                    m = min(left, right)
                    d = abs(left - right)
                    exact_local *= local_deficit_ratio(m, d, h)
                expected = exact_global * exact_local
                if partial_weight / full_weight != expected:
                    raise AssertionError(
                        "global ratio failed for "
                        f"{endpoints}, {deficits}, n={n}"
                    )

                upper = Fraction(n**total_deficit, 1) * exact_local
                if partial_weight / full_weight > upper:
                    raise AssertionError(
                        "global denominator bound has wrong direction"
                    )
                if exact_global == n**total_deficit:
                    equality_cases += 1
                checks += 1
    return {"checks": checks, "upper_bound_equality_cases": equality_cases}


def verify_high_deficit_geometric_bound(
    max_m: int = 120, max_d: int = 3
) -> int:
    checks = 0
    for m in range(2, max_m + 1):
        for d in range(max_d + 1):
            for h in range(1, m + 1):
                if 2 * h >= m:
                    continue
                exact = local_deficit_ratio(m, d, h)
                geometric = Fraction(m, 2 ** floor(2 * m / 3)) ** h
                if exact > geometric:
                    raise AssertionError(
                        f"geometric deficit bound failed for {(m, d, h)}"
                    )
                checks += 1
    return checks


def main() -> None:
    if not __debug__:
        raise RuntimeError("verification must not be run with python -O")

    result = {
        "brute_partial_matching_counts": verify_brute_local_counts(),
        "exact_local_weighted_ratios": verify_local_ratio(),
        "exact_global_ratio": verify_global_ratio(),
        "high_deficit_geometric_bounds": verify_high_deficit_geometric_bound(),
        "status_boundary": (
            "fixed-support physical-fibre identities checked; "
            "global attained-skeleton reindexing not claimed"
        ),
    }
    print("Erdos 625 physical-fibre exact-ratio audit: PASS")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
