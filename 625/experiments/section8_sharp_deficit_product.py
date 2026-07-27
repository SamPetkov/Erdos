#!/usr/bin/env python3
"""Exact regression checks for the sharp Section VIII deficit product.

The script is standard-library only. It verifies finite arithmetic and product
identities used by the concise all-deficit route. It does not prove the phase
asymptotics, the attained-demand reindexing, or the random-graph theorem.
"""

from __future__ import annotations

from decimal import Decimal, getcontext
from fractions import Fraction
from itertools import product
from math import comb, factorial


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def falling(n: int, k: int) -> int:
    require(0 <= k <= n, f"invalid falling factorial ({n})_{{{k}}}")
    value = 1
    for offset in range(k):
        value *= n - offset
    return value


def local_ratio(m: int, d: int, h: int) -> Fraction:
    """The aggregate local ratio R_{m,d}(h)."""

    rising = factorial(d + h) // factorial(d)
    binary_exponent = h * m - h * (h + 1) // 2
    return Fraction(comb(m, h), rising * 2**binary_exponent)


def check_exact_local_ratio(max_m: int = 100) -> int:
    checked = 0
    for m in range(3, max_m + 1):
        for d in range(4):
            for h in range((m - 1) // 2 + 1):
                j = m - h
                decorated = Fraction(
                    falling(m, j) * falling(m + d, j), factorial(j)
                ) * Fraction(2 ** comb(j, 2), 2)
                full = Fraction(
                    falling(m, m) * falling(m + d, m), factorial(m)
                ) * Fraction(2 ** comb(m, 2), 2)
                require(
                    decorated / full == local_ratio(m, d, h),
                    f"local ratio failed at m={m}, d={d}, h={h}",
                )
                checked += 1
    return checked


def check_two_thirds_charge(max_m: int = 220) -> int:
    """Verify n^h R <= (n m / 2^floor(2m/3))^h exactly."""

    checked = 0
    sample_n = (1, 2, 3, 5, 10, 20, 50, 100)
    for m in range(3, max_m + 1):
        exponent = (2 * m) // 3
        for d in range(4):
            for h in range(1, (m - 1) // 2 + 1):
                require(2 * h < m, "loop admitted a non-high deficit")
                exponent_budget = h * m - h * (h + 1) // 2
                require(
                    h * exponent <= exponent_budget,
                    f"two-thirds exponent budget failed at m={m}, h={h}",
                )
                ratio = local_ratio(m, d, h)
                for n in sample_n:
                    lhs = n**h * ratio
                    rho = Fraction(n * m, 2**exponent)
                    require(
                        lhs <= rho**h,
                        f"two-thirds charge failed at n={n}, m={m}, d={d}, h={h}",
                    )
                    checked += 1
    return checked


def check_three_quarter_charge(max_m: int = 280) -> int:
    """Verify the stronger floor((3m-1)/4) charged ratio exactly."""

    checked = 0
    sample_n = (1, 2, 3, 5, 10, 20, 50, 100)
    for m in range(3, max_m + 1):
        two_thirds = (2 * m) // 3
        three_quarters = (3 * m - 1) // 4
        require(
            two_thirds <= three_quarters,
            f"three-quarter exponent is weaker at m={m}",
        )
        for d in range(4):
            for h in range(1, (m - 1) // 2 + 1):
                require(2 * h < m, "loop admitted a non-high deficit")
                exponent_budget = h * m - h * (h + 1) // 2
                require(
                    h * three_quarters <= exponent_budget,
                    f"three-quarter exponent budget failed at m={m}, h={h}",
                )
                ratio = local_ratio(m, d, h)
                for n in sample_n:
                    lhs = n**h * ratio
                    rho = Fraction(n * m, 2**three_quarters)
                    require(
                        lhs <= rho**h,
                        f"three-quarter charge failed at n={n}, m={m}, d={d}, h={h}",
                    )
                    checked += 1
    return checked


def check_finite_geometric_bound() -> int:
    """Check sum_{h=1}^H rho^h <= rho/(1-rho) <= 2 rho."""

    checked = 0
    for denominator in range(2, 81):
        for numerator in range(1, denominator // 2 + 1):
            rho = Fraction(numerator, denominator)
            require(rho <= Fraction(1, 2), "test construction exceeded one half")
            power = Fraction(1, 1)
            finite_sum = Fraction(0, 1)
            for cutoff in range(0, 81):
                if cutoff > 0:
                    power *= rho
                    finite_sum += power
                require(
                    finite_sum <= rho / (1 - rho),
                    f"geometric majorant failed at rho={rho}, H={cutoff}",
                )
                require(
                    finite_sum <= 2 * rho,
                    f"two-rho majorant failed at rho={rho}, H={cutoff}",
                )
                checked += 1
    return checked


def check_head_tail_bound(max_m: int = 100) -> int:
    """Check the optional first-term plus geometric-tail refinement."""

    checked = 0
    for m in range(3, max_m + 1):
        exponent = (3 * m - 1) // 4
        largest = (m - 1) // 2
        for d in range(4):
            ratios = tuple(local_ratio(m, d, h) for h in range(largest + 1))
            for n in range(1, 21):
                rho = Fraction(n * m, 2**exponent)
                if rho > Fraction(1, 2):
                    continue
                actual = sum(
                    (n**h * ratios[h] for h in range(1, largest + 1)),
                    Fraction(0, 1),
                )
                first = n * ratios[1]
                tail = rho**2 / (1 - rho)
                require(
                    actual <= first + tail,
                    f"head-tail bound failed at n={n}, m={m}, d={d}",
                )
                checked += 1
    return checked


def check_partition_function_factorization() -> int:
    """Exhaust exact sums over small distinguishable deficit fibres."""

    local_fibres = (
        (Fraction(1), Fraction(1, 7), Fraction(1, 49)),
        (Fraction(1), Fraction(2, 9)),
        (Fraction(1), Fraction(1, 11), Fraction(1, 121), Fraction(1, 1331)),
        (Fraction(1),),
    )
    checked = 0
    for number_of_cells in range(0, len(local_fibres) + 1):
        fibres = local_fibres[:number_of_cells]
        direct = Fraction(0, 1)
        for choice in product(*fibres):
            term = Fraction(1, 1)
            for value in choice:
                term *= value
            direct += term
        factorized = Fraction(1, 1)
        for fibre in fibres:
            factorized *= sum(fibre, Fraction(0, 1))
        require(
            direct == factorized,
            f"partition-function factorization failed for {number_of_cells} cells",
        )
        checked += 1
    return checked


def check_cellwise_and_uniform_bounds() -> int:
    """Compare cellwise 2 rho charges with the older U rho interface."""

    checked = 0
    for U in range(2, 81):
        for denominator in range(2, 61):
            for numerator in range(1, denominator // 2 + 1):
                rho = Fraction(numerator, denominator)
                require(2 * rho <= U * rho, "sharp charge exceeded old charge")
                require(
                    1 + 2 * rho <= 1 + U * rho,
                    "additive charge comparison failed",
                )
                checked += 1
    return checked


def check_endpoint_type_retention() -> int:
    """Retaining cellwise charges is sharper than replacing them by max rho."""

    checked = 0
    for alpha in range(12, 61):
        endpoint_sizes = tuple(alpha - d for d in (2, 3, 4, 5))
        for n in (1, 2, 5, 10, 20):
            charges = [
                Fraction(
                    n * min(s, t),
                    2 ** ((3 * min(s, t) - 1) // 4),
                )
                for s in endpoint_sizes
                for t in endpoint_sizes
            ]
            require(
                sum(charges, Fraction(0, 1)) <= len(charges) * max(charges),
                "cellwise-to-uniform maximum comparison failed",
            )
            checked += 1
    return checked


def asymptotic_diagnostics() -> list[
    tuple[int, Decimal, Decimal, Decimal, Decimal]
]:
    """Logarithms of error-scale ratios after division by n/N^4.

    With N=log n:

      three-quarter: sqrt(n) N^(3/2) -> exp(-N/2) N^(11/2),
      two-thirds:    n^(2/3) N^(4/3) -> exp(-N/3) N^(16/3),
      old U*rho:     n^(2/3) N^(7/3) -> exp(-N/3) N^(19/3),
      endpoint:      sqrt(nN)         -> exp(-N/2) N^(9/2).
    """

    getcontext().prec = 80
    rows: list[tuple[int, Decimal, Decimal, Decimal, Decimal]] = []
    previous: tuple[Decimal, Decimal, Decimal, Decimal] | None = None
    for nlog in (120, 240, 480, 960, 1920):
        N = Decimal(nlog)
        three_quarter = -N / 2 + (Decimal(11) / 2) * N.ln()
        two_thirds = -N / 3 + (Decimal(16) / 3) * N.ln()
        old = -N / 3 + (Decimal(19) / 3) * N.ln()
        endpoint = -N / 2 + (Decimal(9) / 2) * N.ln()
        current = (three_quarter, two_thirds, old, endpoint)
        if previous is not None:
            labels = ("three-quarter", "two-thirds", "old", "endpoint")
            for label, value, old_value in zip(labels, current, previous):
                require(value < old_value, f"{label} scale diagnostic is not decreasing")
        previous = current
        rows.append((nlog, *current))
    for index, label in enumerate(
        ("three-quarter", "two-thirds", "old", "endpoint"), start=1
    ):
        require(rows[-1][index] < -100, f"{label} scale is not strongly subcritical")
    return rows


def main() -> None:
    local_cases = check_exact_local_ratio()
    two_thirds_cases = check_two_thirds_charge()
    three_quarter_cases = check_three_quarter_charge()
    geometric_cases = check_finite_geometric_bound()
    head_tail_cases = check_head_tail_bound()
    factorization_cases = check_partition_function_factorization()
    comparison_cases = check_cellwise_and_uniform_bounds()
    endpoint_cases = check_endpoint_type_retention()
    diagnostics = asymptotic_diagnostics()

    print("ERDOS 625 SHARP DEFICIT PRODUCT: PASS")
    print(f"  exact aggregate local ratios: {local_cases}")
    print(f"  exact two-thirds charged ratios: {two_thirds_cases}")
    print(f"  exact three-quarter charged ratios: {three_quarter_cases}")
    print(f"  finite geometric sums: {geometric_cases}")
    print(f"  first-term plus tail checks: {head_tail_cases}")
    print(f"  exact partition-function factorizations: {factorization_cases}")
    print(f"  sharp-vs-cardinality comparisons: {comparison_cases}")
    print(f"  cellwise endpoint-type comparisons: {endpoint_cases}")
    print(
        "  asymptotic log-ratios "
        "(N, three-quarter, two-thirds, old-cardinality, endpoint):"
    )
    for row in diagnostics:
        print("   ", row)
    print("  scope: exact finite arithmetic and scale diagnostics only")


if __name__ == "__main__":
    main()
