#!/usr/bin/env python3
"""Exact regression for the simplified Section VIII half-deficit assembly.

The checker verifies finite set inclusions, decoding, injectivity, the optional
choice-product identity, the exact one-cell partial/full ratio, the single
global falling-factorial loss, and the stronger three-quarter geometric charge.
It is standard-library only and is not a proof of the random-graph asymptotics.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import comb, factorial


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def falling(n: int, r: int) -> int:
    require(0 <= r <= n, f"invalid falling factorial ({n})_{r}")
    value = 1
    for t in range(r):
        value *= n - t
    return value


def exact_high_cut(a: int, m: int) -> int:
    return m - (a // 2 + 1)


def exact_high_deficits(a: int, m: int) -> list[int]:
    cut = max(-1, exact_high_cut(a, m))
    return [h for h in range(0, m + 1) if h <= cut]


def half_envelope(m: int) -> list[int]:
    return [h for h in range(0, m + 1) if 2 * h < m]


def sign_reward(x: int) -> int:
    return 2 ** (comb(x, 2) - 1) if x >= 3 else 1


def local_matching_count(m: int, d: int, multiplicity: int) -> int:
    """Number of partial matchings in an m by (m+d) endpoint cell."""
    require(0 <= multiplicity <= m, "infeasible local multiplicity")
    return (
        falling(m, multiplicity)
        * falling(m + d, multiplicity)
        // factorial(multiplicity)
    )


def local_aggregate_factor(m: int, d: int, multiplicity: int) -> int:
    return local_matching_count(m, d, multiplicity) * sign_reward(multiplicity)


def local_ratio(m: int, d: int, h: int) -> Fraction:
    denominator = 1
    for t in range(1, h + 1):
        denominator *= d + t
    exponent = h * m - h * (h + 1) // 2
    return Fraction(comb(m, h), denominator * 2**exponent)


def charged_term(n: int, m: int, d: int, h: int) -> Fraction:
    return n**h * local_ratio(m, d, h)


def check_envelope_inclusion() -> int:
    checked = 0
    for a in range(9, 81):
        for m in range(a // 2 + 1, a + 1):
            exact = set(exact_high_deficits(a, m))
            half = set(half_envelope(m))
            require(exact <= half, f"high window not contained: a={a}, m={m}")
            checked += 1
    return checked


def check_decode_and_injectivity() -> int:
    checked = 0
    for m in range(2, 20):
        deficits = half_envelope(m)
        decoded = {h: m - h for h in deficits}
        require(len(set(decoded.values())) == len(decoded), f"decode not injective at m={m}")
        require(decoded[0] == m, f"zero deficit is not full containment at m={m}")
        checked += len(deficits)
    return checked


def check_product_identity() -> int:
    checked = 0
    for cell_data in (
        ((7, 0),),
        ((7, 0), (8, 1)),
        ((7, 0), (8, 1), (9, 2)),
    ):
        local_weights: list[dict[int, Fraction]] = []
        for m, d in cell_data:
            weights = {h: local_ratio(m, d, h) for h in half_envelope(m) if h > 0}
            local_weights.append(weights)
        lhs = Fraction(0)
        choices = [[None, *weights.keys()] for weights in local_weights]
        for choice in product(*choices):
            term = Fraction(1)
            for index, h in enumerate(choice):
                if h is not None:
                    term *= local_weights[index][h]
            lhs += term
        rhs = Fraction(1)
        for weights in local_weights:
            rhs *= 1 + sum(weights.values(), Fraction(0))
        require(lhs == rhs, f"optional product identity failed for {cell_data}")
        checked += 1
    return checked


def check_exact_local_ratio() -> int:
    """Check the exact local identity underlying manuscript equation (8.21)."""
    checked = 0
    for m in range(4, 41):
        for d in range(4):
            full = local_aggregate_factor(m, d, m)
            for h in half_envelope(m):
                partial = local_aggregate_factor(m, d, m - h)
                require(
                    Fraction(partial, full) == local_ratio(m, d, h),
                    f"local ratio failed: m={m}, d={d}, h={h}",
                )
                checked += 1
    return checked


def check_global_charged_comparison() -> int:
    """Verify the complete pointwise comparison on small finite supports.

    The exact ratio is the product of the one-cell ratios times the single
    ambient falling-factorial ratio.  Replacing that global ratio by n^H gives
    precisely the product of the charged local terms.
    """
    checked = 0
    support_families = (
        ((7, 0),),
        ((7, 0), (8, 1)),
        ((7, 0), (8, 1), (9, 2)),
        ((7, 3), (8, 2), (9, 1), (10, 0)),
    )
    for cells in support_families:
        full_total = sum(m for m, _d in cells)
        n = max(80, full_total + 10)
        full_numerator = 1
        for m, d in cells:
            full_numerator *= local_aggregate_factor(m, d, m)
        full_weight = Fraction(full_numerator, falling(n, full_total))

        deficit_choices = [half_envelope(m) for m, _d in cells]
        for deficits in product(*deficit_choices):
            partial_total = sum(m - h for (m, _d), h in zip(cells, deficits))
            total_deficit = sum(deficits)
            partial_numerator = 1
            exact_local_product = Fraction(1)
            charged_product = Fraction(1)
            for (m, d), h in zip(cells, deficits):
                partial_numerator *= local_aggregate_factor(m, d, m - h)
                exact_local_product *= local_ratio(m, d, h)
                charged_product *= charged_term(n, m, d, h)

            partial_weight = Fraction(partial_numerator, falling(n, partial_total))
            ambient_ratio = Fraction(falling(n, full_total), falling(n, partial_total))
            require(
                partial_weight == full_weight * exact_local_product * ambient_ratio,
                f"exact aggregate ratio failed: cells={cells}, deficits={deficits}",
            )
            require(
                ambient_ratio <= n**total_deficit,
                f"global denominator loss failed: cells={cells}, deficits={deficits}",
            )
            require(
                partial_weight <= full_weight * charged_product,
                f"charged pointwise comparison failed: cells={cells}, deficits={deficits}",
            )
            checked += 1
    return checked


def check_three_quarter_charge() -> int:
    checked = 0
    for n in (10, 100, 1000):
        for m in range(3, 80):
            base = Fraction(n * m, 2 ** ((3 * m - 1) // 4))
            for d in range(4):
                for h in half_envelope(m):
                    if h == 0:
                        continue
                    require(
                        charged_term(n, m, d, h) <= base**h,
                        f"three-quarter charge failed: n={n}, m={m}, d={d}, h={h}",
                    )
                    checked += 1
    return checked


def check_enlargement_is_strict() -> int:
    strict = 0
    for a in range(9, 60):
        for m in range(a // 2 + 1, a):
            if set(exact_high_deficits(a, m)) < set(half_envelope(m)):
                strict += 1
    require(strict > 0, "the half-deficit envelope never strictly enlarges the exact window")
    return strict


def main() -> None:
    inclusion = check_envelope_inclusion()
    decoding = check_decode_and_injectivity()
    products = check_product_identity()
    local_ratios = check_exact_local_ratio()
    global_ratios = check_global_charged_comparison()
    charges = check_three_quarter_charge()
    strict = check_enlargement_is_strict()

    print("ERDOS 625 DIRECT HALF-DEFICIT ASSEMBLY: PASS")
    print(f"  exact-window inclusions: {inclusion}")
    print(f"  decoded deficit values: {decoding}")
    print(f"  optional product instances: {products}")
    print(f"  exact one-cell ratios: {local_ratios}")
    print(f"  exact aggregate charged comparisons: {global_ratios}")
    print(f"  three-quarter charged terms: {charges}")
    print(f"  strict harmless enlargements: {strict}")
    print("  scope: exact finite regression; not the endpoint asymptotic theorem")


if __name__ == "__main__":
    main()
