#!/usr/bin/env python3
"""Exact regression for the simplified Section VIII half-deficit assembly.

The checker verifies finite set inclusions, decoding, injectivity on small
support/deficit data, the optional-choice product identity, and the stronger
three-quarter geometric charge.  It is standard-library only and is not a
proof of the random-graph asymptotics.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import comb


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def exact_high_cut(a: int, m: int) -> int:
    return m - (a // 2 + 1)


def exact_high_deficits(a: int, m: int) -> list[int]:
    cut = max(-1, exact_high_cut(a, m))
    return [h for h in range(0, m + 1) if h <= cut]


def half_envelope(m: int) -> list[int]:
    return [h for h in range(0, m + 1) if 2 * h < m]


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
    charges = check_three_quarter_charge()
    strict = check_enlargement_is_strict()

    print("ERDOS 625 DIRECT HALF-DEFICIT ASSEMBLY: PASS")
    print(f"  exact-window inclusions: {inclusion}")
    print(f"  decoded deficit values: {decoding}")
    print(f"  optional product instances: {products}")
    print(f"  three-quarter charged terms: {charges}")
    print(f"  strict harmless enlargements: {strict}")
    print("  scope: exact finite regression; not the endpoint asymptotic theorem")


if __name__ == "__main__":
    main()
