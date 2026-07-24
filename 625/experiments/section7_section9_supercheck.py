#!/usr/bin/env python3
"""Exact super-checks for two proposed Erdős 625 simplifications.

All assertions use integer or Fraction arithmetic.  The script checks:
  * the Section 7 central-rate endpoint inequalities with rigorous rational
    intervals for logarithms;
  * exhaustive restriction injectivity for even subgraphs on small complete
    bipartite graphs;
  * the weighted subset-product inequality for several rational weight systems;
  * the off-matching square-sum inequality used in the Section 9 envelope.

These finite checks are regression tests, not a proof of the asymptotic theorem.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations, product
from typing import Iterable, Iterator


def require(condition: bool, message: str) -> None:
    """Raise even under ``python -O`` when a verification condition fails."""
    if not condition:
        raise RuntimeError(message)


def log_bounds(r: Fraction, terms: int = 120) -> tuple[Fraction, Fraction]:
    """Rigorous bounds for log(r) via 2*atanh((r-1)/(r+1))."""
    if r <= 0:
        raise ValueError("log requires r > 0")
    if r == 1:
        return Fraction(0), Fraction(0)
    if r < 1:
        lo, hi = log_bounds(1 / r, terms)
        return -hi, -lo
    x = (r - 1) / (r + 1)
    partial = sum(
        Fraction(2) * x ** (2 * k + 1) / (2 * k + 1)
        for k in range(terms)
    )
    # 1/(2k+1) <= 1/(2*terms+1) for k >= terms.
    tail = (
        Fraction(2, 2 * terms + 1)
        * x ** (2 * terms + 1)
        / (1 - x * x)
    )
    return partial, partial + tail


def central_rate_certificate() -> None:
    """Prove the three endpoint signs used for Phi_T <= -(1-R)/100."""
    q_lo, q_hi = log_bounds(Fraction(2), terms=32)
    c = Fraction(1, 100)

    # R=1/64 and log R = -6 log 2 exactly.
    r0 = Fraction(1, 64)
    f0_upper = r0 * (-Fraction(7, 2) * q_lo - 1) + c * (1 - r0)
    require(f0_upper < 0, "central-rate endpoint R=1/64 failed")

    r1 = Fraction(47, 100)
    _, log_r1_hi = log_bounds(r1)
    f1_upper = r1 * log_r1_hi + (Fraction(5, 2) * q_hi - 1) * r1 + c * (1 - r1)
    h1_upper = r1 * log_r1_hi + (1 - q_lo / 2 + c) * (1 - r1)
    require(f1_upper < 0, "central-rate first bound at R=47/100 failed")
    require(h1_upper < 0, "central-rate second bound at R=47/100 failed")


def all_partial_matchings(nr: int, nc: int) -> Iterator[frozenset[tuple[int, int]]]:
    edges = tuple((i, j) for i in range(nr) for j in range(nc))
    for size in range(min(nr, nc) + 1):
        for chosen in combinations(edges, size):
            rows = {i for i, _ in chosen}
            cols = {j for _, j in chosen}
            if len(rows) == size and len(cols) == size:
                yield frozenset(chosen)


def is_even(edges: Iterable[tuple[int, int]], nr: int, nc: int) -> bool:
    row = [0] * nr
    col = [0] * nc
    for i, j in edges:
        row[i] ^= 1
        col[j] ^= 1
    return not any(row) and not any(col)


def subsets(items: tuple[tuple[int, int], ...]) -> Iterator[frozenset[tuple[int, int]]]:
    for mask in range(1 << len(items)):
        yield frozenset(items[k] for k in range(len(items)) if (mask >> k) & 1)


def residual_restriction_exhaustive() -> tuple[int, int]:
    """Exhaust all M,R,F for K_2,2, K_2,3 and K_3,3."""
    relation_cases = 0
    even_sets_checked = 0
    weight_patterns = (
        (Fraction(1, 7), Fraction(2, 5), Fraction(3, 4), Fraction(5, 3)),
        (Fraction(0), Fraction(1, 3), Fraction(7, 5), Fraction(11, 2)),
    )
    for nr, nc in ((2, 2), (2, 3), (3, 3)):
        all_edges = frozenset((i, j) for i in range(nr) for j in range(nc))
        for matching in all_partial_matchings(nr, nc):
            remaining = tuple(sorted(all_edges - matching))
            for residual in subsets(remaining):
                relation_cases += 1
                universe = tuple(sorted(matching | residual))
                images: dict[frozenset[tuple[int, int]], frozenset[tuple[int, int]]] = {}
                even_family: list[frozenset[tuple[int, int]]] = []
                for edge_set in subsets(universe):
                    if not is_even(edge_set, nr, nc):
                        continue
                    even_sets_checked += 1
                    image = edge_set - matching
                    require(image not in images, "even completion restriction was not injective")
                    images[image] = edge_set
                    even_family.append(edge_set)

                for pattern in weight_patterns:
                    weights = {
                        edge: pattern[k % len(pattern)]
                        for k, edge in enumerate(sorted(residual))
                    }
                    lhs = sum(
                        (
                            _product(weights[e] for e in edge_set - matching)
                            for edge_set in even_family
                        ),
                        Fraction(0),
                    )
                    rhs = _product(1 + weights[e] for e in residual)
                    require(lhs <= rhs, "weighted restriction product bound failed")
    return relation_cases, even_sets_checked


def _product(values: Iterable[Fraction]) -> Fraction:
    out = Fraction(1)
    for value in values:
        out *= value
    return out


def square_sum_exhaustive() -> int:
    """Check off-matching <= unrestricted factorized square sum."""
    checked = 0
    for nr, nc in ((2, 2), (2, 3), (3, 2), (3, 3)):
        matchings = tuple(all_partial_matchings(nr, nc))
        for cap in range(1, 7):
            for row_deg in product(range(cap + 1), repeat=nr):
                total = sum(row_deg)
                if total == 0:
                    continue
                for col_deg in product(range(cap + 1), repeat=nc):
                    if sum(col_deg) != total:
                        continue
                    row_sq = sum(d * d for d in row_deg)
                    col_sq = sum(d * d for d in col_deg)
                    full = row_sq * col_sq
                    require(row_sq <= cap * total, "row square-sum cap failed")
                    require(col_sq <= cap * total, "column square-sum cap failed")
                    require(full <= cap * cap * total * total, "factorized square-sum cap failed")
                    for matching in matchings:
                        off = sum(
                            row_deg[i] ** 2 * col_deg[j] ** 2
                            for i in range(nr)
                            for j in range(nc)
                            if (i, j) not in matching
                        )
                        require(off <= full, "off-matching square sum exceeded full sum")
                        checked += 1
    return checked


def main() -> None:
    central_rate_certificate()
    relations, even_sets = residual_restriction_exhaustive()
    squares = square_sum_exhaustive()
    print("ERDOS 625 SECTION 7/9 SUPERCHECK: PASS")
    print("  central-rate endpoint inequalities: exact Fraction bounds")
    print(f"  residual relations exhausted: {relations}")
    print(f"  even edge sets checked: {even_sets}")
    print(f"  square-sum instances checked: {squares}")


if __name__ == "__main__":
    main()
