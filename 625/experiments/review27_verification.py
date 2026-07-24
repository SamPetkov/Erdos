#!/usr/bin/env python3
"""Independent finite diagnostics for the Erdős 625 PR #27 review appendix.

This script uses only the Python standard library.  Exact combinatorial checks
use integers/Fraction.  Decimal checks are explicitly labelled diagnostics,
not substitutes for the displayed analytic proofs.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from decimal import Decimal, getcontext
from fractions import Fraction
from itertools import permutations, product
from math import factorial, floor
from typing import Iterator, Sequence


def falling(n: int, k: int) -> int:
    out = 1
    for x in range(k):
        out *= n - x
    return out


def enumerate_tables(rows: Sequence[int], cols: Sequence[int]) -> Iterator[tuple[tuple[int, ...], ...]]:
    """Enumerate nonnegative integer contingency tables with given margins."""
    r, c = len(rows), len(cols)
    table = [[0] * c for _ in range(r)]

    def fill(i: int, j: int, row_left: list[int], col_left: list[int]):
        if i == r:
            if all(x == 0 for x in col_left):
                yield tuple(tuple(row) for row in table)
            return
        if j == c:
            if row_left[i] == 0:
                yield from fill(i + 1, 0, row_left, col_left)
            return
        if i == r - 1 and j == c - 1:
            x = row_left[i]
            if x == col_left[j]:
                table[i][j] = x
                row_left[i] -= x
                col_left[j] -= x
                yield from fill(i, j + 1, row_left, col_left)
                row_left[i] += x
                col_left[j] += x
            return
        maximum = min(row_left[i], col_left[j])
        for x in range(maximum + 1):
            table[i][j] = x
            row_left[i] -= x
            col_left[j] -= x
            yield from fill(i, j + 1, row_left, col_left)
            row_left[i] += x
            col_left[j] += x

    yield from fill(0, 0, list(rows), list(cols))


def table_margins(table: Sequence[Sequence[int]]) -> tuple[list[int], list[int]]:
    rows = [sum(row) for row in table]
    cols = [sum(table[i][j] for i in range(len(table))) for j in range(len(table[0]))]
    return rows, cols


def canonical_high_checks() -> int:
    checked = 0
    # Regression: without degree caps the matching statement is false.
    U = 4
    bad = ((3, 3),)
    bad_high = [(0, j) for j, x in enumerate(bad[0]) if x > U // 2]
    assert len(bad_high) == 2

    # Exhaust bounded 2x2 tables and smaller 2x3/3x2 tables.
    for nr, nc, max_u in ((2, 2, 6), (2, 3, 4), (3, 2, 4)):
        for U in range(2, max_u + 1):
            cutoff = U // 2
            for rows in product(range(U + 1), repeat=nr):
                if sum(rows) == 0:
                    continue
                for cols in product(range(U + 1), repeat=nc):
                    if sum(rows) != sum(cols):
                        continue
                    for table in enumerate_tables(rows, cols):
                        checked += 1
                        high = [
                            (i, j)
                            for i in range(nr)
                            for j in range(nc)
                            if table[i][j] > cutoff
                        ]
                        assert len({i for i, _ in high}) == len(high)
                        assert len({j for _, j in high}) == len(high)
                        jvals = {(i, j): table[i][j] for i, j in high}
                        drow = [sum(jvals.get((i, j), 0) for j in range(nc)) for i in range(nr)]
                        dcol = [sum(jvals.get((i, j), 0) for i in range(nr)) for j in range(nc)]
                        residual = [
                            [0 if (i, j) in jvals else table[i][j] for j in range(nc)]
                            for i in range(nr)
                        ]
                        rr, cc = table_margins(residual)
                        assert rr == [rows[i] - drow[i] for i in range(nr)]
                        assert cc == [cols[j] - dcol[j] for j in range(nc)]
                        assert all(residual[i][j] <= cutoff for i in range(nr) for j in range(nc))

                        # Exact probability/incidence cancellation.
                        n = sum(rows)
                        J = sum(jvals.values())
                        pi_num = 1
                        for i in range(nr):
                            pi_num *= falling(rows[i], drow[i])
                        for j in range(nc):
                            pi_num *= falling(cols[j], dcol[j])
                        pi_den = falling(n, J)
                        for x in jvals.values():
                            pi_den *= factorial(x)
                        incidence = Fraction(pi_num, pi_den)

                        pres_num = 1
                        for i in range(nr):
                            pres_num *= factorial(rows[i] - drow[i])
                        for j in range(nc):
                            pres_num *= factorial(cols[j] - dcol[j])
                        pres_den = factorial(n - J)
                        for i in range(nr):
                            for j in range(nc):
                                pres_den *= factorial(residual[i][j])
                        residual_mass = Fraction(pres_num, pres_den)

                        p_num = 1
                        for x in rows:
                            p_num *= factorial(x)
                        for x in cols:
                            p_num *= factorial(x)
                        p_den = factorial(n)
                        for row in table:
                            for x in row:
                                p_den *= factorial(x)
                        assert incidence * residual_mass == Fraction(p_num, p_den)
    return checked


def labelled_matching_disintegration_checks() -> int:
    """Exhaust small labelled matchings and their canonical dependent encoding."""
    checked = 0
    cases = [
        (3, (3, 2), (2, 3)),
        (3, (3, 3), (3, 3)),
        (4, (4, 3), (3, 4)),
    ]
    for U, rows, cols in cases:
        row_stubs = tuple((i, k) for i, degree in enumerate(rows) for k in range(degree))
        col_stubs = tuple((j, k) for j, degree in enumerate(cols) for k in range(degree))
        n = len(row_stubs)
        assert n == len(col_stubs)
        cutoff = U // 2
        encodings: set[tuple[object, ...]] = set()
        table_counts: Counter[tuple[tuple[int, ...], ...]] = Counter()

        for perm in permutations(col_stubs):
            pairs = tuple(zip(row_stubs, perm))
            table = [[0] * len(cols) for _ in rows]
            for (i, _), (j, _) in pairs:
                table[i][j] += 1
            table_t = tuple(tuple(row) for row in table)
            table_counts[table_t] += 1

            high = {(i, j) for i in range(len(rows)) for j in range(len(cols)) if table[i][j] > cutoff}
            assert len({i for i, _ in high}) == len(high)
            assert len({j for _, j in high}) == len(high)
            demand = tuple(sorted(((i, j), table[i][j]) for i, j in high))
            witness = tuple(sorted(pair for pair in pairs if (pair[0][0], pair[1][0]) in high))
            residual = tuple(sorted(pair for pair in pairs if (pair[0][0], pair[1][0]) not in high))
            key = (demand, witness, residual)
            assert key not in encodings
            encodings.add(key)
            checked += 1

        assert checked >= len(encodings)
        assert sum(table_counts.values()) == factorial(n)
        for table_t, count in table_counts.items():
            table = [list(row) for row in table_t]
            high = {(i, j) for i in range(len(rows)) for j in range(len(cols)) if table[i][j] > cutoff}
            jvals = {(i, j): table[i][j] for i, j in high}
            drow = [sum(jvals.get((i, j), 0) for j in range(len(cols))) for i in range(len(rows))]
            dcol = [sum(jvals.get((i, j), 0) for i in range(len(rows))) for j in range(len(cols))]
            residual = [[0 if (i, j) in high else table[i][j] for j in range(len(cols))] for i in range(len(rows))]

            table_count = 1
            for x in rows:
                table_count *= factorial(x)
            for x in cols:
                table_count *= factorial(x)
            for row in table:
                for x in row:
                    table_count //= factorial(x)
            assert count == table_count

            witness_count = 1
            for i, degree in enumerate(rows):
                witness_count *= falling(degree, drow[i])
            for j, degree in enumerate(cols):
                witness_count *= falling(degree, dcol[j])
            for x in jvals.values():
                witness_count //= factorial(x)

            residual_table_count = 1
            for i, degree in enumerate(rows):
                residual_table_count *= factorial(degree - drow[i])
            for j, degree in enumerate(cols):
                residual_table_count *= factorial(degree - dcol[j])
            for row in residual:
                for x in row:
                    residual_table_count //= factorial(x)
            assert witness_count * residual_table_count == table_count
    return checked


def multinomial_fibre_checks() -> int:
    checked = 0
    for ell in range(0, 8):
        options = (0, 1, 2, 3)
        fibres: dict[tuple[int, ...], int] = defaultdict(int)
        weights = (Fraction(1), Fraction(2, 3), Fraction(5, 7), Fraction(11, 13))
        labelled_sum = Fraction(0)
        for assignment in product(options, repeat=ell):
            counts = tuple(assignment.count(e) for e in options)
            fibres[counts] += 1
            term = Fraction(1)
            for e in assignment:
                term *= weights[e]
            labelled_sum += term
        for counts, cardinality in fibres.items():
            expected = factorial(ell)
            for count in counts:
                expected //= factorial(count)
            assert cardinality == expected
            checked += 1
        assert labelled_sum == sum(weights) ** ell

        # After multiplication by 1/ell!, grouping gives 1/prod count!.
        grouped = Fraction(0)
        for counts in fibres:
            term = Fraction(1)
            for e, count in enumerate(counts):
                term *= weights[e] ** count / factorial(count)
            grouped += term
        assert grouped == labelled_sum / factorial(ell)
    return checked


def middle_strip_checks() -> int:
    checked = 0
    for a in range(4, 80):
        cutoff = a // 2
        for m in range(max(1, a - 3), a + 1):
            for r in range(cutoff + 1, m + 1):
                e = m - r
                kind = "endpoint" if e == 0 else ("near" if 4 * e < m else "middle")
                if kind == "middle":
                    assert r <= m - ((m + 3) // 4)
                    assert r <= floor(3 * m / 4)
                    assert r <= floor(3 * a / 4)
                elif kind == "near":
                    assert 1 <= e and 4 * e < m
                checked += 1
    return checked


def is_even_edge_set(edge_set: set[tuple[int, int]], nr: int, nc: int) -> bool:
    row_deg = [0] * nr
    col_deg = [0] * nc
    for i, j in edge_set:
        row_deg[i] ^= 1
        col_deg[j] ^= 1
    return not any(row_deg) and not any(col_deg)


def all_matchings(nr: int, nc: int) -> Iterator[set[tuple[int, int]]]:
    edges = [(i, j) for i in range(nr) for j in range(nc)]
    for mask in range(1 << len(edges)):
        chosen = {edges[k] for k in range(len(edges)) if mask >> k & 1}
        if len({i for i, _ in chosen}) == len(chosen) and len({j for _, j in chosen}) == len(chosen):
            yield chosen


def residual_restriction_checks() -> int:
    checked = 0
    weights_pool = [Fraction(1, 7), Fraction(2, 5), Fraction(3, 4), Fraction(5, 3)]
    for nr, nc in ((2, 2), (2, 3), (3, 3)):
        all_edges = [(i, j) for i in range(nr) for j in range(nc)]
        for M in all_matchings(nr, nc):
            remaining = [e for e in all_edges if e not in M]
            # Deterministic family of residual relations, including the full one.
            residual_sets = [set(remaining)]
            residual_sets += [set(remaining[::2]), set(remaining[1::2])]
            for R in residual_sets:
                universe = sorted(M | R)
                even_sets: list[set[tuple[int, int]]] = []
                images: set[frozenset[tuple[int, int]]] = set()
                for mask in range(1 << len(universe)):
                    F = {universe[k] for k in range(len(universe)) if mask >> k & 1}
                    if is_even_edge_set(F, nr, nc):
                        image = frozenset(F - M)
                        assert image not in images
                        images.add(image)
                        even_sets.append(F)
                assert len(even_sets) <= 2 ** len(R - M)

                weights = {e: weights_pool[idx % len(weights_pool)] for idx, e in enumerate(sorted(R - M))}
                lhs = Fraction(0)
                for F in even_sets:
                    term = Fraction(1)
                    for e in F - M:
                        term *= weights[e]
                    lhs += term
                rhs = Fraction(1)
                for e in R - M:
                    rhs *= 1 + weights[e]
                assert lhs <= rhs
                checked += 1
    return checked


def residual_square_sum_checks() -> int:
    """Check the corrected off-matching square-sum inequality exactly."""
    checked = 0
    for nr, nc in ((2, 2), (2, 3), (3, 2), (3, 3)):
        for U in range(1, 6):
            for row_deg in product(range(U + 1), repeat=nr):
                m0 = sum(row_deg)
                if m0 == 0:
                    continue
                for col_deg in product(range(U + 1), repeat=nc):
                    if sum(col_deg) != m0:
                        continue
                    full_numerator = sum(d * d for d in row_deg) * sum(d * d for d in col_deg)
                    assert full_numerator <= U * U * m0 * m0
                    for M in all_matchings(nr, nc):
                        off_numerator = sum(
                            row_deg[i] ** 2 * col_deg[j] ** 2
                            for i in range(nr)
                            for j in range(nc)
                            if (i, j) not in M
                        )
                        assert off_numerator <= full_numerator
                        checked += 1
    return checked


def central_rate_decimal_checks() -> None:
    getcontext().prec = 80
    q = Decimal(2).ln()
    c = Decimal(1) / 100
    r_lo = Decimal(1) / 64
    r_split = Decimal(47) / 100

    def f(r: Decimal) -> Decimal:
        return r * r.ln() + (Decimal(5) * q / 2 - 1) * r + c * (1 - r)

    def h(r: Decimal) -> Decimal:
        return r * r.ln() + (1 - q / 2 + c) * (1 - r)

    assert f(r_lo) < Decimal("-0.0436")
    assert f(r_split) < Decimal("-0.0051")
    assert h(r_split) < Decimal("-0.0032")
    assert h(Decimal(1)) == 0


def main() -> None:
    counts = {
        "bounded canonical tables": canonical_high_checks(),
        "labelled matching decompositions": labelled_matching_disintegration_checks(),
        "typed decoration fibres": multinomial_fibre_checks(),
        "middle-strip classifications": middle_strip_checks(),
        "even-subgraph restriction instances": residual_restriction_checks(),
        "off-matching square-sum instances": residual_square_sum_checks(),
    }
    central_rate_decimal_checks()
    print("PR27 FINITE VERIFICATION: PASS")
    for name, count in counts.items():
        print(f"  {name}: {count}")
    print("  central-rate endpoint diagnostics: PASS (80-digit Decimal)")


if __name__ == "__main__":
    main()
