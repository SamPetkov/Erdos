#!/usr/bin/env python3
"""Exact regression for the matching-demand physical-fibre identity.

For small matching-supported demand tables, compare:

1. the global prescribed-demand physical-skeleton cardinality;
2. the product of the independent one-cell partial-matching cardinalities;
3. the corresponding reward/incidence aggregate weights.

All arithmetic is integer or Fraction arithmetic.  These checks support but do
not replace the Lean equivalence.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations, permutations, product
from math import factorial


def falling(n: int, k: int) -> int:
    if k < 0 or k > n:
        return 0
    value = 1
    for offset in range(k):
        value *= n - offset
    return value


def reward(j: int) -> int:
    if j <= 2:
        return 1
    return 2 ** (j * (j - 1) // 2 - 1)


def global_fibre_card(row: tuple[int, ...], col: tuple[int, ...], demand: tuple[tuple[int, ...], ...]) -> int:
    row_product = 1
    for i, degree in enumerate(row):
        row_product *= falling(degree, sum(demand[i]))
    col_product = 1
    for j, degree in enumerate(col):
        col_product *= falling(degree, sum(demand[i][j] for i in range(len(row))))
    denominator = 1
    for line in demand:
        for value in line:
            denominator *= factorial(value)
    assert denominator > 0
    assert (row_product * col_product) % denominator == 0
    return row_product * col_product // denominator


def local_product_card(row: tuple[int, ...], col: tuple[int, ...], demand: tuple[tuple[int, ...], ...]) -> int:
    value = 1
    for i, line in enumerate(demand):
        for j, multiplicity in enumerate(line):
            if multiplicity:
                numerator = falling(row[i], multiplicity) * falling(col[j], multiplicity)
                assert numerator % factorial(multiplicity) == 0
                value *= numerator // factorial(multiplicity)
    return value


def total_demand(demand: tuple[tuple[int, ...], ...]) -> int:
    return sum(sum(line) for line in demand)


def local_reward(demand: tuple[tuple[int, ...], ...]) -> int:
    value = 1
    for line in demand:
        for multiplicity in line:
            if multiplicity:
                value *= reward(multiplicity)
    return value


def aggregate_weight(
    ambient: int,
    row: tuple[int, ...],
    col: tuple[int, ...],
    demand: tuple[tuple[int, ...], ...],
) -> Fraction:
    return Fraction(global_fibre_card(row, col, demand) * local_reward(demand), falling(ambient, total_demand(demand)))


def matching_demands(row: tuple[int, ...], col: tuple[int, ...]):
    rows = range(len(row))
    cols = range(len(col))
    yield tuple(tuple(0 for _ in cols) for _ in rows)
    for size in range(1, min(len(row), len(col)) + 1):
        for chosen_rows in combinations(rows, size):
            for chosen_cols in combinations(cols, size):
                for ordered_cols in permutations(chosen_cols):
                    bounds = [min(row[i], col[j]) for i, j in zip(chosen_rows, ordered_cols)]
                    for multiplicities in product(*(range(1, bound + 1) for bound in bounds)):
                        table = [[0 for _ in cols] for _ in rows]
                        for i, j, value in zip(chosen_rows, ordered_cols, multiplicities):
                            table[i][j] = value
                        yield tuple(tuple(line) for line in table)


def run() -> None:
    cases = 0
    weighted_cases = 0
    for row in product(range(1, 5), repeat=3):
        for col in product(range(1, 5), repeat=3):
            for demand in matching_demands(row, col):
                total = total_demand(demand)
                if total > sum(row) or total > sum(col):
                    continue
                global_card = global_fibre_card(row, col, demand)
                local_card = local_product_card(row, col, demand)
                assert global_card == local_card, (row, col, demand, global_card, local_card)
                cases += 1
                ambient = max(sum(row), total)
                if falling(ambient, total):
                    global_weight = aggregate_weight(ambient, row, col, demand)
                    local_weight = Fraction(local_card * local_reward(demand), falling(ambient, total))
                    assert global_weight == local_weight
                    weighted_cases += 1

    # A nonmatching table demonstrates why the factorization requires the
    # support-matching hypothesis: row selections are shared between cells.
    row = (3, 3)
    col = (3, 3)
    nonmatching = ((1, 1), (0, 0))
    assert global_fibre_card(row, col, nonmatching) != local_product_card(row, col, nonmatching)

    print("ERDOS 625 MATCHING-DEMAND PARTIAL-FIBRE REGRESSION: PASS")
    print(f"  exact cardinality cases: {cases}")
    print(f"  exact weighted cases: {weighted_cases}")
    print("  nonmatching control: correctly fails cellwise factorization")


if __name__ == "__main__":
    run()
