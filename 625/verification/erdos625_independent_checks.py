#!/usr/bin/env python3
"""Independent finite checks for the Erdős 625 proof dossier.

These checks test exact identities and small finite instances used in
Sections 6 and 8 of COMPLETE_PROOF_SELF_CONTAINED.md.  They are diagnostic;
they do not prove the asymptotic estimates.

Run:
    python erdos625_independent_checks.py
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, factorial, log, sqrt
from typing import Iterable, Iterator, Sequence


def falling(a: int, r: int) -> int:
    if r < 0 or r > a:
        return 0
    out = 1
    for j in range(r):
        out *= a - j
    return out


def g(x: int) -> int:
    return 1 if x <= 2 else 2 ** (comb(x, 2) - 1)


def beta_of_matrix(r: Sequence[Sequence[int]]) -> int:
    """Cycle rank of the support graph formed by cells with multiplicity >= 2."""
    rows = len(r)
    cols = len(r[0])
    edges = [(i, j) for i in range(rows) for j in range(cols) if r[i][j] >= 2]
    if not edges:
        return 0

    vertices: set[tuple[str, int]] = set()
    adjacency: dict[tuple[str, int], list[tuple[str, int]]] = {}
    for i, j in edges:
        a = ("r", i)
        b = ("c", j)
        vertices.update((a, b))
        adjacency.setdefault(a, []).append(b)
        adjacency.setdefault(b, []).append(a)

    seen: set[tuple[str, int]] = set()
    components = 0
    for vertex in vertices:
        if vertex in seen:
            continue
        components += 1
        stack = [vertex]
        seen.add(vertex)
        while stack:
            current = stack.pop()
            for neighbour in adjacency.get(current, []):
                if neighbour not in seen:
                    seen.add(neighbour)
                    stack.append(neighbour)

    return len(edges) - len(vertices) + components


def direct_compatible_sign_pairs(r: Sequence[Sequence[int]]) -> int:
    rows = len(r)
    cols = len(r[0])
    count = 0
    for row_signs in product((0, 1), repeat=rows):
        for col_signs in product((0, 1), repeat=cols):
            if all(
                r[i][j] < 2 or row_signs[i] == col_signs[j]
                for i in range(rows)
                for j in range(cols)
            ):
                count += 1
    return count


def check_sign_sum_identity() -> None:
    """Exhaust Lemma 6.1 on all 2x2 matrices with entries 0,...,4."""
    checked = 0
    for entries in product(range(5), repeat=4):
        r = [list(entries[:2]), list(entries[2:])]
        support_edges = sum(x >= 2 for row in r for x in row)
        nonisolated_rows = sum(any(x >= 2 for x in row) for row in r)
        nonisolated_cols = sum(any(r[i][j] >= 2 for i in range(2)) for j in range(2))
        beta = beta_of_matrix(r)
        components = beta - support_edges + nonisolated_rows + nonisolated_cols

        compatible = direct_compatible_sign_pairs(r)
        expected_compatible = 2 ** (
            4 - nonisolated_rows - nonisolated_cols + components
        )
        assert compatible == expected_compatible

        overlap_pairs = sum(comb(x, 2) for row in r for x in row)
        left = Fraction(2 ** (overlap_pairs + components - nonisolated_rows - nonisolated_cols), 1)
        right = Fraction(2**beta, 1)
        for row in r:
            for x in row:
                right *= g(x)
        assert left == right
        checked += 1

    print(f"PASS Lemma 6.1 sign-sum identity ({checked} overlap matrices)")


def ordered_partitions(n: int, sizes: Sequence[int]) -> list[tuple[frozenset[int], ...]]:
    vertices = tuple(range(n))
    out: list[tuple[frozenset[int], ...]] = []

    def recurse(
        remaining: tuple[int, ...],
        index: int,
        current: list[frozenset[int]],
    ) -> None:
        if index == len(sizes):
            out.append(tuple(current))
            return
        size = sizes[index]
        for choice_tuple in combinations(remaining, size):
            choice = frozenset(choice_tuple)
            recurse(
                tuple(v for v in remaining if v not in choice),
                index + 1,
                current + [choice],
            )

    recurse(vertices, 0, [])
    return out


def graph_edge_assignments(n: int) -> Iterator[dict[tuple[int, int], int]]:
    edges = list(combinations(range(n), 2))
    for mask in range(1 << len(edges)):
        yield {edge: (mask >> index) & 1 for index, edge in enumerate(edges)}


def witness_satisfied(
    graph: dict[tuple[int, int], int],
    partition: Sequence[frozenset[int]],
    signs: Sequence[int],
) -> bool:
    for block, sign in zip(partition, signs):
        for edge in combinations(sorted(block), 2):
            if graph[edge] != sign:
                return False
    return True


def overlap_matrix(
    first: Sequence[frozenset[int]],
    second: Sequence[frozenset[int]],
) -> list[list[int]]:
    return [[len(a & b) for b in second] for a in first]


def check_exact_second_moment() -> None:
    """Compare direct graph enumeration with the overlap formula at n=6."""
    n = 6
    sizes = (3, 3)
    partitions = ordered_partitions(n, sizes)
    signs = list(product((0, 1), repeat=len(sizes)))

    witness_counts: list[int] = []
    for graph in graph_edge_assignments(n):
        count = sum(
            witness_satisfied(graph, partition, sign_assignment)
            for partition in partitions
            for sign_assignment in signs
        )
        witness_counts.append(count)

    expectation = Fraction(sum(witness_counts), len(witness_counts))
    second_moment = Fraction(
        sum(count * count for count in witness_counts), len(witness_counts)
    )
    direct_ratio = second_moment / (expectation * expectation)

    overlap_total = Fraction(0, 1)
    for first in partitions:
        for second in partitions:
            r = overlap_matrix(first, second)
            factor = Fraction(2 ** beta_of_matrix(r), 1)
            for row in r:
                for x in row:
                    factor *= g(x)
            overlap_total += factor
    overlap_ratio = overlap_total / (len(partitions) ** 2)

    assert direct_ratio == overlap_ratio
    print(
        "PASS exact signed second moment for n=6, profile (3,3): "
        f"ratio={direct_ratio}"
    )


def configuration_distribution(
    row_degrees: Sequence[int], col_degrees: Sequence[int]
) -> dict[tuple[int, ...], int]:
    """Enumerate labelled stub matchings and return 2x2 cell-count frequencies."""
    row_stubs: list[tuple[int, int]] = []
    col_stubs: list[tuple[int, int]] = []
    for i, degree in enumerate(row_degrees):
        row_stubs.extend((i, stub) for stub in range(degree))
    for j, degree in enumerate(col_degrees):
        col_stubs.extend((j, stub) for stub in range(degree))
    assert len(row_stubs) == len(col_stubs)

    frequencies: dict[tuple[int, ...], int] = {}
    for permuted_cols in permutations(col_stubs):
        counts = [[0 for _ in col_degrees] for _ in row_degrees]
        for row_stub, col_stub in zip(row_stubs, permuted_cols):
            counts[row_stub[0]][col_stub[0]] += 1
        key = tuple(x for row in counts for x in row)
        frequencies[key] = frequencies.get(key, 0) + 1
    return frequencies


def prescribed_cell_bound(
    row_degrees: Sequence[int],
    col_degrees: Sequence[int],
    demands: dict[tuple[int, int], int],
) -> Fraction:
    row_demands = [0] * len(row_degrees)
    col_demands = [0] * len(col_degrees)
    total_demand = 0
    cell_factorials = 1
    for (i, j), demand in demands.items():
        row_demands[i] += demand
        col_demands[j] += demand
        total_demand += demand
        cell_factorials *= factorial(demand)

    numerator = 1
    for degree, demand in zip(row_degrees, row_demands):
        numerator *= falling(degree, demand)
    for degree, demand in zip(col_degrees, col_demands):
        numerator *= falling(degree, demand)

    total_degree = sum(row_degrees)
    denominator = falling(total_degree, total_demand) * cell_factorials
    return Fraction(numerator, denominator) if denominator else Fraction(0, 1)


def check_prescribed_cell_bound() -> None:
    """Check Lemma 6.2 on all nonzero 2x2 degree lists of total at most 6."""
    checked = 0
    for total in range(1, 7):
        for left_degree in range(total + 1):
            row_degrees = (left_degree, total - left_degree)
            for top_degree in range(total + 1):
                col_degrees = (top_degree, total - top_degree)
                frequencies = configuration_distribution(row_degrees, col_degrees)
                number_of_matchings = factorial(total)

                for raw_demands in product(range(3), repeat=4):
                    if not any(raw_demands) or sum(raw_demands) > 3:
                        continue
                    demands = {
                        divmod(index, 2): demand
                        for index, demand in enumerate(raw_demands)
                        if demand
                    }
                    favourable = 0
                    for flattened, frequency in frequencies.items():
                        if all(flattened[2 * i + j] >= demand for (i, j), demand in demands.items()):
                            favourable += frequency
                    exact_probability = Fraction(favourable, number_of_matchings)
                    upper_bound = prescribed_cell_bound(row_degrees, col_degrees, demands)
                    assert exact_probability <= upper_bound, (
                        row_degrees,
                        col_degrees,
                        demands,
                        exact_probability,
                        upper_bound,
                    )
                    checked += 1

    print(f"PASS Lemma 6.2 prescribed-cell bound ({checked} finite cases)")


def diagonal_weight(
    n: int,
    sizes: Sequence[int],
    counts: Sequence[int],
    margins: Sequence[int],
) -> Fraction:
    mass = sum(size * margin for size, margin in zip(sizes, margins))
    numerator = 1
    for size, count, margin in zip(sizes, counts, margins):
        numerator *= falling(count, margin) ** 2
        numerator *= (factorial(size) * g(size)) ** margin
        numerator //= factorial(margin)
    return Fraction(numerator, falling(n, mass))


def endpoint_weight(
    n: int,
    sizes: Sequence[int],
    counts: Sequence[int],
    table: Sequence[Sequence[int]],
) -> tuple[Fraction, list[int], list[int]]:
    type_count = len(sizes)
    row_margins = [sum(table[i]) for i in range(type_count)]
    col_margins = [sum(table[i][j] for i in range(type_count)) for j in range(type_count)]

    numerator = Fraction(1, 1)
    for count, margin in zip(counts, row_margins):
        numerator *= falling(count, margin)
    for count, margin in zip(counts, col_margins):
        numerator *= falling(count, margin)

    incidence_mass = 0
    for i in range(type_count):
        for j in range(type_count):
            multiplicity = table[i][j]
            numerator /= factorial(multiplicity)
            overlap = min(sizes[i], sizes[j])
            incidence_mass += overlap * multiplicity
            local = Fraction(
                falling(sizes[i], overlap) * falling(sizes[j], overlap),
                factorial(overlap),
            ) * g(overlap)
            numerator *= local**multiplicity

    return (
        numerator / falling(n, incidence_mass),
        row_margins,
        col_margins,
    )


def q_bound(n: int, sizes: Sequence[int], i: int, j: int) -> float:
    if i == j:
        return 1.0
    larger = max(sizes[i], sizes[j])
    smaller = min(sizes[i], sizes[j])
    deficit = larger - smaller
    return (
        (n + 1) ** (deficit / 2)
        * sqrt(falling(larger, deficit))
        / factorial(deficit)
        * 2 ** (-(deficit * smaller + comb(deficit, 2)) / 2)
    )


def bounded_tables(
    type_count: int,
    row_caps: Sequence[int],
    col_caps: Sequence[int],
    total_cap: int,
) -> Iterator[list[list[int]]]:
    table = [[0] * type_count for _ in range(type_count)]
    row_used = [0] * type_count
    col_used = [0] * type_count

    def recurse(cell: int, total_used: int) -> Iterator[list[list[int]]]:
        if cell == type_count * type_count:
            yield [row[:] for row in table]
            return
        i, j = divmod(cell, type_count)
        maximum = min(
            row_caps[i] - row_used[i],
            col_caps[j] - col_used[j],
            total_cap - total_used,
        )
        for value in range(maximum + 1):
            table[i][j] = value
            row_used[i] += value
            col_used[j] += value
            yield from recurse(cell + 1, total_used + value)
            row_used[i] -= value
            col_used[j] -= value
        table[i][j] = 0

    yield from recurse(0, 0)


def check_transport_inequality() -> None:
    """Exhaust a finite family of Lemma 8.1 endpoint tables."""
    sizes = (5, 4, 3, 2)
    counts = (2, 2, 2, 2)
    n = sum(size * count for size, count in zip(sizes, counts))
    checked = 0
    largest_ratio = 0.0

    for table in bounded_tables(4, counts, counts, total_cap=4):
        weight, row_margins, col_margins = endpoint_weight(n, sizes, counts, table)
        diagonal_geometric_mean = sqrt(
            float(
                diagonal_weight(n, sizes, counts, row_margins)
                * diagonal_weight(n, sizes, counts, col_margins)
            )
        )

        combinatorial_factor = 1.0
        for margin in row_margins:
            combinatorial_factor *= factorial(margin)
        for margin in col_margins:
            combinatorial_factor *= factorial(margin)
        combinatorial_factor = sqrt(combinatorial_factor)

        for i in range(4):
            for j in range(4):
                multiplicity = table[i][j]
                combinatorial_factor /= factorial(multiplicity)
                combinatorial_factor *= q_bound(n, sizes, i, j) ** multiplicity

        right_hand_side = diagonal_geometric_mean * combinatorial_factor
        ratio = float(weight) / right_hand_side if right_hand_side else 0.0
        largest_ratio = max(largest_ratio, ratio)
        assert ratio <= 1.0 + 1e-11, (ratio, table)
        checked += 1

    print(
        "PASS Lemma 8.1 transport inequality "
        f"({checked} typed tables; maximum ratio={largest_ratio:.12g})"
    )


def check_near_containment_ratio() -> None:
    """Check the exact local ratio (8.21) in its stated range."""
    checked = 0
    for smaller in range(5, 40):
        for deficit in range(4):
            larger = smaller + deficit
            endpoint = (
                Fraction(
                    falling(larger, smaller) * falling(smaller, smaller),
                    factorial(smaller),
                )
                * g(smaller)
            )
            for missing in range(1, (smaller - 1) // 4 + 1):
                overlap = smaller - missing
                actual = (
                    Fraction(
                        falling(larger, overlap) * falling(smaller, overlap),
                        factorial(overlap),
                    )
                    * g(overlap)
                )
                formula = Fraction(comb(smaller, missing), 1)
                for h in range(1, missing + 1):
                    formula /= deficit + h
                formula *= Fraction(
                    1,
                    2 ** (missing * smaller - missing * (missing + 1) // 2),
                )
                assert actual / endpoint == formula
                checked += 1

    print(f"PASS exact near-containment ratio (8.21) ({checked} cases)")


def main() -> None:
    check_sign_sum_identity()
    check_exact_second_moment()
    check_prescribed_cell_bound()
    check_transport_inequality()
    check_near_containment_ratio()
    print("ALL INDEPENDENT FINITE CHECKS PASSED")


if __name__ == "__main__":
    main()
