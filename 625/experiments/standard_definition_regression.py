#!/usr/bin/env python3
"""Exact finite checks for the standard definitions used in Erdős 625.

This verifies small instances of cocoloring, complement invariance, binary cycle
spaces, the overlap-table law of a uniform bipartite stub matching, and the
matching-supported cell-factorization used in Section VIII. It is not evidence
for the main asymptotic theorem.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
from itertools import permutations, product
from math import factorial


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def pairs(n: int) -> tuple[tuple[int, int], ...]:
    return tuple((i, j) for i in range(n) for j in range(i + 1, n))


def graph_from_code(n: int, code: int) -> frozenset[tuple[int, int]]:
    return frozenset(e for bit, e in enumerate(pairs(n)) if code & (1 << bit))


def complement(n: int, edges: frozenset[tuple[int, int]]) -> frozenset[tuple[int, int]]:
    return frozenset(set(pairs(n)) - set(edges))


def vertices(mask: int, n: int) -> tuple[int, ...]:
    return tuple(v for v in range(n) if mask & (1 << v))


def independent(mask: int, n: int, edges: frozenset[tuple[int, int]]) -> bool:
    vs = vertices(mask, n)
    return all((i, j) not in edges for i in vs for j in vs if i < j)


def clique(mask: int, n: int, edges: frozenset[tuple[int, int]]) -> bool:
    vs = vertices(mask, n)
    return all((i, j) in edges for i in vs for j in vs if i < j)


def minimum_partition_number(n: int, valid: list[bool]) -> int:
    dp = [n + 1] * (1 << n)
    dp[0] = 0
    for mask in range(1, 1 << n):
        first = mask & -mask
        sub = mask
        while sub:
            if sub & first and valid[sub]:
                dp[mask] = min(dp[mask], 1 + dp[mask ^ sub])
            sub = (sub - 1) & mask
    return dp[-1]


def chromatic(n: int, edges: frozenset[tuple[int, int]]) -> int:
    valid = [False] + [independent(mask, n, edges) for mask in range(1, 1 << n)]
    return minimum_partition_number(n, valid)


def cochromatic(n: int, edges: frozenset[tuple[int, int]]) -> int:
    valid = [False] + [
        independent(mask, n, edges) or clique(mask, n, edges)
        for mask in range(1, 1 << n)
    ]
    return minimum_partition_number(n, valid)


def generalized_pco(n: int, edges: frozenset[tuple[int, int]]) -> int:
    """P-chromatic number for P={all complete and all edgeless graphs}."""
    valid = [False] * (1 << n)
    for mask in range(1, 1 << n):
        valid[mask] = independent(mask, n, edges) or clique(mask, n, edges)
    return minimum_partition_number(n, valid)


def check_cocoloring(max_n: int = 5) -> int:
    count = 0
    for n in range(1, max_n + 1):
        for code in range(1 << len(pairs(n))):
            edges = graph_from_code(n, code)
            comp = complement(n, edges)
            zeta = cochromatic(n, edges)
            require(zeta == cochromatic(n, comp), f"complement invariance failed: n={n}, code={code}")
            require(zeta <= chromatic(n, edges), f"zeta<=chi failed: n={n}, code={code}")
            require(zeta <= chromatic(n, comp), f"zeta<=chi(complement) failed: n={n}, code={code}")
            require(zeta == generalized_pco(n, edges), f"P_co interpretation failed: n={n}, code={code}")
            for mask in range(1, 1 << n):
                if mask.bit_count() >= 2:
                    require(
                        not (independent(mask, n, edges) and clique(mask, n, edges)),
                        f"nonunique I/K mark: n={n}, code={code}, mask={mask}",
                    )
            count += 1
    return count


def bipartite_universe(a: int, b: int) -> tuple[tuple[int, int], ...]:
    return tuple((i, j) for i in range(a) for j in range(b))


def component_count(a: int, b: int, edges: frozenset[tuple[int, int]], include_isolates: bool) -> int:
    left = set(range(a)) if include_isolates else {i for i, _ in edges}
    right = set(range(b)) if include_isolates else {j for _, j in edges}
    nodes = {(0, i) for i in left} | {(1, j) for j in right}
    if not nodes:
        return 0
    adjacency = {node: set() for node in nodes}
    for i, j in edges:
        adjacency[(0, i)].add((1, j))
        adjacency[(1, j)].add((0, i))
    seen: set[tuple[int, int]] = set()
    components = 0
    for start in nodes:
        if start in seen:
            continue
        components += 1
        stack = [start]
        seen.add(start)
        while stack:
            node = stack.pop()
            for nxt in adjacency[node]:
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
    return components


def even_subset(subset: frozenset[tuple[int, int]], a: int, b: int) -> bool:
    left = [0] * a
    right = [0] * b
    for i, j in subset:
        left[i] += 1
        right[j] += 1
    return all(value % 2 == 0 for value in left + right)


def check_cycle_spaces(max_a: int = 3, max_b: int = 3) -> int:
    count = 0
    for a in range(1, max_a + 1):
        for b in range(1, max_b + 1):
            universe = bipartite_universe(a, b)
            for code in range(1 << len(universe)):
                edges = frozenset(e for bit, e in enumerate(universe) if code & (1 << bit))
                edge_list = tuple(edges)
                number_even = 0
                for subcode in range(1 << len(edge_list)):
                    subset = frozenset(e for bit, e in enumerate(edge_list) if subcode & (1 << bit))
                    number_even += int(even_subset(subset, a, b))
                incident_vertices = len({i for i, _ in edges}) + len({j for _, j in edges})
                beta = len(edges) - incident_vertices + component_count(a, b, edges, False)
                beta_spanning = len(edges) - (a + b) + component_count(a, b, edges, True)
                require(beta == beta_spanning, "isolated vertices changed cycle rank")
                require(number_even == 2**beta, f"cycle-space count failed: {a}x{b}, code={code}")
                count += 1
    return count


def overlap_table(
    row_types: tuple[int, ...],
    col_types: tuple[int, ...],
    permutation: tuple[int, ...],
    a: int,
    b: int,
) -> tuple[tuple[int, ...], ...]:
    table = [[0] * b for _ in range(a)]
    for row_stub, col_stub in enumerate(permutation):
        table[row_types[row_stub]][col_types[col_stub]] += 1
    return tuple(tuple(row) for row in table)


def overlap_formula(
    row_margins: tuple[int, ...],
    col_margins: tuple[int, ...],
    table: tuple[tuple[int, ...], ...],
) -> int:
    numerator = 1
    for value in row_margins + col_margins:
        numerator *= factorial(value)
    denominator = 1
    for row in table:
        for value in row:
            denominator *= factorial(value)
    require(numerator % denominator == 0, "nonintegral overlap count")
    return numerator // denominator


def check_overlap_law() -> int:
    cases = (
        ((1, 1), (1, 1)),
        ((2, 1), (1, 2)),
        ((2, 2), (1, 3)),
        ((3, 1, 1), (2, 2, 1)),
        ((2, 2, 1), (1, 2, 2)),
    )
    table_count = 0
    for row_margins, col_margins in cases:
        n = sum(row_margins)
        require(n == sum(col_margins), "unequal stub totals")
        row_types = tuple(i for i, d in enumerate(row_margins) for _ in range(d))
        col_types = tuple(j for j, d in enumerate(col_margins) for _ in range(d))
        counts: Counter[tuple[tuple[int, ...], ...]] = Counter()
        for permutation in permutations(range(n)):
            counts[overlap_table(row_types, col_types, permutation, len(row_margins), len(col_margins))] += 1
        require(sum(counts.values()) == factorial(n), "perfect matching count failed")
        total_probability = Fraction(0, 1)
        for table, observed in counts.items():
            expected = overlap_formula(row_margins, col_margins, table)
            require(observed == expected, f"overlap law failed: {row_margins}, {col_margins}, {table}")
            total_probability += Fraction(expected, factorial(n))
            table_count += 1
        require(total_probability == 1, "overlap probabilities do not sum to one")
    return table_count


def falling(x: int, r: int) -> int:
    if r > x:
        return 0
    value = 1
    for offset in range(r):
        value *= x - offset
    return value


def support_is_matching(demand: tuple[tuple[int, ...], ...]) -> bool:
    row_hits = [0] * len(demand)
    col_hits = [0] * len(demand[0])
    for i, row in enumerate(demand):
        for j, value in enumerate(row):
            if value:
                row_hits[i] += 1
                col_hits[j] += 1
    return all(hit <= 1 for hit in row_hits + col_hits)


def global_count(
    row_degree: tuple[int, ...],
    col_degree: tuple[int, ...],
    demand: tuple[tuple[int, ...], ...],
) -> int:
    numerator = 1
    for i, degree in enumerate(row_degree):
        numerator *= falling(degree, sum(demand[i]))
    for j, degree in enumerate(col_degree):
        numerator *= falling(degree, sum(demand[i][j] for i in range(len(demand))))
    denominator = 1
    for row in demand:
        for value in row:
            denominator *= factorial(value)
    return numerator // denominator


def local_product(
    row_degree: tuple[int, ...],
    col_degree: tuple[int, ...],
    demand: tuple[tuple[int, ...], ...],
) -> int:
    value = 1
    for i, row in enumerate(demand):
        for j, cell in enumerate(row):
            if cell:
                value *= falling(row_degree[i], cell) * falling(col_degree[j], cell) // factorial(cell)
    return value


def check_matching_factorization() -> int:
    checked = 0
    degree_cases = (((2, 3), (3, 2)), ((3, 3), (2, 4)), ((2, 3, 2), (3, 2, 2)))
    for row_degree, col_degree in degree_cases:
        size = len(row_degree)
        for entries in product(range(3), repeat=size * size):
            demand = tuple(tuple(entries[i * size + j] for j in range(size)) for i in range(size))
            if any(sum(demand[i]) > row_degree[i] for i in range(size)):
                continue
            if any(sum(demand[i][j] for i in range(size)) > col_degree[j] for j in range(size)):
                continue
            if support_is_matching(demand):
                require(global_count(row_degree, col_degree, demand) == local_product(row_degree, col_degree, demand), "matching cell product failed")
                checked += 1
    explicit_nonmatching = ((1, 1), (0, 0))
    require(not support_is_matching(explicit_nonmatching), "counterexample is a matching")
    require(global_count((3, 3), (3, 3), explicit_nonmatching) != local_product((3, 3), (3, 3), explicit_nonmatching), "nonmatching support did not expose coupling")
    return checked


def main() -> None:
    graphs = check_cocoloring()
    support_graphs = check_cycle_spaces()
    overlap_tables = check_overlap_law()
    matching_demands = check_matching_factorization()
    print("ERDOS 625 STANDARD-DEFINITION REGRESSION: PASS")
    print(f"  simple graphs checked: {graphs}")
    print(f"  bipartite support graphs checked: {support_graphs}")
    print(f"  overlap tables checked: {overlap_tables}")
    print(f"  matching-supported demand tables checked: {matching_demands}")
    print("  verified: zeta(G)=zeta(complement G)")
    print("  verified: zeta is the P_co-chromatic number")
    print("  verified: |cycle space|=2^(|E|-|V|+c)")
    print("  verified: exact uniform-stub overlap law")
    print("  verified: local-cell factorization requires matching support")
    print("  scope: finite definition checks only")


if __name__ == "__main__":
    main()
