#!/usr/bin/env python3
"""Certified small-instance experiments for chromatic and cochromatic number.

The implementation uses only the Python standard library:

* Bron--Kerbosch bitset enumeration of maximal cliques (and, in the
  complement, maximal independent sets);
* an exact minimum-set-cover branch-and-bound over those maximal sets;
* deterministic SplitMix64 random graphs, so a row is reproducible from
  ``(n, seed)`` independently of Python's ``random`` implementation.

Every row written with ``status == "exact"`` contains certified optima.  A
timeout is reported, never silently converted into a bound or estimate.

Examples
--------

Run the exhaustive independent self-test on every labelled graph of order at
most five::

    python exact_chi_zeta.py --self-test --exhaustive-n 5

Generate the checked experiment table used by EXACT_EXPERIMENTS.md::

    python exact_chi_zeta.py --sample --n 12,14,16,18,20,22,24,26,28 \
        --seeds 0,1,2 --check-complement --timeout 120 \
        --output EXACT_EXPERIMENTS.csv

Finite computations in this file are diagnostic only; they do not provide
asymptotic evidence for Erdos Problem 625.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import sys
import time
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Iterable, Sequence


MASK64 = (1 << 64) - 1


class DeadlineExceeded(RuntimeError):
    """Raised when an explicitly supplied wall-clock deadline is exceeded."""


class SplitMix64:
    """Tiny, fully specified deterministic 64-bit generator."""

    def __init__(self, seed: int):
        self.state = seed & MASK64

    def next_u64(self) -> int:
        self.state = (self.state + 0x9E3779B97F4A7C15) & MASK64
        z = self.state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK64
        return (z ^ (z >> 31)) & MASK64

    def bit(self) -> int:
        return self.next_u64() >> 63


def random_graph(n: int, seed: int) -> tuple[int, ...]:
    """Return adjacency bitmasks for deterministic G(n, 1/2)."""

    if n < 0:
        raise ValueError("n must be nonnegative")
    rng = SplitMix64(seed)
    adj = [0] * n
    for i in range(n):
        for j in range(i + 1, n):
            if rng.bit():
                adj[i] |= 1 << j
                adj[j] |= 1 << i
    return tuple(adj)


def graph_from_code(n: int, code: int) -> tuple[int, ...]:
    """Decode upper-triangular edge bits, in lexicographic pair order."""

    adj = [0] * n
    bit = 0
    for i in range(n):
        for j in range(i + 1, n):
            if (code >> bit) & 1:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            bit += 1
    return tuple(adj)


def complement(adj: Sequence[int]) -> tuple[int, ...]:
    n = len(adj)
    all_vertices = (1 << n) - 1
    return tuple((all_vertices ^ (1 << v) ^ adj[v]) for v in range(n))


def edge_count(adj: Sequence[int]) -> int:
    return sum(mask.bit_count() for mask in adj) // 2


def graph_digest(adj: Sequence[int]) -> str:
    """SHA-256 of n and packed upper-triangular edge bits."""

    n = len(adj)
    packed = bytearray()
    current = 0
    used = 0
    for i in range(n):
        for j in range(i + 1, n):
            current |= (((adj[i] >> j) & 1) << used)
            used += 1
            if used == 8:
                packed.append(current)
                current = 0
                used = 0
    if used:
        packed.append(current)
    payload = n.to_bytes(4, "little") + bytes(packed)
    return hashlib.sha256(payload).hexdigest()


def _check_deadline(deadline: float | None) -> None:
    if deadline is not None and time.perf_counter() > deadline:
        raise DeadlineExceeded


def enumerate_maximal_cliques(
    adj: Sequence[int], deadline: float | None = None
) -> tuple[list[int], int]:
    """Enumerate every maximal clique with Bron--Kerbosch plus pivoting.

    Returns ``(clique_masks, recursion_nodes)``.  The empty graph on zero
    vertices is treated separately and has no nonempty cover columns.
    """

    n = len(adj)
    if n == 0:
        return [], 0
    output: list[int] = []
    nodes = 0

    def visit(r: int, p: int, x: int) -> None:
        nonlocal nodes
        nodes += 1
        if (nodes & 1023) == 0:
            _check_deadline(deadline)
        if p == 0 and x == 0:
            output.append(r)
            return

        px = p | x
        if px:
            best_u = -1
            best_score = -1
            scan = px
            while scan:
                b = scan & -scan
                u = b.bit_length() - 1
                score = (p & adj[u]).bit_count()
                if score > best_score:
                    best_score = score
                    best_u = u
                scan ^= b
            candidates = p & ~adj[best_u]
        else:
            candidates = p

        while candidates:
            b = candidates & -candidates
            v = b.bit_length() - 1
            visit(r | b, p & adj[v], x & adj[v])
            p ^= b
            x |= b
            candidates ^= b

    visit(0, (1 << n) - 1, 0)
    output.sort(key=lambda mask: (-mask.bit_count(), mask))
    return output, nodes


@dataclass(frozen=True)
class Column:
    mask: int
    kind: str  # "I" for independent, "C" for clique


@dataclass
class CoverResult:
    value: int
    selected: tuple[Column, ...]
    lower_bound: int
    greedy_upper_bound: int
    search_nodes: int
    seconds: float


def _deduplicate_columns(columns: Iterable[Column]) -> tuple[Column, ...]:
    # The same mask can be both types only for a singleton.  Keep a stable
    # representative; the objective is unaffected.
    by_mask: dict[int, Column] = {}
    for column in columns:
        if column.mask == 0:
            continue
        old = by_mask.get(column.mask)
        if old is None or (column.kind, column.mask) < (old.kind, old.mask):
            by_mask[column.mask] = column
    return tuple(
        sorted(by_mask.values(), key=lambda c: (-c.mask.bit_count(), c.mask, c.kind))
    )


class ExactSetCover:
    """Exact unweighted set cover by iterative deepening.

    The recurrence branches on an uncovered vertex.  For that vertex, a
    column whose currently uncovered part is contained in another candidate's
    part is safely dominated and omitted.  Failed states are memoized by the
    largest tested remaining depth.
    """

    def __init__(
        self,
        n: int,
        columns: Iterable[Column],
        *,
        deadline: float | None = None,
        certified_initial_lower_bound: int = 0,
    ):
        self.n = n
        self.all_vertices = (1 << n) - 1
        self.columns = _deduplicate_columns(columns)
        self.deadline = deadline
        self.certified_initial_lower_bound = certified_initial_lower_bound
        self.nodes = 0
        self.by_vertex: list[tuple[int, ...]] = []
        for v in range(n):
            self.by_vertex.append(
                tuple(i for i, c in enumerate(self.columns) if (c.mask >> v) & 1)
            )
        if n and any(not indices for indices in self.by_vertex):
            raise ValueError("columns do not cover the universe")

        # Two vertices are incompatible if no available column contains both.
        # A greedily constructed clique in this incompatibility graph is a
        # certified lower bound on the number of cover columns.
        self.incompatible = [0] * n
        for v in range(n):
            co_coverable = 0
            for i in self.by_vertex[v]:
                co_coverable |= self.columns[i].mask
            self.incompatible[v] = self.all_vertices & ~co_coverable

        self.pivot_order = tuple(sorted(range(n), key=lambda v: (len(self.by_vertex[v]), v)))
        self._lower_cache: dict[int, int] = {}
        self._fail_depth: dict[int, int] = {}

    def _greedy_cover(self) -> list[int]:
        uncovered = self.all_vertices
        selected: list[int] = []
        while uncovered:
            best = max(
                range(len(self.columns)),
                key=lambda i: (
                    (self.columns[i].mask & uncovered).bit_count(),
                    self.columns[i].mask.bit_count(),
                    -i,
                ),
            )
            if not (self.columns[best].mask & uncovered):
                raise ValueError("columns do not cover the universe")
            selected.append(best)
            uncovered &= ~self.columns[best].mask

        # Make the cover inclusion-minimal, which also guarantees that every
        # selected column has a private vertex for later disjointification.
        changed = True
        while changed:
            changed = False
            for pos in range(len(selected) - 1, -1, -1):
                union_other = 0
                for j, idx in enumerate(selected):
                    if j != pos:
                        union_other |= self.columns[idx].mask
                if union_other == self.all_vertices:
                    del selected[pos]
                    changed = True
                    break
        return selected

    def _packing_bound(self, uncovered: int) -> int:
        """Size of a greedily found pairwise-incompatible vertex set."""

        if uncovered == 0:
            return 0
        candidates = uncovered
        count = 0
        while candidates:
            scan = candidates
            best_v = -1
            best_degree = -1
            while scan:
                b = scan & -scan
                v = b.bit_length() - 1
                degree = (self.incompatible[v] & candidates).bit_count()
                if degree > best_degree:
                    best_degree = degree
                    best_v = v
                scan ^= b
            count += 1
            candidates &= self.incompatible[best_v]
        return count

    def _lower_bound(self, uncovered: int) -> int:
        cached = self._lower_cache.get(uncovered)
        if cached is not None:
            return cached
        if uncovered == 0:
            return 0
        max_gain = max((c.mask & uncovered).bit_count() for c in self.columns)
        volume = (uncovered.bit_count() + max_gain - 1) // max_gain
        packing = self._packing_bound(uncovered)
        answer = max(volume, packing)
        self._lower_cache[uncovered] = answer
        return answer

    def _pivot(self, uncovered: int) -> int:
        for v in self.pivot_order:
            if (uncovered >> v) & 1:
                return v
        raise AssertionError("pivot requested for empty state")

    def _options(self, v: int, uncovered: int) -> list[int]:
        # Collapse columns with identical gain, retaining a deterministic
        # representative.
        representative: dict[int, int] = {}
        for idx in self.by_vertex[v]:
            gain = self.columns[idx].mask & uncovered
            if gain not in representative:
                representative[gain] = idx

        # Retain inclusion-maximal gains only.  Replacing a smaller gain by a
        # larger one cannot make the remainder harder to cover.
        ordered = sorted(
            representative,
            key=lambda gain: (-gain.bit_count(), representative[gain]),
        )
        maximal: list[int] = []
        for gain in ordered:
            if any((gain & ~larger) == 0 for larger in maximal):
                continue
            maximal.append(gain)
        return [representative[gain] for gain in maximal]

    def _decide(self, uncovered: int, remaining: int) -> list[int] | None:
        self.nodes += 1
        if (self.nodes & 1023) == 0:
            _check_deadline(self.deadline)
        if uncovered == 0:
            return []
        if remaining == 0 or self._lower_bound(uncovered) > remaining:
            return None
        if self._fail_depth.get(uncovered, -1) >= remaining:
            return None

        pivot = self._pivot(uncovered)
        for idx in self._options(pivot, uncovered):
            remainder = uncovered & ~self.columns[idx].mask
            tail = self._decide(remainder, remaining - 1)
            if tail is not None:
                return [idx, *tail]
        self._fail_depth[uncovered] = max(self._fail_depth.get(uncovered, -1), remaining)
        return None

    def solve(self) -> CoverResult:
        started = time.perf_counter()
        if self.n == 0:
            return CoverResult(0, (), 0, 0, 0, time.perf_counter() - started)
        _check_deadline(self.deadline)
        greedy = self._greedy_cover()
        greedy_ub = len(greedy)
        initial_lb = max(
            self.certified_initial_lower_bound,
            self._lower_bound(self.all_vertices),
        )
        if initial_lb > greedy_ub:
            raise AssertionError("certified lower bound exceeds a feasible cover")

        selected = greedy
        optimum = greedy_ub
        for depth in range(initial_lb, greedy_ub):
            _check_deadline(self.deadline)
            choice = self._decide(self.all_vertices, depth)
            if choice is not None:
                selected = choice
                optimum = len(choice)
                break

        result_columns = tuple(self.columns[i] for i in selected)
        return CoverResult(
            value=optimum,
            selected=result_columns,
            lower_bound=initial_lb,
            greedy_upper_bound=greedy_ub,
            search_nodes=self.nodes,
            seconds=time.perf_counter() - started,
        )


def _is_clique(mask: int, adj: Sequence[int]) -> bool:
    scan = mask
    while scan:
        b = scan & -scan
        v = b.bit_length() - 1
        if (mask ^ b) & ~adj[v]:
            return False
        scan ^= b
    return True


def _is_independent(mask: int, adj: Sequence[int]) -> bool:
    scan = mask
    while scan:
        b = scan & -scan
        v = b.bit_length() - 1
        if (mask ^ b) & adj[v]:
            return False
        scan ^= b
    return True


def disjointify(selected: Sequence[Column], n: int) -> tuple[Column, ...]:
    """Turn a minimum cover into a nonempty homogeneous partition."""

    all_vertices = (1 << n) - 1
    if not selected:
        if n:
            raise AssertionError("empty selected cover for nonempty graph")
        return ()
    union = 0
    for column in selected:
        union |= column.mask
    if union != all_vertices:
        raise AssertionError("selected columns do not cover every vertex")

    classes = [0] * len(selected)
    assigned = 0
    for i, column in enumerate(selected):
        others = 0
        for j, other in enumerate(selected):
            if i != j:
                others |= other.mask
        private = column.mask & ~others
        if private == 0:
            raise AssertionError("optimal cover contains a redundant column")
        classes[i] |= private
        assigned |= private

    remaining = all_vertices & ~assigned
    while remaining:
        b = remaining & -remaining
        owners = [i for i, column in enumerate(selected) if column.mask & b]
        if not owners:
            raise AssertionError("covered vertex lost during disjointification")
        # Balance ties deterministically so the profile is informative.
        owner = min(owners, key=lambda i: (classes[i].bit_count(), i))
        classes[owner] |= b
        remaining ^= b
    return tuple(Column(classes[i], selected[i].kind) for i in range(len(selected)))


def verify_partition(partition: Sequence[Column], adj: Sequence[int]) -> None:
    n = len(adj)
    union = 0
    for column in partition:
        if not column.mask or (union & column.mask):
            raise AssertionError("partition classes must be nonempty and disjoint")
        union |= column.mask
        if column.kind == "I" and not _is_independent(column.mask, adj):
            raise AssertionError("purported independent class contains an edge")
        if column.kind == "C" and not _is_clique(column.mask, adj):
            raise AssertionError("purported clique class contains a nonedge")
    if union != (1 << n) - 1:
        raise AssertionError("partition does not cover every vertex")


@dataclass
class ExactInvariants:
    alpha: int
    omega: int
    chi: int
    zeta: int
    chi_partition: tuple[Column, ...]
    zeta_partition: tuple[Column, ...]
    maximal_independent_sets: int
    maximal_cliques: int
    enumeration_nodes: int
    enumeration_seconds: float
    chi_result: CoverResult
    zeta_result: CoverResult


def exact_invariants(
    adj: Sequence[int], *, deadline: float | None = None
) -> ExactInvariants:
    n = len(adj)
    enum_started = time.perf_counter()
    cliques, clique_nodes = enumerate_maximal_cliques(adj, deadline)
    independent, independent_nodes = enumerate_maximal_cliques(complement(adj), deadline)
    enum_seconds = time.perf_counter() - enum_started
    alpha = max((m.bit_count() for m in independent), default=0)
    omega = max((m.bit_count() for m in cliques), default=0)

    independent_columns = [Column(mask, "I") for mask in independent]
    clique_columns = [Column(mask, "C") for mask in cliques]
    chi_result = ExactSetCover(
        n,
        independent_columns,
        deadline=deadline,
        certified_initial_lower_bound=omega,
    ).solve()
    zeta_result = ExactSetCover(
        n,
        [*independent_columns, *clique_columns],
        deadline=deadline,
    ).solve()
    chi_partition = disjointify(chi_result.selected, n)
    zeta_partition = disjointify(zeta_result.selected, n)
    verify_partition(chi_partition, adj)
    verify_partition(zeta_partition, adj)
    if any(c.kind != "I" for c in chi_partition):
        raise AssertionError("chromatic certificate contains a clique class")
    if len(chi_partition) != chi_result.value or len(zeta_partition) != zeta_result.value:
        raise AssertionError("certificate length differs from optimum")

    return ExactInvariants(
        alpha=alpha,
        omega=omega,
        chi=chi_result.value,
        zeta=zeta_result.value,
        chi_partition=chi_partition,
        zeta_partition=zeta_partition,
        maximal_independent_sets=len(independent),
        maximal_cliques=len(cliques),
        enumeration_nodes=clique_nodes + independent_nodes,
        enumeration_seconds=enum_seconds,
        chi_result=chi_result,
        zeta_result=zeta_result,
    )


def profile_json(partition: Sequence[Column]) -> str:
    entries = sorted(
        ((column.kind, column.mask.bit_count()) for column in partition),
        key=lambda item: (item[0], -item[1]),
    )
    return json.dumps(entries, separators=(",", ":"))


def alpha0_statistics(n: int) -> dict[str, float | int]:
    if n < 2:
        raise ValueError("alpha0 statistics require n >= 2")
    log2_n = math.log2(n)
    alpha0 = (
        2.0 * log2_n
        - 2.0 * math.log2(log2_n)
        + 2.0 * math.log2(math.e / 2.0)
        + 1.0
    )
    a = math.floor(alpha0)
    ln_mu = (
        math.lgamma(n + 1)
        - math.lgamma(a + 1)
        - math.lgamma(n - a + 1)
        - (a * (a - 1) / 2.0) * math.log(2.0)
    )
    return {
        "alpha0": alpha0,
        "alpha0_floor": a,
        "alpha0_phase": alpha0 - a,
        "log2_mu_alpha0_floor": ln_mu / math.log(2.0),
        "log_mu_alpha_over_log_n": ln_mu / math.log(n),
    }


CSV_FIELDS = [
    "status",
    "n",
    "seed",
    "generator",
    "graph_sha256",
    "edges",
    "alpha0",
    "alpha0_floor",
    "alpha0_phase",
    "log2_mu_alpha0_floor",
    "log_mu_alpha_over_log_n",
    "alpha",
    "omega",
    "chi",
    "zeta",
    "gap",
    "chi_profile",
    "zeta_profile",
    "maximal_independent_sets",
    "maximal_cliques",
    "enumeration_nodes",
    "chi_search_nodes",
    "zeta_search_nodes",
    "chi_initial_lower_bound",
    "chi_greedy_upper_bound",
    "zeta_initial_lower_bound",
    "zeta_greedy_upper_bound",
    "enumeration_seconds",
    "chi_seconds",
    "zeta_seconds",
    "total_seconds",
    "complement_checked",
    "error",
]


def experiment_row(
    n: int,
    seed: int,
    *,
    timeout: float,
    check_complement: bool,
) -> dict[str, object]:
    started = time.perf_counter()
    adj = random_graph(n, seed)
    base: dict[str, object] = {
        "status": "timeout",
        "n": n,
        "seed": seed,
        "generator": "splitmix64-v1/high-bit/p=1/2",
        "graph_sha256": graph_digest(adj),
        "edges": edge_count(adj),
        "complement_checked": False,
        "error": "",
    }
    base.update(alpha0_statistics(n))
    deadline = None if timeout <= 0 else started + timeout
    try:
        inv = exact_invariants(adj, deadline=deadline)
        complement_checked = False
        if check_complement:
            comp = exact_invariants(complement(adj), deadline=deadline)
            if comp.zeta != inv.zeta:
                raise AssertionError("zeta(G) != zeta(complement(G))")
            if comp.alpha != inv.omega or comp.omega != inv.alpha:
                raise AssertionError("alpha/omega complement symmetry failed")
            complement_checked = True
        base.update(
            {
                "status": "exact",
                "alpha": inv.alpha,
                "omega": inv.omega,
                "chi": inv.chi,
                "zeta": inv.zeta,
                "gap": inv.chi - inv.zeta,
                "chi_profile": profile_json(inv.chi_partition),
                "zeta_profile": profile_json(inv.zeta_partition),
                "maximal_independent_sets": inv.maximal_independent_sets,
                "maximal_cliques": inv.maximal_cliques,
                "enumeration_nodes": inv.enumeration_nodes,
                "chi_search_nodes": inv.chi_result.search_nodes,
                "zeta_search_nodes": inv.zeta_result.search_nodes,
                "chi_initial_lower_bound": inv.chi_result.lower_bound,
                "chi_greedy_upper_bound": inv.chi_result.greedy_upper_bound,
                "zeta_initial_lower_bound": inv.zeta_result.lower_bound,
                "zeta_greedy_upper_bound": inv.zeta_result.greedy_upper_bound,
                "enumeration_seconds": f"{inv.enumeration_seconds:.9f}",
                "chi_seconds": f"{inv.chi_result.seconds:.9f}",
                "zeta_seconds": f"{inv.zeta_result.seconds:.9f}",
                "complement_checked": complement_checked,
            }
        )
    except DeadlineExceeded:
        base["error"] = f"wall-clock limit {timeout:g}s exceeded"
    except Exception as exc:  # Preserve a diagnostic row before re-raising later.
        base["status"] = "error"
        base["error"] = f"{type(exc).__name__}: {exc}"
    base["total_seconds"] = f"{time.perf_counter() - started:.9f}"
    return base


def brute_allowed_sets(adj: Sequence[int], homogeneous: bool) -> list[int]:
    n = len(adj)
    allowed = []
    for mask in range(1, 1 << n):
        if _is_independent(mask, adj) or (homogeneous and _is_clique(mask, adj)):
            allowed.append(mask)
    return allowed


def brute_cover_number(adj: Sequence[int], homogeneous: bool) -> int:
    n = len(adj)
    allowed = brute_allowed_sets(adj, homogeneous)
    by_vertex = [tuple(s for s in allowed if (s >> v) & 1) for v in range(n)]

    @lru_cache(maxsize=None)
    def solve(uncovered: int) -> int:
        if uncovered == 0:
            return 0
        b = uncovered & -uncovered
        v = b.bit_length() - 1
        return 1 + min(solve(uncovered & ~s) for s in by_vertex[v])

    return solve((1 << n) - 1)


def brute_maximal_cliques(adj: Sequence[int]) -> set[int]:
    n = len(adj)
    all_vertices = (1 << n) - 1
    answer = set()
    for mask in range(1, 1 << n):
        if not _is_clique(mask, adj):
            continue
        outside = all_vertices & ~mask
        if all(not _is_clique(mask | (1 << v), adj) for v in range(n) if (outside >> v) & 1):
            answer.add(mask)
    return answer


def self_test(exhaustive_n: int) -> int:
    if not 0 <= exhaustive_n <= 6:
        raise ValueError("--exhaustive-n must be in 0..6 (5 is the practical default)")
    checked = 0
    started = time.perf_counter()

    # Include the order-zero boundary case once.
    empty_inv = exact_invariants(())
    assert (empty_inv.alpha, empty_inv.omega, empty_inv.chi, empty_inv.zeta) == (0, 0, 0, 0)

    for n in range(1, exhaustive_n + 1):
        graphs = 1 << (n * (n - 1) // 2)
        for code in range(graphs):
            adj = graph_from_code(n, code)
            inv = exact_invariants(adj)
            brute_chi = brute_cover_number(adj, homogeneous=False)
            brute_zeta = brute_cover_number(adj, homogeneous=True)
            brute_cliques = brute_maximal_cliques(adj)
            got_cliques = set(enumerate_maximal_cliques(adj)[0])
            brute_independent = brute_maximal_cliques(complement(adj))
            got_independent = set(enumerate_maximal_cliques(complement(adj))[0])
            if got_cliques != brute_cliques or got_independent != brute_independent:
                raise AssertionError(f"maximal-set enumeration mismatch at n={n}, code={code}")
            if inv.chi != brute_chi or inv.zeta != brute_zeta:
                raise AssertionError(
                    f"cover optimum mismatch at n={n}, code={code}: "
                    f"got ({inv.chi},{inv.zeta}), brute ({brute_chi},{brute_zeta})"
                )
            comp = exact_invariants(complement(adj))
            if inv.zeta != comp.zeta or inv.alpha != comp.omega or inv.omega != comp.alpha:
                raise AssertionError(f"complement symmetry mismatch at n={n}, code={code}")
            verify_partition(inv.chi_partition, adj)
            verify_partition(inv.zeta_partition, adj)
            checked += 1
    elapsed = time.perf_counter() - started
    print(
        f"SELF-TEST PASS: {checked} labelled graphs (all n=1..{exhaustive_n}) "
        f"plus n=0 in {elapsed:.3f}s",
        flush=True,
    )
    return checked


def parse_int_list(spec: str) -> list[int]:
    result: list[int] = []
    for token in spec.split(","):
        token = token.strip()
        if not token:
            continue
        if ":" in token:
            fields = [int(x) for x in token.split(":")]
            if len(fields) not in (2, 3):
                raise ValueError(f"invalid range {token!r}")
            start, stop = fields[:2]
            step = fields[2] if len(fields) == 3 else 1
            if step == 0:
                raise ValueError("range step cannot be zero")
            result.extend(range(start, stop + (1 if step > 0 else -1), step))
        else:
            result.append(int(token))
    return result


def run_samples(
    ns: Sequence[int],
    seeds: Sequence[int],
    *,
    timeout: float,
    check_complement: bool,
    output: Path,
) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    rows: list[dict[str, object]] = []
    for n in ns:
        if n < 2:
            raise ValueError("sample n must be at least 2")
        for seed in seeds:
            row = experiment_row(
                n,
                seed,
                timeout=timeout,
                check_complement=check_complement,
            )
            rows.append(row)
            print(
                f"n={n:2d} seed={seed:4d} status={row['status']:<7} "
                f"chi={str(row.get('chi', '-')):<2} zeta={str(row.get('zeta', '-')):<2} "
                f"gap={str(row.get('gap', '-')):<2} t={row['total_seconds']}s",
                flush=True,
            )

    with output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=CSV_FIELDS, extrasaction="ignore")
        writer.writeheader()
        for row in rows:
            writer.writerow(row)
    exact = sum(row["status"] == "exact" for row in rows)
    print(f"WROTE {output} ({exact}/{len(rows)} exact rows)", flush=True)
    if exact != len(rows):
        raise SystemExit(2)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true", help="run exhaustive validation")
    parser.add_argument(
        "--exhaustive-n",
        type=int,
        default=5,
        help="validate every labelled graph through this order (default: 5)",
    )
    parser.add_argument("--sample", action="store_true", help="run deterministic random samples")
    parser.add_argument(
        "--n",
        default="12,14,16,18,20,22,24,26,28",
        help="comma list; inclusive ranges use start:stop[:step]",
    )
    parser.add_argument("--seeds", default="0,1,2", help="comma list of integer seeds")
    parser.add_argument(
        "--timeout",
        type=float,
        default=120.0,
        help="wall-clock seconds per graph, including complement check; <=0 disables",
    )
    parser.add_argument(
        "--check-complement",
        action="store_true",
        help="independently solve the complement and assert zeta symmetry",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).with_name("EXACT_EXPERIMENTS.csv"),
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if not args.self_test and not args.sample:
        raise SystemExit("choose --self-test and/or --sample")
    if args.self_test:
        self_test(args.exhaustive_n)
    if args.sample:
        run_samples(
            parse_int_list(args.n),
            parse_int_list(args.seeds),
            timeout=args.timeout,
            check_complement=args.check_complement,
            output=args.output,
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
