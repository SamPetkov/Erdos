#!/usr/bin/env python3
"""Numerical support-frontier scan for the Erdős 625 signed profile.

This is a diagnostic experiment, not a proof.  It scans finite deficit supports
that contain {2,3}, evaluates the limiting entropy advantage over the complete
phase interval, and compares the canonical four-size profile with nearby
alternatives.

The full-support value is approximated twice, with cutoffs 80 and 100.  The
reported truncation disagreement is a numerical stability check.
"""
from __future__ import annotations

import argparse
import itertools
import math
from dataclasses import dataclass


def require(condition: bool, message: str) -> None:
    """Raise even under ``python -O`` when a diagnostic gate fails."""
    if not condition:
        raise RuntimeError(message)


@dataclass(frozen=True)
class ScanResult:
    support: tuple[int, ...]
    minimum_advantage: float
    target_at_minimum: float


def constrained_value(support: tuple[int, ...], target: float) -> float:
    """Return ``log Z(lambda)-lambda*target`` at the mean-matching tilt."""
    q = math.log(2.0)
    lo, hi = -40.0, 40.0

    for _ in range(90):
        lam = (lo + hi) / 2.0
        scores = [lam * i - q * i * i / 2.0 for i in support]
        shift = max(scores)
        weights = [math.exp(score - shift) for score in scores]
        total = math.fsum(weights)
        mean = math.fsum(i * w for i, w in zip(support, weights)) / total
        if mean < target:
            lo = lam
        else:
            hi = lam

    lam = (lo + hi) / 2.0
    scores = [lam * i - q * i * i / 2.0 for i in support]
    shift = max(scores)
    log_partition = shift + math.log(
        math.fsum(math.exp(score - shift) for score in scores)
    )
    return log_partition - lam * target


def scan_support(
    support: tuple[int, ...],
    targets: tuple[float, ...],
    full_values: tuple[float, ...],
) -> ScanResult:
    q = math.log(2.0)
    best_advantage = float("inf")
    best_target = targets[0]
    for target, full_value in zip(targets, full_values):
        finite_value = constrained_value(support, target)
        advantage = q - (full_value - finite_value)
        if advantage < best_advantage:
            best_advantage = advantage
            best_target = target
    return ScanResult(support, best_advantage, best_target)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--grid", type=int, default=1001)
    parser.add_argument("--max-deficit", type=int, default=8)
    parser.add_argument("--max-size", type=int, default=5)
    args = parser.parse_args()

    require(args.grid >= 2, "--grid must be at least 2")
    require(args.max_deficit >= 5, "--max-deficit must be at least 5")
    require(args.max_size >= 3, "--max-size must be at least 3")

    q = math.log(2.0)
    target_lo = 2.0 / q
    target_hi = 1.0 + 2.0 / q
    targets = tuple(
        target_lo + (target_hi - target_lo) * step / (args.grid - 1)
        for step in range(args.grid)
    )

    full_80 = tuple(range(-1, 80))
    full_100 = tuple(range(-1, 100))
    values_80 = tuple(constrained_value(full_80, target) for target in targets)
    values_100 = tuple(constrained_value(full_100, target) for target in targets)
    truncation_disagreement = max(abs(x - y) for x, y in zip(values_80, values_100))
    require(truncation_disagreement < 1e-12, "full-support truncation check failed")

    universe = tuple(range(2, args.max_deficit + 1))
    results: list[ScanResult] = []
    for size in range(3, min(args.max_size, len(universe)) + 1):
        for support in itertools.combinations(universe, size):
            if 2 not in support or 3 not in support:
                continue
            if support[0] > target_lo or support[-1] < target_hi:
                continue
            results.append(scan_support(support, targets, values_100))

    results.sort(key=lambda item: item.minimum_advantage, reverse=True)
    by_support = {item.support: item for item in results}

    expected = {
        (2, 3, 4, 5, 6): 0.525994631053,
        (2, 3, 4, 5): 0.520701335491,
        (2, 3, 4, 6, 7): 0.399733765460,
        (2, 3, 5): 0.092144964328,
    }
    for support, reference in expected.items():
        result = by_support.get(support)
        require(result is not None, f"expected support missing: {support}")
        require(
            abs(result.minimum_advantage - reference) < 2e-9,
            f"support regression changed for {support}: "
            f"{result.minimum_advantage} vs {reference}",
        )

    print("ERDOS 625 SUPPORT FRONTIER SCAN: PASS")
    print("DIAGNOSTIC ONLY — numerical limiting-profile experiment")
    print(f"  grid points: {args.grid}")
    print(f"  supports scanned: {len(results)}")
    print(f"  full-support truncation disagreement: {truncation_disagreement:.3e}")
    print()
    print("rank  support           min(q-D_S)       target at minimum")
    for rank, item in enumerate(results[:15], start=1):
        print(
            f"{rank:>4}  {str(item.support):<17} "
            f"{item.minimum_advantage: .12f}  {item.target_at_minimum:.12f}"
        )

    canonical = by_support[(2, 3, 4, 5)].minimum_advantage
    five_size = by_support[(2, 3, 4, 5, 6)].minimum_advantage
    relative_gain = (five_size / canonical - 1.0) * 100.0
    print()
    print(f"canonical S4 minimum: {canonical:.12f}")
    print(f"S4 plus deficit 6:   {five_size:.12f}")
    print(f"relative numerical gain: {relative_gain:.3f}%")
    print(
        "Interpretation: adding deficit 6 gives only a small limiting advantage "
        "while increasing the transportation dimension from 4x4 to 5x5."
    )


if __name__ == "__main__":
    main()
