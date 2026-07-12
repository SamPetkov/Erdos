"""Diagnostic scan of the exact four-type containment weight (4.11).

This is finite-n numerical evidence only.  It keeps the global falling
factorial exactly (through lgamma), so it can detect a dense off-diagonal
transport family that a product-of-one-cell approximation would miss.
"""

from __future__ import annotations

import math


Q = math.log(2.0)


def alpha0(n: int) -> float:
    l2 = math.log2(n)
    return 2 * l2 - 2 * math.log2(l2) + 2 * math.log2(math.e / 2) + 1


def finite_profile(n: int) -> tuple[int, list[int], list[int]]:
    """Return alpha, sizes alpha-2..alpha-5, and exact integer counts."""
    a0 = alpha0(n)
    alpha = math.floor(a0)
    delta = a0 - alpha
    target_t = 1 + 2 / Q - delta
    k0 = round(n / (alpha - target_t))

    feasible = []
    for k in range(k0 - 20, k0 + 21):
        deficit = alpha * k - n
        if 2 * k <= deficit <= 5 * k:
            feasible.append((abs(deficit / k - target_t), k, deficit))
    if not feasible:
        raise RuntimeError("no nearby feasible class count")
    _, k, deficit = min(feasible)
    mean = deficit / k

    lo, hi = -20.0, 20.0
    for _ in range(120):
        mu = (lo + hi) / 2
        weights = [math.exp(mu * i - Q * i * i / 2) for i in range(2, 6)]
        got = sum(i * w for i, w in zip(range(2, 6), weights)) / sum(weights)
        if got < mean:
            lo = mu
        else:
            hi = mu
    mu = (lo + hi) / 2
    weights = [math.exp(mu * i - Q * i * i / 2) for i in range(2, 6)]
    probs = [w / sum(weights) for w in weights]

    best = None
    centers = [round(k * p) for p in probs]
    for d0 in range(-12, 13):
        for d1 in range(-12, 13):
            c0 = centers[0] + d0
            c1 = centers[1] + d1
            rem_k = k - c0 - c1
            rem_d = deficit - 2 * c0 - 3 * c1
            c3 = rem_d - 4 * rem_k
            c2 = rem_k - c3
            counts = [c0, c1, c2, c3]
            if min(counts) < 0:
                continue
            err = sum((counts[i] - k * probs[i]) ** 2 for i in range(4))
            if best is None or err < best[0]:
                best = (err, counts)
    if best is None:
        raise RuntimeError("rounding failed")
    counts = best[1]
    sizes = [alpha - i for i in range(2, 6)]
    assert sum(counts) == k
    assert sum(c * s for c, s in zip(counts, sizes)) == n
    return alpha, sizes, counts


def log_g(x: int) -> float:
    return (x * (x - 1) / 2 - 1) * Q


def log_falling(x: int, r: int) -> float:
    if r < 0 or r > x:
        return float("-inf")
    return math.lgamma(x + 1) - math.lgamma(x - r + 1)


def log_signed_first_moment(n: int, sizes: list[int], counts: list[int]) -> float:
    k = sum(counts)
    energy = sum(c * s * (s - 1) / 2 for c, s in zip(counts, sizes))
    return (
        k * Q
        + math.lgamma(n + 1)
        - sum(c * math.lgamma(s + 1) for c, s in zip(counts, sizes))
        - sum(math.lgamma(c + 1) for c in counts)
        - Q * energy
    )


def log_transport_weight(
    n: int, sizes: list[int], counts: list[int], matrix: list[list[int]]
) -> float:
    rows = [sum(row) for row in matrix]
    cols = [sum(matrix[i][j] for i in range(4)) for j in range(4)]
    if any(rows[i] > counts[i] or cols[i] > counts[i] for i in range(4)):
        return float("-inf")
    total = sum(log_falling(counts[i], rows[i]) for i in range(4))
    total += sum(log_falling(counts[i], cols[i]) for i in range(4))
    total -= sum(math.lgamma(matrix[i][j] + 1) for i in range(4) for j in range(4))
    exposed = 0
    for i in range(4):
        for j in range(4):
            ell = matrix[i][j]
            x = min(sizes[i], sizes[j])
            exposed += ell * x
            local = (
                log_falling(sizes[i], x)
                + log_falling(sizes[j], x)
                - math.lgamma(x + 1)
                + log_g(x)
            )
            total += ell * local
    total -= log_falling(n, exposed)
    return total


def diagonal(counts: list[int], theta: float) -> list[list[int]]:
    out = [[0] * 4 for _ in range(4)]
    for i, count in enumerate(counts):
        out[i][i] = math.floor(theta * count)
    return out


def cycle_perturb(matrix: list[list[int]], i: int, j: int, moved: int) -> list[list[int]]:
    out = [row[:] for row in matrix]
    moved = min(moved, out[i][i], out[j][j])
    out[i][i] -= moved
    out[j][j] -= moved
    out[i][j] += moved
    out[j][i] += moved
    return out


def run(n: int) -> None:
    alpha, sizes, counts = finite_profile(n)
    log_z = log_signed_first_moment(n, sizes, counts)
    print(f"n={n} alpha={alpha} sizes={sizes} counts={counts}")
    print(f"log Z_signed={log_z:.6g};  (log Z)/(n/log n)={log_z/(n/math.log(n)):.6g}")
    for theta in (0.01, 0.1, 0.5, 0.9, 1.0):
        base = diagonal(counts, theta)
        log_w = log_transport_weight(n, sizes, counts, base)
        print(f"  theta={theta:>4}: diagonal log W={log_w:.6g}, /n={log_w/n:.6g}")
        for i, j in ((0, 1), (0, 3), (1, 2), (2, 3)):
            moved = max(1, min(base[i][i], base[j][j]) // 4)
            pert = cycle_perturb(base, i, j, moved)
            log_p = log_transport_weight(n, sizes, counts, pert)
            print(
                f"    swap {i}<->{j}, m={moved}: log ratio={log_p-log_w:.6g}"
            )
    print()


if __name__ == "__main__":
    for sample_n in (100_000, 1_000_000, 10_000_000):
        run(sample_n)
