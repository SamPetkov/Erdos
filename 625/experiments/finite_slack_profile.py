"""Checks for the finite largest-class calculation in FINITE_SLACK_PROFILE.md.

Only the Python standard library is used.  There are two kinds of output:

* an exact-vs-Euler--Maclaurin comparison at moderate n; and
* the normalized cycle-start asymptotics, which can be evaluated for very
  large N=log n without constructing n.

This is a deterministic asymptotic check, not a random-graph simulation.
"""

from __future__ import annotations

import math


Q = math.log(2.0)
C = 1.0 + math.log(Q) - Q
GAMMA = 2.0 - Q / 2.0


def alpha0(n: int) -> float:
    N = math.log(n)
    return 2.0 / Q * (N - math.log(N) + C) + 1.0


def log_mu(n: int, r: int) -> float:
    return (
        math.lgamma(n + 1)
        - math.lgamma(r + 1)
        - math.lgamma(n - r + 1)
        - Q * r * (r - 1) / 2.0
    )


def exact_log_disjoint(n: int, a: int, ell: int) -> float:
    """Log expected number of ell unordered, disjoint independent a-sets."""
    assert 0 <= a * ell <= n
    return (
        math.lgamma(n + 1)
        - math.lgamma(n - a * ell + 1)
        - ell * math.lgamma(a + 1)
        - math.lgamma(ell + 1)
        - Q * ell * a * (a - 1) / 2.0
    )


def expansion_log_disjoint(n: int, a: int, ell: int, x: float) -> float:
    """Expansion (7) of FINITE_SLACK_PROFILE.md, including 1/n terms."""
    N = math.log(n)
    d = a * ell / n
    assert 0.0 < d < 1.0
    log_mu_a = log_mu(n, a)
    B = log_mu_a - N + math.log(a) + 1.0 - a * Q * x / 2.0
    psi = -(1.0 - d) * math.log1p(-d) + d * (Q * x / 2.0 - 1.0)
    ans = n * psi + n * d / a * (B - math.log(d))
    ans += d * (a - 1) / 2.0
    ans -= 0.5 * math.log(1.0 - d)
    ans -= 0.5 * math.log(2.0 * math.pi * ell)
    ans += d * (a - 1) * (2 * a - 1) / (12.0 * n)
    ans -= 1.0 / (12.0 * ell)
    ans -= d / (12.0 * n * (1.0 - d))
    return ans


def solve_cap(x: float) -> float:
    """Positive root of psi_x(c)=0 (the limiting cap)."""
    if x <= 0.0:
        return 0.0

    def psi(c: float) -> float:
        return -(1.0 - c) * math.log1p(-c) + c * (Q * x / 2.0 - 1.0)

    lo, hi = 0.0, min(0.25, 2.0 * Q * x)
    while psi(hi) > 0.0:
        hi *= 1.5
    for _ in range(100):
        mid = (lo + hi) / 2.0
        if psi(mid) > 0.0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2.0


def residual_constants() -> tuple[float, float, float]:
    """mu_0, Z_0, and the additive constant in Lambda(c)."""
    target = 1.0 + 2.0 / Q

    def moments(mu: float) -> tuple[float, float]:
        weights = [math.exp(mu * i - Q * i * i / 2.0) for i in range(2, 100)]
        Z = math.fsum(weights)
        mean = math.fsum(i * w for i, w in zip(range(2, 100), weights)) / Z
        return mean, Z

    lo, hi = 2.5, 2.8
    for _ in range(100):
        mid = (lo + hi) / 2.0
        if moments(mid)[0] < target:
            lo = mid
        else:
            hi = mid
    mu = (lo + hi) / 2.0
    _, Z = moments(mu)
    kappa = mu - Q / 2.0 - math.log(Z)
    return mu, Z, kappa


def moderate_n_checks() -> None:
    print("exact-vs-expansion checks (d approximately 0.01)")
    print("n          a      exact log E       expansion       difference")
    for n in (10_000, 1_000_000, 100_000_000):
        alpha = math.floor(alpha0(n))
        a = alpha - 1
        ell = max(1, round(0.01 * n / a))
        x = log_mu(n, alpha) / math.log(n)
        exact = exact_log_disjoint(n, a, ell)
        approx = expansion_log_disjoint(n, a, ell, x)
        print(f"{n:<10d} {a:<5d} {exact:16.6f} {approx:16.6f} {exact-approx:12.4g}")


def cycle_start_checks() -> None:
    mu0, Z0, kappa = residual_constants()
    print("\nconstants")
    print(f"q=ln 2                         {Q:.15f}")
    print(f"gamma=2-q/2                   {GAMMA:.15f}")
    print(f"2C+2log(2/q)+1 (equals 3)     {2*C+2*math.log(2/Q)+1:.15f}")
    print(f"residual mu_0                 {mu0:.15f}")
    print(f"residual Z_0                  {Z0:.15f}")
    print(f"kappa_0=mu_0-q/2-log Z_0      {kappa:.15f}")
    print(f"ordinary finite-cap ratio     {1+Q/GAMMA:.15f}")
    print(f"signed bonus coefficient q^2/2 {Q*Q/2:.15f}")

    print("\ncycle-start normalized scales")
    print("N=log n    w=log N  c~gamma*w/N  cap logE/(n*w^2/N^2)  loss(rho=1/N)/(n*w/N^2)")
    for N in (1e3, 1e4, 1e5, 1e6):
        w = math.log(N)
        # The leading two displayed normalizations from the note.
        c = GAMMA * w / N
        cap_norm = Q * GAMMA / 2.0
        lam = -math.log(c) + kappa
        loss_norm = Q * lam / (2.0 * w)
        print(f"{N:8.0f} {w:10.6f} {c:14.6g} {cap_norm:23.12f} {loss_norm:29.12f}")


if __name__ == "__main__":
    moderate_n_checks()
    cycle_start_checks()
