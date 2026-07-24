#!/usr/bin/env python3
"""Exact and diagnostic checks for Erdős 625 root-gap constant propagation.

Exact checks:
  * midpoint and general-theta floor/ceiling inequalities on a rational grid;
  * the factor-four coefficient arithmetic;
  * canonical equation-tag presence when run from the repository root.

Diagnostics, explicitly not proofs:
  * a numerical scan of the limiting four-support advantage A(delta);
  * the finite-n size of the additive rounding loss relative to n/(log n)^3.
"""
from __future__ import annotations

from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path
import math


def require(condition: bool, message: str) -> None:
    """Raise even under ``python -O`` when a verification condition fails."""
    if not condition:
        raise RuntimeError(message)


def floor_fraction(x: Fraction) -> int:
    return x.numerator // x.denominator


def ceil_fraction(x: Fraction) -> int:
    return -((-x.numerator) // x.denominator)


def rounding_grid() -> tuple[int, Fraction, tuple[Fraction, ...]]:
    """Check midpoint/general-theta inequalities on a structured exact grid."""
    fracs = tuple(Fraction(k, 12) for k in range(12))
    thetas = (Fraction(1, 2), Fraction(1, 4), Fraction(1, 10), Fraction(3, 4))
    checked = 0
    worst_deficit = Fraction(-10)
    worst_case: tuple[Fraction, ...] = ()

    for integer_gap in range(1, 9):
        for fx in fracs:
            for fy in fracs:
                x = Fraction(20 + integer_gap) + fx
                y = Fraction(20) + fy
                if x <= y:
                    continue
                gap = x - y
                for fn in fracs:
                    nlog = Fraction(7) + fn
                    k_chi = floor_fraction(x) - ceil_fraction(nlog)
                    for theta in thetas:
                        k_theta = ceil_fraction(y + theta * gap)
                        lhs = k_chi - k_theta
                        main = (1 - theta) * gap - nlog
                        require(
                            lhs > main - 3,
                            "rounding inequality failed: "
                            f"x={x}, y={y}, N={nlog}, theta={theta}",
                        )
                        deficit = main - lhs
                        if deficit > worst_deficit:
                            worst_deficit = deficit
                            worst_case = (
                                x,
                                y,
                                nlog,
                                theta,
                                Fraction(lhs),
                                main,
                            )
                        checked += 1
    return checked, worst_deficit, worst_case


def coefficient_arithmetic() -> tuple[Decimal, Decimal, Decimal]:
    """Check the exact factor four between the displayed coefficients."""
    getcontext().prec = 60
    q = Decimal(2).ln()
    gamma = (Decimal(200) / Decimal(153)).ln()
    old = q * q * gamma / Decimal(32)
    propagated = q * q * gamma / Decimal(8)
    require(
        propagated == Decimal(4) * old,
        "factor-four coefficient identity failed",
    )
    return old, propagated, gamma


def limiting_value(support: tuple[int, ...], target: float) -> tuple[float, float]:
    """Numerically evaluate the limiting constrained entropy value."""
    q = math.log(2.0)
    lo, hi = -20.0, 20.0
    for _ in range(90):
        lam = (lo + hi) / 2.0
        weights = [math.exp(lam * i - q * i * i / 2.0) for i in support]
        mean = sum(i * w for i, w in zip(support, weights)) / sum(weights)
        if mean < target:
            lo = lam
        else:
            hi = lam
    lam = (lo + hi) / 2.0
    weights = [math.exp(lam * i - q * i * i / 2.0) for i in support]
    partition = sum(weights)
    value = math.log(partition) - lam * target
    return lam, value


def phase_scan(points: int = 1001) -> tuple[float, float, float]:
    """Diagnostic scan of A(delta)=log(2)-(F_plus-F_4)."""
    q = math.log(2.0)
    support4 = (2, 3, 4, 5)
    support_plus_60 = tuple(range(-1, 60))
    support_plus_90 = tuple(range(-1, 90))
    best = (float("inf"), 0.0)
    truncation_disagreement = 0.0

    for k in range(points):
        delta = k / (points - 1)
        target = 1.0 + 2.0 / q - delta
        _, value4 = limiting_value(support4, target)
        _, value_plus_60 = limiting_value(support_plus_60, target)
        _, value_plus_90 = limiting_value(support_plus_90, target)
        truncation_disagreement = max(
            truncation_disagreement,
            abs(value_plus_60 - value_plus_90),
        )
        advantage = q - (value_plus_90 - value4)
        if advantage < best[0]:
            best = (advantage, delta)

    return best[0], best[1], truncation_disagreement


def rounding_scale_table() -> list[tuple[int, Decimal]]:
    """Diagnostic values of (N+3)N^3/n for widely separated n."""
    getcontext().prec = 80
    out: list[tuple[int, Decimal]] = []
    for exponent in (6, 12, 24, 48, 96, 192):
        n = Decimal(10) ** exponent
        log_n = n.ln()
        ratio = (log_n + 3) * log_n**3 / n
        out.append((exponent, ratio))
    return out


def source_tag_check() -> str:
    """Guard the canonical equations on which the review note depends."""
    path = Path("625/proofs/COMPLETE_PROOF_SELF_CONTAINED.md")
    if not path.exists():
        return "SKIPPED (canonical source not present in working directory)"
    text = path.read_text(encoding="utf-8")
    for tag in ("\\tag{5.11}", "\\tag{5.13}", "\\tag{10.13}", "\\tag{11.1}"):
        require(tag in text, f"missing canonical equation tag {tag}")
    return "PASS"


def main() -> None:
    checked, worst_deficit, worst_case = rounding_grid()
    old, propagated, gamma = coefficient_arithmetic()
    min_advantage, min_delta, truncation_error = phase_scan()
    source_status = source_tag_check()

    print("ERDOS 625 ROOT-GAP CONSTANT SUPERCHECK: PASS")
    print(f"  exact rounding cases: {checked}")
    print(
        "  largest observed additive rounding deficit: "
        f"{float(worst_deficit):.12f} (< 3)"
    )
    print(f"  worst grid case: {worst_case}")
    print(f"  current displayed coefficient: {old}")
    print(f"  factor-four propagated coefficient: {propagated}")
    print(f"  manuscript gamma: {gamma}")
    print(f"  canonical equation-tag scan: {source_status}")
    print("DIAGNOSTIC ONLY:")
    print(
        f"  scanned min A(delta): {min_advantage:.12f} "
        f"at delta={min_delta:.6f}"
    )
    print(
        "  corresponding q^2*A/8: "
        f"{math.log(2.0) ** 2 * min_advantage / 8.0:.12f}"
    )
    print(
        "  S_plus truncation disagreement (60 vs 90): "
        f"{truncation_error:.3e}"
    )
    for exponent, ratio in rounding_scale_table():
        print(f"  n=10^{exponent}: (N+3)N^3/n = {ratio:.6E}")


if __name__ == "__main__":
    main()
