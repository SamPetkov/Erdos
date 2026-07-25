#!/usr/bin/env python3
"""Finite regression checks for the simplified Sections 8--9 route.

The exact gates use only the Python standard library and remain active under
``python -O``. Floating-point phase scans are diagnostics and are labelled as
such; they are not used to certify an asymptotic theorem.

The primary high-deficit gate follows the formalization-first exponent budget
``floor(2m/3)`` used in Lean.  The earlier sharper ``floor((3m-1)/4)`` bound is
also checked separately as a diagnostic, but it is not needed by the proposed
replacement proof.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb, e, lgamma, log, log2


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def denominator_product(d: int, deficit: int) -> int:
    result = 1
    for t in range(1, deficit + 1):
        result *= d + t
    return result


def local_ratio_with_global_charge(n: int, m: int, d: int, deficit: int) -> Fraction:
    exponent = deficit * m - deficit * (deficit + 1) // 2
    return Fraction(
        (n**deficit) * comb(m, deficit),
        denominator_product(d, deficit) * (2**exponent),
    )


def exact_high_deficit_checks() -> tuple[int, int, int]:
    """Check the formal two-thirds domination and the optional sharper budget."""

    formal_exponent_cases = 0
    sharper_exponent_cases = 0
    ratio_cases = 0

    for m in range(2, 601):
        b_formal = (2 * m) // 3
        b_sharp = (3 * m - 1) // 4
        for deficit in range(1, m):
            if 2 * deficit >= m:
                continue

            exponent = deficit * m - deficit * (deficit + 1) // 2
            require(
                exponent >= deficit * b_formal,
                f"formal exponent budget failed: m={m}, e={deficit}",
            )
            require(
                comb(m, deficit) <= m**deficit,
                f"choose bound failed: m={m}, e={deficit}",
            )
            formal_exponent_cases += 1

            # The stronger budget is retained as an independent diagnostic.
            require(
                exponent >= deficit * b_sharp,
                f"sharper exponent budget failed: m={m}, e={deficit}",
            )
            sharper_exponent_cases += 1

            # Exact Fraction checks on a representative range.  The preceding
            # componentwise inequalities prove the formal comparison generally;
            # these cases guard the implemented formula and integer floors.
            if m <= 120:
                for d in range(4):
                    for n in (2, 3, 10, 97, 10_000):
                        lhs = local_ratio_with_global_charge(n, m, d, deficit)
                        rho_formal = Fraction(n * m, 2**b_formal)
                        require(
                            lhs <= rho_formal**deficit,
                            f"formal local geometric bound failed: n={n}, m={m}, "
                            f"d={d}, e={deficit}",
                        )
                        ratio_cases += 1

    return formal_exponent_cases, sharper_exponent_cases, ratio_cases


def exact_amgm_checks() -> int:
    """Check the square-free form of termwise AM--GM: 4xy <= (x+y)^2."""

    cases = 0
    rationals = [Fraction(a, b) for b in range(1, 13) for a in range(0, 25)]
    for x in rationals:
        for y in rationals:
            require(4 * x * y <= (x + y) ** 2, f"AM-GM failed: x={x}, y={y}")
            cases += 1
    return cases


def exact_q_absorption_checks() -> int:
    """Check lambda <= q and the corresponding product domination exactly."""

    cases = 0
    values = [Fraction(a, b) for b in range(1, 11) for a in range(0, 21)]
    for lam in values:
        for theta in values:
            q = theta * theta / 2 + lam
            require(lam <= q, f"lambda <= q failed: lambda={lam}, theta={theta}")
            require(
                (1 + lam) * (1 + q) <= (1 + q) ** 2,
                f"product absorption failed: lambda={lam}, q={q}",
            )
            cases += 1
    return cases


def alpha_zero(n: int) -> float:
    ell = log2(n)
    return 2 * ell - 2 * log2(ell) + 2 * log2(e / 2) + 1


def log2_local_ratio(n: int, m: int, d: int, deficit: int) -> float:
    exponent = deficit * m - deficit * (deficit + 1) / 2
    return (
        deficit * log2(n)
        + (lgamma(m + 1) - lgamma(deficit + 1) - lgamma(m - deficit + 1)) / log(2)
        - (lgamma(d + deficit + 1) - lgamma(d + 1)) / log(2)
        - exponent
    )


def log2_sum(values: list[float]) -> float:
    maximum = max(values)
    return maximum + log2(sum(2 ** (value - maximum) for value in values))


def phase_diagnostics() -> list[str]:
    lines: list[str] = []
    for power in (10, 20, 50, 100, 200):
        n = 10**power
        alpha = int(alpha_zero(n))
        largest_size = alpha - 2
        cutoff = largest_size // 2

        # Uniform formal base over endpoint sizes m in [U-3,U].
        b_formal_star = 2 * (largest_size - 3) // 3
        log2_rho_formal = log2(n) + log2(largest_size) - b_formal_star

        # Retain the sharper earlier diagnostic for comparison only.
        b_sharp_star = (3 * largest_size - 10) // 4
        log2_rho_sharp = log2(n) + log2(largest_size) - b_sharp_star

        worst_log_sum = float("-inf")
        worst_type: tuple[int, int] | None = None
        for i in range(4):
            for j in range(4):
                m = min(largest_size - i, largest_size - j)
                d = abs(i - j)
                max_deficit = m - (cutoff + 1)
                if max_deficit < 1:
                    continue
                terms = [
                    log2_local_ratio(n, m, d, deficit)
                    for deficit in range(1, max_deficit + 1)
                ]
                value = log2_sum(terms)
                if value > worst_log_sum:
                    worst_log_sum = value
                    worst_type = (i, j)

        if log2_rho_formal < 0:
            rho_formal = 2**log2_rho_formal
            log2_formal_majorant = log2(rho_formal / (1 - rho_formal))
            require(
                worst_log_sum <= log2_formal_majorant + 1e-9,
                f"phase diagnostic exceeds formal geometric majorant at 10^{power}",
            )
            formal_text = f"log2 formal majorant={log2_formal_majorant:.6f}"
        else:
            formal_text = "formal rho >= 1 (pre-asymptotic only)"

        lines.append(
            f"  n=10^{power}: U={largest_size}, worst type={worst_type}, "
            f"log2 full-deficit sum={worst_log_sum:.6f}, "
            f"log2 formal rho={log2_rho_formal:.6f}, {formal_text}, "
            f"log2 sharper rho={log2_rho_sharp:.6f}"
        )
    return lines


def main() -> None:
    formal_cases, sharper_cases, ratio_cases = exact_high_deficit_checks()
    amgm_cases = exact_amgm_checks()
    q_cases = exact_q_absorption_checks()
    diagnostics = phase_diagnostics()

    print("ERDOS 625 SECTIONS 8--9 SIMPLIFICATION CHECK: PASS")
    print(f"  formal two-thirds exponent cases: {formal_cases}")
    print(f"  sharper three-quarters diagnostic cases: {sharper_cases}")
    print(f"  exact formal local-ratio cases: {ratio_cases}")
    print(f"  exact AM-GM cases: {amgm_cases}")
    print(f"  exact q-absorption cases: {q_cases}")
    print("  phase diagnostics:")
    for line in diagnostics:
        print(line)


if __name__ == "__main__":
    main()
