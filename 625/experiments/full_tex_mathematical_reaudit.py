#!/usr/bin/env python3
"""Exact and high-precision checks for the full Erdős 625 TeX re-audit.

The script checks deterministic arithmetic used by the audit.  It does not
prove the random-graph theorem, the Section VIII physical-fibre equivalence,
or any conjectural theorem upgrade.
"""

from __future__ import annotations

from decimal import Decimal, getcontext
from fractions import Fraction
from math import comb, factorial
from pathlib import Path


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def decimal_close(left: Decimal, right: Decimal) -> bool:
    """Relative comparison at a scale well below the 80-digit work precision."""

    scale = max(Decimal(1), abs(left), abs(right))
    return abs(left - right) <= Decimal("1e-70") * scale


def falling(n: int, k: int) -> int:
    require(0 <= k <= n, f"invalid falling factorial ({n})_{k}")
    value = 1
    for offset in range(k):
        value *= n - offset
    return value


def floor_fraction(value: Fraction) -> int:
    return value.numerator // value.denominator


def ceil_fraction(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def signed_local_reward(j: int) -> int:
    if j <= 2:
        return 1
    return 2 ** (comb(j, 2) - 1)


def aggregate_local_weight(m: int, d: int, j: int) -> Fraction:
    return Fraction(
        falling(m, j) * falling(m + d, j) * signed_local_reward(j),
        factorial(j),
    )


def aggregate_ratio_formula(m: int, d: int, h: int) -> Fraction:
    denominator = 1
    for offset in range(1, h + 1):
        denominator *= d + offset
    exponent = h * m - h * (h + 1) // 2
    return Fraction(comb(m, h), denominator * 2**exponent)


def check_coefficient_ledger() -> dict[str, Decimal]:
    getcontext().prec = 80
    q = Decimal(2).ln()

    canonical = q * q * (Decimal(200) / Decimal(153)).ln() / Decimal(32)
    old_certificate_midpoint = (
        q * q * (Decimal(200) / Decimal(153)).ln() / Decimal(8)
    )
    strong_midpoint = q * q * (Decimal(1000) / Decimal(639)).ln() / Decimal(8)
    strong_near_root = q * q * (Decimal(1000) / Decimal(639)).ln() / Decimal(4)
    full_support_near_root = q**3 / Decimal(4)

    require(
        decimal_close(old_certificate_midpoint, 4 * canonical),
        "factor-four ledger failed",
    )
    require(
        decimal_close(strong_near_root, 2 * strong_midpoint),
        "near-root factor-two failed",
    )
    require(
        full_support_near_root > strong_near_root > strong_midpoint > canonical > 0,
        "coefficient ordering failed",
    )

    diagnostic_advantage = Decimal("0.520701335491")
    diagnostic_midpoint = q * q * diagnostic_advantage / Decimal(8)
    diagnostic_near_root = q * q * diagnostic_advantage / Decimal(4)
    require(
        decimal_close(diagnostic_near_root, 2 * diagnostic_midpoint),
        "diagnostic ratio failed",
    )

    return {
        "canonical": canonical,
        "old_certificate_midpoint": old_certificate_midpoint,
        "strong_midpoint": strong_midpoint,
        "strong_near_root": strong_near_root,
        "full_support_near_root": full_support_near_root,
        "strong_midpoint_over_canonical": strong_midpoint / canonical,
        "diagnostic_midpoint": diagnostic_midpoint,
        "diagnostic_near_root": diagnostic_near_root,
    }


def check_midpoint_rounding() -> int:
    checked = 0
    values = [Fraction(i, 12) for i in range(-24, 73)]
    losses = [Fraction(i, 12) for i in range(0, 49)]
    for x in values:
        for y in values:
            if x <= y:
                continue
            for loss in losses:
                lhs = (
                    floor_fraction(x)
                    - ceil_fraction(loss)
                    - ceil_fraction((x + y) / 2)
                )
                rhs = (x - y) / 2 - loss - 3
                require(Fraction(lhs) > rhs, "midpoint rounding inequality failed")
                checked += 1
    return checked


def check_aggregate_local_ratio(max_m: int = 90) -> int:
    checked = 0
    for m in range(5, max_m + 1):
        for d in range(4):
            for h in range(0, m):
                if 2 * h >= m:
                    continue
                j = m - h
                require(j >= 3, "tested high multiplicity fell below reward range")
                actual = aggregate_local_weight(m, d, j) / aggregate_local_weight(m, d, m)
                formula = aggregate_ratio_formula(m, d, h)
                require(actual == formula, f"aggregate local ratio failed: m={m}, d={d}, h={h}")
                checked += 1
    return checked


def check_global_denominator(max_n: int = 120) -> int:
    checked = 0
    for n in range(max_n + 1):
        for j in range(n + 1):
            for h in range(n - j + 1):
                ratio = Fraction(falling(n, j + h), falling(n, j))
                require(ratio == falling(n - j, h), "global denominator identity failed")
                require(ratio <= n**h, "global denominator upper bound failed")
                checked += 1
    return checked


def check_two_thirds_budget(max_m: int = 1200) -> int:
    checked = 0
    for m in range(1, max_m + 1):
        for h in range(1, m + 1):
            if 2 * h >= m:
                continue
            lhs = h * ((2 * m) // 3)
            rhs = h * m - h * (h + 1) // 2
            require(lhs <= rhs, f"two-thirds budget failed: m={m}, h={h}")
            checked += 1
    return checked


def check_geometric_fibre() -> int:
    checked = 0
    for denominator in range(2, 101):
        for numerator in range(1, denominator // 2 + 1):
            rho = Fraction(numerator, denominator)
            for cutoff in range(1, 50):
                finite_sum = sum((rho**h for h in range(1, cutoff + 1)), Fraction())
                require(finite_sum <= rho / (1 - rho), "geometric majorant failed")
                require(finite_sum <= 2 * rho, "two-rho majorant failed")
                checked += 1
    return checked


def check_binary_entropy_penalty() -> list[tuple[Decimal, Decimal]]:
    getcontext().prec = 80
    q = Decimal(2).ln()
    rows: list[tuple[Decimal, Decimal]] = []
    previous: Decimal | None = None
    for integer in range(1, 10):
        x = Decimal(integer) / Decimal(20)
        rho = Decimal("0.5") + x
        entropy = -(rho * rho.ln() + (1 - rho) * (1 - rho).ln())
        penalty = q - entropy
        require(penalty > 0, "binary entropy penalty is not positive")
        if previous is not None:
            require(penalty > previous, "binary entropy penalty is not increasing")
        previous = penalty
        rows.append((x, penalty))
    return rows


def check_asymptotic_scales() -> list[tuple[int, Decimal, Decimal, Decimal]]:
    """Check logarithms of the relevant ratios to n/(log n)^4."""

    getcontext().prec = 80
    rows: list[tuple[int, Decimal, Decimal, Decimal]] = []
    previous_all_high: Decimal | None = None
    previous_transport: Decimal | None = None
    previous_theta_margin: Decimal | None = None

    for nlog in (120, 240, 480, 960, 1920):
        N = Decimal(nlog)
        # n^(2/3) N^(4/3) divided by n/N^4.
        log_all_high = -N / 3 + (Decimal(16) / 3) * N.ln()
        # sqrt(nN) divided by n/N^4.
        log_transport = -N / 2 + (Decimal(9) / 2) * N.ln()
        # theta=N^(-1/2): (theta*n/N) / N, comparing the seed log-margin
        # with a conservative O(N) logarithmic error.
        log_theta_margin = N - (Decimal(5) / 2) * N.ln()

        if previous_all_high is not None:
            require(log_all_high < previous_all_high, "all-high ratio is not decreasing")
            require(log_transport < previous_transport, "transport ratio is not decreasing")
            require(
                log_theta_margin > previous_theta_margin,
                "candidate near-root seed margin is not increasing",
            )
        previous_all_high = log_all_high
        previous_transport = log_transport
        previous_theta_margin = log_theta_margin
        rows.append((nlog, log_all_high, log_transport, log_theta_margin))

    require(rows[-1][1] < -100, "all-high error is not strongly subcritical")
    require(rows[-1][2] < -100, "endpoint transport error is not strongly subcritical")
    require(rows[-1][3] > 100, "candidate near-root margin is not strongly supercritical")
    return rows


def check_slow_support_warning() -> tuple[Decimal, Decimal]:
    """Demonstrate why K=o(N) is insufficient if Lambda=K*n/N^4."""

    getcontext().prec = 80
    N = Decimal(10_000)
    K = N.sqrt()
    require(K / N < Decimal("0.02"), "chosen K is not visibly o(N) at the test point")
    target_ratio = K  # (K*n/N^4)/(n/N^4)
    require(target_ratio > 1, "counterexample to the proposed complexity criterion failed")
    return K / N, target_ratio


def scan_canonical_tex() -> dict[str, bool]:
    path = Path(__file__).resolve().parents[1] / "arxiv" / "main.tex"
    if not path.is_file():
        return {"available": False}
    text = path.read_text(encoding="utf-8")
    return {
        "available": True,
        "old_coefficient": r"\frac{(\ln 2)^2}{32}" in text,
        "old_entropy_certificate": r"\ln\frac{200}{153}" in text,
        "near_middle_split": "canonical near--middle split" in text,
        "cycle_kernel": "Cycle-kernel estimate" in text,
        "partial_diagonal_exponent_typo": r"2^\ell_\bullet" in text,
    }


def main() -> None:
    coefficients = check_coefficient_ledger()
    rounding_cases = check_midpoint_rounding()
    local_ratio_cases = check_aggregate_local_ratio()
    denominator_cases = check_global_denominator()
    budget_cases = check_two_thirds_budget()
    geometric_cases = check_geometric_fibre()
    entropy_rows = check_binary_entropy_penalty()
    scale_rows = check_asymptotic_scales()
    slow_support_ratio, slow_support_target = check_slow_support_warning()
    tex_scan = scan_canonical_tex()

    print("ERDOS 625 FULL TEX MATHEMATICAL RE-AUDIT: PASS")
    print("  coefficient ledger:")
    for name, value in coefficients.items():
        print(f"    {name}: {value}")
    print(f"  midpoint rounding cases: {rounding_cases}")
    print(f"  exact aggregate local-ratio cases: {local_ratio_cases}")
    print(f"  global falling-factorial cases: {denominator_cases}")
    print(f"  two-thirds exponent cases: {budget_cases}")
    print(f"  geometric-fibre cases: {geometric_cases}")
    print("  binary-entropy penalties (x, log2-H(1/2+x)):")
    for x, penalty in entropy_rows:
        print(f"    {x}: {penalty}")
    print("  asymptotic log-ratios (N, all-high/target, transport/target, theta seed/O(N)):")
    for row in scale_rows:
        print(f"    {row[0]}: {row[1]}, {row[2]}, {row[3]}")
    print("  slow-support criterion diagnostic:")
    print(f"    K/N at N=10000: {slow_support_ratio}")
    print(f"    (K*n/N^4)/(n/N^4): {slow_support_target}")
    print("  canonical TeX audit markers:")
    for name, value in tex_scan.items():
        print(f"    {name}: {value}")
    print("  scope: deterministic arithmetic and source-marker audit only")


if __name__ == "__main__":
    main()
