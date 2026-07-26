#!/usr/bin/env python3
"""Numerical regression ledger for the Erdős 625 value-upgrade program.

The script uses only Python's standard library.  It verifies the deterministic
coefficient propagation formulas recorded in the research note and prints
quantitative diagnostics for near-root placement and sign-balance penalties.

It does not prove the four-support entropy certificate, the phase minimum, the
normalized second moment, or any random-graph theorem.  Those are mathematical
inputs or explicitly labelled research targets.
"""

from __future__ import annotations

from decimal import Decimal, getcontext


getcontext().prec = 90


D = Decimal


def require(condition: bool, message: str) -> None:
    """Raise an explicit error; unlike assert, this remains active under -O."""

    if not condition:
        raise RuntimeError(message)


def binary_entropy(rho: Decimal) -> Decimal:
    """Natural-log binary entropy on the open unit interval."""

    require(D(0) < rho < D(1), f"rho must lie in (0,1), got {rho}")
    return -(rho * rho.ln() + (D(1) - rho) * (D(1) - rho).ln())


def coefficient_ledger() -> dict[str, Decimal]:
    q = D(2).ln()

    canonical = q * q * (D(200) / D(153)).ln() / D(32)
    factor_four_old_entropy = q * q * (D(200) / D(153)).ln() / D(8)
    stronger_entropy_old_propagation = q * q * (D(1000) / D(639)).ln() / D(32)
    certified_midpoint = q * q * (D(1000) / D(639)).ln() / D(8)
    certified_near_root = q * q * (D(1000) / D(639)).ln() / D(4)

    full_support_midpoint = q**3 / D(8)
    full_support_near_root = q**3 / D(4)

    diagnostic_advantage = D("0.520701335491")
    diagnostic_midpoint = q * q * diagnostic_advantage / D(8)
    diagnostic_near_root = q * q * diagnostic_advantage / D(4)

    require(
        factor_four_old_entropy == canonical * D(4),
        "factor-four propagation identity failed",
    )
    require(
        certified_midpoint == stronger_entropy_old_propagation * D(4),
        "stronger-entropy factor-four identity failed",
    )
    require(
        certified_near_root == certified_midpoint * D(2),
        "near-root/midpoint factor-two identity failed",
    )
    require(
        full_support_near_root == full_support_midpoint * D(2),
        "full-support near-root/midpoint identity failed",
    )
    require(
        full_support_near_root
        > diagnostic_near_root
        > certified_near_root
        > full_support_midpoint
        > diagnostic_midpoint
        > certified_midpoint
        > factor_four_old_entropy
        > stronger_entropy_old_propagation
        > canonical
        > 0,
        "coefficient ordering failed",
    )

    return {
        "q=ln(2)": q,
        "canonical": canonical,
        "PR31 only (old entropy, /8)": factor_four_old_entropy,
        "PR32 only (strong entropy, /32)": stronger_entropy_old_propagation,
        "certified midpoint (/8)": certified_midpoint,
        "certified near-root (/4)": certified_near_root,
        "diagnostic four-support midpoint": diagnostic_midpoint,
        "diagnostic four-support near-root": diagnostic_near_root,
        "full-support midpoint limit": full_support_midpoint,
        "full-support near-root limit": full_support_near_root,
        "certified midpoint / canonical": certified_midpoint / canonical,
        "certified near-root / canonical": certified_near_root / canonical,
    }


def placement_diagnostics() -> list[tuple[int, Decimal, Decimal, Decimal]]:
    """Check the explicit theta_N=N^{-1/2} buffer criterion.

    If the root-scale buffer is theta_N*n/N^3 and the error scale is n/N^4,
    their ratio is theta_N*N=sqrt(N).  The returned rows record N, theta_N,
    theta_N*N, and the retained deterministic fraction 1-theta_N.
    """

    rows: list[tuple[int, Decimal, Decimal, Decimal]] = []
    previous_ratio: Decimal | None = None
    previous_theta: Decimal | None = None

    for nlog in (16, 64, 256, 1024, 4096, 16384):
        N = D(nlog)
        theta = D(1) / N.sqrt()
        ratio = theta * N
        retained = D(1) - theta

        require(D(0) < theta < D(1), f"invalid theta at N={N}")
        require(ratio > D(1), f"buffer does not dominate error at N={N}")
        require(D(0) < retained < D(1), f"invalid retained fraction at N={N}")

        if previous_ratio is not None:
            require(ratio > previous_ratio, "theta_N*N is not increasing")
            require(theta < previous_theta, "theta_N is not decreasing")

        previous_ratio = ratio
        previous_theta = theta
        rows.append((nlog, theta, ratio, retained))

    require(rows[-1][2] >= D(100), "buffer ratio is not strongly divergent")
    return rows


def balance_penalties() -> list[tuple[Decimal, Decimal, Decimal]]:
    """Compute entropy losses and their formal root-scale coefficients.

    The coefficient q^2/4*(log 2-H(rho)) is a deterministic diagnostic for the
    proposed first-moment balance-stability theorem.  It is not a proved random
    graph bound until the refined profile union bound is written.
    """

    q = D(2).ln()
    rows: list[tuple[Decimal, Decimal, Decimal]] = []

    for epsilon_text in ("0.01", "0.025", "0.05", "0.10", "0.20", "0.30"):
        epsilon = D(epsilon_text)
        rho = D("0.5") + epsilon
        loss = q - binary_entropy(rho)
        coefficient = q * q * loss / D(4)
        require(loss > 0, f"entropy loss not positive at epsilon={epsilon}")
        require(coefficient > 0, f"root penalty not positive at epsilon={epsilon}")
        rows.append((epsilon, loss, coefficient))

    for previous, current in zip(rows, rows[1:]):
        require(current[1] > previous[1], "entropy loss is not increasing")
        require(current[2] > previous[2], "root penalty is not increasing")

    return rows


def theta_coefficient(theta: Decimal, advantage: Decimal) -> Decimal:
    """Formal retained coefficient (1-theta) q^2 advantage / 4."""

    require(D(0) <= theta <= D(1), f"theta outside [0,1]: {theta}")
    require(advantage >= 0, f"negative advantage: {advantage}")
    q = D(2).ln()
    return (D(1) - theta) * q * q * advantage / D(4)


def placement_coefficient_table() -> list[tuple[str, Decimal]]:
    advantage = (D(1000) / D(639)).ln()
    rows = [
        ("midpoint theta=1/2", theta_coefficient(D("0.5"), advantage)),
        ("quarter placement theta=1/4", theta_coefficient(D("0.25"), advantage)),
        ("theta=1/10", theta_coefficient(D("0.1"), advantage)),
        ("formal theta->0 limit", theta_coefficient(D(0), advantage)),
    ]
    require(rows[0][1] < rows[1][1] < rows[2][1] < rows[3][1],
            "placement coefficients are not ordered")
    return rows


def main() -> None:
    coefficients = coefficient_ledger()
    placements = placement_diagnostics()
    balance = balance_penalties()
    placement_coefficients = placement_coefficient_table()

    print("ERDOS 625 VALUE-UPGRADE CONSTANT LEDGER: PASS")
    print("\nCoefficient ledger")
    for name, value in coefficients.items():
        print(f"  {name}: {value}")

    print("\nCertified placement coefficients")
    for name, value in placement_coefficients:
        print(f"  {name}: {value}")

    print("\nNear-root buffer diagnostics")
    print("  N | theta=N^(-1/2) | theta*N | retained fraction")
    for nlog, theta, ratio, retained in placements:
        print(f"  {nlog} | {theta} | {ratio} | {retained}")

    print("\nSign-balance entropy diagnostics")
    print("  epsilon | log(2)-H(1/2+epsilon) | formal q^2/4 penalty")
    for epsilon, loss, coefficient in balance:
        print(f"  {epsilon} | {loss} | {coefficient}")

    print("\nScope: deterministic coefficient arithmetic and diagnostics only")


if __name__ == "__main__":
    main()
