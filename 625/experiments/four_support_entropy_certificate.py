#!/usr/bin/env python3
"""Exact certificate and diagnostics for the Erdős 625 four-support entropy loss.

The exact part proves, by rational interval arithmetic,
    D_4(delta) < log(639/500),
    log(2)-D_4(delta) > log(1000/639).

The continuum scan is diagnostic only.
"""
from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import math

Q_LO = Fraction(693147180559, 10**12)
Q_HI = Fraction(693147180560, 10**12)
X_LO = Fraction(1035264923841, 10**12)  # lower bound for 2^(1/20)
X_HI = Fraction(1035264923842, 10**12)


def require(condition: bool, message: str) -> None:
    """Raise even under ``python -O`` when a verification condition fails."""
    if not condition:
        raise RuntimeError(message)


def certify_constants() -> None:
    """Certify rational intervals for log(2) and 2^(1/20)."""
    a = Fraction(1, 3)
    terms = 14
    partial = sum(
        Fraction(2) * a ** (2 * k + 1) / (2 * k + 1)
        for k in range(terms)
    )
    tail = (
        Fraction(2, 2 * terms + 1)
        * a ** (2 * terms + 1)
        / (1 - a * a)
    )
    require(Q_LO < partial, "lower log(2) enclosure failed")
    require(partial + tail < Q_HI, "upper log(2) enclosure failed")
    require(X_LO**20 < 2 < X_HI**20, "twentieth-root enclosure failed")


def certify_tilt_bracket() -> None:
    """Certify (49/20)q < lambda_4 < (83/20)q."""
    # At lambda=(49/20)q, after a common shift the retained exponents are
    # 63, 62, 41, 0 for deficits 2, 3, 4, 5.
    numerator_hi = 2 * X_HI**63 + 3 * X_HI**62 + 4 * X_HI**41 + 5
    denominator_lo = X_LO**63 + X_LO**62 + X_LO**41 + 1
    require(
        Q_HI * numerator_hi < 2 * denominator_lo,
        "lower tilt does not certify mean < 2/q",
    )

    # At lambda=(83/20)q, the retained exponents are 126,159,172,165.
    lower_sum = Fraction(0)
    for i, exponent in ((2, 126), (3, 159), (4, 172), (5, 165)):
        coefficient = Q_LO * (i - 1) - 2
        power = X_HI**exponent if coefficient < 0 else X_LO**exponent
        lower_sum += coefficient * power
    require(
        lower_sum > 0,
        "upper tilt does not certify mean > 1+2/q",
    )


def certify_omitted_ratios() -> dict[str, Fraction]:
    """Certify the four rational low/high omitted-ratio bounds."""
    # L((49/20)q): shift by the deficit -1 exponent.
    low_num_hi = 1 + X_HI**59 + X_HI**98
    kept_den_lo = X_LO**117 + X_LO**116 + X_LO**95 + X_LO**54
    require(
        1000 * low_num_hi < 263 * kept_den_lo,
        "L(49q/20) bound failed",
    )

    # H((29/10)q): deficit 6 has exponent -12 and subsequent ratios are
    # at most x^(-72).
    high_split_hi = X_LO**(-12) / (1 - X_LO**(-72))
    kept_split_lo = X_LO**76 + X_LO**84 + X_LO**72 + X_LO**40
    require(
        200 * high_split_hi < 3 * kept_split_lo,
        "H(29q/10) bound failed",
    )

    # L((29/10)q): normalized low exponents 0,68,116 and retained
    # exponents 144,152,140,108.
    low_split_hi = 1 + X_HI**68 + X_HI**116
    kept_shifted_lo = X_LO**144 + X_LO**152 + X_LO**140 + X_LO**108
    require(
        250 * low_split_hi < 33 * kept_shifted_lo,
        "L(29q/10) bound failed",
    )

    # H((83/20)q): high exponents 138,91,24,-63,...; after deficit 9
    # every successive ratio is at most x^(-107).
    high_upper_hi = (
        X_HI**138
        + X_HI**91
        + X_HI**24
        + X_LO**(-63) / (1 - X_LO**(-107))
    )
    kept_upper_lo = X_LO**126 + X_LO**159 + X_LO**172 + X_LO**165
    require(
        200 * high_upper_hi < 29 * kept_upper_lo,
        "H(83q/20) bound failed",
    )

    low_case = Fraction(263, 1000) + Fraction(3, 200)
    high_case = Fraction(33, 250) + Fraction(29, 200)
    require(low_case == Fraction(139, 500), "low-case rational sum changed")
    require(high_case == Fraction(277, 1000), "high-case rational sum changed")
    require(high_case < low_case, "case ordering changed")
    return {
        "L_lower": Fraction(263, 1000),
        "H_split": Fraction(3, 200),
        "L_split": Fraction(33, 250),
        "H_upper": Fraction(29, 200),
        "omitted": low_case,
    }


def value_function(support: tuple[int, ...], target: float) -> float:
    """Numerically evaluate the limiting constrained value."""
    q = math.log(2.0)
    lo, hi = -20.0, 20.0
    for _ in range(90):
        lam = (lo + hi) / 2
        scores = [lam * i - q * i * i / 2 for i in support]
        top = max(scores)
        weights = [math.exp(score - top) for score in scores]
        mean = sum(i * w for i, w in zip(support, weights)) / sum(weights)
        if mean < target:
            lo = lam
        else:
            hi = lam
    lam = (lo + hi) / 2
    scores = [lam * i - q * i * i / 2 for i in support]
    top = max(scores)
    log_partition = top + math.log(
        sum(math.exp(score - top) for score in scores)
    )
    return log_partition - lam * target


def phase_scan(points: int = 2001) -> tuple[float, float, float]:
    """Diagnostic scan; not used by the rational certificate."""
    q = math.log(2.0)
    support4 = (2, 3, 4, 5)
    plus60 = tuple(range(-1, 60))
    plus90 = tuple(range(-1, 90))
    best = (float("inf"), 0.0)
    truncation = 0.0
    for step in range(points):
        delta = step / (points - 1)
        target = 1 + 2 / q - delta
        value4 = value_function(support4, target)
        value60 = value_function(plus60, target)
        value90 = value_function(plus90, target)
        truncation = max(truncation, abs(value60 - value90))
        advantage = q - (value90 - value4)
        if advantage < best[0]:
            best = (advantage, delta)
    return best[0], best[1], truncation


def source_check() -> str:
    """Guard the canonical definitions used by this certificate."""
    path = Path("625/proofs/COMPLETE_PROOF_SELF_CONTAINED.md")
    if not path.exists():
        return "SKIPPED"
    text = path.read_text(encoding="utf-8")
    for tag in ("\\tag{5.1}", "\\tag{5.2}", "\\tag{5.3}", "\\tag{5.7}"):
        require(tag in text, f"missing canonical equation tag {tag}")
    return "PASS"


def main() -> None:
    certify_constants()
    certify_tilt_bracket()
    bounds = certify_omitted_ratios()
    minimum, delta, truncation = phase_scan()
    gamma = math.log(1000 / 639)
    q = math.log(2.0)

    print("ERDOS 625 FOUR-SUPPORT ENTROPY CERTIFICATE: PASS")
    print("  tilt bracket: (49/20)q < lambda_4 < (83/20)q")
    print(f"  L(49q/20) < {bounds['L_lower']}")
    print(f"  H(29q/10) < {bounds['H_split']}")
    print(f"  L(29q/10) < {bounds['L_split']}")
    print(f"  H(83q/20) < {bounds['H_upper']}")
    print(f"  uniform omitted ratio < {bounds['omitted']}")
    print("  D_4(delta) < log(639/500)")
    print("  log(2)-D_4(delta) > log(1000/639)")
    print(f"  certificate gamma = {gamma:.15f}")
    print(
        "  coefficient with current /32 propagation = "
        f"{q*q*gamma/32:.15f}"
    )
    print(
        "  coefficient combined with PR #31 /8 propagation = "
        f"{q*q*gamma/8:.15f}"
    )
    print(f"  canonical source scan: {source_check()}")
    print("DIAGNOSTIC ONLY:")
    print(
        f"  phase-grid min advantage = {minimum:.15f} "
        f"at delta={delta:.6f}"
    )
    print(f"  S_plus truncation disagreement = {truncation:.3e}")


if __name__ == "__main__":
    main()
