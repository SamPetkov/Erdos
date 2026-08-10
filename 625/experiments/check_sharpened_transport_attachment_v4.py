#!/usr/bin/env python3
"""Fail-closed scalar and source checks for the sharpened Section 8--9 ledger."""

from __future__ import annotations

import math
import re
from collections import Counter
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "arxiv" / "SECTION9_SHARPENED_TRANSPORT_ATTACHMENT_V4.tex"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def log2_factorial(value: int) -> float:
    return math.lgamma(value + 1) / math.log(2.0)


def check_source() -> tuple[int, int]:
    require(SOURCE.is_file(), f"missing sharpened theorem-facing source: {SOURCE}")
    text = SOURCE.read_text(encoding="utf-8")
    flat = re.sub(r"\s+", " ", text)

    for token in (
        "Fused deficit--endpoint transport",
        "Type-preserving deficit product",
        r"B_{ij}:=\frac1{1-\rho_{ij}}",
        r"\widetilde Q_{ij}:=B_{ij}Q_{ij}",
        r"\Gamma_n^{\mathrm{skel},\sharp}",
        r"T_U:=U^2 2^{U/4}",
        "Critical-quarter residual attachment",
        r"\Gamma_n^{\mathrm{att},\sharp}",
        "Explicit sharpened seed exponent",
        r"\sqrt n\,(\log n)^{5/2}",
        "Neither interface requires the arbitrary exponent $1/3$",
    ):
        require(token in flat, f"sharpened source missing semantic token: {token}")

    bad_controls = [
        (index, ord(character))
        for index, character in enumerate(text)
        if ord(character) < 32 and character not in "\n\r\t"
    ]
    require(not bad_controls, f"hidden control characters: {bad_controls[:8]}")

    begins = Counter(re.findall(r"\\begin\{([^}]+)\}", text))
    ends = Counter(re.findall(r"\\end\{([^}]+)\}", text))
    require(begins == ends, f"unbalanced environments: {begins - ends}, {ends - begins}")
    require(text.count("{") == text.count("}"), "unbalanced braces")

    for forbidden in (
        "TODO",
        "TBD",
        "proof omitted",
        "details are standard",
        r"\ln",
        r"\log2",
    ):
        require(forbidden not in text, f"forbidden marker in sharpened source: {forbidden}")

    tags = re.findall(r"\\tag\{([^}]+)\}", text)
    expected = {f"9.{number}" for number in range(43, 58)}
    require(set(tags) == expected, f"unexpected sharpened tags: {sorted(set(tags) ^ expected)}")
    require(len(tags) == len(set(tags)), "duplicate sharpened equation tags")

    labels = re.findall(r"\\label\{([^}]+)\}", text)
    require(len(labels) == len(set(labels)), "duplicate sharpened semantic labels")
    require(len(text.splitlines()) >= 250, "sharpened source is unexpectedly short")
    return len(text.splitlines()), len(tags)


def check_critical_quarter_endpoint() -> int:
    """Check the exact scalar cancellation and a conservative finite threshold."""
    first_uniform_u = 15
    for u in range(8, 4097):
        r = u // 2
        cancellation = Fraction(r * (r - 1), 2) - Fraction(u * (r - 2), 4)
        require(
            cancellation <= Fraction(u, 2),
            f"critical-quarter cancellation failed at U={u}",
        )

        if u < first_uniform_u:
            continue
        theta_log2 = math.log2(math.e) - u / 4.0
        first_endpoint = (2.0 * r / 3.0) * 2.0**theta_log2
        require(first_endpoint <= 1.0, f"cubic endpoint exceeds theta^2 at U={u}")

        if r >= 3:
            reward_log2 = r * (r - 1) / 2.0 - 1.0
            second_endpoint_log2 = (
                math.log2(r)
                + reward_log2
                + (r - 2) * theta_log2
                - log2_factorial(r)
            )
            require(
                second_endpoint_log2 <= 0.0,
                f"full endpoint exceeds theta^2 at U={u}",
            )
    return first_uniform_u


def check_rate_ledger() -> None:
    # Monomials are encoded as n^a (log n)^b.
    rho = (Fraction(-1, 2), Fraction(5, 2))
    class_count = (Fraction(1), Fraction(-1))
    eta = (Fraction(-1, 2), Fraction(3, 2))
    quarter_attachment = (Fraction(1, 2), Fraction(5, 2))

    fused_deficit = (rho[0] + class_count[0], rho[1] + class_count[1])
    endpoint_transport = (eta[0] + class_count[0], eta[1] + class_count[1])
    require(
        fused_deficit == (Fraction(1, 2), Fraction(3, 2)),
        "fused deficit rate mismatch",
    )
    require(
        endpoint_transport == (Fraction(1, 2), Fraction(1, 2)),
        "endpoint rate mismatch",
    )
    require(
        quarter_attachment == (Fraction(1, 2), Fraction(5, 2)),
        "attachment rate mismatch",
    )

    target_n_power = Fraction(1)
    for name, (n_power, _) in {
        "fused skeleton": fused_deficit,
        "endpoint transport": endpoint_transport,
        "critical-quarter attachment": quarter_attachment,
    }.items():
        require(n_power < target_n_power, f"{name} is not o(n/(log n)^4)")


def main() -> None:
    source_lines, tags = check_source()
    threshold = check_critical_quarter_endpoint()
    check_rate_ledger()
    print("ERDOS 625 SHARPENED TRANSPORT/ATTACHMENT LEDGER: PASS")
    print(f"  source lines: {source_lines}")
    print(f"  guarded equation tags: {tags}")
    print("  fused skeleton exponent: O(sqrt(n) (log n)^(3/2))")
    print("  critical-quarter attachment: O(sqrt(n) (log n)^(5/2))")
    print(f"  numerical endpoint threshold checked from U={threshold} through U=4096")
    print("  finite U below the threshold is absorbed into the absolute activity constant")


if __name__ == "__main__":
    main()
