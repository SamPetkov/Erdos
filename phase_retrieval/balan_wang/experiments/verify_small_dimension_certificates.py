#!/usr/bin/env python3
"""Exact algebraic checks for the Balan--Wang partial-results dossier.

The script uses only the Python standard library.  It verifies identities in
Q(sqrt(5)) and Q(sqrt(6)) exactly, enumerates every three-row subset of the
five-row cyclic construction, and checks the strict comparison with the
optimal equal-norm Parseval value in dimension three.

It is a regression layer for the displayed certificates, not a proof of global
optimality of the cyclic construction or of the universal conjecture.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from decimal import Decimal, getcontext
from fractions import Fraction
from itertools import combinations
from typing import Union


Scalar = Union[int, Fraction, "QuadraticSurd"]


@dataclass(frozen=True)
class QuadraticSurd:
    """An exact element a + b*sqrt(d), with rational a,b and squarefree d."""

    d: int
    a: Fraction = Fraction(0)
    b: Fraction = Fraction(0)

    @classmethod
    def rational(cls, d: int, value: Union[int, Fraction]) -> "QuadraticSurd":
        return cls(d=d, a=Fraction(value), b=Fraction(0))

    def _coerce(self, other: Scalar) -> "QuadraticSurd":
        if isinstance(other, QuadraticSurd):
            if other.d != self.d:
                raise TypeError(f"incompatible quadratic fields: {self.d} and {other.d}")
            return other
        return QuadraticSurd.rational(self.d, Fraction(other))

    def __add__(self, other: Scalar) -> "QuadraticSurd":
        rhs = self._coerce(other)
        return QuadraticSurd(self.d, self.a + rhs.a, self.b + rhs.b)

    def __radd__(self, other: Scalar) -> "QuadraticSurd":
        return self + other

    def __sub__(self, other: Scalar) -> "QuadraticSurd":
        rhs = self._coerce(other)
        return QuadraticSurd(self.d, self.a - rhs.a, self.b - rhs.b)

    def __rsub__(self, other: Scalar) -> "QuadraticSurd":
        return self._coerce(other) - self

    def __neg__(self) -> "QuadraticSurd":
        return QuadraticSurd(self.d, -self.a, -self.b)

    def __mul__(self, other: Scalar) -> "QuadraticSurd":
        rhs = self._coerce(other)
        return QuadraticSurd(
            self.d,
            self.a * rhs.a + self.d * self.b * rhs.b,
            self.a * rhs.b + self.b * rhs.a,
        )

    def __rmul__(self, other: Scalar) -> "QuadraticSurd":
        return self * other

    def __truediv__(self, other: Union[int, Fraction]) -> "QuadraticSurd":
        denominator = Fraction(other)
        if denominator == 0:
            raise ZeroDivisionError("division by zero")
        return QuadraticSurd(self.d, self.a / denominator, self.b / denominator)

    def __pow__(self, exponent: int) -> "QuadraticSurd":
        if exponent < 0:
            raise ValueError("negative powers are not needed by this checker")
        result = QuadraticSurd.rational(self.d, 1)
        base = self
        power = exponent
        while power:
            if power & 1:
                result = result * base
            base = base * base
            power //= 2
        return result

    def sign(self) -> int:
        """Return the exact sign of a+b*sqrt(d)."""

        if self.a == 0 and self.b == 0:
            return 0
        if self.b == 0:
            return 1 if self.a > 0 else -1
        if self.a == 0:
            return 1 if self.b > 0 else -1
        if self.a > 0 and self.b > 0:
            return 1
        if self.a < 0 and self.b < 0:
            return -1

        rational_square = self.a * self.a
        radical_square = self.d * self.b * self.b
        if rational_square == radical_square:
            return 0

        if self.a > 0 and self.b < 0:
            return 1 if rational_square > radical_square else -1
        if self.a < 0 and self.b > 0:
            return 1 if radical_square > rational_square else -1
        raise RuntimeError("unreachable sign case")

    def to_decimal(self) -> Decimal:
        return (
            Decimal(self.a.numerator) / Decimal(self.a.denominator)
            + (Decimal(self.b.numerator) / Decimal(self.b.denominator))
            * Decimal(self.d).sqrt()
        )

    def __str__(self) -> str:
        return f"({self.a}) + ({self.b})*sqrt({self.d})"


def require(condition: bool, message: str) -> None:
    """Optimization-independent regression gate."""

    if not condition:
        raise RuntimeError(message)


def require_equal(left: object, right: object, message: str) -> None:
    if left != right:
        raise RuntimeError(f"{message}: {left!r} != {right!r}")


def q5(a: Union[int, Fraction] = 0, b: Union[int, Fraction] = 0) -> QuadraticSurd:
    return QuadraticSurd(5, Fraction(a), Fraction(b))


def q6(a: Union[int, Fraction] = 0, b: Union[int, Fraction] = 0) -> QuadraticSurd:
    return QuadraticSurd(6, Fraction(a), Fraction(b))


def pair_type(i: int, j: int) -> str:
    distance = min((i - j) % 5, (j - i) % 5)
    if distance == 1:
        return "p"
    if distance == 2:
        return "d"
    raise RuntimeError(f"invalid distinct pair {i}, {j}")


def verify_rho2_certificate() -> None:
    # Two unit rows at projective angle pi/3 have Gram eigenvalues 1 +/- 1/2.
    cosine = Fraction(1, 2)
    least_gram_eigenvalue = 1 - cosine
    require_equal(least_gram_eigenvalue, Fraction(1, 2), "rho_2 Gram value")


def verify_cyclic_rho3_certificate() -> Counter[tuple[str, str, str]]:
    one = q5(1)
    h = q5(Fraction(48, 121), Fraction(-1, 121))
    p = q5(Fraction(57, 242), Fraction(-39, 242))
    d_value = q5(Fraction(31, 121), Fraction(17, 121))

    cos_144 = q5(Fraction(-1, 4), Fraction(-1, 4))
    cos_72 = q5(Fraction(-1, 4), Fraction(1, 4))

    require(h.sign() > 0, "h must be positive")
    require((one - h).sign() > 0, "h must be smaller than one")
    require_equal(h + (one - h) * cos_144, p, "inner product p")
    require_equal(h + (one - h) * cos_72, d_value, "inner product d")

    lambda_a = one - d_value
    expected_lambda_a = q5(Fraction(90, 121), Fraction(-17, 121))
    require_equal(lambda_a, expected_lambda_a, "type-A least eigenvalue")

    lambda_b = q5(Fraction(105, 121), Fraction(-40, 121))
    radical = 2 + p - 2 * lambda_b
    require(radical.sign() > 0, "reconstructed square root must be positive")
    require_equal(
        radical * radical,
        p * p + 8 * d_value * d_value,
        "type-B radical identity",
    )
    require(lambda_b.sign() > 0, "cyclic lower Gram eigenvalue must be positive")
    require((lambda_a - lambda_b).sign() > 0, "type B must be the active orbit")

    patterns: Counter[tuple[str, str, str]] = Counter()
    for triple in combinations(range(5), 3):
        labels = tuple(
            sorted(pair_type(i, j) for i, j in combinations(triple, 2))
        )
        patterns[labels] += 1

    require_equal(
        patterns,
        Counter({("d", "p", "p"): 5, ("d", "d", "p"): 5}),
        "dihedral triple-orbit count",
    )

    parseval_squared = q5(Fraction(1, 2), Fraction(-1, 6))
    # (3-sqrt(5))/6 = 1/2 - sqrt(5)/6.
    expected_gap = q5(Fraction(267, 726), Fraction(-119, 726))
    require_equal(lambda_b - parseval_squared, expected_gap, "Parseval gap identity")
    require(expected_gap.sign() > 0, "cyclic construction must beat Parseval value")
    require_equal(267 * 267 - 5 * 119 * 119, 484, "integer positivity witness")

    return patterns


def verify_rho3_upper_constant() -> None:
    # r=(4-sqrt(6))/6=2/3-sqrt(6)/6 is the smallest positive root
    # of q(x)=10x^3-30x^2+25x-125/27 at equal positive eigenvalues 5/3.
    r = q6(Fraction(2, 3), Fraction(-1, 6))
    polynomial_value = (
        10 * (r**3)
        - 30 * (r**2)
        + 25 * r
        - q6(Fraction(125, 27))
    )
    require_equal(polynomial_value, q6(0), "rho_3 upper-root identity")
    require(r.sign() > 0, "rho_3 upper squared constant must be positive")


def verify_auxiliary_numeric_ordering() -> tuple[Decimal, Decimal, Decimal]:
    getcontext().prec = 80

    cyclic_squared = q5(Fraction(105, 121), Fraction(-40, 121)).to_decimal()
    parseval_squared = q5(Fraction(1, 2), Fraction(-1, 6)).to_decimal()
    upper_squared = q6(Fraction(2, 3), Fraction(-1, 6)).to_decimal()

    require(
        Decimal(0) < parseval_squared < cyclic_squared < upper_squared < Decimal(1),
        "numeric ordering of dimension-three squared constants",
    )

    return (
        parseval_squared.sqrt(),
        cyclic_squared.sqrt(),
        upper_squared.sqrt(),
    )


def verify_simple_prefactor_inequality() -> None:
    # The moment-curve estimate 16 M 4^{-M} is absorbed by
    # 32 (1/3)^M because M(3/4)^M <= 2 for M>=2.
    value = Fraction(2) * Fraction(3, 4) ** 2
    require(value <= 2, "prefactor inequality at M=2")
    for dimension in range(2, 200):
        current = Fraction(dimension) * Fraction(3, 4) ** dimension
        next_value = Fraction(dimension + 1) * Fraction(3, 4) ** (dimension + 1)
        if dimension >= 3:
            require(next_value <= current, "prefactor sequence must decrease from M=3")
        require(current <= 2, f"prefactor inequality failed at M={dimension}")


def main() -> None:
    verify_rho2_certificate()
    patterns = verify_cyclic_rho3_certificate()
    verify_rho3_upper_constant()
    verify_simple_prefactor_inequality()
    parseval_value, cyclic_value, upper_value = verify_auxiliary_numeric_ordering()

    print("BALAN-WANG SMALL-DIMENSION CERTIFICATES: PASS")
    print("  rho_2 = 1/sqrt(2)")
    print(f"  triple patterns: {dict(patterns)}")
    print(f"  equal-norm Parseval M=3 value: {parseval_value}")
    print(f"  cyclic algebraic lower value: {cyclic_value}")
    print(f"  universal M=3 upper value: {upper_value}")
    print("  cyclic lower value is strictly above the Parseval optimum")


if __name__ == "__main__":
    main()
