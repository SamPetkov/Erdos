# Audit: q-only matching-restriction attachment envelope

## Purpose

This follow-up isolates one additional simplification of the direct Section 9
route.  The preceding branch bounds the literal residual attachment by a
product of local-increment factors and a direct outside-matching `q` product.
Here those two products are charged to the same total `q` mass.

Outside the exposed matching,

\[
q_{ab}=\frac{\theta_{ab}^2}{2}+\lambda_{ab},
\]

and both quantities vanish on the matching.  Hence
\(\lambda_{ab}\le q_{ab}\) cellwise.  The accepted total bound

\[
\sum_{a,b}q_{ab}\le \kappa_Q U^2
\]

therefore controls both products, giving

\[
\mathcal A(M,j)
 \le \exp\!\left(2\sum_{a,b}q_{ab}\right)
 \le \exp(\kappa U^2).
\]

## New declarations

`Erdos625/Section9MatchingRestrictionQOnly.lean` proves:

1. `residualLambda_le_residualQ`;
2. `lambda_matching_products_le_exp_two_q_bound`;
3. `le_three_mul_residualCeilThird`;
4. `residualMass_lt_two_pow_ceilThird_of_not_cube`;
5. `exists_absolute_residualActualAttachmentNumerator_le_qOnlyEnvelope`.

The last theorem is pointwise in the finite residual data and concerns the
literal cap/no-return numerator.  It has no separate `U^4/m` term, no cubic
degree moment, no cycle traversal, and no dependence on the number of profile
blocks or matching edges.

## A more intrinsic two-regime split

The finite q-only theorem naturally assumes

\[
2^U\le m^3.
\]

There is no need to introduce the manuscript cutoff
\(m=n/(\log n)^6\) at the finite combinatorial level.  The Lean theorem
`residualMass_lt_two_pow_ceilThird_of_not_cube` proves the exact complementary
statement

\[
2^U\nleq m^3
\quad\Longrightarrow\quad
m<2^{\lceil U/3\rceil},
\qquad
\lceil U/3\rceil=\frac{U+2}{3}.
\]

Thus Section 9 may eventually be organized around the intrinsic dichotomy:

- **quadratic regime:** `2^U <= m^3`, use the q-only envelope
  `exp(O(U^2))`;
- **small-power regime:** `2^U > m^3`, use the deterministic bound together
  with `m < 2^(ceil(U/3))`.

At the midpoint phase, `U=(2+o(1)) log_2 n`, so the second exponent is of order
at most `U 2^(ceil(U/3)) = n^(2/3+o(1))`, still
`o(n/(log n)^4)`.  That asymptotic specialization is not asserted by this PR;
only the exact finite dichotomy is kernel-checked here.

## Reused inputs

- the exact fixed-family Fubini identity;
- the matching-restriction product theorem;
- the direct lambda/q product bridge;
- the already checked quadratic total-q estimate.

## Trust gates

The focused workflow rejects placeholders, project-defined axioms/constants,
and `unsafe`; it then builds the new module and its dependency closure under
the pinned Lean 4.31/mathlib project with warnings fatal.  The source prints
the axioms of every new public theorem.

## Deliberate boundary

This PR does not by itself:

- rewrite the canonical manuscript;
- sum the Section 8 skeleton weights;
- prove the phase-asymptotic small-power estimate;
- combine both residual regimes in the profile-level second moment;
- prove Proposition 9.2 or `Erdos625Statement`.

Its role is to remove a redundant analytic branch from the large-residual
attachment estimate and to expose a cleaner finite regime split before
manuscript integration.
