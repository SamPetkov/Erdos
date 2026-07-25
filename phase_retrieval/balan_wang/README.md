# Universal Balan–Wang instability at the critical threshold

> **Status:** strong deterministic partial result. This directory does **not**
> claim a proof or disproof of the universal conjecture.

This dossier studies the Balan–Wang conjecture for a full-spark real matrix

\[
A\in\mathbb R^{(2M-1)\times M},
\qquad
\omega(A)=\min_{|S|=M}\sigma_{\min}(A_S),
\qquad
R(A)=\max_i\|a_i\|_2.
\]

The open problem asks whether universal constants `C > 0` and `0 < beta < 1`
exist such that

\[
\omega(A)\le C R(A)\beta^M
\]

for every dimension and every full-spark critical frame.

## Contents

- [`proofs/STRONG_PARTIAL_RESULTS.md`](proofs/STRONG_PARTIAL_RESULTS.md) —
  self-contained theorem-by-theorem write-up, independent proof-first and
  counterexample-first cycles, merged obstruction, and adversarial audit.
- [`experiments/verify_small_dimension_certificates.py`](experiments/verify_small_dimension_certificates.py)
  — standard-library exact quadratic-surd checks for the algebraic
  three-dimensional construction, the equal-norm Parseval comparison, and the
  stated upper-bound constants.

## Main conclusions

1. The square-submatrix, projection-order-statistic, and row-to-hyperplane
   incidence formulations are proved with exact constants.
2. Rowwise normalization is monotone, and the general problem is equivalent at
   exponential scale, up to a factor `sqrt(2M-1)`, to the Parseval problem.
3. Every critical frame satisfies an explicit universal
   `O(M^(-3/2))` upper bound. This is polynomial and therefore does not settle
   the conjecture.
4. Normalized real moment-curve/Vandermonde frames satisfy
   \[
   \omega(A)\le 16M R(A)4^{-M}.
   \]
5. A max-volume basis converts the unresolved universal problem into one
   quantitative question about square submatrices of totally nonsingular
   matrices whose minors are bounded by one.
6. The exact two-dimensional value is
   \[
   \rho_2=1/\sqrt2.
   \]
7. The dossier proves the rigorous three-dimensional bracket
   \[
   \frac{\sqrt{105-40\sqrt5}}{11}
   \le \rho_3
   \le \sqrt{\frac{4-\sqrt6}{6}}.
   \]
8. The lower construction is strictly better than every equal-norm Parseval
   frame in dimension three. Hence tightness is not a valid universal extremal
   reduction.

## Precise remaining obstruction

It is enough, and is necessary up to polynomial factors, to prove the following
quantitative totally-nonsingular statement:

> There are universal `c > 0` and `p < infinity` such that every totally
> nonsingular matrix
> \[
> C\in\mathbb R^{(M-1)\times M}
> \]
> whose every square minor has modulus at most one contains a square submatrix
> `E` with
> \[
> \sigma_{\min}(E)\le M^p e^{-cM}.
> \]

No such deterministic estimate is proved here. No explicit infinite family
with subexponential normalized stability is constructed either.

## Reproduction

From the repository root:

```bash
python phase_retrieval/balan_wang/experiments/verify_small_dimension_certificates.py
python -O phase_retrieval/balan_wang/experiments/verify_small_dimension_certificates.py
```

The checker uses explicit exceptions rather than optimization-sensitive
`assert` statements and has no third-party dependencies.

## Literature boundary

The note uses the original Balan–Wang formulation, the Liu–Wang work on decay
of least singular values of submatrices, Shmalo's Gaussian critical-base
result, and recent work connecting full-spark frames with totally nonsingular
matrices. The literature search recorded in the proof note is targeted rather
than exhaustive. No novelty or priority claim should be inferred without a
separate specialist review.

All claims in this directory are preprint-level research claims and have not
undergone external peer review.