# Verification report for Erdős 625 draft PR #27

**Repository base audited:** `main` at
`cda78922ea6c87bfc81f9bf693374dd045dac624`.

**Scope.** This report audits the new review appendix, extensions note, and
standard-library verification scripts in draft PR #27.  It does not audit the
entire canonical manuscript from first principles, and it does not claim that
`Erdos625Statement` is formally proved.

## 1. Corrections made during this audit

Four defects or ambiguities were found in earlier PR #27 text and corrected.

1. **Missing degree-cap hypotheses in Proposition 8.0.**  The high-cell matching
   assertion is false for arbitrary margins.  The corrected statement assumes
   `s_a <= U` and `t_b <= U` for every row and column.  The checker retains the
   counterexample `U=4`, row margin `(6)`, column margins `(3,3)`, table `(3,3)`
   as a regression test.

2. **Non-finite middle-strip notation.**  The expression
   `j <= 3a/4 + O(1)` has been replaced by the exact type-dependent bound

   \[
    R_0<j\le\left\lfloor\frac{3\min(u_i,u_j)}4\right\rfloor
       \le\left\lfloor\frac{3a}4\right\rfloor.
   \]

3. **Missing Section 8 fibre and conditional-sum maps.**  The rewrite now gives
   the dependent demand/witness/residual disjoint union, the explicit
   labelled-decoration map, its multinomial fibre cardinality
   `ell! / prod n_e!`, the cancellation with the endpoint-table factorial, an
   injective endpoint/near/middle encoding, and the pointwise-to-expectation
   inequality in the small-residual branch.  Formal decoration tuples that are
   not feasible are admitted only after the exact extraction, as a nonnegative
   overcount.

4. **Off-matching square-sum equality.**  Since the residual weights `q_e` are
   zero on the exposed matching, the correct statement is

   \[
    \sum_e q_e
    =\frac12\sum_{(a,b)\notin M}\widetilde\theta_{ab}^{\,2}+\Lambda_0
    \le\frac12\sum_{a,b}\widetilde\theta_{ab}^{\,2}+\Lambda_0.
   \]

   Only the unrestricted sum factorizes.  The resulting
   `exp(C(U^2+U^4/m_0))` attachment bound is unchanged.

## 2. Exact finite tests

Run from the repository root:

```text
python 625/experiments/review27_verification.py
python 625/experiments/entropy_certificate_upgrade.py
```

The first script performs the following independent checks using integers and
`fractions.Fraction` except where explicitly labelled as a decimal diagnostic.

| Check | Cases | Result |
|---|---:|---:|
| Bounded-margin canonical extraction, residual margins/cap, and exact mass cancellation | 3,809 tables | PASS |
| Labelled perfect-matchings, dependent demand/witness/residual encoding, and fibre-cardinality factorization | 5,880 matchings | PASS |
| Typed-decoration fibre cardinalities and factorial cancellation | 330 fibres | PASS |
| Exact endpoint/near/middle classification and floor bound | 5,929 cells | PASS |
| Even-subgraph restriction injection, cardinality bound, and weighted subset-product inequality | 162 bipartite instances | PASS |
| Corrected off-matching square-sum inequality | 263,967 degree/matching instances | PASS |
| Central-rate endpoint signs | 80-digit decimal evaluation | PASS |

The entropy script independently verifies, by exact rational arithmetic, the
four-support and three-support tilt brackets and omitted-mass inequalities.  Its
continuum support scans are numerical diagnostics only.

## 3. Mathematical conclusions supported by the audit

The following new statements survived the finite and algebraic audit.

- Restriction away from a matching is injective on even edge sets.  Consequently
  the cycle decomposition in the large-residual branch can be replaced by a
  direct subset-product bound.
- The corrected large-residual estimate is

  \[
   \mathcal A(M,j)
   \le \exp\!\left\{C\left(U^2+\frac{U^4}{m_0}\right)\right\},
  \]

  hence `exp(O(N^2))` when `m_0 >= n/N^6`.
- The displayed central-rate constant `1/100` is valid on the stated domain.
- The exact rational checks support

  \[
   D_4(\delta)<\ln(33/25),\qquad q-D_4(\delta)>\ln(50/33),
  \]

  and the separate three-support first-moment certificate recorded in the
  extensions note.

## 4. Remaining review boundary

The tests above do not prove an asymptotic theorem.  Before canonical
integration, an independent reviewer should still check:

1. that the exact finite disintegration in Proposition 8.0 is instantiated with
   precisely the same labelled/unlabelled conventions as the normalized second
   moment;
2. that every factor in the global inequality (8.29d) agrees with the canonical
   endpoint and conditional residual laws;
3. that the rational entropy comparisons are translated into the manuscript's
   finite-`n` optimizer uniformly in the phase;
4. that carrying equation (5.11) directly through rounding and amplification
   introduces only the stated `o(n/N^3)` loss;
5. the literature-dependent fixed-`p` and second-order upper-bound corollaries.

The three-size profile and non-midpoint root placement remain proposed
alternative routes.  They are not replacements for the four-size theorem until
the full partial-diagonal, transportation, high-skeleton, residual, and
amplification chains are replayed.

## 5. Recommendation

Keep PR #27 as a draft mathematical-review PR.  The residual-restriction
simplification and the corrected Section 8 finite maps are suitable for
line-by-line review.  Do not replace the canonical manuscript or publication
PDFs until that review is complete.
