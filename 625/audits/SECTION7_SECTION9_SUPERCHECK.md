# Super-check of the proposed Erdős 625 Section 7 and Section 9 simplifications

**Repository base:** `main` at `cda78922ea6c87bfc81f9bf693374dd045dac624`.

**Verdict:** the two isolated claims in
`proofs/SECTION7_SECTION9_SUPERCHECK.md` pass this review.  This is not a verdict
on all of draft PR #27 or on the complete candidate proof.

## Checked claims

1. The central partial-diagonal rate satisfies
   \[
   \Phi_T(z)\le-(1-R)/100
   \]
   on the displayed domain.
2. Restriction away from a matching is injective on even edge sets.
3. The resulting weighted family sum is bounded by the full residual subset
   product.
4. The off-matching square sum is bounded by the unrestricted factorized sum.
5. The large-residual attachment envelope is therefore
   \[
   \mathcal A(M,j)\le
   \exp\{C(U^2+U^4/m_0)\}=\exp(O(N^2)).
   \]

## Independent exact checks

Run from the repository root:

```text
python 625/experiments/section7_section9_supercheck.py
```

The current run reports:

```text
ERDOS 625 SECTION 7/9 SUPERCHECK: PASS
  central-rate endpoint inequalities: exact Fraction bounds
  residual relations exhausted: 5912
  even edge sets checked: 12561
  square-sum instances checked: 613711
```

The logarithm endpoint checks use rational lower and upper bounds from the
atanh series, rather than floating-point signs.  The graph checks exhaust every
partial matching and every residual relation in the listed small complete
bipartite graphs.

## Adversarial points checked

- The matching hypothesis is essential.  No restriction-injectivity statement
  is made for a general high-edge graph.
- The product runs only over residual edges outside the matching.
- The identity in the square-sum step is used only for the unrestricted sum;
  the off-matching sum enters by a one-sided inequality.
- The bound `sum d^2 <= U m_0` uses both nonnegativity and the residual degree
  cap `d <= U`.
- The estimate still relies on the previously established threshold expansion
  and `Lambda_0 <= C U^4/m_0`.

## Material deliberately excluded

This clean review does not promote the following PR #27 items:

- the complete Section 8 global skeleton inequality;
- the factor-four theorem-constant improvement;
- the stronger four-support entropy certificate;
- the three-size profile;
- non-midpoint root placement;
- literature-dependent fixed-density and upper-bound corollaries.

Those claims may be correct, but their complete interfaces require separate
review.  Keeping them out of this focused change prevents a verified finite
simplification from being coupled to broader speculative or still-unintegrated
claims.
