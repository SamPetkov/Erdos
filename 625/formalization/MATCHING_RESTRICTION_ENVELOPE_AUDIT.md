# Audit: direct matching-restriction attachment envelope

## Scope

This audit accompanies `Erdos625/Section9MatchingRestrictionEnvelope.lean`.
The branch is stacked on PR #34 and therefore assumes the finite
matching-restriction product theorem from
`Section9MatchingRestrictionProduct.lean`.

## New checked targets

The new module is intended to prove the following finite statements.

1. The complete square mass of the configuration-cell parameters factorizes as

   \[
   \sum_{a,b}\theta_{ab}^2
   =\left(\frac e m\right)^2
     \left(\sum_a d_a^2\right)
     \left(\sum_b (d_b')^2\right).
   \]

2. If both degree families have common positive total `m` and are capped by
   `U`, then

   \[
   \sum_{a,b}\theta_{ab}^2\le e^2U^2.
   \]

3. The existing pointwise quadratic bound on `residualQ` therefore sums to

   \[
   \sum_{a,b}q_{ab}\le \kappa_Q U^2
   \]

   for one absolute positive finite constant.

4. The exact fixed-family Fubini identity transports the direct product theorem
   of PR #34 to the literal event-restricted attachment numerator.

5. Combining the lambda and residual-q products gives

   \[
   \mathcal A(M,j)
   \le
   \exp\!\left(
      \kappa_\Lambda\frac{U^4}{m}
      +\kappa_Q U^2
   \right).
   \]

This statement has no traversal parameter, no factor depending on the number
of profile blocks, and no factor depending on the number of matching edges.

## Dependencies reused

- `residualActualAttachmentNumerator_eq_residualCappedEvenFixedFSum`;
- `residualCappedEvenFixedFSum_le_lambdaProduct_mul_matchingProduct` from the
  stacked PR #34;
- `existsAbsoluteResidualQQuadraticBound`;
- `existsAbsoluteResidualLambdaTotalBound`;
- exact degree-square and configuration-theta identities from
  `ConfigurationThetaMoments.lean`;
- `ennreal_polymer_product_le_ereal_exp_sum` for finite products.

## Trust gates

The focused workflow:

- rejects `sorry`, `admit`, `sorryAx`, project `axiom`/`constant`, and `unsafe`;
- builds the pinned Lean 4.31/mathlib project with warnings fatal;
- compiles the new module directly with `-DwarningAsError=true`;
- prints the axioms of every new public theorem.

The ordinary repository Lean workflow also runs because this PR changes the
formalization tree.

## Deliberate boundary

This module still does not prove the complete Erdős 625 theorem. In particular
it does not:

- sum the Section VIII bare skeleton weights;
- specialize the envelope to the midpoint profile and produce the eventual
  `o(n/(log n)^4)` coefficient;
- update the root aggregate or generated self-contained checkpoint;
- prove the chromatic lower tail, rare seed, or final event intersection.

The next integration step, after review, is a profile-level asymptotic adapter
showing that the displayed exponent is `o(amplificationBase n)` uniformly over
attained canonical demands.
