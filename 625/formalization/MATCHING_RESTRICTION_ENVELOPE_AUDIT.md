# Audit: direct matching-restriction attachment envelope

## Scope

This audit accompanies:

- `Erdos625/Section9MatchingRestrictionEnvelope.lean`;
- `Erdos625/Section9ProfileAttachmentMatchingEnvelope.lean`.

The branch is stacked on PR #34 and therefore assumes the finite
matching-restriction product theorem from
`Section9MatchingRestrictionProduct.lean`.

## New checked targets

The first module is intended to prove the following finite statements.

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

The second module specializes this statement to every attained profile high
skeleton by using its canonical reference witness, literal positive-demand
matching support, residual degree caps, equal residual totals, and the exact
definition of `profileHighSkeletonAttachment`.

The resulting profile theorem has no traversal parameter, no factor depending
on the number of profile blocks, and no factor depending on the number of
matching edges.

## Dependencies reused

- `residualActualAttachmentNumerator_eq_residualCappedEvenFixedFSum`;
- `residualCappedEvenFixedFSum_le_lambdaProduct_mul_matchingProduct` from the
  stacked PR #34;
- `existsAbsoluteResidualQQuadraticBound`;
- `existsAbsoluteResidualLambdaTotalBound`;
- exact degree-square and configuration-theta identities from
  `ConfigurationThetaMoments.lean`;
- `ennreal_polymer_product_le_ereal_exp_sum` for finite products;
- `canonicalReference_residual_parameters` and
  `profileBlockMargin_total_eq_self` for the attained-profile specialization.

## Trust gates

The focused workflow:

- rejects `sorry`, `admit`, `sorryAx`, project `axiom`/`constant`, and `unsafe`;
- prepares the pinned Lean 4.31/mathlib project;
- builds the profile endpoint and its dependency closure with `--wfail`;
- prints the axioms of every new public theorem.

The ordinary repository Lean workflow also runs because this PR changes the
formalization tree.

## Deliberate boundary

These modules still do not prove the complete Erdős 625 theorem. In particular
they do not:

- sum the Section VIII bare skeleton weights;
- specialize the exponent to the midpoint phase and prove the eventual
  `O((log n)^2)` or `o(n/(log n)^4)` scale;
- update the root aggregate or generated self-contained checkpoint;
- prove the chromatic lower tail, rare seed, or final event intersection.

The next integration step, after review, is a profile-level asymptotic adapter
showing that the displayed exponent is `o(amplificationBase n)` uniformly over
attained canonical demands.
