# Matching-restriction product formalization audit

**Date:** 25 July 2026  
**Target module:** `Erdos625/Section9MatchingRestrictionProduct.lean`  
**Status:** focused finite Lean checkpoint; not Lemma 9.1 or `Erdos625Statement`.

## Exact claims

The module proves three finite statements.

1. If `M` is a bipartite matching, the map

   ```text
   F ↦ F \ M
   ```

   is injective on the finite family of bipartite even edge sets.

2. For arbitrary `ENNReal` cell weights,

   ```text
   sum_{F even} product_{e in F\M} q_e
     <= product_{e notin M} (1 + q_e).
   ```

3. The existing capped fixed-`F` aggregation is bounded by the common local
   `residualLambda` product times this direct outside-matching product.

## Proof dependencies

The proof reuses only accepted finite modules:

- `BipartiteEdgeMatrix.lean` for the injective zero-one incidence encoding and
  the equivalence between even edge sets and zero row/column sums over
  `ZMod 2`;
- `EvenMatchingRestriction.lean` for uniqueness of an even matrix after its
  values away from a row matching are fixed;
- `Section9ActualResidualENNRealPolymerBridge.lean` for the definition of
  `edgeWeightOutsideENN` and the finite even-edge family;
- `Section9FixedFEvenAggregation.lean` for the previously checked fixed-`F`
  threshold expansion and aggregation.

No cycle decomposition, walk kernel, marked-cycle encoder, asymptotic estimate,
probability conditioning, or external theorem is used.

## Trust checks

The source contains no `sorry`, `admit`, project-defined `axiom`, `constant`, or
`unsafe` declaration.  Each public theorem is followed by `#print axioms`.
The focused workflow compiles the module with `-DwarningAsError=true`; the full
repository Lean workflow also builds every formalization module with `--wfail`.

## Deliberate boundary

This checkpoint does not prove the manuscript's complete large-residual
attachment estimate.  Remaining bridges include:

1. the precise tagged-law identification of the actual attachment numerator;
2. a finite bound on the direct product in terms of the total `residualQ` mass;
3. the deterministic estimate
   `sum residualQ = O(U^2 + U^4/m_0)` under the large-residual hypotheses;
4. the asymptotic specialization to `exp(O((log n)^2))`;
5. the global Section 8 skeleton sum and Proposition 9.2.

The module is therefore a genuine simplification of the finite Section IX
algebra, but not a completed proof of the theorem.
