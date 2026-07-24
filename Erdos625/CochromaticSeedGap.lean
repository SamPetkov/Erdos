import Erdos625.InducedCochromaticCapacity
import Erdos625.RareSeedInversion

/-!
# The graph-specific rare-seed gap bridge

This module specializes `rareSeed_gap_le` to the largest induced subgraph of
a labelled graph that is cocolourable with at most `k` parts.  It is the exact
probabilistic bridge corresponding to manuscript display (10.7): a lower
bound on the probability of full cocolourability, together with the audited
one-sided vertex-block tail, bounds the deficit between `n` and the actual
expectation of the induced-capacity statistic.
-/

open MeasureTheory Set

namespace Erdos625

noncomputable section

/-- On the finite labelled-graph sample space, the real-valued induced
capacity is measurable. -/
theorem measurable_cochromaticInducedCapacity_real (n k : ℕ) :
    Measurable
      (fun G : LabeledGraph n ↦ (cochromaticInducedCapacity G k : ℝ)) :=
  measurable_of_finite _

/-- On the finite probability space `G(n, 1/2)`, the real-valued induced
capacity is Bochner integrable. -/
theorem integrable_cochromaticInducedCapacity_real (n k : ℕ) :
    Integrable
      (fun G : LabeledGraph n ↦ (cochromaticInducedCapacity G k : ℝ))
      (randomGraphMeasure n) :=
  Integrable.of_finite

/-- The induced-capacity statistic is pointwise bounded above by the number
of vertices, in the real-valued form needed by expectation comparison. -/
theorem cochromaticInducedCapacity_real_le_card (n k : ℕ)
    (G : LabeledGraph n) :
    (cochromaticInducedCapacity G k : ℝ) ≤ (n : ℝ) := by
  exact_mod_cast cochromaticInducedCapacity_le_card G k

/-- Reaching the real endpoint `n` is exactly full `k`-cocolourability. -/
theorem cochromaticInducedCapacity_levelSet_eq (n k : ℕ) :
    {G : LabeledGraph n |
        (cochromaticInducedCapacity G k : ℝ) = (n : ℝ)} =
      {G : LabeledGraph n | CoColorable G k} := by
  ext G
  simpa only [Set.mem_setOf_eq, Nat.cast_inj] using
    (cochromaticInducedCapacity_eq_card_iff (k := k) G)

/-- For `n ≥ 2`, the variance proxy `(n - 1) / 4` from the vertex-block
bounded-differences estimate is strictly positive. -/
theorem cochromaticVarianceProxy_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < (((n - 1 : ℕ) : ℝ) / 4) := by
  have hnm1 : 0 < n - 1 := by omega
  exact div_pos (by exact_mod_cast hnm1) (by norm_num)

/-- Graph-specific rare-seed inversion (manuscript display (10.7)).

For `n ≥ 2`, if full `k`-cocolourability has probability at least
`exp (-Lambda)`, then the deficit between the endpoint `n` and the actual
expectation of the largest induced `k`-cocolourable subgraph is at most the
displayed sub-Gaussian scale. -/
theorem cochromaticSeedGap_le (n k : ℕ) {Lambda : ℝ}
    (hn : 2 ≤ n) (hLambda : 0 ≤ Lambda)
    (hSeed : Real.exp (-Lambda) ≤
      (randomGraphMeasure n).real {G | CoColorable G k}) :
    (n : ℝ) -
        ∫ G, (cochromaticInducedCapacity G k : ℝ)
          ∂(randomGraphMeasure n) ≤
      Real.sqrt
        (2 * (((n - 1 : ℕ) : ℝ) / 4) * Lambda) := by
  apply rareSeed_gap_le
    (measurable_cochromaticInducedCapacity_real n k)
    (integrable_cochromaticInducedCapacity_real n k)
    (Filter.Eventually.of_forall
      (cochromaticInducedCapacity_real_le_card n k))
    (cochromaticVarianceProxy_pos hn) hLambda
  · simpa only [cochromaticInducedCapacity_levelSet_eq] using hSeed
  · intro t ht
    exact randomGraph_cochromaticInducedCapacity_upperTail n k ht

/-- Algebraically simplified form of `cochromaticSeedGap_le`. -/
theorem cochromaticSeedGap_le_simplified (n k : ℕ) {Lambda : ℝ}
    (hn : 2 ≤ n) (hLambda : 0 ≤ Lambda)
    (hSeed : Real.exp (-Lambda) ≤
      (randomGraphMeasure n).real {G | CoColorable G k}) :
    (n : ℝ) -
        ∫ G, (cochromaticInducedCapacity G k : ℝ)
          ∂(randomGraphMeasure n) ≤
      Real.sqrt ((((n - 1 : ℕ) : ℝ) * Lambda) / 2) := by
  have h := cochromaticSeedGap_le n k hn hLambda hSeed
  have hScale :
      2 * (((n - 1 : ℕ) : ℝ) / 4) * Lambda =
        (((n - 1 : ℕ) : ℝ) * Lambda) / 2 := by
    ring
  simpa only [hScale] using h

end

end Erdos625
