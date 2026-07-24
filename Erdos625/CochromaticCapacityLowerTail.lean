import Erdos625.CochromaticSeedGap

/-!
# Lower-tail amplification for induced cochromatic capacity

This module closes the one-sided lower-tail step corresponding to manuscript
display (10.8).  The concentration estimate is derived from the negation of
the audited sub-Gaussian MGF on the exact vertex-block product space and then
transported to `G(n, 1/2)`.  Combining it with the rare-seed endpoint gap
gives an explicit failure-probability estimate with no two-sided factor.
-/

open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open ProbabilityTheory

namespace Erdos625

noncomputable section

/-- One-sided bounded-differences lower tail for induced cochromatic
capacity under the actual random-graph law.  The center is the genuine
`G(n, 1/2)` integral, and the chosen vertex-block proxy is `(n - 1) / 4`.

For `n ≤ 1` the totalized exponential expression is still well-formed but
the bound is generally vacuous; the amplification theorem below assumes
`n ≥ 2` so that the proxy is strictly positive. -/
theorem randomGraph_cochromaticInducedCapacity_lowerTail
    (n k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (randomGraphMeasure n).real
        {G | t ≤
          ∫ H, (cochromaticInducedCapacity H k : ℝ)
              ∂(randomGraphMeasure n) -
            (cochromaticInducedCapacity G k : ℝ)} ≤
      Real.exp
        (-t ^ 2 / (2 * (((n - 1 : ℕ) : ℝ) / 4))) := by
  rw [integral_randomGraphMeasure_eq_randomGraphBlockExpectation]
  have hmgf :=
    (blockBoundedDifferences_hasSubgaussianMGF
      (Omega := fun v : Fin n ↦ VertexBlock v)
      (cochromaticInducedCapacity_hasBlockOscillation n k)).neg
  have hb := hmgf.measure_ge_le ht
  change (randomGraphMeasure n
    {G | t ≤
      randomGraphBlockExpectation
          (fun H : LabeledGraph n ↦
            (cochromaticInducedCapacity H k : ℝ)) -
        (cochromaticInducedCapacity G k : ℝ)}).toReal ≤ _
  rw [← vertexBlockMeasure_preimage_eq_randomGraphMeasure]
  simpa only [Set.preimage_setOf_eq, randomGraphBlockExpectation,
    vertexBlockMeasure, Measure.real, Pi.neg_apply, neg_sub,
    blockVariance_noninitialUnitOscillation] using hb

/-- Rare-seed amplification with the exact one-sided failure probability
(manuscript display (10.8)).

For `n ≥ 2`, suppose that full `k`-cocolourability has probability at least
`exp (-Lambda)`.  Then, for every `r ≥ 0`, the probability that the deficit
`n - cochromaticInducedCapacity` is at least

`sqrt ((n - 1) * Lambda / 2) + sqrt ((n - 1) * r / 2)`

is at most `exp (-r)`.  Both events use non-strict inequalities: the failure
event is included pointwise in the lower-tail event at the second square-root
threshold. -/
theorem randomGraph_cochromaticInducedCapacity_failureProbability_le
    (n k : ℕ) {Lambda r : ℝ}
    (hn : 2 ≤ n) (hLambda : 0 ≤ Lambda) (hr : 0 ≤ r)
    (hSeed : Real.exp (-Lambda) ≤
      (randomGraphMeasure n).real {G | CoColorable G k}) :
    (randomGraphMeasure n).real
        {G |
          Real.sqrt ((((n - 1 : ℕ) : ℝ) * Lambda) / 2) +
              Real.sqrt ((((n - 1 : ℕ) : ℝ) * r) / 2) ≤
            (n : ℝ) - (cochromaticInducedCapacity G k : ℝ)} ≤
      Real.exp (-r) := by
  have hGap := cochromaticSeedGap_le_simplified n k hn hLambda hSeed
  have hSubset :
      {G : LabeledGraph n |
          Real.sqrt ((((n - 1 : ℕ) : ℝ) * Lambda) / 2) +
              Real.sqrt ((((n - 1 : ℕ) : ℝ) * r) / 2) ≤
            (n : ℝ) - (cochromaticInducedCapacity G k : ℝ)} ⊆
        {G : LabeledGraph n |
          Real.sqrt ((((n - 1 : ℕ) : ℝ) * r) / 2) ≤
            ∫ H, (cochromaticInducedCapacity H k : ℝ)
                ∂(randomGraphMeasure n) -
              (cochromaticInducedCapacity G k : ℝ)} := by
    intro G hFailure
    change
      Real.sqrt ((((n - 1 : ℕ) : ℝ) * Lambda) / 2) +
          Real.sqrt ((((n - 1 : ℕ) : ℝ) * r) / 2) ≤
        (n : ℝ) - (cochromaticInducedCapacity G k : ℝ) at hFailure
    change
      Real.sqrt ((((n - 1 : ℕ) : ℝ) * r) / 2) ≤
        ∫ H, (cochromaticInducedCapacity H k : ℝ)
            ∂(randomGraphMeasure n) -
          (cochromaticInducedCapacity G k : ℝ)
    linarith
  have hTail := randomGraph_cochromaticInducedCapacity_lowerTail n k
    (Real.sqrt_nonneg ((((n - 1 : ℕ) : ℝ) * r) / 2))
  have hnm1Nat : 0 < n - 1 := by omega
  have hnm1 : 0 < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hnm1Nat
  have hSqrtArg :
      0 ≤ (((n - 1 : ℕ) : ℝ) * r) / 2 := by positivity
  have hSqrtSq :
      (Real.sqrt ((((n - 1 : ℕ) : ℝ) * r) / 2)) ^ 2 =
        (((n - 1 : ℕ) : ℝ) * r) / 2 :=
    Real.sq_sqrt hSqrtArg
  have hExponent :
      -(Real.sqrt ((((n - 1 : ℕ) : ℝ) * r) / 2)) ^ 2 /
          (2 * (((n - 1 : ℕ) : ℝ) / 4)) = -r := by
    rw [hSqrtSq]
    field_simp [ne_of_gt hnm1]
    ring
  calc
    (randomGraphMeasure n).real
        {G |
          Real.sqrt ((((n - 1 : ℕ) : ℝ) * Lambda) / 2) +
              Real.sqrt ((((n - 1 : ℕ) : ℝ) * r) / 2) ≤
            (n : ℝ) - (cochromaticInducedCapacity G k : ℝ)} ≤
        (randomGraphMeasure n).real
          {G |
            Real.sqrt ((((n - 1 : ℕ) : ℝ) * r) / 2) ≤
              ∫ H, (cochromaticInducedCapacity H k : ℝ)
                  ∂(randomGraphMeasure n) -
                (cochromaticInducedCapacity G k : ℝ)} :=
      measureReal_mono hSubset
    _ ≤ Real.exp
          (-(Real.sqrt ((((n - 1 : ℕ) : ℝ) * r) / 2)) ^ 2 /
            (2 * (((n - 1 : ℕ) : ℝ) / 4))) := hTail
    _ = Real.exp (-r) := by rw [hExponent]

/-- Strict-inequality spelling of the same failure event.  It follows from
the stronger non-strict estimate above by event inclusion. -/
theorem randomGraph_cochromaticInducedCapacity_strictFailureProbability_le
    (n k : ℕ) {Lambda r : ℝ}
    (hn : 2 ≤ n) (hLambda : 0 ≤ Lambda) (hr : 0 ≤ r)
    (hSeed : Real.exp (-Lambda) ≤
      (randomGraphMeasure n).real {G | CoColorable G k}) :
    (randomGraphMeasure n).real
        {G |
          Real.sqrt ((((n - 1 : ℕ) : ℝ) * Lambda) / 2) +
              Real.sqrt ((((n - 1 : ℕ) : ℝ) * r) / 2) <
            (n : ℝ) - (cochromaticInducedCapacity G k : ℝ)} ≤
      Real.exp (-r) := by
  calc
    (randomGraphMeasure n).real
        {G |
          Real.sqrt ((((n - 1 : ℕ) : ℝ) * Lambda) / 2) +
              Real.sqrt ((((n - 1 : ℕ) : ℝ) * r) / 2) <
            (n : ℝ) - (cochromaticInducedCapacity G k : ℝ)} ≤
        (randomGraphMeasure n).real
          {G |
            Real.sqrt ((((n - 1 : ℕ) : ℝ) * Lambda) / 2) +
                Real.sqrt ((((n - 1 : ℕ) : ℝ) * r) / 2) ≤
              (n : ℝ) - (cochromaticInducedCapacity G k : ℝ)} := by
      apply measureReal_mono (h₂ := by finiteness)
      intro G hG
      change
        Real.sqrt ((((n - 1 : ℕ) : ℝ) * Lambda) / 2) +
            Real.sqrt ((((n - 1 : ℕ) : ℝ) * r) / 2) <
          (n : ℝ) - (cochromaticInducedCapacity G k : ℝ) at hG
      exact hG.le
    _ ≤ Real.exp (-r) :=
      randomGraph_cochromaticInducedCapacity_failureProbability_le
        n k hn hLambda hr hSeed

end

end Erdos625
