import Erdos625.Foundation
import Erdos625.GraphModel
import Mathlib.Data.Sym.NatCard
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs

/-!
# Exact formal target

The proposition `Erdos625Statement` is the exact full-sequence probability
claim from the manuscript.  It is deliberately a `def`, not a theorem: this
milestone states the goal without pretending that the analytic and
probabilistic proof chain has already been formalized.
-/

namespace Erdos625

open Filter MeasureTheory

/-- The edge probability `1/2`, packaged as a point of the unit interval. -/
noncomputable def halfProbability : unitInterval :=
  ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

@[simp] theorem toNNReal_halfProbability :
    (unitInterval.toNNReal halfProbability : ENNReal) = 1 / 2 := by
  rw [← ENNReal.toReal_eq_toReal_iff' ENNReal.coe_ne_top (by finiteness)]
  norm_num [halfProbability]

@[simp] theorem toNNReal_symm_halfProbability :
    (unitInterval.toNNReal (unitInterval.symm halfProbability) : ENNReal) =
      1 / 2 := by
  rw [← ENNReal.toReal_eq_toReal_iff' ENNReal.coe_ne_top (by finiteness)]
  norm_num [halfProbability]

/-- The law `G(n,1/2)` on labelled simple graphs with vertex type `Fin n`. -/
noncomputable def randomGraphMeasure (n : ℕ) : Measure (LabeledGraph n) :=
  SimpleGraph.binomialRandom (Fin n) halfProbability

noncomputable instance instIsProbabilityMeasureRandomGraph (n : ℕ) :
    IsProbabilityMeasure (randomGraphMeasure n) := by
  unfold randomGraphMeasure
  infer_instance

/-- The wrapper uses mathlib's binomial-random-graph law; this records its
singleton mass formula on the labelled finite sample space. -/
theorem randomGraphMeasure_singleton (n : ℕ) (G : LabeledGraph n) :
    randomGraphMeasure n {G} =
      (unitInterval.toNNReal halfProbability : ENNReal) ^ G.edgeSet.ncard *
      (unitInterval.toNNReal (unitInterval.symm halfProbability) : ENNReal) ^
        (n.choose 2 - G.edgeSet.ncard) := by
  simp [randomGraphMeasure, SimpleGraph.binomialRandom_singleton]

/-- At edge probability `1/2`, every labelled graph has the same mass. -/
theorem randomGraphMeasure_singleton_uniform (n : ℕ) (G : LabeledGraph n) :
    randomGraphMeasure n {G} = (1 / 2 : ENNReal) ^ n.choose 2 := by
  have hE : G.edgeSet.ncard ≤ n.choose 2 := by
    calc
      G.edgeSet.ncard ≤
          (Sym2.diagSetᶜ : Set (Sym2 (Fin n))).ncard :=
        Set.ncard_le_ncard G.edgeSet_subset_compl_diagSet
          (Set.toFinite (Sym2.diagSetᶜ : Set (Sym2 (Fin n))))
      _ = (Nat.card (Fin n)).choose 2 := Sym2.ncard_diagSet_compl (Fin n)
      _ = n.choose 2 := by simp
  rw [randomGraphMeasure_singleton, toNNReal_halfProbability,
    toNNReal_symm_halfProbability, ← pow_add, Nat.add_sub_of_le hE]

/-- The measurable structure inherited from adjacency makes every singleton
measurable on the finite labelled-graph sample space. -/
instance instMeasurableSingletonClassLabeledGraph (n : ℕ) :
    MeasurableSingletonClass (LabeledGraph n) where
  measurableSet_singleton G := by
    apply SimpleGraph.measurableEmbedding_edgeSet.measurableSet_image.mp
    simp

/-- Graphs whose chromatic/cochromatic gap is at least the explicit manuscript
scale.  The subtraction is in `ℝ`, so it is not truncated natural subtraction. -/
noncomputable def gapEvent (n : ℕ) : Set (LabeledGraph n) :=
  {G | gapScale n ≤
    (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)}

/-- The gap event is measurable.  This matters semantically: its probability
is an ordinary finite-space probability, not merely an outer measure. -/
theorem measurableSet_gapEvent (n : ℕ) : MeasurableSet (gapEvent n) :=
  Set.toFinite (gapEvent n) |>.measurableSet

/-- The probability of the asserted gap event under `G(n,1/2)`. -/
noncomputable def gapProbability (n : ℕ) : ENNReal :=
  randomGraphMeasure n (gapEvent n)

/-- Exact formal statement of the proposed positive resolution of Erdős
Problem 625: the displayed event has probability tending to one along the
full sequence of natural numbers. -/
def Erdos625Statement : Prop :=
  Tendsto gapProbability atTop (nhds 1)

theorem gapProbability_le_one (n : ℕ) : gapProbability n ≤ 1 := by
  calc
    gapProbability n ≤ randomGraphMeasure n Set.univ :=
      measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

/-- Real-valued reformulation matching the probability notation used in the
manuscript. -/
theorem erdos625Statement_iff_real :
    Erdos625Statement ↔
      Tendsto (fun n => (gapProbability n).toReal)
        atTop (nhds (1 : ℝ)) := by
  simpa [Erdos625Statement] using
    (ENNReal.tendsto_toReal_iff
      (fun n => ne_top_of_le_ne_top ENNReal.one_ne_top
        (gapProbability_le_one n))
      ENNReal.one_ne_top).symm

end Erdos625
