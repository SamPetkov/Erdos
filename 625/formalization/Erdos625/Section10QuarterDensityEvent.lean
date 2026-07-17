import Erdos625.Section10InducedRestriction
import Erdos625.Section10QuarterUnionDecay
import Mathlib.Tactic

/-!
# One finite simultaneous cutoff event for Section X

For each `n`, this module forms the literal finite family of
`quarterDensityCutoff n` vertex subsets and defines the event on which no
member of that family has a lower-quarter complement-edge count.  The event is
measurable, and its failure probability is bounded by the finite union bound
obtained from the fixed-subset tail.

This file stops at that finite bound.  It asserts neither its full-sequence
limit nor quarter density for any larger subset.
-/

namespace Erdos625

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal BigOperators

noncomputable section

/-- The literal finite family of vertex subsets at the Section X cutoff. -/
noncomputable def quarterDensityCutoffSubsets (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.powersetCard (quarterDensityCutoff n)

/-- The lower-quarter bad event for one deterministic vertex subset. -/
noncomputable def inducedComplementLowerQuarterEvent
    (n : ℕ) (S : Finset (Fin n)) : Set (LabeledGraph n) :=
  {G | (inducedComplementEdgeCount (↑S : Set (Fin n)) G : ℝ) ≤
    ((Nat.card (↑S : Set (Fin n))).choose 2 : ℝ) / 4}

/-- The finite simultaneous event that no cutoff-size subset has a
lower-quarter complement-edge count. -/
noncomputable def cutoffComplementQuarterDensityEvent (n : ℕ) : Set (LabeledGraph n) :=
  (⋃ S ∈ quarterDensityCutoffSubsets n,
    inducedComplementLowerQuarterEvent n S)ᶜ

theorem measurableSet_cutoffComplementQuarterDensityEvent (n : ℕ) :
    MeasurableSet (cutoffComplementQuarterDensityEvent n) :=
  Set.toFinite _ |>.measurableSet

/-- The fixed-subset complement lower-tail estimate in the event notation
used by the finite union bound. -/
theorem inducedComplementLowerQuarterEvent_tail
    (n : ℕ) (S : Finset (Fin n)) :
    (randomGraphMeasure n).real (inducedComplementLowerQuarterEvent n S) ≤
      Real.exp (-((S.card.choose 2 : ℕ) : ℝ) / 16) := by
  simpa [inducedComplementLowerQuarterEvent] using
    (randomGraphMeasure_inducedComplementEdgeCount_lowerQuarter n
      (↑S : Set (Fin n)))

theorem cutoffComplementQuarterDensityEvent_compl (n : ℕ) :
    (cutoffComplementQuarterDensityEvent n)ᶜ =
      ⋃ S ∈ quarterDensityCutoffSubsets n,
        inducedComplementLowerQuarterEvent n S := by
  simp [cutoffComplementQuarterDensityEvent]

/-- The exact finite union bound, retaining one summand for each literal
cutoff subset. -/
theorem cutoffComplementQuarterDensityEvent_failure_le_sum
    (n : ℕ) :
    (randomGraphMeasure n).real (cutoffComplementQuarterDensityEvent n)ᶜ ≤
      ∑ S ∈ quarterDensityCutoffSubsets n,
        (randomGraphMeasure n).real (inducedComplementLowerQuarterEvent n S) := by
  rw [cutoffComplementQuarterDensityEvent_compl]
  exact measureReal_biUnion_finset_le _ _

theorem quarterDensityCutoffSubsets_card (n : ℕ) :
    (quarterDensityCutoffSubsets n).card = n.choose (quarterDensityCutoff n) := by
  simp [quarterDensityCutoffSubsets]

/-- The finite failure probability bound after inserting the fixed-set tail
and counting the literal cutoff-subset family. -/
theorem cutoffComplementQuarterDensityEvent_failure_le
    (n : ℕ) :
    (randomGraphMeasure n).real (cutoffComplementQuarterDensityEvent n)ᶜ ≤
      (Nat.choose n (quarterDensityCutoff n) : ℝ) *
        Real.exp (-((quarterDensityCutoff n).choose 2 : ℕ) / 16 : ℝ) := by
  calc
    (randomGraphMeasure n).real (cutoffComplementQuarterDensityEvent n)ᶜ ≤
        ∑ S ∈ quarterDensityCutoffSubsets n,
          (randomGraphMeasure n).real (inducedComplementLowerQuarterEvent n S) :=
      cutoffComplementQuarterDensityEvent_failure_le_sum n
    _ ≤ ∑ S ∈ quarterDensityCutoffSubsets n,
        Real.exp (-((S.card.choose 2 : ℕ) : ℝ) / 16) := by
      exact Finset.sum_le_sum fun S hS =>
        inducedComplementLowerQuarterEvent_tail n S
    _ = ∑ _S ∈ quarterDensityCutoffSubsets n,
        Real.exp (-((quarterDensityCutoff n).choose 2 : ℕ) / 16 : ℝ) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [(Finset.mem_powersetCard.mp hS).2]
    _ = (Nat.choose n (quarterDensityCutoff n) : ℝ) *
        Real.exp (-((quarterDensityCutoff n).choose 2 : ℕ) / 16 : ℝ) := by
      rw [Finset.sum_const, quarterDensityCutoffSubsets_card, nsmul_eq_mul]

end

end Erdos625
