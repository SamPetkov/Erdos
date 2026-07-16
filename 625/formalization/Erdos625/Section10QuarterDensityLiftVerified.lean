import Erdos625.Section10QuarterDensityEvent
import Erdos625.QuarterDensityDegree
import Mathlib.Tactic

/-!
# Section X: deterministic density lift from the cutoff event

For a fixed graph sample, membership in the finite simultaneous cutoff event
means that every vertex subset of exactly `quarterDensityCutoff n` vertices
has more than one quarter of its possible complement edges.  This module
converts that strict edge-count fact into the denominator-free predicate
`QuarterDenseOn` and invokes the already checked finite averaging lemma to
extend the conclusion to larger subsets.

The larger-subset statement explicitly assumes that the cutoff is at least
two, as required by `quarterDense_all_larger_of_all_exact`.  No probability
limit, neighbourhood chain, rounding estimate, or greedy-colouring result is
proved here.
-/

namespace Erdos625

open Finset

noncomputable section

private theorem inducedComplementEdgeCount_eq_induced_edgeFinset_card_verified
    (n : ℕ) (S : Finset (Fin n)) (G : LabeledGraph n) :
    inducedComplementEdgeCount (↑S : Set (Fin n)) G =
      (Gᶜ.induce (↑S : Set (Fin n))).edgeFinset.card := by
  classical
  change (Gᶜ.induce (↑S : Set (Fin n))).edgeSet.ncard =
    (Gᶜ.induce (↑S : Set (Fin n))).edgeFinset.card
  rw [Set.ncard_eq_toFinset_card']
  rfl

/-- On the finite cutoff event, every subset of exactly the cutoff cardinality
is quarter-dense in the complement graph. -/
theorem cutoffComplementQuarterDensityEvent_quarterDense_exact_verified
    (n : ℕ) (G : LabeledGraph n)
    (hG : G ∈ cutoffComplementQuarterDensityEvent n) :
    ∀ S : Finset (Fin n), S.card = quarterDensityCutoff n →
      QuarterDenseOn Gᶜ S := by
  classical
  intro S hS
  have hScutoff : S ∈ quarterDensityCutoffSubsets n := by
    simp [quarterDensityCutoffSubsets, hS]
  have hGnotUnion : G ∉ ⋃ T ∈ quarterDensityCutoffSubsets n,
      inducedComplementLowerQuarterEvent n T := by
    simpa [cutoffComplementQuarterDensityEvent] using hG
  have hNotBad : ¬ (inducedComplementEdgeCount (↑S : Set (Fin n)) G : ℝ) ≤
      ((Nat.card (↑S : Set (Fin n))).choose 2 : ℝ) / 4 := by
    intro hBad
    apply hGnotUnion
    exact Set.mem_iUnion_of_mem S (Set.mem_iUnion_of_mem hScutoff hBad)
  have hStrict : ((S.card.choose 2 : ℕ) : ℝ) / 4 <
      (inducedComplementEdgeCount (↑S : Set (Fin n)) G : ℝ) := by
    exact lt_of_not_ge (by simpa using hNotBad)
  have hChooseStrict : S.card.choose 2 <
      4 * inducedComplementEdgeCount (↑S : Set (Fin n)) G := by
    have hReal : ((S.card.choose 2 : ℕ) : ℝ) <
        4 * (inducedComplementEdgeCount (↑S : Set (Fin n)) G : ℝ) := by
      nlinarith
    exact_mod_cast hReal
  have hDensityNat : S.card * (S.card - 1) ≤
      8 * inducedComplementEdgeCount (↑S : Set (Fin n)) G := by
    calc
      S.card * (S.card - 1) = 2 * (S.card.choose 2) := by
        rw [Nat.choose_two_right]
        calc
          S.card * (S.card - 1) = (S.card * (S.card - 1) / 2) * 2 :=
            (Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self S.card)).symm
          _ = 2 * (S.card * (S.card - 1) / 2) := Nat.mul_comm _ _
      _ ≤ 2 * (4 * inducedComplementEdgeCount (↑S : Set (Fin n)) G) :=
        Nat.mul_le_mul_left 2 (Nat.le_of_lt hChooseStrict)
      _ = 8 * inducedComplementEdgeCount (↑S : Set (Fin n)) G := by ring
  unfold QuarterDenseOn
  rw [← inducedComplementEdgeCount_eq_induced_edgeFinset_card_verified n S G]
  exact hDensityNat

/-- If the cutoff is at least two, the cutoff event gives quarter density in
the complement graph simultaneously for every larger vertex subset. -/
theorem cutoffComplementQuarterDensityEvent_quarterDense_all_larger_verified
    (n : ℕ) (G : LabeledGraph n)
    (hG : G ∈ cutoffComplementQuarterDensityEvent n)
    (hcutoff : 2 ≤ quarterDensityCutoff n) :
    ∀ S : Finset (Fin n), quarterDensityCutoff n ≤ S.card →
      QuarterDenseOn Gᶜ S := by
  exact quarterDense_all_larger_of_all_exact Gᶜ (quarterDensityCutoff n)
    hcutoff (cutoffComplementQuarterDensityEvent_quarterDense_exact_verified n G hG)

#print axioms cutoffComplementQuarterDensityEvent_quarterDense_exact_verified
#print axioms cutoffComplementQuarterDensityEvent_quarterDense_all_larger_verified

end

end Erdos625
