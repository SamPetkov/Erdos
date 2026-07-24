import Erdos625.Section9ActualResidualFamily
import Erdos625.Section9CyclePolymerBound

/-!
# Section IX: weighted actual-residual subfamily embedding

The actual residual even-edge family is only a subfamily of the unrestricted
finite family of all even bipartite edge sets.  This module records the exact
one-sided weighted inclusion for arbitrary nonnegative-extended-real cell
weights.  It does not identify a residual probability law, supply an ENNReal
polymer bound, or encode cycles as walks.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

local instance fintypeActualResidualEvenEdgeFamily
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (cellCount : A → B → ℕ) (M : Finset (A × B)) :
    Fintype (ActualResidualEvenEdgeFamily cellCount
      (fun a b => (a, b) ∈ M)) := by
  letI : Finite (ActualResidualEvenEdgeFamily cellCount
      (fun a b => (a, b) ∈ M)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- The two finite presentations of bipartite evenness are equivalent. -/
theorem bipartiteEvenEdgeSet_iff_isBipartiteEven
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (F : Finset (A × B)) :
    BipartiteEvenEdgeSet F ↔ IsBipartiteEven F := by
  have hrowCard (a : A) :
      (F.filter (fun e => e.1 = a)).card = (bipartiteEdgeRow F a).card := by
    let emb : B ↪ A × B :=
      ⟨fun b => (a, b), fun x y h => Prod.mk.inj h |>.2⟩
    have hmap : (bipartiteEdgeRow F a).map emb =
        F.filter (fun e => e.1 = a) := by
      ext e
      rcases e with ⟨a', b⟩
      simp [bipartiteEdgeRow, emb]
      constructor
      · rintro ⟨hF, ha⟩
        subst a'
        exact ⟨hF, rfl⟩
      · rintro ⟨hF, ha⟩
        subst a'
        exact ⟨hF, rfl⟩
    simpa using (congrArg Finset.card hmap).symm
  have hcolumnCard (b : B) :
      (F.filter (fun e => e.2 = b)).card =
        (bipartiteEdgeColumn F b).card := by
    let emb : A ↪ A × B :=
      ⟨fun a => (a, b), fun x y h => Prod.mk.inj h |>.1⟩
    have hmap : (bipartiteEdgeColumn F b).map emb =
        F.filter (fun e => e.2 = b) := by
      ext e
      rcases e with ⟨a, b'⟩
      simp [bipartiteEdgeColumn, emb]
      constructor
      · rintro ⟨hF, hb⟩
        subst b'
        exact ⟨hF, rfl⟩
      · rintro ⟨hF, hb⟩
        subst b'
        exact ⟨hF, rfl⟩
    simpa using (congrArg Finset.card hmap).symm
  constructor
  · rintro ⟨hrow, hcolumn⟩
    constructor
    · intro a
      rw [hrowCard a]
      exact hrow a
    · intro b
      rw [hcolumnCard b]
      exact hcolumn b
  · rintro ⟨hrow, hcolumn⟩
    constructor
    · intro a
      rw [← hrowCard a]
      exact hrow a
    · intro b
      rw [← hcolumnCard b]
      exact hcolumn b

/-- The actual residual even-edge family is a weighted subfamily of all
finite even bipartite edge sets.  This is an exact one-sided inclusion bound,
not an equality of sums. -/
theorem sum_actualResidualEvenEdgeFamily_weight_le_all_even
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (cellCount : A → B → ℕ) (M : Finset (A × B))
    (q : A → B → ℝ≥0∞) :
    (∑ F : ActualResidualEvenEdgeFamily cellCount
        (fun a b => (a, b) ∈ M),
      ∏ e ∈ F.1 \ M, q e.1 e.2) ≤
      ∑ F ∈ bipartiteEvenEdgeSets A B,
        ∏ e ∈ F \ M, q e.1 e.2 := by
  classical
  let weight : Finset (A × B) → ℝ≥0∞ :=
    fun F => ∏ e ∈ F \ M, q e.1 e.2
  have hvalInj : Function.Injective
      (fun F : ActualResidualEvenEdgeFamily cellCount
        (fun a b => (a, b) ∈ M) => F.1) :=
    Subtype.val_injective
  have hsubset :
      Finset.image
          (fun F : ActualResidualEvenEdgeFamily cellCount
            (fun a b => (a, b) ∈ M) => F.1)
          Finset.univ ⊆
        bipartiteEvenEdgeSets A B := by
    intro F hF
    rcases Finset.mem_image.mp hF with ⟨G, _, rfl⟩
    simp only [bipartiteEvenEdgeSets, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (bipartiteEvenEdgeSet_iff_isBipartiteEven G.1).mp G.2.1
  change (∑ F : ActualResidualEvenEdgeFamily cellCount
      (fun a b => (a, b) ∈ M), weight F.1) ≤
      ∑ F ∈ bipartiteEvenEdgeSets A B, weight F
  calc
    (∑ F : ActualResidualEvenEdgeFamily cellCount
        (fun a b => (a, b) ∈ M), weight F.1) =
        ∑ F ∈ Finset.image
            (fun G : ActualResidualEvenEdgeFamily cellCount
              (fun a b => (a, b) ∈ M) => G.1)
            Finset.univ, weight F := by
      symm
      rw [Finset.sum_image]
      exact fun _ _ _ _ hxy => hvalInj hxy
    _ ≤ ∑ F ∈ bipartiteEvenEdgeSets A B, weight F := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro F hF hnotmem
      exact bot_le

#print axioms bipartiteEvenEdgeSet_iff_isBipartiteEven
#print axioms sum_actualResidualEvenEdgeFamily_weight_le_all_even

end

end Erdos625
