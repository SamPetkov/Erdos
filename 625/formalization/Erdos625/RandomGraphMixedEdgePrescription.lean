import Erdos625.ColoringProfileFirstMoment
import Erdos625.RandomGraphUniformLaw
import Mathlib.Tactic

namespace Erdos625

open MeasureTheory

noncomputable section

/-!
# Simultaneous present/absent edge prescriptions

For a fixed pair of edge-disjoint labelled graphs `Hpresent` and `Habsent`,
the event below asks that every edge of `Hpresent` occur and that every edge
of `Habsent` fail to occur.  The proof is deliberately finite: after the
prescribed edges are fixed, the remaining graph is an arbitrary subgraph of
the complement of their union.
-/

/-- The event that all `Hpresent` edges occur and all `Habsent` edges do not
occur. -/
def mixedEdgePrescriptionEvent {n : ℕ}
    (Hpresent Habsent : LabeledGraph n) : Set (LabeledGraph n) :=
  {G | Hpresent ≤ G ∧ G ≤ Habsentᶜ}

/-- Finite sample spaces make a mixed prescription event measurable. -/
theorem measurableSet_mixedEdgePrescriptionEvent {n : ℕ}
    (Hpresent Habsent : LabeledGraph n) :
    MeasurableSet (mixedEdgePrescriptionEvent Hpresent Habsent) :=
  Set.toFinite (mixedEdgePrescriptionEvent Hpresent Habsent) |>.measurableSet

private theorem freeGraph_le_union_compl_of_mem_mixedEdgePrescriptionEvent
    {n : ℕ} {Hpresent Habsent G : LabeledGraph n}
    (h : G ∈ mixedEdgePrescriptionEvent Hpresent Habsent) :
    G \ Hpresent ≤ (Hpresent ⊔ Habsent)ᶜ := by
  rw [mixedEdgePrescriptionEvent, Set.mem_setOf_eq] at h
  rw [compl_sup]
  apply le_inf
  · exact le_compl_iff_disjoint_right.mpr (by
      simpa using (disjoint_sdiff_self_left : Disjoint (G \ Hpresent) Hpresent))
  · exact sdiff_le.trans h.2

private theorem present_sup_free_mem_mixedEdgePrescriptionEvent
    {n : ℕ} {Hpresent Habsent F : LabeledGraph n}
    (hdis : Disjoint Hpresent Habsent)
    (hF : F ≤ (Hpresent ⊔ Habsent)ᶜ) :
    Hpresent ⊔ F ∈ mixedEdgePrescriptionEvent Hpresent Habsent := by
  rw [mixedEdgePrescriptionEvent, Set.mem_setOf_eq]
  constructor
  · exact le_sup_left
  · apply sup_le
    · exact le_compl_iff_disjoint_right.mpr hdis
    · exact hF.trans (compl_le_compl le_sup_right)

private theorem freeGraph_disjoint_present_of_le_union_compl
    {n : ℕ} {Hpresent Habsent F : LabeledGraph n}
    (hF : F ≤ (Hpresent ⊔ Habsent)ᶜ) :
    Disjoint Hpresent F := by
  apply Disjoint.symm
  apply le_compl_iff_disjoint_right.mp
  exact hF.trans (compl_le_compl le_sup_left)

/-- Remove the prescribed-present edges from a graph satisfying a mixed
prescription; conversely, add them back to an arbitrary graph on the free
edges. -/
noncomputable def mixedEdgePrescriptionEquiv {n : ℕ}
    (Hpresent Habsent : LabeledGraph n) (hdis : Disjoint Hpresent Habsent) :
    {G : LabeledGraph n // G ∈ mixedEdgePrescriptionEvent Hpresent Habsent} ≃
      {F : LabeledGraph n // F ≤ (Hpresent ⊔ Habsent)ᶜ} where
  toFun G := ⟨G.1 \ Hpresent,
    freeGraph_le_union_compl_of_mem_mixedEdgePrescriptionEvent G.2⟩
  invFun F := ⟨Hpresent ⊔ F.1,
    present_sup_free_mem_mixedEdgePrescriptionEvent hdis F.2⟩
  left_inv G := by
    apply Subtype.ext
    change Hpresent ⊔ (G.1 \ Hpresent) = G.1
    rw [sup_comm]
    exact sdiff_sup_cancel G.2.1
  right_inv F := by
    apply Subtype.ext
    exact (freeGraph_disjoint_present_of_le_union_compl F.2).sup_sdiff_cancel_left

/-- The two prescribed edge sets have additive cardinality when they are
edge-disjoint. -/
private theorem ncard_edgeSet_sup_of_disjoint {n : ℕ}
    {Hpresent Habsent : LabeledGraph n}
    (hdis : Disjoint Hpresent Habsent) :
    (Hpresent ⊔ Habsent).edgeSet.ncard =
      Hpresent.edgeSet.ncard + Habsent.edgeSet.ncard := by
  rw [SimpleGraph.edgeSet_sup]
  exact Set.ncard_union_eq (SimpleGraph.disjoint_edgeSet.mpr hdis)

/-- The number of labelled graphs satisfying a fixed edge-disjoint mixed
prescription. -/
theorem ncard_mixedEdgePrescriptionEvent {n : ℕ}
    (Hpresent Habsent : LabeledGraph n)
    (hdis : Disjoint Hpresent Habsent) :
    (mixedEdgePrescriptionEvent Hpresent Habsent).ncard =
      2 ^ (n.choose 2 -
        (Hpresent.edgeSet.ncard + Habsent.edgeSet.ncard)) := by
  change Nat.card {G : LabeledGraph n //
    G ∈ mixedEdgePrescriptionEvent Hpresent Habsent} = _
  calc
    Nat.card {G : LabeledGraph n //
        G ∈ mixedEdgePrescriptionEvent Hpresent Habsent} =
        Nat.card {F : LabeledGraph n // F ≤ (Hpresent ⊔ Habsent)ᶜ} :=
      Nat.card_congr (mixedEdgePrescriptionEquiv Hpresent Habsent hdis)
    _ = 2 ^ ((Hpresent ⊔ Habsent)ᶜ).edgeSet.ncard :=
      card_graphBelow ((Hpresent ⊔ Habsent)ᶜ)
    _ = 2 ^ (n.choose 2 -
        (Hpresent.edgeSet.ncard + Habsent.edgeSet.ncard)) := by
      rw [ncard_edgeSet_compl,
        ncard_edgeSet_sup_of_disjoint hdis]

/-- Exact `G(n,1/2)` probability of enforcing disjoint present and absent
edge prescriptions simultaneously. -/
theorem randomGraphMeasure_mixedEdgePrescriptionEvent {n : ℕ}
    (Hpresent Habsent : LabeledGraph n)
    (hdis : Disjoint Hpresent Habsent) :
    randomGraphMeasure n (mixedEdgePrescriptionEvent Hpresent Habsent) =
      (1 / 2 : ENNReal) ^
        (Hpresent.edgeSet.ncard + Habsent.edgeSet.ncard) := by
  classical
  let T := (Finset.univ : Finset (LabeledGraph n)).filter
    fun G ↦ G ∈ mixedEdgePrescriptionEvent Hpresent Habsent
  have hcard : T.card =
      2 ^ (n.choose 2 -
        (Hpresent.edgeSet.ncard + Habsent.edgeSet.ncard)) := by
    calc
      T.card = Fintype.card {G : LabeledGraph n //
          G ∈ mixedEdgePrescriptionEvent Hpresent Habsent} := by
        simp [T]
      _ = Nat.card {G : LabeledGraph n //
          G ∈ mixedEdgePrescriptionEvent Hpresent Habsent} := by
        rw [Nat.card_eq_fintype_card]
      _ = 2 ^ (n.choose 2 -
          (Hpresent.edgeSet.ncard + Habsent.edgeSet.ncard)) := by
        change (mixedEdgePrescriptionEvent Hpresent Habsent).ncard = _
        exact ncard_mixedEdgePrescriptionEvent Hpresent Habsent hdis
  have hunion : (Hpresent ⊔ Habsent).edgeSet.ncard ≤ n.choose 2 := by
    calc
      (Hpresent ⊔ Habsent).edgeSet.ncard ≤
          (Sym2.diagSetᶜ : Set (Sym2 (Fin n))).ncard :=
        Set.ncard_le_ncard (Hpresent ⊔ Habsent).edgeSet_subset_compl_diagSet
          (Set.toFinite (Sym2.diagSetᶜ : Set (Sym2 (Fin n))))
      _ = n.choose 2 := by simpa using Sym2.ncard_diagSet_compl (Fin n)
  have hprescribed :
      Hpresent.edgeSet.ncard + Habsent.edgeSet.ncard ≤ n.choose 2 := by
    rw [← ncard_edgeSet_sup_of_disjoint hdis]
    exact hunion
  calc
    randomGraphMeasure n (mixedEdgePrescriptionEvent Hpresent Habsent) =
        randomGraphMeasure n (T : Set (LabeledGraph n)) := by
      congr 1
      ext G
      simp [T]
    _ = ∑ G ∈ T, randomGraphMeasure n {G} := by
      rw [MeasureTheory.sum_measure_singleton]
    _ = ∑ _G ∈ T, (1 / 2 : ENNReal) ^ n.choose 2 := by
      simp_rw [randomGraphMeasure_singleton_uniform]
    _ = (2 : ENNReal) ^
        (n.choose 2 - (Hpresent.edgeSet.ncard + Habsent.edgeSet.ncard)) *
        (1 / 2 : ENNReal) ^ n.choose 2 := by
      simp [Finset.sum_const, hcard, nsmul_eq_mul]
    _ = (1 / 2 : ENNReal) ^
        (Hpresent.edgeSet.ncard + Habsent.edgeSet.ncard) := by
      conv_lhs =>
        rhs
        rw [show n.choose 2 =
          (n.choose 2 -
            (Hpresent.edgeSet.ncard + Habsent.edgeSet.ncard)) +
            (Hpresent.edgeSet.ncard + Habsent.edgeSet.ncard) by
              exact (Nat.sub_add_cancel hprescribed).symm,
          pow_add]
      rw [← mul_assoc, ← mul_pow]
      rw [div_eq_mul_inv, one_mul,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]

end

end Erdos625
