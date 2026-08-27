import Erdos625.Section9ActualResidualWeightedEmbedding
import Erdos625.Section9CyclePolymerBound

/-!
# Section IX: actual-residual `ENNReal` polymer bridge

This module gives a finite, nonnegative-extended-real version of the
actual-residual polymer-product estimate.  It reconstructs the finite
even-subgraph decomposition locally: an even edge set is written as a
recoverable, pairwise edge-disjoint family of inclusion-minimal even edge
sets.  The actual residual family is then embedded into the unrestricted
even-edge family using the proved literal-family inclusion.

The result is only a finite algebraic estimate.  It does not identify the
conditioned residual law, connect the weights to `residualQ`, bound the
polymer product by a traversal series, or prove any Section IX probability
estimate.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- Product of the `ENNReal` cell weights on the edges of `F` outside `M`. -/
def edgeWeightOutsideENN
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (q : A -> B -> ENNReal) (M F : Finset (A × B)) : ENNReal :=
  ∏ e ∈ F \ M, q e.1 e.2

private lemma ennreal_bipartiteEven_sdiff
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {D F : Finset (A × B)} (hDF : D ⊆ F)
    (hF : IsBipartiteEven F) (hD : IsBipartiteEven D) :
    IsBipartiteEven (F \ D) := by
  constructor
  · intro a
    have h_card_diff :
        Finset.card (Finset.filter (fun e => e.1 = a) F) =
          Finset.card (Finset.filter (fun e => e.1 = a) D) +
            Finset.card (Finset.filter (fun e => e.1 = a) (F \ D)) := by
      rw [← Finset.card_union_of_disjoint]
      · congr with e
        by_cases he : e ∈ D <;> aesop
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ =>
          Finset.mem_sdiff.mp (Finset.mem_filter.mp hx₂).1 |>.2
            (Finset.mem_filter.mp hx₁).1
    replace h_card_diff := congr_arg Even h_card_diff
    simp_all +decide [parity_simps]
    exact (h_card_diff.mp (hF.1 a)).mp (hD.1 a)
  · intro b
    have h_card_diff :
        Finset.card (Finset.filter (fun e => e.2 = b) F) =
          Finset.card (Finset.filter (fun e => e.2 = b) D) +
            Finset.card (Finset.filter (fun e => e.2 = b) (F \ D)) := by
      rw [← Finset.card_union_of_disjoint]
      · congr with e
        by_cases he : e ∈ D <;> aesop
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ =>
          Finset.mem_sdiff.mp (Finset.mem_filter.mp hx₂).1 |>.2
            (Finset.mem_filter.mp hx₁).1
    replace h_card_diff := congr_arg Even h_card_diff
    simp_all +decide [parity_simps]
    exact (h_card_diff.mp (hF.2 b)).mp (hD.2 b)

private lemma ennreal_exists_minimal_even_subset
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {F : Finset (A × B)} (hF : IsBipartiteEven F) (hne : F.Nonempty) :
    ∃ C, C ⊆ F ∧ IsSimpleBipartiteCycle C := by
  obtain ⟨C, hC⟩ :
      ∃ C ∈ {S : Finset (A × B) | S ⊆ F ∧ IsBipartiteEven S ∧ S.Nonempty},
        ∀ D ∈ {S : Finset (A × B) | S ⊆ F ∧ IsBipartiteEven S ∧ S.Nonempty},
          C.card ≤ D.card := by
    apply_rules [Set.exists_min_image]
    · exact Set.toFinite _
    · exact ⟨F, ⟨Finset.Subset.refl _, hF, hne⟩⟩
  refine ⟨C, hC.1.1, hC.1.2.1, hC.1.2.2, ?_⟩
  intro D hDC hD hDne
  exact Finset.eq_of_subset_of_card_le hDC
    (hC.2 D ⟨Finset.Subset.trans hDC hC.1.1, hD, hDne⟩ |>
      le_trans <| by simp +decide)

private lemma ennreal_exists_disjoint_cycle_decomposition
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (F : Finset (A × B)) (hF : IsBipartiteEven F) :
    ∃ s : Finset (Finset (A × B)),
      s ⊆ simpleBipartiteCycles A B ∧
      F = s.biUnion id ∧
      (∀ C₁ ∈ s, ∀ C₂ ∈ s, C₁ ≠ C₂ → Disjoint C₁ C₂) := by
  induction' F using Finset.strongInduction with F ih
  by_cases hF_empty : F = ∅
  · exact ⟨∅, by simp +decide [hF_empty]⟩
  · obtain ⟨C, hC⟩ : ∃ C ⊆ F, IsSimpleBipartiteCycle C := by
      exact ennreal_exists_minimal_even_subset hF
        (Finset.nonempty_of_ne_empty hF_empty) |>
          fun ⟨C, hC₁, hC₂⟩ => ⟨C, hC₁, hC₂⟩
    obtain ⟨s, hs⟩ :
        ∃ s ⊆ simpleBipartiteCycles A B,
          F \ C = s.biUnion id ∧
            ∀ C₁ ∈ s, ∀ C₂ ∈ s, C₁ ≠ C₂ → Disjoint C₁ C₂ := by
      apply ih (F \ C)
      · simp_all +decide [Finset.ssubset_def, Finset.subset_iff]
        exact Exists.elim hC.2.2.1 fun x hx => ⟨_, _, hC.1 _ _ hx, hx⟩
      · exact ennreal_bipartiteEven_sdiff hC.1 hF hC.2.1
    refine ⟨Insert.insert C s, ?_, ?_, ?_⟩ <;>
      simp_all +decide [Finset.subset_iff]
    · unfold simpleBipartiteCycles
      aesop
    · grind
    · simp_all +decide [Finset.ext_iff, Finset.disjoint_left]
      grind +ring

private lemma ennreal_biUnion_recovery_injective
    {α : Type*} [DecidableEq α]
    (U : Finset (Finset α)) (s : Finset α → Finset (Finset α))
    (hrecover : ∀ F ∈ U, F = (s F).biUnion id) :
    ∀ F ∈ U, ∀ G ∈ U, s F = s G → F = G := by
  intro F hF G hG hFG
  rw [hrecover F hF, hrecover G hG, hFG]

private lemma edgeWeightOutsideENN_biUnion
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (q : A → B → ENNReal) (M : Finset (A × B))
    (s : Finset (Finset (A × B)))
    (hdisj : ∀ C₁ ∈ s, ∀ C₂ ∈ s, C₁ ≠ C₂ → Disjoint C₁ C₂) :
    edgeWeightOutsideENN q M (s.biUnion id) =
      ∏ C ∈ s, edgeWeightOutsideENN q M C := by
  unfold edgeWeightOutsideENN
  rw [← Finset.prod_biUnion]
  · rcongr e
    aesop
  · exact fun x hx y hy hxy =>
      Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset
        (hdisj x hx y hy hxy)

/-- The finite `ENNReal` polymer-product bound for all even bipartite edge
sets.  It uses no finiteness or positivity hypothesis on the weights beyond
their `ENNReal` type. -/
theorem weighted_evenSubgraph_ennreal_polymer_product
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ENNReal) (M : Finset (A × B)) :
    (∑ F ∈ bipartiteEvenEdgeSets A B, edgeWeightOutsideENN q M F) ≤
      ∏ C ∈ simpleBipartiteCycles A B,
        (1 + edgeWeightOutsideENN q M C) := by
  have h_decomp :
      ∀ F ∈ bipartiteEvenEdgeSets A B,
        ∃ s : Finset (Finset (A × B)),
          s ⊆ simpleBipartiteCycles A B ∧
          F = s.biUnion id ∧
          (∀ C₁ ∈ s, ∀ C₂ ∈ s, C₁ ≠ C₂ → Disjoint C₁ C₂) := by
    intro F hF
    exact ennreal_exists_disjoint_cycle_decomposition F (by
      unfold bipartiteEvenEdgeSets at hF
      aesop)
  choose! s hs using h_decomp
  have h_inj := ennreal_biUnion_recovery_injective
    (bipartiteEvenEdgeSets A B) s (fun F hF ↦ (hs F hF).2.1)
  have h_sum_prod :
      ∑ F ∈ bipartiteEvenEdgeSets A B, edgeWeightOutsideENN q M F ≤
        ∑ s' ∈ Finset.powerset (simpleBipartiteCycles A B),
          ∏ C ∈ s', edgeWeightOutsideENN q M C := by
    have h_sum_prod :
        ∑ F ∈ bipartiteEvenEdgeSets A B, edgeWeightOutsideENN q M F ≤
          ∑ s' ∈ Finset.image s (bipartiteEvenEdgeSets A B),
            ∏ C ∈ s', edgeWeightOutsideENN q M C := by
      rw [Finset.sum_image]
      · refine Finset.sum_le_sum fun F hF => ?_
        rw [(hs F hF).2.1, edgeWeightOutsideENN_biUnion]
        · rw [← (hs F hF).2.1]
        · exact (hs F hF).2.2
      · exact h_inj
    apply le_trans h_sum_prod
    apply Finset.sum_le_sum_of_subset
    exact Finset.image_subset_iff.mpr fun F hF =>
      Finset.mem_powerset.mpr (hs F hF).1
  convert h_sum_prod using 1
  simp +decide [add_comm, Finset.prod_add]

local instance fintypeActualResidualEvenEdgeFamilyENNReal
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (cellCount : A → B → ℕ) (M : Finset (A × B)) :
    Fintype (ActualResidualEvenEdgeFamily cellCount
      (fun a b => (a, b) ∈ M)) := by
  letI : Finite (ActualResidualEvenEdgeFamily cellCount
      (fun a b => (a, b) ∈ M)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- The literal actual residual even-edge family is bounded by the finite
`ENNReal` polymer product.  The matching hypothesis is retained for the
Section IX interface; this finite algebraic estimate only uses `M` to omit
the corresponding edge weights. -/
theorem sum_actualResidualEvenEdgeFamily_ennreal_weight_le_polymer_product
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (cellCount : A → B → ℕ) (M : Finset (A × B))
    (q : A → B → ENNReal)
    (_hM : IsBipartiteMatching M) :
    (∑ F : ActualResidualEvenEdgeFamily cellCount
        (fun a b => (a, b) ∈ M),
      edgeWeightOutsideENN q M F.1) ≤
      ∏ C ∈ simpleBipartiteCycles A B,
        (1 + edgeWeightOutsideENN q M C) := by
  calc
    (∑ F : ActualResidualEvenEdgeFamily cellCount
        (fun a b => (a, b) ∈ M),
      edgeWeightOutsideENN q M F.1) ≤
        ∑ F ∈ bipartiteEvenEdgeSets A B, edgeWeightOutsideENN q M F := by
      simpa only [edgeWeightOutsideENN] using
        (sum_actualResidualEvenEdgeFamily_weight_le_all_even cellCount M q)
    _ ≤ ∏ C ∈ simpleBipartiteCycles A B,
        (1 + edgeWeightOutsideENN q M C) :=
      weighted_evenSubgraph_ennreal_polymer_product q M

#print axioms weighted_evenSubgraph_ennreal_polymer_product
#print axioms sum_actualResidualEvenEdgeFamily_ennreal_weight_le_polymer_product

end

end Erdos625
