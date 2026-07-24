import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Finite weighted even-subgraph polymer bound for Section IX

This module formalizes the finite algebraic and combinatorial polymer bound
used in manuscript (9.15).  Every finite even bipartite edge set is decomposed
into pairwise edge-disjoint inclusion-minimal nonempty even edge sets.  The
decomposition is recoverable from its union, so no injectivity assumption is
added.  The resulting subset sum is bounded by the full polymer product and
then by the exponential of the total polymer weight.

The distinguished edge set `M` is required to be a matching because that is
the Section IX application.  The algebraic estimate itself only uses `M` to
omit those edge weights.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- Every row and every column has even degree in the finite cell set `F`. -/
def IsBipartiteEven
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (F : Finset (A × B)) : Prop :=
  (∀ a, Even (F.filter (fun e ↦ e.1 = a)).card) ∧
  (∀ b, Even (F.filter (fun e ↦ e.2 = b)).card)

/-- An intrinsic finite-edge-set formulation of a simple bipartite cycle:
it is a nonempty inclusion-minimal even edge set. -/
def IsSimpleBipartiteCycle
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (C : Finset (A × B)) : Prop :=
  IsBipartiteEven C ∧ C.Nonempty ∧
    ∀ D : Finset (A × B),
      D ⊆ C → IsBipartiteEven D → D.Nonempty → D = C

/-- A cell set is a bipartite matching: no two cells share a row or column. -/
def IsBipartiteMatching
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) : Prop :=
  (∀ a b₁ b₂, (a, b₁) ∈ M → (a, b₂) ∈ M → b₁ = b₂) ∧
  (∀ b a₁ a₂, (a₁, b) ∈ M → (a₂, b) ∈ M → a₁ = a₂)

/-- All even bipartite edge sets on the finite vertex classes. -/
noncomputable def bipartiteEvenEdgeSets
    (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] : Finset (Finset (A × B)) := by
  classical
  exact Finset.univ.filter IsBipartiteEven

/-- All simple bipartite cycles, represented by their edge sets. -/
noncomputable def simpleBipartiteCycles
    (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] : Finset (Finset (A × B)) := by
  classical
  exact Finset.univ.filter IsSimpleBipartiteCycle

/-- Product of the cell weights on `F \ M`, exactly the weight used in (9.15). -/
def edgeWeightOutside
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (q : A → B → ℝ) (M F : Finset (A × B)) : ℝ :=
  ∏ e ∈ F \ M, q e.1 e.2

private lemma bipartiteEven_sdiff
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

private lemma exists_minimal_even_subset
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
  refine' ⟨C, hC.1.1, hC.1.2.1, hC.1.2.2, _⟩
  exact fun D hDC hD hDne =>
    Finset.eq_of_subset_of_card_le hDC
      (hC.2 D ⟨Finset.Subset.trans hDC hC.1.1, hD, hDne⟩ |>
        le_trans <| by simp +decide)

private lemma exists_disjoint_cycle_decomposition
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
      exact exists_minimal_even_subset hF (Finset.nonempty_of_ne_empty hF_empty) |>
        fun ⟨C, hC₁, hC₂⟩ => ⟨C, hC₁, hC₂⟩
    obtain ⟨s, hs⟩ :
        ∃ s ⊆ simpleBipartiteCycles A B,
          F \ C = s.biUnion id ∧
            ∀ C₁ ∈ s, ∀ C₂ ∈ s, C₁ ≠ C₂ → Disjoint C₁ C₂ := by
      apply ih (F \ C)
      · simp_all +decide [Finset.ssubset_def, Finset.subset_iff]
        exact Exists.elim hC.2.2.1 fun x hx => ⟨_, _, hC.1 _ _ hx, hx⟩
      · exact bipartiteEven_sdiff hC.1 hF hC.2.1
    refine' ⟨Insert.insert C s, _, _, _⟩ <;>
      simp_all +decide [Finset.subset_iff]
    · unfold simpleBipartiteCycles
      aesop
    · grind
    · simp_all +decide [Finset.ext_iff, Finset.disjoint_left]
      grind +ring

private lemma biUnion_recovery_injective
    {α : Type*} [DecidableEq α]
    (U : Finset (Finset α)) (s : Finset α → Finset (Finset α))
    (hrecover : ∀ F ∈ U, F = (s F).biUnion id) :
    ∀ F ∈ U, ∀ G ∈ U, s F = s G → F = G := by
  intro F hF G hG hFG
  rw [hrecover F hF, hrecover G hG, hFG]

private lemma edgeWeightOutside_biUnion
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (q : A → B → ℝ) (M : Finset (A × B))
    (s : Finset (Finset (A × B)))
    (hdisj : ∀ C₁ ∈ s, ∀ C₂ ∈ s, C₁ ≠ C₂ → Disjoint C₁ C₂) :
    edgeWeightOutside q M (s.biUnion id) =
      ∏ C ∈ s, edgeWeightOutside q M C := by
  unfold edgeWeightOutside
  rw [← Finset.prod_biUnion]
  · rcongr e
    aesop
  · exact fun x hx y hy hxy =>
      Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset
        (hdisj x hx y hy hxy)

/-- Equation (9.15), including both finite polymer-product and exponential
steps.  The finite cycle decomposition, edge-disjointness, and recoverability
are constructed in the proof rather than assumed. -/
theorem weighted_evenSubgraph_polymer_bound
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ℝ) (M : Finset (A × B))
    (_hM : IsBipartiteMatching M)
    (hq : ∀ a b, 0 ≤ q a b) :
    ((∑ F ∈ bipartiteEvenEdgeSets A B, edgeWeightOutside q M F) ≤
      (∏ C ∈ simpleBipartiteCycles A B,
        (1 + edgeWeightOutside q M C))) ∧
    ((∏ C ∈ simpleBipartiteCycles A B,
        (1 + edgeWeightOutside q M C)) ≤
      Real.exp
        (∑ C ∈ simpleBipartiteCycles A B,
          edgeWeightOutside q M C)) := by
  constructor
  · have h_decomp :
        ∀ F ∈ bipartiteEvenEdgeSets A B,
          ∃ s : Finset (Finset (A × B)),
            s ⊆ simpleBipartiteCycles A B ∧
            F = s.biUnion id ∧
            (∀ C₁ ∈ s, ∀ C₂ ∈ s, C₁ ≠ C₂ → Disjoint C₁ C₂) := by
      exact fun F hF =>
        exists_disjoint_cycle_decomposition F
          (by
            unfold bipartiteEvenEdgeSets at hF
            aesop)
    choose! s hs using h_decomp
    have h_inj := biUnion_recovery_injective
      (bipartiteEvenEdgeSets A B) s (fun F hF ↦ (hs F hF).2.1)
    have h_sum_prod :
        ∑ F ∈ bipartiteEvenEdgeSets A B, edgeWeightOutside q M F ≤
          ∑ s' ∈ Finset.powerset (simpleBipartiteCycles A B),
            ∏ C ∈ s', edgeWeightOutside q M C := by
      have h_sum_prod :
          ∑ F ∈ bipartiteEvenEdgeSets A B, edgeWeightOutside q M F ≤
            ∑ s' ∈ Finset.image s (bipartiteEvenEdgeSets A B),
              ∏ C ∈ s', edgeWeightOutside q M C := by
        rw [Finset.sum_image]
        · refine' Finset.sum_le_sum fun F hF => _
          rw [(hs F hF).2.1, edgeWeightOutside_biUnion]
          · rw [← (hs F hF).2.1]
          · exact (hs F hF).2.2
        · exact h_inj
      refine' le_trans h_sum_prod (Finset.sum_le_sum_of_subset_of_nonneg _ _)
      · exact Finset.image_subset_iff.mpr fun F hF =>
          Finset.mem_powerset.mpr (hs F hF).1
      · exact fun _ _ _ =>
          Finset.prod_nonneg fun _ _ =>
            Finset.prod_nonneg fun _ _ => hq _ _
    convert h_sum_prod using 1
    simp +decide [add_comm, Finset.prod_add]
  · rw [Real.exp_sum]
    exact Finset.prod_le_prod
      (fun _ _ =>
        add_nonneg zero_le_one (Finset.prod_nonneg fun _ _ => hq _ _))
      fun _ _ => by
        rw [add_comm]
        exact Real.add_one_le_exp _

#print axioms weighted_evenSubgraph_polymer_bound

end

end Erdos625
