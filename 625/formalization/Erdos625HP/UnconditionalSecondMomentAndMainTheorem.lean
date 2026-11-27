import Erdos625HP.SelectedProfilesAndMaximalPsi2

/-!
# v13 Unconditional Lemma 7.2, Proposition 7.3, Corollary 8.1, Phase Refinement, and Main Theorem

This module completes the end-to-end unconditional formalization of both top-level theorems of the
15-page manuscript (`manuscript/main.tex`) using **zero** public definitions (`0` public
`def`/`abbrev`/`structure` declarations), **zero** external hypotheses on the two top-level
theorems, and only the standard Lean kernel foundations (`propext`, `Classical.choice`,
`Quot.sound`):

1. **Section 7 — Unconditional `G(n, 1/2)` Lemma 7.2 (`lem:hp-transfer`) & Proposition 7.3
   similar-range bound (`prop:hp-second-moment`):**
   - `eventually_lemma72_overlapSum_le`: bounds the fixed-`ν` relevant-pair sum (`n_tr ≥ n^(1 - c₀)`)
     for both unmarked colorings (`partitionColoringEvent`) and cocolorings
     (`partitionCocoloringEvent`) by `exp(C_ov (log n)⁵) E[X̄_k]² F_1^ch(ν)` and
     `exp(C_ov (log n)⁵) E[Z_k^mk]² W(ν)`.
   - `eventually_similarRange_pairSum_le`: bounds the similar-range relevant-pair sum
     (`n_tr < n^(1 - c₀)`) via disjoint scrambled extra edges (`disjoint_scrambled_extra_pairs_ge`)
     and residual vertex colorings.

2. **Section 7 & Section 8 — Unconditional Proposition 7.3 second-moment bounds, Paley–Zygmund
   rare-seed lower bounds, and Corollary 8.1 quasi-exponential upper tails in Regime U & Regime C:**
   - `eventually_prop73_and_cor81_upperTails_regimeU`
   - `eventually_prop73_and_cor81_upperTails_regimeC`

3. **Introduction & Section 9 — Zero-hypothesis top-level closures (`0` binders):**
   - `erdos625_phaseRefinement_unconditional`: complete unconditional **Phase Refinement**
     (`main.tex` lines 239–255).
   - `erdos625_mainTheorem_unconditional`: complete unconditional **Main Theorem `(i)–(iv)`**
     (`main.tex` lines 99–140), including the coupling-uniform running-supremum Orlicz `ψ₂`,
     square-exponential moment, and `L^p` bounds.
-/

namespace Erdos625HP

open Erdos625 Erdos625.FiveSizeEntropyGap FiveSizePhaseGainSharp FiveSizePhaseGainCertificate
open Filter Asymptotics MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal Classical

noncomputable section

set_option autoImplicit false

/-!
## 1. Window-profile partition decomposition and exact joint coloring probability factorization
-/

private theorem multiset_map_card_count_eq_v13 {V : Type*} [DecidableEq V]
    (S : Finset (Finset V)) (s : ℕ) :
    (S.1.map Finset.card).count s = (S.filter fun D ↦ D.card = s).card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert A S hA ih =>
    rw [Finset.insert_val_of_notMem hA, Multiset.map_cons, Finset.filter_insert]
    by_cases h : A.card = s
    · subst h
      rw [if_pos rfl, Finset.card_insert_of_notMem (by simp [hA]), Multiset.count_cons_self, ih]
    · rw [if_neg h, Multiset.count_cons_of_ne (Ne.symm h), ih]

private theorem windowProfile_part_sizes_and_counts_v13
    {n alpha m M : ℕ} (halpha : m + M + 2 ≤ alpha)
    {kv : Fin M → ℕ} {kp : ColoringProfile alpha}
    (hMass : selectedVertexMass (fun j : Fin M ↦ alpha - (m + 1 + j.1)) kv = n)
    (hkp : ∀ idx : Fin alpha,
      kp idx = ∑ j : Fin M, if alpha - (m + 1 + j.1) = idx.1 + 1 then kv j else 0) :
    let u : Fin M → ℕ := fun j ↦ alpha - (m + 1 + j.1)
    Function.Injective u ∧
    (∀ j : Fin M, 2 ≤ u j ∧ alpha - (m + M) ≤ u j ∧ u j ≤ alpha - (m + 1)) ∧
    ColoringProfile.partCount kp = selectedBlockCount kv ∧
    ColoringProfile.vertexMass kp = n ∧
    ColoringProfile.forbiddenEdges kp = selectedInternalEdgeCount u kv ∧
    (∀ P : VertexPartition n, partitionShape P = ColoringProfile.sizes kp →
      P.parts.card = selectedBlockCount kv ∧
      (∀ j : Fin M, (P.parts.filter fun D ↦ D.card = u j).card = kv j) ∧
      P.parts = Finset.univ.biUnion (fun j : Fin M ↦ P.parts.filter fun D ↦ D.card = u j) ∧
      (∀ D ∈ P.parts, ∃ j : Fin M, D.card = u j)) := by
  intro u
  have hu_bds : ∀ j : Fin M, 2 ≤ u j ∧ alpha - (m + M) ≤ u j ∧ u j ≤ alpha - (m + 1) := by
    intro j; dsimp [u]; exact ⟨by omega, by omega, by omega⟩
  have hu_inj : Function.Injective u := by
    intro j₁ j₂ heq; dsimp [u] at heq; ext; omega
  let idxOf : Fin M → Fin alpha := fun j ↦ ⟨u j - 1, by dsimp [u]; omega⟩
  have hidx_inj : Function.Injective idxOf := by
    intro j₁ j₂ heq
    have hv := congrArg Fin.val heq
    dsimp [idxOf, u] at hv; ext; omega
  have hcond_iff : ∀ (j : Fin M) (idx : Fin alpha),
      (u j = idx.1 + 1) ↔ idx = idxOf j := by
    intro j idx
    have hu2 := (hu_bds j).1
    exact ⟨fun h ↦ by ext; dsimp [idxOf]; omega, fun h ↦ by rw [h]; dsimp [idxOf]; omega⟩
  have hkp_at : ∀ j : Fin M, kp (idxOf j) = kv j := by
    intro j
    rw [hkp (idxOf j)]
    have hpt : ∀ j' : Fin M,
        (if u j' = (idxOf j).1 + 1 then kv j' else 0) = if j' = j then kv j' else 0 := by
      intro j'
      have hiff : (u j' = (idxOf j).1 + 1) ↔ j' = j :=
        (hcond_iff j' (idxOf j)).trans ⟨fun h ↦ hidx_inj h.symm, fun h ↦ by rw [h]⟩
      by_cases h : j' = j
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (mt hiff.mp h), if_neg h]
    rw [Finset.sum_congr rfl fun j' _ ↦ hpt j', Finset.sum_ite_eq' Finset.univ j]
    simp
  have hkp_zero_outside : ∀ idx : Fin alpha, idx ∉ Finset.univ.image idxOf → kp idx = 0 := by
    intro idx hnot
    rw [hkp idx]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [if_neg]; intro heq; apply hnot
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ((hcond_iff j idx).mp heq).symm⟩
  have hsum_nat : ∀ f : ℕ → ℕ → ℕ, (∀ s, f s 0 = 0) →
      (∑ idx : Fin alpha, f (idx.1 + 1) (kp idx)) = ∑ j : Fin M, f (u j) (kv j) := by
    intro f hf0
    have hsub : (∑ idx ∈ Finset.univ.image idxOf, f (idx.1 + 1) (kp idx)) =
        ∑ idx : Fin alpha, f (idx.1 + 1) (kp idx) :=
      Finset.sum_subset (Finset.subset_univ _) fun idx _ hnot ↦ by
        rw [hkp_zero_outside idx hnot, hf0]
    rw [← hsub, Finset.sum_image (fun a _ b _ hab ↦ hidx_inj hab)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hu1 : (idxOf j).1 + 1 = u j := by dsimp [idxOf]; have := (hu_bds j).1; omega
    rw [hu1, hkp_at j]
  have hpart_eq : ColoringProfile.partCount kp = selectedBlockCount kv := by
    rw [ColoringProfile.partCount_eq_sum]
    exact hsum_nat (fun _ c ↦ c) (fun _ ↦ rfl)
  have hmass_kp : ColoringProfile.vertexMass kp = n := by
    rw [ColoringProfile.vertexMass_eq_sum,
      hsum_nat (fun s c ↦ s * c) (fun _ ↦ Nat.mul_zero _)]
    exact hMass
  have hforb_eq : ColoringProfile.forbiddenEdges kp = selectedInternalEdgeCount u kv := by
    rw [ColoringProfile.forbiddenEdges_eq_sum,
      hsum_nat (fun s c ↦ c * s.choose 2) (fun _ ↦ Nat.zero_mul _)]
    unfold selectedInternalEdgeCount
    exact Finset.sum_congr rfl fun j _ ↦ Nat.mul_comm _ _
  refine ⟨hu_inj, hu_bds, hpart_eq, hmass_kp, hforb_eq, ?_⟩
  intro P hP_sh
  have hp_card : P.parts.card = selectedBlockCount kv :=
    (ProfilePartition.card_parts_eq (⟨P, hP_sh⟩ : ProfilePartition n kp)).trans hpart_eq
  have hfilt_card : ∀ j : Fin M, (P.parts.filter fun D ↦ D.card = u j).card = kv j := by
    intro j
    rw [← multiset_map_card_count_eq_v13 P.parts (u j)]
    change (partitionShape P).count (u j) = kv j
    have hu1 : (idxOf j).1 + 1 = u j := by dsimp [idxOf]; have := (hu_bds j).1; omega
    rw [hP_sh, ← hu1, ColoringProfile.count_sizes_at kp (idxOf j), hkp_at j]
  have hdisj_f : ((Finset.univ : Finset (Fin M)) : Set (Fin M)).PairwiseDisjoint
      (fun j : Fin M ↦ P.parts.filter fun D ↦ D.card = u j) := by
    intro j₁ _ j₂ _ hjne
    rw [Function.onFun, Finset.disjoint_left]
    intro D h1 h2
    exact hjne (hu_inj ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2))
  have hbi_sub : Finset.univ.biUnion (fun j : Fin M ↦ P.parts.filter fun D ↦ D.card = u j) ⊆
      P.parts := by
    intro D hD
    rcases Finset.mem_biUnion.mp hD with ⟨_, _, hDf⟩
    exact (Finset.mem_filter.mp hDf).1
  have hbi_card :
      (Finset.univ.biUnion (fun j : Fin M ↦ P.parts.filter fun D ↦ D.card = u j)).card =
        P.parts.card := by
    rw [Finset.card_biUnion hdisj_f, Finset.sum_congr rfl fun j _ ↦ hfilt_card j]
    exact hp_card.symm
  have hbi_eq : P.parts =
      Finset.univ.biUnion (fun j : Fin M ↦ P.parts.filter fun D ↦ D.card = u j) :=
    (Finset.eq_of_subset_of_card_le hbi_sub (le_of_eq hbi_card.symm)).symm
  refine ⟨hp_card, hfilt_card, hbi_eq, ?_⟩
  intro D hD
  rw [hbi_eq, Finset.mem_biUnion] at hD
  rcases hD with ⟨j, _, hDf⟩
  exact ⟨j, (Finset.mem_filter.mp hDf).2⟩

private theorem finset_subset_parts_stats_v13
    {V : Type*} [DecidableEq V] {M : ℕ} {u : Fin M → ℕ}
    (hu_inj : Function.Injective u)
    {Parts F : Finset (Finset V)} (hF : F ⊆ Parts)
    (hParts : ∀ D ∈ Parts, ∃ j : Fin M, D.card = u j) :
    let cF : Fin M → ℕ := fun j ↦ (F.filter fun D ↦ D.card = u j).card
    F = Finset.univ.biUnion (fun j : Fin M ↦ F.filter fun D ↦ D.card = u j) ∧
    F.card = selectedBlockCount cF ∧
    (∑ D ∈ F, D.card) = selectedVertexMass u cF ∧
    (∑ D ∈ F, D.card.choose 2) = selectedInternalEdgeCount u cF := by
  intro cF
  have hdisj : ((Finset.univ : Finset (Fin M)) : Set (Fin M)).PairwiseDisjoint
      (fun j : Fin M ↦ F.filter fun D ↦ D.card = u j) := by
    intro j₁ _ j₂ _ hjne
    rw [Function.onFun, Finset.disjoint_left]
    intro D h1 h2
    exact hjne (hu_inj ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2))
  have hbi : F = Finset.univ.biUnion (fun j : Fin M ↦ F.filter fun D ↦ D.card = u j) := by
    ext D
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    refine ⟨fun hDF ↦ ?_, fun ⟨_, hDF, _⟩ ↦ hDF⟩
    obtain ⟨j, hj⟩ := hParts D (hF hDF)
    exact ⟨j, hDF, hj⟩
  have hcard : F.card = selectedBlockCount cF := by
    conv_lhs => rw [hbi]
    rw [Finset.card_biUnion hdisj]
    rfl
  have hmass : (∑ D ∈ F, D.card) = selectedVertexMass u cF := by
    conv_lhs => rw [hbi]
    rw [Finset.sum_biUnion hdisj]
    unfold selectedVertexMass
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    calc ∑ D ∈ F.filter (fun D ↦ D.card = u j), D.card
        = ∑ _D ∈ F.filter (fun D ↦ D.card = u j), u j :=
          Finset.sum_congr rfl fun D hD ↦ (Finset.mem_filter.mp hD).2
      _ = u j * cF j := by simp [cF, Finset.sum_const, smul_eq_mul, mul_comm]
  have hedge : (∑ D ∈ F, D.card.choose 2) = selectedInternalEdgeCount u cF := by
    conv_lhs => rw [hbi]
    rw [Finset.sum_biUnion hdisj]
    unfold selectedInternalEdgeCount
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    calc ∑ D ∈ F.filter (fun D ↦ D.card = u j), D.card.choose 2
        = ∑ _D ∈ F.filter (fun D ↦ D.card = u j), (u j).choose 2 :=
          Finset.sum_congr rfl fun D hD ↦ congrArg (·.choose 2) (Finset.mem_filter.mp hD).2
      _ = (u j).choose 2 * cF j := by simp [cF, Finset.sum_const, smul_eq_mul, mul_comm]
  exact ⟨hbi, hcard, hmass, hedge⟩

private theorem subprofile_inter_and_sdiff_stats_v13
    {n alpha m M : ℕ} (halpha : m + M + 2 ≤ alpha)
    {kv : Fin M → ℕ} {kp : ColoringProfile alpha}
    (hMass : selectedVertexMass (fun j : Fin M ↦ alpha - (m + 1 + j.1)) kv = n)
    (hkp : ∀ idx : Fin alpha,
      kp idx = ∑ j : Fin M, if alpha - (m + 1 + j.1) = idx.1 + 1 then kv j else 0)
    (P Q : VertexPartition n)
    (hP_sh : partitionShape P = ColoringProfile.sizes kp)
    (hQ_sh : partitionShape Q = ColoringProfile.sizes kp) :
    let u : Fin M → ℕ := fun j ↦ alpha - (m + 1 + j.1)
    let Ident : Finset (Finset (Fin n)) := P.parts ∩ Q.parts
    let nu : Fin M → ℕ := fun j ↦ (Ident.filter fun D ↦ D.card = u j).card
    let r_vec : Fin M → ℕ := fun j ↦ kv j - nu j
    let W_res : Finset (Fin n) := Finset.univ \ Ident.biUnion id
    IsPartialSubprofile kv nu ∧
    Ident.card = selectedBlockCount nu ∧
    (∑ D ∈ Ident, D.card) = selectedVertexMass u nu ∧
    (∑ D ∈ Ident, D.card.choose 2) = selectedInternalEdgeCount u nu ∧
    (∀ j : Fin M, ((P.parts \ Q.parts).filter fun D ↦ D.card = u j).card = r_vec j ∧
      ((Q.parts \ P.parts).filter fun D ↦ D.card = u j).card = r_vec j) ∧
    (P.parts \ Q.parts).card = selectedBlockCount r_vec ∧
    (Q.parts \ P.parts).card = selectedBlockCount r_vec ∧
    (P.parts \ Q.parts).biUnion id = W_res ∧
    (Q.parts \ P.parts).biUnion id = W_res ∧
    W_res.card = n - selectedVertexMass u nu := by
  intro u Ident nu r_vec W_res
  obtain ⟨hu_inj, _, _, _, _, hP_all⟩ :=
    windowProfile_part_sizes_and_counts_v13 halpha hMass hkp
  obtain ⟨_, hP_cnt, _, hP_ex⟩ := hP_all P hP_sh
  obtain ⟨_, hQ_cnt, _, hQ_ex⟩ := hP_all Q hQ_sh
  obtain ⟨_, hId_card, hId_mass, hId_edge⟩ :=
    finset_subset_parts_stats_v13 hu_inj (Finset.inter_subset_left : Ident ⊆ P.parts) hP_ex
  have hsub_nu : IsPartialSubprofile kv nu := by
    intro j
    rw [← hP_cnt j]
    exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.inter_subset_left)
  have hsdiff_cnt : ∀ (A B : VertexPartition n),
      (∀ j : Fin M, (A.parts.filter fun D ↦ D.card = u j).card = kv j) →
      A.parts ∩ B.parts = Ident →
      ∀ j : Fin M, ((A.parts \ B.parts).filter fun D ↦ D.card = u j).card = r_vec j := by
    intro A B hAcnt hAB j
    have hun : (Ident.filter fun D ↦ D.card = u j) ∪
        ((A.parts \ B.parts).filter fun D ↦ D.card = u j) =
        A.parts.filter fun D ↦ D.card = u j := by
      rw [← hAB]; ext D; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_inter,
        Finset.mem_sdiff]; tauto
    have hdisj : Disjoint (Ident.filter fun D ↦ D.card = u j)
        ((A.parts \ B.parts).filter fun D ↦ D.card = u j) := by
      rw [← hAB, Finset.disjoint_left]
      intro D h1 h2
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp h2).1).2
        (Finset.mem_inter.mp (Finset.mem_filter.mp h1).1).2
    have hadd := Finset.card_union_of_disjoint hdisj
    rw [hun, hAcnt j] at hadd
    dsimp [nu, r_vec] at hadd ⊢
    omega
  have hrP := hsdiff_cnt P Q hP_cnt rfl
  have hrQ := hsdiff_cnt Q P hQ_cnt (Finset.inter_comm Q.parts P.parts)
  obtain ⟨_, hResP_card, _, _⟩ :=
    finset_subset_parts_stats_v13 hu_inj (Finset.sdiff_subset : P.parts \ Q.parts ⊆ P.parts) hP_ex
  obtain ⟨_, hResQ_card, _, _⟩ :=
    finset_subset_parts_stats_v13 hu_inj (Finset.sdiff_subset : Q.parts \ P.parts ⊆ Q.parts) hQ_ex
  have hResP_c : (P.parts \ Q.parts).card = selectedBlockCount r_vec := by
    rw [hResP_card]; exact Finset.sum_congr rfl fun j _ ↦ hrP j
  have hResQ_c : (Q.parts \ P.parts).card = selectedBlockCount r_vec := by
    rw [hResQ_card]; exact Finset.sum_congr rfl fun j _ ↦ hrQ j
  have hsdiff_bi : ∀ (A B : VertexPartition n), A.parts ∩ B.parts = Ident →
      (A.parts \ B.parts).biUnion id = W_res := by
    intro A B hAB
    ext v
    simp only [W_res, Finset.mem_biUnion, id_eq, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨D, ⟨hDA, hDB⟩, hvD⟩ ⟨E, hEI, hvE⟩
      rw [← hAB] at hEI
      have hDE : D = E := by
        by_contra hne
        exact Finset.disjoint_left.mp (A.disjoint hDA (Finset.mem_inter.mp hEI).1 hne) hvD hvE
      exact hDB (hDE ▸ (Finset.mem_inter.mp hEI).2)
    · intro hnot
      let D := A.part v
      have hDA : D ∈ A.parts := A.part_mem.mpr (Finset.mem_univ v)
      have hvD : v ∈ D := A.mem_part (Finset.mem_univ v)
      have hDB : D ∉ B.parts := fun hDB ↦ hnot ⟨D, hAB ▸ Finset.mem_inter.mpr ⟨hDA, hDB⟩, hvD⟩
      exact ⟨D, ⟨hDA, hDB⟩, hvD⟩
  have hId_disj : (Ident : Set (Finset (Fin n))).PairwiseDisjoint id :=
    fun A hA B hB hne ↦ P.disjoint (Finset.mem_inter.mp hA).1 (Finset.mem_inter.mp hB).1 hne
  have hW_id_card : (Ident.biUnion id).card = selectedVertexMass u nu := by
    rw [Finset.card_biUnion hId_disj]; exact hId_mass
  have hW_res_card : W_res.card = n - selectedVertexMass u nu := by
    dsimp [W_res]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      hW_id_card]
  exact ⟨hsub_nu, hId_card, hId_mass, hId_edge, fun j ↦ ⟨hrP j, hrQ j⟩,
    hResP_c, hResQ_c, hsdiff_bi P Q rfl,
    hsdiff_bi Q P (Finset.inter_comm Q.parts P.parts), hW_res_card⟩

private theorem randomGraphMeasure_coloring_inter_factorization_v13
    {n alpha m M : ℕ} (halpha : m + M + 2 ≤ alpha)
    {kv : Fin M → ℕ} {kp : ColoringProfile alpha}
    (hMass : selectedVertexMass (fun j : Fin M ↦ alpha - (m + 1 + j.1)) kv = n)
    (hkp : ∀ idx : Fin alpha,
      kp idx = ∑ j : Fin M, if alpha - (m + 1 + j.1) = idx.1 + 1 then kv j else 0)
    (P Q : VertexPartition n)
    (hP_sh : partitionShape P = ColoringProfile.sizes kp)
    (hQ_sh : partitionShape Q = ColoringProfile.sizes kp) :
    let u : Fin M → ℕ := fun j ↦ alpha - (m + 1 + j.1)
    let nu : Fin M → ℕ := fun j ↦ ((P.parts ∩ Q.parts).filter fun D ↦ D.card = u j).card
    (randomGraphMeasure n).real (partitionColoringEvent P ∩ partitionColoringEvent Q) =
      ((1 / 2 : ℝ) ^ selectedInternalEdgeCount u kv) ^ 2 *
        (2 : ℝ) ^ selectedInternalEdgeCount u nu *
        (2 : ℝ) ^ (∑ A ∈ P.parts \ Q.parts, ∑ B ∈ Q.parts \ P.parts, (A ∩ B).card.choose 2) := by
  intro u nu
  obtain ⟨_, _, _, _, hforb_eq, _⟩ := windowProfile_part_sizes_and_counts_v13 halpha hMass hkp
  obtain ⟨_, _, _, hId_edge, _, _, _, _, _, _⟩ :=
    subprofile_inter_and_sdiff_stats_v13 halpha hMass hkp P Q hP_sh hQ_sh
  have hset : partitionColoringEvent P ∩ partitionColoringEvent Q =
      {G : LabeledGraph n | G ≤ (partitionInternalGraph P ⊔ partitionInternalGraph Q)ᶜ} := by
    ext G
    rw [Set.mem_inter_iff, mem_partitionColoringEvent_iff_le_compl,
      mem_partitionColoringEvent_iff_le_compl, Set.mem_setOf_eq, compl_sup, le_inf_iff]
  have hprob_enn :
      (randomGraphMeasure n).real (partitionColoringEvent P ∩ partitionColoringEvent Q) =
        (1 / 2 : ℝ) ^ (partitionInternalGraph P ⊔ partitionInternalGraph Q).edgeSet.ncard := by
    rw [Measure.real, hset, randomGraphMeasure_le_compl, ENNReal.toReal_pow]
    congr 1; norm_num
  have hunion_add :
      (partitionInternalGraph P ⊔ partitionInternalGraph Q).edgeSet.ncard +
        (∑ A ∈ P.parts, ∑ B ∈ Q.parts, (A ∩ B).card.choose 2) =
        2 * selectedInternalEdgeCount u kv := by
    let P_pp : ProfilePartition n kp := ⟨P, hP_sh⟩
    let Q_pp : ProfilePartition n kp := ⟨Q, hQ_sh⟩
    have hraw := ncard_profilePartitionInternalGraph_edgeSet_union_add_overlap P_pp Q_pp
    simpa only [P_pp, Q_pp, profileOverlapCellCount, hforb_eq] using hraw
  set Ident := P.parts ∩ Q.parts
  set ResP := P.parts \ Q.parts
  set ResQ := Q.parts \ P.parts
  have hunP : Ident ∪ ResP = P.parts := by ext D; simp [Ident, ResP]; tauto
  have hdisjP : Disjoint Ident ResP := by
    rw [Finset.disjoint_left]; intro D h1 h2
    exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2
  have hunQ : Ident ∪ ResQ = Q.parts := by ext D; simp [Ident, ResQ]; tauto
  have hdisjQ : Disjoint Ident ResQ := by
    rw [Finset.disjoint_left]; intro D h1 h2
    exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).1
  have hov_id : ∀ A ∈ Ident,
      (∑ B ∈ Q.parts, (A ∩ B).card.choose 2) = A.card.choose 2 := by
    intro A hAI
    have hAQ : A ∈ Q.parts := (Finset.mem_inter.mp hAI).2
    rw [← Finset.add_sum_erase _ _ hAQ, Finset.inter_self]
    have hzero : ∑ B ∈ Q.parts.erase A, (A ∩ B).card.choose 2 = 0 := by
      refine Finset.sum_eq_zero fun B hB ↦ ?_
      have hne : A ≠ B := (Finset.mem_erase.mp hB).1.symm
      have hBQ : B ∈ Q.parts := (Finset.mem_erase.mp hB).2
      have hemp : A ∩ B = ∅ := Finset.disjoint_iff_inter_eq_empty.mp (Q.disjoint hAQ hBQ hne)
      simp [hemp]
    omega
  have hov_res_id : ∀ A ∈ ResP,
      (∑ B ∈ Ident, (A ∩ B).card.choose 2) = 0 := by
    intro A hAR
    obtain ⟨hAP, hAnQ⟩ := Finset.mem_sdiff.mp hAR
    refine Finset.sum_eq_zero fun B hBI ↦ ?_
    obtain ⟨hBP, hBQ⟩ := Finset.mem_inter.mp hBI
    have hne : A ≠ B := fun heq ↦ hAnQ (heq ▸ hBQ)
    have hemp : A ∩ B = ∅ := Finset.disjoint_iff_inter_eq_empty.mp (P.disjoint hAP hBP hne)
    simp [hemp]
  have hov_split :
      (∑ A ∈ P.parts, ∑ B ∈ Q.parts, (A ∩ B).card.choose 2) =
        selectedInternalEdgeCount u nu + ∑ A ∈ ResP, ∑ B ∈ ResQ, (A ∩ B).card.choose 2 := by
    rw [← hunP, Finset.sum_union hdisjP, Finset.sum_congr rfl hov_id, hId_edge]
    congr 1
    refine Finset.sum_congr rfl fun A hAR ↦ ?_
    rw [← hunQ, Finset.sum_union hdisjQ, hov_res_id A hAR, zero_add]
  rw [hov_split] at hunion_add
  set a_nc := (partitionInternalGraph P ⊔ partitionInternalGraph Q).edgeSet.ncard
  set w_ov := selectedInternalEdgeCount u nu + ∑ A ∈ ResP, ∑ B ∈ ResQ, (A ∩ B).card.choose 2
  have hpow_id : (1 / 2 : ℝ) ^ a_nc =
      ((1 / 2 : ℝ) ^ selectedInternalEdgeCount u kv) ^ 2 * (2 : ℝ) ^ w_ov := by
    have h2w_ne : (2 : ℝ) ^ w_ov ≠ 0 := by positivity
    have h1 : (1 / 2 : ℝ) ^ a_nc * (1 / 2 : ℝ) ^ w_ov =
        ((1 / 2 : ℝ) ^ selectedInternalEdgeCount u kv) ^ 2 := by
      rw [← pow_add, hunion_add, pow_mul', sq]
    have h2 : (1 / 2 : ℝ) ^ w_ov = ((2 : ℝ) ^ w_ov)⁻¹ := by rw [one_div, inv_pow]
    rw [h2] at h1
    exact (eq_mul_inv_iff_mul_eq₀ h2w_ne).mp h1.symm |>.symm
  rw [hprob_enn, hpow_id]
  dsimp [w_ov]
  rw [pow_add, ← mul_assoc]

/-!
## 2. Unconditional Lemma 7.2 (`lem:hp-transfer`): fixed-`ν` relevant-pair overlap sum
-/

private theorem nat_factorial_mul_choose_le_pow_v13 :
    ∀ (u k : ℕ), k.factorial * u.choose k ≤ u ^ k
  | _, 0 => by simp
  | 0, _ + 1 => by simp
  | u + 1, k + 1 => by
    by_cases hle : k ≤ u
    · have hid1 := Nat.choose_mul_factorial_mul_factorial (Nat.succ_le_succ hle)
      have hid2 := Nat.choose_mul_factorial_mul_factorial hle
      have hsub : u + 1 - (k + 1) = u - k := by omega
      rw [hsub] at hid1
      have hrem_pos : 0 < (u - k).factorial := Nat.factorial_pos _
      have hstep : (k + 1).factorial * (u + 1).choose (k + 1) =
          (u + 1) * (k.factorial * u.choose k) := by
        apply Nat.eq_of_mul_eq_mul_right hrem_pos
        calc (k + 1).factorial * (u + 1).choose (k + 1) * (u - k).factorial
            = (u + 1).choose (k + 1) * (k + 1).factorial * (u - k).factorial := by ring
          _ = (u + 1).factorial := hid1
          _ = (u + 1) * u.factorial := Nat.factorial_succ u
          _ = (u + 1) * (u.choose k * k.factorial * (u - k).factorial) := by rw [hid2]
          _ = (u + 1) * (k.factorial * u.choose k) * (u - k).factorial := by ring
      rw [hstep, pow_succ']
      exact Nat.mul_le_mul_left (u + 1)
        ((nat_factorial_mul_choose_le_pow_v13 u k).trans (Nat.pow_le_pow_left (Nat.le_succ u) k))
    · rw [Nat.choose_eq_zero_of_lt (by omega : u + 1 < k + 1), Nat.mul_zero]
      exact Nat.zero_le _

private theorem unmarked_moment_sq_mul_weight_factorization_v13
    {M n : ℕ} {u kv nu : Fin M → ℕ}
    (hMass : selectedVertexMass u kv = n)
    (hnu : IsPartialSubprofile kv nu) :
    let n_tr : ℕ := n - selectedVertexMass u nu
    let r_vec : Fin M → ℕ := fun j ↦ kv j - nu j
    (completeUnmarkedFirstMoment u kv) ^ 2 * unmarkedDiagonalWeight n u kv nu =
      (((1 / 2 : ℝ) ^ selectedInternalEdgeCount u kv) ^ 2 *
          (2 : ℝ) ^ selectedInternalEdgeCount u nu) *
        ((n.factorial : ℝ) /
          ((n_tr.factorial : ℝ) * (partialProfileFactorialProduct u nu : ℝ))) *
        ((n_tr.factorial : ℝ) / (partialProfileFactorialProduct u r_vec : ℝ)) ^ 2 := by
  intro n_tr r_vec
  have hprod_id :
      (partialProfileFactorialProduct u kv) ^ 2 =
        (partialMarkingCount kv nu * partialProfileFactorialProduct u nu) *
          (partialProfileFactorialProduct u nu * (partialProfileFactorialProduct u r_vec) ^ 2) := by
    unfold partialProfileFactorialProduct partialMarkingCount
    rw [← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    have hch := Nat.choose_mul_factorial_mul_factorial (hnu j)
    have hadd : nu j + r_vec j = kv j := Nat.add_sub_of_le (hnu j)
    have hpow : (u j).factorial ^ kv j = (u j).factorial ^ (nu j) * (u j).factorial ^ (r_vec j) := by
      rw [← hadd, pow_add]
    change ((u j).factorial ^ kv j * (kv j).factorial) ^ 2 =
      ((kv j).choose (nu j) ^ 2 * ((u j).factorial ^ nu j * (nu j).factorial)) *
        (((u j).factorial ^ nu j * (nu j).factorial) *
          ((u j).factorial ^ r_vec j * (r_vec j).factorial) ^ 2)
    rw [hpow, ← hch]
    ring
  have hprod_R :
      ((partialProfileFactorialProduct u kv : ℝ)) ^ 2 =
        ((partialMarkingCount kv nu : ℝ) * (partialProfileFactorialProduct u nu : ℝ)) *
          ((partialProfileFactorialProduct u nu : ℝ) *
            ((partialProfileFactorialProduct u r_vec : ℝ)) ^ 2) := by
    exact_mod_cast hprod_id
  have hpf_kv_pos : (0 : ℝ) < (partialProfileFactorialProduct u kv : ℝ) := by
    unfold partialProfileFactorialProduct
    exact_mod_cast Finset.prod_pos fun j _ ↦
      mul_pos (pow_pos (Nat.factorial_pos _) _) (Nat.factorial_pos _)
  have hpf_nu_pos : (0 : ℝ) < (partialProfileFactorialProduct u nu : ℝ) := by
    unfold partialProfileFactorialProduct
    exact_mod_cast Finset.prod_pos fun j _ ↦
      mul_pos (pow_pos (Nat.factorial_pos _) _) (Nat.factorial_pos _)
  have hpf_r_pos : (0 : ℝ) < (partialProfileFactorialProduct u r_vec : ℝ) := by
    unfold partialProfileFactorialProduct
    exact_mod_cast Finset.prod_pos fun j _ ↦
      mul_pos (pow_pos (Nat.factorial_pos _) _) (Nat.factorial_pos _)
  have hnf_pos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hntrf_pos : (0 : ℝ) < (n_tr.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n_tr
  have h2k_ne : (2 : ℝ) ^ (∑ j : Fin M, kv j) ≠ 0 := by positivity
  have h2nu_ne : (2 : ℝ) ^ (∑ j : Fin M, nu j) ≠ 0 := by positivity
  have h2ek_ne : (2 : ℝ) ^ selectedInternalEdgeCount u kv ≠ 0 := by positivity
  have h2enu_ne : (2 : ℝ) ^ selectedInternalEdgeCount u nu ≠ 0 := by positivity
  unfold completeUnmarkedFirstMoment completeSignedFirstMoment residualVertexMass
    unmarkedDiagonalWeight partialDiagonalWeight partialSignedFirstMoment selectedBlockCount
  rw [hMass, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_mul]
  change ((((2 : ℝ) ^ ∑ j : Fin M, kv j)⁻¹ *
        ((2 : ℝ) ^ (∑ j : Fin M, kv j) * (n.factorial : ℝ) /
          ((partialProfileFactorialProduct u kv : ℝ) *
            (2 : ℝ) ^ selectedInternalEdgeCount u kv))) ^ 2 *
      ((2 : ℝ) ^ (∑ j : Fin M, nu j) *
        ((partialMarkingCount kv nu : ℝ) /
          ((2 : ℝ) ^ (∑ j : Fin M, nu j) * (n.factorial : ℝ) /
            ((n_tr.factorial : ℝ) * (partialProfileFactorialProduct u nu : ℝ) *
              (2 : ℝ) ^ selectedInternalEdgeCount u nu))))) = _
  rw [one_div, inv_pow]
  field_simp [h2k_ne, h2nu_ne, h2ek_ne, h2enu_ne, hpf_kv_pos.ne', hpf_nu_pos.ne',
    hpf_r_pos.ne', hnf_pos.ne', hntrf_pos.ne']
  rw [hprod_R]
  ring

private theorem card_identFamily_mul_factorials_le_v13
    {M n : ℕ} {u nu : Fin M → ℕ}
    (hu_inj : Function.Injective u)
    (hmass_le : selectedVertexMass u nu ≤ n)
    (IdentFamily : Finset (Finset (Finset (Fin n))))
    (hFam : ∀ Ident ∈ IdentFamily,
      (Ident : Set (Finset (Fin n))).PairwiseDisjoint id ∧
      Ident = Finset.univ.biUnion (fun j : Fin M ↦ Ident.filter fun D ↦ D.card = u j) ∧
      (∀ j : Fin M, (Ident.filter fun D ↦ D.card = u j).card = nu j)) :
    let n_tr : ℕ := n - selectedVertexMass u nu
    (IdentFamily.card : ℝ) ≤
      (n.factorial : ℝ) /
        ((n_tr.factorial : ℝ) * (partialProfileFactorialProduct u nu : ℝ)) := by
  intro n_tr
  let SlotNu := Option (Σ j : Fin M, Fin (nu j))
  let marginNu : SlotNu → ℕ
    | none => n_tr
    | some s => u s.1
  have huniv_opt : (Finset.univ : Finset SlotNu) =
      insert none (Finset.univ.image some) := by
    ext x; cases x <;> simp
  have huniv_sig : (Finset.univ : Finset (Σ j : Fin M, Fin (nu j))) =
      Finset.univ.sigma (fun j : Fin M ↦ (Finset.univ : Finset (Fin (nu j)))) := by
    ext x; simp
  have hsum_margin : ∑ b : SlotNu, marginNu b = Fintype.card (Fin n) := by
    rw [huniv_opt, Finset.sum_insert (by simp),
      Finset.sum_image (fun _ _ _ _ h ↦ Option.some.inj h), huniv_sig, Finset.sum_sigma]
    have h1 : (∑ j : Fin M, ∑ _c : Fin (nu j), u j) = selectedVertexMass u nu := by
      unfold selectedVertexMass
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp [Finset.sum_const, smul_eq_mul, mul_comm]
    dsimp [marginNu]
    rw [h1, Fintype.card_fin]
    dsimp [n_tr]; omega
  have hprod_margin :
      (∏ b : SlotNu, (marginNu b).factorial) * (∏ j : Fin M, (nu j).factorial) =
        n_tr.factorial * partialProfileFactorialProduct u nu := by
    rw [huniv_opt, Finset.prod_insert (by simp),
      Finset.prod_image (fun _ _ _ _ h ↦ Option.some.inj h), huniv_sig, Finset.prod_sigma]
    have h1 : (∏ j : Fin M, ∏ _c : Fin (nu j), (u j).factorial) =
        ∏ j : Fin M, (u j).factorial ^ (nu j) := by
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      simp [Finset.prod_const]
    dsimp [marginNu]
    rw [h1, mul_assoc, ← Finset.prod_mul_distrib]
    rfl
  let Decorated :=
    Σ Ident : ↥IdentFamily,
      ∀ j : Fin M, ↥(Ident.1.filter fun D ↦ D.card = u j) ≃ Fin (nu j)
  have hDec_card : Fintype.card Decorated =
      IdentFamily.card * ∏ j : Fin M, (nu j).factorial := by
    dsimp [Decorated]
    rw [Fintype.card_sigma]
    have hfib : ∀ Ident : ↥IdentFamily,
        Fintype.card (∀ j : Fin M, ↥(Ident.1.filter fun D ↦ D.card = u j) ≃ Fin (nu j)) =
          ∏ j : Fin M, (nu j).factorial := by
      intro Ident
      rw [Fintype.card_pi]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      have hc : Fintype.card ↥(Ident.1.filter fun D ↦ D.card = u j) = nu j := by
        rw [Fintype.card_coe, (hFam Ident.1 Ident.2).2.2 j]
      exact (Fintype.card_congr (Equiv.equivCongr (Fintype.equivFinOfCardEq hc) (Equiv.refl _))).trans
        (by rw [Fintype.card_perm, Fintype.card_fin])
    simp_rw [hfib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
  let partOf : Decorated → (Σ j : Fin M, Fin (nu j)) → Finset (Fin n) :=
    fun d s ↦ ((d.2 s.1).symm s.2).1
  have hpart_mem : ∀ (d : Decorated) (s : Σ j : Fin M, Fin (nu j)),
      partOf d s ∈ d.1.1 ∧ (partOf d s).card = u s.1 := by
    intro d s
    exact Finset.mem_filter.mp ((d.2 s.1).symm s.2).2
  have hpart_inj : ∀ (d : Decorated), Function.Injective (partOf d) := by
    intro d s₁ s₂ heq
    have hc₁ := (hpart_mem d s₁).2
    have hc₂ := (hpart_mem d s₂).2
    have hj : s₁.1 = s₂.1 := hu_inj (hc₁.symm.trans ((congrArg Finset.card heq).trans hc₂))
    rcases s₁ with ⟨j₁, c₁⟩
    rcases s₂ with ⟨j₂, c₂⟩
    dsimp at hj
    subst hj
    have hsub : (d.2 j₁).symm c₁ = (d.2 j₁).symm c₂ := Subtype.ext heq
    exact congrArg (Sigma.mk j₁) ((d.2 j₁).symm.injective hsub)
  have hpart_surj : ∀ (d : Decorated) {D : Finset (Fin n)}, D ∈ d.1.1 →
      ∃ s : Σ j : Fin M, Fin (nu j), partOf d s = D := by
    intro d D hD
    have hbi := (hFam d.1.1 d.1.2).2.1
    rw [hbi, Finset.mem_biUnion] at hD
    rcases hD with ⟨j, _, hDf⟩
    refine ⟨⟨j, d.2 j ⟨D, hDf⟩⟩, ?_⟩
    change ((d.2 j).symm (d.2 j ⟨D, hDf⟩)).1 = D
    exact congrArg Subtype.val ((d.2 j).symm_apply_apply ⟨D, hDf⟩)
  let raw : Decorated → Fin n → SlotNu := fun d v ↦
    if h : ∃ s : Σ j : Fin M, Fin (nu j), v ∈ partOf d s then some h.choose else none
  have hraw_some : ∀ (d : Decorated) (s : Σ j : Fin M, Fin (nu j)) (v : Fin n),
      raw d v = some s ↔ v ∈ partOf d s := by
    intro d s v
    constructor
    · intro hr
      dsimp [raw] at hr
      split_ifs at hr with h
      have hs : h.choose = s := Option.some.inj hr
      exact hs ▸ h.choose_spec
    · intro hv
      have h : ∃ s' : Σ j : Fin M, Fin (nu j), v ∈ partOf d s' := ⟨s, hv⟩
      have heq_s : h.choose = s := by
        by_contra hne
        have hne_p : partOf d h.choose ≠ partOf d s := fun hp ↦ hne (hpart_inj d hp)
        exact Finset.disjoint_left.mp
          ((hFam d.1.1 d.1.2).1 (hpart_mem d h.choose).1 (hpart_mem d s).1 hne_p)
          h.choose_spec hv
      dsimp [raw]
      rw [dif_pos h, heq_s]
  have hraw_none : ∀ (d : Decorated) (v : Fin n),
      raw d v = none ↔ v ∈ Finset.univ \ d.1.1.biUnion id := by
    intro d v
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion, id_eq]
    constructor
    · intro hr ⟨D, hD, hvD⟩
      obtain ⟨s, rfl⟩ := hpart_surj d hD
      have hs := (hraw_some d s v).mpr hvD
      rw [hr] at hs; simp at hs
    · intro hnot
      have hno : ¬ ∃ s : Σ j : Fin M, Fin (nu j), v ∈ partOf d s := by
        rintro ⟨s, hvs⟩
        exact hnot ⟨partOf d s, (hpart_mem d s).1, hvs⟩
      dsimp [raw]; exact dif_neg hno
  let toLab : Decorated → FixedFiberLabeling (V := Fin n) marginNu := fun d ↦
    ⟨raw d, by
      intro b
      cases b with
      | none =>
        unfold labelingFiberCount
        have hf : (Finset.univ.filter fun v : Fin n ↦ raw d v = none) =
            Finset.univ \ d.1.1.biUnion id := by
          ext v; simp [hraw_none d v]
        rw [hf, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
          Fintype.card_fin, Finset.card_biUnion (hFam d.1.1 d.1.2).1]
        obtain ⟨_, _, hmass_d, _⟩ := finset_subset_parts_stats_v13 hu_inj
          (Finset.Subset.refl d.1.1) (fun D hD ↦ by
            obtain ⟨s, rfl⟩ := hpart_surj d hD
            exact ⟨s.1, (hpart_mem d s).2⟩)
        have hcF_eq : (fun j : Fin M ↦ (d.1.1.filter fun D ↦ D.card = u j).card) = nu :=
          funext fun j ↦ (hFam d.1.1 d.1.2).2.2 j
        dsimp only [id_eq, marginNu, n_tr]
        rw [hmass_d, hcF_eq]
      | some s =>
        unfold labelingFiberCount
        have hf : (Finset.univ.filter fun v : Fin n ↦ raw d v = some s) = partOf d s := by
          ext v; simp [hraw_some d s v]
        rw [hf, (hpart_mem d s).2]⟩
  have htoLab_inj : Function.Injective toLab := by
    rintro ⟨I₁, α₁⟩ ⟨I₂, α₂⟩ heq
    have hraw_eq : raw ⟨I₁, α₁⟩ = raw ⟨I₂, α₂⟩ := congrArg Subtype.val heq
    have hp_eq : ∀ s : Σ j : Fin M, Fin (nu j),
        partOf ⟨I₁, α₁⟩ s = partOf ⟨I₂, α₂⟩ s := by
      intro s; ext v
      rw [← hraw_some ⟨I₁, α₁⟩ s v, ← hraw_some ⟨I₂, α₂⟩ s v, hraw_eq]
    have hI_val : I₁.1 = I₂.1 := by
      ext D; constructor
      · intro hD; obtain ⟨s, rfl⟩ := hpart_surj ⟨I₁, α₁⟩ hD
        rw [hp_eq s]; exact (hpart_mem ⟨I₂, α₂⟩ s).1
      · intro hD; obtain ⟨s, rfl⟩ := hpart_surj ⟨I₂, α₂⟩ hD
        rw [← hp_eq s]; exact (hpart_mem ⟨I₁, α₁⟩ s).1
    have hI_eq : I₁ = I₂ := Subtype.ext hI_val
    subst hI_eq
    congr 1; funext j
    apply Equiv.ext; intro x
    apply (α₂ j).symm.injective
    rw [(α₂ j).symm_apply_apply]
    have hc := hp_eq ⟨j, α₁ j x⟩
    change ((α₁ j).symm (α₁ j x)).1 = ((α₂ j).symm (α₁ j x)).1 at hc
    rw [(α₁ j).symm_apply_apply] at hc
    exact Subtype.ext hc.symm
  have hcard_le : Fintype.card Decorated ≤ Fintype.card (FixedFiberLabeling (V := Fin n) marginNu) :=
    Fintype.card_le_of_injective toLab htoLab_inj
  have hff_eq := card_fixedFiberLabeling_mul_factorials (V := Fin n) marginNu hsum_margin
  rw [Fintype.card_fin] at hff_eq
  have hnat_le : IdentFamily.card * (n_tr.factorial * partialProfileFactorialProduct u nu) ≤
      n.factorial := by
    calc IdentFamily.card * (n_tr.factorial * partialProfileFactorialProduct u nu)
        = (IdentFamily.card * ∏ j : Fin M, (nu j).factorial) *
            ∏ b : SlotNu, (marginNu b).factorial := by
          rw [← hprod_margin]; ring
      _ = Fintype.card Decorated * ∏ b : SlotNu, (marginNu b).factorial := by rw [hDec_card]
      _ ≤ Fintype.card (FixedFiberLabeling (V := Fin n) marginNu) *
            ∏ b : SlotNu, (marginNu b).factorial := Nat.mul_le_mul_right _ hcard_le
      _ = n.factorial := hff_eq
  have hden_pos : (0 : ℝ) < (n_tr.factorial : ℝ) * (partialProfileFactorialProduct u nu : ℝ) := by
    unfold partialProfileFactorialProduct
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos n_tr)
      (Finset.prod_pos fun j _ ↦ mul_pos (pow_pos (Nat.factorial_pos _) _) (Nat.factorial_pos _))
  rw [le_div_iff₀ hden_pos]
  exact_mod_cast hnat_le

private theorem residual_pair_lift_to_tables_le_v13
    {M n X_max u_lo a B s₂_max : ℕ}
    {u r_vec : Fin M → ℕ}
    (hu_inj : Function.Injective u)
    {W_res : Finset (Fin n)}
    (hW_card : W_res.card = selectedVertexMass u r_vec)
    (PairRes : Finset (Finset (Finset (Fin n)) × Finset (Finset (Fin n))))
    (hRes_mem : ∀ pq ∈ PairRes,
      ((pq.1 : Set (Finset (Fin n))).PairwiseDisjoint id ∧
        pq.1.biUnion id = W_res ∧
        pq.1 = Finset.univ.biUnion (fun j : Fin M ↦ pq.1.filter fun D ↦ D.card = u j) ∧
        (∀ j : Fin M, (pq.1.filter fun D ↦ D.card = u j).card = r_vec j)) ∧
      ((pq.2 : Set (Finset (Fin n))).PairwiseDisjoint id ∧
        pq.2.biUnion id = W_res ∧
        pq.2 = Finset.univ.biUnion (fun j : Fin M ↦ pq.2.filter fun D ↦ D.card = u j) ∧
        (∀ j : Fin M, (pq.2.filter fun D ↦ D.card = u j).card = r_vec j)) ∧
      (∀ A ∈ pq.1, ∀ C ∈ pq.2, (A ∩ C).card ≤ X_max ∨ (u_lo ≤ (A ∩ C).card ∧ (A ∩ C).card ≤ a)) ∧
      (((pq.1 ×ˢ pq.2).filter fun ac ↦ X_max < (ac.1 ∩ ac.2).card).card ≤ 2 * B) ∧
      (∑ ac ∈ (pq.1 ×ˢ pq.2).filter (fun ac ↦ 2 ≤ (ac.1 ∩ ac.2).card), (ac.1 ∩ ac.2).card ≤ s₂_max)) :
    let SlotR := Σ j : Fin M, Fin (r_vec j)
    let marginR : SlotR → ℕ := fun s ↦ u s.1
    ∃ ValidTables : Finset (SlotR → SlotR → ℕ),
      (∀ X ∈ ValidTables,
        (∀ s₁ : SlotR, ∑ s₂ : SlotR, X s₁ s₂ = marginR s₁) ∧
        (∀ s₂ : SlotR, ∑ s₁ : SlotR, X s₁ s₂ = marginR s₂) ∧
        (∀ s₁ s₂ : SlotR, X s₁ s₂ ≤ X_max ∨ (u_lo ≤ X s₁ s₂ ∧ X s₁ s₂ ≤ a)) ∧
        (((Finset.univ ×ˢ Finset.univ).filter fun p : SlotR × SlotR ↦ X_max < X p.1 p.2).card ≤ 2 * B) ∧
        (∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : SlotR × SlotR ↦ 2 ≤ X p.1 p.2),
            X p.1 p.2 ≤ s₂_max)) ∧
      (∑ pq ∈ PairRes, (2 : ℝ) ^ (∑ A ∈ pq.1, ∑ C ∈ pq.2, (A ∩ C).card.choose 2)) ≤
        ((W_res.card.factorial : ℝ) / (partialProfileFactorialProduct u r_vec : ℝ)) ^ 2 *
          ∑ X ∈ ValidTables,
            (((∏ s₁ : SlotR, (marginR s₁).factorial : ℝ) *
                (∏ s₂ : SlotR, (marginR s₂).factorial : ℝ)) /
              ((W_res.card.factorial : ℝ) *
                (∏ s₁ : SlotR, ∏ s₂ : SlotR, (X s₁ s₂).factorial : ℝ))) *
              (2 : ℝ) ^ (∑ s₁ : SlotR, ∑ s₂ : SlotR, (X s₁ s₂).choose 2) := by
  intro SlotR marginR
  let IsGoodPart (F : Finset (Finset (Fin n))) : Prop :=
    (F : Set (Finset (Fin n))).PairwiseDisjoint id ∧
    F.biUnion id = W_res ∧
    F = Finset.univ.biUnion (fun j : Fin M ↦ F.filter fun D ↦ D.card = u j) ∧
    (∀ j : Fin M, (F.filter fun D ↦ D.card = u j).card = r_vec j)
  let DecOne := Σ F : {F : Finset (Finset (Fin n)) // IsGoodPart F},
    ∀ j : Fin M, ↥(F.1.filter fun D ↦ D.card = u j) ≃ Fin (r_vec j)
  let partR : DecOne → SlotR → Finset (Fin n) := fun d s ↦ ((d.2 s.1).symm s.2).1
  have hpartR_mem : ∀ (d : DecOne) (s : SlotR),
      partR d s ∈ d.1.1 ∧ (partR d s).card = u s.1 ∧ partR d s ⊆ W_res := by
    intro d s
    obtain ⟨hmem, hcard⟩ := Finset.mem_filter.mp ((d.2 s.1).symm s.2).2
    refine ⟨hmem, hcard, fun v hv ↦ ?_⟩
    rw [← d.1.2.2.1, Finset.mem_biUnion]
    exact ⟨partR d s, hmem, hv⟩
  have hpartR_inj : ∀ d : DecOne, Function.Injective (partR d) := by
    intro d s₁ s₂ heq
    have hj : s₁.1 = s₂.1 :=
      hu_inj ((hpartR_mem d s₁).2.1.symm.trans ((congrArg Finset.card heq).trans (hpartR_mem d s₂).2.1))
    rcases s₁ with ⟨j₁, c₁⟩; rcases s₂ with ⟨j₂, c₂⟩
    dsimp at hj; subst hj
    exact congrArg (Sigma.mk j₁) ((d.2 j₁).symm.injective (Subtype.ext heq))
  have hpartR_surj : ∀ (d : DecOne) {D : Finset (Fin n)}, D ∈ d.1.1 →
      ∃ s : SlotR, partR d s = D := by
    intro d D hD
    have hbi := d.1.2.2.2.1
    rw [hbi, Finset.mem_biUnion] at hD
    rcases hD with ⟨j, _, hDf⟩
    refine ⟨⟨j, d.2 j ⟨D, hDf⟩⟩, ?_⟩
    change ((d.2 j).symm (d.2 j ⟨D, hDf⟩)).1 = D
    exact congrArg Subtype.val ((d.2 j).symm_apply_apply ⟨D, hDf⟩)
  have hex_slot : ∀ (d : DecOne) (v : ↥W_res), ∃ s : SlotR, v.1 ∈ partR d s := by
    intro d v
    have hv : v.1 ∈ d.1.1.biUnion id := d.1.2.2.1.symm ▸ v.2
    rcases Finset.mem_biUnion.mp hv with ⟨D, hD, hvD⟩
    obtain ⟨s, rfl⟩ := hpartR_surj d hD
    exact ⟨s, hvD⟩
  let rawR : DecOne → ↥W_res → SlotR := fun d v ↦ (hex_slot d v).choose
  have hrawR_iff : ∀ (d : DecOne) (s : SlotR) (v : ↥W_res),
      rawR d v = s ↔ v.1 ∈ partR d s := by
    intro d s v
    constructor
    · rintro rfl; exact (hex_slot d v).choose_spec
    · intro hv
      by_contra hne
      have hne_p : partR d (rawR d v) ≠ partR d s := fun hp ↦ hne (hpartR_inj d hp)
      exact Finset.disjoint_left.mp
        (d.1.2.1 (hpartR_mem d (rawR d v)).1 (hpartR_mem d s).1 hne_p)
        (hex_slot d v).choose_spec hv
  let toLabR : DecOne → FixedFiberLabeling (V := ↥W_res) marginR := fun d ↦
    ⟨rawR d, by
      intro s
      unfold labelingFiberCount
      have hbij : (Finset.univ.filter fun v : ↥W_res ↦ rawR d v = s).card = (partR d s).card := by
        refine Finset.card_bij (fun v _ ↦ v.1) ?_ ?_ ?_
        · intro v hv; exact (hrawR_iff d s v).mp (Finset.mem_filter.mp hv).2
        · intro v₁ _ v₂ _ h; exact Subtype.ext h
        · intro x hx
          exact ⟨⟨x, (hpartR_mem d s).2.2 hx⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hrawR_iff d s _).mpr hx⟩, rfl⟩
      exact hbij.trans (hpartR_mem d s).2.1⟩
  have htoLabR_inj : Function.Injective toLabR := by
    rintro ⟨F₁, α₁⟩ ⟨F₂, α₂⟩ heq
    have hraw_eq : rawR ⟨F₁, α₁⟩ = rawR ⟨F₂, α₂⟩ := congrArg Subtype.val heq
    have hp_eq : ∀ s : SlotR, partR ⟨F₁, α₁⟩ s = partR ⟨F₂, α₂⟩ s := by
      intro s; ext x
      constructor
      · intro hx
        have hxW : x ∈ W_res := (hpartR_mem ⟨F₁, α₁⟩ s).2.2 hx
        have hr := (hrawR_iff ⟨F₁, α₁⟩ s ⟨x, hxW⟩).mpr hx
        rw [hraw_eq] at hr
        exact (hrawR_iff ⟨F₂, α₂⟩ s ⟨x, hxW⟩).mp hr
      · intro hx
        have hxW : x ∈ W_res := (hpartR_mem ⟨F₂, α₂⟩ s).2.2 hx
        have hr := (hrawR_iff ⟨F₂, α₂⟩ s ⟨x, hxW⟩).mpr hx
        rw [← hraw_eq] at hr
        exact (hrawR_iff ⟨F₁, α₁⟩ s ⟨x, hxW⟩).mp hr
    have hF_val : F₁.1 = F₂.1 := by
      ext D; constructor
      · intro hD; obtain ⟨s, rfl⟩ := hpartR_surj ⟨F₁, α₁⟩ hD
        rw [hp_eq s]; exact (hpartR_mem ⟨F₂, α₂⟩ s).1
      · intro hD; obtain ⟨s, rfl⟩ := hpartR_surj ⟨F₂, α₂⟩ hD
        rw [← hp_eq s]; exact (hpartR_mem ⟨F₁, α₁⟩ s).1
    have hF_eq : F₁ = F₂ := Subtype.ext hF_val
    subst hF_eq
    congr 1; funext j; apply Equiv.ext; intro x
    apply (α₂ j).symm.injective
    rw [(α₂ j).symm_apply_apply]
    have hc := hp_eq ⟨j, α₁ j x⟩
    change ((α₁ j).symm (α₁ j x)).1 = ((α₂ j).symm (α₁ j x)).1 at hc
    rw [(α₁ j).symm_apply_apply] at hc
    exact Subtype.ext hc.symm
  have hov_cell : ∀ (d₁ d₂ : DecOne) (s₁ s₂ : SlotR),
      orderedOverlapCount (toLabR d₁).1 (toLabR d₂).1 s₁ s₂ =
        (partR d₁ s₁ ∩ partR d₂ s₂).card := by
    intro d₁ d₂ s₁ s₂
    unfold orderedOverlapCount
    refine Finset.card_bij (fun v _ ↦ v.1) ?_ ?_ ?_
    · intro v hv
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hv).2
      exact Finset.mem_inter.mpr ⟨(hrawR_iff d₁ s₁ v).mp h1, (hrawR_iff d₂ s₂ v).mp h2⟩
    · intro v₁ _ v₂ _ h; exact Subtype.ext h
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
      have hxW : x ∈ W_res := (hpartR_mem d₁ s₁).2.2 hx1
      exact ⟨⟨x, hxW⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hrawR_iff d₁ s₁ ⟨x, hxW⟩).mpr hx1, (hrawR_iff d₂ s₂ ⟨x, hxW⟩).mpr hx2⟩, rfl⟩
  let ValidPred (X : SlotR → SlotR → ℕ) : Prop :=
    (∀ s₁ : SlotR, ∑ s₂ : SlotR, X s₁ s₂ = marginR s₁) ∧
    (∀ s₂ : SlotR, ∑ s₁ : SlotR, X s₁ s₂ = marginR s₂) ∧
    (∀ s₁ s₂ : SlotR, X s₁ s₂ ≤ X_max ∨ (u_lo ≤ X s₁ s₂ ∧ X s₁ s₂ ≤ a)) ∧
    (((Finset.univ ×ˢ Finset.univ).filter fun p : SlotR × SlotR ↦ X_max < X p.1 p.2).card ≤ 2 * B) ∧
    (∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : SlotR × SlotR ↦ 2 ≤ X p.1 p.2),
        X p.1 p.2 ≤ s₂_max)
  let LabR := FixedFiberLabeling (V := ↥W_res) marginR
  let ValidLabPairs : Finset (LabR × LabR) :=
    Finset.univ.filter fun rc ↦ ValidPred (orderedOverlapCount rc.1.1 rc.2.1)
  let ValidTables : Finset (SlotR → SlotR → ℕ) :=
    ValidLabPairs.image fun rc ↦ orderedOverlapCount rc.1.1 rc.2.1
  refine ⟨ValidTables, ?_, ?_⟩
  · intro X hX
    rcases Finset.mem_image.mp hX with ⟨rc, hrc, rfl⟩
    exact (Finset.mem_filter.mp hrc).2
  -- Lift `PairRes` with `(∏ j, (r_vec j)!)^2` decorations into `ValidLabPairs`
  let DecPair :=
    Σ pq : ↥PairRes,
      (∀ j : Fin M, ↥(pq.1.1.filter fun D ↦ D.card = u j) ≃ Fin (r_vec j)) ×
      (∀ j : Fin M, ↥(pq.1.2.filter fun D ↦ D.card = u j) ≃ Fin (r_vec j))
  let toLabPair : DecPair → LabR × LabR := fun dp ↦
    let h := hRes_mem dp.1.1 dp.1.2
    (toLabR ⟨⟨dp.1.1.1, h.1⟩, dp.2.1⟩, toLabR ⟨⟨dp.1.1.2, h.2.1⟩, dp.2.2⟩)
  have htoLabPair_inj : Function.Injective toLabPair := by
    rintro ⟨pq₁, α₁, β₁⟩ ⟨pq₂, α₂, β₂⟩ heq
    have h1 := htoLabR_inj (congrArg Prod.fst heq)
    have h2 := htoLabR_inj (congrArg Prod.snd heq)
    have hpq_eq : pq₁ = pq₂ := Subtype.ext (Prod.ext
      (congrArg (fun d : DecOne ↦ d.1.1) h1) (congrArg (fun d : DecOne ↦ d.1.1) h2))
    subst hpq_eq
    congr 1
    refine Prod.ext ?_ ?_
    · exact eq_of_heq (Sigma.ext_iff.mp h1).2
    · exact eq_of_heq (Sigma.ext_iff.mp h2).2
  have hrow_margin : ∀ (rc : LabR × LabR) (s₁ : SlotR),
      ∑ s₂ : SlotR, orderedOverlapCount rc.1.1 rc.2.1 s₁ s₂ = marginR s₁ := by
    intro rc s₁
    have hpart : (Finset.univ.filter fun v : ↥W_res ↦ rc.1.1 v = s₁) =
        Finset.univ.biUnion (fun s₂ : SlotR ↦
          Finset.univ.filter fun v : ↥W_res ↦ rc.1.1 v = s₁ ∧ rc.2.1 v = s₂) := by
      ext v; simp
    have hdisj : ((Finset.univ : Finset SlotR) : Set SlotR).PairwiseDisjoint
        (fun s₂ : SlotR ↦ Finset.univ.filter fun v : ↥W_res ↦ rc.1.1 v = s₁ ∧ rc.2.1 v = s₂) := by
      intro x _ y _ hne; rw [Function.onFun, Finset.disjoint_left]
      intro v h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.2.symm.trans (Finset.mem_filter.mp h2).2.2)
    have hc := congrArg Finset.card hpart
    rw [Finset.card_biUnion hdisj] at hc
    exact hc.symm.trans (rc.1.2 s₁)
  have hcol_margin : ∀ (rc : LabR × LabR) (s₂ : SlotR),
      ∑ s₁ : SlotR, orderedOverlapCount rc.1.1 rc.2.1 s₁ s₂ = marginR s₂ := by
    intro rc s₂
    have hpart : (Finset.univ.filter fun v : ↥W_res ↦ rc.2.1 v = s₂) =
        Finset.univ.biUnion (fun s₁ : SlotR ↦
          Finset.univ.filter fun v : ↥W_res ↦ rc.1.1 v = s₁ ∧ rc.2.1 v = s₂) := by
      ext v; simp
    have hdisj : ((Finset.univ : Finset SlotR) : Set SlotR).PairwiseDisjoint
        (fun s₁ : SlotR ↦ Finset.univ.filter fun v : ↥W_res ↦ rc.1.1 v = s₁ ∧ rc.2.1 v = s₂) := by
      intro x _ y _ hne; rw [Function.onFun, Finset.disjoint_left]
      intro v h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.1.symm.trans (Finset.mem_filter.mp h2).2.1)
    have hc := congrArg Finset.card hpart
    rw [Finset.card_biUnion hdisj] at hc
    exact hc.symm.trans (rc.2.2 s₂)
  have htoLabPair_mem : ∀ dp : DecPair,
      toLabPair dp ∈ ValidLabPairs ∧
      (∑ s₁ : SlotR, ∑ s₂ : SlotR,
          (orderedOverlapCount (toLabPair dp).1.1 (toLabPair dp).2.1 s₁ s₂).choose 2) =
        ∑ A ∈ dp.1.1.1, ∑ C ∈ dp.1.1.2, (A ∩ C).card.choose 2 := by
    intro dp
    have h := hRes_mem dp.1.1 dp.1.2
    let d₁ : DecOne := ⟨⟨dp.1.1.1, h.1⟩, dp.2.1⟩
    let d₂ : DecOne := ⟨⟨dp.1.1.2, h.2.1⟩, dp.2.2⟩
    have hov : ∀ s₁ s₂ : SlotR,
        orderedOverlapCount (toLabPair dp).1.1 (toLabPair dp).2.1 s₁ s₂ =
          (partR d₁ s₁ ∩ partR d₂ s₂).card := hov_cell d₁ d₂
    have hbij_prod : ∀ (P_f : Finset (Fin n) → Finset (Fin n) → Prop) [DecidableRel P_f]
        (g : Finset (Fin n) → Finset (Fin n) → ℕ),
        (∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : SlotR × SlotR ↦ P_f (partR d₁ p.1) (partR d₂ p.2)),
            g (partR d₁ p.1) (partR d₂ p.2)) =
          ∑ ac ∈ (dp.1.1.1 ×ˢ dp.1.1.2).filter (fun ac ↦ P_f ac.1 ac.2), g ac.1 ac.2 := by
      intro P_f _ g
      refine Finset.sum_bij (fun p _ ↦ (partR d₁ p.1, partR d₂ p.2)) ?_ ?_ ?_ (fun _ _ ↦ rfl)
      · intro p hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(hpartR_mem d₁ p.1).1, (hpartR_mem d₂ p.2).1⟩,
          (Finset.mem_filter.mp hp).2⟩
      · intro p₁ _ p₂ _ heq
        exact Prod.ext (hpartR_inj d₁ (congrArg Prod.fst heq)) (hpartR_inj d₂ (congrArg Prod.snd heq))
      · intro ac hac
        obtain ⟨hmem_ac, hPac⟩ := Finset.mem_filter.mp hac
        obtain ⟨hA, hC⟩ := Finset.mem_product.mp hmem_ac
        obtain ⟨s₁, hs₁⟩ := hpartR_surj d₁ hA
        obtain ⟨s₂, hs₂⟩ := hpartR_surj d₂ hC
        exact ⟨(s₁, s₂), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
          by rwa [hs₁, hs₂]⟩, Prod.ext hs₁ hs₂⟩
    have hval : ValidPred (orderedOverlapCount (toLabPair dp).1.1 (toLabPair dp).2.1) := by
      refine ⟨hrow_margin _, hcol_margin _, ?_, ?_, ?_⟩
      · intro s₁ s₂; rw [hov s₁ s₂]
        exact h.2.2.1 (partR d₁ s₁) (hpartR_mem d₁ s₁).1 (partR d₂ s₂) (hpartR_mem d₂ s₂).1
      · simp_rw [hov]
        have hc := hbij_prod (fun A C ↦ X_max < (A ∩ C).card) (fun _ _ ↦ 1)
        simp only [Finset.sum_const, smul_eq_mul, mul_one] at hc
        rw [hc]; exact h.2.2.2.1
      · simp_rw [hov]
        rw [hbij_prod (fun A C ↦ 2 ≤ (A ∩ C).card) (fun A C ↦ (A ∩ C).card)]
        exact h.2.2.2.2
    have hsum_ch :
        (∑ s₁ : SlotR, ∑ s₂ : SlotR, (partR d₁ s₁ ∩ partR d₂ s₂).card.choose 2) =
          ∑ A ∈ dp.1.1.1, ∑ C ∈ dp.1.1.2, (A ∩ C).card.choose 2 := by
      rw [← Finset.sum_product', ← Finset.sum_product']
      have hc := hbij_prod (fun _ _ ↦ True) (fun A C ↦ (A ∩ C).card.choose 2)
      simpa using hc
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hval⟩, ?_⟩
    simp_rw [hov]; exact hsum_ch
  -- Relate sum over `PairRes` to sum over `ValidLabPairs`
  let r_fac : ℕ := ∏ j : Fin M, (r_vec j).factorial
  have hr_fac_pos : (0 : ℝ) < (r_fac : ℝ) := by
    dsimp [r_fac]; exact_mod_cast Finset.prod_pos fun j _ ↦ Nat.factorial_pos _
  have hfib_card : ∀ pq : ↥PairRes,
      Fintype.card
        ((∀ j : Fin M, ↥(pq.1.1.filter fun D ↦ D.card = u j) ≃ Fin (r_vec j)) ×
          (∀ j : Fin M, ↥(pq.1.2.filter fun D ↦ D.card = u j) ≃ Fin (r_vec j))) = r_fac ^ 2 := by
    intro pq
    have h := hRes_mem pq.1 pq.2
    rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_pi, sq]
    congr 1
    · refine Finset.prod_congr rfl fun j _ ↦ ?_
      have hc : Fintype.card ↥(pq.1.1.filter fun D ↦ D.card = u j) = r_vec j := by
        rw [Fintype.card_coe, h.1.2.2.2 j]
      exact (Fintype.card_congr (Equiv.equivCongr (Fintype.equivFinOfCardEq hc) (Equiv.refl _))).trans
        (by rw [Fintype.card_perm, Fintype.card_fin])
    · refine Finset.prod_congr rfl fun j _ ↦ ?_
      have hc : Fintype.card ↥(pq.1.2.filter fun D ↦ D.card = u j) = r_vec j := by
        rw [Fintype.card_coe, h.2.1.2.2.2 j]
      exact (Fintype.card_congr (Equiv.equivCongr (Fintype.equivFinOfCardEq hc) (Equiv.refl _))).trans
        (by rw [Fintype.card_perm, Fintype.card_fin])
  have hsum_lift :
      ((r_fac : ℝ) ^ 2) *
          (∑ pq ∈ PairRes, (2 : ℝ) ^ (∑ A ∈ pq.1, ∑ C ∈ pq.2, (A ∩ C).card.choose 2)) ≤
        ∑ rc ∈ ValidLabPairs,
          (2 : ℝ) ^ (∑ s₁ : SlotR, ∑ s₂ : SlotR, (orderedOverlapCount rc.1.1 rc.2.1 s₁ s₂).choose 2) := by
    have h1 : ((r_fac : ℝ) ^ 2) *
        (∑ pq ∈ PairRes, (2 : ℝ) ^ (∑ A ∈ pq.1, ∑ C ∈ pq.2, (A ∩ C).card.choose 2)) =
        ∑ dp : DecPair,
          (2 : ℝ) ^ (∑ s₁ : SlotR, ∑ s₂ : SlotR,
            (orderedOverlapCount (toLabPair dp).1.1 (toLabPair dp).2.1 s₁ s₂).choose 2) := by
      simp_rw [(htoLabPair_mem _).2]
      dsimp [DecPair]
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp_rw [hfib_card, Nat.cast_pow]
      rw [← Finset.mul_sum, Finset.sum_coe_sort PairRes
        (fun pq ↦ (2 : ℝ) ^ ∑ A ∈ pq.1, ∑ C ∈ pq.2, (A ∩ C).card.choose 2)]
    rw [h1, ← Finset.sum_image (f := fun rc : LabR × LabR ↦
      (2 : ℝ) ^ (∑ s₁ : SlotR, ∑ s₂ : SlotR, (orderedOverlapCount rc.1.1 rc.2.1 s₁ s₂).choose 2))
      (fun a _ b _ hab ↦ htoLabPair_inj hab)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ ↦ by positivity)
    intro rc hrc
    rcases Finset.mem_image.mp hrc with ⟨dp, _, rfl⟩
    exact (htoLabPair_mem dp).1
  -- Fiber `ValidLabPairs` over `X ∈ ValidTables`
  have htotal_margin : ∑ s : SlotR, marginR s = Fintype.card ↥W_res := by
    have huniv_sig : (Finset.univ : Finset SlotR) =
        Finset.univ.sigma (fun j : Fin M ↦ (Finset.univ : Finset (Fin (r_vec j)))) := by
      ext x; simp
    rw [huniv_sig, Finset.sum_sigma]
    have h1 : (∑ j : Fin M, ∑ _c : Fin (r_vec j), u j) = selectedVertexMass u r_vec := by
      unfold selectedVertexMass
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp [Finset.sum_const, smul_eq_mul, mul_comm]
    dsimp [marginR]; rw [h1, Fintype.card_coe, hW_card]
  have hprod_marginR :
      (∏ s : SlotR, (marginR s).factorial) * r_fac = partialProfileFactorialProduct u r_vec := by
    have huniv_sig : (Finset.univ : Finset SlotR) =
        Finset.univ.sigma (fun j : Fin M ↦ (Finset.univ : Finset (Fin (r_vec j)))) := by
      ext x; simp
    rw [huniv_sig, Finset.prod_sigma]
    have h1 : (∏ j : Fin M, ∏ _c : Fin (r_vec j), (u j).factorial) =
        ∏ j : Fin M, (u j).factorial ^ (r_vec j) := by
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      simp [Finset.prod_const]
    dsimp [marginR, r_fac]; rw [h1, ← Finset.prod_mul_distrib]; rfl
  have hff_card := card_fixedFiberLabeling_mul_factorials (V := ↥W_res) marginR htotal_margin
  rw [Fintype.card_coe] at hff_card
  have hfibre_X : ∀ X ∈ ValidTables,
      ((ValidLabPairs.filter fun rc ↦ orderedOverlapCount rc.1.1 rc.2.1 = X).card : ℝ) ≤
        ((r_fac : ℝ) ^ 2) *
          ((W_res.card.factorial : ℝ) / (partialProfileFactorialProduct u r_vec : ℝ)) ^ 2 *
          (((∏ s₁ : SlotR, (marginR s₁).factorial : ℝ) *
              (∏ s₂ : SlotR, (marginR s₂).factorial : ℝ)) /
            ((W_res.card.factorial : ℝ) *
              (∏ s₁ : SlotR, ∏ s₂ : SlotR, (X s₁ s₂).factorial : ℝ))) := by
    intro X hX
    rcases Finset.mem_image.mp hX with ⟨rc₀, hrc₀, rfl⟩
    set X₀ := orderedOverlapCount rc₀.1.1 rc₀.2.1
    have hX₀_row : ∀ s₁ : SlotR, ∑ s₂ : SlotR, X₀ s₁ s₂ = marginR s₁ :=
      ((Finset.mem_filter.mp hrc₀).2).1
    have hrow_slice : ∀ row : LabR,
        ((Finset.univ.filter fun col : LabR ↦ orderedOverlapCount row.1 col.1 = X₀).card) *
          (∏ s₁ : SlotR, ∏ s₂ : SlotR, (X₀ s₁ s₂).factorial) ≤
          ∏ s₁ : SlotR, (marginR s₁).factorial := by
      intro row
      have hrow_eq : ∀ s₁ : SlotR, ∑ s₂ : SlotR, X₀ s₁ s₂ = labelingFiberCount row.1 s₁ :=
        fun s₁ ↦ (hX₀_row s₁).trans (row.2 s₁).symm
      have hov_eq := card_orderedOverlapLabeling_mul_factorials row.1 X₀ hrow_eq
      have hle_card :
          (Finset.univ.filter fun col : LabR ↦ orderedOverlapCount row.1 col.1 = X₀).card ≤
            Fintype.card (OrderedOverlapLabeling row.1 X₀) := by
        rw [← Fintype.card_coe]
        let toOv : ↥(Finset.univ.filter fun col : LabR ↦ orderedOverlapCount row.1 col.1 = X₀) →
            OrderedOverlapLabeling row.1 X₀ :=
          fun c ↦ ⟨c.1.1, fun s₁ s₂ ↦ by
            have heq := (Finset.mem_filter.mp c.2).2
            exact congrFun (congrFun heq s₁) s₂⟩
        refine Fintype.card_le_of_injective toOv fun c₁ c₂ h ↦ ?_
        have hcol : c₁.1.1 = c₂.1.1 := congrArg (fun x : OrderedOverlapLabeling row.1 X₀ ↦ x.1) h
        have hlab : c₁.1 = c₂.1 := Subtype.ext hcol
        exact Subtype.ext hlab
      calc (Finset.univ.filter fun col : LabR ↦ orderedOverlapCount row.1 col.1 = X₀).card *
              (∏ s₁ : SlotR, ∏ s₂ : SlotR, (X₀ s₁ s₂).factorial)
          ≤ Fintype.card (OrderedOverlapLabeling row.1 X₀) *
              (∏ s₁ : SlotR, ∏ s₂ : SlotR, (X₀ s₁ s₂).factorial) :=
            Nat.mul_le_mul_right _ hle_card
        _ = ∏ s₁ : SlotR, (labelingFiberCount row.1 s₁).factorial := hov_eq
        _ = ∏ s₁ : SlotR, (marginR s₁).factorial :=
            Finset.prod_congr rfl fun s₁ _ ↦ congrArg Nat.factorial (row.2 s₁)
    have htot_nat :
        (ValidLabPairs.filter fun rc ↦ orderedOverlapCount rc.1.1 rc.2.1 = X₀).card *
          (∏ s₁ : SlotR, ∏ s₂ : SlotR, (X₀ s₁ s₂).factorial) ≤
          Fintype.card LabR * ∏ s₁ : SlotR, (marginR s₁).factorial := by
      have hsub_p : (ValidLabPairs.filter fun rc ↦ orderedOverlapCount rc.1.1 rc.2.1 = X₀) ⊆
          (Finset.univ ×ˢ Finset.univ).filter (fun rc : LabR × LabR ↦ orderedOverlapCount rc.1.1 rc.2.1 = X₀) :=
        fun rc hrc ↦ Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
          (Finset.mem_filter.mp hrc).2⟩
      have hc1 : (ValidLabPairs.filter fun rc ↦ orderedOverlapCount rc.1.1 rc.2.1 = X₀).card ≤
          ∑ row : LabR, (Finset.univ.filter fun col : LabR ↦ orderedOverlapCount row.1 col.1 = X₀).card := by
        refine (Finset.card_le_card hsub_p).trans ?_
        rw [Finset.card_filter, Finset.sum_product]
        exact le_of_eq (Finset.sum_congr rfl fun row _ ↦ (Finset.card_filter _ _).symm)
      calc (ValidLabPairs.filter fun rc ↦ orderedOverlapCount rc.1.1 rc.2.1 = X₀).card *
              (∏ s₁ : SlotR, ∏ s₂ : SlotR, (X₀ s₁ s₂).factorial)
          ≤ (∑ row : LabR, (Finset.univ.filter fun col : LabR ↦ orderedOverlapCount row.1 col.1 = X₀).card) *
              (∏ s₁ : SlotR, ∏ s₂ : SlotR, (X₀ s₁ s₂).factorial) := Nat.mul_le_mul_right _ hc1
        _ = ∑ row : LabR, (Finset.univ.filter fun col : LabR ↦ orderedOverlapCount row.1 col.1 = X₀).card *
              (∏ s₁ : SlotR, ∏ s₂ : SlotR, (X₀ s₁ s₂).factorial) := Finset.sum_mul _ _ _
        _ ≤ ∑ _row : LabR, ∏ s₁ : SlotR, (marginR s₁).factorial :=
            Finset.sum_le_sum fun row _ ↦ hrow_slice row
        _ = Fintype.card LabR * ∏ s₁ : SlotR, (marginR s₁).factorial := by
            simp [Finset.sum_const, smul_eq_mul]
    have htot_R :
        ((ValidLabPairs.filter fun rc ↦ orderedOverlapCount rc.1.1 rc.2.1 = X₀).card : ℝ) *
          (∏ s₁ : SlotR, ∏ s₂ : SlotR, (X₀ s₁ s₂).factorial : ℝ) ≤
          (Fintype.card LabR : ℝ) * (∏ s₁ : SlotR, (marginR s₁).factorial : ℝ) := by
      exact_mod_cast htot_nat
    have hff_R : (Fintype.card LabR : ℝ) * (∏ s : SlotR, (marginR s).factorial : ℝ) =
        (W_res.card.factorial : ℝ) := by exact_mod_cast hff_card
    have hpm_R : (∏ s : SlotR, (marginR s).factorial : ℝ) * (r_fac : ℝ) =
        (partialProfileFactorialProduct u r_vec : ℝ) := by exact_mod_cast hprod_marginR
    have hpf_pos : (0 : ℝ) < (partialProfileFactorialProduct u r_vec : ℝ) := by
      unfold partialProfileFactorialProduct
      exact_mod_cast Finset.prod_pos fun j _ ↦
        mul_pos (pow_pos (Nat.factorial_pos _) _) (Nat.factorial_pos _)
    have hXfac_pos : (0 : ℝ) < (∏ s₁ : SlotR, ∏ s₂ : SlotR, (X₀ s₁ s₂).factorial : ℝ) := by
      exact_mod_cast Finset.prod_pos fun _ _ ↦ Finset.prod_pos fun _ _ ↦ Nat.factorial_pos _
    have hWfac_pos : (0 : ℝ) < (W_res.card.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have hrhs_eq :
        ((r_fac : ℝ) ^ 2) *
          ((W_res.card.factorial : ℝ) / (partialProfileFactorialProduct u r_vec : ℝ)) ^ 2 *
          (((∏ s₁ : SlotR, (marginR s₁).factorial : ℝ) *
              (∏ s₂ : SlotR, (marginR s₂).factorial : ℝ)) /
            ((W_res.card.factorial : ℝ) *
              (∏ s₁ : SlotR, ∏ s₂ : SlotR, (X₀ s₁ s₂).factorial : ℝ))) =
        ((Fintype.card LabR : ℝ) * (∏ s₁ : SlotR, (marginR s₁).factorial : ℝ)) /
          (∏ s₁ : SlotR, ∏ s₂ : SlotR, (X₀ s₁ s₂).factorial : ℝ) := by
      rw [← hpm_R, ← hff_R]
      have hm_pos : (0 : ℝ) < (∏ s : SlotR, (marginR s).factorial : ℝ) := by
        exact_mod_cast Finset.prod_pos fun _ _ ↦ Nat.factorial_pos _
      have hcard_pos : (0 : ℝ) < (Fintype.card LabR : ℝ) := by
        by_contra hle; have hz : (Fintype.card LabR : ℝ) = 0 := le_antisymm (not_lt.mp hle) (Nat.cast_nonneg _)
        rw [hz, zero_mul] at hff_R; linarith [hWfac_pos, hff_R]
      field_simp [hr_fac_pos.ne', hm_pos.ne', hcard_pos.ne', hXfac_pos.ne']
    rw [hrhs_eq, le_div_iff₀ hXfac_pos]
    exact htot_R
  have hpart_tables :
      (∑ rc ∈ ValidLabPairs,
          (2 : ℝ) ^ (∑ s₁ : SlotR, ∑ s₂ : SlotR, (orderedOverlapCount rc.1.1 rc.2.1 s₁ s₂).choose 2)) =
        ∑ X ∈ ValidTables,
          ((ValidLabPairs.filter fun rc ↦ orderedOverlapCount rc.1.1 rc.2.1 = X).card : ℝ) *
            (2 : ℝ) ^ (∑ s₁ : SlotR, ∑ s₂ : SlotR, (X s₁ s₂).choose 2) := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun rc : LabR × LabR ↦ orderedOverlapCount rc.1.1 rc.2.1)
      (fun rc hrc ↦ Finset.mem_image_of_mem _ hrc)]
    refine Finset.sum_congr rfl fun X _ ↦ ?_
    trans ∑ _rc ∈ ValidLabPairs.filter (fun rc ↦ orderedOverlapCount rc.1.1 rc.2.1 = X),
        (2 : ℝ) ^ (∑ s₁ : SlotR, ∑ s₂ : SlotR, (X s₁ s₂).choose 2)
    · refine Finset.sum_congr rfl fun rc hrc ↦ ?_
      rw [(Finset.mem_filter.mp hrc).2]
    · simp [Finset.sum_const, nsmul_eq_mul]
  have htot_sum :
      ((r_fac : ℝ) ^ 2) *
          (∑ pq ∈ PairRes, (2 : ℝ) ^ (∑ A ∈ pq.1, ∑ C ∈ pq.2, (A ∩ C).card.choose 2)) ≤
        ((r_fac : ℝ) ^ 2) *
          (((W_res.card.factorial : ℝ) / (partialProfileFactorialProduct u r_vec : ℝ)) ^ 2 *
            ∑ X ∈ ValidTables,
              (((∏ s₁ : SlotR, (marginR s₁).factorial : ℝ) *
                  (∏ s₂ : SlotR, (marginR s₂).factorial : ℝ)) /
                ((W_res.card.factorial : ℝ) *
                  (∏ s₁ : SlotR, ∏ s₂ : SlotR, (X s₁ s₂).factorial : ℝ))) *
                (2 : ℝ) ^ (∑ s₁ : SlotR, ∑ s₂ : SlotR, (X s₁ s₂).choose 2)) := by
    refine hsum_lift.trans ?_
    rw [hpart_tables, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun X hX ↦ ?_
    have hf := mul_le_mul_of_nonneg_right (hfibre_X X hX)
      (pow_nonneg two_pos.le (∑ s₁ : SlotR, ∑ s₂ : SlotR, (X s₁ s₂).choose 2))
    exact hf.trans_eq (by ring)
  exact le_of_mul_le_mul_left htot_sum (pow_pos hr_fac_pos 2)


private theorem peeled_heavyMatrix_fibre_le_v13
    {I : Type*} [Fintype I] [DecidableEq I]
    {n_tr alpha : ℕ} (hn_tr : 1 ≤ n_tr) (halpha_ntr : alpha ≤ n_tr)
    {margin : I → ℕ} (hmargin_sum : ∑ s : I, margin s = n_tr)
    (hmargin_le : ∀ s : I, margin s ≤ alpha)
    {B_sizes : Finset ℕ} (hB_bds : ∀ x ∈ B_sizes, 2 ≤ x ∧ x ≤ alpha)
    {H : I → I → ℕ}
    (hH_mem : ∀ s₁ s₂ : I, H s₁ s₂ = 0 ∨ H s₁ s₂ ∈ B_sizes)
    (hH_row : ∀ s₁ : I, ∑ s₂ : I, H s₁ s₂ ≤ margin s₁)
    (hH_col : ∀ s₂ : I, ∑ s₁ : I, H s₁ s₂ ≤ margin s₂)
    (hs₂_half : 2 * (∑ s₁ : I, ∑ s₂ : I, H s₁ s₂) ≤ n_tr)
    (Fibre_H : Finset (I → I → ℕ))
    (hFibre : ∀ X ∈ Fibre_H,
      (∀ s₁ s₂ : I, (if 2 ≤ X s₁ s₂ then X s₁ s₂ else 0) = H s₁ s₂) ∧
      (∀ s₁ : I, ∑ s₂ : I, X s₁ s₂ = margin s₁) ∧
      (∀ s₂ : I, ∑ s₁ : I, X s₁ s₂ = margin s₂)) :
    let r_H : ℕ → ℕ := fun x ↦
      ((Finset.univ ×ˢ Finset.univ).filter fun p : I × I ↦ H p.1 p.2 = x).card
    (∑ X ∈ Fibre_H,
        (((∏ s₁ : I, (margin s₁).factorial : ℝ) *
            (∏ s₂ : I, (margin s₂).factorial : ℝ)) /
          ((n_tr.factorial : ℝ) *
            (∏ s₁ : I, ∏ s₂ : I, (X s₁ s₂).factorial : ℝ))) *
          (2 : ℝ) ^ (∑ s₁ : I, ∑ s₂ : I, (X s₁ s₂).choose 2)) ≤
      ∏ x ∈ B_sizes,
        (Real.exp (x : ℝ) * ((alpha : ℝ) ^ x / (x.factorial : ℝ)) ^ 2 *
          (2 : ℝ) ^ (x.choose 2) / (n_tr.choose x : ℝ)) ^ (r_H x) := by
  intro r_H
  set s₂_H : ℕ := ∑ s₁ : I, ∑ s₂ : I, H s₁ s₂
  let sigma₁ : I → ℕ := fun s₁ ↦ margin s₁ - ∑ s₂ : I, H s₁ s₂
  let tau₁ : I → ℕ := fun s₂ ↦ margin s₂ - ∑ s₁ : I, H s₁ s₂
  have hXH_invar : ∀ X ∈ Fibre_H,
      (∏ s₁ : I, ∏ s₂ : I, (X s₁ s₂).factorial) = (∏ s₁ : I, ∏ s₂ : I, (H s₁ s₂).factorial) ∧
      (∑ s₁ : I, ∑ s₂ : I, (X s₁ s₂).choose 2) = (∑ s₁ : I, ∑ s₂ : I, (H s₁ s₂).choose 2) := by
    intro X hX
    have hpt : ∀ s₁ s₂ : I,
        (X s₁ s₂).factorial = (H s₁ s₂).factorial ∧ (X s₁ s₂).choose 2 = (H s₁ s₂).choose 2 := by
      intro s₁ s₂
      have heq := (hFibre X hX).1 s₁ s₂
      by_cases h2 : 2 ≤ X s₁ s₂
      · rw [if_pos h2] at heq; rw [heq]; exact ⟨rfl, rfl⟩
      · rw [if_neg h2] at heq; rw [← heq]
        have hlt : X s₁ s₂ < 2 := Nat.lt_of_not_ge h2
        interval_cases X s₁ s₂ <;> exact ⟨rfl, rfl⟩
    exact ⟨Finset.prod_congr rfl fun s₁ _ ↦ Finset.prod_congr rfl fun s₂ _ ↦ (hpt s₁ s₂).1,
      Finset.sum_congr rfl fun s₁ _ ↦ Finset.sum_congr rfl fun s₂ _ ↦ (hpt s₁ s₂).2⟩
  -- Map `X ∈ Fibre_H` injectively to `A₁_of X ∈ zeroOneMatricesWithMargins sigma₁ tau₁`
  let A₁_of : (I → I → ℕ) → Finset (I × I) := fun X ↦
    (Finset.univ ×ˢ Finset.univ).filter fun p : I × I ↦ X p.1 p.2 = 1
  have hX_split : ∀ X ∈ Fibre_H, ∀ s₁ s₂ : I,
      X s₁ s₂ = (if (s₁, s₂) ∈ A₁_of X then 1 else 0) + H s₁ s₂ := by
    intro X hX s₁ s₂
    have heq := (hFibre X hX).1 s₁ s₂
    have hmem_iff : (s₁, s₂) ∈ A₁_of X ↔ X s₁ s₂ = 1 := by simp [A₁_of]
    simp only [hmem_iff]
    by_cases h2 : 2 ≤ X s₁ s₂
    · rw [if_pos h2] at heq; rw [← heq, if_neg (by omega), zero_add]
    · rw [if_neg h2] at heq; rw [← heq, add_zero]
      have hlt : X s₁ s₂ < 2 := Nat.lt_of_not_ge h2
      interval_cases X s₁ s₂ <;> simp
  have hA₁_mem : ∀ X ∈ Fibre_H, A₁_of X ∈ zeroOneMatricesWithMargins sigma₁ tau₁ := by
    intro X hX
    unfold zeroOneMatricesWithMargins
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro s₁
      have hrow_card : ((A₁_of X).filter fun p : I × I ↦ p.1 = s₁).card =
          ∑ s₂ : I, if (s₁, s₂) ∈ A₁_of X then 1 else 0 := by
        rw [← Finset.card_filter]
        refine Finset.card_bij (fun p _ ↦ p.2) ?_ ?_ ?_
        · intro p hp
          obtain ⟨hpA, hp1⟩ := Finset.mem_filter.mp hp
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rcases p with ⟨a, b⟩; dsimp at hp1; subst hp1; exact hpA
        · intro p₁ hp₁ p₂ hp₂ hb
          have h1 := (Finset.mem_filter.mp hp₁).2
          have h2 := (Finset.mem_filter.mp hp₂).2
          exact Prod.ext (h1.trans h2.symm) hb
        · intro s₂ hs₂
          have hm := (Finset.mem_filter.mp hs₂).2
          exact ⟨(s₁, s₂), Finset.mem_filter.mpr ⟨hm, rfl⟩, rfl⟩
      have hsum_X := (hFibre X hX).2.1 s₁
      rw [Finset.sum_congr rfl fun s₂ _ ↦ hX_split X hX s₁ s₂, Finset.sum_add_distrib] at hsum_X
      rw [hrow_card]; dsimp [sigma₁]; omega
    · intro s₂
      have hcol_card : ((A₁_of X).filter fun p : I × I ↦ p.2 = s₂).card =
          ∑ s₁ : I, if (s₁, s₂) ∈ A₁_of X then 1 else 0 := by
        rw [← Finset.card_filter]
        refine Finset.card_bij (fun p _ ↦ p.1) ?_ ?_ ?_
        · intro p hp
          obtain ⟨hpA, hp2⟩ := Finset.mem_filter.mp hp
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rcases p with ⟨a, b⟩; dsimp at hp2; subst hp2; exact hpA
        · intro p₁ hp₁ p₂ hp₂ ha
          have h1 := (Finset.mem_filter.mp hp₁).2
          have h2 := (Finset.mem_filter.mp hp₂).2
          exact Prod.ext ha (h1.trans h2.symm)
        · intro s₁ hs₁
          have hm := (Finset.mem_filter.mp hs₁).2
          exact ⟨(s₁, s₂), Finset.mem_filter.mpr ⟨hm, rfl⟩, rfl⟩
      have hsum_X := (hFibre X hX).2.2 s₂
      rw [Finset.sum_congr rfl fun s₁ _ ↦ hX_split X hX s₁ s₂, Finset.sum_add_distrib] at hsum_X
      rw [hcol_card]; dsimp [tau₁]; omega
  have hFibre_card : Fibre_H.card ≤ (zeroOneMatricesWithMargins sigma₁ tau₁).card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    refine Fintype.card_le_of_injective
      (fun X ↦ ⟨A₁_of X.1, hA₁_mem X.1 X.2⟩) ?_
    intro X₁ X₂ heq
    have hA_eq : A₁_of X₁.1 = A₁_of X₂.1 := congrArg Subtype.val heq
    apply Subtype.ext; funext s₁ s₂
    rw [hX_split X₁.1 X₁.2 s₁ s₂, hX_split X₂.1 X₂.2 s₁ s₂, hA_eq]
  have hsum_sigma : ∑ s₁ : I, sigma₁ s₁ = n_tr - s₂_H := by
    have hadd : (∑ s₁ : I, sigma₁ s₁) + s₂_H = n_tr := by
      dsimp [sigma₁, s₂_H]
      rw [← Finset.sum_add_distrib]
      calc ∑ s₁ : I, ((margin s₁ - ∑ s₂ : I, H s₁ s₂) + ∑ s₂ : I, H s₁ s₂)
          = ∑ s₁ : I, margin s₁ := Finset.sum_congr rfl fun s₁ _ ↦ Nat.sub_add_cancel (hH_row s₁)
        _ = n_tr := hmargin_sum
    omega
  have hsum_tau : ∑ s₂ : I, tau₁ s₂ = n_tr - s₂_H := by
    have hadd : (∑ s₂ : I, tau₁ s₂) + s₂_H = n_tr := by
      dsimp [tau₁, s₂_H]
      rw [Finset.sum_comm (f := H), ← Finset.sum_add_distrib]
      calc ∑ s₂ : I, ((margin s₂ - ∑ s₁ : I, H s₁ s₂) + ∑ s₁ : I, H s₁ s₂)
          = ∑ s₂ : I, margin s₂ := Finset.sum_congr rfl fun s₂ _ ↦ Nat.sub_add_cancel (hH_col s₂)
        _ = n_tr := hmargin_sum
    omega
  have hstub := card_zeroOneMatrices_mul_factorials_le sigma₁ tau₁ (n_tr - s₂_H) hsum_sigma hsum_tau
  -- Row and column factorial peeling
  let eI : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hpeel_row : ∀ s₁ : I,
      (margin s₁).factorial ≤ (sigma₁ s₁).factorial * ∏ s₂ : I, alpha ^ (H s₁ s₂) := by
    intro s₁
    have hsum_e : ∑ i : Fin (Fintype.card I), H s₁ (eI i) = ∑ s₂ : I, H s₁ s₂ :=
      eI.sum_comp (fun s₂ ↦ H s₁ s₂)
    have hp := factorial_le_residual_mul_prod_choose (margin s₁) (fun i ↦ H s₁ (eI i))
      (hsum_e.trans_le (hH_row s₁))
    rw [hsum_e, eI.prod_comp (fun s₂ ↦ (H s₁ s₂).factorial * (margin s₁).choose (H s₁ s₂))] at hp
    refine hp.trans (Nat.mul_le_mul_left _ (Finset.prod_le_prod' fun s₂ _ ↦ ?_))
    exact (nat_factorial_mul_choose_le_pow_v13 (margin s₁) (H s₁ s₂)).trans
      (Nat.pow_le_pow_left (hmargin_le s₁) _)
  have hpeel_col : ∀ s₂ : I,
      (margin s₂).factorial ≤ (tau₁ s₂).factorial * ∏ s₁ : I, alpha ^ (H s₁ s₂) := by
    intro s₂
    have hsum_e : ∑ i : Fin (Fintype.card I), H (eI i) s₂ = ∑ s₁ : I, H s₁ s₂ :=
      eI.sum_comp (fun s₁ ↦ H s₁ s₂)
    have hp := factorial_le_residual_mul_prod_choose (margin s₂) (fun i ↦ H (eI i) s₂)
      (hsum_e.trans_le (hH_col s₂))
    rw [hsum_e, eI.prod_comp (fun s₁ ↦ (H s₁ s₂).factorial * (margin s₂).choose (H s₁ s₂))] at hp
    refine hp.trans (Nat.mul_le_mul_left _ (Finset.prod_le_prod' fun s₁ _ ↦ ?_))
    exact (nat_factorial_mul_choose_le_pow_v13 (margin s₂) (H s₁ s₂)).trans
      (Nat.pow_le_pow_left (hmargin_le s₂) _)
  have hcomb_nat :
      Fibre_H.card * (∏ s₁ : I, (margin s₁).factorial) * (∏ s₂ : I, (margin s₂).factorial) ≤
        (n_tr - s₂_H).factorial * ∏ s₁ : I, ∏ s₂ : I, alpha ^ (2 * H s₁ s₂) := by
    have hr_prod : (∏ s₁ : I, (margin s₁).factorial) ≤
        (∏ s₁ : I, (sigma₁ s₁).factorial) * ∏ s₁ : I, ∏ s₂ : I, alpha ^ (H s₁ s₂) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod' fun s₁ _ ↦ hpeel_row s₁
    have hc_prod : (∏ s₂ : I, (margin s₂).factorial) ≤
        (∏ s₂ : I, (tau₁ s₂).factorial) * ∏ s₁ : I, ∏ s₂ : I, alpha ^ (H s₁ s₂) := by
      rw [Finset.prod_comm (s := Finset.univ) (t := Finset.univ) (f := fun s₁ s₂ ↦ alpha ^ (H s₁ s₂)),
        ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod' fun s₂ _ ↦ hpeel_col s₂
    have hpow2 : (∏ s₁ : I, ∏ s₂ : I, alpha ^ (H s₁ s₂)) *
        (∏ s₁ : I, ∏ s₂ : I, alpha ^ (H s₁ s₂)) =
        ∏ s₁ : I, ∏ s₂ : I, alpha ^ (2 * H s₁ s₂) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun s₁ _ ↦ ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun s₂ _ ↦ ?_
      rw [← pow_add, ← two_mul]
    calc Fibre_H.card * (∏ s₁ : I, (margin s₁).factorial) * (∏ s₂ : I, (margin s₂).factorial)
        ≤ Fibre_H.card *
            ((∏ s₁ : I, (sigma₁ s₁).factorial) * ∏ s₁ : I, ∏ s₂ : I, alpha ^ (H s₁ s₂)) *
            ((∏ s₂ : I, (tau₁ s₂).factorial) * ∏ s₁ : I, ∏ s₂ : I, alpha ^ (H s₁ s₂)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hr_prod) hc_prod
      _ = (Fibre_H.card * (∏ s₁ : I, (sigma₁ s₁).factorial) * (∏ s₂ : I, (tau₁ s₂).factorial)) *
            ((∏ s₁ : I, ∏ s₂ : I, alpha ^ (H s₁ s₂)) *
              (∏ s₁ : I, ∏ s₂ : I, alpha ^ (H s₁ s₂))) := by ring
      _ ≤ ((zeroOneMatricesWithMargins sigma₁ tau₁).card *
              (∏ s₁ : I, (sigma₁ s₁).factorial) * (∏ s₂ : I, (tau₁ s₂).factorial)) *
            (∏ s₁ : I, ∏ s₂ : I, alpha ^ (2 * H s₁ s₂)) := by
          rw [hpow2]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hFibre_card))
      _ ≤ (n_tr - s₂_H).factorial * ∏ s₁ : I, ∏ s₂ : I, alpha ^ (2 * H s₁ s₂) :=
          Nat.mul_le_mul_right _ hstub
  -- Fiber `s₂_H` and cell products over `B_sizes`
  have h0_not_B : 0 ∉ B_sizes := fun h0 ↦ by have := (hB_bds 0 h0).1; omega
  let P_zero := (Finset.univ ×ˢ Finset.univ).filter fun p : I × I ↦ H p.1 p.2 = 0
  let P_pos := (Finset.univ ×ˢ Finset.univ).filter fun p : I × I ↦ H p.1 p.2 ≠ 0
  have hP_union : P_zero ∪ P_pos = Finset.univ ×ˢ Finset.univ :=
    Finset.filter_union_filter_not_eq _ _
  have hP_disj : Disjoint P_zero P_pos := Finset.disjoint_filter_filter_not _ _ _
  have hP_maps : ∀ p ∈ P_pos, H p.1 p.2 ∈ B_sizes := fun p hp ↦
    (hH_mem p.1 p.2).resolve_left (Finset.mem_filter.mp hp).2
  have hfib_eq_r : ∀ x ∈ B_sizes,
      (P_pos.filter fun p : I × I ↦ H p.1 p.2 = x) =
        (Finset.univ ×ˢ Finset.univ).filter fun p : I × I ↦ H p.1 p.2 = x := by
    intro x hx; ext p
    simp only [P_pos, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨by rw [h]; exact fun h0 ↦ h0_not_B (h0 ▸ hx), h⟩⟩
  have hs₂_eq : s₂_H = ∑ x ∈ B_sizes, x * r_H x := by
    dsimp [s₂_H]
    rw [← Finset.sum_product', ← hP_union, Finset.sum_union hP_disj]
    have hz : ∑ p ∈ P_zero, H p.1 p.2 = 0 :=
      Finset.sum_eq_zero fun p hp ↦ (Finset.mem_filter.mp hp).2
    rw [hz, zero_add, ← Finset.sum_fiberwise_of_maps_to hP_maps]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [hfib_eq_r x hx]
    calc ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : I × I ↦ H p.1 p.2 = x), H p.1 p.2
        = ∑ _p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : I × I ↦ H p.1 p.2 = x), x :=
          Finset.sum_congr rfl fun p hp ↦ (Finset.mem_filter.mp hp).2
      _ = x * r_H x := by simp [r_H, Finset.sum_const, smul_eq_mul, mul_comm]
  let cellWt : ℕ → ℝ := fun x ↦
    (alpha : ℝ) ^ (2 * x) * (2 : ℝ) ^ (x.choose 2) / (x.factorial : ℝ)
  have hcellWt_prod :
      (∏ s₁ : I, ∏ s₂ : I, cellWt (H s₁ s₂)) = ∏ x ∈ B_sizes, (cellWt x) ^ (r_H x) := by
    rw [← Finset.prod_product', ← hP_union, Finset.prod_union hP_disj]
    have hz : ∏ p ∈ P_zero, cellWt (H p.1 p.2) = 1 := by
      refine Finset.prod_eq_one fun p hp ↦ ?_
      rw [(Finset.mem_filter.mp hp).2]; simp [cellWt]
    rw [hz, one_mul, ← Finset.prod_fiberwise_of_maps_to hP_maps]
    refine Finset.prod_congr rfl fun x hx ↦ ?_
    rw [hfib_eq_r x hx]
    calc ∏ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : I × I ↦ H p.1 p.2 = x), cellWt (H p.1 p.2)
        = ∏ _p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : I × I ↦ H p.1 p.2 = x), cellWt x :=
          Finset.prod_congr rfl fun p hp ↦ congrArg cellWt (Finset.mem_filter.mp hp).2
      _ = (cellWt x) ^ (r_H x) := by simp [r_H, Finset.prod_const]
  have htr_ratio := (transmuted_factorial_ratio_le hn_tr hs₂_half B_sizes r_H hs₂_eq
    (fun x hx _ ↦ (hB_bds x hx).2.trans halpha_ntr)).2
  have htr_full := (transmuted_factorial_ratio_le hn_tr hs₂_half B_sizes r_H hs₂_eq
    (fun x hx _ ↦ (hB_bds x hx).2.trans halpha_ntr)).1.trans htr_ratio
  -- Combine `hcomb_nat`, `hcellWt_prod`, and `htr_full`
  have hsum_const :
      (∑ X ∈ Fibre_H,
        (((∏ s₁ : I, (margin s₁).factorial : ℝ) * (∏ s₂ : I, (margin s₂).factorial : ℝ)) /
          ((n_tr.factorial : ℝ) * (∏ s₁ : I, ∏ s₂ : I, (X s₁ s₂).factorial : ℝ))) *
          (2 : ℝ) ^ (∑ s₁ : I, ∑ s₂ : I, (X s₁ s₂).choose 2)) =
      ((Fibre_H.card : ℝ) * (∏ s₁ : I, (margin s₁).factorial : ℝ) * (∏ s₂ : I, (margin s₂).factorial : ℝ)) /
        ((n_tr.factorial : ℝ) * (∏ s₁ : I, ∏ s₂ : I, (H s₁ s₂).factorial : ℝ)) *
        (2 : ℝ) ^ (∑ s₁ : I, ∑ s₂ : I, (H s₁ s₂).choose 2) := by
    trans ∑ _X ∈ Fibre_H,
      (((∏ s₁ : I, (margin s₁).factorial : ℝ) * (∏ s₂ : I, (margin s₂).factorial : ℝ)) /
        ((n_tr.factorial : ℝ) * (∏ s₁ : I, ∏ s₂ : I, (H s₁ s₂).factorial : ℝ))) *
        (2 : ℝ) ^ (∑ s₁ : I, ∑ s₂ : I, (H s₁ s₂).choose 2)
    · refine Finset.sum_congr rfl fun X hX ↦ ?_
      have hfac_R : (∏ s₁ : I, ∏ s₂ : I, ((X s₁ s₂).factorial : ℝ)) =
          ∏ s₁ : I, ∏ s₂ : I, ((H s₁ s₂).factorial : ℝ) := by
        exact_mod_cast (hXH_invar X hX).1
      rw [hfac_R, (hXH_invar X hX).2]
    · simp [Finset.sum_const, nsmul_eq_mul]; ring
  have hcomb_R :
      (Fibre_H.card : ℝ) * (∏ s₁ : I, (margin s₁).factorial : ℝ) * (∏ s₂ : I, (margin s₂).factorial : ℝ) ≤
        ((n_tr - s₂_H).factorial : ℝ) * ∏ s₁ : I, ∏ s₂ : I, ((alpha : ℝ) ^ (2 * H s₁ s₂)) := by
    exact_mod_cast hcomb_nat
  have hH_prod_split :
      ((∏ s₁ : I, ∏ s₂ : I, (alpha : ℝ) ^ (2 * H s₁ s₂)) /
        (∏ s₁ : I, ∏ s₂ : I, (H s₁ s₂).factorial : ℝ)) *
        (2 : ℝ) ^ (∑ s₁ : I, ∑ s₂ : I, (H s₁ s₂).choose 2) =
      ∏ s₁ : I, ∏ s₂ : I, cellWt (H s₁ s₂) := by
    have h2_sum : (2 : ℝ) ^ (∑ s₁ : I, ∑ s₂ : I, (H s₁ s₂).choose 2) =
        ∏ s₁ : I, ∏ s₂ : I, (2 : ℝ) ^ ((H s₁ s₂).choose 2) := by
      have hp1 : ∀ (s : Finset I) (f : I → ℕ),
          (2 : ℝ) ^ (∑ j ∈ s, f j) = ∏ j ∈ s, (2 : ℝ) ^ (f j) := by
        intro s f; induction s using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih => rw [Finset.sum_insert ha, pow_add, Finset.prod_insert ha, ih]
      rw [hp1 Finset.univ (fun s₁ : I ↦ ∑ s₂ : I, (H s₁ s₂).choose 2)]
      exact Finset.prod_congr rfl fun s₁ _ ↦ hp1 Finset.univ (fun s₂ : I ↦ (H s₁ s₂).choose 2)
    rw [h2_sum, div_mul_eq_mul_div, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun s₁ _ ↦ ?_
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  rw [hsum_const]
  calc ((Fibre_H.card : ℝ) * (∏ s₁ : I, (margin s₁).factorial : ℝ) * (∏ s₂ : I, (margin s₂).factorial : ℝ)) /
          ((n_tr.factorial : ℝ) * (∏ s₁ : I, ∏ s₂ : I, (H s₁ s₂).factorial : ℝ)) *
          (2 : ℝ) ^ (∑ s₁ : I, ∑ s₂ : I, (H s₁ s₂).choose 2)
      ≤ (((n_tr - s₂_H).factorial : ℝ) * ∏ s₁ : I, ∏ s₂ : I, (alpha : ℝ) ^ (2 * H s₁ s₂)) /
          ((n_tr.factorial : ℝ) * (∏ s₁ : I, ∏ s₂ : I, (H s₁ s₂).factorial : ℝ)) *
          (2 : ℝ) ^ (∑ s₁ : I, ∑ s₂ : I, (H s₁ s₂).choose 2) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hcomb_R
            (mul_nonneg (Nat.cast_nonneg _)
              (Finset.prod_nonneg fun _ _ ↦ Finset.prod_nonneg fun _ _ ↦ Nat.cast_nonneg _)))
          (by positivity)
    _ = (((n_tr - s₂_H).factorial : ℝ) / (n_tr.factorial : ℝ)) *
          (((∏ s₁ : I, ∏ s₂ : I, (alpha : ℝ) ^ (2 * H s₁ s₂)) /
            (∏ s₁ : I, ∏ s₂ : I, (H s₁ s₂).factorial : ℝ)) *
            (2 : ℝ) ^ (∑ s₁ : I, ∑ s₂ : I, (H s₁ s₂).choose 2)) := by ring
    _ = (((n_tr - s₂_H).factorial : ℝ) / (n_tr.factorial : ℝ)) *
          ∏ x ∈ B_sizes, (cellWt x) ^ (r_H x) := by rw [hH_prod_split, hcellWt_prod]
    _ ≤ (∏ x ∈ B_sizes, (Real.exp (x : ℝ) / ((x.factorial : ℝ) * (n_tr.choose x : ℝ))) ^ (r_H x)) *
          (∏ x ∈ B_sizes, (cellWt x) ^ (r_H x)) :=
        mul_le_mul_of_nonneg_right htr_full
          (Finset.prod_nonneg fun x _ ↦ pow_nonneg (by dsimp [cellWt]; positivity) _)
    _ = ∏ x ∈ B_sizes,
          (Real.exp (x : ℝ) * ((alpha : ℝ) ^ x / (x.factorial : ℝ)) ^ 2 *
            (2 : ℝ) ^ (x.choose 2) / (n_tr.choose x : ℝ)) ^ (r_H x) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun x _ ↦ ?_
        rw [← mul_pow]; congr 1
        dsimp [cellWt]
        have hxf_ne : (x.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos x).ne'
        rw [pow_mul', sq]
        field_simp [hxf_ne]

private theorem validOverlapTable_sum_le_v13
    {I : Type*} [Fintype I] [DecidableEq I]
    {n_tr alpha X_max u_lo B s₂_max : ℕ}
    (hn_tr : 1 ≤ n_tr) (halpha_ntr : alpha ≤ n_tr)
    (h2_Xmax : 2 ≤ X_max) (hgap_sep : X_max < u_lo) (hulo_le : u_lo ≤ alpha)
    (hs₂_half : 2 * s₂_max ≤ n_tr)
    {margin : I → ℕ} (hmargin_sum : ∑ s : I, margin s = n_tr)
    (hmargin_le : ∀ s : I, margin s ≤ alpha)
    (ValidTables : Finset (I → I → ℕ))
    (hValid : ∀ X ∈ ValidTables,
      (∀ s₁ : I, ∑ s₂ : I, X s₁ s₂ = margin s₁) ∧
      (∀ s₂ : I, ∑ s₁ : I, X s₁ s₂ = margin s₂) ∧
      (∀ s₁ s₂ : I, X s₁ s₂ ≤ X_max ∨ (u_lo ≤ X s₁ s₂ ∧ X s₁ s₂ ≤ alpha)) ∧
      (((Finset.univ ×ˢ Finset.univ).filter fun p : I × I ↦ X_max < X p.1 p.2).card ≤ 2 * B) ∧
      (∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : I × I ↦ 2 ≤ X p.1 p.2),
          X p.1 p.2 ≤ s₂_max)) :
    let t : ℕ := Fintype.card I
    (∑ X ∈ ValidTables,
        (((∏ s₁ : I, (margin s₁).factorial : ℝ) *
            (∏ s₂ : I, (margin s₂).factorial : ℝ)) /
          ((n_tr.factorial : ℝ) *
            (∏ s₁ : I, ∏ s₂ : I, (X s₁ s₂).factorial : ℝ))) *
          (2 : ℝ) ^ (∑ s₁ : I, ∑ s₂ : I, (X s₁ s₂).choose 2)) ≤
      Real.exp
          (∑ x ∈ Finset.Icc 2 X_max,
            Real.exp (x : ℝ) * ((t : ℝ) * (alpha : ℝ) ^ x / (x.factorial : ℝ)) ^ 2 /
              ((n_tr.choose x : ℝ) * (2 : ℝ) ^ (-(x.choose 2 : ℝ)))) *
        (((2 * B + 1 : ℕ) : ℝ) ^ (Finset.Icc u_lo alpha).card *
          (max 1 ((t : ℝ) ^ 2 * (alpha : ℝ) ^ (2 * alpha) *
            Real.exp (alpha : ℝ) * (2 : ℝ) ^ (alpha.choose 2 : ℝ))) ^ (2 * B)) := by
  intro t
  set S_small := Finset.Icc 2 X_max
  set S_large := Finset.Icc u_lo alpha
  have hdisj_SL : Disjoint S_small S_large := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    have := (Finset.mem_Icc.mp h1).2; have := (Finset.mem_Icc.mp h2).1; omega
  set B_sizes := S_small ∪ S_large
  have hB_bds : ∀ x ∈ B_sizes, 2 ≤ x ∧ x ≤ alpha := by
    intro x hx
    rcases Finset.mem_union.mp hx with hs | hl
    · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hs; exact ⟨h1, h2.trans (by omega)⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hl; exact ⟨by omega, h2⟩
  let H_of : (I → I → ℕ) → (I → I → ℕ) := fun X s₁ s₂ ↦
    if 2 ≤ X s₁ s₂ then X s₁ s₂ else 0
  let HeavyFam : Finset (I → I → ℕ) := ValidTables.image H_of
  let r_of : (I → I → ℕ) → ℕ → ℕ := fun H x ↦
    ((Finset.univ ×ˢ Finset.univ).filter fun p : I × I ↦ H p.1 p.2 = x).card
  let baseWt : ℕ → ℝ := fun x ↦
    Real.exp (x : ℝ) * ((alpha : ℝ) ^ x / (x.factorial : ℝ)) ^ 2 *
      (2 : ℝ) ^ (x.choose 2) / (n_tr.choose x : ℝ)
  have hbase_nn : ∀ x : ℕ, 0 ≤ baseWt x := fun x ↦ by dsimp [baseWt]; positivity
  -- Step 1: Fiber `ValidTables` over `H ∈ HeavyFam` and apply `peeled_heavyMatrix_fibre_le_v13`
  have hH_props : ∀ H ∈ HeavyFam,
      (∀ s₁ s₂ : I, H s₁ s₂ = 0 ∨ H s₁ s₂ ∈ B_sizes) ∧
      ((∑ x ∈ S_large, r_of H x) ≤ 2 * B) ∧
      (∑ X ∈ ValidTables.filter (fun X ↦ H_of X = H),
        (((∏ s₁ : I, (margin s₁).factorial : ℝ) * (∏ s₂ : I, (margin s₂).factorial : ℝ)) /
          ((n_tr.factorial : ℝ) * (∏ s₁ : I, ∏ s₂ : I, (X s₁ s₂).factorial : ℝ))) *
          (2 : ℝ) ^ (∑ s₁ : I, ∑ s₂ : I, (X s₁ s₂).choose 2)) ≤
        ∏ x ∈ B_sizes, (baseWt x) ^ (r_of H x) := by
    intro H hH
    rcases Finset.mem_image.mp hH with ⟨X₀, hX₀, rfl⟩
    have hv₀ := hValid X₀ hX₀
    have hmem_B : ∀ s₁ s₂ : I, H_of X₀ s₁ s₂ = 0 ∨ H_of X₀ s₁ s₂ ∈ B_sizes := by
      intro s₁ s₂; dsimp [H_of]
      by_cases h2 : 2 ≤ X₀ s₁ s₂
      · rw [if_pos h2]; refine Or.inr (Finset.mem_union.mpr ?_)
        rcases hv₀.2.2.1 s₁ s₂ with hsm | hlg
        · exact Or.inl (Finset.mem_Icc.mpr ⟨h2, hsm⟩)
        · exact Or.inr (Finset.mem_Icc.mpr hlg)
      · rw [if_neg h2]; exact Or.inl rfl
    have hrow_H : ∀ s₁ : I, ∑ s₂ : I, H_of X₀ s₁ s₂ ≤ margin s₁ := fun s₁ ↦ by
      rw [← hv₀.1 s₁]
      exact Finset.sum_le_sum fun s₂ _ ↦ by dsimp [H_of]; split_ifs <;> omega
    have hcol_H : ∀ s₂ : I, ∑ s₁ : I, H_of X₀ s₁ s₂ ≤ margin s₂ := fun s₂ ↦ by
      rw [← hv₀.2.1 s₂]
      exact Finset.sum_le_sum fun s₁ _ ↦ by dsimp [H_of]; split_ifs <;> omega
    have hs₂_H_le : ∑ s₁ : I, ∑ s₂ : I, H_of X₀ s₁ s₂ ≤ s₂_max := by
      rw [← Finset.sum_product']
      have hsub : (∑ p ∈ Finset.univ ×ˢ Finset.univ, H_of X₀ p.1 p.2) =
          ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : I × I ↦ 2 ≤ X₀ p.1 p.2), X₀ p.1 p.2 := by
        rw [Finset.sum_filter]
      exact hsub.trans_le hv₀.2.2.2.2
    have hlg_sum : ∑ x ∈ S_large, r_of (H_of X₀) x ≤ 2 * B := by
      have hbi : S_large.biUnion (fun x ↦ (Finset.univ ×ˢ Finset.univ).filter
          fun p : I × I ↦ H_of X₀ p.1 p.2 = x) ⊆
          (Finset.univ ×ˢ Finset.univ).filter (fun p : I × I ↦ X_max < X₀ p.1 p.2) := by
        intro p hp
        rcases Finset.mem_biUnion.mp hp with ⟨x, hxL, hpf⟩
        have heq := (Finset.mem_filter.mp hpf).2
        have hx_lo := (Finset.mem_Icc.mp hxL).1
        dsimp [H_of] at heq
        split_ifs at heq with h2
        · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
            by omega⟩
        · omega
      have hdisj_f : (S_large : Set ℕ).PairwiseDisjoint
          (fun x ↦ (Finset.univ ×ˢ Finset.univ).filter fun p : I × I ↦ H_of X₀ p.1 p.2 = x) := by
        intro x _ y _ hne; rw [Function.onFun, Finset.disjoint_left]
        intro p h1 h2; exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      rw [← Finset.card_biUnion hdisj_f]
      exact (Finset.card_le_card hbi).trans hv₀.2.2.2.1
    refine ⟨hmem_B, hlg_sum, peeled_heavyMatrix_fibre_le_v13 hn_tr halpha_ntr hmargin_sum hmargin_le
      hB_bds hmem_B hrow_H hcol_H (by omega) _ fun X hXf ↦ ?_⟩
    obtain ⟨hXV, hXH⟩ := Finset.mem_filter.mp hXf
    exact ⟨fun s₁ s₂ ↦ congrFun (congrFun hXH s₁) s₂, (hValid X hXV).1, (hValid X hXV).2.1⟩
  have hstep1 :
      (∑ X ∈ ValidTables,
        (((∏ s₁ : I, (margin s₁).factorial : ℝ) * (∏ s₂ : I, (margin s₂).factorial : ℝ)) /
          ((n_tr.factorial : ℝ) * (∏ s₁ : I, ∏ s₂ : I, (X s₁ s₂).factorial : ℝ))) *
          (2 : ℝ) ^ (∑ s₁ : I, ∑ s₂ : I, (X s₁ s₂).choose 2)) ≤
      ∑ H ∈ HeavyFam, ∏ x ∈ B_sizes, (baseWt x) ^ (r_of H x) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := H_of)
      (fun X hX ↦ Finset.mem_image_of_mem H_of hX)]
    exact Finset.sum_le_sum fun H hH ↦ (hH_props H hH).2.2
  -- Step 2: Fiber `HeavyFam` by `(r_s : ↥S_small → ℕ, r_l : ↥S_large → ℕ)`
  let multPair : (I → I → ℕ) → (↥S_small → ℕ) × (↥S_large → ℕ) := fun H ↦
    (fun x ↦ r_of H x.1, fun x ↦ r_of H x.1)
  let SmallMulti : Finset (↥S_small → ℕ) := HeavyFam.image (fun H x ↦ r_of H x.1)
  let LargeMulti : Finset (↥S_large → ℕ) :=
    (Fintype.piFinset fun _ : ↥S_large ↦ Finset.range (2 * B + 1)).filter
      fun rl ↦ ∑ x : ↥S_large, rl x ≤ 2 * B
  have hmaps_mult : ∀ H ∈ HeavyFam, multPair H ∈ SmallMulti ×ˢ LargeMulti := by
    intro H hH
    refine Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hH, ?_⟩
    have hsum_le : ∑ x : ↥S_large, r_of H x.1 ≤ 2 * B := by
      rw [Finset.sum_coe_sort S_large (fun x ↦ r_of H x)]
      exact (hH_props H hH).2.1
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun x ↦ Finset.mem_range.mpr ?_, hsum_le⟩
    have hle : r_of H x.1 ≤ ∑ y : ↥S_large, r_of H y.1 :=
      Finset.single_le_sum (f := fun y : ↥S_large ↦ r_of H y.1)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ x)
    exact Nat.lt_succ_of_le (hle.trans hsum_le)
  have hcard_mult_fib : ∀ rs ∈ SmallMulti, ∀ rl ∈ LargeMulti,
      ((HeavyFam.filter fun H ↦ multPair H = (rs, rl)).card : ℝ) ≤
        (∏ x : ↥S_small, (((t : ℝ) ^ 2) ^ (rs x)) / ((rs x).factorial : ℝ)) *
          (∏ x : ↥S_large, ((t : ℝ) ^ 2) ^ (rl x)) := by
    intro rs _ rl _
    let Cells := (Finset.univ : Finset I) ×ˢ (Finset.univ : Finset I)
    have hCells_card : Cells.card = t ^ 2 := by
      rw [Finset.card_product, Finset.card_univ, sq]
    let toSubsets : ↥(HeavyFam.filter fun H ↦ multPair H = (rs, rl)) →
        (∀ x : ↥S_small, ↥(Cells.powersetCard (rs x))) ×
        (∀ x : ↥S_large, ↥(Cells.powersetCard (rl x))) := fun H ↦
      have hm := (Finset.mem_filter.mp H.2).2
      have hrs : (fun x : ↥S_small ↦ r_of H.1 x.1) = rs := congrArg Prod.fst hm
      have hrl : (fun x : ↥S_large ↦ r_of H.1 x.1) = rl := congrArg Prod.snd hm
      (fun x ↦ ⟨Cells.filter (fun p ↦ H.1 p.1 p.2 = x.1),
          Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, congrFun hrs x⟩⟩,
        fun x ↦ ⟨Cells.filter (fun p ↦ H.1 p.1 p.2 = x.1),
          Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, congrFun hrl x⟩⟩)
    have htoSub_inj : Function.Injective toSubsets := by
      intro H₁ H₂ heq
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      apply Subtype.ext; funext s₁ s₂
      have hm₁ := (hH_props H₁.1 (Finset.mem_filter.mp H₁.2).1).1 s₁ s₂
      have hm₂ := (hH_props H₂.1 (Finset.mem_filter.mp H₂.2).1).1 s₁ s₂
      have hcell_iff : ∀ x ∈ B_sizes, H₁.1 s₁ s₂ = x ↔ H₂.1 s₁ s₂ = x := by
        intro x hx
        have hmem_c : (s₁, s₂) ∈ Cells := Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
        rcases Finset.mem_union.mp hx with hs | hl
        · have hx_eq := congrArg Subtype.val (congrFun h1 ⟨x, hs⟩)
          dsimp only [toSubsets] at hx_eq
          have hm := Finset.ext_iff.mp hx_eq (s₁, s₂)
          simpa only [Finset.mem_filter, hmem_c, true_and] using hm
        · have hx_eq := congrArg Subtype.val (congrFun h2 ⟨x, hl⟩)
          dsimp only [toSubsets] at hx_eq
          have hm := Finset.ext_iff.mp hx_eq (s₁, s₂)
          simpa only [Finset.mem_filter, hmem_c, true_and] using hm
      rcases hm₁ with hz₁ | hb₁
      · rcases hm₂ with hz₂ | hb₂
        · exact hz₁.trans hz₂.symm
        · exfalso
          have h := (hcell_iff _ hb₂).mpr rfl
          have := (hB_bds _ hb₂).1; omega
      · exact ((hcell_iff _ hb₁).mp rfl).symm
    have hcard_nat :
        (HeavyFam.filter fun H ↦ multPair H = (rs, rl)).card ≤
          (∏ x : ↥S_small, (t ^ 2).choose (rs x)) * (∏ x : ↥S_large, (t ^ 2).choose (rl x)) := by
      rw [← Fintype.card_coe]
      refine (Fintype.card_le_of_injective toSubsets htoSub_inj).trans ?_
      rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_pi]
      refine le_of_eq ?_
      congr 1 <;> refine Finset.prod_congr rfl fun x _ ↦ ?_ <;>
        rw [Fintype.card_coe, Finset.card_powersetCard, hCells_card]
    have hcard_R :
        ((HeavyFam.filter fun H ↦ multPair H = (rs, rl)).card : ℝ) ≤
          (∏ x : ↥S_small, ((t ^ 2).choose (rs x) : ℝ)) *
            (∏ x : ↥S_large, ((t ^ 2).choose (rl x) : ℝ)) := by
      exact_mod_cast hcard_nat
    refine hcard_R.trans (mul_le_mul ?_ ?_ (by positivity) (by positivity))
    · refine Finset.prod_le_prod (fun _ _ ↦ Nat.cast_nonneg _) fun x _ ↦ ?_
      rw [le_div_iff₀ (by exact_mod_cast Nat.factorial_pos (rs x)), mul_comm]
      have h := nat_factorial_mul_choose_le_pow_v13 (t ^ 2) (rs x)
      exact_mod_cast h
    · refine Finset.prod_le_prod (fun _ _ ↦ Nat.cast_nonneg _) fun x _ ↦ ?_
      have h2 := (Nat.le_mul_of_pos_left ((t ^ 2).choose (rl x)) (Nat.factorial_pos (rl x))).trans
        (nat_factorial_mul_choose_le_pow_v13 (t ^ 2) (rl x))
      exact_mod_cast h2
  -- Combine Step 1 and Step 2
  let T_small : ↥S_small → ℝ := fun x ↦ (t : ℝ) ^ 2 * baseWt x.1
  have hT_small_nn : ∀ x : ↥S_small, 0 ≤ T_small x := fun x ↦ mul_nonneg (sq_nonneg _) (hbase_nn x.1)
  have hstep2 :
      (∑ H ∈ HeavyFam, ∏ x ∈ B_sizes, (baseWt x) ^ (r_of H x)) ≤
        (∑ rs ∈ SmallMulti, ∏ x : ↥S_small, (T_small x) ^ (rs x) / ((rs x).factorial : ℝ)) *
          (∑ rl ∈ LargeMulti, ∏ x : ↥S_large, ((t : ℝ) ^ 2 * baseWt x.1) ^ (rl x)) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps_mult, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_le_sum fun p hp ↦ ?_
    obtain ⟨hrs, hrl⟩ := Finset.mem_product.mp hp
    have hconst : ∀ H ∈ HeavyFam.filter (fun H ↦ multPair H = p),
        (∏ x ∈ B_sizes, (baseWt x) ^ (r_of H x)) =
          (∏ x : ↥S_small, (baseWt x.1) ^ (p.1 x)) * (∏ x : ↥S_large, (baseWt x.1) ^ (p.2 x)) := by
      intro H hHf
      have hm := (Finset.mem_filter.mp hHf).2
      have hrs_eq : (fun x : ↥S_small ↦ r_of H x.1) = p.1 := congrArg Prod.fst hm
      have hrl_eq : (fun x : ↥S_large ↦ r_of H x.1) = p.2 := congrArg Prod.snd hm
      rw [Finset.prod_union hdisj_SL,
        ← Finset.prod_coe_sort S_small (fun x ↦ (baseWt x) ^ (r_of H x)),
        ← Finset.prod_coe_sort S_large (fun x ↦ (baseWt x) ^ (r_of H x))]
      congr 1
      · exact Finset.prod_congr rfl fun x _ ↦ by rw [congrFun hrs_eq x]
      · exact Finset.prod_congr rfl fun x _ ↦ by rw [congrFun hrl_eq x]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hb_nn : 0 ≤ (∏ x : ↥S_small, (baseWt x.1) ^ (p.1 x)) *
        (∏ x : ↥S_large, (baseWt x.1) ^ (p.2 x)) :=
      mul_nonneg (Finset.prod_nonneg fun (x : ↥S_small) _ ↦ pow_nonneg (hbase_nn x.1) (p.1 x))
        (Finset.prod_nonneg fun (x : ↥S_large) _ ↦ pow_nonneg (hbase_nn x.1) (p.2 x))
    have hcm := mul_le_mul_of_nonneg_right (hcard_mult_fib p.1 hrs p.2 hrl) hb_nn
    refine hcm.trans_eq ?_
    have heq_s :
        (∏ x : ↥S_small, (((t : ℝ) ^ 2) ^ (p.1 x)) / ((p.1 x).factorial : ℝ)) *
          (∏ x : ↥S_small, (baseWt x.1) ^ (p.1 x)) =
        ∏ x : ↥S_small, (T_small x) ^ (p.1 x) / ((p.1 x).factorial : ℝ) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun x _ ↦ ?_
      dsimp [T_small]; rw [mul_pow, div_mul_eq_mul_div]
    have heq_l :
        (∏ x : ↥S_large, ((t : ℝ) ^ 2) ^ (p.2 x)) *
          (∏ x : ↥S_large, (baseWt x.1) ^ (p.2 x)) =
        ∏ x : ↥S_large, ((t : ℝ) ^ 2 * baseWt x.1) ^ (p.2 x) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun x _ ↦ (mul_pow _ _ _).symm
    calc ((∏ x : ↥S_small, (((t : ℝ) ^ 2) ^ (p.1 x)) / ((p.1 x).factorial : ℝ)) *
            (∏ x : ↥S_large, ((t : ℝ) ^ 2) ^ (p.2 x))) *
          ((∏ x : ↥S_small, (baseWt x.1) ^ (p.1 x)) *
            (∏ x : ↥S_large, (baseWt x.1) ^ (p.2 x)))
        = ((∏ x : ↥S_small, (((t : ℝ) ^ 2) ^ (p.1 x)) / ((p.1 x).factorial : ℝ)) *
            (∏ x : ↥S_small, (baseWt x.1) ^ (p.1 x))) *
          ((∏ x : ↥S_large, ((t : ℝ) ^ 2) ^ (p.2 x)) *
            (∏ x : ↥S_large, (baseWt x.1) ^ (p.2 x))) := by ring
      _ = _ := by rw [heq_s, heq_l]
  -- Step 3: Bound the small Poisson sum and the large finite sum
  have hsmall_bound :
      (∑ rs ∈ SmallMulti, ∏ x : ↥S_small, (T_small x) ^ (rs x) / ((rs x).factorial : ℝ)) ≤
        Real.exp
          (∑ x ∈ S_small,
            Real.exp (x : ℝ) * ((t : ℝ) * (alpha : ℝ) ^ x / (x.factorial : ℝ)) ^ 2 /
              ((n_tr.choose x : ℝ) * (2 : ℝ) ^ (-(x.choose 2 : ℝ)))) := by
    refine ((finset_sum_prod_pow_div_factorial_le_exp_and_tsum_eq T_small hT_small_nn).1 SmallMulti).trans_eq ?_
    congr 1
    rw [Finset.sum_coe_sort S_small (fun x ↦ (t : ℝ) ^ 2 * baseWt x)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    dsimp [baseWt]
    rw [Real.rpow_neg two_pos.le, Real.rpow_natCast]
    have h2ne : (2 : ℝ) ^ (x.choose 2) ≠ 0 := by positivity
    field_simp [h2ne]
  set M_wt : ℝ := max 1 ((t : ℝ) ^ 2 * (alpha : ℝ) ^ (2 * alpha) *
    Real.exp (alpha : ℝ) * (2 : ℝ) ^ (alpha.choose 2 : ℝ))
  have hlarge_bound :
      (∑ rl ∈ LargeMulti, ∏ x : ↥S_large, ((t : ℝ) ^ 2 * baseWt x.1) ^ (rl x)) ≤
        ((2 * B + 1 : ℕ) : ℝ) ^ S_large.card * M_wt ^ (2 * B) := by
    have hterm_le : ∀ x : ↥S_large, (t : ℝ) ^ 2 * baseWt x.1 ≤ M_wt := by
      intro x
      refine le_trans ?_ (le_max_right _ _)
      have hx_le_a : x.1 ≤ alpha := (Finset.mem_Icc.mp x.2).2
      have hx_ntr : x.1 ≤ n_tr := hx_le_a.trans halpha_ntr
      have h1_ch : (1 : ℝ) ≤ (n_tr.choose x.1 : ℝ) := by exact_mod_cast Nat.choose_pos hx_ntr
      have h1_fac : (1 : ℝ) ≤ (x.1.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos x.1
      dsimp [baseWt]
      by_cases ha0 : alpha = 0
      · have hx0 : x.1 = 0 := by omega
        have := (Finset.mem_Icc.mp x.2).1; omega
      · have ha1 : (1 : ℝ) ≤ (alpha : ℝ) := by exact_mod_cast (show 1 ≤ alpha by omega)
        have hpow_a : ((alpha : ℝ) ^ x.1 / (x.1.factorial : ℝ)) ^ 2 ≤ (alpha : ℝ) ^ (2 * alpha) := by
          have hd : (alpha : ℝ) ^ x.1 / (x.1.factorial : ℝ) ≤ (alpha : ℝ) ^ alpha := by
            calc (alpha : ℝ) ^ x.1 / (x.1.factorial : ℝ)
                ≤ (alpha : ℝ) ^ x.1 / 1 := div_le_div_of_nonneg_left (by positivity) one_pos h1_fac
              _ = (alpha : ℝ) ^ x.1 := div_one _
              _ ≤ (alpha : ℝ) ^ alpha := pow_le_pow_right₀ ha1 hx_le_a
          exact (pow_le_pow_left₀ (by positivity) hd 2).trans_eq
            (by rw [← pow_mul, mul_comm alpha 2])
        have hexp_x : Real.exp (x.1 : ℝ) ≤ Real.exp (alpha : ℝ) :=
          Real.exp_le_exp.mpr (by exact_mod_cast hx_le_a)
        have h2_ch : (2 : ℝ) ^ (x.1.choose 2) ≤ (2 : ℝ) ^ (alpha.choose 2 : ℝ) := by
          rw [Real.rpow_natCast]
          exact pow_le_pow_right₀ one_le_two (Nat.choose_le_choose 2 hx_le_a)
        calc (t : ℝ) ^ 2 * (Real.exp (x.1 : ℝ) * ((alpha : ℝ) ^ x.1 / (x.1.factorial : ℝ)) ^ 2 *
                (2 : ℝ) ^ (x.1.choose 2) / (n_tr.choose x.1 : ℝ))
            ≤ (t : ℝ) ^ 2 * ((Real.exp (x.1 : ℝ) * ((alpha : ℝ) ^ x.1 / (x.1.factorial : ℝ)) ^ 2 *
                (2 : ℝ) ^ (x.1.choose 2)) / 1) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) one_pos h1_ch) (sq_nonneg _)
          _ = (t : ℝ) ^ 2 * (((alpha : ℝ) ^ x.1 / (x.1.factorial : ℝ)) ^ 2 *
                Real.exp (x.1 : ℝ) * (2 : ℝ) ^ (x.1.choose 2)) := by ring
          _ ≤ (t : ℝ) ^ 2 * ((alpha : ℝ) ^ (2 * alpha) * Real.exp (alpha : ℝ) *
                (2 : ℝ) ^ (alpha.choose 2 : ℝ)) := by
              refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
              exact mul_le_mul (mul_le_mul hpow_a hexp_x (by positivity) (by positivity))
                h2_ch (by positivity) (by positivity)
          _ = _ := by ring
    have hprod_rl : ∀ rl ∈ LargeMulti,
        (∏ x : ↥S_large, ((t : ℝ) ^ 2 * baseWt x.1) ^ (rl x)) ≤ M_wt ^ (2 * B) := by
      intro rl hrl
      have hsum_rl : ∑ x : ↥S_large, rl x ≤ 2 * B := (Finset.mem_filter.mp hrl).2
      have h1_M : 1 ≤ M_wt := le_max_left _ _
      have hp_pow : ∀ (s : Finset ↥S_large), (∏ x ∈ s, M_wt ^ (rl x)) = M_wt ^ (∑ x ∈ s, rl x) := by
        intro s; induction s using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih => rw [Finset.prod_insert ha, ih, Finset.sum_insert ha, pow_add]
      calc ∏ x : ↥S_large, ((t : ℝ) ^ 2 * baseWt x.1) ^ (rl x)
          ≤ ∏ x : ↥S_large, M_wt ^ (rl x) :=
            Finset.prod_le_prod (fun x _ ↦ pow_nonneg (mul_nonneg (sq_nonneg _) (hbase_nn x.1)) _)
              (fun x _ ↦ pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) (hbase_nn x.1)) (hterm_le x) _)
        _ = M_wt ^ (∑ x : ↥S_large, rl x) := hp_pow Finset.univ
        _ ≤ M_wt ^ (2 * B) := pow_le_pow_right₀ h1_M hsum_rl
    have hcard_LM : LargeMulti.card ≤ (2 * B + 1) ^ S_large.card := by
      refine (Finset.card_le_card (Finset.filter_subset _ _)).trans ?_
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
        Finset.card_range]
    calc ∑ rl ∈ LargeMulti, ∏ x : ↥S_large, ((t : ℝ) ^ 2 * baseWt x.1) ^ (rl x)
        ≤ ∑ _rl ∈ LargeMulti, M_wt ^ (2 * B) := Finset.sum_le_sum hprod_rl
      _ = (LargeMulti.card : ℝ) * M_wt ^ (2 * B) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((2 * B + 1 : ℕ) : ℝ) ^ S_large.card * M_wt ^ (2 * B) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_LM)
            (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  exact hstep1.trans (hstep2.trans (mul_le_mul hsmall_bound hlarge_bound
    (Finset.sum_nonneg fun _ _ ↦ Finset.prod_nonneg fun (x : ↥S_large) _ ↦
      pow_nonneg (mul_nonneg (sq_nonneg _) (hbase_nn x.1)) _)
    (Real.exp_pos _).le))

private theorem lemma72_fixed_n_of_relPair_v13
    {n M m : ℕ} {c₀ C_ov : ℝ}
    (hn4 : 4 ≤ n) (hM : 1 ≤ M) (hm : m ≤ 1)
    (h1mc₀_pos : 0 < 1 - c₀)
    (hL2 : (2 : ℝ) ≤ Real.log (n : ℝ))
    (hPh : logOrder n ≤ (phaseNat n : ℝ) ∧ (phaseNat n : ℝ) ≤ 4 * logOrder n)
    (halpha_n : 20 * M + 30 ≤ phaseNat n)
    (hb4_n : ‖(Real.log (n : ℝ)) ^ ((4 : ℕ) : ℝ)‖ ≤ (1 / 32 : ℝ) * ‖(n : ℝ) ^ (1 - c₀)‖)
    (hKern : ∀ (n_tr t : ℕ),
      (n : ℝ) ^ (1 - c₀) ≤ (n_tr : ℝ) → n_tr ≤ n → t * (phaseNat n - (M + 1)) ≤ n_tr →
      Real.exp
          (∑ x ∈ Finset.Icc 2 (2 * M + 4),
            Real.exp (x : ℝ) * ((t : ℝ) * (phaseNat n : ℝ) ^ x / (x.factorial : ℝ)) ^ 2 /
              ((n_tr.choose x : ℝ) * (2 : ℝ) ^ (-(x.choose 2 : ℝ)))) *
        ((2 * (Real.log (n : ℝ)) ^ 3 + 1) ^ ((M + 1) ^ 3) *
          (max 1 ((t : ℝ) ^ 2 * (phaseNat n : ℝ) ^ (2 * phaseNat n) *
            Real.exp (phaseNat n : ℝ) * (2 : ℝ) ^ ((phaseNat n).choose 2 : ℝ))) ^
            (2 * Nat.floor ((Real.log (n : ℝ)) ^ 3))) ≤
      Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5))
    {RelPair : VertexPartition n → VertexPartition n → Prop}
    (hRel_spec : ∀ Q Q' : VertexPartition n, RelPair Q Q' →
      ((∀ D ∈ Q.parts,
          (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card ≤ 2 ∨
            D.card ≤ (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card + 2 * (phaseNat n - D.card) + 1) ∧
        (∀ D' ∈ Q'.parts,
          (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card ≤ 2 ∨
            D'.card ≤ (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card + 2 * (phaseNat n - D'.card) + 1)) ∧
      ((∀ D ∈ Q.parts, (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 →
          ∃ D' ∈ Q'.parts, (D ∩ D').card = D.card - 1) ∧
        (∀ D' ∈ Q'.parts, (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 →
          ∃ D ∈ Q.parts, (D' ∩ D).card = D'.card - 1)) ∧
      ((Q.parts.filter fun D ↦
          (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 ∧
            ∃ D' ∈ Q'.parts, D'.card - 1 ≤ (D ∩ D').card).card ≤ Nat.floor ((Real.log (n : ℝ)) ^ 3) ∧
        (Q'.parts.filter fun D' ↦
          (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 ∧
            ∃ D ∈ Q.parts, D.card - 1 ≤ (D' ∩ D).card).card ≤ Nat.floor ((Real.log (n : ℝ)) ^ 3)))
    (kv : Fin M → ℕ) (kp : ColoringProfile (phaseNat n)) (nu : Fin M → ℕ)
    (hMass : selectedVertexMass (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) kv = n)
    (hkp : ∀ idx : Fin (phaseNat n),
      kp idx = ∑ j : Fin M, if phaseNat n - (m + 1 + j.1) = idx.1 + 1 then kv j else 0)
    (hnu : IsPartialSubprofile kv nu)
    (hntr_ge : (n : ℝ) ^ (1 - c₀) ≤
      ((n - selectedVertexMass (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) nu : ℕ) : ℝ))
    (S_idx : Finset ℕ) (P : ℕ → VertexPartition n)
    (hP_inj : Set.InjOn P (S_idx : Set ℕ))
    (hP_sh : ∀ i ∈ S_idx, partitionShape (P i) = ColoringProfile.sizes kp) :
    (∑ pq ∈ (S_idx ×ˢ S_idx).filter (fun pq ↦
          RelPair (P pq.1) (P pq.2) ∧
          (∀ j : Fin M,
            (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = phaseNat n - (m + 1 + j.1)).card = nu j)),
        (randomGraphMeasure n).real
          (partitionColoringEvent (P pq.1) ∩ partitionColoringEvent (P pq.2))) ≤
      Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
        (completeUnmarkedFirstMoment (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) kv) ^ 2 *
        unmarkedDiagonalWeight n (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) kv nu ∧
    (∑ pq ∈ (S_idx ×ˢ S_idx).filter (fun pq ↦
          RelPair (P pq.1) (P pq.2) ∧
          (∀ j : Fin M,
            (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = phaseNat n - (m + 1 + j.1)).card = nu j)),
        (randomGraphMeasure n).real
          (partitionCocoloringEvent (P pq.1) ∩ partitionCocoloringEvent (P pq.2))) ≤
      Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
        (completeSignedFirstMoment (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) kv) ^ 2 *
        partialDiagonalWeight n (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) kv nu := by
  let u : Fin M → ℕ := fun j ↦ phaseNat n - (m + 1 + j.1)
  set PairNu : Finset (ℕ × ℕ) :=
    (S_idx ×ˢ S_idx).filter fun pq ↦
      RelPair (P pq.1) (P pq.2) ∧
      (∀ j : Fin M, (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = u j).card = nu j)
  let α : ℕ := phaseNat n
  have halpha_m : m + M + 2 ≤ phaseNat n := by omega
  set B : ℕ := Nat.floor ((Real.log (n : ℝ)) ^ 3)
  set n_tr : ℕ := n - selectedVertexMass u nu
  set r_vec : Fin M → ℕ := fun j ↦ kv j - nu j
  have hPh2 : (α : ℝ) ≤ 4 * Real.log (n : ℝ) := hPh.2
  have hL_pos : 0 < Real.log (n : ℝ) := by linarith only [hL2]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hntr_ge1 : 1 ≤ n_tr := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 - c₀) :=
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) h1mc₀_pos.le
    exact_mod_cast (h1.trans hntr_ge)
  have h32L4_le_ntr : 32 * (Real.log (n : ℝ)) ^ 4 ≤ (n_tr : ℝ) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hL_pos _),
      abs_of_pos (Real.rpow_pos_of_pos hn_pos _), Real.rpow_natCast] at hb4_n
    have hm32 := mul_le_mul_of_nonneg_left hb4_n (by norm_num : (0 : ℝ) ≤ 32)
    have hc : (32 : ℝ) * (1 / 32 * (n : ℝ) ^ (1 - c₀)) = (n : ℝ) ^ (1 - c₀) := by ring
    rw [hc] at hm32
    exact hm32.trans hntr_ge
  have halpha_le_ntr : α ≤ n_tr := by
    have ha_le : (α : ℝ) ≤ 32 * (Real.log (n : ℝ)) ^ 4 := by
      have h1 : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := one_le_pow₀ (by linarith only [hL2])
      have h2 : 4 * Real.log (n : ℝ) ≤ 32 * (Real.log (n : ℝ)) ^ 4 := by
        calc 4 * Real.log (n : ℝ) ≤ 32 * Real.log (n : ℝ) * 1 := by linarith only [hL_pos]
          _ ≤ 32 * Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ 3 :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = 32 * (Real.log (n : ℝ)) ^ 4 := by ring
      exact hPh2.trans h2
    exact_mod_cast (ha_le.trans h32L4_le_ntr)
  have hm_nu_le : selectedVertexMass u nu ≤ n := by
    rw [← hMass]; exact Finset.sum_le_sum fun j _ ↦ Nat.mul_le_mul_left _ (hnu j)
  have hmass_r : selectedVertexMass u r_vec = n_tr := by
    have hadd : selectedVertexMass u nu + selectedVertexMass u r_vec = selectedVertexMass u kv := by
      unfold selectedVertexMass
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← Nat.mul_add, Nat.add_sub_of_le (hnu j)]
    rw [hMass] at hadd
    dsimp [n_tr]; omega
  obtain ⟨hu_inj, hu_bds, _, _, _, hP_all⟩ :=
    windowProfile_part_sizes_and_counts_v13 halpha_m hMass hkp
  set u_minus : ℕ := α - (m + M)
  set a_max : ℕ := α - (m + 1)
  set u_lo : ℕ := u_minus - 1
  set X_max : ℕ := 2 * M + 4
  set t : ℕ := selectedBlockCount r_vec
  set s₂_max : ℕ := (4 * M + 6) * t + 2 * a_max * B
  have ht_mul_uminus : t * u_minus ≤ n_tr := by
    dsimp [t]; rw [← hmass_r]; unfold selectedBlockCount selectedVertexMass
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ ↦ by rw [mul_comm]; exact Nat.mul_le_mul_right _ (hu_bds j).2.1
  have ht_mul_M1 : t * (α - (M + 1)) ≤ n_tr :=
    (Nat.mul_le_mul_left t (by dsimp [u_minus]; omega)).trans ht_mul_uminus
  have hs₂_half : 2 * s₂_max ≤ n_tr := by
    have h1 : 2 * ((4 * M + 6) * t) ≤ n_tr / 2 := by
      have h4u : 4 * (4 * M + 6) ≤ u_minus := by dsimp [u_minus, α]; omega
      have hmul : 4 * ((4 * M + 6) * t) ≤ n_tr := by
        calc 4 * ((4 * M + 6) * t) = t * (4 * (4 * M + 6)) := by ring
          _ ≤ t * u_minus := Nat.mul_le_mul_left t h4u
          _ ≤ n_tr := ht_mul_uminus
      omega
    have hB_le : (B : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := Nat.floor_le (by positivity)
    have ha_α : (a_max : ℝ) ≤ (α : ℝ) := by exact_mod_cast (show a_max ≤ α by dsimp [a_max]; omega)
    have ha_le : (a_max : ℝ) ≤ 4 * Real.log (n : ℝ) := ha_α.trans hPh2
    have hR : (8 * (a_max * B) : ℝ) ≤ 32 * (Real.log (n : ℝ)) ^ 4 := by
      calc (8 * (a_max * B) : ℝ) = 8 * ((a_max : ℝ) * (B : ℝ)) := by ring
        _ ≤ 8 * ((4 * Real.log (n : ℝ)) * (Real.log (n : ℝ)) ^ 3) :=
            mul_le_mul_of_nonneg_left (mul_le_mul ha_le hB_le (Nat.cast_nonneg _) (by positivity))
              (by norm_num)
        _ = 32 * (Real.log (n : ℝ)) ^ 4 := by ring
    have h8 : 8 * (a_max * B) ≤ n_tr := by exact_mod_cast (hR.trans h32L4_le_ntr)
    have hs₂_eq : 2 * s₂_max = 2 * ((4 * M + 6) * t) + 4 * (a_max * B) := by dsimp [s₂_max]; ring
    omega
  -- 1. Unmarked coloring sum
  have hunm_bound :
      (∑ pq ∈ PairNu,
          (randomGraphMeasure n).real (partitionColoringEvent (P pq.1) ∩ partitionColoringEvent (P pq.2))) ≤
        Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
          (completeUnmarkedFirstMoment u kv) ^ 2 * unmarkedDiagonalWeight n u kv nu := by
    let IdentOf : ℕ × ℕ → Finset (Finset (Fin n)) :=
      fun pq ↦ (P pq.1).parts ∩ (P pq.2).parts
    let IdentFam : Finset (Finset (Finset (Fin n))) := PairNu.image IdentOf
    have hIdentFam_props : ∀ Ident ∈ IdentFam,
        (Ident : Set (Finset (Fin n))).PairwiseDisjoint id ∧
        Ident = Finset.univ.biUnion (fun j : Fin M ↦ Ident.filter fun D ↦ D.card = u j) ∧
        (∀ j : Fin M, (Ident.filter fun D ↦ D.card = u j).card = nu j) := by
      intro Ident hI
      rcases Finset.mem_image.mp hI with ⟨pq, hpq, rfl⟩
      obtain ⟨hpq_prod, _, hnu_pq⟩ := Finset.mem_filter.mp hpq
      obtain ⟨hpq1, _⟩ := Finset.mem_product.mp hpq_prod
      obtain ⟨hbi, _, _, _⟩ := finset_subset_parts_stats_v13 hu_inj
        (Finset.inter_subset_left : IdentOf pq ⊆ (P pq.1).parts) (hP_all (P pq.1) (hP_sh pq.1 hpq1)).2.2.2
      exact ⟨fun A hA C hC hne ↦ (P pq.1).disjoint (Finset.mem_inter.mp hA).1
        (Finset.mem_inter.mp hC).1 hne, hbi, hnu_pq⟩
    have hIdent_card := card_identFamily_mul_factorials_le_v13 hu_inj hm_nu_le IdentFam hIdentFam_props
    have hslice_Ident : ∀ Ident ∈ IdentFam,
        (∑ pq ∈ PairNu.filter (fun pq ↦ IdentOf pq = Ident),
            (2 : ℝ) ^ (∑ A ∈ (P pq.1).parts \ (P pq.2).parts,
              ∑ C ∈ (P pq.2).parts \ (P pq.1).parts, (A ∩ C).card.choose 2)) ≤
          ((n_tr.factorial : ℝ) / (partialProfileFactorialProduct u r_vec : ℝ)) ^ 2 *
            Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) := by
      intro Ident hI
      set W_res : Finset (Fin n) := Finset.univ \ Ident.biUnion id
      rcases Finset.mem_image.mp hI with ⟨pq₀, hpq₀, hId₀⟩
      obtain ⟨hpq₀_prod, _, hnu₀⟩ := Finset.mem_filter.mp hpq₀
      obtain ⟨hpq₀1, hpq₀2⟩ := Finset.mem_product.mp hpq₀_prod
      have hst₀ := subprofile_inter_and_sdiff_stats_v13 halpha_m hMass hkp
        (P pq₀.1) (P pq₀.2) (hP_sh pq₀.1 hpq₀1) (hP_sh pq₀.2 hpq₀2)
      have hnu₀_eq : (fun j : Fin M ↦ (((P pq₀.1).parts ∩ (P pq₀.2).parts).filter fun D ↦ D.card = u j).card) = nu :=
        funext hnu₀
      have hW_card_ntr : W_res.card = n_tr := by
        have hc : (Finset.univ \ ((P pq₀.1).parts ∩ (P pq₀.2).parts).biUnion id).card =
            n - selectedVertexMass u
              (fun j : Fin M ↦ (((P pq₀.1).parts ∩ (P pq₀.2).parts).filter fun D ↦ D.card = u j).card) :=
          hst₀.2.2.2.2.2.2.2.2.2
        dsimp [W_res, n_tr]
        dsimp [IdentOf] at hId₀
        rwa [hnu₀_eq, hId₀] at hc
      have hW_card_r : W_res.card = selectedVertexMass u r_vec := hW_card_ntr.trans hmass_r.symm
      let toRes : ℕ × ℕ → Finset (Finset (Fin n)) × Finset (Finset (Fin n)) :=
        fun pq ↦ ((P pq.1).parts \ (P pq.2).parts, (P pq.2).parts \ (P pq.1).parts)
      let Slice := PairNu.filter (fun pq ↦ IdentOf pq = Ident)
      let PairRes := Slice.image toRes
      have htoRes_inj : ∀ a ∈ Slice, ∀ b ∈ Slice, toRes a = toRes b → a = b := by
        intro a ha b hb heq
        obtain ⟨haN, hIa⟩ := Finset.mem_filter.mp ha
        obtain ⟨hbN, hIb⟩ := Finset.mem_filter.mp hb
        obtain ⟨ha1, ha2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp haN).1
        obtain ⟨hb1, hb2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hbN).1
        have hPa : (P a.1).parts = Ident ∪ (toRes a).1 := by
          rw [← hIa]; ext D
          simp only [IdentOf, toRes, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
        have hPb : (P b.1).parts = Ident ∪ (toRes b).1 := by
          rw [← hIb]; ext D
          simp only [IdentOf, toRes, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
        have hQa : (P a.2).parts = Ident ∪ (toRes a).2 := by
          rw [← hIa]; ext D
          simp only [IdentOf, toRes, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
        have hQb : (P b.2).parts = Ident ∪ (toRes b).2 := by
          rw [← hIb]; ext D
          simp only [IdentOf, toRes, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
        exact Prod.ext
          (hP_inj ha1 hb1 (Finpartition.ext (hPa.trans ((congrArg (Ident ∪ ·) (congrArg Prod.fst heq)).trans hPb.symm))))
          (hP_inj ha2 hb2 (Finpartition.ext (hQa.trans ((congrArg (Ident ∪ ·) (congrArg Prod.snd heq)).trans hQb.symm))))
      have hRes_mem : ∀ rs ∈ PairRes,
          ((rs.1 : Set (Finset (Fin n))).PairwiseDisjoint id ∧
            rs.1.biUnion id = W_res ∧
            rs.1 = Finset.univ.biUnion (fun j : Fin M ↦ rs.1.filter fun D ↦ D.card = u j) ∧
            (∀ j : Fin M, (rs.1.filter fun D ↦ D.card = u j).card = r_vec j)) ∧
          ((rs.2 : Set (Finset (Fin n))).PairwiseDisjoint id ∧
            rs.2.biUnion id = W_res ∧
            rs.2 = Finset.univ.biUnion (fun j : Fin M ↦ rs.2.filter fun D ↦ D.card = u j) ∧
            (∀ j : Fin M, (rs.2.filter fun D ↦ D.card = u j).card = r_vec j)) ∧
          (∀ A ∈ rs.1, ∀ C ∈ rs.2, (A ∩ C).card ≤ X_max ∨ (u_lo ≤ (A ∩ C).card ∧ (A ∩ C).card ≤ α)) ∧
          (((rs.1 ×ˢ rs.2).filter fun ac ↦ X_max < (ac.1 ∩ ac.2).card).card ≤ 2 * B) ∧
          (∑ ac ∈ (rs.1 ×ˢ rs.2).filter (fun ac ↦ 2 ≤ (ac.1 ∩ ac.2).card), (ac.1 ∩ ac.2).card ≤ s₂_max) := by
        intro rs hrs
        rcases Finset.mem_image.mp hrs with ⟨pq, hpqS, rfl⟩
        obtain ⟨hpqN, hId_pq⟩ := Finset.mem_filter.mp hpqS
        obtain ⟨hpq_prod, hRel_raw, hnu_pq⟩ := Finset.mem_filter.mp hpqN
        obtain ⟨hpq1, hpq2⟩ := Finset.mem_product.mp hpq_prod
        have hRel_pq := hRel_spec (P pq.1) (P pq.2) hRel_raw
        have hnu_pq_eq : (fun j : Fin M ↦ (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = u j).card) = nu :=
          funext hnu_pq
        have hst := subprofile_inter_and_sdiff_stats_v13 halpha_m hMass hkp
          (P pq.1) (P pq.2) (hP_sh pq.1 hpq1) (hP_sh pq.2 hpq2)
        obtain ⟨hbi1, _, _, _⟩ := finset_subset_parts_stats_v13 hu_inj
          (Finset.sdiff_subset : (P pq.1).parts \ (P pq.2).parts ⊆ (P pq.1).parts)
          (hP_all (P pq.1) (hP_sh pq.1 hpq1)).2.2.2
        obtain ⟨hbi2, _, _, _⟩ := finset_subset_parts_stats_v13 hu_inj
          (Finset.sdiff_subset : (P pq.2).parts \ (P pq.1).parts ⊆ (P pq.2).parts)
          (hP_all (P pq.2) (hP_sh pq.2 hpq2)).2.2.2
        have hP_sz : ∀ D ∈ (P pq.1).parts, u_minus ≤ D.card ∧ D.card ≤ a_max := by
          intro D hD; obtain ⟨j, hj⟩ := (hP_all (P pq.1) (hP_sh pq.1 hpq1)).2.2.2 D hD
          rw [hj]; exact ⟨(hu_bds j).2.1, (hu_bds j).2.2⟩
        have hQ_sz : ∀ D ∈ (P pq.2).parts, u_minus ≤ D.card ∧ D.card ≤ a_max := by
          intro D hD; obtain ⟨j, hj⟩ := (hP_all (P pq.2) (hP_sh pq.2 hpq2)).2.2.2 D hD
          rw [hj]; exact ⟨(hu_bds j).2.1, (hu_bds j).2.2⟩
        obtain ⟨⟨_, _, _, _⟩, ⟨hExc_card, hExc_one⟩, hgap_tri, hs₂_tri⟩ :=
          relevantPair_part_trichotomy_and_overlap_gap (P pq.1) (P pq.2)
            (u_minus := u_minus) (a := a_max) (α := α) (M := M) (B := B)
            hM (by dsimp [u_minus, α]; omega) (by dsimp [a_max, u_minus, α]; omega)
            (by dsimp [a_max]; omega) (by dsimp [u_minus, α]; omega)
            hP_sz hQ_sz hRel_pq.1 hRel_pq.2.1 hRel_pq.2.2
        dsimp [IdentOf] at hId_pq
        refine ⟨⟨fun A hA C hC hne ↦ (P pq.1).disjoint (Finset.mem_sdiff.mp hA).1 (Finset.mem_sdiff.mp hC).1 hne,
            by
              have hb : ((P pq.1).parts \ (P pq.2).parts).biUnion id =
                  Finset.univ \ ((P pq.1).parts ∩ (P pq.2).parts).biUnion id := hst.2.2.2.2.2.2.2.1
              rwa [hId_pq] at hb,
            hbi1,
            fun j ↦ by
              have hr : (((P pq.1).parts \ (P pq.2).parts).filter fun D ↦ D.card = u j).card =
                  kv j - (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = u j).card :=
                (hst.2.2.2.2.1 j).1
              rw [hr, congrFun hnu_pq_eq j]⟩,
          ⟨fun A hA C hC hne ↦ (P pq.2).disjoint (Finset.mem_sdiff.mp hA).1 (Finset.mem_sdiff.mp hC).1 hne,
            by
              have hb : ((P pq.2).parts \ (P pq.1).parts).biUnion id =
                  Finset.univ \ ((P pq.1).parts ∩ (P pq.2).parts).biUnion id := hst.2.2.2.2.2.2.2.2.1
              rwa [hId_pq] at hb,
            hbi2,
            fun j ↦ by
              have hr : (((P pq.2).parts \ (P pq.1).parts).filter fun D ↦ D.card = u j).card =
                  kv j - (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = u j).card :=
                (hst.2.2.2.2.1 j).2
              rw [hr, congrFun hnu_pq_eq j]⟩,
          ?_, ?_, ?_⟩
        · intro A hA C hC
          have hC_Q : C ∈ (P pq.2).parts := (Finset.mem_sdiff.mp hC).1
          have hng := hgap_tri A hA C hC_Q
          by_cases hle : (A ∩ C).card ≤ X_max
          · exact Or.inl hle
          · refine Or.inr ⟨by dsimp [X_max, u_lo] at hle hng ⊢; omega, ?_⟩
            exact (Finset.card_le_card Finset.inter_subset_left).trans
              ((hP_sz A (Finset.mem_sdiff.mp hA).1).2.trans (by dsimp [a_max]; omega))
        · set zQ : Finset (Fin n) → ℕ := fun D ↦ ((P pq.2).parts.filter fun E ↦ (D ∩ E).Nonempty).card
          set Exc := ((P pq.1).parts \ (P pq.2).parts).filter fun D ↦ ¬ (D.card ≤ zQ D + 2 * (α - D.card) + 1)
          set Scr := ((P pq.1).parts \ (P pq.2).parts).filter fun D ↦ D.card ≤ zQ D + 2 * (α - D.card) + 1
          have hfst_Exc : ∀ ac ∈ (((P pq.1).parts \ (P pq.2).parts) ×ˢ ((P pq.2).parts \ (P pq.1).parts)).filter
              (fun ac ↦ X_max < (ac.1 ∩ ac.2).card), ac.1 ∈ Exc := by
            intro ac hac
            obtain ⟨hm_p, hgt⟩ := Finset.mem_filter.mp hac
            obtain ⟨hA, hC⟩ := Finset.mem_product.mp hm_p
            by_contra hnotE
            have hAS : ac.1 ∈ Scr := by
              have hun : Scr ∪ Exc = (P pq.1).parts \ (P pq.2).parts := Finset.filter_union_filter_not_eq _ _
              rw [← hun] at hA
              exact (Finset.mem_union.mp hA).resolve_right hnotE
            have hscr_ineq := (Finset.mem_filter.mp hAS).2
            have hdef_A : α - ac.1.card ≤ M + 1 := by
              have := (hP_sz ac.1 (Finset.mem_sdiff.mp hA).1).1; dsimp [u_minus] at this; omega
            have hne_ac : (ac.1 ∩ ac.2).Nonempty := Finset.card_pos.mp (by dsimp [X_max] at hgt; omega)
            have hC_Q : ac.2 ∈ (P pq.2).parts := (Finset.mem_sdiff.mp hC).1
            set Ov := (P pq.2).parts.filter fun E ↦ (ac.1 ∩ E).Nonempty
            have hac2_Ov : ac.2 ∈ Ov := Finset.mem_filter.mpr ⟨hC_Q, hne_ac⟩
            have hbi_A : Ov.biUnion (fun E ↦ ac.1 ∩ E) = ac.1 := by
              ext v
              simp only [Ov, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_inter]
              refine ⟨fun ⟨_, _, hv, _⟩ ↦ hv, fun hv ↦ ?_⟩
              let E := (P pq.2).part v
              have hEQ : E ∈ (P pq.2).parts := (P pq.2).part_mem.mpr (Finset.mem_univ v)
              have hvE : v ∈ E := (P pq.2).mem_part (Finset.mem_univ v)
              exact ⟨E, ⟨hEQ, ⟨v, Finset.mem_inter.mpr ⟨hv, hvE⟩⟩⟩, hv, hvE⟩
            have hdisj_Ov : (Ov : Set (Finset (Fin n))).PairwiseDisjoint (fun E ↦ ac.1 ∩ E) := by
              intro E₁ hE₁ E₂ hE₂ hne
              rw [Function.onFun, Finset.disjoint_left]
              intro v hv₁ hv₂
              exact Finset.disjoint_left.mp
                ((P pq.2).disjoint (Finset.mem_filter.mp hE₁).1 (Finset.mem_filter.mp hE₂).1 hne)
                (Finset.mem_inter.mp hv₁).2 (Finset.mem_inter.mp hv₂).2
            have hsum_A : (ac.1 ∩ ac.2).card + ∑ E ∈ Ov.erase ac.2, (ac.1 ∩ E).card = ac.1.card := by
              rw [Finset.add_sum_erase Ov (fun E ↦ (ac.1 ∩ E).card) hac2_Ov,
                ← Finset.card_biUnion hdisj_Ov, hbi_A]
            have hrest_ge : Ov.card - 1 ≤ ∑ E ∈ Ov.erase ac.2, (ac.1 ∩ E).card := by
              rw [← Finset.card_erase_of_mem hac2_Ov]
              calc (Ov.erase ac.2).card = ∑ _E ∈ Ov.erase ac.2, 1 := by simp
                _ ≤ ∑ E ∈ Ov.erase ac.2, (ac.1 ∩ E).card := Finset.sum_le_sum fun E hE ↦
                    (Finset.mem_filter.mp (Finset.mem_of_mem_erase hE)).2.card_pos
            have hOv_pos : 1 ≤ Ov.card := Finset.card_pos.mpr ⟨ac.2, hac2_Ov⟩
            have hOv_zQ : Ov.card = zQ ac.1 := rfl
            dsimp [X_max] at hgt; omega
          have hinj_fst : ∀ a ∈ (((P pq.1).parts \ (P pq.2).parts) ×ˢ ((P pq.2).parts \ (P pq.1).parts)).filter
                (fun ac ↦ X_max < (ac.1 ∩ ac.2).card),
              ∀ b ∈ (((P pq.1).parts \ (P pq.2).parts) ×ˢ ((P pq.2).parts \ (P pq.1).parts)).filter
                (fun ac ↦ X_max < (ac.1 ∩ ac.2).card),
              a.1 = b.1 → a = b := by
            intro a ha b hb h1
            have haE : a.1 ∈ Exc := hfst_Exc a ha
            have hle1 := (hExc_one a.1 haE).1
            have ha2 : a.2 ∈ (P pq.2).parts.filter (fun D' ↦ 2 ≤ (a.1 ∩ D').card) :=
              Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_product.mp (Finset.mem_filter.mp ha).1).2).1,
                by have := (Finset.mem_filter.mp ha).2; dsimp [X_max] at this; omega⟩
            have hb2 : b.2 ∈ (P pq.2).parts.filter (fun D' ↦ 2 ≤ (a.1 ∩ D').card) :=
              Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_product.mp (Finset.mem_filter.mp hb).1).2).1,
                by rw [h1]; have := (Finset.mem_filter.mp hb).2; dsimp [X_max] at this; omega⟩
            by_contra hne_ab
            have hne2 : a.2 ≠ b.2 := fun h2 ↦ hne_ab (Prod.ext h1 h2)
            have h2_le := Finset.card_le_card (show ({a.2, b.2} : Finset _) ⊆
              (P pq.2).parts.filter (fun D' ↦ 2 ≤ (a.1 ∩ D').card) by
                intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl <;> assumption)
            rw [Finset.card_pair hne2] at h2_le; omega
          exact (Finset.card_le_card_of_injOn Prod.fst hfst_Exc hinj_fst).trans hExc_card
        · have hcard_sdiff : ((P pq.1).parts \ (P pq.2).parts).card = t := by
            have hc : ((P pq.1).parts \ (P pq.2).parts).card =
                selectedBlockCount
                  (fun j : Fin M ↦ kv j - (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = u j).card) :=
              hst.2.2.2.2.2.1
            dsimp [t, r_vec]
            simp_rw [hnu_pq] at hc
            exact hc
          have hsub_sum :
              (∑ ac ∈ (((P pq.1).parts \ (P pq.2).parts) ×ˢ ((P pq.2).parts \ (P pq.1).parts)).filter
                  (fun ac ↦ 2 ≤ (ac.1 ∩ ac.2).card), (ac.1 ∩ ac.2).card) ≤
                ∑ D ∈ (P pq.1).parts \ (P pq.2).parts,
                  ∑ D' ∈ (P pq.2).parts.filter (fun D' ↦ 2 ≤ (D ∩ D').card), (D ∩ D').card := by
            rw [Finset.sum_filter, Finset.sum_product]
            refine Finset.sum_le_sum fun D _ ↦ ?_
            rw [← Finset.sum_filter]
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset_filter _ Finset.sdiff_subset) (fun _ _ _ ↦ Nat.zero_le _)
          exact hsub_sum.trans (hs₂_tri.trans_eq (by rw [hcard_sdiff]))
      obtain ⟨ValidTables, hVT_props, hlift_le⟩ :=
        residual_pair_lift_to_tables_le_v13 hu_inj hW_card_r PairRes hRes_mem
      let SlotR := Σ j : Fin M, Fin (r_vec j)
      let marginR : SlotR → ℕ := fun s ↦ u s.1
      have hcard_SlotR : Fintype.card SlotR = t := by
        simp [SlotR, t, selectedBlockCount, Fintype.card_sigma]
      have hmarginR_sum : ∑ s : SlotR, marginR s = n_tr := by
        have huniv_sig : (Finset.univ : Finset SlotR) =
            Finset.univ.sigma (fun j : Fin M ↦ (Finset.univ : Finset (Fin (r_vec j)))) := by
          ext x; simp
        rw [huniv_sig, Finset.sum_sigma]
        have h1 : (∑ j : Fin M, ∑ _c : Fin (r_vec j), u j) = selectedVertexMass u r_vec := by
          unfold selectedVertexMass
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp [Finset.sum_const, smul_eq_mul, mul_comm]
        dsimp [marginR]; rw [h1, hmass_r]
      have hv_sum_le := validOverlapTable_sum_le_v13 (I := SlotR)
        hntr_ge1 halpha_le_ntr (by dsimp [X_max]; omega)
        (by dsimp [X_max, u_lo, u_minus, α]; omega) (by dsimp [u_lo, u_minus, α]; omega)
        hs₂_half hmarginR_sum (fun s ↦ (hu_bds s.1).2.2.trans (Nat.sub_le _ _))
        ValidTables hVT_props
      rw [hW_card_ntr] at hlift_le
      rw [hcard_SlotR] at hv_sum_le
      have hcard_Slarge : (Finset.Icc u_lo α).card ≤ (M + 1) ^ 3 := by
        rw [Nat.card_Icc]
        have h1 : α + 1 - u_lo ≤ M + 3 := by dsimp [u_lo, u_minus, α]; omega
        have h2 : M + 3 ≤ (M + 1) ^ 3 := by
          calc M + 3 ≤ 3 * M + 1 := by omega
            _ ≤ M ^ 3 + 3 * M ^ 2 + (3 * M + 1) := Nat.le_add_left _ _
            _ = (M + 1) ^ 3 := by ring
        exact h1.trans h2
      have h2B1_le : ((2 * B + 1 : ℕ) : ℝ) ^ (Finset.Icc u_lo α).card ≤
          (2 * (Real.log (n : ℝ)) ^ 3 + 1) ^ ((M + 1) ^ 3) := by
        have hB_le : ((2 * B + 1 : ℕ) : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 3 + 1 := by
          have hf : (B : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := Nat.floor_le (pow_nonneg hL_pos.le 3)
          push_cast; linarith only [hf]
        have hbase_ge1 : (1 : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 3 + 1 := by
          have hp : 0 ≤ (Real.log (n : ℝ)) ^ 3 := pow_nonneg hL_pos.le 3
          linarith only [hp]
        exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hB_le _).trans
          (pow_le_pow_right₀ hbase_ge1 hcard_Slarge)
      have hkern_bound := hKern n_tr t hntr_ge (Nat.sub_le _ _) ht_mul_M1
      have htot_tab :
          (∑ X ∈ ValidTables,
            (((∏ s₁ : SlotR, (marginR s₁).factorial : ℝ) *
                (∏ s₂ : SlotR, (marginR s₂).factorial : ℝ)) /
              ((n_tr.factorial : ℝ) *
                (∏ s₁ : SlotR, ∏ s₂ : SlotR, (X s₁ s₂).factorial : ℝ))) *
              (2 : ℝ) ^ (∑ s₁ : SlotR, ∑ s₂ : SlotR, (X s₁ s₂).choose 2)) ≤
          Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) := by
        refine hv_sum_le.trans ?_
        refine (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h2B1_le
            (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _))
          (Real.exp_pos _).le).trans hkern_bound
      have himg_eq :
          (∑ pq ∈ Slice, (2 : ℝ) ^ (∑ A ∈ (P pq.1).parts \ (P pq.2).parts,
              ∑ C ∈ (P pq.2).parts \ (P pq.1).parts, (A ∩ C).card.choose 2)) =
          (∑ rs ∈ PairRes, (2 : ℝ) ^ (∑ A ∈ rs.1, ∑ C ∈ rs.2, (A ∩ C).card.choose 2)) :=
        (Finset.sum_image (f := fun rs : Finset (Finset (Fin n)) × Finset (Finset (Fin n)) ↦
          (2 : ℝ) ^ (∑ A ∈ rs.1, ∑ C ∈ rs.2, (A ∩ C).card.choose 2)) htoRes_inj).symm
      rw [himg_eq]
      exact hlift_le.trans (mul_le_mul_of_nonneg_left htot_tab (sq_nonneg _))
    have hpq_fact : ∀ pq ∈ PairNu,
        (randomGraphMeasure n).real (partitionColoringEvent (P pq.1) ∩ partitionColoringEvent (P pq.2)) =
          (((1 / 2 : ℝ) ^ selectedInternalEdgeCount u kv) ^ 2 *
            (2 : ℝ) ^ selectedInternalEdgeCount u nu) *
            (2 : ℝ) ^ (∑ A ∈ (P pq.1).parts \ (P pq.2).parts,
              ∑ C ∈ (P pq.2).parts \ (P pq.1).parts, (A ∩ C).card.choose 2) := by
      intro pq hpq
      obtain ⟨hpq_prod, _, hnu_pq_f⟩ := Finset.mem_filter.mp hpq
      obtain ⟨hpq1, hpq2⟩ := Finset.mem_product.mp hpq_prod
      have hfac := randomGraphMeasure_coloring_inter_factorization_v13
        halpha_m hMass hkp (P pq.1) (P pq.2) (hP_sh pq.1 hpq1) (hP_sh pq.2 hpq2)
      dsimp only at hfac
      have hnu_pq : (fun j : Fin M ↦ (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = u j).card) = nu :=
        funext hnu_pq_f
      rwa [hnu_pq] at hfac
    rw [Finset.sum_congr rfl hpq_fact, ← Finset.mul_sum,
      ← Finset.sum_fiberwise_of_maps_to (g := IdentOf) (fun pq hpq ↦ Finset.mem_image_of_mem _ hpq)]
    have hsum_id_le :
        (∑ Ident ∈ IdentFam, ∑ pq ∈ PairNu.filter (fun pq ↦ IdentOf pq = Ident),
            (2 : ℝ) ^ (∑ A ∈ (P pq.1).parts \ (P pq.2).parts,
              ∑ C ∈ (P pq.2).parts \ (P pq.1).parts, (A ∩ C).card.choose 2)) ≤
          (IdentFam.card : ℝ) *
            (((n_tr.factorial : ℝ) / (partialProfileFactorialProduct u r_vec : ℝ)) ^ 2 *
              Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5)) := by
      calc ∑ Ident ∈ IdentFam, _
          ≤ ∑ _Ident ∈ IdentFam,
              (((n_tr.factorial : ℝ) / (partialProfileFactorialProduct u r_vec : ℝ)) ^ 2 *
                Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5)) := Finset.sum_le_sum hslice_Ident
        _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
    have hwt_eq := unmarked_moment_sq_mul_weight_factorization_v13 hMass hnu
    dsimp only at hwt_eq
    calc (((1 / 2 : ℝ) ^ selectedInternalEdgeCount u kv) ^ 2 *
            (2 : ℝ) ^ selectedInternalEdgeCount u nu) *
          (∑ Ident ∈ IdentFam, _)
        ≤ (((1 / 2 : ℝ) ^ selectedInternalEdgeCount u kv) ^ 2 *
            (2 : ℝ) ^ selectedInternalEdgeCount u nu) *
          (((n.factorial : ℝ) / ((n_tr.factorial : ℝ) * (partialProfileFactorialProduct u nu : ℝ))) *
            (((n_tr.factorial : ℝ) / (partialProfileFactorialProduct u r_vec : ℝ)) ^ 2 *
              Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5))) :=
          mul_le_mul_of_nonneg_left
            (hsum_id_le.trans (mul_le_mul_of_nonneg_right hIdent_card
              (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)))
            (mul_nonneg (sq_nonneg _) (pow_nonneg zero_le_two _))
      _ = Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
            ((((1 / 2 : ℝ) ^ selectedInternalEdgeCount u kv) ^ 2 *
                (2 : ℝ) ^ selectedInternalEdgeCount u nu) *
              ((n.factorial : ℝ) / ((n_tr.factorial : ℝ) * (partialProfileFactorialProduct u nu : ℝ))) *
              ((n_tr.factorial : ℝ) / (partialProfileFactorialProduct u r_vec : ℝ)) ^ 2) := by ring
      _ = Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
            (completeUnmarkedFirstMoment u kv) ^ 2 * unmarkedDiagonalWeight n u kv nu := by
          rw [← hwt_eq]; ring
  -- 2. Cocoloring sum via `randomGraphMeasure_partitionCocoloringEvent_inter_le_two_pow_sub_inter`
  refine ⟨hunm_bound, ?_⟩
  set k := selectedBlockCount kv
  set L_nu := selectedBlockCount nu
  have hL_le_2k : L_nu ≤ 2 * k := by
    have hle : L_nu ≤ k := Finset.sum_le_sum fun j _ ↦ hnu j
    omega
  have hpq_co : ∀ pq ∈ PairNu,
      (randomGraphMeasure n).real (partitionCocoloringEvent (P pq.1) ∩ partitionCocoloringEvent (P pq.2)) ≤
        (2 : ℝ) ^ (2 * k - L_nu) *
          (randomGraphMeasure n).real (partitionColoringEvent (P pq.1) ∩ partitionColoringEvent (P pq.2)) := by
    intro pq hpq
    obtain ⟨hpq_prod, _, hnu_pq_f⟩ := Finset.mem_filter.mp hpq
    obtain ⟨hpq1, hpq2⟩ := Finset.mem_product.mp hpq_prod
    have hnu_pq : (fun j : Fin M ↦ (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = u j).card) = nu :=
      funext hnu_pq_f
    have hst := subprofile_inter_and_sdiff_stats_v13 halpha_m hMass hkp
      (P pq.1) (P pq.2) (hP_sh pq.1 hpq1) (hP_sh pq.2 hpq2)
    have hId_c : ((P pq.1).parts ∩ (P pq.2).parts).card = L_nu := by
      have hc : ((P pq.1).parts ∩ (P pq.2).parts).card =
          selectedBlockCount
            (fun j : Fin M ↦ (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = u j).card) :=
        hst.2.1
      rwa [hnu_pq] at hc
    have hcard_sub : (P pq.1).parts.card + (P pq.2).parts.card - ((P pq.1).parts ∩ (P pq.2).parts).card =
        2 * k - L_nu := by
      rw [(hP_all (P pq.1) (hP_sh pq.1 hpq1)).1, (hP_all (P pq.2) (hP_sh pq.2 hpq2)).1, hId_c]
      dsimp [k]; omega
    have hsh2 : ∀ D ∈ (P pq.1).parts ∩ (P pq.2).parts, 2 ≤ D.card := by
      intro D hD; obtain ⟨j, hj⟩ := (hP_all (P pq.1) (hP_sh pq.1 hpq1)).2.2.2 D (Finset.mem_inter.mp hD).1
      rw [hj]; exact (hu_bds j).1
    rw [← hcard_sub]
    exact (randomGraphMeasure_partitionCocoloringEvent_inter_le_two_pow_sub_inter (P pq.1) (P pq.2) hsh2).2
  have hmom_rel :
      (2 : ℝ) ^ (2 * k - L_nu) *
        (Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
          (completeUnmarkedFirstMoment u kv) ^ 2 * unmarkedDiagonalWeight n u kv nu) =
      Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
        (completeSignedFirstMoment u kv) ^ 2 * partialDiagonalWeight n u kv nu := by
    have h2L : (2 : ℝ) ^ (2 * k - L_nu) * (2 : ℝ) ^ L_nu = ((2 : ℝ) ^ k) ^ 2 := by
      rw [← pow_add, Nat.sub_add_cancel hL_le_2k, mul_comm 2 k, pow_mul]
    have h2k_ne : (2 : ℝ) ^ k ≠ 0 := by positivity
    dsimp [k, L_nu] at h2L h2k_ne ⊢
    unfold selectedBlockCount at h2L h2k_ne
    unfold completeUnmarkedFirstMoment unmarkedDiagonalWeight selectedBlockCount
    calc (2 : ℝ) ^ (2 * ∑ i, kv i - ∑ i, nu i) *
            (Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
              (((2 : ℝ) ^ ∑ i, kv i)⁻¹ * completeSignedFirstMoment u kv) ^ 2 *
              ((2 : ℝ) ^ (∑ i, nu i) * partialDiagonalWeight n u kv nu))
        = Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
            (((2 : ℝ) ^ (2 * ∑ i, kv i - ∑ i, nu i) * (2 : ℝ) ^ (∑ i, nu i)) *
              (((2 : ℝ) ^ ∑ i, kv i)⁻¹ ^ 2)) *
            (completeSignedFirstMoment u kv) ^ 2 * partialDiagonalWeight n u kv nu := by ring
      _ = Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
            (completeSignedFirstMoment u kv) ^ 2 * partialDiagonalWeight n u kv nu := by
          rw [h2L, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 h2k_ne), mul_one]
  calc ∑ pq ∈ PairNu,
          (randomGraphMeasure n).real (partitionCocoloringEvent (P pq.1) ∩ partitionCocoloringEvent (P pq.2))
      ≤ ∑ pq ∈ PairNu, (2 : ℝ) ^ (2 * k - L_nu) *
          (randomGraphMeasure n).real (partitionColoringEvent (P pq.1) ∩ partitionColoringEvent (P pq.2)) :=
        Finset.sum_le_sum hpq_co
    _ = (2 : ℝ) ^ (2 * k - L_nu) *
          ∑ pq ∈ PairNu,
            (randomGraphMeasure n).real (partitionColoringEvent (P pq.1) ∩ partitionColoringEvent (P pq.2)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (2 : ℝ) ^ (2 * k - L_nu) *
          (Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
            (completeUnmarkedFirstMoment u kv) ^ 2 * unmarkedDiagonalWeight n u kv nu) :=
        mul_le_mul_of_nonneg_left hunm_bound (pow_nonneg zero_le_two _)
    _ = Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
          (completeSignedFirstMoment u kv) ^ 2 * partialDiagonalWeight n u kv nu := hmom_rel

private theorem sum_filter_eq_of_iff_v13 {α β : Type*} [AddCommMonoid β]
    (s : Finset α) (f : α → β) {p₁ p₂ : α → Prop}
    {i₁ : DecidablePred p₁} {i₂ : DecidablePred p₂} (hp : ∀ x, p₁ x ↔ p₂ x) :
    (∑ x ∈ @Finset.filter α p₁ i₁ s, f x) = ∑ x ∈ @Finset.filter α p₂ i₂ s, f x := by
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ ↦ hp x

/-- **Unconditional `G(n, 1/2)` Lemma 7.2 (`main.tex` lines 1018–1034, `lem:hp-transfer`):**
for every `M ≥ 1` and `c₀ ∈ (0, 1/2)`, there exists `C_ov > 0` such that eventually for all `n`,
uniformly over `m ∈ {0, 1}`, any window profile `kv : Fin M → ℕ` embedded as `kp` with vertex mass
`n`, any subprofile `ν ≤ kv` in the non-similar range `n - m_ν ≥ n^(1 - c₀)`, and any injective
family `(P i)_{i ∈ S_idx}` of partitions realizing profile `kp`, the sum of joint coloring (resp.
cocoloring) probabilities over all relevant pairs `(i, j) ∈ Π_rel` with common-class profile `ν`
is at most `exp(C_ov (log n)⁵) E[X̄_k]² F_1^ch(ν)` (resp. `exp(C_ov (log n)⁵) E[Z_k^mk]² W(ν)`). -/
theorem eventually_lemma72_overlapSum_le
    {M : ℕ} (hM : 1 ≤ M) {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    ∃ C_ov : ℝ, 0 < C_ov ∧ ∀ᶠ n : ℕ in atTop,
      let α : ℕ := phaseNat n
      let B : ℕ := Nat.floor ((Real.log (n : ℝ)) ^ 3)
      let RelPair : VertexPartition n → VertexPartition n → Prop := fun Q Q' ↦
        ((∀ D ∈ Q.parts,
            (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card ≤ 2 ∨
              D.card ≤ (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card + 2 * (α - D.card) + 1) ∧
          (∀ D' ∈ Q'.parts,
            (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card ≤ 2 ∨
              D'.card ≤ (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card + 2 * (α - D'.card) + 1)) ∧
        ((∀ D ∈ Q.parts, (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 →
            ∃ D' ∈ Q'.parts, (D ∩ D').card = D.card - 1) ∧
          (∀ D' ∈ Q'.parts, (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 →
            ∃ D ∈ Q.parts, (D' ∩ D).card = D'.card - 1)) ∧
        ((Q.parts.filter fun D ↦
            (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 ∧
              ∃ D' ∈ Q'.parts, D'.card - 1 ≤ (D ∩ D').card).card ≤ B ∧
          (Q'.parts.filter fun D' ↦
            (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 ∧
              ∃ D ∈ Q.parts, D.card - 1 ≤ (D' ∩ D).card).card ≤ B)
      ∀ {m : ℕ}, m ≤ 1 →
        let u : Fin M → ℕ := fun j ↦ α - (m + 1 + j.1)
        ∀ (kv : Fin M → ℕ) (kp : ColoringProfile α) (nu : Fin M → ℕ),
          selectedVertexMass u kv = n →
          (∀ idx : Fin α, kp idx = ∑ j : Fin M, if u j = idx.1 + 1 then kv j else 0) →
          IsPartialSubprofile kv nu →
          (n : ℝ) ^ (1 - c₀) ≤ ((n - selectedVertexMass u nu : ℕ) : ℝ) →
          ∀ (S_idx : Finset ℕ) (P : ℕ → VertexPartition n),
            Set.InjOn P (S_idx : Set ℕ) →
            (∀ i ∈ S_idx, partitionShape (P i) = ColoringProfile.sizes kp) →
            let PairNu : Finset (ℕ × ℕ) :=
              (S_idx ×ˢ S_idx).filter fun pq ↦
                RelPair (P pq.1) (P pq.2) ∧
                (∀ j : Fin M, (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = u j).card = nu j)
            (∑ pq ∈ PairNu,
                (randomGraphMeasure n).real
                  (partitionColoringEvent (P pq.1) ∩ partitionColoringEvent (P pq.2))) ≤
              Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
                (completeUnmarkedFirstMoment u kv) ^ 2 *
                unmarkedDiagonalWeight n u kv nu ∧
            (∑ pq ∈ PairNu,
                (randomGraphMeasure n).real
                  (partitionCocoloringEvent (P pq.1) ∩ partitionCocoloringEvent (P pq.2))) ≤
              Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
                (completeSignedFirstMoment u kv) ^ 2 *
                partialDiagonalWeight n u kv nu := by
  have hc₀_01 : c₀ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hc₀.1, by linarith only [hc₀.2]⟩
  obtain ⟨C_ov, hC_ov_pos, hKern_ev⟩ := eventually_overlapKernel_le_exp_polylog5 M hc₀_01
  refine ⟨C_ov, hC_ov_pos, ?_⟩
  have h1mc₀_pos : 0 < 1 - c₀ := by linarith only [hc₀.2]
  have ho4 : (fun x : ℝ ↦ (Real.log x) ^ ((4 : ℕ) : ℝ)) =o[atTop] (fun x : ℝ ↦ x ^ (1 - c₀)) :=
    isLittleO_log_rpow_rpow_atTop ((4 : ℕ) : ℝ) h1mc₀_pos
  have hb4 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Asymptotics.isLittleO_iff.mp ho4 (by norm_num : (0 : ℝ) < 1 / 32))
  have halpha_ev : ∀ᶠ n : ℕ in atTop, 20 * M + 30 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (((20 * M + 30 : ℕ) : ℝ)),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  filter_upwards [eventually_ge_atTop 4,
    tendsto_logOrder_atTop.eventually_ge_atTop 2,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    halpha_ev, hb4, hKern_ev] with n hn4 hL2 hPh halpha_n hb4_n hKern
  intro α B RelPair m hm u kv kp nu hMass hkp hnu hntr_ge S_idx P hP_inj hP_sh PairNu
  dsimp [logOrder] at hL2
  have h := lemma72_fixed_n_of_relPair_v13 hn4 hM hm h1mc₀_pos hL2 hPh halpha_n hb4_n hKern
    (RelPair := RelPair) (fun _ _ h ↦ h) kv kp nu hMass hkp hnu hntr_ge S_idx P hP_inj hP_sh
  dsimp only [PairNu, u, α, B]
  exact ⟨(sum_filter_eq_of_iff_v13 _ _ (fun _ ↦ Iff.rfl)).trans_le h.1,
    (sum_filter_eq_of_iff_v13 _ _ (fun _ ↦ Iff.rfl)).trans_le h.2⟩

/-!
## 3. Unconditional Proposition 7.3 similar-range bound (`n - m_ν < n^(1 - c₀)`)
-/

private theorem resPartition_card_le_pow_v13
    {n t : ℕ} (W₀ : Finset (Fin n))
    (ResFam : Finset (Finset (Finset (Fin n))))
    (hFam : ∀ R ∈ ResFam,
      (R : Set (Finset (Fin n))).PairwiseDisjoint id ∧
      R.biUnion id = W₀ ∧
      R.card = t) :
    (ResFam.card : ℝ) ≤ ((max 1 t : ℕ) : ℝ) ^ W₀.card := by
  rcases Nat.eq_zero_or_pos t with rfl | ht_pos
  · have hle1 : ResFam.card ≤ 1 := by
      have hsub : ResFam ⊆ {∅} := by
        intro R hR
        rw [Finset.mem_singleton]
        exact Finset.card_eq_zero.mp (hFam R hR).2.2
      exact (Finset.card_le_card hsub).trans (by simp)
    simp only [Nat.max_zero]
    exact_mod_cast (hle1.trans (by simp))
  · have hmax_eq : max 1 t = t := Nat.max_eq_right ht_pos
    rw [hmax_eq]
    let DecQ := Σ R : ↥ResFam, ↥R.1 ≃ Fin t
    have hDec_card : Fintype.card DecQ = ResFam.card * t.factorial := by
      dsimp [DecQ]; rw [Fintype.card_sigma]
      have hfib : ∀ R : ↥ResFam, Fintype.card (↥R.1 ≃ Fin t) = t.factorial := by
        intro R
        have hc : Fintype.card ↥R.1 = t := by rw [Fintype.card_coe, (hFam R.1 R.2).2.2]
        exact (Fintype.card_congr (Equiv.equivCongr (Fintype.equivFinOfCardEq hc) (Equiv.refl _))).trans
          (by rw [Fintype.card_perm, Fintype.card_fin])
      simp_rw [hfib]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
    let partQ : DecQ → Fin t → Finset (Fin n) := fun d i ↦ (d.2.symm i).1
    have hpartQ_mem : ∀ (d : DecQ) (i : Fin t), partQ d i ∈ d.1.1 ∧ partQ d i ⊆ W₀ := by
      intro d i
      have hm := (d.2.symm i).2
      refine ⟨hm, fun x hx ↦ ?_⟩
      rw [← (hFam d.1.1 d.1.2).2.1, Finset.mem_biUnion]
      exact ⟨partQ d i, hm, hx⟩
    have hpartQ_inj : ∀ d : DecQ, Function.Injective (partQ d) := by
      intro d i₁ i₂ heq
      exact d.2.symm.injective (Subtype.ext heq)
    have hex_i : ∀ (d : DecQ) (v : ↥W₀), ∃ i : Fin t, v.1 ∈ partQ d i := by
      intro d v
      have hv : v.1 ∈ d.1.1.biUnion id := (hFam d.1.1 d.1.2).2.1.symm ▸ v.2
      rcases Finset.mem_biUnion.mp hv with ⟨D, hD, hvD⟩
      refine ⟨d.2 ⟨D, hD⟩, ?_⟩
      change v.1 ∈ (d.2.symm (d.2 ⟨D, hD⟩)).1
      rw [d.2.symm_apply_apply]; exact hvD
    let toFn : DecQ → (↥W₀ → Fin t) := fun d v ↦ (hex_i d v).choose
    have htoFn_iff : ∀ (d : DecQ) (i : Fin t) (v : ↥W₀),
        toFn d v = i ↔ v.1 ∈ partQ d i := by
      intro d i v
      constructor
      · rintro rfl; exact (hex_i d v).choose_spec
      · intro hv
        by_contra hne
        have hne_p : partQ d (toFn d v) ≠ partQ d i := fun hp ↦ hne (hpartQ_inj d hp)
        exact Finset.disjoint_left.mp
          ((hFam d.1.1 d.1.2).1 (hpartQ_mem d (toFn d v)).1 (hpartQ_mem d i).1 hne_p)
          (hex_i d v).choose_spec hv
    have htoFn_inj : Function.Injective toFn := by
      rintro ⟨R₁, β₁⟩ ⟨R₂, β₂⟩ heq
      have hp_eq : ∀ i : Fin t, partQ ⟨R₁, β₁⟩ i = partQ ⟨R₂, β₂⟩ i := by
        intro i; ext x
        constructor
        · intro hx
          have hxW : x ∈ W₀ := (hpartQ_mem ⟨R₁, β₁⟩ i).2 hx
          have hr := (htoFn_iff ⟨R₁, β₁⟩ i ⟨x, hxW⟩).mpr hx
          rw [heq] at hr
          exact (htoFn_iff ⟨R₂, β₂⟩ i ⟨x, hxW⟩).mp hr
        · intro hx
          have hxW : x ∈ W₀ := (hpartQ_mem ⟨R₂, β₂⟩ i).2 hx
          have hr := (htoFn_iff ⟨R₂, β₂⟩ i ⟨x, hxW⟩).mpr hx
          rw [← heq] at hr
          exact (htoFn_iff ⟨R₁, β₁⟩ i ⟨x, hxW⟩).mp hr
      have hR_val : R₁.1 = R₂.1 := by
        ext D; constructor
        · intro hD
          have hc : partQ ⟨R₁, β₁⟩ (β₁ ⟨D, hD⟩) = D :=
            congrArg Subtype.val (β₁.symm_apply_apply ⟨D, hD⟩)
          rw [← hc, hp_eq]; exact (hpartQ_mem ⟨R₂, β₂⟩ _).1
        · intro hD
          have hc : partQ ⟨R₂, β₂⟩ (β₂ ⟨D, hD⟩) = D :=
            congrArg Subtype.val (β₂.symm_apply_apply ⟨D, hD⟩)
          rw [← hc, ← hp_eq]; exact (hpartQ_mem ⟨R₁, β₁⟩ _).1
      have hR_eq : R₁ = R₂ := Subtype.ext hR_val
      subst hR_eq
      congr 1; apply Equiv.ext; intro x
      apply β₂.symm.injective
      rw [β₂.symm_apply_apply]
      have hc := hp_eq (β₁ x)
      change (β₁.symm (β₁ x)).1 = (β₂.symm (β₁ x)).1 at hc
      rw [β₁.symm_apply_apply] at hc
      exact Subtype.ext hc.symm
    have hle_nat : ResFam.card ≤ t ^ W₀.card := by
      have h1 : ResFam.card ≤ Fintype.card DecQ := by
        rw [hDec_card]; exact Nat.le_mul_of_pos_right _ (Nat.factorial_pos t)
      refine h1.trans ((Fintype.card_le_of_injective toFn htoFn_inj).trans ?_)
      rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_coe, Fintype.card_fin]
    exact_mod_cast hle_nat

private theorem coloring_inter_le_of_scrambled_count_v13
    {n alpha m M z : ℕ} (halpha : m + M + 2 ≤ alpha)
    {kv : Fin M → ℕ} {kp : ColoringProfile alpha}
    (hMass : selectedVertexMass (fun j : Fin M ↦ alpha - (m + 1 + j.1)) kv = n)
    (hkp : ∀ idx : Fin alpha,
      kp idx = ∑ j : Fin M, if alpha - (m + 1 + j.1) = idx.1 + 1 then kv j else 0)
    (P Q : VertexPartition n)
    (hP_sh : partitionShape P = ColoringProfile.sizes kp)
    (hQ_sh : partitionShape Q = ColoringProfile.sizes kp)
    {Scr : Finset (Finset (Fin n))} (hScr_sub : Scr ⊆ P.parts)
    (hz_scr : ∀ D ∈ Scr, z ≤ (Q.parts.filter fun W ↦ (D ∩ W).Nonempty).card) :
    (randomGraphMeasure n).real (partitionColoringEvent P ∩ partitionColoringEvent Q) ≤
      (randomGraphMeasure n).real (partitionColoringEvent P) *
        ((2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ Scr.card := by
  let u : Fin M → ℕ := fun j ↦ alpha - (m + 1 + j.1)
  obtain ⟨_, _, _, _, hforb_eq, _⟩ := windowProfile_part_sizes_and_counts_v13 halpha hMass hkp
  have hP_prob : (randomGraphMeasure n).real (partitionColoringEvent P) =
      (1 / 2 : ℝ) ^ selectedInternalEdgeCount u kv := by
    let P_pp : ProfilePartition n kp := ⟨P, hP_sh⟩
    rw [Measure.real, show P = P_pp.1 from rfl, randomGraphMeasure_partitionColoringEvent P_pp,
      hforb_eq, ENNReal.toReal_pow]
    congr 1; norm_num
  have hPQ_prob : (randomGraphMeasure n).real (partitionColoringEvent P ∩ partitionColoringEvent Q) =
      ((1 / 2 : ℝ) ^ selectedInternalEdgeCount u kv) ^ 2 *
        (2 : ℝ) ^ (∑ A ∈ P.parts, ∑ C ∈ Q.parts, (A ∩ C).card.choose 2) := by
    have hset : partitionColoringEvent P ∩ partitionColoringEvent Q =
        {G : LabeledGraph n | G ≤ (partitionInternalGraph P ⊔ partitionInternalGraph Q)ᶜ} := by
      ext G
      rw [Set.mem_inter_iff, mem_partitionColoringEvent_iff_le_compl,
        mem_partitionColoringEvent_iff_le_compl, Set.mem_setOf_eq, compl_sup, le_inf_iff]
    have hp : (randomGraphMeasure n).real (partitionColoringEvent P ∩ partitionColoringEvent Q) =
        (1 / 2 : ℝ) ^ (partitionInternalGraph P ⊔ partitionInternalGraph Q).edgeSet.ncard := by
      rw [Measure.real, hset, randomGraphMeasure_le_compl, ENNReal.toReal_pow]; congr 1; norm_num
    have hun : (partitionInternalGraph P ⊔ partitionInternalGraph Q).edgeSet.ncard +
        ∑ A ∈ P.parts, ∑ C ∈ Q.parts, (A ∩ C).card.choose 2 =
        2 * selectedInternalEdgeCount u kv := by
      let P_pp : ProfilePartition n kp := ⟨P, hP_sh⟩
      let Q_pp : ProfilePartition n kp := ⟨Q, hQ_sh⟩
      simpa only [P_pp, Q_pp, profileOverlapCellCount, hforb_eq] using
        ncard_profilePartitionInternalGraph_edgeSet_union_add_overlap P_pp Q_pp
    set a_nc := (partitionInternalGraph P ⊔ partitionInternalGraph Q).edgeSet.ncard
    set w_ov := ∑ A ∈ P.parts, ∑ C ∈ Q.parts, (A ∩ C).card.choose 2
    have h2w_ne : (2 : ℝ) ^ w_ov ≠ 0 := by positivity
    have h1 : (1 / 2 : ℝ) ^ a_nc * (1 / 2 : ℝ) ^ w_ov =
        ((1 / 2 : ℝ) ^ selectedInternalEdgeCount u kv) ^ 2 := by
      rw [← pow_add, hun, pow_mul', sq]
    have hw_inv : (1 / 2 : ℝ) ^ w_ov * (2 : ℝ) ^ w_ov = 1 := by
      rw [one_div, inv_pow, inv_mul_cancel₀ h2w_ne]
    have h2 : (1 / 2 : ℝ) ^ a_nc =
        ((1 / 2 : ℝ) ^ selectedInternalEdgeCount u kv) ^ 2 * (2 : ℝ) ^ w_ov := by
      calc (1 / 2 : ℝ) ^ a_nc
          = (1 / 2 : ℝ) ^ a_nc * ((1 / 2 : ℝ) ^ w_ov * (2 : ℝ) ^ w_ov) := by rw [hw_inv, mul_one]
        _ = ((1 / 2 : ℝ) ^ a_nc * (1 / 2 : ℝ) ^ w_ov) * (2 : ℝ) ^ w_ov := (mul_assoc _ _ _).symm
        _ = ((1 / 2 : ℝ) ^ selectedInternalEdgeCount u kv) ^ 2 * (2 : ℝ) ^ w_ov := by rw [h1]
    rw [hp, h2]
  -- Bound `∑ A ∈ P.parts, ∑ C ∈ Q.parts, (A ∩ C).card.choose 2 + Scr.card * z.choose 2 ≤ E_kv`
  have hA_in_le : ∀ A ∈ P.parts,
      (∑ C ∈ Q.parts, (A ∩ C).card.choose 2) +
        (((A.powersetCard 2).filter fun e ↦ ∀ W ∈ Q.parts, ¬ e ⊆ W).card) ≤
        A.card.choose 2 := by
    intro A _
    let SubIn := Q.parts.biUnion fun C ↦ (A ∩ C).powersetCard 2
    let SubOut := (A.powersetCard 2).filter fun e ↦ ∀ W ∈ Q.parts, ¬ e ⊆ W
    have hdisj_Q : (Q.parts : Set (Finset (Fin n))).PairwiseDisjoint
        (fun C ↦ (A ∩ C).powersetCard 2) := by
      intro C₁ hC₁ C₂ hC₂ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro e he₁ he₂
      obtain ⟨hsub₁, hc2⟩ := Finset.mem_powersetCard.mp he₁
      obtain ⟨hsub₂, _⟩ := Finset.mem_powersetCard.mp he₂
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < e.card)
      exact Finset.disjoint_left.mp (Q.disjoint hC₁ hC₂ hne)
        (Finset.mem_inter.mp (hsub₁ hv)).2 (Finset.mem_inter.mp (hsub₂ hv)).2
    have hcard_in : SubIn.card = ∑ C ∈ Q.parts, (A ∩ C).card.choose 2 := by
      rw [Finset.card_biUnion hdisj_Q]
      exact Finset.sum_congr rfl fun C _ ↦ Finset.card_powersetCard 2 (A ∩ C)
    have hdisj_io : Disjoint SubIn SubOut := by
      rw [Finset.disjoint_left]
      intro e hin hout
      rcases Finset.mem_biUnion.mp hin with ⟨C, hCQ, heC⟩
      exact (Finset.mem_filter.mp hout).2 C hCQ
        ((Finset.mem_powersetCard.mp heC).1.trans Finset.inter_subset_right)
    have hun_sub : SubIn ∪ SubOut ⊆ A.powersetCard 2 := by
      refine Finset.union_subset ?_ (Finset.filter_subset _ _)
      intro e he
      rcases Finset.mem_biUnion.mp he with ⟨C, _, heC⟩
      obtain ⟨hsub, hc2⟩ := Finset.mem_powersetCard.mp heC
      exact Finset.mem_powersetCard.mpr ⟨hsub.trans Finset.inter_subset_left, hc2⟩
    have hcu := (Finset.card_union_of_disjoint hdisj_io).symm.trans_le
      ((Finset.card_le_card hun_sub).trans_eq (Finset.card_powersetCard 2 A))
    rwa [hcard_in] at hcu
  have hScr_extra : ∀ A ∈ Scr,
      z.choose 2 ≤ ((A.powersetCard 2).filter fun e ↦ ∀ W ∈ Q.parts, ¬ e ⊆ W).card := by
    intro A hAS
    let Ov := Q.parts.filter fun W ↦ (A ∩ W).Nonempty
    have hz_Ov : z ≤ Ov.card := hz_scr A hAS
    let rep : ↥Ov → Fin n := fun W ↦ (Finset.mem_filter.mp W.2).2.choose
    have hrep_mem : ∀ W : ↥Ov, rep W ∈ A ∧ rep W ∈ W.1 := fun W ↦
      Finset.mem_inter.mp (Finset.mem_filter.mp W.2).2.choose_spec
    have hrep_inj : Function.Injective rep := by
      intro W₁ W₂ heq
      by_contra hne
      have hne_val : W₁.1 ≠ W₂.1 := fun h ↦ hne (Subtype.ext h)
      exact Finset.disjoint_left.mp
        (Q.disjoint (Finset.mem_filter.mp W₁.2).1 (Finset.mem_filter.mp W₂.2).1 hne_val)
        (hrep_mem W₁).2 (heq ▸ (hrep_mem W₂).2)
    let Reps : Finset (Fin n) := Finset.univ.image rep
    have hReps_sub : Reps ⊆ A := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨W, _, rfl⟩
      exact (hrep_mem W).1
    have hReps_card : Reps.card = Ov.card := by
      rw [Finset.card_image_of_injective _ hrep_inj, Finset.card_univ, Fintype.card_coe]
    have hpow_sub : Reps.powersetCard 2 ⊆
        (A.powersetCard 2).filter (fun e ↦ ∀ W ∈ Q.parts, ¬ e ⊆ W) := by
      intro e he
      obtain ⟨heR, he2⟩ := Finset.mem_powersetCard.mp he
      refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨heR.trans hReps_sub, he2⟩, ?_⟩
      intro W hWQ heW
      rcases Finset.card_eq_two.mp he2 with ⟨x, y, hxy, rfl⟩
      have hxR : x ∈ Reps := heR (Finset.mem_insert_self x {y})
      have hyR : y ∈ Reps := heR (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
      rcases Finset.mem_image.mp hxR with ⟨W₁, _, rfl⟩
      rcases Finset.mem_image.mp hyR with ⟨W₂, _, rfl⟩
      have hW₁_ne_W₂ : W₁.1 ≠ W₂.1 := fun h ↦ hxy (congrArg rep (Subtype.ext h))
      have hxW : rep W₁ ∈ W := heW (Finset.mem_insert_self _ _)
      have hyW : rep W₂ ∈ W := heW (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hW_eq₁ : W = W₁.1 := by
        by_contra hne₁
        exact Finset.disjoint_left.mp (Q.disjoint hWQ (Finset.mem_filter.mp W₁.2).1 hne₁)
          hxW (hrep_mem W₁).2
      have hW_eq₂ : W = W₂.1 := by
        by_contra hne₂
        exact Finset.disjoint_left.mp (Q.disjoint hWQ (Finset.mem_filter.mp W₂.2).1 hne₂)
          hyW (hrep_mem W₂).2
      exact hW₁_ne_W₂ (hW_eq₁.symm.trans hW_eq₂)
    calc z.choose 2 ≤ Reps.card.choose 2 := Nat.choose_le_choose 2 (hReps_card ▸ hz_Ov)
      _ = (Reps.powersetCard 2).card := (Finset.card_powersetCard 2 Reps).symm
      _ ≤ _ := Finset.card_le_card hpow_sub
  have hov_le :
      (∑ A ∈ P.parts, ∑ C ∈ Q.parts, (A ∩ C).card.choose 2) + Scr.card * z.choose 2 ≤
        selectedInternalEdgeCount u kv := by
    have hsum_parts : ∑ A ∈ P.parts, A.card.choose 2 = selectedInternalEdgeCount u kv := by
      obtain ⟨hu_inj, _, _, _, _, hP_all⟩ :=
        windowProfile_part_sizes_and_counts_v13 halpha hMass hkp
      obtain ⟨_, _, _, hedge⟩ := finset_subset_parts_stats_v13 hu_inj
        (Finset.Subset.refl P.parts) (hP_all P hP_sh).2.2.2
      have hcF : (fun j : Fin M ↦ (P.parts.filter fun D ↦ D.card = u j).card) = kv :=
        funext (hP_all P hP_sh).2.1
      rw [hedge, hcF]
    have hun_S : Scr ∪ (P.parts \ Scr) = P.parts := Finset.union_sdiff_of_subset hScr_sub
    have hdisj_S : Disjoint Scr (P.parts \ Scr) := Finset.disjoint_sdiff
    rw [← hsum_parts, ← hun_S, Finset.sum_union hdisj_S, Finset.sum_union hdisj_S]
    have h1 : (∑ A ∈ Scr, ∑ C ∈ Q.parts, (A ∩ C).card.choose 2) + Scr.card * z.choose 2 ≤
        ∑ A ∈ Scr, A.card.choose 2 := by
      have hsc : Scr.card * z.choose 2 = ∑ _A ∈ Scr, z.choose 2 := by simp
      rw [hsc, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun A hAS ↦
        (Nat.add_le_add_left (hScr_extra A hAS) _).trans (hA_in_le A (hScr_sub hAS))
    have h2 : ∑ A ∈ P.parts \ Scr, ∑ C ∈ Q.parts, (A ∩ C).card.choose 2 ≤
        ∑ A ∈ P.parts \ Scr, A.card.choose 2 :=
      Finset.sum_le_sum fun A hA ↦
        (Nat.le_add_right _ _).trans (hA_in_le A (Finset.mem_sdiff.mp hA).1)
    omega
  -- Convert `hov_le` into the real probability inequality
  rw [hPQ_prob, hP_prob]
  set E_kv := selectedInternalEdgeCount u kv
  set W_ov := ∑ A ∈ P.parts, ∑ C ∈ Q.parts, (A ∩ C).card.choose 2
  have h2_rpow : ((2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ Scr.card =
      ((2 : ℝ) ^ (Scr.card * z.choose 2))⁻¹ := by
    rw [Real.rpow_neg two_pos.le, Real.rpow_natCast, inv_pow, ← pow_mul, mul_comm]
  rw [h2_rpow]
  have hpow_le : (2 : ℝ) ^ W_ov * (2 : ℝ) ^ (Scr.card * z.choose 2) ≤ (2 : ℝ) ^ E_kv := by
    rw [← pow_add]; exact pow_le_pow_right₀ one_le_two hov_le
  have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ (Scr.card * z.choose 2) := by positivity
  have h2E_ne : (2 : ℝ) ^ E_kv ≠ 0 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ h2s_pos]
  calc ((1 / 2 : ℝ) ^ E_kv) ^ 2 * (2 : ℝ) ^ W_ov * (2 : ℝ) ^ (Scr.card * z.choose 2)
      = ((1 / 2 : ℝ) ^ E_kv) ^ 2 * ((2 : ℝ) ^ W_ov * (2 : ℝ) ^ (Scr.card * z.choose 2)) := by ring
    _ ≤ ((1 / 2 : ℝ) ^ E_kv) ^ 2 * (2 : ℝ) ^ E_kv :=
        mul_le_mul_of_nonneg_left hpow_le (by positivity)
    _ = (1 / 2 : ℝ) ^ E_kv := by
        rw [sq, mul_assoc, one_div, inv_pow, inv_mul_cancel₀ h2E_ne, mul_one]

private theorem similarRange_fixed_n_of_relPair_v13
    {n M m : ℕ} {c₀ : ℝ}
    (hn4 : 4 ≤ n) (hM : 1 ≤ M) (hm : m ≤ 1) (hc₀ : c₀ ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hL3 : (3 : ℝ) ≤ Real.log (n : ℝ))
    (hPh : logOrder n ≤ (phaseNat n : ℝ) ∧ (phaseNat n : ℝ) ≤ 4 * logOrder n)
    (halpha_n : 6 * M + 12 ≤ phaseNat n)
    {RelPair : VertexPartition n → VertexPartition n → Prop}
    (hRel_spec : ∀ Q Q' : VertexPartition n, RelPair Q Q' →
      ((∀ D ∈ Q.parts,
          (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card ≤ 2 ∨
            D.card ≤ (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card + 2 * (phaseNat n - D.card) + 1) ∧
        (∀ D' ∈ Q'.parts,
          (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card ≤ 2 ∨
            D'.card ≤ (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card + 2 * (phaseNat n - D'.card) + 1)) ∧
      ((∀ D ∈ Q.parts, (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 →
          ∃ D' ∈ Q'.parts, (D ∩ D').card = D.card - 1) ∧
        (∀ D' ∈ Q'.parts, (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 →
          ∃ D ∈ Q.parts, (D' ∩ D).card = D'.card - 1)) ∧
      ((Q.parts.filter fun D ↦
          (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 ∧
            ∃ D' ∈ Q'.parts, D'.card - 1 ≤ (D ∩ D').card).card ≤ Nat.floor ((Real.log (n : ℝ)) ^ 3) ∧
        (Q'.parts.filter fun D' ↦
          (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 ∧
            ∃ D ∈ Q.parts, D.card - 1 ≤ (D' ∩ D).card).card ≤ Nat.floor ((Real.log (n : ℝ)) ^ 3)))
    (kv : Fin M → ℕ) (kp : ColoringProfile (phaseNat n))
    (hMass : selectedVertexMass (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) kv = n)
    (hkp : ∀ idx : Fin (phaseNat n),
      kp idx = ∑ j : Fin M, if phaseNat n - (m + 1 + j.1) = idx.1 + 1 then kv j else 0)
    (hUnm_eq : (profileColoringExpectation n kp).toReal =
      completeUnmarkedFirstMoment (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) kv)
    (hSgn_eq : (signedProfileExpectation n kp).toReal =
      completeSignedFirstMoment (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) kv)
    (S_idx : Finset ℕ) (P : ℕ → VertexPartition n)
    (hP_inj : Set.InjOn P (S_idx : Set ℕ))
    (hP_sh : ∀ i ∈ S_idx, partitionShape (P i) = ColoringProfile.sizes kp) :
    (∑ pq ∈ (S_idx ×ˢ S_idx).filter (fun pq ↦
          RelPair (P pq.1) (P pq.2) ∧
          (((n - selectedVertexMass (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1))
            (fun j : Fin M ↦ (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = phaseNat n - (m + 1 + j.1)).card) : ℕ) : ℝ) <
            (n : ℝ) ^ (1 - c₀))),
        (randomGraphMeasure n).real
          (partitionColoringEvent (P pq.1) ∩ partitionColoringEvent (P pq.2))) ≤
      completeUnmarkedFirstMoment (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) kv *
        Real.exp (12 * (Real.log (n : ℝ)) ^ 5) *
        ∑ s ∈ Finset.range (selectedBlockCount kv + 1),
          ((selectedBlockCount kv : ℝ) * (n : ℝ) ^ ((1 - c₀) * ((phaseNat n - (m + 1) : ℕ) : ℝ)) *
            (2 : ℝ) ^ (-((phaseNat n - (3 * M + 4)).choose 2 : ℝ))) ^ s ∧
    (∑ pq ∈ (S_idx ×ˢ S_idx).filter (fun pq ↦
          RelPair (P pq.1) (P pq.2) ∧
          (((n - selectedVertexMass (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1))
            (fun j : Fin M ↦ (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = phaseNat n - (m + 1 + j.1)).card) : ℕ) : ℝ) <
            (n : ℝ) ^ (1 - c₀))),
        (randomGraphMeasure n).real
          (partitionCocoloringEvent (P pq.1) ∩ partitionCocoloringEvent (P pq.2))) ≤
      completeSignedFirstMoment (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) kv *
        (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((phaseNat n - (M + 1) : ℕ) : ℝ)) *
        Real.exp (12 * (Real.log (n : ℝ)) ^ 5) *
        ∑ s ∈ Finset.range (selectedBlockCount kv + 1),
          ((selectedBlockCount kv : ℝ) * (n : ℝ) ^ ((1 - c₀) * ((phaseNat n - (m + 1) : ℕ) : ℝ)) *
            (2 : ℝ) ^ (-((phaseNat n - (3 * M + 4)).choose 2 : ℝ))) ^ s := by
  let α : ℕ := phaseNat n
  let u : Fin M → ℕ := fun j ↦ α - (m + 1 + j.1)
  let a_max : ℕ := α - (m + 1)
  let z : ℕ := α - (3 * M + 4)
  let k : ℕ := selectedBlockCount kv
  set PairSim : Finset (ℕ × ℕ) :=
    (S_idx ×ˢ S_idx).filter fun pq ↦
      RelPair (P pq.1) (P pq.2) ∧
      (((n - selectedVertexMass u
        (fun j : Fin M ↦ (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = u j).card) : ℕ) : ℝ) <
        (n : ℝ) ^ (1 - c₀))
  set B : ℕ := Nat.floor ((Real.log (n : ℝ)) ^ 3)
  set L : ℝ := Real.log (n : ℝ)
  have hL_pos : 0 < L := by dsimp [L]; linarith only [hL3]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have h1mc₀_pos : 0 < 1 - c₀ := by linarith only [hc₀.2]
  have h1mc₀_le1 : 1 - c₀ ≤ 1 := by linarith only [hc₀.1]
  have halpha_m : m + M + 2 ≤ phaseNat n := by omega
  obtain ⟨_, hu_bds, hpart_eq, _, _, hP_all⟩ :=
    windowProfile_part_sizes_and_counts_v13 halpha_m hMass hkp
  set u_minus : ℕ := α - (m + M)
  have hk_le_n : k ≤ n := by
    dsimp [k]; rw [← hMass]; unfold selectedBlockCount selectedVertexMass
    exact Finset.sum_le_sum fun j _ ↦ by
      have h2u := (hu_bds j).1; exact Nat.le_mul_of_pos_left _ (by omega)
  have hprefac_le :
      ((2 * B + 1 : ℕ) : ℝ) * (n : ℝ) ^ (2 * B) *
        ((n : ℝ) ^ (1 - c₀)) ^ (2 * B * α) ≤ Real.exp (12 * L ^ 5) := by
    have hB_le : (B : ℝ) ≤ L ^ 3 := Nat.floor_le (by positivity)
    have h2B1 : ((2 * B + 1 : ℕ) : ℝ) ≤ Real.exp (L ^ 5) := by
      have h1 : ((2 * B + 1 : ℕ) : ℝ) ≤ 3 * L ^ 3 := by
        have hL3_ge1 : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ (by dsimp [L]; linarith only [hL3])
        push_cast; linarith only [hB_le, hL3_ge1]
      have h2 : 3 * L ^ 3 ≤ L ^ 5 := by
        have h3_L2 : (3 : ℝ) ≤ L ^ 2 := by
          have : (3 : ℝ) ≤ L := hL3
          nlinarith only [this]
        calc 3 * L ^ 3 ≤ L ^ 2 * L ^ 3 := mul_le_mul_of_nonneg_right h3_L2 (by positivity)
          _ = L ^ 5 := by ring
      exact (h1.trans h2).trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp (L ^ 5)))
    have hn_exp : (n : ℝ) = Real.exp L := (Real.exp_log hn_pos).symm
    have hn_2B : (n : ℝ) ^ (2 * B) ≤ Real.exp (2 * L ^ 5) := by
      rw [hn_exp, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hL_le_L2 : L ≤ L ^ 2 := by nlinarith only [hL3]
      calc ((2 * B : ℕ) : ℝ) * L = 2 * (B : ℝ) * L := by push_cast; ring
        _ ≤ 2 * L ^ 3 * L ^ 2 := mul_le_mul (by linarith only [hB_le]) hL_le_L2 hL_pos.le (by positivity)
        _ = 2 * L ^ 5 := by ring
    have hn_c0 : ((n : ℝ) ^ (1 - c₀)) ^ (2 * B * α) ≤ Real.exp (8 * L ^ 5) := by
      have hr : (n : ℝ) ^ (1 - c₀) ≤ Real.exp L := by
        rw [Real.rpow_def_of_pos hn_pos]; apply Real.exp_le_exp.mpr
        dsimp [L]; exact mul_le_of_le_one_right hL_pos.le h1mc₀_le1
      refine (pow_le_pow_left₀ (by positivity) hr _).trans ?_
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have ha_4L : (α : ℝ) ≤ 4 * L := hPh.2
      calc ((2 * B * α : ℕ) : ℝ) * L = 2 * (B : ℝ) * (α : ℝ) * L := by push_cast; ring
        _ ≤ 2 * L ^ 3 * (4 * L) * L :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (by linarith only [hB_le]) ha_4L (Nat.cast_nonneg _) (by positivity)) hL_pos.le
        _ = 8 * L ^ 5 := by ring
    calc ((2 * B + 1 : ℕ) : ℝ) * (n : ℝ) ^ (2 * B) * ((n : ℝ) ^ (1 - c₀)) ^ (2 * B * α)
        ≤ Real.exp (L ^ 5) * Real.exp (2 * L ^ 5) * Real.exp (8 * L ^ 5) :=
          mul_le_mul (mul_le_mul h2B1 hn_2B (by positivity) (by positivity)) hn_c0
            (by positivity) (by positivity)
      _ = Real.exp (11 * L ^ 5) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (12 * L ^ 5) := Real.exp_le_exp.mpr (by linarith [pow_pos hL_pos 5])
  let ScrOf : ℕ → ℕ → Finset (Finset (Fin n)) :=
    fun i j ↦ ((P i).parts \ (P j).parts).filter fun D ↦
      D.card ≤ ((P j).parts.filter fun E ↦ (D ∩ E).Nonempty).card + 2 * (α - D.card) + 1
  let ExcOf : ℕ → ℕ → Finset (Finset (Fin n)) :=
    fun i j ↦ ((P i).parts \ (P j).parts).filter fun D ↦
      ¬ (D.card ≤ ((P j).parts.filter fun E ↦ (D ∩ E).Nonempty).card + 2 * (α - D.card) + 1)
  have hper_P : ∀ i ∈ S_idx,
      (∑ j ∈ S_idx.filter (fun j ↦ (i, j) ∈ PairSim),
          (randomGraphMeasure n).real (partitionColoringEvent (P i) ∩ partitionColoringEvent (P j))) ≤
        (randomGraphMeasure n).real (partitionColoringEvent (P i)) *
          Real.exp (12 * L ^ 5) *
          ∑ s ∈ Finset.range (k + 1),
            ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ)) *
              (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s := by
    intro i hi
    let QSim := S_idx.filter (fun j ↦ (i, j) ∈ PairSim)
    have hP_sz : ∀ D ∈ (P i).parts, u_minus ≤ D.card ∧ D.card ≤ a_max := by
      intro D hD; obtain ⟨j_u, hj_u⟩ := (hP_all (P i) (hP_sh i hi)).2.2.2 D hD
      rw [hj_u]; exact ⟨(hu_bds j_u).2.1, (hu_bds j_u).2.2⟩
    have hmaps_s : ∀ j ∈ QSim, (ScrOf i j).card ∈ Finset.range (k + 1) := by
      intro j _
      rw [Finset.mem_range]
      have hle : (ScrOf i j).card ≤ (P i).parts.card :=
        Finset.card_le_card ((Finset.filter_subset _ _).trans Finset.sdiff_subset)
      rw [(hP_all (P i) (hP_sh i hi)).1] at hle
      dsimp [k]; omega
    have hslice_s : ∀ s ∈ Finset.range (k + 1),
        (∑ j ∈ QSim.filter (fun j ↦ (ScrOf i j).card = s),
            (randomGraphMeasure n).real (partitionColoringEvent (P i) ∩ partitionColoringEvent (P j))) ≤
          (randomGraphMeasure n).real (partitionColoringEvent (P i)) *
            Real.exp (12 * L ^ 5) *
            ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ)) *
              (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s := by
      intro s _
      let Q_s := QSim.filter (fun j ↦ (ScrOf i j).card = s)
      have hpt_prob : ∀ j ∈ Q_s,
          (randomGraphMeasure n).real (partitionColoringEvent (P i) ∩ partitionColoringEvent (P j)) ≤
            (randomGraphMeasure n).real (partitionColoringEvent (P i)) *
              ((2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s := by
        intro j hj
        obtain ⟨hjSim, hs_eq⟩ := Finset.mem_filter.mp hj
        have hjS : j ∈ S_idx := (Finset.mem_filter.mp hjSim).1
        rw [← hs_eq]
        refine coloring_inter_le_of_scrambled_count_v13 halpha_m hMass hkp
          (P i) (P j) (hP_sh i hi) (hP_sh j hjS)
          ((Finset.filter_subset _ _).trans Finset.sdiff_subset) ?_
        intro D hDS
        have hDP : D ∈ (P i).parts := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hDS).1).1
        have hscr := (Finset.mem_filter.mp hDS).2
        have hD_lo := (hP_sz D hDP).1
        dsimp [u_minus, z] at hD_lo ⊢
        omega
      let SE_dom := (P i).parts.powersetCard s ×ˢ ((P i).parts.powerset.filter fun E ↦ E.card ≤ 2 * B)
      let seOf : ℕ → Finset (Finset (Fin n)) × Finset (Finset (Fin n)) :=
        fun j ↦ (ScrOf i j, ExcOf i j)
      have hmaps_se : ∀ j ∈ Q_s, seOf j ∈ SE_dom := by
        intro j hj
        obtain ⟨hjSim, hs_eq⟩ := Finset.mem_filter.mp hj
        obtain ⟨hjS, hPQ⟩ := Finset.mem_filter.mp hjSim
        have hRel := hRel_spec (P i) (P j) (Finset.mem_filter.mp hPQ).2.1
        have hQ_sz : ∀ D ∈ (P j).parts, u_minus ≤ D.card ∧ D.card ≤ a_max := by
          intro D hD; obtain ⟨j_u, hj_u⟩ := (hP_all (P j) (hP_sh j hjS)).2.2.2 D hD
          rw [hj_u]; exact ⟨(hu_bds j_u).2.1, (hu_bds j_u).2.2⟩
        obtain ⟨_, ⟨hExc_c, _⟩, _, _⟩ := relevantPair_part_trichotomy_and_overlap_gap (P i) (P j)
          (u_minus := u_minus) (a := a_max) (α := α) (M := M) (B := B)
          hM (by dsimp [u_minus, α]; omega) (by dsimp [a_max, u_minus, α]; omega)
          (by dsimp [a_max]; omega) (by dsimp [u_minus, α]; omega)
          hP_sz hQ_sz hRel.1 hRel.2.1 hRel.2.2
        exact Finset.mem_product.mpr
          ⟨Finset.mem_powersetCard.mpr ⟨(Finset.filter_subset _ _).trans Finset.sdiff_subset, hs_eq⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
              ((Finset.filter_subset _ _).trans Finset.sdiff_subset), hExc_c⟩⟩
      have hfib_se : ∀ se ∈ SE_dom,
          ((Q_s.filter fun j ↦ seOf j = se).card : ℝ) ≤
            (((n : ℝ) ^ (1 - c₀)) ^ (2 * B * α)) * ((n : ℝ) ^ ((1 - c₀) * (a_max : ℝ))) ^ s := by
        intro se hse
        let Fib := Q_s.filter fun j ↦ seOf j = se
        by_cases hne : Fib.Nonempty
        · obtain ⟨j₀, hj₀⟩ := hne
          obtain ⟨hj₀_s, hse₀⟩ := Finset.mem_filter.mp hj₀
          have hj₀_sim : j₀ ∈ QSim := (Finset.mem_filter.mp hj₀_s).1
          obtain ⟨hj₀S, hPQ₀⟩ := Finset.mem_filter.mp hj₀_sim
          have hSim₀ := (Finset.mem_filter.mp hPQ₀).2.2
          obtain ⟨hs_mem, he_mem⟩ := Finset.mem_product.mp hse
          have hS_sub : se.1 ⊆ (P i).parts ∧ se.1.card = s := Finset.mem_powersetCard.mp hs_mem
          have hE_sub : se.2 ⊆ (P i).parts ∧ se.2.card ≤ 2 * B := by
            obtain ⟨hp, hc⟩ := Finset.mem_filter.mp he_mem
            exact ⟨Finset.mem_powerset.mp hp, hc⟩
          set U₀ : Finset (Finset (Fin n)) := se.1 ∪ se.2
          set Ident₀ := (P i).parts \ U₀
          set W₀ := Finset.univ \ Ident₀.biUnion id
          set t₀ := U₀.card
          have hId_eq : ∀ j ∈ Fib, (P i).parts ∩ (P j).parts = Ident₀ := by
            intro j hj
            have hseQ := (Finset.mem_filter.mp hj).2
            have hun_Q : U₀ = (P i).parts \ (P j).parts := by
              dsimp only [U₀]
              rw [← congrArg Prod.fst hseQ, ← congrArg Prod.snd hseQ]
              exact Finset.filter_union_filter_not_eq _ _
            dsimp only [Ident₀]
            rw [hun_Q]; ext D; simp only [Finset.mem_inter, Finset.mem_sdiff]; tauto
          have hst₀ := subprofile_inter_and_sdiff_stats_v13 halpha_m hMass hkp
            (P i) (P j₀) (hP_sh i hi) (hP_sh j₀ hj₀S)
          have hW₀_lt : (W₀.card : ℝ) ≤ (n : ℝ) ^ (1 - c₀) := by
            have hW₀_eq : W₀ = Finset.univ \ ((P i).parts ∩ (P j₀).parts).biUnion id := by
              dsimp [W₀]; rw [hId_eq j₀ hj₀]
            have hc : (Finset.univ \ ((P i).parts ∩ (P j₀).parts).biUnion id).card =
                n - selectedVertexMass u
                  (fun j_u : Fin M ↦ (((P i).parts ∩ (P j₀).parts).filter fun D ↦ D.card = u j_u).card) :=
              hst₀.2.2.2.2.2.2.2.2.2
            rw [hW₀_eq, hc]; exact hSim₀.le
          have hun₀ : U₀ = (P i).parts \ (P j₀).parts := by
            dsimp only [U₀]
            rw [← congrArg Prod.fst hse₀, ← congrArg Prod.snd hse₀]
            exact Finset.filter_union_filter_not_eq _ _
          have hbi₀ : U₀.biUnion id = W₀ := by
            rw [hun₀]
            have hb : ((P i).parts \ (P j₀).parts).biUnion id =
                Finset.univ \ ((P i).parts ∩ (P j₀).parts).biUnion id := hst₀.2.2.2.2.2.2.2.1
            rwa [hId_eq j₀ hj₀] at hb
          have hW₀_ub : W₀.card ≤ s * a_max + 2 * B * α := by
            rw [← hbi₀]
            have h1 : (U₀.biUnion id).card ≤ ∑ D ∈ U₀, D.card := Finset.card_biUnion_le
            have h2 : (∑ D ∈ U₀, D.card) + (∑ D ∈ se.1 ∩ se.2, D.card) =
                (∑ D ∈ se.1, D.card) + (∑ D ∈ se.2, D.card) := by
              dsimp only [U₀]; exact Finset.sum_union_inter
            have h3 : ∑ D ∈ se.1, D.card ≤ s * a_max := by
              calc ∑ D ∈ se.1, D.card ≤ ∑ _D ∈ se.1, a_max :=
                    Finset.sum_le_sum fun D hD ↦ (hP_sz D (hS_sub.1 hD)).2
                _ = s * a_max := by simp [hS_sub.2]
            have h4 : ∑ D ∈ se.2, D.card ≤ 2 * B * α := by
              calc ∑ D ∈ se.2, D.card ≤ ∑ _D ∈ se.2, α :=
                    Finset.sum_le_sum fun D hD ↦ (hP_sz D (hE_sub.1 hD)).2.trans (by dsimp [a_max]; omega)
                _ = se.2.card * α := by simp
                _ ≤ 2 * B * α := Nat.mul_le_mul_right α hE_sub.2
            omega
          have ht₀_le_W₀ : t₀ ≤ W₀.card := by
            have hdisj₀ : (U₀ : Set (Finset (Fin n))).PairwiseDisjoint id := by
              intro A hA C hC hne
              have hA' : A ∈ (P i).parts \ (P j₀).parts := hun₀ ▸ Finset.mem_coe.mp hA
              have hC' : C ∈ (P i).parts \ (P j₀).parts := hun₀ ▸ Finset.mem_coe.mp hC
              exact (P i).disjoint (Finset.mem_sdiff.mp hA').1 (Finset.mem_sdiff.mp hC').1 hne
            rw [← hbi₀, Finset.card_biUnion hdisj₀]
            calc t₀ = ∑ _D ∈ U₀, 1 := by simp [t₀]
              _ ≤ ∑ D ∈ U₀, D.card := Finset.sum_le_sum fun D hD ↦ by
                  have hD' : D ∈ (P i).parts \ (P j₀).parts := hun₀ ▸ hD
                  have := (hP_sz D (Finset.mem_sdiff.mp hD').1).1; dsimp [u_minus] at this; omega
          let resOf : ℕ → Finset (Finset (Fin n)) := fun j ↦ (P j).parts \ (P i).parts
          let ResFam := Fib.image resOf
          have hres_inj : ∀ j₁ ∈ Fib, ∀ j₂ ∈ Fib, resOf j₁ = resOf j₂ → j₁ = j₂ := by
            intro j₁ h₁ j₂ h₂ heq
            have hj₁S : j₁ ∈ S_idx := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h₁).1).1).1
            have hj₂S : j₂ ∈ S_idx := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h₂).1).1).1
            have h1 : (P j₁).parts = Ident₀ ∪ resOf j₁ := by
              rw [← hId_eq j₁ h₁]; ext D; simp only [resOf, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
            have h2 : (P j₂).parts = Ident₀ ∪ resOf j₂ := by
              rw [← hId_eq j₂ h₂]; ext D; simp only [resOf, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
            exact hP_inj hj₁S hj₂S (Finpartition.ext (h1.trans ((congrArg (Ident₀ ∪ ·) heq).trans h2.symm)))
          have hFib_eq : Fib.card = ResFam.card := (Finset.card_image_of_injOn hres_inj).symm
          have hRes_props : ∀ R ∈ ResFam,
              (R : Set (Finset (Fin n))).PairwiseDisjoint id ∧ R.biUnion id = W₀ ∧ R.card = t₀ := by
            intro R hR
            rcases Finset.mem_image.mp hR with ⟨j, hj, rfl⟩
            have hjS : j ∈ S_idx := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1).1
            have hstQ := subprofile_inter_and_sdiff_stats_v13 halpha_m hMass hkp
              (P i) (P j) (hP_sh i hi) (hP_sh j hjS)
            have hunQ : U₀ = (P i).parts \ (P j).parts := by
              dsimp only [U₀]
              have hseQ := (Finset.mem_filter.mp hj).2
              rw [← congrArg Prod.fst hseQ, ← congrArg Prod.snd hseQ]
              exact Finset.filter_union_filter_not_eq _ _
            refine ⟨fun A hA C hC hne ↦ (P j).disjoint (Finset.mem_sdiff.mp hA).1 (Finset.mem_sdiff.mp hC).1 hne,
              ?_, ?_⟩
            · have hb : ((P j).parts \ (P i).parts).biUnion id =
                  Finset.univ \ ((P i).parts ∩ (P j).parts).biUnion id := hstQ.2.2.2.2.2.2.2.2.1
              rwa [hId_eq j hj] at hb
            · dsimp [resOf, t₀]
              exact hstQ.2.2.2.2.2.2.1.trans (by rw [hunQ]; exact hstQ.2.2.2.2.2.1.symm)
          have hrc_le := resPartition_card_le_pow_v13 W₀ ResFam hRes_props
          have h1_nc : (1 : ℝ) ≤ (n : ℝ) ^ (1 - c₀) :=
            Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) h1mc₀_pos.le
          have hmax_le : ((max 1 t₀ : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 - c₀) := by
            rw [Nat.cast_max, Nat.cast_one]
            exact max_le h1_nc ((Nat.cast_le.mpr ht₀_le_W₀).trans hW₀_lt)
          rw [hFib_eq]
          calc (ResFam.card : ℝ)
              ≤ ((max 1 t₀ : ℕ) : ℝ) ^ W₀.card := hrc_le
            _ ≤ ((n : ℝ) ^ (1 - c₀)) ^ W₀.card := pow_le_pow_left₀ (by positivity) hmax_le _
            _ ≤ ((n : ℝ) ^ (1 - c₀)) ^ (s * a_max + 2 * B * α) := pow_le_pow_right₀ h1_nc hW₀_ub
            _ = (((n : ℝ) ^ (1 - c₀)) ^ (2 * B * α)) * ((n : ℝ) ^ ((1 - c₀) * (a_max : ℝ))) ^ s := by
                rw [pow_add, mul_comm _ (((n : ℝ) ^ (1 - c₀)) ^ (2 * B * α))]
                congr 1
                rw [mul_comm s a_max, pow_mul]
                congr 1
                rw [← Real.rpow_natCast ((n : ℝ) ^ (1 - c₀)) a_max, ← Real.rpow_mul hn_pos.le]
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          dsimp [Fib] at hne
          rw [hne, Finset.card_empty, Nat.cast_zero]; positivity
      have hSE_card :
          (SE_dom.card : ℝ) ≤ ((2 * B + 1 : ℕ) : ℝ) * (n : ℝ) ^ (2 * B) * (k : ℝ) ^ s := by
        dsimp [SE_dom]
        rw [Finset.card_product, Nat.cast_mul, Finset.card_powersetCard, (hP_all (P i) (hP_sh i hi)).1]
        have hks : ((k.choose s : ℕ) : ℝ) ≤ (k : ℝ) ^ s := by
          have h := (Nat.le_mul_of_pos_left (k.choose s) (Nat.factorial_pos s)).trans
            (nat_factorial_mul_choose_le_pow_v13 k s)
          exact_mod_cast h
        have hExc_dom_le : (((P i).parts.powerset.filter fun E ↦ E.card ≤ 2 * B).card : ℝ) ≤
            ((2 * B + 1 : ℕ) : ℝ) * (n : ℝ) ^ (2 * B) := by
          have hbi : ((P i).parts.powerset.filter fun E ↦ E.card ≤ 2 * B) =
              (Finset.range (2 * B + 1)).biUnion (fun r ↦ (P i).parts.powersetCard r) := by
            ext E; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
              Finset.mem_range, Finset.mem_powersetCard]
            exact ⟨fun ⟨h1, h2⟩ ↦ ⟨E.card, by omega, h1, rfl⟩,
              fun ⟨r, hr, h1, h2⟩ ↦ ⟨h1, by omega⟩⟩
          have h1 : ((P i).parts.powerset.filter fun E ↦ E.card ≤ 2 * B).card ≤
              ∑ r ∈ Finset.range (2 * B + 1), n ^ (2 * B) := by
            rw [hbi]
            refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun r hr ↦ ?_)
            rw [Finset.card_powersetCard, (hP_all (P i) (hP_sh i hi)).1]
            have hr_le : r ≤ 2 * B := by have := Finset.mem_range.mp hr; omega
            calc k.choose r ≤ k ^ r :=
                  (Nat.le_mul_of_pos_left _ (Nat.factorial_pos r)).trans
                    (nat_factorial_mul_choose_le_pow_v13 k r)
              _ ≤ n ^ r := Nat.pow_le_pow_left hk_le_n r
              _ ≤ n ^ (2 * B) := Nat.pow_le_pow_right (by omega) hr_le
          have h2 : ∑ _r ∈ Finset.range (2 * B + 1), n ^ (2 * B) = (2 * B + 1) * n ^ (2 * B) := by simp
          exact_mod_cast (h1.trans_eq h2)
        exact (mul_le_mul hks hExc_dom_le (Nat.cast_nonneg _) (by positivity)).trans_eq (by ring)
      have hQs_card :
          (Q_s.card : ℝ) ≤ Real.exp (12 * L ^ 5) *
            ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ))) ^ s := by
        have hfib_sum : Q_s.card = ∑ se ∈ SE_dom, (Q_s.filter fun j ↦ seOf j = se).card :=
          (Finset.card_eq_sum_card_fiberwise hmaps_se)
        have hR : (Q_s.card : ℝ) = ∑ se ∈ SE_dom, ((Q_s.filter fun j ↦ seOf j = se).card : ℝ) := by
          exact_mod_cast hfib_sum
        rw [hR]
        calc ∑ se ∈ SE_dom, ((Q_s.filter fun j ↦ seOf j = se).card : ℝ)
            ≤ ∑ _se ∈ SE_dom,
                (((n : ℝ) ^ (1 - c₀)) ^ (2 * B * α)) * ((n : ℝ) ^ ((1 - c₀) * (a_max : ℝ))) ^ s :=
              Finset.sum_le_sum hfib_se
          _ = (SE_dom.card : ℝ) *
                ((((n : ℝ) ^ (1 - c₀)) ^ (2 * B * α)) * ((n : ℝ) ^ ((1 - c₀) * (a_max : ℝ))) ^ s) := by
              simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (((2 * B + 1 : ℕ) : ℝ) * (n : ℝ) ^ (2 * B) * (k : ℝ) ^ s) *
                ((((n : ℝ) ^ (1 - c₀)) ^ (2 * B * α)) * ((n : ℝ) ^ ((1 - c₀) * (a_max : ℝ))) ^ s) :=
              mul_le_mul_of_nonneg_right hSE_card (by positivity)
          _ = (((2 * B + 1 : ℕ) : ℝ) * (n : ℝ) ^ (2 * B) * ((n : ℝ) ^ (1 - c₀)) ^ (2 * B * α)) *
                ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ))) ^ s := by
              rw [mul_pow]; ring
          _ ≤ Real.exp (12 * L ^ 5) * ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ))) ^ s :=
              mul_le_mul_of_nonneg_right hprefac_le (by positivity)
      calc ∑ j ∈ Q_s, (randomGraphMeasure n).real (partitionColoringEvent (P i) ∩ partitionColoringEvent (P j))
          ≤ ∑ _j ∈ Q_s, (randomGraphMeasure n).real (partitionColoringEvent (P i)) *
              ((2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s := Finset.sum_le_sum hpt_prob
        _ = (Q_s.card : ℝ) * ((randomGraphMeasure n).real (partitionColoringEvent (P i)) *
              ((2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s) := by simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Real.exp (12 * L ^ 5) * ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ))) ^ s) *
              ((randomGraphMeasure n).real (partitionColoringEvent (P i)) *
                ((2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s) :=
            mul_le_mul_of_nonneg_right hQs_card
              (mul_nonneg measureReal_nonneg (by positivity))
        _ = (randomGraphMeasure n).real (partitionColoringEvent (P i)) * Real.exp (12 * L ^ 5) *
              ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ)) *
                (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s := by
            rw [mul_pow ((k : ℝ) * _) ((2 : ℝ) ^ _)]; ring
    rw [← Finset.sum_fiberwise_of_maps_to hmaps_s, Finset.mul_sum]
    exact Finset.sum_le_sum hslice_s
  have hsum_P_unm :
      (∑ i ∈ S_idx, (randomGraphMeasure n).real (partitionColoringEvent (P i))) ≤
        completeUnmarkedFirstMoment u kv := by
    have hcard_le : S_idx.card ≤ Fintype.card (ProfilePartition n kp) := by
      rw [← Fintype.card_coe]
      refine Fintype.card_le_of_injective
        (fun i : ↥S_idx ↦ (⟨P i.1, hP_sh i.1 i.2⟩ : ProfilePartition n kp)) ?_
      intro i₁ i₂ heq
      exact Subtype.ext (hP_inj i₁.2 i₂.2 (congrArg Subtype.val heq))
    have hpt : ∀ i ∈ S_idx, (randomGraphMeasure n).real (partitionColoringEvent (P i)) =
        ((1 / 2 : ℝ≥0∞) ^ kp.forbiddenEdges).toReal := by
      intro i hi
      let Pi : ProfilePartition n kp := ⟨P i, hP_sh i hi⟩
      rw [Measure.real, show P i = Pi.1 from rfl, randomGraphMeasure_partitionColoringEvent Pi]
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul]
    have h1 : (Fintype.card (ProfilePartition n kp) : ℝ) *
        ((1 / 2 : ℝ≥0∞) ^ kp.forbiddenEdges).toReal = completeUnmarkedFirstMoment u kv := by
      rw [← hUnm_eq, profileColoringExpectation_eq_card_mul, Nat.card_eq_fintype_card,
        ENNReal.toReal_mul, ENNReal.toReal_natCast]
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le) ENNReal.toReal_nonneg).trans_eq h1
  have hunm_sim :
      (∑ pq ∈ PairSim,
          (randomGraphMeasure n).real (partitionColoringEvent (P pq.1) ∩ partitionColoringEvent (P pq.2))) ≤
        completeUnmarkedFirstMoment u kv * Real.exp (12 * L ^ 5) *
          ∑ s ∈ Finset.range (k + 1),
            ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ)) *
              (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s := by
    have hsplit_P :
        (∑ pq ∈ PairSim,
            (randomGraphMeasure n).real (partitionColoringEvent (P pq.1) ∩ partitionColoringEvent (P pq.2))) =
          ∑ i ∈ S_idx,
            ∑ j ∈ S_idx.filter (fun j ↦ (i, j) ∈ PairSim),
              (randomGraphMeasure n).real (partitionColoringEvent (P i) ∩ partitionColoringEvent (P j)) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst)
        (fun pq hpq ↦ (Finset.mem_product.mp (Finset.mem_filter.mp hpq).1).1)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      refine Finset.sum_bij (fun pq _ ↦ pq.2) ?_ ?_ ?_ (fun pq hpq ↦ ?_)
      · intro pq hpq
        obtain ⟨hpqS, rfl⟩ := Finset.mem_filter.mp hpq
        exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hpqS).1).2, hpqS⟩
      · intro pq₁ h₁ pq₂ h₂ h2
        exact Prod.ext ((Finset.mem_filter.mp h₁).2.trans (Finset.mem_filter.mp h₂).2.symm) h2
      · intro j hj
        exact ⟨(i, j), Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).2, rfl⟩, rfl⟩
      · rw [(Finset.mem_filter.mp hpq).2]
    rw [hsplit_P]
    calc ∑ i ∈ S_idx, _
        ≤ ∑ i ∈ S_idx,
            (randomGraphMeasure n).real (partitionColoringEvent (P i)) *
              Real.exp (12 * L ^ 5) *
              ∑ s ∈ Finset.range (k + 1),
                ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ)) *
                  (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s :=
          Finset.sum_le_sum hper_P
      _ = (∑ i ∈ S_idx, (randomGraphMeasure n).real (partitionColoringEvent (P i))) *
            Real.exp (12 * L ^ 5) *
            ∑ s ∈ Finset.range (k + 1),
              ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ)) *
                (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ ≤ _ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hsum_P_unm (Real.exp_pos _).le)
            (Finset.sum_nonneg fun s _ ↦ pow_nonneg (by positivity) s)
  refine ⟨hunm_sim, ?_⟩
  have hpq_co : ∀ pq ∈ PairSim,
      (randomGraphMeasure n).real (partitionCocoloringEvent (P pq.1) ∩ partitionCocoloringEvent (P pq.2)) ≤
        ((2 : ℝ) ^ k * (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((α - (M + 1) : ℕ) : ℝ))) *
          (randomGraphMeasure n).real (partitionColoringEvent (P pq.1) ∩ partitionColoringEvent (P pq.2)) := by
    intro pq hpq
    obtain ⟨hpq_prod, _, hSim_pq⟩ := Finset.mem_filter.mp hpq
    obtain ⟨hpq1, hpq2⟩ := Finset.mem_product.mp hpq_prod
    have hst := subprofile_inter_and_sdiff_stats_v13 halpha_m hMass hkp
      (P pq.1) (P pq.2) (hP_sh pq.1 hpq1) (hP_sh pq.2 hpq2)
    set t_pq := ((P pq.2).parts \ (P pq.1).parts).card
    have hcard_add : (P pq.1).parts.card + (P pq.2).parts.card - ((P pq.1).parts ∩ (P pq.2).parts).card =
        k + t_pq := by
      have hun : ((P pq.1).parts ∩ (P pq.2).parts) ∪ ((P pq.2).parts \ (P pq.1).parts) = (P pq.2).parts := by
        ext D; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
      have hdisj : Disjoint ((P pq.1).parts ∩ (P pq.2).parts) ((P pq.2).parts \ (P pq.1).parts) := by
        rw [Finset.disjoint_left]; intro D h1 h2
        exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).1
      have hcu := Finset.card_union_of_disjoint hdisj
      rw [hun, (hP_all (P pq.2) (hP_sh pq.2 hpq2)).1] at hcu
      rw [(hP_all (P pq.1) (hP_sh pq.1 hpq1)).1, (hP_all (P pq.2) (hP_sh pq.2 hpq2)).1]
      dsimp [k, t_pq] at hcu ⊢; omega
    have ht_ub : (t_pq : ℝ) ≤ (n : ℝ) ^ (1 - c₀) / ((α - (M + 1) : ℕ) : ℝ) := by
      have hu_pos : (0 : ℝ) < ((α - (M + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < α - (M + 1) by dsimp [α]; omega)
      rw [le_div_iff₀ hu_pos]
      have hnat : t_pq * (α - (M + 1)) ≤
          n - selectedVertexMass u
            (fun j : Fin M ↦ (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = u j).card) := by
        have hw : (Finset.univ \ ((P pq.1).parts ∩ (P pq.2).parts).biUnion id).card =
            n - selectedVertexMass u
              (fun j : Fin M ↦ (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = u j).card) :=
          hst.2.2.2.2.2.2.2.2.2
        have hbi : ((P pq.2).parts \ (P pq.1).parts).biUnion id =
            Finset.univ \ ((P pq.1).parts ∩ (P pq.2).parts).biUnion id :=
          hst.2.2.2.2.2.2.2.2.1
        rw [← hw, ← hbi, Finset.card_biUnion
          (fun A hA C hC hne ↦ (P pq.2).disjoint (Finset.mem_sdiff.mp hA).1 (Finset.mem_sdiff.mp hC).1 hne)]
        calc t_pq * (α - (M + 1))
            = ∑ _D ∈ (P pq.2).parts \ (P pq.1).parts, (α - (M + 1)) := by simp [t_pq]
          _ ≤ ∑ D ∈ (P pq.2).parts \ (P pq.1).parts, D.card := Finset.sum_le_sum fun D hD ↦ by
              obtain ⟨j, hj⟩ := (hP_all (P pq.2) (hP_sh pq.2 hpq2)).2.2.2 D (Finset.mem_sdiff.mp hD).1
              rw [hj]; have := (hu_bds j).2.1; omega
      have hnat_R : (t_pq : ℝ) * ((α - (M + 1) : ℕ) : ℝ) ≤
          ((n - selectedVertexMass u
            (fun j : Fin M ↦ (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = u j).card) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      exact hnat_R.trans hSim_pq.le
    have hsh2 : ∀ D ∈ (P pq.1).parts ∩ (P pq.2).parts, 2 ≤ D.card := by
      intro D hD; obtain ⟨j, hj⟩ := (hP_all (P pq.1) (hP_sh pq.1 hpq1)).2.2.2 D (Finset.mem_inter.mp hD).1
      rw [hj]; exact (hu_bds j).1
    have hco := (randomGraphMeasure_partitionCocoloringEvent_inter_le_two_pow_sub_inter
      (P pq.1) (P pq.2) hsh2).2
    rw [hcard_add, pow_add] at hco
    have h2t : (2 : ℝ) ^ t_pq ≤ (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((α - (M + 1) : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two ht_ub
    exact hco.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h2t (by positivity)) measureReal_nonneg)
  have hsgn_rel : (2 : ℝ) ^ k * completeUnmarkedFirstMoment u kv = completeSignedFirstMoment u kv := by
    rw [← hUnm_eq, ← hSgn_eq, signedProfileExpectation_eq, hpart_eq, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  calc ∑ pq ∈ PairSim,
          (randomGraphMeasure n).real (partitionCocoloringEvent (P pq.1) ∩ partitionCocoloringEvent (P pq.2))
      ≤ ∑ pq ∈ PairSim,
          ((2 : ℝ) ^ k * (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((α - (M + 1) : ℕ) : ℝ))) *
            (randomGraphMeasure n).real (partitionColoringEvent (P pq.1) ∩ partitionColoringEvent (P pq.2)) :=
        Finset.sum_le_sum hpq_co
    _ = ((2 : ℝ) ^ k * (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((α - (M + 1) : ℕ) : ℝ))) *
          ∑ pq ∈ PairSim,
            (randomGraphMeasure n).real (partitionColoringEvent (P pq.1) ∩ partitionColoringEvent (P pq.2)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ ((2 : ℝ) ^ k * (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((α - (M + 1) : ℕ) : ℝ))) *
          (completeUnmarkedFirstMoment u kv * Real.exp (12 * L ^ 5) *
            ∑ s ∈ Finset.range (k + 1),
              ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ)) *
                (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s) :=
        mul_le_mul_of_nonneg_left hunm_sim (by positivity)
    _ = ((2 : ℝ) ^ k * completeUnmarkedFirstMoment u kv) *
          (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((α - (M + 1) : ℕ) : ℝ)) *
          Real.exp (12 * L ^ 5) *
          ∑ s ∈ Finset.range (k + 1),
            ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ)) *
              (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s := by ring
    _ = _ := by rw [hsgn_rel]

/-- **Unconditional `G(n, 1/2)` Proposition 7.3 similar-range bound (`main.tex` lines 1118–1131):**
for every `M ≥ 1` and `c₀ ∈ (0, 1/2)`, eventually for all `n`, uniformly over `m ∈ {0, 1}`, any
window profile `kv : Fin M → ℕ` embedded as `kp` with vertex mass `n`, and any injective family
`(P i)_{i ∈ S_idx}` of partitions realizing profile `kp`, the sum of joint coloring (resp.
cocoloring) probabilities over all relevant pairs `(i, j) ∈ Π_rel` in the similar range
`n - m_ν < n^(1 - c₀)` is bounded by `E[X̄_k] exp(12 (log n)⁵) ∑_{s=0}^k (k n^((1-c₀)a) 2^(-binom(z,2)))^s`
(resp. `E[Z_k^mk] 2^(n^(1-c₀)/(α-(M+1))) exp(12 (log n)⁵) ∑_{s=0}^k (...)^s` with
`a := α - (m + 1)` and `z := α - (3M + 4)`). -/
theorem eventually_similarRange_pairSum_le
    {M : ℕ} (hM : 1 ≤ M) {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    ∀ᶠ n : ℕ in atTop,
      let α : ℕ := phaseNat n
      let B : ℕ := Nat.floor ((Real.log (n : ℝ)) ^ 3)
      let RelPair : VertexPartition n → VertexPartition n → Prop := fun Q Q' ↦
        ((∀ D ∈ Q.parts,
            (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card ≤ 2 ∨
              D.card ≤ (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card + 2 * (α - D.card) + 1) ∧
          (∀ D' ∈ Q'.parts,
            (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card ≤ 2 ∨
              D'.card ≤ (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card + 2 * (α - D'.card) + 1)) ∧
        ((∀ D ∈ Q.parts, (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 →
            ∃ D' ∈ Q'.parts, (D ∩ D').card = D.card - 1) ∧
          (∀ D' ∈ Q'.parts, (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 →
            ∃ D ∈ Q.parts, (D' ∩ D).card = D'.card - 1)) ∧
        ((Q.parts.filter fun D ↦
            (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 ∧
              ∃ D' ∈ Q'.parts, D'.card - 1 ≤ (D ∩ D').card).card ≤ B ∧
          (Q'.parts.filter fun D' ↦
            (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 ∧
              ∃ D ∈ Q.parts, D.card - 1 ≤ (D' ∩ D).card).card ≤ B)
      ∀ {m : ℕ}, m ≤ 1 →
        let u : Fin M → ℕ := fun j ↦ α - (m + 1 + j.1)
        let a_max : ℕ := α - (m + 1)
        let z : ℕ := α - (3 * M + 4)
        ∀ (kv : Fin M → ℕ) (kp : ColoringProfile α),
          selectedVertexMass u kv = n →
          (∀ idx : Fin α, kp idx = ∑ j : Fin M, if u j = idx.1 + 1 then kv j else 0) →
          (profileColoringExpectation n kp).toReal = completeUnmarkedFirstMoment u kv →
          (signedProfileExpectation n kp).toReal = completeSignedFirstMoment u kv →
          ∀ (S_idx : Finset ℕ) (P : ℕ → VertexPartition n),
            Set.InjOn P (S_idx : Set ℕ) →
            (∀ i ∈ S_idx, partitionShape (P i) = ColoringProfile.sizes kp) →
            let k : ℕ := selectedBlockCount kv
            let PairSim : Finset (ℕ × ℕ) :=
              (S_idx ×ˢ S_idx).filter fun pq ↦
                RelPair (P pq.1) (P pq.2) ∧
                (((n - selectedVertexMass u
                  (fun j : Fin M ↦ (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = u j).card) : ℕ) : ℝ) <
                  (n : ℝ) ^ (1 - c₀))
            (∑ pq ∈ PairSim,
                (randomGraphMeasure n).real
                  (partitionColoringEvent (P pq.1) ∩ partitionColoringEvent (P pq.2))) ≤
              completeUnmarkedFirstMoment u kv *
                Real.exp (12 * (Real.log (n : ℝ)) ^ 5) *
                ∑ s ∈ Finset.range (k + 1),
                  ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ)) *
                    (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s ∧
            (∑ pq ∈ PairSim,
                (randomGraphMeasure n).real
                  (partitionCocoloringEvent (P pq.1) ∩ partitionCocoloringEvent (P pq.2))) ≤
              completeSignedFirstMoment u kv *
                (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((α - (M + 1) : ℕ) : ℝ)) *
                Real.exp (12 * (Real.log (n : ℝ)) ^ 5) *
                ∑ s ∈ Finset.range (k + 1),
                  ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ)) *
                    (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s := by
  have halpha_ev : ∀ᶠ n : ℕ in atTop, 6 * M + 12 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (((6 * M + 12 : ℕ) : ℝ)),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  filter_upwards [eventually_ge_atTop 4,
    tendsto_logOrder_atTop.eventually_ge_atTop 3,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    halpha_ev] with n hn4 hL3 hPh halpha_n
  intro α B RelPair m hm u a_max z kv kp hMass hkp hUnm_eq hSgn_eq S_idx P hP_inj hP_sh k PairSim
  dsimp [logOrder] at hL3
  have h := similarRange_fixed_n_of_relPair_v13 hn4 hM hm hc₀ hL3 hPh halpha_n
    (RelPair := RelPair) (fun _ _ h ↦ h) kv kp hMass hkp hUnm_eq hSgn_eq S_idx P hP_inj hP_sh
  dsimp only [PairSim, k, z, a_max, u, α, B]
  exact ⟨(sum_filter_eq_of_iff_v13 _ _ (fun _ ↦ Iff.rfl)).trans_le h.1,
    (sum_filter_eq_of_iff_v13 _ _ (fun _ ↦ Iff.rfl)).trans_le h.2⟩

/-!
## 4. Unconditional Proposition 7.3 second-moment bounds & Corollary 8.1 upper tails (Regimes U & C)
-/

private theorem relPair_index_to_profile_sum_le_v13
    {n α M m : ℕ} (halpha_n : m + M + 2 ≤ α)
    {c₀ C_ov E_Z M_mom C_sim_pow : ℝ} (hL_pos : 0 < Real.log (n : ℝ))
    {kv : Fin M → ℕ} {kp : ColoringProfile α}
    (S_idx : Finset ℕ) (P_seq : ℕ → VertexPartition n)
    (hP_sh : ∀ i ∈ S_idx, partitionShape (P_seq i) = ColoringProfile.sizes kp)
    (hMass : selectedVertexMass (fun j : Fin M ↦ α - (m + 1 + j.1)) kv = n)
    (hkp : ∀ idx : Fin α, kp idx = ∑ j : Fin M, if α - (m + 1 + j.1) = idx.1 + 1 then kv j else 0)
    {RelPair : VertexPartition n → VertexPartition n → Prop}
    (f_prob : VertexPartition n → VertexPartition n → ℝ)
    (hf_nn : ∀ Q Q', 0 ≤ f_prob Q Q')
    (wt : (Fin M → ℕ) → ℝ)
    (hwt_nn : ∀ nu, IsPartialSubprofile kv nu → 0 ≤ wt nu)
    (_hEZ_ge : 0 ≤ E_Z) (hM_le_sq : M_mom ≤ E_Z ^ 2) (hM_sq_le : M_mom ^ 2 ≤ 2 * E_Z ^ 2)
    (hC_sim_nn : 0 ≤ C_sim_pow)
    (hC_sim_le : C_sim_pow ≤ (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((α - (M + 1) : ℕ) : ℝ)))
    (hScr : ∀ S_scr : Finset (Fin M → ℕ),
      (∀ nu ∈ S_scr, IsPartialSubprofile kv nu ∧
        (selectedVertexMass (fun j : Fin M ↦ α - (m + 1 + j.1)) nu : ℝ) <
          (n : ℝ) / (Real.log (n : ℝ)) ^ 3) →
      (∑ nu ∈ S_scr, wt nu) ≤ Real.exp ((n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)))
    (hMid : ∀ S_mid : Finset (Fin M → ℕ),
      (∀ nu ∈ S_mid, IsPartialSubprofile kv nu ∧
        (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤
          (selectedVertexMass (fun j : Fin M ↦ α - (m + 1 + j.1)) nu : ℝ) ∧
        (n : ℝ) ^ (1 - c₀) ≤
          ((n - selectedVertexMass (fun j : Fin M ↦ α - (m + 1 + j.1)) nu : ℕ) : ℝ)) →
      Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) * (∑ nu ∈ S_mid, wt nu) ≤ 1)
    (hNonSim_nu : ∀ nu : Fin M → ℕ,
      IsPartialSubprofile kv nu →
      (n : ℝ) ^ (1 - c₀) ≤
        ((n - selectedVertexMass (fun j : Fin M ↦ α - (m + 1 + j.1)) nu : ℕ) : ℝ) →
      (∑ pq ∈ (S_idx ×ˢ S_idx).filter
            (fun pq : ℕ × ℕ ↦
              RelPair (P_seq pq.1) (P_seq pq.2) ∧
              (∀ j : Fin M,
                (((P_seq pq.1).parts ∩ (P_seq pq.2).parts).filter fun D ↦ D.card = α - (m + 1 + j.1)).card = nu j)),
          f_prob (P_seq pq.1) (P_seq pq.2)) ≤
        Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) * M_mom ^ 2 * wt nu)
    (hSim_all :
      (∑ pq ∈ (S_idx ×ˢ S_idx).filter
            (fun pq : ℕ × ℕ ↦
              RelPair (P_seq pq.1) (P_seq pq.2) ∧
              (((n - selectedVertexMass (fun j : Fin M ↦ α - (m + 1 + j.1))
                  (fun j : Fin M ↦ (((P_seq pq.1).parts ∩ (P_seq pq.2).parts).filter
                    fun D ↦ D.card = α - (m + 1 + j.1)).card) : ℕ) : ℝ) <
                (n : ℝ) ^ (1 - c₀))),
          f_prob (P_seq pq.1) (P_seq pq.2)) ≤
        M_mom * C_sim_pow * Real.exp (12 * (Real.log (n : ℝ)) ^ 5) *
          ∑ s ∈ Finset.range (selectedBlockCount kv + 1),
            ((selectedBlockCount kv : ℝ) * (n : ℝ) ^ ((1 - c₀) * ((α - (m + 1) : ℕ) : ℝ)) *
              (2 : ℝ) ^ (-((α - (3 * M + 4)).choose 2 : ℝ))) ^ s) :
    ∃ W_scr W_mid : ℝ,
      W_scr ≤ Real.exp ((n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) ∧
      Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) * W_mid ≤ 1 ∧
      (∑ p ∈ (S_idx ×ˢ S_idx).filter (fun p ↦ RelPair (P_seq p.1) (P_seq p.2)),
          f_prob (P_seq p.1) (P_seq p.2)) ≤
        E_Z ^ 2 *
          (2 * (Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) * W_scr +
              Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) * W_mid) +
            (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((α - (M + 1) : ℕ) : ℝ)) *
              Real.exp (13 * (Real.log (n : ℝ)) ^ 5) *
              ∑ s ∈ Finset.range (selectedBlockCount kv + 1),
                ((selectedBlockCount kv : ℝ) * (n : ℝ) ^ ((1 - c₀) * ((α - (m + 1) : ℕ) : ℝ)) *
                  (2 : ℝ) ^ (-((α - (3 * M + 4)).choose 2 : ℝ))) ^ s) := by
  let u : Fin M → ℕ := fun j ↦ α - (m + 1 + j.1)
  set L : ℝ := Real.log (n : ℝ)
  have hexp12_13 : Real.exp (12 * L ^ 5) ≤ Real.exp (13 * L ^ 5) :=
    Real.exp_le_exp.mpr (by have hp := pow_pos hL_pos 5; linarith only [hp])
  let AllRel : Finset (ℕ × ℕ) := (S_idx ×ˢ S_idx).filter fun pq ↦ RelPair (P_seq pq.1) (P_seq pq.2)
  let nuOf : ℕ × ℕ → Fin M → ℕ :=
    fun pq j ↦ (((P_seq pq.1).parts ∩ (P_seq pq.2).parts).filter fun D ↦ D.card = u j).card
  let PairNonSim := AllRel.filter fun pq ↦
    (n : ℝ) ^ (1 - c₀) ≤ ((n - selectedVertexMass u (nuOf pq) : ℕ) : ℝ)
  let PairSim := AllRel.filter fun pq ↦
    ¬ ((n : ℝ) ^ (1 - c₀) ≤ ((n - selectedVertexMass u (nuOf pq) : ℕ) : ℝ))
  let AllNu : Finset (Fin M → ℕ) :=
    (Fintype.piFinset fun j : Fin M ↦ Finset.range (kv j + 1)).filter fun nu ↦
      (n : ℝ) ^ (1 - c₀) ≤ ((n - selectedVertexMass u nu : ℕ) : ℝ)
  let S_scr := AllNu.filter fun nu ↦ (selectedVertexMass u nu : ℝ) < (n : ℝ) / L ^ 3
  let S_mid := AllNu.filter fun nu ↦ ¬ ((selectedVertexMass u nu : ℝ) < (n : ℝ) / L ^ 3)
  set W_scr := ∑ nu ∈ S_scr, wt nu
  set W_mid := ∑ nu ∈ S_mid, wt nu
  have hmaps_nu : ∀ pq ∈ PairNonSim, nuOf pq ∈ AllNu := by
    intro pq hpq
    obtain ⟨hpqA, hge⟩ := Finset.mem_filter.mp hpq
    obtain ⟨hpq1, hpq2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hpqA).1
    have hsub := (subprofile_inter_and_sdiff_stats_v13 halpha_n hMass hkp
      (P_seq pq.1) (P_seq pq.2) (hP_sh pq.1 hpq1) (hP_sh pq.2 hpq2)).1
    exact Finset.mem_filter.mpr
      ⟨Fintype.mem_piFinset.mpr fun j ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (hsub j)), hge⟩
  have hAllNu_props : ∀ nu ∈ AllNu,
      IsPartialSubprofile kv nu ∧ (n : ℝ) ^ (1 - c₀) ≤ ((n - selectedVertexMass u nu : ℕ) : ℝ) := by
    intro nu hnu
    obtain ⟨hpi, hge⟩ := Finset.mem_filter.mp hnu
    exact ⟨fun j ↦ Nat.lt_succ_iff.mp (Finset.mem_range.mp (Fintype.mem_piFinset.mp hpi j)), hge⟩
  refine ⟨W_scr, W_mid,
    hScr S_scr (fun nu hnu ↦ ⟨(hAllNu_props nu (Finset.mem_filter.mp hnu).1).1, (Finset.mem_filter.mp hnu).2⟩),
    hMid S_mid (fun nu hnu ↦ ⟨(hAllNu_props nu (Finset.mem_filter.mp hnu).1).1,
      not_lt.mp (Finset.mem_filter.mp hnu).2, (hAllNu_props nu (Finset.mem_filter.mp hnu).1).2⟩),
    ?_⟩
  rw [← Finset.sum_filter_add_sum_filter_not AllRel
    (fun pq ↦ (n : ℝ) ^ (1 - c₀) ≤ ((n - selectedVertexMass u (nuOf pq) : ℕ) : ℝ))
    (fun pq ↦ f_prob (P_seq pq.1) (P_seq pq.2))]
  have hNonSim_bound :
      (∑ pq ∈ PairNonSim, f_prob (P_seq pq.1) (P_seq pq.2)) ≤
        E_Z ^ 2 * (2 * (Real.exp (C_ov * L ^ 5) * W_scr + Real.exp (C_ov * L ^ 5) * W_mid)) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := nuOf) hmaps_nu]
    have hnu_each : ∀ nu ∈ AllNu,
        (∑ pq ∈ PairNonSim.filter (fun pq ↦ nuOf pq = nu), f_prob (P_seq pq.1) (P_seq pq.2)) ≤
          Real.exp (C_ov * L ^ 5) * M_mom ^ 2 * wt nu := by
      intro nu hnu
      obtain ⟨hsub, hge⟩ := hAllNu_props nu hnu
      refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ ↦ hf_nn _ _)).trans
        (hNonSim_nu nu hsub hge)
      intro pq hpq
      obtain ⟨hpqNS, hnu_eq⟩ := Finset.mem_filter.mp hpq
      obtain ⟨hpqS, hRel⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hpqNS).1
      exact Finset.mem_filter.mpr ⟨hpqS, hRel, fun j ↦ congrFun hnu_eq j⟩
    have hun_SM : S_scr ∪ S_mid = AllNu := Finset.filter_union_filter_not_eq _ _
    have hdisj_SM : Disjoint S_scr S_mid := Finset.disjoint_filter_filter_not _ _ _
    have hW1 : 0 ≤ W_scr := Finset.sum_nonneg fun nu hnu ↦
      hwt_nn nu (hAllNu_props nu (Finset.mem_filter.mp hnu).1).1
    have hW2 : 0 ≤ W_mid := Finset.sum_nonneg fun nu hnu ↦
      hwt_nn nu (hAllNu_props nu (Finset.mem_filter.mp hnu).1).1
    calc ∑ nu ∈ AllNu, _
        ≤ ∑ nu ∈ AllNu, Real.exp (C_ov * L ^ 5) * M_mom ^ 2 * wt nu := Finset.sum_le_sum hnu_each
      _ = M_mom ^ 2 * (Real.exp (C_ov * L ^ 5) * W_scr + Real.exp (C_ov * L ^ 5) * W_mid) := by
          rw [← Finset.mul_sum, ← hun_SM, Finset.sum_union hdisj_SM]; ring
      _ ≤ (2 * E_Z ^ 2) * (Real.exp (C_ov * L ^ 5) * W_scr + Real.exp (C_ov * L ^ 5) * W_mid) :=
          mul_le_mul_of_nonneg_right hM_sq_le
            (add_nonneg (mul_nonneg (Real.exp_pos _).le hW1) (mul_nonneg (Real.exp_pos _).le hW2))
      _ = _ := by ring
  have hSim_bound :
      (∑ pq ∈ PairSim, f_prob (P_seq pq.1) (P_seq pq.2)) ≤
        E_Z ^ 2 *
          ((2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((α - (M + 1) : ℕ) : ℝ)) *
            Real.exp (13 * L ^ 5) *
            ∑ s ∈ Finset.range (selectedBlockCount kv + 1),
              ((selectedBlockCount kv : ℝ) * (n : ℝ) ^ ((1 - c₀) * ((α - (m + 1) : ℕ) : ℝ)) *
                (2 : ℝ) ^ (-((α - (3 * M + 4)).choose 2 : ℝ))) ^ s) := by
    have hsub_ps : PairSim ⊆ (S_idx ×ˢ S_idx).filter (fun pq ↦
        RelPair (P_seq pq.1) (P_seq pq.2) ∧
        (((n - selectedVertexMass u (nuOf pq) : ℕ) : ℝ) < (n : ℝ) ^ (1 - c₀))) := by
      intro pq hpq
      obtain ⟨hpqA, hnot_ge⟩ := Finset.mem_filter.mp hpq
      obtain ⟨hpqS, hRel⟩ := Finset.mem_filter.mp hpqA
      exact Finset.mem_filter.mpr ⟨hpqS, hRel, not_le.mp hnot_ge⟩
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub_ps (fun _ _ _ ↦ hf_nn _ _)).trans
      (hSim_all.trans ?_)
    have h1 : M_mom * C_sim_pow * Real.exp (12 * L ^ 5) ≤
        E_Z ^ 2 * ((2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((α - (M + 1) : ℕ) : ℝ)) * Real.exp (13 * L ^ 5)) := by
      calc M_mom * C_sim_pow * Real.exp (12 * L ^ 5)
          ≤ E_Z ^ 2 * (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((α - (M + 1) : ℕ) : ℝ)) * Real.exp (13 * L ^ 5) :=
            mul_le_mul (mul_le_mul hM_le_sq hC_sim_le hC_sim_nn (sq_nonneg _)) hexp12_13
              (by positivity) (by positivity)
        _ = _ := by ring
    refine (mul_le_mul_of_nonneg_right h1 ?_).trans_eq (by ring)
    exact Finset.sum_nonneg fun s _ ↦ pow_nonneg (by positivity) s
  exact (add_le_add hNonSim_bound hSim_bound).trans_eq (by ring)

private theorem secondMoment_seed_of_selected_v13
    {n M m : ℕ} (_hn4 : 4 ≤ n) (_hM1 : 1 ≤ M) (hm : m ≤ 1)
    (halpha_n : m + M + 2 ≤ phaseNat n)
    (hL_ge1 : (1 : ℝ) ≤ Real.log (n : ℝ))
    {c₀ C_ov C_sm : ℝ}
    {k_co_vec k_ch_vec : Fin M → ℕ} {kp_co kp_ch : ColoringProfile (phaseNat n)}
    (hco_mass : selectedVertexMass (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) k_co_vec = n)
    (hch_mass : selectedVertexMass (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) k_ch_vec = n)
    (hco_ub : (selectedBlockCount k_co_vec : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ))
    (hch_ub : (selectedBlockCount k_ch_vec : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ))
    (hco_kp : ∀ idx : Fin (phaseNat n),
      kp_co idx = ∑ j : Fin M, if phaseNat n - (m + 1 + j.1) = idx.1 + 1 then k_co_vec j else 0)
    (hch_kp : ∀ idx : Fin (phaseNat n),
      kp_ch idx = ∑ j : Fin M, if phaseNat n - (m + 1 + j.1) = idx.1 + 1 then k_ch_vec j else 0)
    (hco_sgn : (signedProfileExpectation n kp_co).toReal =
      completeSignedFirstMoment (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) k_co_vec)
    (hch_unm : (profileColoringExpectation n kp_ch).toReal =
      completeUnmarkedFirstMoment (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) k_ch_vec)
    (hco_G : ∀ G : LabeledGraph n,
      (∃ P : ProfilePartition n kp_co, G ∈ partitionCocoloringEvent P.1) →
        cochromaticNumber G ≤ selectedBlockCount k_co_vec)
    (hch_G : ∀ G : LabeledGraph n,
      (∃ P : ProfilePartition n kp_ch, G ∈ partitionColoringEvent P.1) →
        chromaticNumberNat G ≤ selectedBlockCount k_ch_vec)
    (hco_log2 : 2 ≤ Real.log (completeSignedFirstMoment
      (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) k_co_vec))
    (hch_log2 : 2 ≤ Real.log (completeUnmarkedFirstMoment
      (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) k_ch_vec))
    (hScr_co : ∀ S_scr : Finset (Fin M → ℕ),
      (∀ nu ∈ S_scr, IsPartialSubprofile k_co_vec nu ∧
        (selectedVertexMass (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) nu : ℝ) <
          (n : ℝ) / (Real.log (n : ℝ)) ^ 3) →
      (∑ nu ∈ S_scr, partialDiagonalWeight n
          (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) k_co_vec nu) ≤
        Real.exp ((n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)))
    (hScr_ch : ∀ S_scr : Finset (Fin M → ℕ),
      (∀ nu ∈ S_scr, IsPartialSubprofile k_ch_vec nu ∧
        (selectedVertexMass (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) nu : ℝ) <
          (n : ℝ) / (Real.log (n : ℝ)) ^ 3) →
      (∑ nu ∈ S_scr, unmarkedDiagonalWeight n
          (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) k_ch_vec nu) ≤
        Real.exp ((n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)))
    (hMid_co : ∀ S_mid : Finset (Fin M → ℕ),
      (∀ nu ∈ S_mid, IsPartialSubprofile k_co_vec nu ∧
        (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤
          (selectedVertexMass (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) nu : ℝ) ∧
        (n : ℝ) ^ (1 - c₀) ≤
          ((n - selectedVertexMass (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) nu : ℕ) : ℝ)) →
      Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
        (∑ nu ∈ S_mid, partialDiagonalWeight n
            (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) k_co_vec nu) ≤ 1)
    (hMid_ch : ∀ S_mid : Finset (Fin M → ℕ),
      (∀ nu ∈ S_mid, IsPartialSubprofile k_ch_vec nu ∧
        (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤
          (selectedVertexMass (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) nu : ℝ) ∧
        (n : ℝ) ^ (1 - c₀) ≤
          ((n - selectedVertexMass (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) nu : ℕ) : ℝ)) →
      Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
        (∑ nu ∈ S_mid, unmarkedDiagonalWeight n
            (fun j : Fin M ↦ phaseNat n - (m + 1 + j.1)) k_ch_vec nu) ≤ 1)
    (hLem71_n :
      let α : ℕ := phaseNat n
      let U_sizes : Set ℕ := {s : ℕ | α - (M + 1) ≤ s ∧ s ≤ α}
      let c_full : ℝ := (Real.log (n : ℝ)) ^ 3
      let c_half : ℝ := (1 / 2 : ℝ) * (Real.log (n : ℝ)) ^ 3
      let B_ind : VertexPartition n → Set (LabeledGraph n) := fun Q ↦
        {G | ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) → S.card ∈ U_sizes →
          (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card ≤ 2 ∨
            S.card ≤ (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card + 2 * (α - S.card) + 1}
      let C_ind : VertexPartition n → Set (LabeledGraph n) := fun Q ↦
        {G | ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) → S.card ∈ U_sizes →
          (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 →
            ∃ E ∈ Q.parts, (S ∩ E).card = S.card - 1}
      let D_ind : VertexPartition n → ℝ → Set (LabeledGraph n) := fun Q c_cap ↦
        {G | (((Finset.univ : Finset (Fin n)).powerset.filter fun S : Finset (Fin n) ↦
            G.IsIndepSet (S : Set (Fin n)) ∧ S.card ∈ U_sizes ∧
            (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 ∧
            ∃ E ∈ Q.parts, E.card - 1 ≤ (S ∩ E).card).card : ℝ) ≤ c_cap}
      let B_cl : VertexPartition n → Set (LabeledGraph n) := fun Q ↦
        {G | ∀ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) → S.card ∈ U_sizes →
          (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card ≤ 2 ∨
            S.card ≤ (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card + 2 * (α - S.card) + 1}
      let C_cl : VertexPartition n → Set (LabeledGraph n) := fun Q ↦
        {G | ∀ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) → S.card ∈ U_sizes →
          (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 →
            ∃ E ∈ Q.parts, (S ∩ E).card = S.card - 1}
      let D_cl : VertexPartition n → ℝ → Set (LabeledGraph n) := fun Q c_cap ↦
        {G | (((Finset.univ : Finset (Fin n)).powerset.filter fun S : Finset (Fin n) ↦
            G.IsClique (S : Set (Fin n)) ∧ S.card ∈ U_sizes ∧
            (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 ∧
            ∃ E ∈ Q.parts, E.card - 1 ≤ (S ∩ E).card).card : ℝ) ≤ c_cap}
      let RelPair : ℕ → VertexPartition n → VertexPartition n → Prop := fun B Q Q' ↦
        ((∀ D ∈ Q.parts,
            (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card ≤ 2 ∨
              D.card ≤ (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card + 2 * (α - D.card) + 1) ∧
          (∀ D' ∈ Q'.parts,
            (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card ≤ 2 ∨
              D'.card ≤ (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card + 2 * (α - D'.card) + 1)) ∧
        ((∀ D ∈ Q.parts, (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 →
            ∃ D' ∈ Q'.parts, (D ∩ D').card = D.card - 1) ∧
          (∀ D' ∈ Q'.parts, (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 →
            ∃ D ∈ Q.parts, (D' ∩ D).card = D'.card - 1)) ∧
        ((Q.parts.filter fun D ↦
            (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 ∧
              ∃ D' ∈ Q'.parts, D'.card - 1 ≤ (D ∩ D').card).card ≤ B ∧
          (Q'.parts.filter fun D' ↦
            (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 ∧
              ∃ D ∈ Q.parts, D.card - 1 ≤ (D' ∩ D).card).card ≤ B)
      ∀ (S_idx : Finset ℕ) (P : ℕ → VertexPartition n),
        (∀ i ∈ S_idx, ∀ D ∈ (P i).parts, D.card ∈ U_sizes) →
        let Z_ch : LabeledGraph n → ℝ := fun G ↦
          ∑ i ∈ S_idx,
            if G ∈ partitionColoringEvent (P i) ∩ B_ind (P i) ∩ C_ind (P i) ∩ D_ind (P i) c_full
            then (1 : ℝ) else 0
        let Z_co : LabeledGraph n → ℝ := fun G ↦
          ∑ i ∈ S_idx,
            if G ∈ partitionCocoloringEvent (P i) ∩ B_ind (P i) ∩ C_ind (P i) ∩
                D_ind (P i) c_half ∩ B_cl (P i) ∩ C_cl (P i) ∩ D_cl (P i) c_half
            then (1 : ℝ) else 0
        (1 - (1 / 4 : ℝ)) * (∑ i ∈ S_idx, (randomGraphMeasure n).real (partitionColoringEvent (P i))) ≤
            (∫ G : LabeledGraph n, Z_ch G ∂randomGraphMeasure n) ∧
          (1 - (1 / 4 : ℝ)) * (∑ i ∈ S_idx,
              (2 : ℝ) ^ (P i).parts.card *
                (randomGraphMeasure n).real (partitionColoringEvent (P i))) ≤
            (∫ G : LabeledGraph n, Z_co G ∂randomGraphMeasure n) ∧
          (∫ G : LabeledGraph n, (Z_ch G) ^ 2 ∂randomGraphMeasure n) ≤
            ∑ p ∈ (S_idx ×ˢ S_idx).filter (fun p ↦ RelPair (Nat.floor c_full) (P p.1) (P p.2)),
              (randomGraphMeasure n).real
                (partitionColoringEvent (P p.1) ∩ partitionColoringEvent (P p.2)) ∧
          (∫ G : LabeledGraph n, (Z_co G) ^ 2 ∂randomGraphMeasure n) ≤
            ∑ p ∈ (S_idx ×ˢ S_idx).filter (fun p ↦ RelPair (Nat.floor (2 * c_half)) (P p.1) (P p.2)),
              (randomGraphMeasure n).real
                (partitionCocoloringEvent (P p.1) ∩ partitionCocoloringEvent (P p.2)))
    (hLem72_n :
      let α : ℕ := phaseNat n
      let B : ℕ := Nat.floor ((Real.log (n : ℝ)) ^ 3)
      let RelPair : VertexPartition n → VertexPartition n → Prop := fun Q Q' ↦
        ((∀ D ∈ Q.parts,
            (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card ≤ 2 ∨
              D.card ≤ (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card + 2 * (α - D.card) + 1) ∧
          (∀ D' ∈ Q'.parts,
            (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card ≤ 2 ∨
              D'.card ≤ (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card + 2 * (α - D'.card) + 1)) ∧
        ((∀ D ∈ Q.parts, (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 →
            ∃ D' ∈ Q'.parts, (D ∩ D').card = D.card - 1) ∧
          (∀ D' ∈ Q'.parts, (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 →
            ∃ D ∈ Q.parts, (D' ∩ D).card = D'.card - 1)) ∧
        ((Q.parts.filter fun D ↦
            (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 ∧
              ∃ D' ∈ Q'.parts, D'.card - 1 ≤ (D ∩ D').card).card ≤ B ∧
          (Q'.parts.filter fun D' ↦
            (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 ∧
              ∃ D ∈ Q.parts, D.card - 1 ≤ (D' ∩ D).card).card ≤ B)
      let u : Fin M → ℕ := fun j ↦ α - (m + 1 + j.1)
      ∀ (kv : Fin M → ℕ) (kp : ColoringProfile α) (nu : Fin M → ℕ),
        selectedVertexMass u kv = n →
        (∀ idx : Fin α, kp idx = ∑ j : Fin M, if u j = idx.1 + 1 then kv j else 0) →
        IsPartialSubprofile kv nu →
        (n : ℝ) ^ (1 - c₀) ≤ ((n - selectedVertexMass u nu : ℕ) : ℝ) →
        ∀ (S_idx : Finset ℕ) (P : ℕ → VertexPartition n),
          Set.InjOn P (S_idx : Set ℕ) →
          (∀ i ∈ S_idx, partitionShape (P i) = ColoringProfile.sizes kp) →
          let PairNu : Finset (ℕ × ℕ) :=
            (S_idx ×ˢ S_idx).filter fun pq ↦
              RelPair (P pq.1) (P pq.2) ∧
              (∀ j : Fin M, (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = u j).card = nu j)
          (∑ pq ∈ PairNu,
              (randomGraphMeasure n).real
                (partitionColoringEvent (P pq.1) ∩ partitionColoringEvent (P pq.2))) ≤
            Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
              (completeUnmarkedFirstMoment u kv) ^ 2 *
              unmarkedDiagonalWeight n u kv nu ∧
          (∑ pq ∈ PairNu,
              (randomGraphMeasure n).real
                (partitionCocoloringEvent (P pq.1) ∩ partitionCocoloringEvent (P pq.2))) ≤
            Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
              (completeSignedFirstMoment u kv) ^ 2 *
              partialDiagonalWeight n u kv nu)
    (hSim_n :
      let α : ℕ := phaseNat n
      let B : ℕ := Nat.floor ((Real.log (n : ℝ)) ^ 3)
      let RelPair : VertexPartition n → VertexPartition n → Prop := fun Q Q' ↦
        ((∀ D ∈ Q.parts,
            (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card ≤ 2 ∨
              D.card ≤ (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card + 2 * (α - D.card) + 1) ∧
          (∀ D' ∈ Q'.parts,
            (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card ≤ 2 ∨
              D'.card ≤ (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card + 2 * (α - D'.card) + 1)) ∧
        ((∀ D ∈ Q.parts, (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 →
            ∃ D' ∈ Q'.parts, (D ∩ D').card = D.card - 1) ∧
          (∀ D' ∈ Q'.parts, (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 →
            ∃ D ∈ Q.parts, (D' ∩ D).card = D'.card - 1)) ∧
        ((Q.parts.filter fun D ↦
            (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 ∧
              ∃ D' ∈ Q'.parts, D'.card - 1 ≤ (D ∩ D').card).card ≤ B ∧
          (Q'.parts.filter fun D' ↦
            (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 ∧
              ∃ D ∈ Q.parts, D.card - 1 ≤ (D' ∩ D).card).card ≤ B)
      let u : Fin M → ℕ := fun j ↦ α - (m + 1 + j.1)
      let a_max : ℕ := α - (m + 1)
      let z : ℕ := α - (3 * M + 4)
      ∀ (kv : Fin M → ℕ) (kp : ColoringProfile α),
        selectedVertexMass u kv = n →
        (∀ idx : Fin α, kp idx = ∑ j : Fin M, if u j = idx.1 + 1 then kv j else 0) →
        (profileColoringExpectation n kp).toReal = completeUnmarkedFirstMoment u kv →
        (signedProfileExpectation n kp).toReal = completeSignedFirstMoment u kv →
        ∀ (S_idx : Finset ℕ) (P : ℕ → VertexPartition n),
          Set.InjOn P (S_idx : Set ℕ) →
          (∀ i ∈ S_idx, partitionShape (P i) = ColoringProfile.sizes kp) →
          let k : ℕ := selectedBlockCount kv
          let PairSim : Finset (ℕ × ℕ) :=
            (S_idx ×ˢ S_idx).filter fun pq ↦
              RelPair (P pq.1) (P pq.2) ∧
              (((n - selectedVertexMass u
                (fun j : Fin M ↦ (((P pq.1).parts ∩ (P pq.2).parts).filter fun D ↦ D.card = u j).card) : ℕ) : ℝ) <
                (n : ℝ) ^ (1 - c₀))
          (∑ pq ∈ PairSim,
              (randomGraphMeasure n).real
                (partitionColoringEvent (P pq.1) ∩ partitionColoringEvent (P pq.2))) ≤
            completeUnmarkedFirstMoment u kv *
              Real.exp (12 * (Real.log (n : ℝ)) ^ 5) *
              ∑ s ∈ Finset.range (k + 1),
                ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ)) *
                  (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s ∧
          (∑ pq ∈ PairSim,
              (randomGraphMeasure n).real
                (partitionCocoloringEvent (P pq.1) ∩ partitionCocoloringEvent (P pq.2))) ≤
            completeSignedFirstMoment u kv *
              (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((α - (M + 1) : ℕ) : ℝ)) *
              Real.exp (12 * (Real.log (n : ℝ)) ^ 5) *
              ∑ s ∈ Finset.range (k + 1),
                ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ)) *
                  (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s)
    (h3R_n :
      ∀ (Z : LabeledGraph n → ℝ) (W_scr W_mid : ℝ) (k a z : ℕ),
        (∀ G, 0 ≤ Z G) →
        0 < (∫ G : LabeledGraph n, Z G ∂randomGraphMeasure n) →
        k ≤ n → a ≤ phaseNat n → phaseNat n - (3 * M + 4) ≤ z →
        W_scr ≤ Real.exp ((n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) →
        Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) * W_mid ≤ 1 →
        (∫ G : LabeledGraph n, (Z G) ^ 2 ∂randomGraphMeasure n) ≤
          (∫ G : LabeledGraph n, Z G ∂randomGraphMeasure n) ^ 2 *
            (2 * (Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) * W_scr +
                Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) * W_mid) +
              (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((phaseNat n - (M + 1) : ℕ) : ℝ)) *
                Real.exp (13 * (Real.log (n : ℝ)) ^ 5) *
                ∑ s ∈ Finset.range (k + 1),
                  ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a : ℝ)) *
                    (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s) →
        (∫ G : LabeledGraph n, (Z G) ^ 2 ∂randomGraphMeasure n) ≤
            Real.exp (C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) *
              (∫ G : LabeledGraph n, Z G ∂randomGraphMeasure n) ^ 2 ∧
          Real.exp (-C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) ≤
            (randomGraphMeasure n).real {G : LabeledGraph n | 0 < Z G}) :
    Real.exp (-C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) ≤
        (randomGraphMeasure n).real
          {G : LabeledGraph n | cochromaticNumber G ≤ selectedBlockCount k_co_vec} ∧
      Real.exp (-C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) ≤
        (randomGraphMeasure n).real
          {G : LabeledGraph n | chromaticNumberNat G ≤ selectedBlockCount k_ch_vec} := by
  let α := phaseNat n
  let u : Fin M → ℕ := fun j ↦ α - (m + 1 + j.1)
  set a_max := α - (m + 1)
  set z := α - (3 * M + 4)
  set L : ℝ := Real.log (n : ℝ)
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL_ge1
  have hexp2_ge4 : (4 : ℝ) ≤ Real.exp 2 := by
    have h1 := Real.add_one_le_exp 1
    calc (4 : ℝ) = (1 + 1) * (1 + 1) := by norm_num
      _ ≤ Real.exp 1 * Real.exp 1 := mul_le_mul h1 h1 (by norm_num) (Real.exp_pos 1).le
      _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have hexp12_13 : Real.exp (12 * L ^ 5) ≤ Real.exp (13 * L ^ 5) :=
    Real.exp_le_exp.mpr (by have hp := pow_pos hL_pos 5; linarith only [hp])
  obtain ⟨_, hu_bds, hco_part_eq, _, _, hP_co_all⟩ :=
    windowProfile_part_sizes_and_counts_v13 halpha_n hco_mass hco_kp
  obtain ⟨_, _, hch_part_eq, _, _, hP_ch_all⟩ :=
    windowProfile_part_sizes_and_counts_v13 halpha_n hch_mass hch_kp
  have hco_unm : (profileColoringExpectation n kp_co).toReal = completeUnmarkedFirstMoment u k_co_vec := by
    have hs := congrArg ENNReal.toReal (signedProfileExpectation_eq n kp_co)
    rw [hco_sgn, hco_part_eq, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hs
    unfold completeUnmarkedFirstMoment
    unfold selectedBlockCount at hs
    rw [hs, inv_mul_cancel_left₀ (by positivity)]
  have hch_sgn : (signedProfileExpectation n kp_ch).toReal = completeSignedFirstMoment u k_ch_vec := by
    have hs := congrArg ENNReal.toReal (signedProfileExpectation_eq n kp_ch)
    rw [hch_part_eq, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat, hch_unm] at hs
    unfold completeUnmarkedFirstMoment selectedBlockCount at hs
    rw [hs, mul_inv_cancel_left₀ (by positivity)]
  have hex_enum : ∀ kp : ColoringProfile α,
      ∃ (N_kp : ℕ) (P_seq : ℕ → VertexPartition n),
        N_kp = Nat.card (ProfilePartition n kp) ∧
        Set.InjOn P_seq (Finset.range N_kp : Set ℕ) ∧
        (∀ i ∈ Finset.range N_kp, partitionShape (P_seq i) = ColoringProfile.sizes kp) := by
    intro kp
    let N_kp := Nat.card (ProfilePartition n kp)
    let e_kp : Fin N_kp ≃ ProfilePartition n kp := (Finite.equivFin (ProfilePartition n kp)).symm
    let P_seq : ℕ → VertexPartition n := fun i ↦ if hi : i < N_kp then (e_kp ⟨i, hi⟩).1 else ⊥
    refine ⟨N_kp, P_seq, rfl, ?_, ?_⟩
    · intro i₁ hi₁ i₂ hi₂ heq
      have hi₁' : i₁ < N_kp := Finset.mem_range.mp (Finset.mem_coe.mp hi₁)
      have hi₂' : i₂ < N_kp := Finset.mem_range.mp (Finset.mem_coe.mp hi₂)
      simp only [P_seq, dif_pos hi₁', dif_pos hi₂'] at heq
      exact Fin.val_eq_of_eq (e_kp.injective (Subtype.ext heq))
    · intro i hi
      have hi' : i < N_kp := Finset.mem_range.mp hi
      simp only [P_seq, dif_pos hi']
      exact (e_kp ⟨i, hi'⟩).2
  set B_fl : ℕ := Nat.floor (L ^ 3)
  let RelPair_fl : VertexPartition n → VertexPartition n → Prop := fun Q Q' ↦
    ((∀ D ∈ Q.parts,
        (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card ≤ 2 ∨
          D.card ≤ (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card + 2 * (α - D.card) + 1) ∧
      (∀ D' ∈ Q'.parts,
        (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card ≤ 2 ∨
          D'.card ≤ (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card + 2 * (α - D'.card) + 1)) ∧
    ((∀ D ∈ Q.parts, (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 →
        ∃ D' ∈ Q'.parts, (D ∩ D').card = D.card - 1) ∧
      (∀ D' ∈ Q'.parts, (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 →
        ∃ D ∈ Q.parts, (D' ∩ D).card = D'.card - 1)) ∧
    ((Q.parts.filter fun D ↦
        (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 ∧
          ∃ D' ∈ Q'.parts, D'.card - 1 ≤ (D ∩ D').card).card ≤ B_fl ∧
      (Q'.parts.filter fun D' ↦
        (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 ∧
          ∃ D ∈ Q.parts, D.card - 1 ≤ (D' ∩ D).card).card ≤ B_fl)
  -- 1. Cochromatic seed lower bound
  have hSeed_co :
      Real.exp (-C_sm * (n : ℝ) ^ (1 - c₀) / L) ≤
        (randomGraphMeasure n).real
          {G : LabeledGraph n | cochromaticNumber G ≤ selectedBlockCount k_co_vec} := by
    set k_co := selectedBlockCount k_co_vec
    have hk_co_le_n : k_co ≤ n := by
      have hR : (k_co : ℝ) ≤ (n : ℝ) := hco_ub.trans (div_le_self (Nat.cast_nonneg n) hL_ge1)
      exact_mod_cast hR
    rcases hex_enum kp_co with ⟨N_co, P_co_seq, hN_co_card, hP_co_inj, hP_co_sh⟩
    let S_co : Finset ℕ := Finset.range N_co
    have hU_co : ∀ i ∈ S_co, ∀ D ∈ (P_co_seq i).parts, α - (M + 1) ≤ D.card ∧ D.card ≤ α := by
      intro i hi D hD
      obtain ⟨j, hj⟩ := (hP_co_all (P_co_seq i) (hP_co_sh i hi)).2.2.2 D hD
      rw [hj]; exact ⟨by have := (hu_bds j).2.1; omega, (hu_bds j).2.2.trans (Nat.sub_le _ _)⟩
    have h71 := hLem71_n S_co P_co_seq hU_co
    dsimp only at h71
    obtain ⟨_, hEZ_co_lb, _, hEZ2_co_ub⟩ := h71
    let U_sizes : Set ℕ := {s : ℕ | α - (M + 1) ≤ s ∧ s ≤ α}
    set Z_co : LabeledGraph n → ℝ := fun G ↦
      ∑ i ∈ S_co,
        if G ∈ partitionCocoloringEvent (P_co_seq i) ∩
            {G | ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) → S.card ∈ U_sizes →
              ((P_co_seq i).parts.filter fun E ↦ (S ∩ E).Nonempty).card ≤ 2 ∨
                S.card ≤ ((P_co_seq i).parts.filter fun E ↦ (S ∩ E).Nonempty).card + 2 * (α - S.card) + 1} ∩
            {G | ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) → S.card ∈ U_sizes →
              ((P_co_seq i).parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 →
                ∃ E ∈ (P_co_seq i).parts, (S ∩ E).card = S.card - 1} ∩
            {G | (((Finset.univ : Finset (Fin n)).powerset.filter fun S : Finset (Fin n) ↦
                G.IsIndepSet (S : Set (Fin n)) ∧ S.card ∈ U_sizes ∧
                ((P_co_seq i).parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 ∧
                ∃ E ∈ (P_co_seq i).parts, E.card - 1 ≤ (S ∩ E).card).card : ℝ) ≤ (1 / 2 : ℝ) * L ^ 3} ∩
            {G | ∀ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) → S.card ∈ U_sizes →
              ((P_co_seq i).parts.filter fun E ↦ (S ∩ E).Nonempty).card ≤ 2 ∨
                S.card ≤ ((P_co_seq i).parts.filter fun E ↦ (S ∩ E).Nonempty).card + 2 * (α - S.card) + 1} ∩
            {G | ∀ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) → S.card ∈ U_sizes →
              ((P_co_seq i).parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 →
                ∃ E ∈ (P_co_seq i).parts, (S ∩ E).card = S.card - 1} ∩
            {G | (((Finset.univ : Finset (Fin n)).powerset.filter fun S : Finset (Fin n) ↦
                G.IsClique (S : Set (Fin n)) ∧ S.card ∈ U_sizes ∧
                ((P_co_seq i).parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 ∧
                ∃ E ∈ (P_co_seq i).parts, E.card - 1 ≤ (S ∩ E).card).card : ℝ) ≤ (1 / 2 : ℝ) * L ^ 3}
        then (1 : ℝ) else 0
    have hZ_co_nn : ∀ G, 0 ≤ Z_co G := fun G ↦
      Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num
    have hsum_co_eq :
        (∑ i ∈ S_co, (2 : ℝ) ^ (P_co_seq i).parts.card *
          (randomGraphMeasure n).real (partitionColoringEvent (P_co_seq i))) =
        completeSignedFirstMoment u k_co_vec := by
      have hpt : ∀ i ∈ S_co,
          (2 : ℝ) ^ (P_co_seq i).parts.card *
            (randomGraphMeasure n).real (partitionColoringEvent (P_co_seq i)) =
          (2 : ℝ) ^ k_co * ((1 / 2 : ℝ≥0∞) ^ kp_co.forbiddenEdges).toReal := by
        intro i hi
        rw [(hP_co_all (P_co_seq i) (hP_co_sh i hi)).1]
        let Pi : ProfilePartition n kp_co := ⟨P_co_seq i, hP_co_sh i hi⟩
        have hpr : (randomGraphMeasure n).real (partitionColoringEvent (P_co_seq i)) =
            ((1 / 2 : ℝ≥0∞) ^ kp_co.forbiddenEdges).toReal := by
          rw [Measure.real, show P_co_seq i = Pi.1 from rfl,
            randomGraphMeasure_partitionColoringEvent Pi]
        rw [hpr]
      rw [Finset.sum_congr rfl hpt, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← mul_assoc, mul_comm (N_co : ℝ) ((2 : ℝ) ^ k_co), mul_assoc]
      have hunm_val : (N_co : ℝ) * ((1 / 2 : ℝ≥0∞) ^ kp_co.forbiddenEdges).toReal =
          completeUnmarkedFirstMoment u k_co_vec := by
        rw [hN_co_card, ← hco_unm, profileColoringExpectation_eq_card_mul,
          ENNReal.toReal_mul, ENNReal.toReal_natCast]
      rw [hunm_val]
      dsimp [k_co]; unfold completeUnmarkedFirstMoment selectedBlockCount
      rw [mul_inv_cancel_left₀ (by positivity)]
    rw [hsum_co_eq] at hEZ_co_lb
    set M_co := completeSignedFirstMoment u k_co_vec
    have hEZ_co_34 : (3 / 4 : ℝ) * M_co ≤ ∫ G : LabeledGraph n, Z_co G ∂randomGraphMeasure n := by
      have h1 : (3 / 4 : ℝ) * M_co = (1 - (1 / 4 : ℝ)) * M_co := by ring
      exact h1.trans_le hEZ_co_lb
    have hM_co_ge4 : 4 ≤ M_co := by
      have hnn : 0 ≤ M_co := hco_sgn ▸ ENNReal.toReal_nonneg
      have hne0 : M_co ≠ 0 := fun h0 ↦ by rw [h0, Real.log_zero] at hco_log2; norm_num at hco_log2
      have hpos : 0 < M_co := lt_of_le_of_ne hnn hne0.symm
      rw [← Real.exp_log hpos]
      exact hexp2_ge4.trans (Real.exp_le_exp.mpr hco_log2)
    have hEZ_co_ge3 : 3 ≤ ∫ G : LabeledGraph n, Z_co G ∂randomGraphMeasure n := by
      linarith only [hEZ_co_34, hM_co_ge4]
    have hEZ_co_pos : 0 < ∫ G : LabeledGraph n, Z_co G ∂randomGraphMeasure n := by
      linarith only [hEZ_co_ge3]
    have hM_co_le_43 : M_co ≤ (4 / 3 : ℝ) * ∫ G : LabeledGraph n, Z_co G ∂randomGraphMeasure n := by
      linarith only [hEZ_co_34]
    have hM_co_le_sq : M_co ≤ (∫ G : LabeledGraph n, Z_co G ∂randomGraphMeasure n) ^ 2 := by
      calc M_co ≤ (4 / 3 : ℝ) * ∫ G : LabeledGraph n, Z_co G ∂randomGraphMeasure n := hM_co_le_43
        _ ≤ (∫ G : LabeledGraph n, Z_co G ∂randomGraphMeasure n) *
              (∫ G : LabeledGraph n, Z_co G ∂randomGraphMeasure n) :=
            mul_le_mul_of_nonneg_right (by linarith only [hEZ_co_ge3]) hEZ_co_pos.le
        _ = (∫ G : LabeledGraph n, Z_co G ∂randomGraphMeasure n) ^ 2 := (sq _).symm
    have hM_co_sq_le : M_co ^ 2 ≤ 2 * (∫ G : LabeledGraph n, Z_co G ∂randomGraphMeasure n) ^ 2 := by
      calc M_co ^ 2
          ≤ ((4 / 3 : ℝ) * ∫ G : LabeledGraph n, Z_co G ∂randomGraphMeasure n) ^ 2 :=
            pow_le_pow_left₀ (by linarith only [hM_co_ge4]) hM_co_le_43 2
        _ = (16 / 9 : ℝ) * (∫ G : LabeledGraph n, Z_co G ∂randomGraphMeasure n) ^ 2 := by ring
        _ ≤ 2 * (∫ G : LabeledGraph n, Z_co G ∂randomGraphMeasure n) ^ 2 :=
            mul_le_mul_of_nonneg_right (by norm_num)
              (sq_nonneg (∫ G : LabeledGraph n, Z_co G ∂randomGraphMeasure n))
    have h2half : (2 : ℝ) * ((1 / 2 : ℝ) * L ^ 3) = L ^ 3 := by ring
    rw [h2half] at hEZ2_co_ub
    obtain ⟨W_scr_co, W_mid_co, hW_scr_co_le, hW_mid_co_le, hRel_co_bound⟩ :=
      relPair_index_to_profile_sum_le_v13 (RelPair := RelPair_fl)
        halpha_n hL_pos S_co P_co_seq hP_co_sh hco_mass hco_kp
        (fun Q Q' ↦ (randomGraphMeasure n).real (partitionCocoloringEvent Q ∩ partitionCocoloringEvent Q'))
        (fun _ _ ↦ measureReal_nonneg)
        (partialDiagonalWeight n u k_co_vec)
        (fun nu hsub ↦ (partialDiagonalWeight_pos n u k_co_vec nu hsub).le)
        hEZ_co_pos.le hM_co_le_sq hM_co_sq_le (Real.rpow_nonneg zero_le_two _) le_rfl hScr_co hMid_co
        (fun nu hsub hge ↦
          (sum_filter_eq_of_iff_v13 _ _ (fun _ ↦ Iff.rfl)).trans_le
            (hLem72_n k_co_vec kp_co nu hco_mass hco_kp hsub hge S_co P_co_seq hP_co_inj hP_co_sh).2)
        ((sum_filter_eq_of_iff_v13 _ _ (fun _ ↦ Iff.rfl)).trans_le
          (hSim_n k_co_vec kp_co hco_mass hco_kp hco_unm hco_sgn S_co P_co_seq hP_co_inj hP_co_sh).2)
    have hEZ2_tot :
        (∫ G : LabeledGraph n, (Z_co G) ^ 2 ∂randomGraphMeasure n) ≤
          (∫ G : LabeledGraph n, Z_co G ∂randomGraphMeasure n) ^ 2 *
            (2 * (Real.exp (C_ov * L ^ 5) * W_scr_co + Real.exp (C_ov * L ^ 5) * W_mid_co) +
              (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((α - (M + 1) : ℕ) : ℝ)) *
                Real.exp (13 * L ^ 5) *
                ∑ s ∈ Finset.range (k_co + 1),
                  ((k_co : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ)) *
                    (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s) :=
      hEZ2_co_ub.trans ((sum_filter_eq_of_iff_v13 _ _ (fun _ ↦ Iff.rfl)).trans_le hRel_co_bound)
    have hPZ_co := (h3R_n Z_co W_scr_co W_mid_co k_co a_max z
      hZ_co_nn hEZ_co_pos hk_co_le_n (Nat.sub_le _ _) le_rfl
      hW_scr_co_le hW_mid_co_le hEZ2_tot).2
    refine hPZ_co.trans (measureReal_mono ?_)
    intro G hG_pos
    change 0 < Z_co G at hG_pos
    have hex_i : ∃ i ∈ S_co, G ∈ partitionCocoloringEvent (P_co_seq i) := by
      by_contra hnone
      have hz0 : Z_co G = 0 := by
        dsimp [Z_co]
        refine Finset.sum_eq_zero fun i hi ↦ ?_
        rw [if_neg]; intro hm_g
        exact hnone ⟨i, hi, hm_g.1.1.1.1.1.1⟩
      linarith only [hG_pos, hz0]
    rcases hex_i with ⟨i, hi, hGi⟩
    exact hco_G G ⟨⟨P_co_seq i, hP_co_sh i hi⟩, hGi⟩
  -- 2. Chromatic seed lower bound
  refine ⟨hSeed_co, ?_⟩
  set k_ch := selectedBlockCount k_ch_vec
  have hk_ch_le_n : k_ch ≤ n := by
    have hR : (k_ch : ℝ) ≤ (n : ℝ) := hch_ub.trans (div_le_self (Nat.cast_nonneg n) hL_ge1)
    exact_mod_cast hR
  rcases hex_enum kp_ch with ⟨N_ch, P_ch_seq, hN_ch_card, hP_ch_inj, hP_ch_sh⟩
  let S_ch : Finset ℕ := Finset.range N_ch
  have hU_ch : ∀ i ∈ S_ch, ∀ D ∈ (P_ch_seq i).parts, α - (M + 1) ≤ D.card ∧ D.card ≤ α := by
    intro i hi D hD
    obtain ⟨j, hj⟩ := (hP_ch_all (P_ch_seq i) (hP_ch_sh i hi)).2.2.2 D hD
    rw [hj]; exact ⟨by have := (hu_bds j).2.1; omega, (hu_bds j).2.2.trans (Nat.sub_le _ _)⟩
  have h71 := hLem71_n S_ch P_ch_seq hU_ch
  dsimp only at h71
  obtain ⟨hEZ_ch_lb, _, hEZ2_ch_ub, _⟩ := h71
  let U_sizes : Set ℕ := {s : ℕ | α - (M + 1) ≤ s ∧ s ≤ α}
  set Z_ch : LabeledGraph n → ℝ := fun G ↦
    ∑ i ∈ S_ch,
      if G ∈ partitionColoringEvent (P_ch_seq i) ∩
          {G | ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) → S.card ∈ U_sizes →
            ((P_ch_seq i).parts.filter fun E ↦ (S ∩ E).Nonempty).card ≤ 2 ∨
              S.card ≤ ((P_ch_seq i).parts.filter fun E ↦ (S ∩ E).Nonempty).card + 2 * (α - S.card) + 1} ∩
          {G | ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) → S.card ∈ U_sizes →
            ((P_ch_seq i).parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 →
              ∃ E ∈ (P_ch_seq i).parts, (S ∩ E).card = S.card - 1} ∩
          {G | (((Finset.univ : Finset (Fin n)).powerset.filter fun S : Finset (Fin n) ↦
              G.IsIndepSet (S : Set (Fin n)) ∧ S.card ∈ U_sizes ∧
              ((P_ch_seq i).parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 ∧
              ∃ E ∈ (P_ch_seq i).parts, E.card - 1 ≤ (S ∩ E).card).card : ℝ) ≤ L ^ 3}
      then (1 : ℝ) else 0
  have hZ_ch_nn : ∀ G, 0 ≤ Z_ch G := fun G ↦
    Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num
  have hsum_ch_eq :
      (∑ i ∈ S_ch, (randomGraphMeasure n).real (partitionColoringEvent (P_ch_seq i))) =
        completeUnmarkedFirstMoment u k_ch_vec := by
    have hpt : ∀ i ∈ S_ch,
        (randomGraphMeasure n).real (partitionColoringEvent (P_ch_seq i)) =
          ((1 / 2 : ℝ≥0∞) ^ kp_ch.forbiddenEdges).toReal := by
      intro i hi
      let Pi : ProfilePartition n kp_ch := ⟨P_ch_seq i, hP_ch_sh i hi⟩
      rw [Measure.real, show P_ch_seq i = Pi.1 from rfl,
        randomGraphMeasure_partitionColoringEvent Pi]
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      hN_ch_card, ← hch_unm, profileColoringExpectation_eq_card_mul,
      ENNReal.toReal_mul, ENNReal.toReal_natCast]
  rw [hsum_ch_eq] at hEZ_ch_lb
  set M_ch := completeUnmarkedFirstMoment u k_ch_vec
  have hEZ_ch_34 : (3 / 4 : ℝ) * M_ch ≤ ∫ G : LabeledGraph n, Z_ch G ∂randomGraphMeasure n := by
    have h1 : (3 / 4 : ℝ) * M_ch = (1 - (1 / 4 : ℝ)) * M_ch := by ring
    exact h1.trans_le hEZ_ch_lb
  have hM_ch_ge4 : 4 ≤ M_ch := by
    have hnn : 0 ≤ M_ch := hch_unm ▸ ENNReal.toReal_nonneg
    have hne0 : M_ch ≠ 0 := fun h0 ↦ by rw [h0, Real.log_zero] at hch_log2; norm_num at hch_log2
    have hpos : 0 < M_ch := lt_of_le_of_ne hnn hne0.symm
    rw [← Real.exp_log hpos]
    exact hexp2_ge4.trans (Real.exp_le_exp.mpr hch_log2)
  have hEZ_ch_ge3 : 3 ≤ ∫ G : LabeledGraph n, Z_ch G ∂randomGraphMeasure n := by
    linarith only [hEZ_ch_34, hM_ch_ge4]
  have hEZ_ch_pos : 0 < ∫ G : LabeledGraph n, Z_ch G ∂randomGraphMeasure n := by
    linarith only [hEZ_ch_ge3]
  have hM_ch_le_43 : M_ch ≤ (4 / 3 : ℝ) * ∫ G : LabeledGraph n, Z_ch G ∂randomGraphMeasure n := by
    linarith only [hEZ_ch_34]
  have hM_ch_le_sq : M_ch ≤ (∫ G : LabeledGraph n, Z_ch G ∂randomGraphMeasure n) ^ 2 := by
    calc M_ch ≤ (4 / 3 : ℝ) * ∫ G : LabeledGraph n, Z_ch G ∂randomGraphMeasure n := hM_ch_le_43
      _ ≤ (∫ G : LabeledGraph n, Z_ch G ∂randomGraphMeasure n) *
            (∫ G : LabeledGraph n, Z_ch G ∂randomGraphMeasure n) :=
          mul_le_mul_of_nonneg_right (by linarith only [hEZ_ch_ge3]) hEZ_ch_pos.le
      _ = (∫ G : LabeledGraph n, Z_ch G ∂randomGraphMeasure n) ^ 2 := (sq _).symm
  have hM_ch_sq_le : M_ch ^ 2 ≤ 2 * (∫ G : LabeledGraph n, Z_ch G ∂randomGraphMeasure n) ^ 2 := by
    calc M_ch ^ 2
        ≤ ((4 / 3 : ℝ) * ∫ G : LabeledGraph n, Z_ch G ∂randomGraphMeasure n) ^ 2 :=
          pow_le_pow_left₀ (by linarith only [hM_ch_ge4]) hM_ch_le_43 2
      _ = (16 / 9 : ℝ) * (∫ G : LabeledGraph n, Z_ch G ∂randomGraphMeasure n) ^ 2 := by ring
      _ ≤ 2 * (∫ G : LabeledGraph n, Z_ch G ∂randomGraphMeasure n) ^ 2 :=
          mul_le_mul_of_nonneg_right (by norm_num)
            (sq_nonneg (∫ G : LabeledGraph n, Z_ch G ∂randomGraphMeasure n))
  obtain ⟨W_scr_ch, W_mid_ch, hW_scr_ch_le, hW_mid_ch_le, hRel_ch_bound⟩ :=
    relPair_index_to_profile_sum_le_v13 (RelPair := RelPair_fl)
      halpha_n hL_pos S_ch P_ch_seq hP_ch_sh hch_mass hch_kp
      (fun Q Q' ↦ (randomGraphMeasure n).real (partitionColoringEvent Q ∩ partitionColoringEvent Q'))
      (fun _ _ ↦ measureReal_nonneg)
      (unmarkedDiagonalWeight n u k_ch_vec)
      (fun nu hsub ↦ by
        unfold unmarkedDiagonalWeight
        exact mul_nonneg (pow_nonneg zero_le_two _) (partialDiagonalWeight_pos n u k_ch_vec nu hsub).le)
      hEZ_ch_pos.le hM_ch_le_sq hM_ch_sq_le zero_le_one
      (Real.one_le_rpow one_le_two (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Nat.cast_nonneg _)))
      hScr_ch hMid_ch
      (fun nu hsub hge ↦
        (sum_filter_eq_of_iff_v13 _ _ (fun _ ↦ Iff.rfl)).trans_le
          (hLem72_n k_ch_vec kp_ch nu hch_mass hch_kp hsub hge S_ch P_ch_seq hP_ch_inj hP_ch_sh).1)
      ((sum_filter_eq_of_iff_v13 _ _ (fun _ ↦ Iff.rfl)).trans_le
        (by
          rw [mul_one]
          exact (hSim_n k_ch_vec kp_ch hch_mass hch_kp hch_unm hch_sgn S_ch P_ch_seq hP_ch_inj hP_ch_sh).1))
  have hEZ2_ch_tot :
      (∫ G : LabeledGraph n, (Z_ch G) ^ 2 ∂randomGraphMeasure n) ≤
        (∫ G : LabeledGraph n, Z_ch G ∂randomGraphMeasure n) ^ 2 *
          (2 * (Real.exp (C_ov * L ^ 5) * W_scr_ch + Real.exp (C_ov * L ^ 5) * W_mid_ch) +
            (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((α - (M + 1) : ℕ) : ℝ)) *
              Real.exp (13 * L ^ 5) *
              ∑ s ∈ Finset.range (k_ch + 1),
                ((k_ch : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a_max : ℝ)) *
                  (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s) :=
    hEZ2_ch_ub.trans ((sum_filter_eq_of_iff_v13 _ _ (fun _ ↦ Iff.rfl)).trans_le hRel_ch_bound)
  have hPZ_ch := (h3R_n Z_ch W_scr_ch W_mid_ch k_ch a_max z
    hZ_ch_nn hEZ_ch_pos hk_ch_le_n (Nat.sub_le _ _) le_rfl
    hW_scr_ch_le hW_mid_ch_le hEZ2_ch_tot).2
  refine hPZ_ch.trans (measureReal_mono ?_)
  intro G hG_pos
  change 0 < Z_ch G at hG_pos
  have hex_i : ∃ i ∈ S_ch, G ∈ partitionColoringEvent (P_ch_seq i) := by
    by_contra hnone
    have hz0 : Z_ch G = 0 := by
      dsimp [Z_ch]
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      rw [if_neg]; intro hm_g
      exact hnone ⟨i, hi, hm_g.1.1.1⟩
    linarith only [hG_pos, hz0]
  rcases hex_i with ⟨i, hi, hGi⟩
  exact hch_G G ⟨⟨P_ch_seq i, hP_ch_sh i hi⟩, hGi⟩

private theorem eventually_seed_beats_quasiExpTail_v13
    {c₀ : ℝ} (hc₀_pos : 0 < c₀) (C_sm : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧
      0 ≤ universalShift n ∧
      universalAllowance n = 2 * universalShift n ∧
      Real.exp (-2 * (universalShift n) ^ 2 / ((n - 1 : ℕ) : ℝ)) ≤ quasiExpTail n ∧
      Real.exp (-2 * (universalShift n) ^ 2 / ((n - 1 : ℕ) : ℝ)) <
        Real.exp (-C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) := by
  have ho : (fun x : ℝ ↦ (Real.log x) ^ ((9 : ℕ) : ℝ)) =o[atTop] (fun x : ℝ ↦ x ^ c₀) :=
    isLittleO_log_rpow_rpow_atTop ((9 : ℕ) : ℝ) hc₀_pos
  set c_eps : ℝ := 1 / (|C_sm| + 1)
  have hc_eps : 0 < c_eps := by dsimp [c_eps]; positivity
  have hb := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Asymptotics.isLittleO_iff.mp ho hc_eps)
  filter_upwards [eventually_ge_atTop 3, hb,
    tendsto_logOrder_atTop.eventually_ge_atTop 1] with n hn3 hbn hLn
  dsimp [logOrder] at hLn
  have hn2 : 2 ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hL_pos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le zero_lt_one hLn
  have ht_nn : 0 ≤ universalShift n := by unfold universalShift; positivity
  have h2t : universalAllowance n = 2 * universalShift n := by
    unfold universalAllowance universalShift; ring
  have hexp_le : Real.exp (-2 * (universalShift n) ^ 2 / ((n - 1 : ℕ) : ℝ)) ≤ quasiExpTail n := by
    unfold universalShift quasiExpTail
    apply Real.exp_le_exp.mpr
    have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
    have hn1_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    have hL10_pos : 0 < (Real.log (n : ℝ)) ^ 10 := pow_pos hL_pos 10
    rw [div_pow, ← pow_mul, show 5 * 2 = 10 by rfl, div_le_div_iff₀ hn1_pos hL10_pos]
    have h1 : -2 * ((n : ℝ) ^ 2 / (Real.log (n : ℝ)) ^ 10) * (Real.log (n : ℝ)) ^ 10 =
        -2 * (n : ℝ) ^ 2 := by
      field_simp [hL10_pos.ne']
    rw [h1]
    nlinarith
  refine ⟨hn2, ht_nn, h2t, hexp_le, lt_of_le_of_lt hexp_le ?_⟩
  unfold quasiExpTail
  apply Real.exp_lt_exp.mpr
  change ‖(Real.log (n : ℝ)) ^ ((9 : ℕ) : ℝ)‖ ≤ c_eps * ‖(n : ℝ) ^ c₀‖ at hbn
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hL_pos _),
    abs_of_pos (Real.rpow_pos_of_pos hn_pos _), Real.rpow_natCast] at hbn
  have hmul_c : (|C_sm| + 1) * (Real.log (n : ℝ)) ^ 9 ≤ (n : ℝ) ^ c₀ := by
    have h := mul_le_mul_of_nonneg_left hbn (show (0 : ℝ) ≤ |C_sm| + 1 by positivity)
    have hc_cancel : (|C_sm| + 1) * (c_eps * (n : ℝ) ^ c₀) = (n : ℝ) ^ c₀ := by
      dsimp [c_eps]; field_simp [(show (0 : ℝ) < |C_sm| + 1 by positivity).ne']
    linarith only [h, hc_cancel]
  have hstrict_log9 : C_sm * (Real.log (n : ℝ)) ^ 9 < 2 * (n : ℝ) ^ c₀ := by
    have hC_lt : C_sm < |C_sm| + 1 := lt_of_le_of_lt (le_abs_self C_sm) (by linarith)
    have hpow_pos : 0 < (Real.log (n : ℝ)) ^ 9 := pow_pos hL_pos 9
    have hrp_pos : 0 < (n : ℝ) ^ c₀ := Real.rpow_pos_of_pos hn_pos c₀
    calc C_sm * (Real.log (n : ℝ)) ^ 9
        < (|C_sm| + 1) * (Real.log (n : ℝ)) ^ 9 := mul_lt_mul_of_pos_right hC_lt hpow_pos
      _ ≤ (n : ℝ) ^ c₀ := hmul_c
      _ < 2 * (n : ℝ) ^ c₀ := by linarith only [hrp_pos]
  have hlt_div : C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ) <
      2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10 := by
    rw [div_lt_div_iff₀ hL_pos (pow_pos hL_pos 10)]
    have hn_split : (n : ℝ) ^ c₀ * (n : ℝ) ^ (1 - c₀) = (n : ℝ) := by
      rw [← Real.rpow_add hn_pos]; norm_num [Real.rpow_one]
    have hlhs : C_sm * (n : ℝ) ^ (1 - c₀) * (Real.log (n : ℝ)) ^ 10 =
        (C_sm * (Real.log (n : ℝ)) ^ 9) * ((n : ℝ) ^ (1 - c₀) * Real.log (n : ℝ)) := by ring
    have hrhs : 2 * (n : ℝ) * Real.log (n : ℝ) =
        (2 * (n : ℝ) ^ c₀) * ((n : ℝ) ^ (1 - c₀) * Real.log (n : ℝ)) := by
      calc 2 * (n : ℝ) * Real.log (n : ℝ)
          = 2 * ((n : ℝ) ^ c₀ * (n : ℝ) ^ (1 - c₀)) * Real.log (n : ℝ) := by rw [hn_split]
        _ = (2 * (n : ℝ) ^ c₀) * ((n : ℝ) ^ (1 - c₀) * Real.log (n : ℝ)) := by ring
    rw [hlhs, hrhs]
    exact mul_lt_mul_of_pos_right hstrict_log9 (mul_pos (Real.rpow_pos_of_pos hn_pos _) hL_pos)
  linarith only [hlt_div,
    show -C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ) =
      -(C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) by ring,
    show -2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10 =
      -(2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10) by ring]

/-- **Unconditional Proposition 7.3 & Corollary 8.1 in `Regime U` (`main.tex` lines 1096–1104, 1152–1160):**
for every `7 ≤ M`, `m ≤ 1`, and `δ_- ∈ (x₀, 1 + δ_*]`, there exist `C_corr > 0` and `C_sm > 0`
such that eventually whenever `δ_n + m ∈ [δ_-, 1 + δ_*]`:
1. `𝓛_{S_{m, M}}(n, ·) + (log 2) · = 0` and `𝓛_{S_{m, M}}(n, ·) = 0` have unique corridor roots `r_co, r_ch`;
2. at `k_co := ⌈r_co⌉ + 16` and `k_ch := ⌈r_ch⌉ + ⌈log n⌉`, both rare-seed lower bounds
   `P(ζ(G_n) ≤ k_co) ≥ exp(-C_sm n^(1 - c₀) / log n)` and
   `P(χ(G_n) ≤ k_ch) ≥ exp(-C_sm n^(1 - c₀) / log n)` (`c₀ = secondMomentExponent δ_-`) hold;
3. with universal allowance `a_n = 2 n / (log n)⁵`, both upper tails satisfy
   `P(ζ(G_n) > k_co + a_n) ≤ exp(-2 n / (log n)^10)` and
   `P(χ(G_n) > k_ch + a_n) ≤ exp(-2 n / (log n)^10)`. -/
theorem eventually_prop73_and_cor81_upperTails_regimeU
    {M m : ℕ} (hM : 7 ≤ M) (hm : m ≤ 1)
    {deltaMinus : ℝ} (hd : deltaMinus ∈ Set.Ioc criticalPhaseX0 (1 + deltaStar)) :
    ∃ C_corr C_sm : ℝ, 0 < C_corr ∧ 0 < C_sm ∧
      ∀ᶠ n : ℕ in atTop,
        phaseDelta n + (m : ℝ) ∈ Set.Icc deltaMinus (1 + deltaStar) →
          let c₀ : ℝ := secondMomentExponent deltaMinus
          let h_sc : ℕ → ℝ := fun i ↦
            Real.log ((phaseNat n).descFactorial i : ℝ) -
              (i : ℝ) * Real.log (phaseNat n : ℝ) -
              Real.log 2 / 2 * (i : ℝ) ^ 2
          let F_win : ℝ → ℝ := fun T ↦ ⨅ l : ℝ,
            (Real.log (∑ i ∈ Finset.Icc (m + 1) (m + M), Real.exp (l * (i : ℝ) + h_sc i)) - l * T)
          let obj_win : ℝ → ℝ → ℝ := fun tau s ↦
            (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
              s * (profileDeficitAffineA (phaseNat n) +
                profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
                F_win (fourSizeTarget n (phaseNat n) s) + tau)
          (∃! r_co : ℝ,
            r_co ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) ∧
              obj_win (Real.log 2) r_co = 0) ∧
          (∃! r_ch : ℝ,
            r_ch ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) ∧
              obj_win 0 r_ch = 0) ∧
          (∀ {r_co r_ch : ℝ},
            r_co ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) →
            obj_win (Real.log 2) r_co = 0 →
            r_ch ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) →
            obj_win 0 r_ch = 0 →
            let k_co : ℕ := Nat.ceil r_co + 16
            let k_ch : ℕ := Nat.ceil r_ch + Nat.ceil (Real.log (n : ℝ))
            Real.exp (-C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) ≤
                (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_co} ∧
              Real.exp (-C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) ≤
                (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_ch} ∧
              (randomGraphMeasure n).real
                  {G : LabeledGraph n | (k_co : ℝ) + universalAllowance n < (cochromaticNumber G : ℝ)} ≤
                quasiExpTail n ∧
              (randomGraphMeasure n).real
                  {G : LabeledGraph n | (k_ch : ℝ) + universalAllowance n < (chromaticNumberNat G : ℝ)} ≤
                quasiExpTail n) := by
  obtain ⟨⟨hx0_pos, _⟩, _⟩ := criticalPhaseX0_bounds_and_sign
  have hd_pos : 0 < deltaMinus := lt_trans (lt_of_le_of_lt (by norm_num) hx0_pos) hd.1
  set c₀ : ℝ := secondMomentExponent deltaMinus
  have hc₀_pos : 0 < c₀ := lt_min (half_pos hd_pos) (by norm_num)
  have hc₀_14 : c₀ ∈ Set.Ioo (0 : ℝ) (1 / 4) :=
    ⟨hc₀_pos, lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
  have hc₀_12 : c₀ ∈ Set.Ioo (0 : ℝ) (1 / 2) :=
    ⟨hc₀_pos, lt_trans hc₀_14.2 (by norm_num)⟩
  have hM1 : 1 ≤ M := by omega
  obtain ⟨C_ov, _, hLem72_ev⟩ := eventually_lemma72_overlapSum_le hM1 hc₀_12
  obtain ⟨C_corr, _, c_Z, _, hCc_pos, _, hcZ_pos, _, hSel_ev⟩ :=
    eventually_selectedProfiles_lemma61_and_commonClass_sums_regimeU hM hm hd C_ov
  obtain ⟨C_sm, hCsm_pos, h3R_ev⟩ :=
    eventually_threeRange_secondMoment_and_paleyZygmund M hc₀_14 C_ov 13
  refine ⟨C_corr, C_sm, hCc_pos, hCsm_pos, ?_⟩
  have halpha_ev : ∀ᶠ n : ℕ in atTop, m + M + 2 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (((m + M + 2 : ℕ) : ℝ)),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  have hcZ_big : ∀ᶠ n : ℕ in atTop,
      2 ≤ c_Z * (Real.log (n : ℝ)) ^ 2 ∧ 2 ≤ c_Z * (Real.log (n : ℝ)) ^ 3 := by
    set L_min : ℝ := max 1 (2 / c_Z + 1)
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop L_min] with n hLn
    dsimp [logOrder] at hLn
    have hL1 : 1 ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hLn
    have hLc : 2 / c_Z + 1 ≤ Real.log (n : ℝ) := (le_max_right _ _).trans hLn
    have h1 : 2 ≤ c_Z * Real.log (n : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hLc hcZ_pos.le
      have hc : c_Z * (2 / c_Z + 1) = 2 + c_Z := by field_simp [hcZ_pos.ne']
      linarith only [hm, hc, hcZ_pos]
    have hL_le2 : Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by nlinarith only [hL1]
    have hL2_le3 : (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ 3 := by
      calc (Real.log (n : ℝ)) ^ 2 = (Real.log (n : ℝ)) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (Real.log (n : ℝ)) ^ 2 * Real.log (n : ℝ) := mul_le_mul_of_nonneg_left hL1 (sq_nonneg _)
        _ = (Real.log (n : ℝ)) ^ 3 := by ring
    have hsq : 2 ≤ c_Z * (Real.log (n : ℝ)) ^ 2 :=
      h1.trans (mul_le_mul_of_nonneg_left hL_le2 hcZ_pos.le)
    exact ⟨hsq, hsq.trans (mul_le_mul_of_nonneg_left hL2_le3 hcZ_pos.le)⟩
  filter_upwards [eventually_ge_atTop 4,
    tendsto_logOrder_atTop.eventually_ge_atTop 1,
    halpha_ev, hcZ_big, hSel_ev, hLem72_ev,
    eventually_similarRange_pairSum_le hM1 hc₀_12,
    eventually_lemma71_complete_regularity M (eps := 1 / 4) (by norm_num),
    h3R_ev,
    eventually_seed_beats_quasiExpTail_v13 hc₀_pos C_sm] with
    n hn4 hL1 halpha_n ⟨hcZ2, hcZ3⟩ hSel h72 hSim h71 h3R ⟨hn2, ht_nn, h2t, hexp_le, hstrict⟩
    htd c₀' h_sc F_win obj_win
  obtain ⟨hexu_co, hexu_ch, hsel_r⟩ := hSel htd
  refine ⟨hexu_co, hexu_ch, ?_⟩
  intro r_co r_ch hr_co hobj_co hr_ch hobj_ch k_co k_ch
  obtain ⟨_, hk_co_ub, _, hk_ch_ub, k_co_vec, k_ch_vec, kp_co, kp_ch,
    hco_blk, hco_mass, hch_blk, hch_mass, _, _, hco_kp, hch_kp,
    _, _, hco_sgn, _, hco_G,
    _, _, hch_unm, _, hch_G,
    hmom_co, hmom_ch, _, _, _, _, hScr_co, hScr_ch, hMid_co, hMid_ch⟩ :=
    hsel_r hr_co hobj_co hr_ch hobj_ch
  obtain ⟨hSeed_co, hSeed_ch⟩ := secondMoment_seed_of_selected_v13
    hn4 hM1 hm halpha_n hL1 hco_mass hch_mass
    (by rwa [hco_blk]) (by rwa [hch_blk]) hco_kp hch_kp hco_sgn hch_unm
    (by rw [hco_blk]; exact hco_G) (by rw [hch_blk]; exact hch_G)
    (hcZ2.trans hmom_co) (hcZ3.trans hmom_ch)
    hScr_co hScr_ch hMid_co hMid_ch
    h71.2 (h72 hm) (hSim hm) h3R
  rw [hco_blk] at hSeed_co
  rw [hch_blk] at hSeed_ch
  refine ⟨hSeed_co, hSeed_ch, ?_, ?_⟩
  · rw [h2t]
    exact (cochromatic_upperTail_of_seed hn2 ht_nn (lt_of_lt_of_le hstrict hSeed_co)).trans hexp_le
  · rw [h2t]
    exact (chromatic_upperTail_of_seed hn2 ht_nn (lt_of_lt_of_le hstrict hSeed_ch)).trans hexp_le

/-- **Unconditional Proposition 7.3 & Corollary 8.1 in `Regime C` (`main.tex` lines 1096–1104, 1152–1160):**
for every `8 ≤ M`, `p̄₁ ∈ (0, 1/40]`, `δ_- ∈ (0, δ_*]`, and `γ > 0`, there exist `C_corr > 0` and
`C_sm > 0` such that eventually whenever `δ_n ∈ [δ_-, δ_*]` and
`g(p̄₁) + (log 2 / 2)(T_{δ_n} - 1) ≤ -γ`:
1. `𝓛_{S_{0, M}}^{=p̄₁}(n, ·) + (log 2) · = 0` and `𝓛_{S_{0, M}}^{=p̄₁}(n, ·) = 0` have unique corridor roots `r_co, r_ch`;
2. at `k_co := ⌈r_co⌉ + 16` and `k_ch := ⌈r_ch⌉ + ⌈log n⌉`, both rare-seed lower bounds
   `P(ζ(G_n) ≤ k_co) ≥ exp(-C_sm n^(1 - c₀) / log n)` and
   `P(χ(G_n) ≤ k_ch) ≥ exp(-C_sm n^(1 - c₀) / log n)` (`c₀ = secondMomentExponent δ_-`) hold;
3. with universal allowance `a_n = 2 n / (log n)⁵`, both upper tails satisfy
   `P(ζ(G_n) > k_co + a_n) ≤ exp(-2 n / (log n)^10)` and
   `P(χ(G_n) > k_ch + a_n) ≤ exp(-2 n / (log n)^10)`. -/
theorem eventually_prop73_and_cor81_upperTails_regimeC
    {M : ℕ} (hM : 8 ≤ M)
    {p1Bar : ℝ} (hp1 : p1Bar ∈ Set.Ioc (0 : ℝ) (1 / 40))
    {deltaMinus : ℝ} (hd : deltaMinus ∈ Set.Ioc (0 : ℝ) deltaStar)
    {gamma : ℝ} (hgam : 0 < gamma) :
    ∃ C_corr C_sm : ℝ, 0 < C_corr ∧ 0 < C_sm ∧
      ∀ᶠ n : ℕ in atTop,
        phaseDelta n ∈ Set.Icc deltaMinus deltaStar →
        phiInfAux p1Bar + Real.log 2 / 2 * (phaseTarget (phaseDelta n) - 1) ≤ -gamma →
          let c₀ : ℝ := secondMomentExponent deltaMinus
          let h_sc : ℕ → ℝ := fun i ↦
            Real.log ((phaseNat n).descFactorial i : ℝ) -
              (i : ℝ) * Real.log (phaseNat n : ℝ) -
              Real.log 2 / 2 * (i : ℝ) ^ 2
          let F_cap : ℝ → ℝ → ℝ := fun theta T ↦
            binEntropy theta - Real.log 2 / 2 * theta +
              (1 - theta) * (⨅ l : ℝ,
                (Real.log (∑ i ∈ Finset.Icc 2 M, Real.exp (l * (i : ℝ) + h_sc i)) -
                  l * ((T - theta) / (1 - theta))))
          let obj_cap : ℝ → ℝ → ℝ := fun tau s ↦
            (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
              s * (profileDeficitAffineA (phaseNat n) +
                profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
                F_cap p1Bar (fourSizeTarget n (phaseNat n) s) + tau)
          (∃! r_co : ℝ,
            r_co ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) ∧
              obj_cap (Real.log 2) r_co = 0) ∧
          (∃! r_ch : ℝ,
            r_ch ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) ∧
              obj_cap 0 r_ch = 0) ∧
          (∀ {r_co r_ch : ℝ},
            r_co ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) →
            obj_cap (Real.log 2) r_co = 0 →
            r_ch ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) →
            obj_cap 0 r_ch = 0 →
            let k_co : ℕ := Nat.ceil r_co + 16
            let k_ch : ℕ := Nat.ceil r_ch + Nat.ceil (Real.log (n : ℝ))
            Real.exp (-C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) ≤
                (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_co} ∧
              Real.exp (-C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) ≤
                (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_ch} ∧
              (randomGraphMeasure n).real
                  {G : LabeledGraph n | (k_co : ℝ) + universalAllowance n < (cochromaticNumber G : ℝ)} ≤
                quasiExpTail n ∧
              (randomGraphMeasure n).real
                  {G : LabeledGraph n | (k_ch : ℝ) + universalAllowance n < (chromaticNumberNat G : ℝ)} ≤
                quasiExpTail n) := by
  set c₀ : ℝ := secondMomentExponent deltaMinus
  have hc₀_pos : 0 < c₀ := lt_min (half_pos hd.1) (by norm_num)
  have hc₀_14 : c₀ ∈ Set.Ioo (0 : ℝ) (1 / 4) :=
    ⟨hc₀_pos, lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
  have hc₀_12 : c₀ ∈ Set.Ioo (0 : ℝ) (1 / 2) :=
    ⟨hc₀_pos, lt_trans hc₀_14.2 (by norm_num)⟩
  have hM1 : 1 ≤ M := by omega
  obtain ⟨C_ov, _, hLem72_ev⟩ := eventually_lemma72_overlapSum_le hM1 hc₀_12
  obtain ⟨C_corr, _, c_Z, _, hCc_pos, _, hcZ_pos, _, hSel_ev⟩ :=
    eventually_selectedProfiles_lemma61_and_commonClass_sums_regimeC hM hp1 hd hgam C_ov
  obtain ⟨C_sm, hCsm_pos, h3R_ev⟩ :=
    eventually_threeRange_secondMoment_and_paleyZygmund M hc₀_14 C_ov 13
  refine ⟨C_corr, C_sm, hCc_pos, hCsm_pos, ?_⟩
  have halpha_ev : ∀ᶠ n : ℕ in atTop, 0 + M + 2 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (((0 + M + 2 : ℕ) : ℝ)),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  have hcZ_big : ∀ᶠ n : ℕ in atTop,
      2 ≤ c_Z * (Real.log (n : ℝ)) ^ 2 ∧ 2 ≤ c_Z * (Real.log (n : ℝ)) ^ 3 := by
    set L_min : ℝ := max 1 (2 / c_Z + 1)
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop L_min] with n hLn
    dsimp [logOrder] at hLn
    have hL1 : 1 ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hLn
    have hLc : 2 / c_Z + 1 ≤ Real.log (n : ℝ) := (le_max_right _ _).trans hLn
    have h1 : 2 ≤ c_Z * Real.log (n : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hLc hcZ_pos.le
      have hc : c_Z * (2 / c_Z + 1) = 2 + c_Z := by field_simp [hcZ_pos.ne']
      linarith only [hm, hc, hcZ_pos]
    have hL_le2 : Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by nlinarith only [hL1]
    have hL2_le3 : (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ 3 := by
      calc (Real.log (n : ℝ)) ^ 2 = (Real.log (n : ℝ)) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (Real.log (n : ℝ)) ^ 2 * Real.log (n : ℝ) := mul_le_mul_of_nonneg_left hL1 (sq_nonneg _)
        _ = (Real.log (n : ℝ)) ^ 3 := by ring
    have hsq : 2 ≤ c_Z * (Real.log (n : ℝ)) ^ 2 :=
      h1.trans (mul_le_mul_of_nonneg_left hL_le2 hcZ_pos.le)
    exact ⟨hsq, hsq.trans (mul_le_mul_of_nonneg_left hL2_le3 hcZ_pos.le)⟩
  filter_upwards [eventually_ge_atTop 4,
    tendsto_logOrder_atTop.eventually_ge_atTop 1,
    halpha_ev, hcZ_big, hSel_ev, hLem72_ev,
    eventually_similarRange_pairSum_le hM1 hc₀_12,
    eventually_lemma71_complete_regularity M (eps := 1 / 4) (by norm_num),
    h3R_ev,
    eventually_seed_beats_quasiExpTail_v13 hc₀_pos C_sm] with
    n hn4 hL1 halpha_n ⟨hcZ2, hcZ3⟩ hSel h72 hSim h71 h3R ⟨hn2, ht_nn, h2t, hexp_le, hstrict⟩
    hdn hcap_gap c₀' h_sc F_cap obj_cap
  obtain ⟨hexu_co, hexu_ch, hsel_r⟩ := hSel hdn hcap_gap
  refine ⟨hexu_co, hexu_ch, ?_⟩
  intro r_co r_ch hr_co hobj_co hr_ch hobj_ch k_co k_ch
  obtain ⟨_, hk_co_ub, _, hk_ch_ub, k_co_vec, k_ch_vec, kp_co, kp_ch,
    hco_blk, hco_mass, hch_blk, hch_mass, _, _, hco_kp, hch_kp,
    _, _, hco_sgn, _, hco_G,
    _, _, hch_unm, _, hch_G,
    hmom_co, hmom_ch, _, _, _, _, hScr_co, hScr_ch, hMid_co, hMid_ch⟩ :=
    hsel_r hr_co hobj_co hr_ch hobj_ch
  have hu0 : (fun j : Fin M ↦ phaseNat n - (0 + 1 + j.1)) = fun j : Fin M ↦ phaseNat n - (1 + j.1) := rfl
  obtain ⟨hSeed_co, hSeed_ch⟩ := secondMoment_seed_of_selected_v13
    (m := 0) hn4 hM1 (Nat.zero_le 1) halpha_n hL1 hco_mass hch_mass
    (by rwa [hco_blk]) (by rwa [hch_blk]) hco_kp hch_kp hco_sgn hch_unm
    (by rw [hco_blk]; exact hco_G) (by rw [hch_blk]; exact hch_G)
    (hcZ2.trans hmom_co) (hcZ3.trans hmom_ch)
    hScr_co hScr_ch hMid_co hMid_ch
    h71.2 (h72 (Nat.zero_le 1)) (hSim (Nat.zero_le 1)) h3R
  rw [hco_blk] at hSeed_co
  rw [hch_blk] at hSeed_ch
  refine ⟨hSeed_co, hSeed_ch, ?_, ?_⟩
  · rw [h2t]
    exact (cochromatic_upperTail_of_seed hn2 ht_nn (lt_of_lt_of_le hstrict hSeed_co)).trans hexp_le
  · rw [h2t]
    exact (chromatic_upperTail_of_seed hn2 ht_nn (lt_of_lt_of_le hstrict hSeed_ch)).trans hexp_le

/-!
## 5. Complete unconditional Phase Refinement & Main Theorem (`0` external hypotheses)
-/

/-- **Unconditional Phase Refinement (`main.tex` lines 239–255, `0` external hypotheses):**
proves with **zero** hypotheses:
1. continuity, strict positivity, nonconstancy (`A₇(1 + δ_*) < A₇(δ_*)`), and uniform lower bound
   `log(391 / 200) < A₇(δ̃)` on `[δ_*, 1 + δ_*]`, together with
   `0.080 < (log 2)² / 4 · log(391 / 200) < c₇` and `C₇ < (log 2)² / 4 · log(800 / 391) < 0.086`;
2. existence of `C₁ > 0` and `ε_n ≥ 0` (`ε_n ≤ C₁ log log n / log n` for `n ≥ 3`) such that
   eventually `P((log n)³ / n · Δ(G_n) ∉ I_n) ≤ 2 exp(-n (log log n)² / (2 (log n)⁸))` and
   `(log n)³ / n · E[Δ(G_n)] ∈ I_n`;
3. for every `c' < c₇`, `C' > C₇`, and `ϑ ∈ (0, 1)` (`η₀ := min(c₇ - c', C' - C₇)`), eventual
   single-`n` and coupling-uniform tail-union bounds `≤ 2 exp(-ϑ² η₀² n / (2 (log n)⁶))` (`∃ N`
   independent of the coupling), eventual expectation bracketing, and almost-sure eventual
   bracketing `c' n / (log n)³ ≤ Δ(G_n) ≤ C' n / (log n)³`. -/
theorem erdos625_phaseRefinement_unconditional.{u} :
    let c₇ : ℝ := (Real.log 2) ^ 2 / 4 * sInf (phaseGain7 '' Set.Icc deltaStar (1 + deltaStar))
    let C₇ : ℝ := (Real.log 2) ^ 3 / 2 - c₇
    (ContinuousOn phaseGain7 (Set.Icc deltaStar (1 + deltaStar)) ∧
      phaseGain7 (1 + deltaStar) < phaseGain7 deltaStar ∧
      (∀ td ∈ Set.Icc deltaStar (1 + deltaStar),
        0 < phaseGain7 td ∧ Real.log (391 / 200) < phaseGain7 td) ∧
      80 / 1000 < (Real.log 2) ^ 2 / 4 * Real.log (391 / 200) ∧
      (Real.log 2) ^ 2 / 4 * Real.log (391 / 200) < c₇ ∧
      C₇ < (Real.log 2) ^ 2 / 4 * Real.log (800 / 391) ∧
      (Real.log 2) ^ 2 / 4 * Real.log (800 / 391) < 86 / 1000) ∧
    (∃ eps : ℕ → ℝ,
      (∃ C₁ : ℝ, 0 < C₁ ∧ (∀ n : ℕ, 0 ≤ eps n) ∧
        ∀ n : ℕ, 3 ≤ n → eps n ≤ C₁ * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) ∧
      (∀ᶠ n : ℕ in atTop,
        (randomGraphMeasure n).real
            (twoSidedGapEvent
              (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n)
              (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) n)ᶜ ≤
          2 * Real.exp (-(n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 /
            (2 * (Real.log (n : ℝ)) ^ 8))) ∧
      (∀ᶠ n : ℕ in atTop,
        lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n ≤
            (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
              (∫ G : LabeledGraph n,
                ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
                ∂randomGraphMeasure n) ∧
          (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
              (∫ G : LabeledGraph n,
                ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
                ∂randomGraphMeasure n) ≤
            upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n)) ∧
    (∀ {c' C' ϑ : ℝ}, c' < c₇ → C₇ < C' → ϑ ∈ Set.Ioo (0 : ℝ) 1 →
      let η₀ : ℝ := min (c₇ - c') (C' - C₇)
      (∀ᶠ n : ℕ in atTop,
        (randomGraphMeasure n).real (twoSidedGapEvent c' C' n)ᶜ ≤
          2 * Real.exp (-ϑ ^ 2 * η₀ ^ 2 * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6))) ∧
      (∀ᶠ n : ℕ in atTop,
        c' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) ≤
            (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ∧
          (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ≤
            C' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)) ∧
      (∃ N : ℕ,
        ∀ {Ω : Type u} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
          (G : ∀ m : ℕ, Ω → LabeledGraph m),
          (∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m) →
          (∀ n ≥ N,
            ℙ.real {ω : Ω | ∃ m ≥ n,
                (Real.log (m : ℝ)) ^ 3 / (m : ℝ) *
                  ((chromaticNumberNat (G m ω) : ℝ) - (cochromaticNumber (G m ω) : ℝ)) ∉
                  Set.Icc c' C'} ≤
              2 * Real.exp (-ϑ ^ 2 * η₀ ^ 2 * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6))) ∧
          (∀ᵐ ω ∂ℙ, ∀ᶠ n : ℕ in atTop,
            c' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) ≤
                (chromaticNumberNat (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ) ∧
              (chromaticNumberNat (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ) ≤
                C' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)))) := by
  intro c₇ C₇
  have hsub_ds : Set.Icc deltaStar (1 + deltaStar) ⊆ Set.Icc (0 : ℝ) (207 / 200) := by
    intro x hx; unfold deltaStar at hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcont_A7 : ContinuousOn phaseGain7 (Set.Icc deltaStar (1 + deltaStar)) :=
    continuousOn_phaseGain7.mono hsub_ds
  have hnonconst_A7 : phaseGain7 (1 + deltaStar) < phaseGain7 deltaStar :=
    phaseGain7_nonconstant.2.2
  have hgt_A7 : ∀ td ∈ Set.Icc deltaStar (1 + deltaStar),
      0 < phaseGain7 td ∧ Real.log (391 / 200) < phaseGain7 td := by
    intro td htd
    have hlt := log_391_div_200_lt_phaseGain7 td (hsub_ds htd)
    exact ⟨lt_trans (Real.log_pos (by norm_num)) hlt, hlt⟩
  have hd_ds : deltaStar ∈ Set.Ioc criticalPhaseX0 (1 + deltaStar) :=
    ⟨lt_trans criticalPhaseX0_bounds_and_sign.1.2 (by unfold deltaStar; norm_num),
      by unfold deltaStar; norm_num⟩
  obtain ⟨C_w0, _, hCw0_pos, _, hU0⟩ :=
    eventually_prop73_and_cor81_upperTails_regimeU (M := 7) (m := 0) le_rfl (Nat.zero_le 1) hd_ds
  obtain ⟨C_w1, _, hCw1_pos, _, hU1⟩ :=
    eventually_prop73_and_cor81_upperTails_regimeU (M := 7) (m := 1) le_rfl le_rfl hd_ds
  have hUpper7 : ∃ C_up C_w : ℝ, 0 < C_up ∧ 0 < C_w ∧
      ∀ᶠ n : ℕ in atTop,
        let m_n : ℕ := boundaryShift (phaseDelta n)
        let F_win : ℝ → ℝ := fun T ↦ ⨅ l : ℝ,
          (Real.log (∑ i ∈ Finset.Icc (m_n + 1) (m_n + 7),
              Real.exp (l * (i : ℝ) +
                (Real.log ((phaseNat n).descFactorial i : ℝ) -
                  (i : ℝ) * Real.log (phaseNat n : ℝ) -
                  Real.log 2 / 2 * (i : ℝ) ^ 2))) - l * T)
        let obj_win : ℝ → ℝ → ℝ := fun tau s ↦
          (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
            s * (profileDeficitAffineA (phaseNat n) +
              profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
              F_win (fourSizeTarget n (phaseNat n) s) + tau)
        ∃ r_winCo ∈ Set.Icc (phaseRootCenter n - C_w * logLogOrder n * phaseRootGapRadius n)
                            (phaseRootCenter n + C_w * logLogOrder n * phaseRootGapRadius n),
          obj_win (Real.log 2) r_winCo = 0 ∧
          ∃ r_win0 ∈ Set.Icc (phaseRootCenter n - C_w * logLogOrder n * phaseRootGapRadius n)
                             (phaseRootCenter n + C_w * logLogOrder n * phaseRootGapRadius n),
            obj_win 0 r_win0 = 0 ∧
            let k_co : ℕ := Nat.ceil r_winCo + 16
            let k_ch : ℕ := Nat.ceil r_win0 + Nat.ceil (Real.log (n : ℝ))
            (randomGraphMeasure n).real
                ({G : LabeledGraph n |
                    (k_co : ℝ) + universalAllowance n < (cochromaticNumber G : ℝ)} ∪
                  {G : LabeledGraph n |
                    (k_ch : ℝ) + universalAllowance n < (chromaticNumberNat G : ℝ)}) ≤
              C_up * quasiExpTail n := by
    refine ⟨2, max C_w0 C_w1, two_pos, lt_max_of_lt_left hCw0_pos, ?_⟩
    filter_upwards [hU0, hU1, eventually_phaseRoot_domain_pos_and_target_corridor,
      tendsto_logLogOrder_atTop.eventually_ge_atTop 1] with n hU0_n hU1_n hcenterDom hw1
    have hw_nn : 0 ≤ logLogOrder n * phaseRootGapRadius n := by
      unfold phaseRootGapRadius
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hcenterDom.1.1)
      exact mul_nonneg (by linarith only [hw1])
        (div_nonneg (div_nonneg hn_pos.le hcenterDom.2.1.le) (sq_nonneg _))
    have hd_ico : phaseDelta n ∈ Set.Ico (0 : ℝ) 1 := ⟨phaseDelta_nonneg n, phaseDelta_lt_one n⟩
    dsimp only
    by_cases hlt : phaseDelta n < deltaStar
    · have hm1 : boundaryShift (phaseDelta n) = 1 := by unfold boundaryShift; rw [if_pos hlt]
      have htd1 : phaseDelta n + ((1 : ℕ) : ℝ) ∈ Set.Icc deltaStar (1 + deltaStar) := by
        push_cast; unfold deltaStar at hlt ⊢; exact ⟨by linarith [hd_ico.1], by linarith⟩
      obtain ⟨⟨r_co, ⟨hr_co, hz_co⟩, _⟩, ⟨r_ch, ⟨hr_ch, hz_ch⟩, _⟩, hTails⟩ := hU1_n htd1
      obtain ⟨_, _, hco_up, hch_up⟩ := hTails hr_co hz_co hr_ch hz_ch
      have hm_le := mul_le_mul_of_nonneg_right (le_max_right C_w0 C_w1) hw_nn
      rw [hm1]
      refine ⟨r_co, ⟨by linarith [hr_co.1, hm_le], by linarith [hr_co.2, hm_le]⟩, hz_co,
        r_ch, ⟨by linarith [hr_ch.1, hm_le], by linarith [hr_ch.2, hm_le]⟩, hz_ch, ?_⟩
      exact (measureReal_union_le _ _).trans (by linarith [hco_up, hch_up])
    · have hm0 : boundaryShift (phaseDelta n) = 0 := by unfold boundaryShift; rw [if_neg hlt]
      have htd0 : phaseDelta n + ((0 : ℕ) : ℝ) ∈ Set.Icc deltaStar (1 + deltaStar) := by
        push_cast; unfold deltaStar at hlt ⊢; exact ⟨by linarith, by linarith [hd_ico.2]⟩
      obtain ⟨⟨r_co, ⟨hr_co, hz_co⟩, _⟩, ⟨r_ch, ⟨hr_ch, hz_ch⟩, _⟩, hTails⟩ := hU0_n htd0
      obtain ⟨_, _, hco_up, hch_up⟩ := hTails hr_co hz_co hr_ch hz_ch
      have hm_le := mul_le_mul_of_nonneg_right (le_max_left C_w0 C_w1) hw_nn
      rw [hm0]
      refine ⟨r_co, ⟨by linarith [hr_co.1, hm_le], by linarith [hr_co.2, hm_le]⟩, hz_co,
        r_ch, ⟨by linarith [hr_ch.1, hm_le], by linarith [hr_ch.2, hm_le]⟩, hz_ch, ?_⟩
      exact (measureReal_union_le _ _).trans (by linarith [hco_up, hch_up])
  obtain ⟨⟨hc1, hc2, hc3, hc4⟩, hmov, hfixed⟩ := phaseRefinement_v12_complete.{u} hUpper7
  exact ⟨⟨hcont_A7, hnonconst_A7, hgt_A7, hc1, hc2, hc3, hc4⟩, hmov, hfixed⟩

private theorem eventually_mu_adj_le_universalShift_v13 :
    ∀ᶠ n : ℕ in atTop,
      mu n (phaseNat n + 1) ≤ universalShift n ∧
      (phaseDelta n ≤ deltaStar → mu n (phaseNat n) ≤ universalShift n) := by
  obtain ⟨C₂, _, hC₂_pos, _, hmu_ev⟩ := exists_uniform_phaseExpansion_and_adjacent_bounds
  have ho_succ : (fun x : ℝ ↦ (Real.log x) ^ (2 / q - 1 / 2 + 5 : ℝ)) =o[atTop]
      (fun x : ℝ ↦ x ^ (1 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop _ zero_lt_one
  have hsucc_small : ∀ᶠ n : ℕ in atTop,
      C₂ * (Real.log (n : ℝ)) ^ (2 / q - 1 / 2 + 5 : ℝ) ≤ (n : ℝ) := by
    have hb := (ho_succ.comp_tendsto tendsto_natCast_atTop_atTop).bound (inv_pos.mpr hC₂_pos)
    filter_upwards [hb, eventually_gt_atTop 2] with n hn hn2
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    dsimp only [Function.comp_apply] at hn
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL_pos _),
      Real.rpow_one, Real.norm_eq_abs, abs_of_pos hn_pos] at hn
    have hm := mul_le_mul_of_nonneg_left hn hC₂_pos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hC₂_pos.ne', one_mul] at hm
  have ho_L5 : (fun x : ℝ ↦ (Real.log x) ^ ((5 : ℕ) : ℝ)) =o[atTop]
      (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop ((5 : ℕ) : ℝ) (by norm_num)
  have hL5_small : ∀ᶠ n : ℕ in atTop, (Real.log (n : ℝ)) ^ 5 ≤ Real.sqrt (n : ℝ) := by
    have hb := (ho_L5.comp_tendsto tendsto_natCast_atTop_atTop).bound zero_lt_one
    filter_upwards [hb, eventually_gt_atTop 2] with n hn hn2
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    dsimp only [Function.comp_apply] at hn
    rw [Real.rpow_natCast, Real.norm_eq_abs, abs_of_pos (pow_pos hL_pos 5), Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hn_pos _), one_mul, ← Real.sqrt_eq_rpow] at hn
    exact hn
  have hll_small : ∀ᶠ n : ℕ in atTop,
      (2 / q) * logLogOrder n + C₂ ≤ (1 / 4 : ℝ) * logOrder n := by
    have hb := logLogOrder_isLittleO_logOrder.bound
      (show (0 : ℝ) < (1 / 8) / (2 / q) by have := q_pos; positivity)
    filter_upwards [hb, tendsto_logOrder_atTop.eventually_ge_atTop (8 * C₂ + 16),
      tendsto_logLogOrder_atTop.eventually_gt_atTop 0] with n h1 hL hll
    have hL_pos : 0 < logOrder n := by linarith
    rw [Real.norm_eq_abs, abs_of_pos hll, Real.norm_eq_abs, abs_of_pos hL_pos] at h1
    have hm := mul_le_mul_of_nonneg_left h1 (div_pos two_pos q_pos).le
    have hc : (2 / q) * ((1 / 8) / (2 / q) * logOrder n) = (1 / 8 : ℝ) * logOrder n := by
      field_simp [q_pos.ne']
    rw [hc] at hm
    linarith
  filter_upwards [hmu_ev, hsucc_small, hL5_small, hll_small,
    tendsto_logOrder_atTop.eventually_ge_atTop 16, eventually_gt_atTop 2] with
    n hmu hsucc hL5 hll hL16 hn2
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  refine ⟨?_, ?_⟩
  · unfold universalShift
    rw [le_div_iff₀ (pow_pos hL_pos 5)]
    calc mu n (phaseNat n + 1) * (Real.log (n : ℝ)) ^ 5
        ≤ (C₂ * (logOrder n) ^ (2 / q - 1 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ 5 :=
          mul_le_mul_of_nonneg_right hmu.2.1 (pow_nonneg hL_pos.le 5)
      _ = C₂ * (Real.log (n : ℝ)) ^ (2 / q - 1 / 2 + 5 : ℝ) := by
          unfold logOrder
          rw [mul_assoc, ← Real.rpow_natCast (Real.log (n : ℝ)) 5, ← Real.rpow_add hL_pos]
          push_cast; rfl
      _ ≤ (n : ℝ) := hsucc
  · intro hd
    rcases eq_or_lt_of_le (mu_nonneg n (phaseNat n)) with h0 | hmu_pos
    · rw [← h0]; unfold universalShift; positivity
    · have hlog_hi := (abs_le.mp hmu.1).2
      have hd_nn : 0 ≤ phaseDelta n := phaseDelta_nonneg n
      have hll_nn : 0 ≤ logLogOrder n :=
        Real.log_nonneg (by unfold logOrder at hL16 ⊢; linarith)
      have hcoef : (2 / q - 1 / 2 - phaseDelta n) * logLogOrder n ≤ (2 / q) * logLogOrder n :=
        mul_le_mul_of_nonneg_right (by linarith) hll_nn
      have hd_L : phaseDelta n * logOrder n ≤ (1 / 4 : ℝ) * logOrder n := by
        unfold deltaStar at hd
        exact mul_le_mul_of_nonneg_right (by linarith) (by unfold logOrder; linarith)
      have hlog_le : Real.log (mu n (phaseNat n)) ≤ (1 / 2 : ℝ) * Real.log (n : ℝ) := by
        unfold logOrder at hlog_hi hd_L hll
        linarith
      have hmu_le_sqrt : mu n (phaseNat n) ≤ Real.sqrt (n : ℝ) := by
        rw [← Real.exp_log hmu_pos, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn_pos, mul_comm]
        exact Real.exp_le_exp.mpr hlog_le
      unfold universalShift
      rw [le_div_iff₀ (pow_pos hL_pos 5)]
      calc mu n (phaseNat n) * (Real.log (n : ℝ)) ^ 5
          ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
            mul_le_mul hmu_le_sqrt hL5 (pow_nonneg hL_pos.le 5) (Real.sqrt_nonneg _)
        _ = (n : ℝ) := Real.mul_self_sqrt hn_pos.le

private theorem pad_low_ii_le_v13 {n c k_low : ℕ} {r : ℝ}
    (hc : c ≤ 4) (hL_pos : 0 < Real.log (n : ℝ)) (hw1 : 1 ≤ Real.log (Real.log (n : ℝ)))
    (hmu : mu n (phaseNat n + 1) ≤ universalShift n)
    (hk_int : (k_low : ℤ) =
      ⌊r⌋ - (Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 3 / (Real.log (n : ℝ)) ^ 4) : ℤ) -
        (c : ℤ) * (Nat.ceil (mu n (phaseNat n + 1) + universalShift n) : ℤ)) :
    r - ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 3 / (Real.log (n : ℝ)) ^ 4 +
      8 * universalShift n + Real.log (n : ℝ) + 20) ≤ (k_low : ℝ) := by
  set L : ℝ := Real.log (n : ℝ)
  set ell : ℝ := Real.log L
  set t_n : ℝ := universalShift n
  have htn_nn : 0 ≤ t_n := by dsimp [t_n]; unfold universalShift; positivity
  have hk_real : (k_low : ℝ) =
      (⌊r⌋ : ℝ) - (Nat.ceil ((n : ℝ) * ell ^ 3 / L ^ 4) : ℝ) -
        (c : ℝ) * (Nat.ceil (mu n (phaseNat n + 1) + t_n) : ℝ) := by
    have h := congrArg (fun z : ℤ ↦ (z : ℝ)) hk_int
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using h
  have hfl : r - 1 ≤ (⌊r⌋ : ℝ) := (Int.sub_one_lt_floor r).le
  have hsh : (Nat.ceil ((n : ℝ) * ell ^ 3 / L ^ 4) : ℝ) ≤ (n : ℝ) * ell ^ 3 / L ^ 4 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hd_nn : 0 ≤ (Nat.ceil (mu n (phaseNat n + 1) + t_n) : ℝ) := Nat.cast_nonneg _
  have hd_le : (Nat.ceil (mu n (phaseNat n + 1) + t_n) : ℝ) ≤ 2 * t_n + 1 := by
    have h1 := (Nat.ceil_lt_add_one (add_nonneg (mu_nonneg n (phaseNat n + 1)) htn_nn)).le
    linarith only [h1, hmu]
  have hcd_le : (c : ℝ) * (Nat.ceil (mu n (phaseNat n + 1) + t_n) : ℝ) ≤ 8 * t_n + 4 := by
    have hc4 : (c : ℝ) ≤ 4 := by exact_mod_cast hc
    calc (c : ℝ) * (Nat.ceil (mu n (phaseNat n + 1) + t_n) : ℝ)
        ≤ 4 * (2 * t_n + 1) := mul_le_mul hc4 hd_le hd_nn (by norm_num)
      _ = 8 * t_n + 4 := by ring
  linarith only [hk_real, hfl, hsh, hcd_le, hL_pos, hw1]

private theorem pad_low_iii_le_v13 {n c k_low : ℕ} {r : ℝ}
    (hc : c ≤ 4) (hL_pos : 0 < Real.log (n : ℝ)) (hw1 : 1 ≤ Real.log (Real.log (n : ℝ)))
    (hmu : mu n (phaseNat n) ≤ universalShift n)
    (hk_int : (k_low : ℤ) =
      ⌊r⌋ - (Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 / (Real.log (n : ℝ)) ^ 4) : ℤ) -
        (c : ℤ) * (Nat.ceil (mu n (phaseNat n) + universalShift n) : ℤ)) :
    r - ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 3 / (Real.log (n : ℝ)) ^ 4 +
      8 * universalShift n + Real.log (n : ℝ) + 20) ≤ (k_low : ℝ) := by
  set L : ℝ := Real.log (n : ℝ)
  set ell : ℝ := Real.log L
  set t_n : ℝ := universalShift n
  have htn_nn : 0 ≤ t_n := by dsimp [t_n]; unfold universalShift; positivity
  have hk_real : (k_low : ℝ) =
      (⌊r⌋ : ℝ) - (Nat.ceil ((n : ℝ) * ell ^ 2 / L ^ 4) : ℝ) -
        (c : ℝ) * (Nat.ceil (mu n (phaseNat n) + t_n) : ℝ) := by
    have h := congrArg (fun z : ℤ ↦ (z : ℝ)) hk_int
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using h
  have hfl : r - 1 ≤ (⌊r⌋ : ℝ) := (Int.sub_one_lt_floor r).le
  have hell23 : (n : ℝ) * ell ^ 2 / L ^ 4 ≤ (n : ℝ) * ell ^ 3 / L ^ 4 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hw1 (by omega)) (Nat.cast_nonneg n)
  have hsh : (Nat.ceil ((n : ℝ) * ell ^ 2 / L ^ 4) : ℝ) ≤ (n : ℝ) * ell ^ 3 / L ^ 4 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le.trans (by linarith only [hell23])
  have hd_nn : 0 ≤ (Nat.ceil (mu n (phaseNat n) + t_n) : ℝ) := Nat.cast_nonneg _
  have hd_le : (Nat.ceil (mu n (phaseNat n) + t_n) : ℝ) ≤ 2 * t_n + 1 := by
    have h1 := (Nat.ceil_lt_add_one (add_nonneg (mu_nonneg n (phaseNat n)) htn_nn)).le
    linarith only [h1, hmu]
  have hcd_le : (c : ℝ) * (Nat.ceil (mu n (phaseNat n) + t_n) : ℝ) ≤ 8 * t_n + 4 := by
    have hc4 : (c : ℝ) ≤ 4 := by exact_mod_cast hc
    calc (c : ℝ) * (Nat.ceil (mu n (phaseNat n) + t_n) : ℝ)
        ≤ 4 * (2 * t_n + 1) := mul_le_mul hc4 hd_le hd_nn (by norm_num)
      _ = 8 * t_n + 4 := by ring
  linarith only [hk_real, hfl, hsh, hcd_le, hL_pos]

private theorem pad_up_le_v13 {n : ℕ} {r_upCo r_up0 : ℝ}
    (hr_co_nn : 0 ≤ r_upCo) (hr_0_nn : 0 ≤ r_up0)
    (hL_pos : 0 < Real.log (n : ℝ)) (hw1 : 1 ≤ Real.log (Real.log (n : ℝ))) :
    let pad_err : ℝ :=
      (n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 3 / (Real.log (n : ℝ)) ^ 4 +
        8 * universalShift n + Real.log (n : ℝ) + 20
    ((Nat.ceil r_upCo + 16 : ℕ) : ℝ) + universalAllowance n ≤ r_upCo + pad_err ∧
    ((Nat.ceil r_up0 + Nat.ceil (Real.log (n : ℝ)) : ℕ) : ℝ) + universalAllowance n ≤
      r_up0 + pad_err := by
  intro pad_err
  set L : ℝ := Real.log (n : ℝ)
  set ell : ℝ := Real.log L
  set t_n : ℝ := universalShift n
  have htn_nn : 0 ≤ t_n := by dsimp [t_n]; unfold universalShift; positivity
  have h2t : universalAllowance n = 2 * t_n := by
    dsimp [t_n]; unfold universalAllowance universalShift; ring
  have hterm_nn : 0 ≤ (n : ℝ) * ell ^ 3 / L ^ 4 := by positivity
  have hc_co : (Nat.ceil r_upCo : ℝ) ≤ r_upCo + 1 := (Nat.ceil_lt_add_one hr_co_nn).le
  have hc_0 : (Nat.ceil r_up0 : ℝ) ≤ r_up0 + 1 := (Nat.ceil_lt_add_one hr_0_nn).le
  have hc_L : (Nat.ceil L : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one hL_pos.le).le
  refine ⟨?_, ?_⟩
  · push_cast; rw [h2t]; dsimp [pad_err]
    linarith only [hc_co, hterm_nn, htn_nn, hL_pos]
  · push_cast; rw [h2t]; dsimp [pad_err]
    linarith only [hc_0, hc_L, hterm_nn, htn_nn]

private theorem bracket_prob_le_eight_quasiExpTail_v13
    {n k_chi_low k_zeta_low k_co k_ch : ℕ}
    {eps r_low0 r_lowCo r_upCo r_up0 D_low D_up K_sep pad_err : ℝ}
    (hn3 : 3 ≤ n)
    (hr_low0 : r_low0 - pad_err ≤ (k_chi_low : ℝ))
    (hr_lowCo : r_lowCo - pad_err ≤ (k_zeta_low : ℝ))
    (hr_upCo : (k_co : ℝ) + universalAllowance n ≤ r_upCo + pad_err)
    (hr_up0 : (k_ch : ℝ) + universalAllowance n ≤ r_up0 + pad_err)
    (hsep1 :
      |(r_low0 - r_upCo) - (Real.log 2) ^ 2 / 4 * (Real.log 2 + D_up - D_low) *
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)| ≤
        K_sep * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4)
    (hsep2 :
      |(r_lowCo - r_up0) - (Real.log 2) ^ 2 / 4 * (-Real.log 2 + D_up - D_low) *
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)| ≤
        K_sep * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4)
    (hdual : (Real.log 2) ^ 2 / 4 * |D_low - D_up| ≤ 2 * ((Real.log 2) ^ 3 * eps) / 3)
    (herr_small :
      (Real.log (n : ℝ)) ^ 3 / ((Real.log 2) ^ 3 * (n : ℝ)) *
        (K_sep * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4 +
          2 * pad_err) ≤ eps / 3)
    (hp_chi_low : (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi_low} ≤
      3 * quasiExpTail n)
    (hp_zeta_low : (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta_low} ≤
      3 * quasiExpTail n)
    (hp_co_up : (randomGraphMeasure n).real
      {G : LabeledGraph n | (k_co : ℝ) + universalAllowance n < (cochromaticNumber G : ℝ)} ≤
      quasiExpTail n)
    (hp_ch_up : (randomGraphMeasure n).real
      {G : LabeledGraph n | (k_ch : ℝ) + universalAllowance n < (chromaticNumberNat G : ℝ)} ≤
      quasiExpTail n) :
    (randomGraphMeasure n).real
        {G : LabeledGraph n |
          eps < |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4|} ≤
      8 * quasiExpTail n := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  set L : ℝ := Real.log (n : ℝ)
  set ell : ℝ := Real.log L
  set scaleY : ℝ := L ^ 3 / ((Real.log 2) ^ 3 * (n : ℝ))
  have hscale_pos : 0 < scaleY := by dsimp [scaleY]; positivity
  have hscale_eq : (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) = scaleY := by
    dsimp [scaleY, L]; rw [Real.logb, div_pow, div_div]
  have hd_abs := abs_le.mp (show |D_low - D_up| ≤ 8 * Real.log 2 * eps / 3 by
    have h1 : (Real.log 2) ^ 2 / 4 > 0 := by positivity
    rw [← le_div_iff₀' h1] at hdual
    refine hdual.trans_eq ?_
    field_simp [hq_pos.ne']
    ring)
  have hsub_bad :
      {G : LabeledGraph n |
        eps < |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
          ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4|} ⊆
      ({G : LabeledGraph n | chromaticNumberNat G ≤ k_chi_low} ∪
        {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta_low}) ∪
      ({G : LabeledGraph n | (k_co : ℝ) + universalAllowance n < (cochromaticNumber G : ℝ)} ∪
        {G : LabeledGraph n | (k_ch : ℝ) + universalAllowance n < (chromaticNumberNat G : ℝ)}) := by
    intro G hGbad
    by_cases h1 : chromaticNumberNat G ≤ k_chi_low
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : cochromaticNumber G ≤ k_zeta_low
      · exact Or.inl (Or.inr h2)
      · by_cases h3 : (k_co : ℝ) + universalAllowance n < (cochromaticNumber G : ℝ)
        · exact Or.inr (Or.inl h3)
        · by_cases h4 : (k_ch : ℝ) + universalAllowance n < (chromaticNumberNat G : ℝ)
          · exact Or.inr (Or.inr h4)
          · exfalso
            rw [Set.mem_setOf_eq, hscale_eq] at hGbad
            have hchi_ge : (k_chi_low : ℝ) ≤ (chromaticNumberNat G : ℝ) :=
              Nat.cast_le.mpr (not_le.mp h1).le
            have hzeta_ge : (k_zeta_low : ℝ) ≤ (cochromaticNumber G : ℝ) :=
              Nat.cast_le.mpr (not_le.mp h2).le
            have hzeta_le : (cochromaticNumber G : ℝ) ≤ (k_co : ℝ) + universalAllowance n :=
              not_lt.mp h3
            have hchi_le : (chromaticNumberNat G : ℝ) ≤ (k_ch : ℝ) + universalAllowance n :=
              not_lt.mp h4
            set E_sep : ℝ := K_sep * (n : ℝ) * ell / L ^ 4
            have hdiff_lo :
                (Real.log 2) ^ 2 / 4 * (Real.log 2 + D_up - D_low) * ((n : ℝ) / L ^ 3) -
                  (E_sep + 2 * pad_err) ≤
                (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ) := by
              have hs1 := (abs_le.mp hsep1).1
              linarith only [hchi_ge, hr_low0, hzeta_le, hr_upCo, hs1]
            have hdiff_hi :
                (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ) ≤
                (Real.log 2) ^ 2 / 4 * (Real.log 2 + D_low - D_up) * ((n : ℝ) / L ^ 3) +
                  (E_sep + 2 * pad_err) := by
              have hs2 := (abs_le.mp hsep2).1
              linarith only [hchi_le, hr_up0, hzeta_ge, hr_lowCo, hs2]
            have hm_lo := mul_le_mul_of_nonneg_left hdiff_lo hscale_pos.le
            have hm_hi := mul_le_mul_of_nonneg_left hdiff_hi hscale_pos.le
            have hc1 :
                scaleY * ((Real.log 2) ^ 2 / 4 * (Real.log 2 + D_up - D_low) * ((n : ℝ) / L ^ 3)) =
                1 / 4 + (D_up - D_low) / (4 * Real.log 2) := by
              dsimp [scaleY]; field_simp [hq_pos.ne', hn_pos.ne', hL_pos.ne']; ring
            have hc2 :
                scaleY * ((Real.log 2) ^ 2 / 4 * (Real.log 2 + D_low - D_up) * ((n : ℝ) / L ^ 3)) =
                1 / 4 + (D_low - D_up) / (4 * Real.log 2) := by
              dsimp [scaleY]; field_simp [hq_pos.ne', hn_pos.ne', hL_pos.ne']; ring
            have hd_div_lo : -(2 * eps / 3) ≤ (D_up - D_low) / (4 * Real.log 2) := by
              rw [le_div_iff₀ (by positivity)]; linarith only [hd_abs.2]
            have hd_div_hi : (D_low - D_up) / (4 * Real.log 2) ≤ 2 * eps / 3 := by
              rw [div_le_iff₀ (by positivity)]; linarith only [hd_abs.2]
            rw [mul_sub, hc1] at hm_lo
            rw [mul_add, hc2] at hm_hi
            have habs_le :
                |scaleY * ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4| ≤ eps :=
              abs_le.mpr ⟨by linarith only [hm_lo, hd_div_lo, herr_small],
                by linarith only [hm_hi, hd_div_hi, herr_small]⟩
            linarith only [hGbad, habs_le]
  calc (randomGraphMeasure n).real _
      ≤ ((randomGraphMeasure n).real {G | chromaticNumberNat G ≤ k_chi_low} +
          (randomGraphMeasure n).real {G | cochromaticNumber G ≤ k_zeta_low}) +
        ((randomGraphMeasure n).real
            {G | (k_co : ℝ) + universalAllowance n < (cochromaticNumber G : ℝ)} +
          (randomGraphMeasure n).real
            {G | (k_ch : ℝ) + universalAllowance n < (chromaticNumberNat G : ℝ)}) :=
        (measureReal_mono hsub_bad).trans
          ((measureReal_union_le _ _).trans
            (add_le_add (measureReal_union_le _ _) (measureReal_union_le _ _)))
    _ ≤ 8 * quasiExpTail n := by
        linarith only [hp_chi_low, hp_zeta_low, hp_co_up, hp_ch_up]

private theorem NormalizedGap_tail_isBigO_quasiExpTail_v13 :
    ∀ eps : ℝ, 0 < eps →
      (fun n : ℕ ↦ (randomGraphMeasure n).real
        {G : LabeledGraph n |
          eps < |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4|})
        =O[atTop] quasiExpTail := by
  intro eps heps
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨⟨hx0_lo, hx0_hi⟩, _⟩ := criticalPhaseX0_bounds_and_sign
  obtain ⟨δ₀, M_tr, M_main, a₁, M₀, N_mesh, M_cap,
    hδ₀, hM_tr, hM_main, ha₁, hM₀, hN_mesh, hM_cap,
    h_tr, h_main, h_zero, h_mesh, h_cov⟩ := exists_finite_phase_cover_dual_budget heps
  set p_tr : ℝ := capThresholdTheta (criticalPhaseX0 - 2 * δ₀)
  set θBar₀ : ℝ := capThresholdTheta (2 * a₁)
  set h : ℝ := (criticalPhaseX0 - δ₀ - a₁) / (N_mesh : ℝ)
  have ha₁_lt_ds : a₁ < deltaStar := by
    unfold deltaStar; linarith only [ha₁.2, hx0_hi, hδ₀.1]
  have hx0_sub_mem : criticalPhaseX0 - δ₀ ∈ Set.Ioc (0 : ℝ) deltaStar := by
    unfold deltaStar
    exact ⟨by linarith only [hx0_lo, hδ₀.2], by linarith only [hx0_hi, hδ₀.1]⟩
  have hx0_add_mem : criticalPhaseX0 + δ₀ ∈ Set.Ioc criticalPhaseX0 (1 + deltaStar) := by
    unfold deltaStar
    exact ⟨by linarith only [hδ₀.1], by linarith only [hx0_hi, hδ₀.2]⟩
  have h1_mem_U : (1 : ℝ) ∈ Set.Ioc criticalPhaseX0 (1 + deltaStar) := by
    unfold deltaStar; exact ⟨by linarith only [hx0_hi], by norm_num⟩
  have ha₁_mem_C : a₁ ∈ Set.Ioc (0 : ℝ) deltaStar := ⟨ha₁.1, ha₁_lt_ds.le⟩
  -- Lower-tail `Eventually` witnesses (`Prop 4.1(ii)` + `Prop 4.1(iii)` on `I₀` and mesh)
  obtain ⟨C_low_ii, hC_low_ii_pos, hLow_ii_ev⟩ := eventually_randomGraph_lowerTails_prop41_ii
  obtain ⟨C_low_zero, hC_low_zero_pos, hLow_zero_ev⟩ :=
    eventually_randomGraph_lowerTails_prop41_iii h_zero.1
      (show 0 < Real.log 2 / 4 * a₁ by have := ha₁.1; positivity)
  let hLow_mesh_ex := fun j : Fin N_mesh ↦
    eventually_randomGraph_lowerTails_prop41_iii (h_mesh.2 j).1
      (show 0 < Real.log 2 / 4 * h by have := h_mesh.1.1; positivity)
  let C_low_mesh : Fin N_mesh → ℝ := fun j ↦ (hLow_mesh_ex j).choose
  have hLow_mesh_ev := Filter.eventually_all.mpr fun j ↦ (hLow_mesh_ex j).choose_spec.2
  -- Upper-tail `Eventually` witnesses (`Cor 8.1` on `I₀`, mesh, `I_tr`, and `I_main`)
  obtain ⟨C_up_zero, _, hC_up_zero_pos, _, hUp_zero_ev⟩ :=
    eventually_prop73_and_cor81_upperTails_regimeU hM₀ le_rfl h1_mem_U
  let hUp_mesh_ex := fun j : Fin N_mesh ↦
    eventually_prop73_and_cor81_upperTails_regimeC hM_cap (h_mesh.2 j).2.1 ha₁_mem_C
      (show 0 < Real.log 2 / 2 * h by have := h_mesh.1.1; positivity)
  let C_up_mesh : Fin N_mesh → ℝ := fun j ↦ (hUp_mesh_ex j).choose
  have hUp_mesh_ev := Filter.eventually_all.mpr fun j ↦ (hUp_mesh_ex j).choose_spec.choose_spec.2.2
  obtain ⟨C_up_tr, _, hC_up_tr_pos, _, hUp_tr_ev⟩ :=
    eventually_prop73_and_cor81_upperTails_regimeC hM_tr h_tr.1 hx0_sub_mem
      (show 0 < Real.log 2 / 2 * δ₀ by have := hδ₀.1; positivity)
  obtain ⟨C_up_main, _, hC_up_main_pos, _, hUp_main_ev⟩ :=
    eventually_prop73_and_cor81_upperTails_regimeU hM_main (Nat.zero_le 1) hx0_add_mem
  -- Master corridor width `C_all` and support bound `M_max`
  have hfin_ne : (Finset.univ : Finset (Fin N_mesh)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  set C_mesh_max : ℝ := Finset.univ.sup' hfin_ne fun j ↦ max (C_low_mesh j) (C_up_mesh j)
  set C_all : ℝ := max (max (max C_low_ii C_low_zero) (max C_up_zero C_up_tr))
                       (max C_up_main C_mesh_max)
  set M_max : ℕ := max (max M_tr M_main) (max (M₀ + 1) M_cap)
  have hC_all_pos : 0 < C_all :=
    lt_max_of_lt_left (lt_max_of_lt_left (lt_max_of_lt_left hC_low_ii_pos))
  have hM_max8 : 8 ≤ M_max := le_trans hM_tr (le_trans (le_max_left _ _) (le_max_left _ _))
  obtain ⟨K_sep, hK_sep_pos, hSep_ev⟩ :=
    eventually_allSupport_corridorRoot_separation_and_prop53_iii M_max C_all hC_all_pos.le
  -- Deterministic `o(1)` error bound `err_tot n ≤ eps / 3`
  have herr_ev : ∀ᶠ n : ℕ in atTop,
      let pad_err : ℝ :=
        (n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 3 / (Real.log (n : ℝ)) ^ 4 +
          8 * universalShift n + Real.log (n : ℝ) + 20
      (Real.log (n : ℝ)) ^ 3 / ((Real.log 2) ^ 3 * (n : ℝ)) *
        (K_sep * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4 +
          2 * pad_err) ≤ eps / 3 := by
    have ho_w3 : (fun x : ℝ ↦ (Real.log x) ^ ((3 : ℕ) : ℝ)) =o[atTop] (fun x : ℝ ↦ x ^ (1 : ℝ)) :=
      isLittleO_log_rpow_rpow_atTop ((3 : ℕ) : ℝ) zero_lt_one
    set c_small : ℝ := (Real.log 2) ^ 3 * eps / (18 * (K_sep + 2))
    have hc_small_pos : 0 < c_small := by dsimp [c_small]; positivity
    have hbw := (ho_w3.comp_tendsto tendsto_logOrder_atTop).bound hc_small_pos
    have ho_L4 : (fun x : ℝ ↦ (Real.log x) ^ ((4 : ℕ) : ℝ)) =o[atTop] (fun x : ℝ ↦ x ^ (1 : ℝ)) :=
      isLittleO_log_rpow_rpow_atTop ((4 : ℕ) : ℝ) zero_lt_one
    set c_L4 : ℝ := (Real.log 2) ^ 3 * eps / 126
    have hc_L4_pos : 0 < c_L4 := by dsimp [c_L4]; positivity
    have hbL4 := (ho_L4.comp_tendsto tendsto_natCast_atTop_atTop).bound hc_L4_pos
    set L_thresh : ℝ := max 20 (Real.sqrt (144 / ((Real.log 2) ^ 3 * eps)) + 1)
    filter_upwards [eventually_ge_atTop 4,
      tendsto_logOrder_atTop.eventually_ge_atTop L_thresh,
      tendsto_logLogOrder_atTop.eventually_ge_atTop 1,
      hbw, hbL4] with n hn4 hLbig hw1 hbw_n hbL4_n
    intro pad_err
    dsimp [logOrder] at hLbig
    set L : ℝ := Real.log (n : ℝ)
    set ell : ℝ := Real.log L
    have hL20 : 20 ≤ L := (le_max_left _ _).trans hLbig
    have hL_pos : 0 < L := by linarith only [hL20]
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hell_pos : 0 < ell := lt_of_lt_of_le zero_lt_one hw1
    dsimp only [Function.comp_apply] at hbw_n hbL4_n
    change ‖ell ^ ((3 : ℕ) : ℝ)‖ ≤ c_small * ‖L ^ (1 : ℝ)‖ at hbw_n
    rw [Real.rpow_natCast, Real.rpow_one, Real.norm_eq_abs, abs_of_pos (pow_pos hell_pos 3),
      Real.norm_eq_abs, abs_of_pos hL_pos] at hbw_n
    change ‖L ^ ((4 : ℕ) : ℝ)‖ ≤ c_L4 * ‖(n : ℝ) ^ (1 : ℝ)‖ at hbL4_n
    rw [Real.rpow_natCast, Real.rpow_one, Real.norm_eq_abs, abs_of_pos (pow_pos hL_pos 4),
      Real.norm_eq_abs, abs_of_pos hn_pos] at hbL4_n
    have hell_le3 : ell ≤ ell ^ 3 := by
      calc ell = ell ^ 1 := (pow_one ell).symm
        _ ≤ ell ^ 3 := pow_le_pow_right₀ hw1 (by omega)
    -- Bound 1: `L^3 / ((log 2)^3 * n) * (K_sep * n * ell / L^4 + 2 * n * ell^3 / L^4) ≤ eps / 9`
    have hb1 : L ^ 3 / ((Real.log 2) ^ 3 * (n : ℝ)) *
        (K_sep * (n : ℝ) * ell / L ^ 4 + 2 * ((n : ℝ) * ell ^ 3 / L ^ 4)) ≤ eps / 9 := by
      have h1 : K_sep * (n : ℝ) * ell / L ^ 4 + 2 * ((n : ℝ) * ell ^ 3 / L ^ 4) ≤
          (K_sep + 2) * (n : ℝ) * ell ^ 3 / L ^ 4 := by
        have hm := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hell_le3 (mul_nonneg hK_sep_pos.le hn_pos.le)) (pow_pos hL_pos 4).le
        linarith only [hm, show (K_sep + 2) * (n : ℝ) * ell ^ 3 / L ^ 4 =
          K_sep * (n : ℝ) * ell ^ 3 / L ^ 4 + 2 * ((n : ℝ) * ell ^ 3 / L ^ 4) by ring]
      calc L ^ 3 / ((Real.log 2) ^ 3 * (n : ℝ)) *
              (K_sep * (n : ℝ) * ell / L ^ 4 + 2 * ((n : ℝ) * ell ^ 3 / L ^ 4))
          ≤ L ^ 3 / ((Real.log 2) ^ 3 * (n : ℝ)) * ((K_sep + 2) * (n : ℝ) * ell ^ 3 / L ^ 4) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (K_sep + 2) / (Real.log 2) ^ 3 * (ell ^ 3 / L) := by
            field_simp [hq_pos.ne', hn_pos.ne', hL_pos.ne']
        _ ≤ (K_sep + 2) / (Real.log 2) ^ 3 * c_small :=
            mul_le_mul_of_nonneg_left ((div_le_iff₀ hL_pos).mpr hbw_n) (by positivity)
        _ = eps / 18 := by
            dsimp [c_small]; field_simp [hq_pos.ne', (show (0 : ℝ) < K_sep + 2 by positivity).ne']
        _ ≤ eps / 9 := by linarith only [heps]
    -- Bound 2: `L^3 / ((log 2)^3 * n) * (16 * universalShift n) ≤ eps / 9`
    have hb2 : L ^ 3 / ((Real.log 2) ^ 3 * (n : ℝ)) * (16 * universalShift n) ≤ eps / 9 := by
      have hL_sq : 144 / ((Real.log 2) ^ 3 * eps) ≤ L ^ 2 := by
        have hsr : Real.sqrt (144 / ((Real.log 2) ^ 3 * eps)) ≤ L := by
          have := (le_max_right 20 _).trans hLbig; linarith only [this]
        have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsr 2
        rwa [Real.sq_sqrt (by positivity)] at hsq
      have hrew : L ^ 3 / ((Real.log 2) ^ 3 * (n : ℝ)) * (16 * universalShift n) =
          16 / ((Real.log 2) ^ 3 * L ^ 2) := by
        unfold universalShift; dsimp [L] at *; field_simp [hq_pos.ne', hn_pos.ne', hL_pos.ne']
      rw [hrew, div_le_iff₀ (by positivity)]
      have hm := mul_le_mul_of_nonneg_left hL_sq (show (0 : ℝ) ≤ eps / 9 * (Real.log 2) ^ 3 by positivity)
      have hc : eps / 9 * (Real.log 2) ^ 3 * (144 / ((Real.log 2) ^ 3 * eps)) = 16 := by
        field_simp [hq_pos.ne', heps.ne']
        norm_num
      linarith only [hm, hc, show eps / 9 * ((Real.log 2) ^ 3 * L ^ 2) =
        eps / 9 * (Real.log 2) ^ 3 * L ^ 2 by ring]
    -- Bound 3: `L^3 / ((log 2)^3 * n) * (2 * L + 40) ≤ eps / 9`
    have hb3 : L ^ 3 / ((Real.log 2) ^ 3 * (n : ℝ)) * (2 * L + 40) ≤ eps / 9 := by
      have h40 : 2 * L + 40 ≤ 4 * L := by linarith only [hL20]
      calc L ^ 3 / ((Real.log 2) ^ 3 * (n : ℝ)) * (2 * L + 40)
          ≤ L ^ 3 / ((Real.log 2) ^ 3 * (n : ℝ)) * (4 * L) :=
            mul_le_mul_of_nonneg_left h40 (by positivity)
        _ = 4 / (Real.log 2) ^ 3 * (L ^ 4 / (n : ℝ)) := by ring
        _ ≤ 4 / (Real.log 2) ^ 3 * c_L4 :=
            mul_le_mul_of_nonneg_left ((div_le_iff₀ hn_pos).mpr hbL4_n) (by positivity)
        _ = 4 * eps / 126 := by dsimp [c_L4]; field_simp [hq_pos.ne']
        _ ≤ eps / 9 := by linarith only [heps]
    have hsplit :
        L ^ 3 / ((Real.log 2) ^ 3 * (n : ℝ)) * (K_sep * (n : ℝ) * ell / L ^ 4 + 2 * pad_err) =
        L ^ 3 / ((Real.log 2) ^ 3 * (n : ℝ)) *
            (K_sep * (n : ℝ) * ell / L ^ 4 + 2 * ((n : ℝ) * ell ^ 3 / L ^ 4)) +
          L ^ 3 / ((Real.log 2) ^ 3 * (n : ℝ)) * (16 * universalShift n) +
          L ^ 3 / ((Real.log 2) ^ 3 * (n : ℝ)) * (2 * L + 40) := by
      dsimp [pad_err, L, ell]; ring
    linarith only [hsplit, hb1, hb2, hb3]
  -- Eventual positivity of all corridor elements `r ∈ Corr`
  have hcorr_nn_ev : ∀ᶠ n : ℕ in atTop,
      0 ≤ logLogOrder n * phaseRootGapRadius n ∧
      ∀ r ∈ Set.Icc (phaseRootCenter n - C_all * logLogOrder n * phaseRootGapRadius n)
                    (phaseRootCenter n + C_all * logLogOrder n * phaseRootGapRadius n),
        0 ≤ r := by
    filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      tendsto_logOrder_atTop.eventually_ge_atTop (max 4 (C_all + 1)),
      tendsto_logLogOrder_atTop.eventually_ge_atTop 1] with n hcenterDom hPh hLbig hw1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hcenterDom.1.1)
    have hs0_pos : 0 < phaseRootCenter n := div_pos hn_pos hcenterDom.2.1
    have hL_ge4 : 4 ≤ logOrder n := (le_max_left _ _).trans hLbig
    have hL_geC : C_all + 1 ≤ logOrder n := (le_max_right _ _).trans hLbig
    have hL_pos : 0 < logOrder n := by linarith only [hL_ge4]
    have hw_le_L : logLogOrder n ≤ logOrder n := by
      unfold logLogOrder; exact (Real.log_le_sub_one_of_pos hL_pos).trans (by linarith)
    have hprod_le : C_all * logLogOrder n ≤ (phaseNat n : ℝ) ^ 2 := by
      calc C_all * logLogOrder n
          ≤ logOrder n * logOrder n :=
            mul_le_mul (by linarith only [hL_geC]) hw_le_L (by linarith only [hw1]) hL_pos.le
        _ = (logOrder n) ^ 2 := (sq _).symm
        _ ≤ (phaseNat n : ℝ) ^ 2 := pow_le_pow_left₀ hL_pos.le hPh.1 2
    have ha_sq_pos : 0 < (phaseNat n : ℝ) ^ 2 := sq_pos_of_pos (lt_of_lt_of_le hL_pos hPh.1)
    have hgap_nn : 0 ≤ logLogOrder n * phaseRootGapRadius n := by
      unfold phaseRootGapRadius
      exact mul_nonneg (by linarith only [hw1]) (div_nonneg hs0_pos.le ha_sq_pos.le)
    refine ⟨hgap_nn, fun r hr ↦ ?_⟩
    have hsub_le : C_all * logLogOrder n * phaseRootGapRadius n ≤ phaseRootCenter n := by
      unfold phaseRootGapRadius
      calc C_all * logLogOrder n * (phaseRootCenter n / (phaseNat n : ℝ) ^ 2)
          = (C_all * logLogOrder n / (phaseNat n : ℝ) ^ 2) * phaseRootCenter n := by ring
        _ ≤ 1 * phaseRootCenter n :=
            mul_le_mul_of_nonneg_right ((div_le_one ha_sq_pos).mpr hprod_le) hs0_pos.le
        _ = phaseRootCenter n := one_mul _
    linarith only [hr.1, hsub_le]
  -- Assemble `=O[atTop] quasiExpTail` with uniform constant `8` across all 4 cover pieces
  refine IsBigO.of_bound 8 ?_
  filter_upwards [eventually_ge_atTop 4,
    tendsto_logOrder_atTop.eventually_ge_atTop 4,
    tendsto_logLogOrder_atTop.eventually_ge_atTop 1,
    eventually_mu_adj_le_universalShift_v13,
    hcorr_nn_ev, herr_ev, hSep_ev,
    hLow_ii_ev, hLow_zero_ev, hLow_mesh_ev,
    hUp_zero_ev, hUp_mesh_ev, hUp_tr_ev, hUp_main_ev] with
    n hn4 hL4 hw1 hMuAdj ⟨hgap_nn, hcorr_nn⟩ herr_n hSep
    hLow_ii hLow_zero hLow_mesh
    hUp_zero hUp_mesh hUp_tr hUp_main
  have hn3 : 3 ≤ n := by omega
  have hL_pos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num) hL4
  have hq_tail_pos : 0 < quasiExpTail n := by unfold quasiExpTail; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg,
    Real.norm_eq_abs, abs_of_pos hq_tail_pos]
  have htau0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.log 2) := ⟨le_rfl, hq_pos.le⟩
  have htauL : Real.log 2 ∈ Set.Icc (0 : ℝ) (Real.log 2) := ⟨hq_pos.le, le_rfl⟩
  let Corr_n : Set ℝ := Set.Icc
    (phaseRootCenter n - C_all * logLogOrder n * phaseRootGapRadius n)
    (phaseRootCenter n + C_all * logLogOrder n * phaseRootGapRadius n)
  have hsub_corr : ∀ {C' : ℝ}, C' ≤ C_all →
      Set.Icc (phaseRootCenter n - C' * logLogOrder n * phaseRootGapRadius n)
              (phaseRootCenter n + C' * logLogOrder n * phaseRootGapRadius n) ⊆ Corr_n := by
    intro C' hC' x hx
    have hm := mul_le_mul_of_nonneg_right hC' hgap_nn
    exact ⟨by linarith only [hx.1, hm], by linarith only [hx.2, hm]⟩
  have hd_ico : phaseDelta n ∈ Set.Ico (0 : ℝ) 1 := ⟨phaseDelta_nonneg n, phaseDelta_lt_one n⟩
  rcases h_cov (phaseDelta n) hd_ico with hd_zero | ⟨j, hd_j⟩ | hd_tr | hd_main
  · -- Case 1: `δ_n ∈ I₀ = [0, a₁]` (`Prop 4.1(iii)` at `θ̄₀` vs `Regime U` at `(m = 1, M = M₀)`)
    have hd_ds : phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar :=
      ⟨hd_zero.1, hd_zero.2.trans ha₁_lt_ds.le⟩
    obtain ⟨hth_le_p1, hgap_zero, hdual_zero⟩ := h_zero.2 (phaseDelta n) hd_zero
    have h2gam_zero :
        2 * (Real.log 2 / 4 * a₁) ≤
          phiInfAux θBar₀ + Real.log 2 / 2 * (phaseTarget (phaseDelta n) - 1) := by
      linarith only [hgap_zero]
    obtain ⟨⟨r_low0, ⟨hr_low0_ioo, hz_low0⟩, _⟩, ⟨r_lowCo, ⟨hr_lowCo_ioo, hz_lowCo⟩, _⟩, hLowT⟩ :=
      hLow_zero hd_ds hth_le_p1 h2gam_zero
    have hr_low0_icc := Ioo_subset_Icc_self hr_low0_ioo
    have hr_lowCo_icc := Ioo_subset_Icc_self hr_lowCo_ioo
    obtain ⟨_, _, _, hk_chi_int, hk_zeta_int, _, _, hp_chi_low, hp_zeta_low⟩ :=
      hLowT r_low0 hr_low0_icc hz_low0 r_lowCo hr_lowCo_icc hz_lowCo
    have htd1 : phaseDelta n + ((1 : ℕ) : ℝ) ∈ Set.Icc 1 (1 + deltaStar) := by
      push_cast; exact ⟨by linarith only [hd_ds.1], by linarith only [hd_ds.2]⟩
    obtain ⟨⟨r_upCo, ⟨hr_upCo_ioo, hz_upCo⟩, _⟩, ⟨r_up0, ⟨hr_up0_ioo, hz_up0⟩, _⟩, hUpT⟩ :=
      hUp_zero htd1
    obtain ⟨_, _, hp_co_up, hp_ch_up⟩ := hUpT hr_upCo_ioo hz_upCo hr_up0_ioo hz_up0
    have hC_lo_le : C_low_zero ≤ C_all :=
      (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
    have hC_up_le : C_up_zero ≤ C_all :=
      (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
    have hr_low0_all := hsub_corr hC_lo_le hr_low0_icc
    have hr_lowCo_all := hsub_corr hC_lo_le hr_lowCo_icc
    have hr_upCo_all := hsub_corr hC_up_le (Ioo_subset_Icc_self hr_upCo_ioo)
    have hr_up0_all := hsub_corr hC_up_le (Ioo_subset_Icc_self hr_up0_ioo)
    -- Rewrite `F_win 1 M₀` as `F_cap_win (M₀ + 1) 0` and `cappedDualValue (S0M (M₀ + 1)) 0`
    have hIcc_eq : Finset.Icc 2 (M₀ + 1) = Finset.Icc (1 + 1) (1 + M₀) := by
      rw [Nat.add_comm 1 M₀]
    have hF_zero_eq :
        (fun T : ℝ ↦
          binEntropy 0 - Real.log 2 / 2 * 0 +
            (1 - 0) * (⨅ l : ℝ,
              (Real.log (∑ i ∈ Finset.Icc 2 (M₀ + 1),
                  Real.exp (l * (i : ℝ) +
                    (Real.log ((phaseNat n).descFactorial i : ℝ) -
                      (i : ℝ) * Real.log (phaseNat n : ℝ) -
                      Real.log 2 / 2 * (i : ℝ) ^ 2))) -
                l * ((T - 0) / (1 - 0))))) =
        (fun T : ℝ ↦ ⨅ l : ℝ,
          (Real.log (∑ i ∈ Finset.Icc (1 + 1) (1 + M₀),
              Real.exp (l * (i : ℝ) +
                (Real.log ((phaseNat n).descFactorial i : ℝ) -
                  (i : ℝ) * Real.log (phaseNat n : ℝ) -
                  Real.log 2 / 2 * (i : ℝ) ^ 2))) - l * T)) := by
      funext T; unfold binEntropy; simp [hIcc_eq]
    have hS_diff_eq : S0M (M₀ + 1) \ {1} = shiftSupportOne (S0M M₀) := by
      ext m_idx
      simp only [S0M, shiftSupportOne, Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_singleton_iff]
      push_cast; omega
    have hdual_cap0 :
        cappedDualValue (S0M (M₀ + 1)) 0 (phaseTarget (phaseDelta n)) =
          dualValue (shiftSupportOne (S0M M₀)) (phaseTarget (phaseDelta n)) := by
      rw [cappedDualValue_zero, hS_diff_eq]
    have hM0_succ_le : M₀ + 1 ≤ M_max := (le_max_left _ _).trans (le_max_right _ _)
    have hth0_icc : θBar₀ ∈ Set.Icc (0 : ℝ) (1 / 20) := ⟨h_zero.1.1.le, h_zero.1.2⟩
    have h0_icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 20) := ⟨le_rfl, by norm_num⟩
    have hs1 := (hSep.2.1 hM_max8 hd_ds (M₀ + 1) (by omega) hM0_succ_le
      θBar₀ hth0_icc 0 h0_icc 0 htau0 (Real.log 2) htauL
      r_upCo hr_upCo_all (by
        have hFz := congrFun hF_zero_eq (fourSizeTarget n (phaseNat n) r_upCo)
        dsimp only at hFz hz_upCo ⊢; rwa [hFz])).1
      r_low0 hr_low0_all hz_low0
    have hs2 := (hSep.2.1 hM_max8 hd_ds (M₀ + 1) (by omega) hM0_succ_le
      θBar₀ hth0_icc 0 h0_icc (Real.log 2) htauL 0 htau0
      r_up0 hr_up0_all (by
        have hFz := congrFun hF_zero_eq (fourSizeTarget n (phaseNat n) r_up0)
        dsimp only at hFz hz_up0 ⊢; rwa [hFz])).1
      r_lowCo hr_lowCo_all hz_lowCo
    rw [hdual_cap0, sub_zero] at hs1
    rw [hdual_cap0, zero_sub] at hs2
    obtain ⟨hpad_upCo, hpad_up0⟩ :=
      pad_up_le_v13 (hcorr_nn _ hr_upCo_all) (hcorr_nn _ hr_up0_all) hL_pos hw1
    exact bracket_prob_le_eight_quasiExpTail_v13 hn3
      (pad_low_iii_le_v13 (c := 2) (by norm_num) hL_pos hw1 (hMuAdj.2 hd_ds.2) hk_chi_int)
      (pad_low_iii_le_v13 (c := 4) le_rfl hL_pos hw1 (hMuAdj.2 hd_ds.2) hk_zeta_int)
      hpad_upCo hpad_up0 hs1 hs2 hdual_zero.le herr_n
      hp_chi_low hp_zeta_low hp_co_up hp_ch_up
  · -- Case 2: `δ_n ∈ I_j` (`Prop 4.1(iii)` at `θ̄_j` vs `Regime C` at `(M_cap, θ̲_j)`)
    obtain ⟨hthBar_j, hthUnder_j, h_j_spec⟩ := h_mesh.2 j
    obtain ⟨hd_a1_ds, hth_le_p1, hgap_lo_j, hgap_hi_j, hdual_nn_j, hdual_lt_j⟩ :=
      h_j_spec (phaseDelta n) hd_j
    have hd_ds : phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar :=
      ⟨le_trans ha₁.1.le hd_a1_ds.1, hd_a1_ds.2⟩
    have h2gam_j :
        2 * (Real.log 2 / 4 * h) ≤
          phiInfAux (capThresholdTheta (a₁ + ((j.1 + 1 : ℕ) : ℝ) * h + h)) +
            Real.log 2 / 2 * (phaseTarget (phaseDelta n) - 1) := by
      linarith only [hgap_lo_j]
    obtain ⟨⟨r_low0, ⟨hr_low0_ioo, hz_low0⟩, _⟩, ⟨r_lowCo, ⟨hr_lowCo_ioo, hz_lowCo⟩, _⟩, hLowT⟩ :=
      hLow_mesh j hd_ds hth_le_p1 h2gam_j
    have hr_low0_icc := Ioo_subset_Icc_self hr_low0_ioo
    have hr_lowCo_icc := Ioo_subset_Icc_self hr_lowCo_ioo
    obtain ⟨_, _, _, hk_chi_int, hk_zeta_int, _, _, hp_chi_low, hp_zeta_low⟩ :=
      hLowT r_low0 hr_low0_icc hz_low0 r_lowCo hr_lowCo_icc hz_lowCo
    obtain ⟨⟨r_upCo, ⟨hr_upCo_ioo, hz_upCo⟩, _⟩, ⟨r_up0, ⟨hr_up0_ioo, hz_up0⟩, _⟩, hUpT⟩ :=
      hUp_mesh j hd_a1_ds hgap_hi_j
    obtain ⟨_, _, hp_co_up, hp_ch_up⟩ := hUpT hr_upCo_ioo hz_upCo hr_up0_ioo hz_up0
    have hC_j_le_mesh :
        max (C_low_mesh j) (C_up_mesh j) ≤ C_mesh_max :=
      Finset.le_sup' (fun i ↦ max (C_low_mesh i) (C_up_mesh i)) (Finset.mem_univ j)
    have hC_lo_le : C_low_mesh j ≤ C_all :=
      (le_max_left _ _).trans (hC_j_le_mesh.trans ((le_max_right _ _).trans (le_max_right _ _)))
    have hC_up_le : C_up_mesh j ≤ C_all :=
      (le_max_right _ _).trans (hC_j_le_mesh.trans ((le_max_right _ _).trans (le_max_right _ _)))
    have hr_low0_all := hsub_corr hC_lo_le hr_low0_icc
    have hr_lowCo_all := hsub_corr hC_lo_le hr_lowCo_icc
    have hr_upCo_all := hsub_corr hC_up_le (Ioo_subset_Icc_self hr_upCo_ioo)
    have hr_up0_all := hsub_corr hC_up_le (Ioo_subset_Icc_self hr_up0_ioo)
    have hMcap_le : M_cap ≤ M_max := (le_max_right _ _).trans (le_max_right _ _)
    have hthBar_icc : capThresholdTheta (a₁ + ((j.1 + 1 : ℕ) : ℝ) * h + h) ∈ Set.Icc 0 (1 / 20) :=
      ⟨hthBar_j.1.le, hthBar_j.2⟩
    have hthUnder_icc : capThresholdTheta (a₁ + (j.1 : ℝ) * h - h) ∈ Set.Icc 0 (1 / 20) :=
      ⟨hthUnder_j.1.le, hthUnder_j.2.trans (by norm_num)⟩
    have hs1 := (hSep.2.1 hM_max8 hd_ds M_cap hM_cap hMcap_le
      _ hthBar_icc _ hthUnder_icc 0 htau0 (Real.log 2) htauL
      r_upCo hr_upCo_all hz_upCo).1 r_low0 hr_low0_all hz_low0
    have hs2 := (hSep.2.1 hM_max8 hd_ds M_cap hM_cap hMcap_le
      _ hthBar_icc _ hthUnder_icc (Real.log 2) htauL 0 htau0
      r_up0 hr_up0_all hz_up0).1 r_lowCo hr_lowCo_all hz_lowCo
    rw [sub_zero] at hs1
    rw [zero_sub] at hs2
    have hdual_abs_j :
        (Real.log 2) ^ 2 / 4 *
          |cappedDualValue Sge1 (capThresholdTheta (a₁ + ((j.1 + 1 : ℕ) : ℝ) * h + h))
              (phaseTarget (phaseDelta n)) -
            cappedDualValue (S0M M_cap) (capThresholdTheta (a₁ + (j.1 : ℝ) * h - h))
              (phaseTarget (phaseDelta n))| ≤
        2 * ((Real.log 2) ^ 3 * eps) / 3 := by
      rw [abs_of_nonneg hdual_nn_j]; exact hdual_lt_j.le
    obtain ⟨hpad_upCo, hpad_up0⟩ :=
      pad_up_le_v13 (hcorr_nn _ hr_upCo_all) (hcorr_nn _ hr_up0_all) hL_pos hw1
    exact bracket_prob_le_eight_quasiExpTail_v13 hn3
      (pad_low_iii_le_v13 (c := 2) (by norm_num) hL_pos hw1 (hMuAdj.2 hd_ds.2) hk_chi_int)
      (pad_low_iii_le_v13 (c := 4) le_rfl hL_pos hw1 (hMuAdj.2 hd_ds.2) hk_zeta_int)
      hpad_upCo hpad_up0 hs1 hs2 hdual_abs_j herr_n
      hp_chi_low hp_zeta_low hp_co_up hp_ch_up
  · -- Case 3: `δ_n ∈ I_tr = [x₀ - δ₀, x₀ + δ₀]` (`Prop 4.1(ii)` vs `Regime C` at `(M_tr, p_tr)`)
    obtain ⟨hd_ds, hgap_tr, hdual_nn_tr, hdual_lt_tr⟩ := h_tr.2 (phaseDelta n) hd_tr
    obtain ⟨⟨r_low0, ⟨hr_low0_ioo, hz_low0⟩, _⟩, ⟨r_lowCo, ⟨hr_lowCo_ioo, hz_lowCo⟩, _⟩, hLowT⟩ :=
      hLow_ii
    have hr_low0_icc := Ioo_subset_Icc_self hr_low0_ioo
    have hr_lowCo_icc := Ioo_subset_Icc_self hr_lowCo_ioo
    obtain ⟨_, _, _, hk_chi_int, hk_zeta_int, _, _, hp_chi_low, hp_zeta_low⟩ :=
      hLowT r_low0 hr_low0_icc hz_low0 r_lowCo hr_lowCo_icc hz_lowCo
    obtain ⟨⟨r_upCo, ⟨hr_upCo_ioo, hz_upCo⟩, _⟩, ⟨r_up0, ⟨hr_up0_ioo, hz_up0⟩, _⟩, hUpT⟩ :=
      hUp_tr ⟨hd_tr.1, hd_ds.2⟩ hgap_tr
    obtain ⟨_, _, hp_co_up, hp_ch_up⟩ := hUpT hr_upCo_ioo hz_upCo hr_up0_ioo hz_up0
    have hC_lo_le : C_low_ii ≤ C_all :=
      (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
    have hC_up_le : C_up_tr ≤ C_all :=
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
    have hr_low0_all := hsub_corr hC_lo_le hr_low0_icc
    have hr_lowCo_all := hsub_corr hC_lo_le hr_lowCo_icc
    have hr_upCo_all := hsub_corr hC_up_le (Ioo_subset_Icc_self hr_upCo_ioo)
    have hr_up0_all := hsub_corr hC_up_le (Ioo_subset_Icc_self hr_up0_ioo)
    have hMtr_le : M_tr ≤ M_max := (le_max_left _ _).trans (le_max_left _ _)
    have h0_icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 20) := ⟨le_rfl, by norm_num⟩
    have hptr_icc : p_tr ∈ Set.Icc (0 : ℝ) (1 / 20) := ⟨h_tr.1.1.le, h_tr.1.2.trans (by norm_num)⟩
    have hS1_eq : {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} = Sge1 := by
      ext m_idx; simp [Sge1]
    have hs1 := (hSep.2.1 hM_max8 hd_ds M_tr hM_tr hMtr_le
      0 h0_icc p_tr hptr_icc 0 htau0 (Real.log 2) htauL
      r_upCo hr_upCo_all hz_upCo).2 1 (by omega) r_low0 hr_low0_all hz_low0
    have hs2 := (hSep.2.1 hM_max8 hd_ds M_tr hM_tr hMtr_le
      0 h0_icc p_tr hptr_icc (Real.log 2) htauL 0 htau0
      r_up0 hr_up0_all hz_up0).2 1 (by omega) r_lowCo hr_lowCo_all hz_lowCo
    rw [hS1_eq, sub_zero] at hs1
    rw [hS1_eq, zero_sub] at hs2
    have hdual_abs_tr :
        (Real.log 2) ^ 2 / 4 *
          |dualValue Sge1 (phaseTarget (phaseDelta n)) -
            cappedDualValue (S0M M_tr) p_tr (phaseTarget (phaseDelta n))| ≤
        2 * ((Real.log 2) ^ 3 * eps) / 3 := by
      rw [abs_of_nonneg hdual_nn_tr]; exact hdual_lt_tr.le
    obtain ⟨hpad_upCo, hpad_up0⟩ :=
      pad_up_le_v13 (hcorr_nn _ hr_upCo_all) (hcorr_nn _ hr_up0_all) hL_pos hw1
    exact bracket_prob_le_eight_quasiExpTail_v13 hn3
      (pad_low_ii_le_v13 (c := 2) (by norm_num) hL_pos hw1 hMuAdj.1 hk_chi_int)
      (pad_low_ii_le_v13 (c := 4) le_rfl hL_pos hw1 hMuAdj.1 hk_zeta_int)
      hpad_upCo hpad_up0 hs1 hs2 hdual_abs_tr herr_n
      hp_chi_low hp_zeta_low hp_co_up hp_ch_up
  · -- Case 4: `δ_n ∈ I_main = [x₀ + δ₀, 1)` (`Prop 4.1(ii)` vs `Regime U` at `(m = 0, M = M_main)`)
    obtain ⟨hdual_nn_m, hdual_lt_m⟩ := h_main (phaseDelta n) hd_main
    obtain ⟨⟨r_low0, ⟨hr_low0_ioo, hz_low0⟩, _⟩, ⟨r_lowCo, ⟨hr_lowCo_ioo, hz_lowCo⟩, _⟩, hLowT⟩ :=
      hLow_ii
    have hr_low0_icc := Ioo_subset_Icc_self hr_low0_ioo
    have hr_lowCo_icc := Ioo_subset_Icc_self hr_lowCo_ioo
    obtain ⟨_, _, _, hk_chi_int, hk_zeta_int, _, _, hp_chi_low, hp_zeta_low⟩ :=
      hLowT r_low0 hr_low0_icc hz_low0 r_lowCo hr_lowCo_icc hz_lowCo
    have htd_m : phaseDelta n + ((0 : ℕ) : ℝ) ∈ Set.Icc (criticalPhaseX0 + δ₀) (1 + deltaStar) := by
      push_cast; rw [add_zero]; unfold deltaStar; exact ⟨hd_main.1, by linarith only [hd_main.2]⟩
    obtain ⟨⟨r_upCo, ⟨hr_upCo_ioo, hz_upCo⟩, _⟩, ⟨r_up0, ⟨hr_up0_ioo, hz_up0⟩, _⟩, hUpT⟩ :=
      hUp_main htd_m
    obtain ⟨_, _, hp_co_up, hp_ch_up⟩ := hUpT hr_upCo_ioo hz_upCo hr_up0_ioo hz_up0
    have hC_lo_le : C_low_ii ≤ C_all :=
      (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
    have hC_up_le : C_up_main ≤ C_all :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hr_low0_all := hsub_corr hC_lo_le hr_low0_icc
    have hr_lowCo_all := hsub_corr hC_lo_le hr_lowCo_icc
    have hr_upCo_all := hsub_corr hC_up_le (Ioo_subset_Icc_self hr_upCo_ioo)
    have hr_up0_all := hsub_corr hC_up_le (Ioo_subset_Icc_self hr_up0_ioo)
    have hMmain_le : M_main ≤ M_max := (le_max_right _ _).trans (le_max_left _ _)
    have hS1_eq : {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} = Sge1 := by ext m_idx; simp [Sge1]
    have hSM_eq :
        {j : ℤ | ((0 + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((0 + M_main : ℕ) : ℤ)} = S0M M_main := by
      ext m_idx; simp [S0M]
    have hs1 := hSep.1 1 0 M_main (by omega) (Nat.zero_le 1) hM_main hMmain_le
      0 htau0 (Real.log 2) htauL r_low0 hr_low0_all r_upCo hr_upCo_all hz_low0 hz_upCo
    have hs2 := hSep.1 1 0 M_main (by omega) (Nat.zero_le 1) hM_main hMmain_le
      (Real.log 2) htauL 0 htau0 r_lowCo hr_lowCo_all r_up0 hr_up0_all hz_lowCo hz_up0
    rw [hS1_eq, hSM_eq, sub_zero] at hs1
    rw [hS1_eq, hSM_eq, zero_sub] at hs2
    have hdual_abs_m :
        (Real.log 2) ^ 2 / 4 *
          |dualValue Sge1 (phaseTarget (phaseDelta n)) -
            dualValue (S0M M_main) (phaseTarget (phaseDelta n))| ≤
        2 * ((Real.log 2) ^ 3 * eps) / 3 := by
      rw [abs_of_nonneg hdual_nn_m]; exact hdual_lt_m.le
    obtain ⟨hpad_upCo, hpad_up0⟩ :=
      pad_up_le_v13 (hcorr_nn _ hr_upCo_all) (hcorr_nn _ hr_up0_all) hL_pos hw1
    exact bracket_prob_le_eight_quasiExpTail_v13 hn3
      (pad_low_ii_le_v13 (c := 2) (by norm_num) hL_pos hw1 hMuAdj.1 hk_chi_int)
      (pad_low_ii_le_v13 (c := 4) le_rfl hL_pos hw1 hMuAdj.1 hk_zeta_int)
      hpad_upCo hpad_up0 hs1 hs2 hdual_abs_m herr_n
      hp_chi_low hp_zeta_low hp_co_up hp_ch_up

/-- **Unconditional Main Theorem `(i)–(iv)` (`main.tex` lines 99–140, `0` external hypotheses):**
proves with **zero** hypotheses all four parts `(i)–(iv)` of the Main Theorem for `G_n ∼ G(n, 1/2)`,
including:
- in `(i)`: non-asymptotic variance, CGF, sub-Gaussian tail, square-exponential moment, Orlicz `ψ₂`,
  and `L^p` bounds (`n ≥ 2`), plus for every coupling of `(G_m)_{m ≥ 2}` the running-supremum Orlicz
  `ψ₂` bound `‖sup_{m ≥ n} |Y_m - E[Y_m]|‖_{ψ₂} ≤ 4 (log₂ n)³ √((log n) / n)` (`n ≥ exp 12`), the
  `2(1/η + 1/n) n^(-η)` fluctuation tail-union bound, and the almost-sure `√(2 n log n)` envelope;
- in `(ii)`: eventual `2 exp(-ϑ² ε² n / (2 (log₂ n)⁶))` upper and lower deviations around `1/4`;
- in `(iii)`: coupling-independent `∃ N : ℕ` for `ℙ(∃ m ≥ n : |Y_m - 1/4| > ε)` and almost-sure
  convergence `(log₂ n)³ / n · (χ(G_n) - ζ(G_n)) → 1/4` (`(log n)³ / n · Δ(G_n) → (log 2)³ / 4`);
- in `(iv)`: marginal and running-supremum (`S_n := sup_{m ≥ n} |Y_m - 1/4|`) Orlicz `ψ₂` bounds and
  convergence to `0`, `E[exp(M S_n²)] → 1` & `E[exp(M (Y_n - 1/4)²)] → 1` (`M ≥ 0`), `E[S_n^p] → 0`
  & `E[|Y_n - 1/4|^p] → 0` (`1 ≤ p < ∞`), `E[Δ(G_n)] = (1/4 + o(1)) n / (log₂ n)³`, and uniform CGF
  & MGF convergence on `[-T, T]`. -/
theorem erdos625_mainTheorem_unconditional.{u₁, u₂, u₃, u₄} :
    let D : ∀ n : ℕ, LabeledGraph n → ℝ := fun _ G ↦
      (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)
    let Y : ∀ n : ℕ, LabeledGraph n → ℝ := fun n G ↦
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) * D n G
    let meanY : ℕ → ℝ := fun n ↦ ∫ H : LabeledGraph n, Y n H ∂randomGraphMeasure n
    let S_Yq : ℕ → Set ℝ := fun n ↦
      {s : ℝ | 0 < s ∧
        (∫ G : LabeledGraph n, Real.exp ((Y n G - 1 / 4) ^ 2 / s ^ 2) ∂randomGraphMeasure n) ≤ 2}
    (((∀ n : ℕ,
        (∫ G : LabeledGraph n, (D n G - ∫ H, D n H ∂randomGraphMeasure n) ^ 2
          ∂randomGraphMeasure n) ≤ ((n - 1 : ℕ) : ℝ)) ∧
      (∀ {n : ℕ}, 2 ≤ n → ∀ lam : ℝ,
        0 ≤ Real.log (∫ G : LabeledGraph n, Real.exp (lam * Y n G) ∂randomGraphMeasure n) -
            lam * meanY n ∧
          Real.log (∫ G : LabeledGraph n, Real.exp (lam * Y n G) ∂randomGraphMeasure n) -
            lam * meanY n ≤
          lam ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ))) ∧
      (∀ {n : ℕ}, 2 ≤ n → ∀ {u : ℝ}, 0 ≤ u →
        (randomGraphMeasure n).real
            {G : LabeledGraph n | u ≤ |Y n G - meanY n|} ≤
          2 * Real.exp (-u ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6))) ∧
      (∀ {n : ℕ}, 2 ≤ n → ∀ {θ : ℝ}, θ ∈ Set.Ico (0 : ℝ) (1 / 2) →
        (∫ G : LabeledGraph n,
            Real.exp (θ * (D n G - ∫ H, D n H ∂randomGraphMeasure n) ^ 2 / ((n - 1 : ℕ) : ℝ))
            ∂randomGraphMeasure n) ≤ (1 - 2 * θ) ^ (-(1 / 2 : ℝ)) ∧
        (∫ G : LabeledGraph n,
            Real.exp (θ * (n : ℝ) * (Y n G - meanY n) ^ 2 / (Real.logb 2 (n : ℝ)) ^ 6)
            ∂randomGraphMeasure n) ≤ (1 - 2 * θ) ^ (-(1 / 2 : ℝ))) ∧
      (∀ {n : ℕ}, 2 ≤ n →
        let S_D : Set ℝ := {s : ℝ | 0 < s ∧
          (∫ G : LabeledGraph n,
              Real.exp ((D n G - ∫ H, D n H ∂randomGraphMeasure n) ^ 2 / s ^ 2)
              ∂randomGraphMeasure n) ≤ 2}
        let S_Y : Set ℝ := {s : ℝ | 0 < s ∧
          (∫ G : LabeledGraph n, Real.exp ((Y n G - meanY n) ^ 2 / s ^ 2)
              ∂randomGraphMeasure n) ≤ 2}
        (S_D.Nonempty ∧ BddBelow S_D ∧
          sInf S_D ≤ Real.sqrt (8 / 3 * ((n - 1 : ℕ) : ℝ))) ∧
        (S_Y.Nonempty ∧ BddBelow S_Y ∧
          sInf S_Y ≤ Real.sqrt (8 / 3) * (Real.logb 2 (n : ℝ)) ^ 3 / Real.sqrt (n : ℝ))) ∧
      (∀ {n : ℕ}, 2 ≤ n → ∀ {p : ℝ}, 1 ≤ p →
        (∫ G : LabeledGraph n, |D n G - ∫ H, D n H ∂randomGraphMeasure n| ^ p
          ∂randomGraphMeasure n) ≤
          2 * (p / Real.exp 1 * ((n - 1 : ℕ) : ℝ)) ^ (p / 2) ∧
        (∫ G : LabeledGraph n, |Y n G - meanY n| ^ p ∂randomGraphMeasure n) ≤
          2 * (p * (Real.logb 2 (n : ℝ)) ^ 6 / (Real.exp 1 * (n : ℝ))) ^ (p / 2)) ∧
      (∀ {Ω : Type u₁} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
        (G : ∀ m : ℕ, Ω → LabeledGraph m),
        (∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m) →
        (∀ {n : ℕ}, Real.exp 12 ≤ (n : ℝ) →
          let SupCenter : Ω → ℝ := fun ω ↦ ⨆ m : {m : ℕ // n ≤ m}, |Y m.1 (G m.1 ω) - meanY m.1|
          let S_sup : Set ℝ := {s : ℝ | 0 < s ∧
            Integrable (fun ω ↦ Real.exp ((SupCenter ω) ^ 2 / s ^ 2)) ℙ ∧
            (∫ ω : Ω, Real.exp ((SupCenter ω) ^ 2 / s ^ 2) ∂ℙ) ≤ 2}
          (∀ᵐ ω ∂ℙ, BddAbove (Set.range fun m : {m : ℕ // n ≤ m} ↦ |Y m.1 (G m.1 ω) - meanY m.1|)) ∧
            AEStronglyMeasurable SupCenter ℙ ∧
            S_sup.Nonempty ∧ BddBelow S_sup ∧
            sInf S_sup ≤ 4 * (Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (Real.log (n : ℝ) / (n : ℝ))) ∧
        (∀ {n : ℕ} {η : ℝ}, 2 ≤ n → 0 < η →
          ℙ.real {ω : Ω | ∃ m ≥ n,
              Real.sqrt (2 * (1 + η) * ((m - 1 : ℕ) : ℝ) * Real.log (m : ℝ)) ≤
                |D m (G m ω) - ∫ H : LabeledGraph m, D m H ∂randomGraphMeasure m|} ≤
            2 * (1 / η + 1 / (n : ℝ)) * (n : ℝ) ^ (-η)) ∧
        ((∀ {eps : ℝ}, 0 < eps →
            ∀ᵐ ω ∂ℙ, ∀ᶠ n : ℕ in atTop,
              |D n (G n ω) - ∫ H : LabeledGraph n, D n H ∂randomGraphMeasure n| ≤
                (1 + eps) * Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ)) ∧
              |Y n (G n ω) - meanY n| ≤
                (1 + eps) * (Real.logb 2 (n : ℝ)) ^ 3 *
                  Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ))) ∧
          (∀ᵐ ω ∂ℙ,
            Filter.limsup (fun n : ℕ ↦
              ENNReal.ofReal (|D n (G n ω) - ∫ H : LabeledGraph n, D n H ∂randomGraphMeasure n| /
                Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ)))) atTop ≤ 1 ∧
            Filter.limsup (fun n : ℕ ↦
              ENNReal.ofReal (Real.sqrt (n : ℝ) /
                ((Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (2 * Real.log (n : ℝ))) *
                |Y n (G n ω) - meanY n|))
                atTop ≤ 1)))) ∧
    (∀ {eps theta : ℝ}, 0 < eps → theta ∈ Set.Ioo 0 1 →
      ∀ᶠ n : ℕ in atTop,
        (randomGraphMeasure n).real {G : LabeledGraph n | eps < |Y n G - 1 / 4|} ≤
          2 * Real.exp (-theta ^ 2 * eps ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6))) ∧
    ((∀ {eps theta : ℝ}, 0 < eps → theta ∈ Set.Ioo (0 : ℝ) 1 →
        ∃ N : ℕ,
          ∀ {Ω : Type u₂} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
            (G : ∀ m : ℕ, Ω → LabeledGraph m),
            (∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m) →
            ∀ n ≥ N,
              ℙ.real {ω : Ω | ∃ m ≥ n, eps < |Y m (G m ω) - 1 / 4|} ≤
                2 * Real.exp (-theta ^ 2 * eps ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6))) ∧
      (∀ {Ω : Type u₃} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
        (G : ∀ m : ℕ, Ω → LabeledGraph m),
        (∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m) →
        ∀ᵐ ω ∂ℙ,
          Tendsto (fun n : ℕ ↦ (Real.log n) ^ 3 / (n : ℝ) * D n (G n ω))
            atTop (nhds sharpGapConstant) ∧
          Tendsto (fun n : ℕ ↦ Y n (G n ω)) atTop (nhds (1 / 4 : ℝ)))) ∧
    ((∀ {n : ℕ}, 2 ≤ n →
        (S_Yq n).Nonempty ∧ BddBelow (S_Yq n) ∧
          sInf (S_Yq n) ≤ Real.sqrt (8 / 3) * (Real.logb 2 (n : ℝ)) ^ 3 / Real.sqrt (n : ℝ) +
            |meanY n - 1 / 4| / Real.sqrt (Real.log 2)) ∧
      Tendsto (fun n : ℕ ↦ sInf (S_Yq n)) atTop (nhds 0) ∧
      (∀ {Ω : Type u₄} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
        (G : ∀ m : ℕ, Ω → LabeledGraph m),
        (∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m) →
        let SupMeanErr : ℕ → ℝ := fun n ↦ ⨆ m : {m : ℕ // n ≤ m}, |meanY m.1 - 1 / 4|
        let SupQuarter : ℕ → Ω → ℝ := fun n ω ↦
          ⨆ m : {m : ℕ // n ≤ m}, |Y m.1 (G m.1 ω) - 1 / 4|
        let S_supQ : ℕ → Set ℝ := fun n ↦ {s : ℝ | 0 < s ∧
          Integrable (fun ω ↦ Real.exp ((SupQuarter n ω) ^ 2 / s ^ 2)) ℙ ∧
          (∫ ω : Ω, Real.exp ((SupQuarter n ω) ^ 2 / s ^ 2) ∂ℙ) ≤ 2}
        (∀ {n : ℕ}, 2 ≤ n →
          BddAbove (Set.range fun m : {m : ℕ // n ≤ m} ↦ |meanY m.1 - 1 / 4|) ∧
          (∀ᵐ ω ∂ℙ, BddAbove (Set.range fun m : {m : ℕ // n ≤ m} ↦ |Y m.1 (G m.1 ω) - 1 / 4|)) ∧
          AEStronglyMeasurable (SupQuarter n) ℙ) ∧
        (∀ {n : ℕ}, Real.exp 12 ≤ (n : ℝ) →
          (S_supQ n).Nonempty ∧ BddBelow (S_supQ n) ∧
            sInf (S_supQ n) ≤
              4 * (Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) +
                SupMeanErr n / Real.sqrt (Real.log 2)) ∧
        Tendsto (fun n : ℕ ↦ sInf (S_supQ n)) atTop (nhds 0) ∧
        (∀ {M : ℝ}, 0 ≤ M →
          (∀ᶠ n : ℕ in atTop, Integrable (fun ω ↦ Real.exp (M * (SupQuarter n ω) ^ 2)) ℙ) ∧
            Tendsto (fun n : ℕ ↦ ∫ ω : Ω, Real.exp (M * (SupQuarter n ω) ^ 2) ∂ℙ) atTop (nhds 1)) ∧
        (∀ {p : ℝ}, 1 ≤ p →
          (∀ᶠ n : ℕ in atTop, Integrable (fun ω ↦ (SupQuarter n ω) ^ p) ℙ) ∧
            Tendsto (fun n : ℕ ↦ ∫ ω : Ω, (SupQuarter n ω) ^ p ∂ℙ) atTop (nhds 0))) ∧
      (∀ {M : ℝ}, 0 ≤ M →
        Tendsto (fun n : ℕ ↦
            ∫ G : LabeledGraph n, Real.exp (M * (Y n G - 1 / 4) ^ 2) ∂randomGraphMeasure n)
          atTop (nhds 1)) ∧
      (∀ {p : ℝ}, 1 ≤ p →
        Tendsto (fun n : ℕ ↦ ∫ G : LabeledGraph n, |Y n G - 1 / 4| ^ p ∂randomGraphMeasure n)
          atTop (nhds 0)) ∧
      Tendsto (fun n : ℕ ↦
        (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
          ∫ G : LabeledGraph n, D n G ∂randomGraphMeasure n)
        atTop (nhds (1 / 4 : ℝ)) ∧
      (∀ {T : ℝ}, 0 ≤ T →
        TendstoUniformlyOn
          (fun n t ↦ Real.log (∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n))
          (fun t ↦ t / 4) atTop (Set.Icc (-T) T) ∧
        TendstoUniformlyOn
          (fun n t ↦ ∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n)
          (fun t ↦ Real.exp (t / 4)) atTop (Set.Icc (-T) T)))) := by
  intro D Y meanY S_Yq
  obtain ⟨⟨hvar, hcgf, hmean_tail, hsq_exp, hpsi2_c, hlp_c, hfluct⟩,
    hsubg, hpart3,
    ⟨hpsi2_q, hpsi2_tendsto, hsqExp_lim, hlp_q, hmean_lim, hmgf_unif⟩⟩ :=
    mainTheorem_v12_complete.{u₁, u₂, u₃} NormalizedGap_tail_isBigO_quasiExpTail_v13
  have hMeanY_lim : Tendsto meanY atTop (nhds (1 / 4 : ℝ)) :=
    hmean_lim.congr fun m ↦ (integral_const_mul _ _).symm
  refine ⟨⟨hvar, hcgf, hmean_tail, hsq_exp, hpsi2_c, hlp_c, ?_⟩, hsubg, hpart3,
    ⟨hpsi2_q, hpsi2_tendsto, ?_, hsqExp_lim, hlp_q, hmean_lim, hmgf_unif⟩⟩
  · intro Ω _ ℙ _ G hMarg
    obtain ⟨h1, h2⟩ := hfluct ℙ G hMarg
    exact ⟨fun hn12 ↦ coupling_orliczPsi2_sup_normalizedGap_center_le ℙ G hMarg hn12, h1, h2⟩
  · intro Ω _ ℙ _ G hMarg
    exact coupling_orliczPsi2_and_moments_sup_normalizedGap_sub_quarter hMeanY_lim ℙ G hMarg

end

end Erdos625HP
