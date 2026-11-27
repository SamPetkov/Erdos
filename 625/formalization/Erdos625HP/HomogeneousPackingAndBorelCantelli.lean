import Erdos625.MuVertexScaling
import Erdos625HP.CochromaticLowerTail
import Erdos625HP.ShiftedSevenSizeCertificate

/-!
# Section 1 (`lem:homogeneous-packing`) & Section 8: homogeneous `u`-packings and Borel–Cantelli

This module kernel-checks two foundational pillars of the upgraded full-sequence
`1/4` Main Theorem and Phase Refinement:

1. **Homogeneous exact-size packings `H_u(G)` (`Lemma 1.2`, eq. `(1.4)`):**
   * `maxDisjointHomogeneousEq G u`: maximum cardinality of a collection of
     pairwise disjoint `u`-subsets of `Fin n`, each inducing an independent set
     or a clique in `G`.
   * `coloring_card_filter_eq_le_maxDisjointHomogeneousEq` and
     `cocoloring_card_filter_eq_le_maxDisjointHomogeneousEq`: every proper
     colouring or cocolouring partition has at most `H_u(G)` classes of size `u`.
   * `randomGraph_maxDisjointHomogeneousEq_ge_le_factorial` and
     `randomGraph_maxDisjointHomogeneousEq_ge_le`: both inequalities in `(1.4)`
     of Lemma 1.2:
     `P(H_u(G_n) ≥ m) ≤ n! / ((n - m u)! (u!)^m m!) · 2^m · (2 ^ C(u,2))⁻ᵐ`
     `≤ (2 μ_u)^m / m! · exp (- u² / n · C(m, 2))`
     for all `1 ≤ n`, `1 ≤ u`, and `m * u ≤ n`.

2. **First Borel–Cantelli and almost-sure full-sequence convergence under every coupling:**
   * `ae_eventually_notMem_of_summable_measureReal` and
     `ae_eventually_mem_of_summable_compl`: for any probability space `(Ω, ℙ)`
     and any sequence `G : ∀ n, Ω → LabeledGraph n` with marginals
     `Measure.map (G n) ℙ = randomGraphMeasure n` (measurability is deduced
     automatically), summable failure probabilities force `G n ω ∈ E n`
     eventually almost surely.
   * `ae_eventually_twoSidedGap_of_summable_compl`: almost-sure eventual
     two-sided gap certificate (covering the Phase Refinement).
   * `ae_tendsto_normalizedGap_of_summable_failures`: summable two-sided failure
     tails around `sharpGapConstant = (log 2)³ / 4` for every `eps > 0` imply
     that under **every** joint coupling `(Ω, ℙ, G)` with `G(n, 1/2)` marginals,
     almost surely `(log n)³ / n · (χ(G_n) - ζ(G_n)) → (log 2)³ / 4` and
     `(log₂ n)³ / n · (χ(G_n) - ζ(G_n)) → 1 / 4`.
-/

namespace Erdos625HP

open Erdos625 Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

noncomputable section

set_option autoImplicit false

/-! ## 1. Homogeneous exact-size packings `H_u(G)` and class-count bounds -/

/-- A subset `A` of vertices is homogeneous in `G` if it induces an independent
set or a clique. -/
def IsHomogeneousSet {n : ℕ} (G : LabeledGraph n) (A : Finset (Fin n)) : Prop :=
  G.IsIndepSet (A : Set (Fin n)) ∨ G.IsClique (A : Set (Fin n))

/-- A family `F` of vertex subsets in `G` consists of pairwise disjoint
homogeneous subsets each of exact cardinality `u`. -/
def IsDisjointHomogeneousFamilyEq {n : ℕ} (G : LabeledGraph n) (u : ℕ)
    (F : Finset (Finset (Fin n))) : Prop :=
  (∀ A ∈ F, A.card = u ∧ IsHomogeneousSet G A) ∧
    (F : Set (Finset (Fin n))).PairwiseDisjoint id

/-- Finite set of all pairwise disjoint homogeneous `u`-set families in `G`. -/
def disjointHomogeneousFamiliesEq {n : ℕ} (G : LabeledGraph n) (u : ℕ) :
    Finset (Finset (Finset (Fin n))) := by
  classical
  exact Finset.univ.filter (IsDisjointHomogeneousFamilyEq G u)

/-- Maximum number `H_u(G)` of pairwise disjoint homogeneous `u`-subsets in `G`. -/
def maxDisjointHomogeneousEq {n : ℕ} (G : LabeledGraph n) (u : ℕ) : ℕ :=
  (disjointHomogeneousFamiliesEq G u).sup Finset.card

theorem mem_disjointHomogeneousFamiliesEq {n : ℕ} {G : LabeledGraph n} {u : ℕ}
    {F : Finset (Finset (Fin n))} :
    F ∈ disjointHomogeneousFamiliesEq G u ↔ IsDisjointHomogeneousFamilyEq G u F := by
  classical
  simp [disjointHomogeneousFamiliesEq]

theorem empty_mem_disjointHomogeneousFamiliesEq {n : ℕ} (G : LabeledGraph n) (u : ℕ) :
    ∅ ∈ disjointHomogeneousFamiliesEq G u := by
  rw [mem_disjointHomogeneousFamiliesEq]
  exact ⟨by simp, by simp⟩

theorem card_le_maxDisjointHomogeneousEq {n : ℕ} {G : LabeledGraph n} {u : ℕ}
    {F : Finset (Finset (Fin n))} (hF : IsDisjointHomogeneousFamilyEq G u F) :
    F.card ≤ maxDisjointHomogeneousEq G u :=
  Finset.le_sup (f := Finset.card) (mem_disjointHomogeneousFamiliesEq.mpr hF)

theorem exists_isDisjointHomogeneousFamilyEq_card_eq {n : ℕ}
    (G : LabeledGraph n) (u : ℕ) :
    ∃ F : Finset (Finset (Fin n)),
      IsDisjointHomogeneousFamilyEq G u F ∧
        F.card = maxDisjointHomogeneousEq G u := by
  obtain ⟨F, hFmem, hFcard⟩ :=
    Finset.exists_mem_eq_sup (disjointHomogeneousFamiliesEq G u)
      ⟨∅, empty_mem_disjointHomogeneousFamiliesEq G u⟩ Finset.card
  exact ⟨F, mem_disjointHomogeneousFamiliesEq.mp hFmem, hFcard.symm⟩

/-- Every proper colouring partition has at most `H_u(G)` classes of size `u`. -/
theorem coloring_card_filter_eq_le_maxDisjointHomogeneousEq {n u : ℕ}
    {G : LabeledGraph n} {P : VertexPartition n}
    (hG : G ∈ partitionColoringEvent P) :
    (P.parts.filter (fun B ↦ B.card = u)).card ≤ maxDisjointHomogeneousEq G u := by
  apply card_le_maxDisjointHomogeneousEq
  refine ⟨?_, ?_⟩
  · intro B hB
    rw [Finset.mem_filter] at hB
    exact ⟨hB.2, Or.inl (hG B hB.1)⟩
  · exact P.disjoint.subset fun B hB ↦ (Finset.mem_filter.mp hB).1

/-- Every cocolouring partition has at most `H_u(G)` classes of size `u`. -/
theorem cocoloring_card_filter_eq_le_maxDisjointHomogeneousEq {n u : ℕ}
    {G : LabeledGraph n} {P : VertexPartition n}
    (hG : G ∈ partitionCocoloringEvent P) :
    (P.parts.filter (fun B ↦ B.card = u)).card ≤ maxDisjointHomogeneousEq G u := by
  apply card_le_maxDisjointHomogeneousEq
  refine ⟨?_, ?_⟩
  · intro B hB
    rw [Finset.mem_filter] at hB
    exact ⟨hB.2, hG B hB.1⟩
  · exact P.disjoint.subset fun B hB ↦ (Finset.mem_filter.mp hB).1

/-! ## 2. Exact `G(n, 1/2)` probability bound for `H_u(G_n) ≥ m` (Lemma 1.2) -/

/-- Unordered families of `m` pairwise disjoint `u`-subsets of `Fin n`. -/
def IsDisjointCardFamily {n : ℕ} (u m : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  F.card = m ∧ (∀ A ∈ F, A.card = u) ∧ (F : Set (Finset (Fin n))).PairwiseDisjoint id

/-- Finite set of all `m`-element pairwise disjoint `u`-set families in `Fin n`. -/
def disjointCardFamilies (n u m : ℕ) : Finset (Finset (Finset (Fin n))) := by
  classical
  exact Finset.univ.filter (IsDisjointCardFamily u m)

theorem mem_disjointCardFamilies {n u m : ℕ} {F : Finset (Finset (Fin n))} :
    F ∈ disjointCardFamilies n u m ↔ IsDisjointCardFamily u m F := by
  classical
  simp [disjointCardFamilies]

private def familyIndepEvent {n : ℕ} (F : Finset (Finset (Fin n))) :
    Set (LabeledGraph n) :=
  {G | ∀ A ∈ F, G.IsIndepSet (A : Set (Fin n))}

private def familyMarkedEvent {n : ℕ} (F : Finset (Finset (Fin n)))
    (σ : F → Bool) : Set (LabeledGraph n) :=
  {G | ∀ A : F,
    if σ A then G.IsClique (A.1 : Set (Fin n)) else G.IsIndepSet (A.1 : Set (Fin n))}

private def familyMarkedPair {n : ℕ} (F : Finset (Finset (Fin n)))
    (σ : F → Bool) (x y : Fin n) : Prop :=
  ∃ A : F, σ A = true ∧ x ∈ A.1 ∧ y ∈ A.1

private theorem familyMarkedPair_comm {n : ℕ} (F : Finset (Finset (Fin n)))
    (σ : F → Bool) (x y : Fin n) :
    familyMarkedPair F σ x y ↔ familyMarkedPair F σ y x := by
  unfold familyMarkedPair
  constructor <;> rintro ⟨A, hσ, h1, h2⟩ <;> exact ⟨A, hσ, h2, h1⟩

private def flipFamilyAdj {n : ℕ} (F : Finset (Finset (Fin n)))
    (σ : F → Bool) (G : LabeledGraph n) (x y : Fin n) : Prop := by
  classical
  exact x ≠ y ∧ if familyMarkedPair F σ x y then ¬ G.Adj x y else G.Adj x y

private def flipFamilyInternal {n : ℕ} (F : Finset (Finset (Fin n)))
    (σ : F → Bool) (G : LabeledGraph n) : LabeledGraph n where
  Adj := flipFamilyAdj F σ G
  symm := ⟨by
    classical
    intro x y hxy
    unfold flipFamilyAdj at hxy ⊢
    refine ⟨hxy.1.symm, ?_⟩
    by_cases hm : familyMarkedPair F σ x y
    · have hmy : familyMarkedPair F σ y x := (familyMarkedPair_comm F σ x y).mp hm
      rw [if_pos hm] at hxy
      rw [if_pos hmy]
      exact fun hadj ↦ hxy.2 (G.adj_symm hadj)
    · have hmy : ¬ familyMarkedPair F σ y x :=
        fun hc ↦ hm ((familyMarkedPair_comm F σ x y).mpr hc)
      rw [if_neg hm] at hxy
      rw [if_neg hmy]
      exact G.adj_symm hxy.2⟩
  loopless := ⟨fun _ hx ↦ hx.1 rfl⟩

private theorem flipFamilyInternal_involutive {n : ℕ}
    (F : Finset (Finset (Fin n))) (σ : F → Bool) :
    Function.Involutive (flipFamilyInternal F σ) := by
  classical
  intro G
  ext x y
  change flipFamilyAdj F σ (flipFamilyInternal F σ G) x y ↔ G.Adj x y
  unfold flipFamilyAdj
  change (x ≠ y ∧
    if familyMarkedPair F σ x y then ¬ flipFamilyAdj F σ G x y
    else flipFamilyAdj F σ G x y) ↔ G.Adj x y
  unfold flipFamilyAdj
  by_cases hxy : x = y
  · subst y
    exact ⟨fun h ↦ (h.1 rfl).elim, fun h ↦ (G.ne_of_adj h rfl).elim⟩
  · by_cases hm : familyMarkedPair F σ x y <;> simp [hxy, hm]

private theorem flipFamilyInternal_mem_familyIndepEvent {n : ℕ}
    {F : Finset (Finset (Fin n))}
    (hdisj : (F : Set (Finset (Fin n))).PairwiseDisjoint id)
    {σ : F → Bool} {G : LabeledGraph n}
    (hG : G ∈ familyMarkedEvent F σ) :
    flipFamilyInternal F σ G ∈ familyIndepEvent F := by
  classical
  intro D hD x hx y hy hxy hadj
  change flipFamilyAdj F σ G x y at hadj
  unfold flipFamilyAdj at hadj
  have hxD : x ∈ D := by simpa using hx
  have hyD : y ∈ D := by simpa using hy
  have hA_eq : ∀ A : F, x ∈ A.1 → A = ⟨D, hD⟩ := by
    intro A hxA
    apply Subtype.ext
    by_contra hne
    exact (Finset.disjoint_left.mp (hdisj A.2 hD hne) hxA) hxD
  have hDspec := hG ⟨D, hD⟩
  cases hσD : σ ⟨D, hD⟩
  · simp only [hσD] at hDspec
    have hnot : ¬ familyMarkedPair F σ x y := by
      rintro ⟨A, hσA, hxA, -⟩
      rw [hA_eq A hxA, hσD] at hσA
      exact Bool.false_ne_true hσA
    have hadj_ite := hadj.2
    rw [if_neg hnot] at hadj_ite
    exact hDspec hx hy hxy hadj_ite
  · simp only [hσD, ↓reduceIte] at hDspec
    have hex : familyMarkedPair F σ x y := ⟨⟨D, hD⟩, hσD, hxD, hyD⟩
    have hadj_ite := hadj.2
    rw [if_pos hex] at hadj_ite
    exact hadj_ite (hDspec hx hy hxy)

private theorem randomGraphMeasure_familyIndepEvent {n u m : ℕ}
    {F : Finset (Finset (Fin n))} (hF : IsDisjointCardFamily u m F) :
    randomGraphMeasure n (familyIndepEvent F) =
      (1 / 2 : ENNReal) ^ (m * u.choose 2) := by
  have hev : familyIndepEvent F = {G | G ≤ (F.sup completeOn)ᶜ} := by
    ext G
    rw [familyIndepEvent, Set.mem_setOf_eq, Set.mem_setOf_eq,
      le_compl_iff_disjoint_right, Finset.disjoint_sup_right]
    exact ⟨fun h A hA ↦ (isIndepSet_iff_disjoint_completeOn G A).mp (h A hA),
      fun h A hA ↦ (isIndepSet_iff_disjoint_completeOn G A).mpr (h hA)⟩
  have hpw : (F : Set (Finset (Fin n))).PairwiseDisjoint completeOn :=
    fun A hA B hB hne ↦ disjoint_completeOn_of_disjoint (hF.2.2 hA hB hne)
  have hncard : (F.sup completeOn).edgeSet.ncard = m * u.choose 2 := by
    rw [ncard_edgeSet_finset_sup_of_pairwise F completeOn hpw]
    calc ∑ A ∈ F, (completeOn A).edgeSet.ncard
        = ∑ A ∈ F, A.card.choose 2 :=
          Finset.sum_congr rfl fun A _ ↦ ncard_edgeSet_completeOn A
      _ = ∑ _A ∈ F, u.choose 2 :=
          Finset.sum_congr rfl fun A hA ↦ by rw [hF.2.1 A hA]
      _ = m * u.choose 2 := by simp [hF.1]
  rw [hev, randomGraphMeasure_le_compl, hncard]

/-- Exact `G(n, 1/2)` probability bound for a fixed pairwise disjoint `u`-set
family `F` of size `m` to be homogeneous. -/
theorem randomGraphMeasure_familyHomogeneousEvent_le {n u m : ℕ}
    {F : Finset (Finset (Fin n))} (hF : IsDisjointCardFamily u m F) :
    randomGraphMeasure n {G | ∀ A ∈ F, IsHomogeneousSet G A} ≤
      (2 : ENNReal) ^ m * (1 / 2 : ENNReal) ^ (m * u.choose 2) := by
  classical
  have hcov : {G | ∀ A ∈ F, IsHomogeneousSet G A} ⊆
      ⋃ σ : F → Bool, familyMarkedEvent F σ := by
    intro G hG
    rw [Set.mem_iUnion]
    refine ⟨fun A ↦ decide (G.IsClique (A.1 : Set (Fin n))), ?_⟩
    intro A
    by_cases hcl : G.IsClique (A.1 : Set (Fin n))
    · simp [hcl]
    · simp only [hcl, decide_false, Bool.false_eq_true, ↓reduceIte]
      rcases hG A.1 A.2 with hind | hcl'
      · exact hind
      · exact (hcl hcl').elim
  calc randomGraphMeasure n {G | ∀ A ∈ F, IsHomogeneousSet G A}
      ≤ randomGraphMeasure n (⋃ σ : F → Bool, familyMarkedEvent F σ) :=
        measure_mono hcov
    _ ≤ ∑ σ : F → Bool, randomGraphMeasure n (familyMarkedEvent F σ) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _σ : F → Bool, randomGraphMeasure n (familyIndepEvent F) :=
        Finset.sum_le_sum fun σ _ ↦
          randomGraphMeasure_image_le_of_involutive (flipFamilyInternal F σ)
            (flipFamilyInternal_involutive F σ)
            (fun _ hG ↦ flipFamilyInternal_mem_familyIndepEvent hF.2.2 hG)
    _ = (Fintype.card (F → Bool) : ENNReal) *
          randomGraphMeasure n (familyIndepEvent F) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ = (2 : ENNReal) ^ m * (1 / 2 : ENNReal) ^ (m * u.choose 2) := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hF.1,
          randomGraphMeasure_familyIndepEvent hF]
        norm_cast

private def IsOrderedDisjointTuple {n : ℕ} (u m : ℕ)
    (T : Fin m → Finset (Fin n)) : Prop :=
  (∀ i, (T i).card = u) ∧ Pairwise (fun i j ↦ Disjoint (T i) (T j))

private def orderedDisjointTuples (n u m : ℕ) :
    Finset (Fin m → Finset (Fin n)) := by
  classical
  exact Finset.univ.filter (IsOrderedDisjointTuple u m)

private theorem mem_orderedDisjointTuples {n u m : ℕ}
    {T : Fin m → Finset (Fin n)} :
    T ∈ orderedDisjointTuples n u m ↔ IsOrderedDisjointTuple u m T := by
  classical
  simp [orderedDisjointTuples]

private theorem card_orderedDisjointTuples_le (n u m : ℕ) :
    (orderedDisjointTuples n u m).card ≤
      ∏ r ∈ Finset.range m, (n - r * u).choose u := by
  classical
  induction m with
  | zero =>
    rw [Finset.prod_range_zero]
    exact le_trans (Finset.card_le_univ _) (by simp)
  | succ m ih =>
    let S : Finset (Σ _ : Fin m → Finset (Fin n), Finset (Fin n)) :=
      (orderedDisjointTuples n u m).sigma
        (fun T₀ ↦ ((Finset.univ : Finset (Fin n)) \
          (Finset.univ : Finset (Fin m)).biUnion T₀).powersetCard u)
    let split : (Fin (m + 1) → Finset (Fin n)) →
        (Σ _ : Fin m → Finset (Fin n), Finset (Fin n)) :=
      fun T ↦ ⟨fun i ↦ T i.castSucc, T (Fin.last m)⟩
    have hinj : Function.Injective split := by
      intro T₁ T₂ h
      have h1 : (fun i : Fin m ↦ T₁ i.castSucc) = (fun i : Fin m ↦ T₂ i.castSucc) :=
        congrArg Sigma.fst h
      have h2 : T₁ (Fin.last m) = T₂ (Fin.last m) := congrArg Sigma.snd h
      funext j
      refine Fin.lastCases h2 (fun i ↦ ?_) j
      exact congrFun h1 i
    have himg : (orderedDisjointTuples n u (m + 1)).image split ⊆ S := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨T, hT, rfl⟩
      rw [mem_orderedDisjointTuples] at hT
      rw [Finset.mem_sigma, mem_orderedDisjointTuples, Finset.mem_powersetCard]
      refine ⟨⟨fun i ↦ hT.1 i.castSucc, ?_⟩, ?_, hT.1 (Fin.last m)⟩
      · intro i j hij
        exact hT.2 (fun h ↦ hij (Fin.castSucc_inj.mp h))
      · intro x hx
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ x, ?_⟩
        intro hxU
        rw [Finset.mem_biUnion] at hxU
        rcases hxU with ⟨i, -, hxi⟩
        have hne : i.castSucc ≠ Fin.last m := (Fin.castSucc_lt_last i).ne
        exact (Finset.disjoint_left.mp (hT.2 hne) hxi) hx
    have hcard_le : (orderedDisjointTuples n u (m + 1)).card ≤ S.card := by
      rw [← Finset.card_image_of_injective _ hinj]
      exact Finset.card_le_card himg
    have hScard : S.card =
        (orderedDisjointTuples n u m).card * (n - m * u).choose u := by
      rw [Finset.card_sigma]
      have hfib : ∀ T₀ ∈ orderedDisjointTuples n u m,
          (((Finset.univ : Finset (Fin n)) \
            (Finset.univ : Finset (Fin m)).biUnion T₀).powersetCard u).card =
            (n - m * u).choose u := by
        intro T₀ hT₀
        rw [mem_orderedDisjointTuples] at hT₀
        rw [Finset.card_powersetCard]
        have hpw : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint T₀ :=
          fun i _ j _ hij ↦ hT₀.2 hij
        have hUcard : ((Finset.univ : Finset (Fin m)).biUnion T₀).card = m * u := by
          rw [Finset.card_biUnion hpw]
          calc ∑ i : Fin m, (T₀ i).card
              = ∑ _i : Fin m, u := Finset.sum_congr rfl fun i _ ↦ hT₀.1 i
            _ = m * u := by simp
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
          Finset.card_univ, Fintype.card_fin, hUcard]
      rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
    rw [Finset.prod_range_succ]
    exact le_trans hcard_le (by rw [hScard]; exact Nat.mul_le_mul_right _ ih)

/-- Unordered disjoint `u`-set families of size `m` satisfy
`|disjointCardFamilies n u m| * m! ≤ ∏_{r < m} C(n - r u, u)`. -/
theorem card_disjointCardFamilies_mul_factorial_le (n u m : ℕ) :
    (disjointCardFamilies n u m).card * m.factorial ≤
      ∏ r ∈ Finset.range m, (n - r * u).choose u := by
  classical
  let enumOf (F : disjointCardFamilies n u m) : Fin m ≃ F.1 :=
    Fintype.equivOfCardEq (by simp [(mem_disjointCardFamilies.mp F.2).1])
  let g : disjointCardFamilies n u m × Equiv.Perm (Fin m) →
      orderedDisjointTuples n u m := fun ⟨F, π⟩ ↦
    ⟨fun i ↦ (enumOf F (π i)).1, by
      rw [mem_orderedDisjointTuples]
      have hF := mem_disjointCardFamilies.mp F.2
      refine ⟨fun i ↦ hF.2.1 _ (enumOf F (π i)).2, ?_⟩
      intro i j hij
      have hne_sub : enumOf F (π i) ≠ enumOf F (π j) :=
        fun h ↦ hij (π.injective ((enumOf F).injective h))
      have hne_val : (enumOf F (π i)).1 ≠ (enumOf F (π j)).1 :=
        fun h ↦ hne_sub (Subtype.ext h)
      exact hF.2.2 (enumOf F (π i)).2 (enumOf F (π j)).2 hne_val⟩
  have himg_eq (F : disjointCardFamilies n u m) (π : Equiv.Perm (Fin m)) :
      (Finset.univ : Finset (Fin m)).image (fun i ↦ (enumOf F (π i)).1) = F.1 := by
    ext A
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (enumOf F (π i)).2
    · intro hA
      refine ⟨π.symm ((enumOf F).symm ⟨A, hA⟩), ?_⟩
      simp
  have hinj : Function.Injective g := by
    rintro ⟨F₁, π₁⟩ ⟨F₂, π₂⟩ h
    have hfun : (fun i ↦ (enumOf F₁ (π₁ i)).1) = (fun i ↦ (enumOf F₂ (π₂ i)).1) :=
      congrArg Subtype.val h
    have hF_eq : F₁ = F₂ := by
      apply Subtype.ext
      rw [← himg_eq F₁ π₁, ← himg_eq F₂ π₂, hfun]
    subst hF_eq
    congr 1
    apply Equiv.ext
    intro i
    have hi := congrFun hfun i
    have hsub : enumOf F₁ (π₁ i) = enumOf F₁ (π₂ i) := Subtype.ext hi
    exact (enumOf F₁).injective hsub
  have hcard : Fintype.card (disjointCardFamilies n u m × Equiv.Perm (Fin m)) ≤
      Fintype.card (orderedDisjointTuples n u m) :=
    Fintype.card_le_of_injective g hinj
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_perm, Fintype.card_fin,
    Fintype.card_coe] at hcard
  exact le_trans hcard (card_orderedDisjointTuples_le n u m)

private theorem prod_choose_mul_factorial_eq {n u m : ℕ} (hmu : m * u ≤ n) :
    (∏ r ∈ Finset.range m, (n - r * u).choose u) *
        (u.factorial ^ m * (n - m * u).factorial) =
      n.factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hmu' : m * u ≤ n := by
      calc m * u ≤ m * u + u := Nat.le_add_right _ _
        _ = (m + 1) * u := by ring
        _ ≤ n := hmu
    have hu_le : u ≤ n - m * u := by
      have : m * u + u ≤ n := by simpa [Nat.succ_mul] using hmu
      omega
    have hsub_eq : n - m * u - u = n - (m + 1) * u := by
      rw [Nat.sub_sub, Nat.succ_mul]
    have hstep : (n - m * u).choose u * u.factorial * (n - (m + 1) * u).factorial =
        (n - m * u).factorial := by
      rw [← hsub_eq]
      exact Nat.choose_mul_factorial_mul_factorial hu_le
    rw [Finset.prod_range_succ, pow_succ]
    calc ((∏ r ∈ Finset.range m, (n - r * u).choose u) * (n - m * u).choose u) *
            (u.factorial ^ m * u.factorial * (n - (m + 1) * u).factorial)
        = (∏ r ∈ Finset.range m, (n - r * u).choose u) *
            (u.factorial ^ m *
              ((n - m * u).choose u * u.factorial * (n - (m + 1) * u).factorial)) := by ring
      _ = (∏ r ∈ Finset.range m, (n - r * u).choose u) *
            (u.factorial ^ m * (n - m * u).factorial) := by rw [hstep]
      _ = n.factorial := ih hmu'

private theorem sum_range_cast_eq_choose_two (m : ℕ) :
    (∑ r ∈ Finset.range m, (r : ℝ)) = (m.choose 2 : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, chooseTwo_succ, Nat.cast_add]

private theorem maxDisjointHomogeneousEq_ge_le_prod {n u m : ℕ} :
    (randomGraphMeasure n).real {G | m ≤ maxDisjointHomogeneousEq G u} ≤
      ((∏ r ∈ Finset.range m, ((n - r * u).choose u : ℝ)) / (m.factorial : ℝ)) *
        (2 : ℝ) ^ m * (((2 : ℝ) ^ (u.choose 2))⁻¹) ^ m := by
  classical
  have hcov : {G : LabeledGraph n | m ≤ maxDisjointHomogeneousEq G u} ⊆
      ⋃ F ∈ disjointCardFamilies n u m, {G | ∀ A ∈ F, IsHomogeneousSet G A} := by
    intro G hG
    rw [Set.mem_setOf_eq] at hG
    obtain ⟨F₀, hF₀, hcard₀⟩ := exists_isDisjointHomogeneousFamilyEq_card_eq G u
    obtain ⟨F, hFsub, hFcard⟩ :=
      Finset.exists_subset_card_eq (s := F₀) (n := m) (by omega)
    rw [Set.mem_iUnion₂]
    refine ⟨F, ?_, fun A hA ↦ (hF₀.1 A (hFsub hA)).2⟩
    rw [mem_disjointCardFamilies]
    exact ⟨hFcard, fun A hA ↦ (hF₀.1 A (hFsub hA)).1, hF₀.2.subset hFsub⟩
  have henn : randomGraphMeasure n {G | m ≤ maxDisjointHomogeneousEq G u} ≤
      ((disjointCardFamilies n u m).card : ENNReal) *
        ((2 : ENNReal) ^ m * (1 / 2 : ENNReal) ^ (m * u.choose 2)) := by
    calc randomGraphMeasure n {G | m ≤ maxDisjointHomogeneousEq G u}
        ≤ randomGraphMeasure n
            (⋃ F ∈ disjointCardFamilies n u m, {G | ∀ A ∈ F, IsHomogeneousSet G A}) :=
          measure_mono hcov
      _ ≤ ∑ F ∈ disjointCardFamilies n u m,
            randomGraphMeasure n {G | ∀ A ∈ F, IsHomogeneousSet G A} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _F ∈ disjointCardFamilies n u m,
            ((2 : ENNReal) ^ m * (1 / 2 : ENNReal) ^ (m * u.choose 2)) :=
          Finset.sum_le_sum fun F hF ↦
            randomGraphMeasure_familyHomogeneousEvent_le (mem_disjointCardFamilies.mp hF)
      _ = ((disjointCardFamilies n u m).card : ENNReal) *
            ((2 : ENNReal) ^ m * (1 / 2 : ENNReal) ^ (m * u.choose 2)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hfin : (((disjointCardFamilies n u m).card : ENNReal) *
      ((2 : ENNReal) ^ m * (1 / 2 : ENNReal) ^ (m * u.choose 2))) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
        (ENNReal.pow_ne_top (by norm_num)))
  have hreal := (ENNReal.toReal_le_toReal (measure_ne_top _ _) hfin).mpr henn
  have htoR : (((disjointCardFamilies n u m).card : ENNReal) *
        ((2 : ENNReal) ^ m * (1 / 2 : ENNReal) ^ (m * u.choose 2))).toReal =
      ((disjointCardFamilies n u m).card : ℝ) *
        (2 : ℝ) ^ m * (((2 : ℝ) ^ (u.choose 2))⁻¹) ^ m := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      show (1 / 2 : ENNReal).toReal = (2 : ℝ)⁻¹ by norm_num,
      mul_comm m (u.choose 2), pow_mul, inv_pow, ← mul_assoc]
  change (randomGraphMeasure n {G | m ≤ maxDisjointHomogeneousEq G u}).toReal ≤ _
  rw [htoR] at hreal
  have hcnt : ((disjointCardFamilies n u m).card : ℝ) ≤
      (∏ r ∈ Finset.range m, ((n - r * u).choose u : ℝ)) / (m.factorial : ℝ) := by
    have hmpos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    rw [le_div_iff₀ hmpos]
    exact_mod_cast card_disjointCardFamilies_mul_factorial_le n u m
  refine le_trans hreal ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcnt (by positivity)) (by positivity)

/-- **First inequality of Lemma 1.2 (`eq:homog-packing`, `(1.4)`):**
`P(H_u(G_n) ≥ m) ≤ n! / ((n - m u)! (u!)^m m!) · 2^m · (2 ^ C(u,2))⁻ᵐ`. -/
theorem randomGraph_maxDisjointHomogeneousEq_ge_le_factorial
    {n u m : ℕ} (hmu : m * u ≤ n) :
    (randomGraphMeasure n).real {G | m ≤ maxDisjointHomogeneousEq G u} ≤
      (n.factorial : ℝ) /
          (((n - m * u).factorial : ℝ) * (u.factorial : ℝ) ^ m * (m.factorial : ℝ)) *
        (2 : ℝ) ^ m * (((2 : ℝ) ^ (u.choose 2))⁻¹) ^ m := by
  have hprod_eq :
      (∏ r ∈ Finset.range m, ((n - r * u).choose u : ℝ)) / (m.factorial : ℝ) =
        (n.factorial : ℝ) /
          (((n - m * u).factorial : ℝ) * (u.factorial : ℝ) ^ m * (m.factorial : ℝ)) := by
    have hid : (∏ r ∈ Finset.range m, ((n - r * u).choose u : ℝ)) *
        ((u.factorial : ℝ) ^ m * ((n - m * u).factorial : ℝ)) = (n.factorial : ℝ) := by
      exact_mod_cast prod_choose_mul_factorial_eq hmu
    have huf : (u.factorial : ℝ) ^ m ≠ 0 := pow_ne_zero m (by exact_mod_cast Nat.factorial_ne_zero u)
    have hnf : ((n - m * u).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n - m * u)
    have hmf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    rw [← hid]
    field_simp [huf, hnf, hmf]
  rw [← hprod_eq]
  exact maxDisjointHomogeneousEq_ge_le_prod

/-- **Second inequality of Lemma 1.2 (`eq:homog-packing`, `(1.4)`):**
for `1 ≤ n`, `1 ≤ u`, and `m * u ≤ n`,
`P(H_u(G_n) ≥ m) ≤ (2 μ_u)^m / m! · exp (- u² / n · C(m, 2))`. -/
theorem randomGraph_maxDisjointHomogeneousEq_ge_le
    {n u m : ℕ} (hn : 1 ≤ n) (hu : 1 ≤ u) (hmu : m * u ≤ n) :
    (randomGraphMeasure n).real {G | m ≤ maxDisjointHomogeneousEq G u} ≤
      (2 * mu n u) ^ m / (m.factorial : ℝ) *
        Real.exp (-(u : ℝ) ^ 2 / (n : ℝ) * (m.choose 2 : ℝ)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hbase := maxDisjointHomogeneousEq_ge_le_prod (n := n) (u := u) (m := m)
  have hrewrite :
      ((∏ r ∈ Finset.range m, ((n - r * u).choose u : ℝ)) / (m.factorial : ℝ)) *
          (2 : ℝ) ^ m * (((2 : ℝ) ^ (u.choose 2))⁻¹) ^ m =
        (∏ r ∈ Finset.range m, (2 * mu (n - r * u) u)) / (m.factorial : ℝ) := by
    have hprod_mu :
        ∏ r ∈ Finset.range m, (2 * mu (n - r * u) u) =
          (∏ r ∈ Finset.range m, ((n - r * u).choose u : ℝ)) *
            (2 : ℝ) ^ m * (((2 : ℝ) ^ (u.choose 2))⁻¹) ^ m := by
      unfold mu
      calc ∏ r ∈ Finset.range m,
              (2 * (((n - r * u).choose u : ℝ) * ((2 : ℝ) ^ (u.choose 2))⁻¹))
          = ∏ r ∈ Finset.range m,
              (((n - r * u).choose u : ℝ) * (2 * ((2 : ℝ) ^ (u.choose 2))⁻¹)) :=
            Finset.prod_congr rfl fun _ _ ↦ by ring
        _ = (∏ r ∈ Finset.range m, ((n - r * u).choose u : ℝ)) *
              (2 * ((2 : ℝ) ^ (u.choose 2))⁻¹) ^ m := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
        _ = (∏ r ∈ Finset.range m, ((n - r * u).choose u : ℝ)) *
              (2 : ℝ) ^ m * (((2 : ℝ) ^ (u.choose 2))⁻¹) ^ m := by ring
    rw [hprod_mu]
    ring
  rw [hrewrite] at hbase
  have hterm : ∀ r ∈ Finset.range m,
      2 * mu (n - r * u) u ≤
        (2 * mu n u) * Real.exp (-(r : ℝ) * (u : ℝ) ^ 2 / (n : ℝ)) := by
    intro r hr
    rw [Finset.mem_range] at hr
    have hru_u : r * u + u ≤ n := by
      calc r * u + u = (r + 1) * u := by ring
        _ ≤ m * u := Nat.mul_le_mul_right u hr
        _ ≤ n := hmu
    have hu_le : u ≤ n - r * u := by omega
    have hru_le : r * u ≤ n := by omega
    have hscale := mu_le_mu_mul_vertex_ratio_pow (by omega : 0 < n) hu_le (Nat.sub_le n (r * u))
    have hrat_eq : ((n - r * u : ℕ) : ℝ) / (n : ℝ) = 1 - (r : ℝ) * (u : ℝ) / (n : ℝ) := by
      rw [Nat.cast_sub hru_le, Nat.cast_mul, sub_div, div_self hn_pos.ne']
    have hrat_nn : 0 ≤ ((n - r * u : ℕ) : ℝ) / (n : ℝ) := by positivity
    have hexp1 : ((n - r * u : ℕ) : ℝ) / (n : ℝ) ≤
        Real.exp (-(r : ℝ) * (u : ℝ) / (n : ℝ)) := by
      rw [hrat_eq]
      have h1 := Real.add_one_le_exp (-((r : ℝ) * (u : ℝ) / (n : ℝ)))
      have h2 : -((r : ℝ) * (u : ℝ) / (n : ℝ)) = -(r : ℝ) * (u : ℝ) / (n : ℝ) := by ring
      rw [h2] at h1
      linarith
    have hpow_exp : (((n - r * u : ℕ) : ℝ) / (n : ℝ)) ^ u ≤
        Real.exp (-(r : ℝ) * (u : ℝ) ^ 2 / (n : ℝ)) := by
      calc (((n - r * u : ℕ) : ℝ) / (n : ℝ)) ^ u
          ≤ (Real.exp (-(r : ℝ) * (u : ℝ) / (n : ℝ))) ^ u :=
            pow_le_pow_left₀ hrat_nn hexp1 u
        _ = Real.exp ((u : ℝ) * (-(r : ℝ) * (u : ℝ) / (n : ℝ))) :=
            (Real.exp_nat_mul _ u).symm
        _ = Real.exp (-(r : ℝ) * (u : ℝ) ^ 2 / (n : ℝ)) := by
            congr 1; ring
    calc 2 * mu (n - r * u) u
        ≤ 2 * (mu n u * (((n - r * u : ℕ) : ℝ) / (n : ℝ)) ^ u) :=
          mul_le_mul_of_nonneg_left hscale zero_le_two
      _ = (2 * mu n u) * (((n - r * u : ℕ) : ℝ) / (n : ℝ)) ^ u := by ring
      _ ≤ (2 * mu n u) * Real.exp (-(r : ℝ) * (u : ℝ) ^ 2 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow_exp (mul_nonneg zero_le_two (mu_nonneg n u))
  have hprod_le :
      ∏ r ∈ Finset.range m, (2 * mu (n - r * u) u) ≤
        (2 * mu n u) ^ m * Real.exp (-(u : ℝ) ^ 2 / (n : ℝ) * (m.choose 2 : ℝ)) := by
    calc ∏ r ∈ Finset.range m, (2 * mu (n - r * u) u)
        ≤ ∏ r ∈ Finset.range m,
            ((2 * mu n u) * Real.exp (-(r : ℝ) * (u : ℝ) ^ 2 / (n : ℝ))) :=
          Finset.prod_le_prod (fun r _ ↦ mul_nonneg zero_le_two (mu_nonneg _ u)) hterm
      _ = (2 * mu n u) ^ m *
            ∏ r ∈ Finset.range m, Real.exp (-(r : ℝ) * (u : ℝ) ^ 2 / (n : ℝ)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      _ = (2 * mu n u) ^ m *
            Real.exp (∑ r ∈ Finset.range m, (-(r : ℝ) * (u : ℝ) ^ 2 / (n : ℝ))) := by
          rw [← Real.exp_sum]
      _ = (2 * mu n u) ^ m *
            Real.exp (-(u : ℝ) ^ 2 / (n : ℝ) * (m.choose 2 : ℝ)) := by
          congr 2
          calc ∑ r ∈ Finset.range m, (-(r : ℝ) * (u : ℝ) ^ 2 / (n : ℝ))
              = ∑ r ∈ Finset.range m, (-(u : ℝ) ^ 2 / (n : ℝ) * (r : ℝ)) :=
                Finset.sum_congr rfl fun _ _ ↦ by ring
            _ = -(u : ℝ) ^ 2 / (n : ℝ) * ∑ r ∈ Finset.range m, (r : ℝ) := by
                rw [← Finset.mul_sum]
            _ = -(u : ℝ) ^ 2 / (n : ℝ) * (m.choose 2 : ℝ) := by
                rw [sum_range_cast_eq_choose_two]
  refine le_trans hbase ?_
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hprod_le (by positivity)

/-! ## 3. First Borel–Cantelli & almost-sure convergence under arbitrary couplings -/

/-- **First Borel–Cantelli lemma for real-valued probabilities:** on any
probability space `(Ω, ℙ)`, if `∑' n, ℙ.real (E n)` converges, then almost surely
`ω ∉ E n` for all sufficiently large `n`. -/
theorem ae_eventually_notMem_of_summable_measureReal
    {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    {E : ℕ → Set Ω} (hsum : Summable (fun n ↦ ℙ.real (E n))) :
    ∀ᵐ ω ∂ℙ, ∀ᶠ n in atTop, ω ∉ E n := by
  have htail_bound : ∀ N : ℕ,
      ℙ {ω | ¬ ∀ᶠ n in atTop, ω ∉ E n} ≤
        ENNReal.ofReal (∑' k : ℕ, ℙ.real (E (k + N))) := by
    intro N
    have hsub : {ω | ¬ ∀ᶠ n in atTop, ω ∉ E n} ⊆ ⋃ k : ℕ, E (k + N) := by
      intro ω hω
      rw [Set.mem_setOf_eq, Filter.eventually_atTop] at hω
      have hex : ∃ n ≥ N, ω ∈ E n := by
        by_contra hnone
        apply hω
        exact ⟨N, fun n hn hmem ↦ hnone ⟨n, hn, hmem⟩⟩
      rcases hex with ⟨n, hn, hmem⟩
      rw [Set.mem_iUnion]
      exact ⟨n - N, by rwa [Nat.sub_add_cancel hn]⟩
    have hsumN : Summable (fun k : ℕ ↦ ℙ.real (E (k + N))) :=
      hsum.comp_injective (add_left_injective N)
    have h1 : ℙ {ω | ¬ ∀ᶠ n in atTop, ω ∉ E n} ≤ ℙ (⋃ k : ℕ, E (k + N)) :=
      measure_mono hsub
    have h2 : ℙ (⋃ k : ℕ, E (k + N)) ≤ ∑' k : ℕ, ℙ (E (k + N)) :=
      measure_iUnion_le (fun k : ℕ ↦ E (k + N))
    have h3 : ∑' k : ℕ, ℙ (E (k + N)) ≤
        ENNReal.ofReal (∑' k : ℕ, ℙ.real (E (k + N))) := by
      rw [ENNReal.tsum_eq_iSup_sum]
      refine iSup_le fun s ↦ ?_
      have heq : ∑ k ∈ s, ℙ (E (k + N)) =
          ENNReal.ofReal (∑ k ∈ s, ℙ.real (E (k + N))) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ measureReal_nonneg)]
        exact Finset.sum_congr rfl fun k _ ↦
          (ENNReal.ofReal_toReal (measure_ne_top ℙ _)).symm
      rw [heq]
      exact ENNReal.ofReal_le_ofReal
        (hsumN.sum_le_tsum s (fun _ _ ↦ measureReal_nonneg))
    exact le_trans h1 (le_trans h2 h3)
  have htail_zero : Tendsto (fun N : ℕ ↦ ∑' k : ℕ, ℙ.real (E (k + N))) atTop (nhds 0) := by
    have hpart := hsum.hasSum.tendsto_sum_nat
    have hsub : Tendsto (fun N : ℕ ↦ (∑' i : ℕ, ℙ.real (E i)) -
        ∑ i ∈ Finset.range N, ℙ.real (E i)) atTop (nhds 0) := by
      simpa only [sub_self] using
        (tendsto_const_nhds (x := ∑' i : ℕ, ℙ.real (E i))).sub hpart
    refine hsub.congr fun N ↦ ?_
    linarith [hsum.sum_add_tsum_nat_add N]
  have htoReal_zero : (ℙ {ω | ¬ ∀ᶠ n in atTop, ω ∉ E n}).toReal = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    by_contra hpos
    have heps : 0 < (ℙ {ω | ¬ ∀ᶠ n in atTop, ω ∉ E n}).toReal := not_le.mp hpos
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp htail_zero)
      ((ℙ {ω | ¬ ∀ᶠ n in atTop, ω ∉ E n}).toReal / 2) (half_pos heps)
    have hNN := hN N le_rfl
    have hnn : 0 ≤ ∑' k : ℕ, ℙ.real (E (k + N)) :=
      tsum_nonneg fun _ ↦ measureReal_nonneg
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hNN
    have hb := (ENNReal.toReal_le_toReal
      (measure_ne_top ℙ {ω | ¬ ∀ᶠ n in atTop, ω ∉ E n})
      ENNReal.ofReal_ne_top).mpr (htail_bound N)
    rw [ENNReal.toReal_ofReal hnn] at hb
    linarith
  rw [ae_iff]
  exact (ENNReal.toReal_eq_zero_iff _).mp htoReal_zero |>.resolve_right
    (measure_ne_top ℙ _)

/-- Any map `g : Ω → LabeledGraph n` on a probability space with pushforward
`Measure.map g ℙ = randomGraphMeasure n` is automatically `ℙ`-a.e. measurable. -/
theorem aemeasurable_of_map_eq_randomGraphMeasure
    {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω} {n : ℕ}
    {g : Ω → LabeledGraph n} (hmap : Measure.map g ℙ = randomGraphMeasure n) :
    AEMeasurable g ℙ := by
  by_contra hnaem
  have hzero : Measure.map g ℙ = 0 := Measure.map_of_not_aemeasurable hnaem
  rw [hzero] at hmap
  have huniv := congrArg (fun μ : Measure (LabeledGraph n) ↦ μ Set.univ) hmap
  simp only [Measure.coe_zero, Pi.zero_apply, measure_univ, zero_ne_one] at huniv

/-- **Coupling Borel–Cantelli:** for any probability space `(Ω, ℙ)`, any joint
sequence `G : ∀ n, Ω → LabeledGraph n` with `G(n, 1/2)` marginals, and any
events `E : ∀ n, Set (LabeledGraph n)` with summable failure probabilities
`∑' n, P(G_n ∉ E_n) < ∞`, almost surely `G n ω ∈ E n` eventually. -/
theorem ae_eventually_mem_of_summable_compl
    {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (G : ∀ n : ℕ, Ω → LabeledGraph n)
    (hMarg : ∀ n : ℕ, Measure.map (G n) ℙ = randomGraphMeasure n)
    {E : ∀ n : ℕ, Set (LabeledGraph n)}
    (hsum : Summable (fun n : ℕ ↦ (randomGraphMeasure n).real (E n)ᶜ)) :
    ∀ᵐ ω ∂ℙ, ∀ᶠ n in atTop, G n ω ∈ E n := by
  have hsum_pre : Summable (fun n : ℕ ↦ ℙ.real ((G n) ⁻¹' (E n)ᶜ)) := by
    refine hsum.congr fun n ↦ ?_
    have haem := aemeasurable_of_map_eq_randomGraphMeasure (hMarg n)
    have hms : MeasurableSet (E n)ᶜ := (Set.toFinite _).measurableSet
    dsimp only [Measure.real]
    rw [← Measure.map_apply_of_aemeasurable haem hms, hMarg n]
  filter_upwards [ae_eventually_notMem_of_summable_measureReal ℙ hsum_pre] with ω hω
  filter_upwards [hω] with n hn
  by_contra hnot
  exact hn hnot

/-- **Almost-sure two-sided gap certificate under arbitrary couplings**
(covering the almost-sure clause of the **Phase Refinement**): if the single-`n`
two-sided failure probabilities are summable, then under every coupling `(Ω, ℙ, G)`
with `G(n, 1/2)` marginals, almost surely `G n ω ∈ twoSidedGapEvent (c n) (C n) n`
for all sufficiently large `n`. -/
theorem ae_eventually_twoSidedGap_of_summable_compl
    {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (G : ∀ n : ℕ, Ω → LabeledGraph n)
    (hMarg : ∀ n : ℕ, Measure.map (G n) ℙ = randomGraphMeasure n)
    {c C : ℕ → ℝ}
    (hsum : Summable (fun n : ℕ ↦
      (randomGraphMeasure n).real (twoSidedGapEvent (c n) (C n) n)ᶜ)) :
    ∀ᵐ ω ∂ℙ, ∀ᶠ n in atTop, G n ω ∈ twoSidedGapEvent (c n) (C n) n :=
  ae_eventually_mem_of_summable_compl ℙ G hMarg hsum

/-- **Almost-sure full-sequence Main Theorem bridge:** if for every `eps > 0`
the single-`n` failure probabilities around `sharpGapConstant = (log 2)³ / 4`
are summable over `n`, then under **every** joint coupling `(Ω, ℙ, G)` with
marginals `G_n ∼ G(n, 1/2)`, almost surely
`(log n)³ / n · (χ(G_n) - ζ(G_n)) → (log 2)³ / 4` and
`(log₂ n)³ / n · (χ(G_n) - ζ(G_n)) → 1 / 4`. -/
theorem ae_tendsto_normalizedGap_of_summable_failures
    {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (G : ∀ n : ℕ, Ω → LabeledGraph n)
    (hMarg : ∀ n : ℕ, Measure.map (G n) ℙ = randomGraphMeasure n)
    (hsum : ∀ eps : ℝ, 0 < eps →
      Summable (fun n : ℕ ↦ (randomGraphMeasure n).real
        (twoSidedGapEvent (sharpGapConstant - eps) (sharpGapConstant + eps) n)ᶜ)) :
    ∀ᵐ ω ∂ℙ,
      Tendsto (fun n : ℕ ↦
        (Real.log n) ^ 3 / (n : ℝ) *
          ((chromaticNumberNat (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ)))
        atTop (nhds sharpGapConstant) ∧
      Tendsto (fun n : ℕ ↦
        (Real.logb 2 n) ^ 3 / (n : ℝ) *
          ((chromaticNumberNat (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ)))
        atTop (nhds (1 / 4 : ℝ)) := by
  have hall : ∀ᵐ ω ∂ℙ, ∀ k : ℕ, ∀ᶠ n in atTop,
      G n ω ∈ twoSidedGapEvent
        (sharpGapConstant - 1 / ((k : ℝ) + 1))
        (sharpGapConstant + 1 / ((k : ℝ) + 1)) n := by
    rw [ae_all_iff]
    intro k
    exact ae_eventually_twoSidedGap_of_summable_compl ℙ G hMarg
      (hsum (1 / ((k : ℝ) + 1)) (by positivity))
  filter_upwards [hall] with ω hω
  have hnat : Tendsto (fun n : ℕ ↦
      (Real.log n) ^ 3 / (n : ℝ) *
        ((chromaticNumberNat (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ)))
      atTop (nhds sharpGapConstant) := by
    rw [Metric.tendsto_nhds]
    intro delta hdelta
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hdelta
    filter_upwards [eventually_ge_atTop 2, hω k] with n hn hGn
    obtain ⟨hlo, hhi⟩ := hGn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have hfac_pos : 0 < (Real.log n) ^ 3 / (n : ℝ) := by positivity
    have hmul_lo := mul_le_mul_of_nonneg_left hlo hfac_pos.le
    have hmul_hi := mul_le_mul_of_nonneg_left hhi hfac_pos.le
    have hcancel : ∀ x : ℝ,
        (Real.log n) ^ 3 / (n : ℝ) * (x * ((n : ℝ) / (Real.log n) ^ 3)) = x := by
      intro x
      field_simp [hn_pos.ne', (pow_pos hlog_pos 3).ne']
    rw [hcancel] at hmul_lo hmul_hi
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith⟩
  refine ⟨hnat, ?_⟩
  have hlog2_ne : (Real.log 2) ^ 3 ≠ 0 := pow_ne_zero 3 (Real.log_pos one_lt_two).ne'
  have hdiv := hnat.const_mul (1 / (Real.log 2) ^ 3)
  rw [one_div_mul_eq_div, sharpGapConstant_div_log_two_cube] at hdiv
  refine hdiv.congr fun n ↦ ?_
  rw [Real.logb]
  field_simp [hlog2_ne]

end

end Erdos625HP
