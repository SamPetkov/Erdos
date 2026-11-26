import Erdos625HP.Amplification
import Erdos625HP.CochromaticLowerTail

/-!
# Section 1 (`lem:disjoint-packing`) & Section 4 (`prop:lower-tails`): disjoint large-set packings

For a graph `G : LabeledGraph n` and integer `u`, let `maxDisjointIndepGe G u`
(`D_u(G)` in Lemma 1.1 of the manuscript) be the maximum cardinality of a family
of pairwise disjoint independent subsets of `G`, each of size at least `u`.

This module proves unconditionally in Lean 4:
1. **Comparison with `X_u(G)` and first moment:** for `1 ≤ u`,
   `maxDisjointIndepGe G u ≤ independentSetCount G u` and
   `∫ G, (maxDisjointIndepGe G u : ℝ) ∂(randomGraphMeasure n) ≤ mu n u`.
2. **Unit vertex-deletion oscillation and McDiarmid upper tail (`eq:disjoint-tail`):**
   `maxDisjointIndepGe_hasVertexDeletionOscillation` and
   `randomGraph_maxDisjointIndepGe_gt_mu_add_le_exp`:
   `P(D_u(G_n) > μ_u + t) ≤ exp (-2 t² / (n - 1))` for `n ≥ 2`, `1 ≤ u`, `t ≥ 0`.
3. **Bounded-size class splitting for colourings and cocolourings (Lemma 1.1 & Prop. 4.1):**
   * `exists_bounded_coloring_partition_of_maxDisjointIndepGe_le`: if `2 ≤ u`,
     `k + d ≤ n`, `α(G) ≤ 2(u - 1)`, `D_u(G) ≤ d`, and `χ(G) ≤ k`, then `G`
     admits an exact `(k + d)`-block proper-colouring partition into nonempty
     parts of size `≤ u - 1`.
   * `exists_bounded_cocoloring_partition_of_maxDisjointIndepGe_le`: if also
     `k + 2d ≤ n`, `α(Gᶜ) ≤ 2(u - 1)`, `D_u(Gᶜ) ≤ d`, and `ζ(G) ≤ k`, then `G`
     admits an exact `(k + 2d)`-block cocolouring partition into nonempty parts
     of size `≤ u - 1`.
-/

namespace Erdos625HP

open Erdos625 MeasureTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

/-! ## 1. Disjoint large independent families and `D_u(G) ≤ X_u(G)` -/

/-- A family `F` of vertex subsets in `G` consists of pairwise disjoint
independent sets each of cardinality at least `u`. -/
def IsDisjointIndepFamilyGe {n : ℕ} (G : LabeledGraph n) (u : ℕ)
    (F : Finset (Finset (Fin n))) : Prop :=
  (∀ A ∈ F, u ≤ A.card ∧ G.IsIndepSet (A : Set (Fin n))) ∧
    (F : Set (Finset (Fin n))).PairwiseDisjoint id

/-- Finite set of all pairwise disjoint independent families of size `≥ u`. -/
def disjointIndepFamiliesGe {n : ℕ} (G : LabeledGraph n) (u : ℕ) :
    Finset (Finset (Finset (Fin n))) := by
  classical
  exact Finset.univ.filter (IsDisjointIndepFamilyGe G u)

/-- Maximum number `D_u(G)` of pairwise disjoint independent subsets of size `≥ u`. -/
def maxDisjointIndepGe {n : ℕ} (G : LabeledGraph n) (u : ℕ) : ℕ :=
  (disjointIndepFamiliesGe G u).sup Finset.card

theorem mem_disjointIndepFamiliesGe {n : ℕ} {G : LabeledGraph n} {u : ℕ}
    {F : Finset (Finset (Fin n))} :
    F ∈ disjointIndepFamiliesGe G u ↔ IsDisjointIndepFamilyGe G u F := by
  classical
  simp [disjointIndepFamiliesGe]

theorem empty_mem_disjointIndepFamiliesGe {n : ℕ} (G : LabeledGraph n) (u : ℕ) :
    ∅ ∈ disjointIndepFamiliesGe G u := by
  rw [mem_disjointIndepFamiliesGe]
  exact ⟨by simp, by simp⟩

theorem card_le_maxDisjointIndepGe {n : ℕ} {G : LabeledGraph n} {u : ℕ}
    {F : Finset (Finset (Fin n))} (hF : IsDisjointIndepFamilyGe G u F) :
    F.card ≤ maxDisjointIndepGe G u :=
  Finset.le_sup (f := Finset.card) (mem_disjointIndepFamiliesGe.mpr hF)

theorem exists_isDisjointIndepFamilyGe_card_eq {n : ℕ} (G : LabeledGraph n) (u : ℕ) :
    ∃ F : Finset (Finset (Fin n)),
      IsDisjointIndepFamilyGe G u F ∧ F.card = maxDisjointIndepGe G u := by
  obtain ⟨F, hFmem, hFcard⟩ :=
    Finset.exists_mem_eq_sup (disjointIndepFamiliesGe G u)
      ⟨∅, empty_mem_disjointIndepFamiliesGe G u⟩ Finset.card
  exact ⟨F, mem_disjointIndepFamiliesGe.mp hFmem, hFcard.symm⟩

/-- Pointwise comparison `D_u(G) ≤ X_u(G)` for `1 ≤ u` (choosing one `u`-subset
inside each member of a disjoint family). -/
theorem maxDisjointIndepGe_le_independentSetCount {n u : ℕ} (hu : 1 ≤ u)
    (G : LabeledGraph n) :
    maxDisjointIndepGe G u ≤ independentSetCount G u := by
  classical
  obtain ⟨F, hF, hFcard⟩ := exists_isDisjointIndepFamilyGe_card_eq G u
  let IndU : Finset (Finset (Fin n)) :=
    ((Finset.univ : Finset (Fin n)).powersetCard u).filter
      (fun S ↦ G.IsIndepSet (S : Set (Fin n)))
  have hIndU_eq : independentSetCount G u = IndU.card := by
    unfold independentSetCount independentIndicatorNat
    rw [Finset.sum_boole]
    simp [IndU]
  let pick : F → Finset (Fin n) := fun A ↦
    (Finset.exists_subset_card_eq (hF.1 A.1 A.2).1).choose
  have hpick_sub (A : F) : pick A ⊆ A.1 :=
    (Finset.exists_subset_card_eq (hF.1 A.1 A.2).1).choose_spec.1
  have hpick_card (A : F) : (pick A).card = u :=
    (Finset.exists_subset_card_eq (hF.1 A.1 A.2).1).choose_spec.2
  have hpick_mem (A : F) : pick A ∈ IndU := by
    simp only [IndU, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    refine ⟨hpick_card A, ?_⟩
    exact Set.Pairwise.mono (by simpa using hpick_sub A) (hF.1 A.1 A.2).2
  let f : F → IndU := fun A ↦ ⟨pick A, hpick_mem A⟩
  have hinj : Function.Injective f := by
    intro A B hAB
    have hp : pick A = pick B := congrArg Subtype.val hAB
    have hne : (pick A).Nonempty :=
      Finset.card_pos.mp (by have := hpick_card A; omega)
    obtain ⟨x, hx⟩ := hne
    have hxA : x ∈ A.1 := hpick_sub A hx
    have hxB : x ∈ B.1 := hpick_sub B (hp ▸ hx)
    apply Subtype.ext
    by_contra hneAB
    exact (Finset.disjoint_left.mp (hF.2 A.2 B.2 hneAB) hxA) hxB
  have hcard : F.card ≤ IndU.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj
  rw [← hFcard, hIndU_eq]
  exact hcard

/-- First moment of `X_u(G_n)` as a Bochner integral equals `mu n u`. -/
theorem integral_independentSetCount_eq_mu (n u : ℕ) :
    ∫ G, (independentSetCount G u : ℝ) ∂(randomGraphMeasure n) = mu n u := by
  rw [MeasureTheory.integral_fintype (Integrable.of_finite)]
  have hexp := congrArg ENNReal.toReal (independentSetExpectation_eq_ofReal_mu n u)
  rw [ENNReal.toReal_ofReal (mu_nonneg n u)] at hexp
  unfold independentSetExpectation at hexp
  rw [ENNReal.toReal_sum (fun G _ ↦ ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (measure_ne_top _ _))] at hexp
  rw [← hexp]
  refine Finset.sum_congr rfl fun G _ ↦ ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, Measure.real, smul_eq_mul, mul_comm]

/-- First-moment bound `E[D_u(G_n)] ≤ μ_u` for `1 ≤ u`. -/
theorem integral_maxDisjointIndepGe_le_mu {n u : ℕ} (hu : 1 ≤ u) :
    ∫ G, (maxDisjointIndepGe G u : ℝ) ∂(randomGraphMeasure n) ≤ mu n u := by
  rw [← integral_independentSetCount_eq_mu n u]
  refine integral_mono (Integrable.of_finite) (Integrable.of_finite) fun G ↦ ?_
  dsimp only
  exact Nat.cast_le.mpr (maxDisjointIndepGe_le_independentSetCount hu G)

/-! ## 2. Unit vertex-deletion oscillation and McDiarmid upper tail -/

/-- Changing the edges incident to a single vertex `i` increases `D_u` by at most `1`,
since at most one member of a pairwise disjoint family contains `i`. -/
theorem maxDisjointIndepGe_le_add_one_of_induce_away_eq {n u : ℕ}
    {G H : LabeledGraph n} {i : Fin n}
    (hGH : G.induce {v | v ≠ i} = H.induce {v | v ≠ i}) :
    maxDisjointIndepGe G u ≤ maxDisjointIndepGe H u + 1 := by
  classical
  obtain ⟨F, hF, hFcard⟩ := exists_isDisjointIndepFamilyGe_card_eq G u
  let Faway := Finset.filter (fun A ↦ i ∉ A) F
  let Fhit := Finset.filter (fun A ↦ i ∈ A) F
  have hsplit : Faway.card + Fhit.card = F.card := by
    simpa [Faway, Fhit] using
      Finset.card_filter_add_card_filter_not (s := F) (p := fun A ↦ i ∉ A)
  have hhit_le : Fhit.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro A B hA hB
    simp only [Fhit, Finset.mem_filter] at hA hB
    by_contra hne
    exact (Finset.disjoint_left.mp (hF.2 hA.1 hB.1 hne) hA.2) hB.2
  have haway_fam : IsDisjointIndepFamilyGe H u Faway := by
    refine ⟨?_, ?_⟩
    · intro A hA
      simp only [Faway, Finset.mem_filter] at hA
      refine ⟨(hF.1 A hA.1).1, ?_⟩
      intro x hx y hy hxy hadjH
      have hxi : x ≠ i := fun h ↦ hA.2 (h ▸ hx)
      have hyi : y ≠ i := fun h ↦ hA.2 (h ▸ hy)
      have hadjG : G.Adj x y := by
        change (G.induce {v | v ≠ i}).Adj ⟨x, hxi⟩ ⟨y, hyi⟩
        rw [hGH]
        exact hadjH
      exact (hF.1 A hA.1).2 hx hy hxy hadjG
    · exact hF.2.subset fun A hA ↦ (Finset.mem_filter.mp hA).1
  have haway_le := card_le_maxDisjointIndepGe haway_fam
  omega

/-- `D_u(G)` has vertex-deletion oscillation `1`. -/
theorem maxDisjointIndepGe_hasVertexDeletionOscillation (n u : ℕ) :
    HasVertexDeletionOscillation
      (fun G : LabeledGraph n ↦ (maxDisjointIndepGe G u : ℝ))
      (fun _ ↦ (1 : ℝ≥0)) := by
  intro i G H hGH
  have h1 : (maxDisjointIndepGe G u : ℝ) ≤ (maxDisjointIndepGe H u : ℝ) + 1 := by
    exact_mod_cast maxDisjointIndepGe_le_add_one_of_induce_away_eq hGH
  have h2 : (maxDisjointIndepGe H u : ℝ) ≤ (maxDisjointIndepGe G u : ℝ) + 1 := by
    exact_mod_cast maxDisjointIndepGe_le_add_one_of_induce_away_eq hGH.symm
  change |(maxDisjointIndepGe G u : ℝ) - (maxDisjointIndepGe H u : ℝ)| ≤ 1
  rw [abs_le]
  constructor <;> linarith

/-- **McDiarmid tail for `D_u(G_n)` (Lemma 1.1, eq. `(1.4)`):** for `n ≥ 2`,
`1 ≤ u`, and `t ≥ 0`, `P(D_u(G_n) > μ_u + t) ≤ exp (-2 t² / (n - 1))`. -/
theorem randomGraph_maxDisjointIndepGe_gt_mu_add_le_exp {n u : ℕ}
    (hn : 2 ≤ n) (hu : 1 ≤ u) {t : ℝ} (ht : 0 ≤ t) :
    (randomGraphMeasure n).real
        {G | mu n u + t < (maxDisjointIndepGe G u : ℝ)} ≤
      Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) := by
  have hmean := integral_maxDisjointIndepGe_le_mu (n := n) hu
  have hsub :
      {G : LabeledGraph n | mu n u + t < (maxDisjointIndepGe G u : ℝ)} ⊆
        {G : LabeledGraph n |
          t ≤ (maxDisjointIndepGe G u : ℝ) -
            ∫ H, (maxDisjointIndepGe H u : ℝ) ∂(randomGraphMeasure n)} := by
    intro G hG
    simp only [Set.mem_setOf_eq] at hG ⊢
    linarith
  exact le_trans (measureReal_mono hsub)
    (randomGraph_upperTail_noninitial hn
      (maxDisjointIndepGe_hasVertexDeletionOscillation n u) ht)

/-! ## 3. Bounded-size class splitting for `Finpartition`, colourings, and cocolourings -/

private theorem split_one_large_finset {α : Type*} [DecidableEq α]
    {B : Finset α} {u : ℕ} (hu : 2 ≤ u) (hlo : u ≤ B.card)
    (hhi : B.card ≤ 2 * (u - 1)) :
    ∃ A₁ A₂ : Finset α,
      A₁.Nonempty ∧ A₂.Nonempty ∧ Disjoint A₁ A₂ ∧ A₁ ∪ A₂ = B ∧
        A₁.card ≤ u - 1 ∧ A₂.card ≤ u - 1 := by
  obtain ⟨A₁, hA₁sub, hA₁card⟩ :=
    Finset.exists_subset_card_eq (s := B) (n := u - 1) (by omega)
  let A₂ := B \ A₁
  have hA₂card : A₂.card = B.card - (u - 1) := by
    dsimp [A₂]
    rw [Finset.card_sdiff_of_subset hA₁sub, hA₁card]
  refine ⟨A₁, A₂, ?_, ?_, disjoint_sdiff_self_right,
    Finset.union_sdiff_of_subset hA₁sub, by omega, by omega⟩
  · exact Finset.card_pos.mp (by omega)
  · exact Finset.card_pos.mp (by omega)

private theorem split_one_part_finpartition {n u : ℕ} (hu : 2 ≤ u)
    (P : VertexPartition n) {B : Finset (Fin n)} (hB : B ∈ P.parts)
    (hBlo : u ≤ B.card) (hBhi : B.card ≤ 2 * (u - 1)) :
    ∃ P' : VertexPartition n,
      P' ≤ P ∧
        P'.parts.card = P.parts.card + 1 ∧
        (P'.parts.filter (fun D ↦ u ≤ D.card)).card + 1 =
          (P.parts.filter (fun D ↦ u ≤ D.card)).card := by
  classical
  obtain ⟨A₁, A₂, hA₁ne, hA₂ne, hdisj12, hunion, hA₁le, hA₂le⟩ :=
    split_one_large_finset hu hBlo hBhi
  have hA₁sub : A₁ ⊆ B := by rw [← hunion]; exact Finset.subset_union_left
  have hA₂sub : A₂ ⊆ B := by rw [← hunion]; exact Finset.subset_union_right
  have hA₁not : A₁ ∉ P.parts.erase B := by
    intro hmem
    obtain ⟨hne, hmemP⟩ := Finset.mem_erase.mp hmem
    obtain ⟨x, hx⟩ := hA₁ne
    exact (Finset.disjoint_left.mp (P.disjoint hmemP hB hne) hx) (hA₁sub hx)
  have hA₂not : A₂ ∉ P.parts.erase B := by
    intro hmem
    obtain ⟨hne, hmemP⟩ := Finset.mem_erase.mp hmem
    obtain ⟨x, hx⟩ := hA₂ne
    exact (Finset.disjoint_left.mp (P.disjoint hmemP hB hne) hx) (hA₂sub hx)
  have hA₁neA₂ : A₁ ≠ A₂ := by
    intro heq
    obtain ⟨x, hx⟩ := hA₁ne
    exact (Finset.disjoint_left.mp hdisj12 hx) (heq ▸ hx)
  let parts' : Finset (Finset (Fin n)) := insert A₁ (insert A₂ (P.parts.erase B))
  have hnotbot : ⊥ ∉ parts' := by
    intro hbot
    simp only [parts', Finset.mem_insert, Finset.bot_eq_empty] at hbot
    rcases hbot with h1 | h2 | h3
    · exact hA₁ne.ne_empty h1.symm
    · exact hA₂ne.ne_empty h2.symm
    · exact P.bot_notMem (Finset.mem_of_mem_erase h3)
  have hind : (parts' : Set (Finset (Fin n))).PairwiseDisjoint id := by
    intro X hX Y hY hXY
    simp only [parts', Finset.mem_coe, Finset.mem_insert, Finset.mem_erase] at hX hY
    rcases hX with rfl | rfl | ⟨hXne, hXP⟩ <;> rcases hY with rfl | rfl | ⟨hYne, hYP⟩
    · exact (hXY rfl).elim
    · exact hdisj12
    · exact Disjoint.mono_left hA₁sub (P.disjoint hB hYP hYne.symm)
    · exact hdisj12.symm
    · exact (hXY rfl).elim
    · exact Disjoint.mono_left hA₂sub (P.disjoint hB hYP hYne.symm)
    · exact Disjoint.mono_right hA₁sub (P.disjoint hXP hB hXne)
    · exact Disjoint.mono_right hA₂sub (P.disjoint hXP hB hXne)
    · exact P.disjoint hXP hYP hXY
  have hsup : parts'.sup id = (Finset.univ : Finset (Fin n)) := by
    rw [← P.sup_parts]
    dsimp [parts']
    rw [Finset.sup_insert, Finset.sup_insert, ← sup_assoc]
    change (A₁ ∪ A₂) ⊔ (P.parts.erase B).sup id = P.parts.sup id
    rw [hunion]
    have hins : (insert B (P.parts.erase B)).sup id = P.parts.sup id :=
      congrArg (fun S ↦ S.sup id) (Finset.insert_erase hB)
    simpa only [Finset.sup_insert, id_eq] using hins
  let P' : VertexPartition n :=
    { parts := parts'
      supIndep := by
        rw [Finset.supIndep_iff_pairwiseDisjoint]
        exact hind
      sup_parts := hsup
      bot_notMem := hnotbot }
  have hle : P' ≤ P := by
    intro D hD
    simp only [P', parts', Finset.mem_insert, Finset.mem_erase] at hD
    rcases hD with rfl | rfl | ⟨_, hDP⟩
    · exact ⟨B, hB, hA₁sub⟩
    · exact ⟨B, hB, hA₂sub⟩
    · exact ⟨D, hDP, le_rfl⟩
  have hcard : P'.parts.card = P.parts.card + 1 := by
    dsimp [P', parts']
    rw [Finset.card_insert_of_notMem (by simp [hA₁neA₂, hA₁not]),
      Finset.card_insert_of_notMem hA₂not, Finset.card_erase_of_mem hB]
    have hpos : 1 ≤ P.parts.card := Finset.card_pos.mpr ⟨B, hB⟩
    omega
  have hfilt :
      P'.parts.filter (fun D ↦ u ≤ D.card) =
        (P.parts.filter (fun D ↦ u ≤ D.card)).erase B := by
    ext D
    simp only [P', parts', Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨rfl | rfl | ⟨hDne, hDP⟩, hDu⟩
      · omega
      · omega
      · exact ⟨hDne, hDP, hDu⟩
    · rintro ⟨hDne, hDP, hDu⟩
      exact ⟨Or.inr (Or.inr ⟨hDne, hDP⟩), hDu⟩
  have hBfilt : B ∈ P.parts.filter (fun D ↦ u ≤ D.card) :=
    Finset.mem_filter.mpr ⟨hB, hBlo⟩
  refine ⟨P', hle, hcard, ?_⟩
  rw [hfilt, Finset.card_erase_of_mem hBfilt]
  have hpos : 1 ≤ (P.parts.filter (fun D ↦ u ≤ D.card)).card :=
    Finset.card_pos.mpr ⟨B, hBfilt⟩
  omega

/-- Splitting all parts of size `≥ u` (each of size `≤ 2(u - 1)`) refines `P`
to a partition `P'` with `|P'.parts| = |P.parts| + #{B ∈ P : |B| ≥ u}` and all
parts of size `≤ u - 1`. -/
theorem exists_finpartition_split_large_parts {n u : ℕ} (hu : 2 ≤ u) :
    ∀ m : ℕ, ∀ P : VertexPartition n,
      (∀ B ∈ P.parts, B.card ≤ 2 * (u - 1)) →
      (P.parts.filter (fun D ↦ u ≤ D.card)).card = m →
      ∃ P' : VertexPartition n,
        P' ≤ P ∧
          P'.parts.card = P.parts.card + m ∧
          ∀ D ∈ P'.parts, D.card ≤ u - 1 := by
  intro m
  induction m with
  | zero =>
    intro P _ hcard0
    refine ⟨P, le_rfl, by simp, ?_⟩
    intro D hD
    by_contra hgt
    have hmem : D ∈ P.parts.filter (fun X ↦ u ≤ X.card) :=
      Finset.mem_filter.mpr ⟨hD, by omega⟩
    have hpos : 0 < (P.parts.filter (fun X ↦ u ≤ X.card)).card :=
      Finset.card_pos.mpr ⟨D, hmem⟩
    omega
  | succ m ih =>
    intro P hbound hcard
    have hne : (P.parts.filter (fun D ↦ u ≤ D.card)).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨B, hBfilt⟩ := hne
    obtain ⟨hBP, hBlo⟩ := Finset.mem_filter.mp hBfilt
    obtain ⟨P₁, hP₁le, hP₁card, hP₁filt⟩ :=
      split_one_part_finpartition hu P hBP hBlo (hbound B hBP)
    have hP₁bound : ∀ D ∈ P₁.parts, D.card ≤ 2 * (u - 1) := by
      intro D hD
      obtain ⟨C, hCP, hDC⟩ := hP₁le hD
      exact (Finset.card_le_card hDC).trans (hbound C hCP)
    obtain ⟨P', hP'le, hP'card, hP'small⟩ := ih P₁ hP₁bound (by omega)
    refine ⟨P', hP'le.trans hP₁le, by omega, hP'small⟩

/-- Extracting an unordered proper-colouring partition with at most `k` parts
from `chromaticNumberNat G ≤ k`. -/
theorem exists_coloring_partition_card_le_of_chromaticNumberNat_le
    {n k : ℕ} (G : LabeledGraph n) (hchi : chromaticNumberNat G ≤ k) :
    ∃ P : VertexPartition n,
      P.parts.card ≤ k ∧ G ∈ partitionColoringEvent P := by
  classical
  have hcol : G.Colorable k :=
    (colorable_chromaticNumberNat G).mono hchi
  let C : G.Coloring (Fin k) := hcol.some
  let P : VertexPartition n := Finpartition.ofSetoid (Setoid.ker C)
  have hPmem : G ∈ partitionColoringEvent P := by
    intro B hB
    obtain ⟨v, hvB⟩ := P.nonempty_of_mem_parts hB
    have hvpart : P.part v = B := P.part_eq_of_mem hB hvB
    have hsub : (B : Set (Fin n)) ⊆ C.colorClass (C v) := by
      intro w hw
      have hwP : w ∈ P.part v := by rw [hvpart]; exact hw
      have hker : (Setoid.ker C) v w :=
        Finpartition.mem_part_ofSetoid_iff_rel.mp hwP
      exact hker.symm
    exact Set.Pairwise.mono hsub (C.isIndepSet_colorClass (C v))
  have hPcard : P.parts.card ≤ k := by
    let rep : P.parts → Fin n := fun B ↦ (P.nonempty_of_mem_parts B.2).choose
    have rep_mem (B : P.parts) : rep B ∈ B.1 :=
      (P.nonempty_of_mem_parts B.2).choose_spec
    let f : P.parts → Fin k := fun B ↦ C (rep B)
    have hinj : Function.Injective f := by
      intro B D hBD
      have hrel : (Setoid.ker C) (rep B) (rep D) := hBD
      have hmem : rep D ∈ P.part (rep B) :=
        Finpartition.mem_part_ofSetoid_iff_rel.mpr hrel
      have hp : P.part (rep B) = P.part (rep D) :=
        ((P.mem_part_iff_part_eq_part
          (Finset.mem_univ (rep D)) (Finset.mem_univ (rep B))).mp hmem).symm
      apply Subtype.ext
      calc
        B.1 = P.part (rep B) := (P.part_eq_of_mem B.2 (rep_mem B)).symm
        _ = P.part (rep D) := hp
        _ = D.1 := P.part_eq_of_mem D.2 (rep_mem D)
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      Fintype.card_le_of_injective f hinj
  exact ⟨P, hPcard, hPmem⟩

/-- **Colouring refinement claim of Lemma 1.1 (`lem:disjoint-packing`):**
if `2 ≤ u`, `k + d ≤ n`, `α(G) ≤ 2(u - 1)`, `D_u(G) ≤ d`, and `χ(G) ≤ k`,
then `G` admits an exact `(k + d)`-block proper-colouring partition into
nonempty classes of size at most `u - 1`. -/
theorem exists_bounded_coloring_partition_of_maxDisjointIndepGe_le
    {n u k d : ℕ} (hu : 2 ≤ u) (hkd : k + d ≤ n)
    (G : LabeledGraph n)
    (halpha : G.indepNum ≤ 2 * (u - 1))
    (hDu : maxDisjointIndepGe G u ≤ d)
    (hchi : chromaticNumberNat G ≤ k) :
    ∃ Q : VertexPartition n,
      Q.parts.card = k + d ∧
        G ∈ partitionColoringEvent Q ∧
        ∀ D ∈ Q.parts, D.card ≤ u - 1 := by
  classical
  obtain ⟨P, hPcard, hPcol⟩ :=
    exists_coloring_partition_card_le_of_chromaticNumberNat_le G hchi
  have hPbound : ∀ B ∈ P.parts, B.card ≤ 2 * (u - 1) :=
    fun B hB ↦ (hPcol B hB).card_le_indepNum.trans halpha
  let Big := Finset.filter (fun B ↦ u ≤ B.card) P.parts
  have hBigFam : IsDisjointIndepFamilyGe G u Big := by
    refine ⟨?_, ?_⟩
    · intro B hB
      obtain ⟨hBP, hBu⟩ := Finset.mem_filter.mp hB
      exact ⟨hBu, hPcol B hBP⟩
    · exact P.disjoint.subset fun B hB ↦ (Finset.mem_filter.mp hB).1
  have hBigLe : Big.card ≤ d := (card_le_maxDisjointIndepGe hBigFam).trans hDu
  obtain ⟨P', hP'le, hP'card, hP'small⟩ :=
    exists_finpartition_split_large_parts hu Big.card P hPbound rfl
  have hP'col : G ∈ partitionColoringEvent P' := by
    intro D hD
    obtain ⟨B, hBP, hDB⟩ := hP'le hD
    exact Set.Pairwise.mono (by simpa using hDB) (hPcol B hBP)
  have hlo : P'.parts.card ≤ k + d := by omega
  have hhi : k + d ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hkd
  obtain ⟨Q, hQcard, hQP'⟩ := exists_finpartition_refinement_card_eq P' hlo hhi
  refine ⟨Q, hQcard, ?_, ?_⟩
  · intro D hD
    obtain ⟨C, hCP', hDC⟩ := hQP' hD
    exact Set.Pairwise.mono (by simpa using hDC) (hP'col C hCP')
  · intro D hD
    obtain ⟨C, hCP', hDC⟩ := hQP' hD
    exact (Finset.card_le_card hDC).trans (hP'small C hCP')

/-- **Cocolouring refinement claim of Lemma 1.1 (`lem:disjoint-packing`):**
if `2 ≤ u`, `k + 2d ≤ n`, `α(G) ≤ 2(u - 1)`, `α(Gᶜ) ≤ 2(u - 1)`, `D_u(G) ≤ d`,
`D_u(Gᶜ) ≤ d`, and `ζ(G) ≤ k`, then `G` admits an exact `(k + 2d)`-block
cocolouring partition into nonempty classes of size at most `u - 1`. -/
theorem exists_bounded_cocoloring_partition_of_maxDisjointIndepGe_le
    {n u k d : ℕ} (hu : 2 ≤ u) (hk2d : k + 2 * d ≤ n)
    (G : LabeledGraph n)
    (halpha : G.indepNum ≤ 2 * (u - 1))
    (homega : Gᶜ.indepNum ≤ 2 * (u - 1))
    (hDu : maxDisjointIndepGe G u ≤ d)
    (hDuCompl : maxDisjointIndepGe Gᶜ u ≤ d)
    (hzeta : cochromaticNumber G ≤ k) :
    ∃ Q : VertexPartition n,
      Q.parts.card = k + 2 * d ∧
        G ∈ partitionCocoloringEvent Q ∧
        ∀ D ∈ Q.parts, D.card ≤ u - 1 := by
  classical
  obtain ⟨P, hPcard, hPco⟩ :=
    exists_exact_cocoloring_partition_of_cochromaticNumber_le G hzeta (by omega)
  have hPbound : ∀ B ∈ P.parts, B.card ≤ 2 * (u - 1) := by
    intro B hB
    rcases hPco B hB with hind | hcl
    · exact hind.card_le_indepNum.trans halpha
    · have hindC : Gᶜ.IsIndepSet (B : Set (Fin n)) := by
        intro x hx y hy hxy hadj
        exact hadj.2 (hcl hx hy hxy)
      exact hindC.card_le_indepNum.trans homega
  let Big : Finset (Finset (Fin n)) := Finset.filter (fun B : Finset (Fin n) ↦ u ≤ B.card) P.parts
  let BigInd : Finset (Finset (Fin n)) :=
    Finset.filter (fun B : Finset (Fin n) ↦ G.IsIndepSet (B : Set (Fin n))) Big
  let BigClq : Finset (Finset (Fin n)) :=
    Finset.filter (fun B : Finset (Fin n) ↦ ¬ G.IsIndepSet (B : Set (Fin n))) Big
  have hBigSplit : BigInd.card + BigClq.card = Big.card := by
    simpa [BigInd, BigClq] using
      Finset.card_filter_add_card_filter_not
        (s := Big) (p := fun B ↦ G.IsIndepSet (B : Set (Fin n)))
  have hBigIndFam : IsDisjointIndepFamilyGe G u BigInd := by
    refine ⟨?_, ?_⟩
    · intro B hB
      obtain ⟨hBBig, hind⟩ := Finset.mem_filter.mp hB
      exact ⟨(Finset.mem_filter.mp hBBig).2, hind⟩
    · exact P.disjoint.subset fun B hB ↦
        (Finset.mem_filter.mp (Finset.mem_filter.mp hB).1).1
  have hBigClqFam : IsDisjointIndepFamilyGe Gᶜ u BigClq := by
    refine ⟨?_, ?_⟩
    · intro B hB
      obtain ⟨hBBig, hnotind⟩ := Finset.mem_filter.mp hB
      obtain ⟨hBP, hBu⟩ := Finset.mem_filter.mp hBBig
      refine ⟨hBu, ?_⟩
      rcases hPco B hBP with hind | hcl
      · exact (hnotind hind).elim
      · intro x hx y hy hxy hadj
        exact hadj.2 (hcl hx hy hxy)
    · exact P.disjoint.subset fun B hB ↦
        (Finset.mem_filter.mp (Finset.mem_filter.mp hB).1).1
  have hBigIndLe : BigInd.card ≤ d :=
    (card_le_maxDisjointIndepGe hBigIndFam).trans hDu
  have hBigClqLe : BigClq.card ≤ d :=
    (card_le_maxDisjointIndepGe hBigClqFam).trans hDuCompl
  obtain ⟨P', hP'le, hP'card, hP'small⟩ :=
    exists_finpartition_split_large_parts hu Big.card P hPbound rfl
  have hP'co : G ∈ partitionCocoloringEvent P' := by
    intro D hD
    obtain ⟨B, hBP, hDB⟩ := hP'le hD
    rcases hPco B hBP with hind | hcl
    · exact Or.inl (Set.Pairwise.mono (by simpa using hDB) hind)
    · exact Or.inr (Set.Pairwise.mono (by simpa using hDB) hcl)
  have hlo : P'.parts.card ≤ k + 2 * d := by omega
  have hhi : k + 2 * d ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hk2d
  obtain ⟨Q, hQcard, hQP'⟩ := exists_finpartition_refinement_card_eq P' hlo hhi
  refine ⟨Q, hQcard, ?_, ?_⟩
  · intro D hD
    obtain ⟨C, hCP', hDC⟩ := hQP' hD
    rcases hP'co C hCP' with hind | hcl
    · exact Or.inl (Set.Pairwise.mono (by simpa using hDC) hind)
    · exact Or.inr (Set.Pairwise.mono (by simpa using hDC) hcl)
  · intro D hD
    obtain ⟨C, hCP', hDC⟩ := hQP' hD
    exact (Finset.card_le_card hDC).trans (hP'small C hCP')

end

end Erdos625HP
