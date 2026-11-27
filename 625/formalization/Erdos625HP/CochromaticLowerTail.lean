import Erdos625.ColoringProfileProbability

/-!
# Section 4: finite first-moment probability bound for `ζ(G_n) ≤ k`

This module kernel-checks the cochromatic part of Proposition 4.1 (`eq:t4-6`):
1. For any unordered partition `P : VertexPartition n` (including singleton
   parts `|B| = 1`), flipping the edges inside the clique-marked blocks gives a
   bijection on `LabeledGraph n` preserving the uniform `G(n, 1/2)` mass, so
   `P(P is a cocoloring of G) ≤ 2 ^ |P.parts| * P(P is a coloring of G)`.
2. Every graph with `cochromaticNumber G ≤ parts` (`parts ≤ n`) either has an
   exact `parts`-block cocoloring partition of block sizes `≤ b`, or satisfies
   `b < G.indepNum` or `b < Gᶜ.indepNum`.
3. Graph complementation preserves `G(n, 1/2)`, giving
   `P(ζ(G) ≤ parts) ≤ 2 ^ parts * (((n + 1) ^ b) * exp L) + 2 * mu n (b + 1)`.
-/

namespace Erdos625HP

open Erdos625 MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Event that every part of `P` is either independent or a clique in `G`. -/
def partitionCocoloringEvent {n : ℕ} (P : VertexPartition n) :
    Set (LabeledGraph n) :=
  {G | ∀ B ∈ P.parts, G.IsIndepSet (B : Set (Fin n)) ∨ G.IsClique (B : Set (Fin n))}

/-- Event that every part `B : P.parts` has the homogeneity prescribed by `σ B`
(`false` = independent, `true` = clique). -/
def partitionMarkedEvent {n : ℕ} (P : VertexPartition n)
    (σ : P.parts → Bool) : Set (LabeledGraph n) :=
  {G | ∀ B : P.parts,
    if σ B then G.IsClique (B.1 : Set (Fin n)) else G.IsIndepSet (B.1 : Set (Fin n))}

/-- Predicate that `u, v` lie in a common `true`-marked part of `P`. -/
def markedPair {n : ℕ} (P : VertexPartition n) (σ : P.parts → Bool)
    (u v : Fin n) : Prop :=
  ∃ B : P.parts, σ B = true ∧ u ∈ B.1 ∧ v ∈ B.1

theorem markedPair_comm {n : ℕ} (P : VertexPartition n) (σ : P.parts → Bool)
    (u v : Fin n) : markedPair P σ u v ↔ markedPair P σ v u := by
  unfold markedPair
  constructor <;> rintro ⟨B, hσ, h1, h2⟩ <;> exact ⟨B, hσ, h2, h1⟩

/-- Adjacency relation obtained by flipping edges inside `true`-marked parts. -/
def flipMarkedAdj {n : ℕ} (P : VertexPartition n) (σ : P.parts → Bool)
    (G : LabeledGraph n) (u v : Fin n) : Prop := by
  classical
  exact u ≠ v ∧ if markedPair P σ u v then ¬ G.Adj u v else G.Adj u v

/-- Flip edges internal to parts `B : P.parts` with `σ B = true`, leaving all
other pairs unchanged. -/
def flipMarkedInternal {n : ℕ} (P : VertexPartition n)
    (σ : P.parts → Bool) (G : LabeledGraph n) : LabeledGraph n where
  Adj := flipMarkedAdj P σ G
  symm := ⟨by
    classical
    intro u v huv
    unfold flipMarkedAdj at huv ⊢
    refine ⟨huv.1.symm, ?_⟩
    by_cases hm : markedPair P σ u v
    · have hmv : markedPair P σ v u := (markedPair_comm P σ u v).mp hm
      rw [if_pos hm] at huv
      rw [if_pos hmv]
      exact fun hadj ↦ huv.2 (G.adj_symm hadj)
    · have hmv : ¬ markedPair P σ v u :=
        fun hc ↦ hm ((markedPair_comm P σ u v).mpr hc)
      rw [if_neg hm] at huv
      rw [if_neg hmv]
      exact G.adj_symm huv.2⟩
  loopless := ⟨fun u hu ↦ hu.1 rfl⟩

/-- `flipMarkedInternal P σ` is an involution on `LabeledGraph n`. -/
theorem flipMarkedInternal_involutive {n : ℕ} (P : VertexPartition n)
    (σ : P.parts → Bool) :
    Function.Involutive (flipMarkedInternal P σ) := by
  classical
  intro G
  ext u v
  change flipMarkedAdj P σ (flipMarkedInternal P σ G) u v ↔ G.Adj u v
  unfold flipMarkedAdj
  change (u ≠ v ∧
    if markedPair P σ u v then ¬ flipMarkedAdj P σ G u v
    else flipMarkedAdj P σ G u v) ↔ G.Adj u v
  unfold flipMarkedAdj
  by_cases huv : u = v
  · subst v
    constructor
    · intro h
      exact (h.1 rfl).elim
    · intro h
      exact (G.ne_of_adj h rfl).elim
  · by_cases hm : markedPair P σ u v
    · simp [huv, hm]
    · simp [huv, hm]

/-- If `G ∈ partitionMarkedEvent P σ`, then `flipMarkedInternal P σ G` makes
every part of `P` independent (including singleton parts vacuously). -/
theorem flipMarkedInternal_mem_partitionColoringEvent {n : ℕ}
    {P : VertexPartition n} {σ : P.parts → Bool} {G : LabeledGraph n}
    (hG : G ∈ partitionMarkedEvent P σ) :
    flipMarkedInternal P σ G ∈ partitionColoringEvent P := by
  classical
  intro D hD u hu v hv huv hadj
  change flipMarkedAdj P σ G u v at hadj
  unfold flipMarkedAdj at hadj
  have huD : u ∈ D := by simpa using hu
  have hvD : v ∈ D := by simpa using hv
  have hB_eq : ∀ B : P.parts, u ∈ B.1 → B = ⟨D, hD⟩ := by
    intro B huB
    apply Subtype.ext
    by_contra hne
    exact (Finset.disjoint_left.mp (P.disjoint B.2 hD hne) huB) huD
  have hDspec := hG ⟨D, hD⟩
  cases hσD : σ ⟨D, hD⟩
  · simp only [hσD] at hDspec
    have hnot : ¬ markedPair P σ u v := by
      rintro ⟨B, hσB, huB, -⟩
      rw [hB_eq B huB, hσD] at hσB
      exact Bool.false_ne_true hσB
    have hadj_ite := hadj.2
    rw [if_neg hnot] at hadj_ite
    exact hDspec hu hv huv hadj_ite
  · simp only [hσD, ↓reduceIte] at hDspec
    have hex : markedPair P σ u v := ⟨⟨D, hD⟩, hσD, huD, hvD⟩
    have hadj_ite := hadj.2
    rw [if_pos hex] at hadj_ite
    exact hadj_ite (hDspec hu hv huv)

/-- Measure preservation under any involution on `LabeledGraph n` in `G(n, 1/2)`. -/
theorem randomGraphMeasure_image_le_of_involutive {n : ℕ}
    {S T : Set (LabeledGraph n)} (f : LabeledGraph n → LabeledGraph n)
    (hf : Function.Involutive f) (hST : ∀ G ∈ S, f G ∈ T) :
    randomGraphMeasure n S ≤ randomGraphMeasure n T := by
  classical
  let FS := (Finset.univ : Finset (LabeledGraph n)).filter (· ∈ S)
  let FT := (Finset.univ : Finset (LabeledGraph n)).filter (· ∈ T)
  have hinj : Function.Injective f := hf.injective
  have himg : FS.image f ⊆ FT := by
    intro H hH
    rcases Finset.mem_image.mp hH with ⟨G, hGS, rfl⟩
    simp only [FS, FT, Finset.mem_filter, Finset.mem_univ, true_and] at hGS ⊢
    exact hST G hGS
  have hcard : FS.card ≤ FT.card := by
    calc
      FS.card = (FS.image f).card := (Finset.card_image_of_injective FS hinj).symm
      _ ≤ FT.card := Finset.card_le_card himg
  have hmeas (U : Set (LabeledGraph n))
      (FU : Finset (LabeledGraph n)) (hFU : ∀ G, G ∈ FU ↔ G ∈ U) :
      randomGraphMeasure n U =
        (FU.card : ENNReal) * (1 / 2 : ENNReal) ^ n.choose 2 := by
    calc
      randomGraphMeasure n U = randomGraphMeasure n (FU : Set (LabeledGraph n)) := by
        congr 1; ext G; exact (hFU G).symm
      _ = ∑ G ∈ FU, randomGraphMeasure n {G} := by
        rw [MeasureTheory.sum_measure_singleton]
      _ = ∑ _G ∈ FU, (1 / 2 : ENNReal) ^ n.choose 2 := by
        simp_rw [randomGraphMeasure_singleton_uniform]
      _ = (FU.card : ENNReal) * (1 / 2 : ENNReal) ^ n.choose 2 := by
        simp [Finset.sum_const, nsmul_eq_mul]
  rw [hmeas S FS (fun G ↦ by simp [FS]), hmeas T FT (fun G ↦ by simp [FT])]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) zero_le

/-- Fixed-marking cocoloring probability is at most the proper-coloring probability. -/
theorem randomGraphMeasure_partitionMarkedEvent_le {n : ℕ}
    (P : VertexPartition n) (σ : P.parts → Bool) :
    randomGraphMeasure n (partitionMarkedEvent P σ) ≤
      randomGraphMeasure n (partitionColoringEvent P) :=
  randomGraphMeasure_image_le_of_involutive (flipMarkedInternal P σ)
    (flipMarkedInternal_involutive P σ)
    (fun _ hG ↦ flipMarkedInternal_mem_partitionColoringEvent hG)

/-- **Section 4 partition inequality:** for any partition `P` (even with
singletons), `P(P is a cocoloring) ≤ 2 ^ |P.parts| * P(P is a coloring)`. -/
theorem randomGraphMeasure_partitionCocoloringEvent_le_two_pow_mul {n : ℕ}
    (P : VertexPartition n) :
    randomGraphMeasure n (partitionCocoloringEvent P) ≤
      (2 : ENNReal) ^ P.parts.card *
        randomGraphMeasure n (partitionColoringEvent P) := by
  classical
  have hcov : partitionCocoloringEvent P ⊆
      ⋃ σ : P.parts → Bool, partitionMarkedEvent P σ := by
    intro G hG
    rw [Set.mem_iUnion]
    refine ⟨fun B ↦ decide (G.IsClique (B.1 : Set (Fin n))), ?_⟩
    intro B
    by_cases hcl : G.IsClique (B.1 : Set (Fin n))
    · simp [hcl]
    · simp only [hcl, decide_false, Bool.false_eq_true, ↓reduceIte]
      rcases hG B.1 B.2 with hind | hcl'
      · exact hind
      · exact (hcl hcl').elim
  calc
    randomGraphMeasure n (partitionCocoloringEvent P) ≤
        randomGraphMeasure n (⋃ σ : P.parts → Bool, partitionMarkedEvent P σ) :=
      measure_mono hcov
    _ ≤ ∑ σ : P.parts → Bool, randomGraphMeasure n (partitionMarkedEvent P σ) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _σ : P.parts → Bool, randomGraphMeasure n (partitionColoringEvent P) :=
      Finset.sum_le_sum fun σ _ ↦ randomGraphMeasure_partitionMarkedEvent_le P σ
    _ = (Fintype.card (P.parts → Bool) : ENNReal) *
          randomGraphMeasure n (partitionColoringEvent P) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = (2 : ENNReal) ^ P.parts.card *
          randomGraphMeasure n (partitionColoringEvent P) := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
      norm_cast

/-- Extracting a `VertexPartition n` with at most `k` homogeneous parts from a
cocolouring with palette `Fin k`, then refining to **exactly** `k` parts (`k ≤ n`). -/
theorem exists_exact_cocoloring_partition_of_cochromaticNumber_le
    {n k : ℕ} (G : LabeledGraph n)
    (hzeta : cochromaticNumber G ≤ k) (hkn : k ≤ n) :
    ∃ Q : VertexPartition n,
      Q.parts.card = k ∧ G ∈ partitionCocoloringEvent Q := by
  classical
  have hco : CoColorable G k :=
    (coColorable_iff_cochromaticNumber_le G).mpr hzeta
  let C : CoColoring G (Fin k) := hco.some
  let P : VertexPartition n := Finpartition.ofSetoid (Setoid.ker C.color)
  have hPmem : G ∈ partitionCocoloringEvent P := by
    intro B hB
    obtain ⟨v, hvB⟩ := P.nonempty_of_mem_parts hB
    have hvpart : P.part v = B := P.part_eq_of_mem hB hvB
    have hsub : (B : Set (Fin n)) ⊆ C.colorClass (C.color v) := by
      intro w hw
      have hwP : w ∈ P.part v := by rw [hvpart]; exact hw
      have hker : (Setoid.ker C.color) v w :=
        Finpartition.mem_part_ofSetoid_iff_rel.mp hwP
      exact hker.symm
    cases hkind : C.kind (C.color v) with
    | independent =>
      exact Or.inl (Set.Pairwise.mono hsub (C.valid_independent hkind))
    | clique =>
      exact Or.inr (Set.Pairwise.mono hsub (C.valid_clique hkind))
  have hPcard : P.parts.card ≤ k := by
    let rep : P.parts → Fin n := fun B ↦ (P.nonempty_of_mem_parts B.2).choose
    have rep_mem (B : P.parts) : rep B ∈ B.1 :=
      (P.nonempty_of_mem_parts B.2).choose_spec
    let f : P.parts → Fin k := fun B ↦ C.color (rep B)
    have hinj : Function.Injective f := by
      intro B D hBD
      have hrel : (Setoid.ker C.color) (rep B) (rep D) := hBD
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
  have hhi : k ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hkn
  obtain ⟨Q, hQcard, hQP⟩ := exists_finpartition_refinement_card_eq P hPcard hhi
  refine ⟨Q, hQcard, ?_⟩
  intro D hD
  obtain ⟨B, hB, hDB⟩ := hQP hD
  rcases hPmem B hB with hind | hcl
  · exact Or.inl (Set.Pairwise.mono (by simpa using hDB) hind)
  · exact Or.inr (Set.Pairwise.mono (by simpa using hDB) hcl)

/-- Graph complementation preserves the independence-number tail in `G(n, 1/2)`. -/
theorem randomGraphMeasure_compl_independenceNumberExceeds_le_mu_succ
    (n b : ℕ) :
    randomGraphMeasure n {G : LabeledGraph n | b < Gᶜ.indepNum} ≤
      ENNReal.ofReal (mu n (b + 1)) := by
  have hle :
      randomGraphMeasure n {G : LabeledGraph n | b < Gᶜ.indepNum} ≤
        randomGraphMeasure n (independenceNumberExceedsEvent n b) :=
    randomGraphMeasure_image_le_of_involutive (fun G : LabeledGraph n ↦ Gᶜ)
      compl_involutive (fun G hG ↦ hG)
  exact le_trans hle (randomGraphMeasure_independenceNumberExceeds_le_mu_succ n b)

/-- **Proposition 4.1 (`eq:t4-6`, cochromatic lower-tail reduction):** for any
`parts ≤ n`, the `G(n, 1/2)` probability that `ζ(G) ≤ parts` is at most
`2 ^ parts * boundedProfileColoringExpectation n b parts + 2 * mu n (b + 1)`. -/
theorem randomGraphMeasure_cochromaticNumberAtMost_le_two_pow_mul_expectation_add_two_mu
    {n b parts : ℕ} (hparts : parts ≤ n) :
    randomGraphMeasure n {G : LabeledGraph n | cochromaticNumber G ≤ parts} ≤
      (2 : ENNReal) ^ parts * boundedProfileColoringExpectation n b parts +
        2 * ENNReal.ofReal (mu n (b + 1)) := by
  classical
  let GoodP : Set (LabeledGraph n) :=
    ⋃ k ∈ boundedColoringProfiles n b parts,
      ⋃ P : ProfilePartition n k, partitionCocoloringEvent P.1
  have hcov :
      {G : LabeledGraph n | cochromaticNumber G ≤ parts} ⊆
        GoodP ∪ (independenceNumberExceedsEvent n b ∪
          {G : LabeledGraph n | b < Gᶜ.indepNum}) := by
    intro G hzeta
    by_cases hind : G.indepNum ≤ b
    · by_cases hcl : Gᶜ.indepNum ≤ b
      · left
        obtain ⟨Q, hQcard, hQco⟩ :=
          exists_exact_cocoloring_partition_of_cochromaticNumber_le G hzeta hparts
        have hQbound : ∀ B ∈ Q.parts, B.card ≤ b := by
          intro B hB
          rcases hQco B hB with hBind | hBcl
          · exact hBind.card_le_indepNum.trans hind
          · have hBindCompl : Gᶜ.IsIndepSet (B : Set (Fin n)) := by
              intro u hu v hv huv hadj
              exact hadj.2 (hBcl hu hv huv)
            exact hBindCompl.card_le_indepNum.trans hcl
        let kp : ColoringProfile b := vertexPartitionProfile b Q
        let Qp : ProfilePartition n kp := vertexPartitionAsProfilePartition Q hQbound
        have hkp : kp ∈ boundedColoringProfiles n b parts :=
          mem_boundedColoringProfiles_of_constraints Qp.vertexMass_eq
            (Qp.card_parts_eq.symm.trans hQcard)
        exact Set.mem_biUnion hkp (Set.mem_iUnion.mpr ⟨Qp, hQco⟩)
      · right; right; exact not_le.mp hcl
    · right; left; exact not_le.mp hind
  have hGoodP_le :
      randomGraphMeasure n GoodP ≤
        (2 : ENNReal) ^ parts * boundedProfileColoringExpectation n b parts := by
    calc
      randomGraphMeasure n GoodP ≤
          ∑ k ∈ boundedColoringProfiles n b parts,
            randomGraphMeasure n
              (⋃ P : ProfilePartition n k, partitionCocoloringEvent P.1) :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ boundedColoringProfiles n b parts,
            ∑ P : ProfilePartition n k,
              randomGraphMeasure n (partitionCocoloringEvent P.1) :=
        Finset.sum_le_sum fun k _ ↦ measure_iUnion_fintype_le _ _
      _ ≤ ∑ k ∈ boundedColoringProfiles n b parts,
            ∑ P : ProfilePartition n k,
              (2 : ENNReal) ^ parts *
                randomGraphMeasure n (partitionColoringEvent P.1) := by
        refine Finset.sum_le_sum fun k hk ↦ Finset.sum_le_sum fun P _ ↦ ?_
        have hkparts : P.1.parts.card = parts :=
          P.card_parts_eq.trans ((mem_boundedColoringProfiles k).mp hk).2
        simpa [hkparts] using
          randomGraphMeasure_partitionCocoloringEvent_le_two_pow_mul P.1
      _ = (2 : ENNReal) ^ parts * boundedProfileColoringExpectation n b parts := by
        rw [boundedProfileColoringExpectation_eq_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [← Finset.mul_sum, profileColoringExpectation_eq_card_mul]
        simp_rw [randomGraphMeasure_partitionColoringEvent]
        simp [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card]
  calc
    randomGraphMeasure n {G : LabeledGraph n | cochromaticNumber G ≤ parts} ≤
        randomGraphMeasure n (GoodP ∪ (independenceNumberExceedsEvent n b ∪
          {G : LabeledGraph n | b < Gᶜ.indepNum})) :=
      measure_mono hcov
    _ ≤ randomGraphMeasure n GoodP +
          randomGraphMeasure n (independenceNumberExceedsEvent n b ∪
            {G : LabeledGraph n | b < Gᶜ.indepNum}) :=
      measure_union_le _ _
    _ ≤ randomGraphMeasure n GoodP +
          (randomGraphMeasure n (independenceNumberExceedsEvent n b) +
            randomGraphMeasure n {G : LabeledGraph n | b < Gᶜ.indepNum}) :=
      add_le_add le_rfl (measure_union_le _ _)
    _ ≤ (2 : ENNReal) ^ parts * boundedProfileColoringExpectation n b parts +
          (ENNReal.ofReal (mu n (b + 1)) + ENNReal.ofReal (mu n (b + 1))) :=
      add_le_add hGoodP_le
        (add_le_add (randomGraphMeasure_independenceNumberExceeds_le_mu_succ n b)
          (randomGraphMeasure_compl_independenceNumberExceeds_le_mu_succ n b))
    _ = (2 : ENNReal) ^ parts * boundedProfileColoringExpectation n b parts +
          2 * ENNReal.ofReal (mu n (b + 1)) := by
      rw [two_mul]

/-- **Box-and-Stirling form of Proposition 4.1 (`eq:t4-6`, cochromatic part).** -/
theorem randomGraphMeasure_cochromaticNumberAtMost_le_two_pow_mul_box_add_two_mu
    {n b parts : ℕ} (L : ℝ) (hparts : parts ≤ n)
    (hL : ∀ k ∈ boundedColoringProfiles n b parts,
      profileStirlingUpperMain n k + factorialLogErrorBound n ≤ L) :
    randomGraphMeasure n {G : LabeledGraph n | cochromaticNumber G ≤ parts} ≤
      (2 : ENNReal) ^ parts *
        ((((n + 1) ^ b : ℕ) : ENNReal) * ENNReal.ofReal (Real.exp L)) +
      2 * ENNReal.ofReal (mu n (b + 1)) := by
  calc
    randomGraphMeasure n {G : LabeledGraph n | cochromaticNumber G ≤ parts} ≤
        (2 : ENNReal) ^ parts * boundedProfileColoringExpectation n b parts +
          2 * ENNReal.ofReal (mu n (b + 1)) :=
      randomGraphMeasure_cochromaticNumberAtMost_le_two_pow_mul_expectation_add_two_mu
        hparts
    _ ≤ (2 : ENNReal) ^ parts *
          ((((n + 1) ^ b : ℕ) : ENNReal) * ENNReal.ofReal (Real.exp L)) +
        2 * ENNReal.ofReal (mu n (b + 1)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (boundedProfileColoringExpectation_le_box_mul_exp n b parts L hL)
          zero_le)
        le_rfl

end

end Erdos625HP
