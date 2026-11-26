import Erdos625HP.BoundedLowerTailsAndMomentCore
import Erdos625HP.PairMomentAndPhaseAsymptotics

/-!
# Unconditional `(k + 2d)` / `(k + 4d)` class splitting, integer rounding, and quasi-exponential `exp(-2 n / (log n)^10)` tails

This module kernel-checks the mathematical upgrades of the 15-page v7 manuscript:

1. **Unconditional Lemma 1.1 (`lem:disjoint-packing`, zero `α(G)` / `ω(G)` hypothesis):**
   * `splitCost_eq_natCeil_sub_one_and_le_two_mul_div`: for `2 ≤ u` and `1 ≤ m`,
     `(m - 1) / (u - 1) = ⌈m / (u - 1)⌉₊ - 1 ≤ 2 * (m / u)`.
   * `exists_finpartition_unconditional_split_large_parts`: any `P : VertexPartition n`
     refines to `P' ≤ P` with all parts of size `≤ u - 1` (`2 ≤ u`) and
     `P'.parts.card = P.parts.card + ∑ B ∈ P.parts, splitCost u B.card`.
   * `exists_unconditional_bounded_coloring_partition_of_maxDisjointIndepGe_le` and
     `exists_unconditional_bounded_cocoloring_partition_of_maxDisjointIndepGe_le`:
     for **every** graph `G` on `Fin n` (with **no** bound on `α(G)` or `ω(G)`),
     `D_u(G) ≤ d` refines any `k`-coloring to an exact `(k + 2d)`-coloring of max
     class size `≤ u - 1`, and `D_u(G), D_u(Gᶜ) ≤ d` refines any `k`-cocoloring to
     an exact `(k + 4d)`-cocoloring of max class size `≤ u - 1`.

2. **Unconditional finite Proposition 4.1(i) lower-tail reductions (no `X_{α+2} ≥ 2` event):**
   * `randomGraph_chromaticNumberAtMost_le_of_unconditional_splitting` and
     `randomGraph_cochromaticNumberAtMost_le_of_unconditional_splitting`:
     bound `P(χ(G_n) ≤ k)` and `P(ζ(G_n) ≤ k)` directly by the `D_u` McDiarmid tail
     `exp(-2 t^2 / (n - 1))` (resp. `2 * exp(-2 t^2 / (n - 1))`) plus the bounded-profile
     first-moment expectation at `k + 2d` (resp. `k + 4d`).

3. **Proposition 5.3 deterministic two-coordinate integer profile rounding (`Δk₃, Δk₄`):**
   * `roundedWindowProfile_conservation_and_error`: rounding `k * p_i` by floor on
     `S_{m,M} = {m + 1, ..., m + M}` (`m ∈ {0, 1}`, `M ≥ 4`) and adjusting only
     `i ∈ {3, 4}` preserves `∑_i k_i = k` and `∑_i (α - i) k_i = n` exactly with
     uniform `ℓ_∞` error `|k_i - k p_i| ≤ (m + M + 4) * M + 1`.

4. **Universal `a_n = 2 n / (log n)^5` allowance, `exp(-2 n / (log n)^10)` tails, and MGF convergence:**
   * `universalAllowance_isLittleO`, `quasiExpTail_isBigO_polylogTail`,
     `summable_quasiExpTail`, and `randomGraph_packingPair_gt_universalShift_le`.
   * `regime_cochromatic_and_chromatic_upperTail_quasiExp_of_secondMoment_seed`:
     Corollary 8.1 (`cor:zeta-upper`) with universal `a_n = 2 n / (log n)^5` and
     quasi-exponential upper tail `≤ exp(-2 n / (log n)^10)`.
   * `tendsto_mgf_normalizedGap_of_quasiExp_tail`,
     `mainTheorem_ae_lp_expectation_and_mgf_of_quasiExp_tail`, and
     `phaseRefinement_expectation_and_ae_of_quasiExp_tail`: full Main Theorem
     (arbitrary-coupling almost-sure, `L^p` for `1 ≤ p < ∞`, expectation, and MGF
     `E[exp(t Y_n)] → exp(t / 4)` for all `t ∈ ℝ`) and Phase Refinement assemblies.
-/

namespace Erdos625HP

open Erdos625 Erdos625.FiveSizeEntropyGap Filter Asymptotics MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

/-! ## 1. Unconditional class splitting (`Lemma 1.1`, zero `α(G)` / `ω(G)` bound) -/

/-- Exact number of extra classes created when splitting a nonempty class of size `m`
into chunks of size at most `u - 1`: `(m - 1) / (u - 1)`. -/
def splitCost (u m : ℕ) : ℕ :=
  (m - 1) / (u - 1)

/-- **Elementary splitting inequality (`Lemma 1.1` proof):**
for `2 ≤ u` and `1 ≤ m`, `splitCost u m = ⌈m / (u - 1)⌉₊ - 1` and
`splitCost u m ≤ 2 * (m / u)` because `m ≤ (⌊m / u⌋ + 1) u - 1 ≤ (2 ⌊m / u⌋ + 1)(u - 1)`. -/
theorem splitCost_eq_natCeil_sub_one_and_le_two_mul_div {u m : ℕ}
    (hu : 2 ≤ u) (hm : 1 ≤ m) :
    splitCost u m = Nat.ceil ((m : ℝ) / ((u - 1 : ℕ) : ℝ)) - 1 ∧
      splitCost u m ≤ 2 * (m / u) := by
  have hu1_pos : 0 < u - 1 := by omega
  have hu1R_pos : (0 : ℝ) < ((u - 1 : ℕ) : ℝ) := by exact_mod_cast hu1_pos
  set qm : ℕ := m - 1
  set d : ℕ := u - 1
  have hm_eq : m = qm + 1 := (Nat.sub_add_cancel hm).symm
  -- Part 1: `(m - 1) / (u - 1) = ⌈m / (u - 1)⌉₊ - 1`
  have hceil_eq : Nat.ceil ((m : ℝ) / ((u - 1 : ℕ) : ℝ)) = qm / d + 1 := by
    rw [Nat.ceil_eq_iff (Nat.succ_ne_zero _)]
    have hdiv_mod : (qm / d) * d + qm % d = qm := by
      simpa [Nat.mul_comm] using Nat.div_add_mod qm d
    have hmod_lt : qm % d < d := Nat.mod_lt qm hu1_pos
    have hlo_nat : (qm / d) * d < m := by omega
    have hhi_nat : m ≤ (qm / d + 1) * d := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    constructor
    · rw [lt_div_iff₀ hu1R_pos]
      simpa [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using
        (show (((qm / d) * d : ℕ) : ℝ) < (m : ℝ) by exact_mod_cast hlo_nat)
    · rw [div_le_iff₀ hu1R_pos]
      exact_mod_cast hhi_nat
  refine ⟨?_, ?_⟩
  · dsimp [splitCost, qm, d]
    rw [hceil_eq, Nat.add_sub_cancel]
  -- Part 2: `(m - 1) / (u - 1) ≤ 2 * (m / u)`
  set q : ℕ := m / u
  have hmu_div : u * q + m % u = m := Nat.div_add_mod m u
  have hmu_mod : m % u < u := Nat.mod_lt m (by omega)
  have hlt_mul : m - 1 < (2 * q + 1) * (u - 1) := by
    have hq_ineq : 0 ≤ q * (u - 2) := Nat.zero_le _
    have hu_split : u = (u - 2) + 2 := by omega
    have hu1_split : u - 1 = (u - 2) + 1 := by omega
    nlinarith
  have hdiv_lt : (m - 1) / (u - 1) < 2 * q + 1 :=
    (Nat.div_lt_iff_lt_mul hu1_pos).mpr hlt_mul
  unfold splitCost
  omega

private theorem splitCost_eq_zero_of_le {u m : ℕ} (hu : 2 ≤ u) (hle : m ≤ u - 1) :
    splitCost u m = 0 := by
  unfold splitCost
  exact Nat.div_eq_of_lt (by omega)

private theorem splitCost_sub_pred {u m : ℕ} (hu : 2 ≤ u) (hge : u ≤ m) :
    splitCost u (m - (u - 1)) + 1 = splitCost u m := by
  unfold splitCost
  have hd : 0 < u - 1 := by omega
  have heq : m - 1 = (m - (u - 1) - 1) + (u - 1) := by omega
  rw [heq, Nat.add_div_right _ hd]

private theorem peel_one_chunk_finpartition {n u : ℕ} (hu : 2 ≤ u)
    (P : VertexPartition n) {B : Finset (Fin n)} (hB : B ∈ P.parts)
    (hBlo : u ≤ B.card) :
    ∃ P' : VertexPartition n,
      P' ≤ P ∧
        P'.parts.card = P.parts.card + 1 ∧
        (∑ D ∈ P'.parts, splitCost u D.card) + 1 =
          ∑ D ∈ P.parts, splitCost u D.card := by
  classical
  obtain ⟨A₁, hA₁sub, hA₁card⟩ :=
    Finset.exists_subset_card_eq (s := B) (n := u - 1) (by omega)
  let A₂ : Finset (Fin n) := B \ A₁
  have hA₂card : A₂.card = B.card - (u - 1) := by
    dsimp [A₂]
    rw [Finset.card_sdiff_of_subset hA₁sub, hA₁card]
  have hA₁ne : A₁.Nonempty := Finset.card_pos.mp (by omega)
  have hA₂ne : A₂.Nonempty := Finset.card_pos.mp (by omega)
  have hdisj12 : Disjoint A₁ A₂ := disjoint_sdiff_self_right
  have hunion : A₁ ∪ A₂ = B := Finset.union_sdiff_of_subset hA₁sub
  have hA₂sub : A₂ ⊆ B := Finset.sdiff_subset
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
  have hA₁not2 : A₁ ∉ insert A₂ (P.parts.erase B) := by
    simp [hA₁neA₂, hA₁not]
  have hcard : P'.parts.card = P.parts.card + 1 := by
    dsimp [P', parts']
    rw [Finset.card_insert_of_notMem hA₁not2,
      Finset.card_insert_of_notMem hA₂not, Finset.card_erase_of_mem hB]
    have hpos : 1 ≤ P.parts.card := Finset.card_pos.mpr ⟨B, hB⟩
    omega
  have hsum : (∑ D ∈ P'.parts, splitCost u D.card) + 1 =
      ∑ D ∈ P.parts, splitCost u D.card := by
    dsimp [P', parts']
    rw [Finset.sum_insert hA₁not2, Finset.sum_insert hA₂not,
      hA₁card, splitCost_eq_zero_of_le hu le_rfl, zero_add, hA₂card]
    have herase := (Finset.add_sum_erase P.parts (fun D ↦ splitCost u D.card) hB).symm
    have hstep := splitCost_sub_pred hu hBlo
    omega
  exact ⟨P', hle, hcard, hsum⟩

/-- **Unconditional partition splitting (`Lemma 1.1`):**
for `2 ≤ u`, every `P : VertexPartition n` refines to `P' ≤ P` whose parts all
have size at most `u - 1`, with exact part count
`P'.parts.card = P.parts.card + ∑ B ∈ P.parts, splitCost u B.card`. -/
theorem exists_finpartition_unconditional_split_large_parts {n u : ℕ}
    (hu : 2 ≤ u) (P : VertexPartition n) :
    ∃ P' : VertexPartition n,
      P' ≤ P ∧
        P'.parts.card = P.parts.card + ∑ B ∈ P.parts, splitCost u B.card ∧
        ∀ D ∈ P'.parts, D.card ≤ u - 1 := by
  classical
  have hmain : ∀ K : ℕ, ∀ Q : VertexPartition n,
      ∑ B ∈ Q.parts, splitCost u B.card = K →
      ∃ Q' : VertexPartition n,
        Q' ≤ Q ∧
          Q'.parts.card = Q.parts.card + K ∧
          ∀ D ∈ Q'.parts, D.card ≤ u - 1 := by
    intro K
    induction K with
    | zero =>
      intro Q hK0
      refine ⟨Q, le_rfl, by simp, ?_⟩
      intro D hD
      have hD0 : splitCost u D.card = 0 :=
        (Finset.sum_eq_zero_iff.mp hK0) D hD
      unfold splitCost at hD0
      have hlt : D.card - 1 < u - 1 :=
        Nat.lt_of_div_eq_zero (by omega) hD0
      omega
    | succ K ih =>
      intro Q hK
      have hex : ∃ B ∈ Q.parts, 0 < splitCost u B.card := by
        by_contra hall
        have h0 : ∑ B ∈ Q.parts, splitCost u B.card = 0 :=
          Finset.sum_eq_zero fun B hB ↦
            Nat.eq_zero_of_not_pos fun hp ↦ hall ⟨B, hB, hp⟩
        omega
      obtain ⟨B, hBQ, hBpos⟩ := hex
      have hBlo : u ≤ B.card := by
        by_contra hlt
        rw [splitCost_eq_zero_of_le hu (by omega)] at hBpos
        omega
      obtain ⟨Q₁, hQ₁le, hQ₁card, hQ₁sum⟩ :=
        peel_one_chunk_finpartition hu Q hBQ hBlo
      obtain ⟨Q', hQ'le, hQ'card, hQ'small⟩ := ih Q₁ (by omega)
      exact ⟨Q', hQ'le.trans hQ₁le, by omega, hQ'small⟩
  exact hmain (∑ B ∈ P.parts, splitCost u B.card) P rfl

private theorem exists_disjoint_subsets_card_eq_div {α : Type*} [DecidableEq α]
    {u : ℕ} (hu : 1 ≤ u) :
    ∀ k : ℕ, ∀ B : Finset α, B.card = k →
      ∃ F : Finset (Finset α),
        F.card = B.card / u ∧
          (F : Set (Finset α)).PairwiseDisjoint id ∧
          ∀ A ∈ F, A ⊆ B ∧ A.card = u := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro B hBk
    by_cases hlt : B.card < u
    · refine ⟨∅, ?_, by simp, by simp⟩
      rw [Nat.div_eq_of_lt hlt, Finset.card_empty]
    · have hge : u ≤ B.card := not_lt.mp hlt
      obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hge
      let B' : Finset α := B \ A
      have hB'card : B'.card = B.card - u := by
        dsimp [B']
        rw [Finset.card_sdiff_of_subset hAsub, hAcard]
      have hB'lt : B'.card < k := by omega
      obtain ⟨F', hF'card, hF'disj, hF'sub⟩ := ih B'.card hB'lt B' rfl
      have hAnot : A ∉ F' := by
        intro hmem
        obtain ⟨hAB', _⟩ := hF'sub A hmem
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
        exact (Finset.mem_sdiff.mp (hAB' hx)).2 hx
      refine ⟨insert A F', ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hAnot, hF'card, hB'card]
        have heq : B.card = (B.card - u) + u := (Nat.sub_add_cancel hge).symm
        conv_rhs => rw [heq, Nat.add_div_right _ (by omega)]
      · rw [Finset.coe_insert]
        refine hF'disj.insert fun C hCF' _ ↦ ?_
        have hCB' : C ⊆ B \ A := (hF'sub C hCF').1
        exact Disjoint.mono_right hCB' disjoint_sdiff_self_right
      · intro C hC
        rcases Finset.mem_insert.mp hC with rfl | hCF'
        · exact ⟨hAsub, hAcard⟩
        · exact ⟨(hF'sub C hCF').1.trans Finset.sdiff_subset, (hF'sub C hCF').2⟩

private theorem sum_div_le_maxDisjointIndepGe {n u : ℕ} (hu : 1 ≤ u)
    (G : LabeledGraph n) (S : Finset (Finset (Fin n)))
    (hdisj : (S : Set (Finset (Fin n))).PairwiseDisjoint id)
    (hind : ∀ B ∈ S, G.IsIndepSet (B : Set (Fin n))) :
    ∑ B ∈ S, (B.card / u) ≤ maxDisjointIndepGe G u := by
  classical
  have hex : ∀ B : Finset (Fin n),
      ∃ F : Finset (Finset (Fin n)),
        F.card = B.card / u ∧
          (F : Set (Finset (Fin n))).PairwiseDisjoint id ∧
          ∀ A ∈ F, A ⊆ B ∧ A.card = u :=
    fun B ↦ exists_disjoint_subsets_card_eq_div hu B.card B rfl
  choose F hFcard hFdisj hFsub using hex
  let Fam : Finset (Finset (Fin n)) := S.biUnion F
  have hdisj_fam : ∀ B₁ ∈ S, ∀ B₂ ∈ S, B₁ ≠ B₂ → Disjoint (F B₁) (F B₂) := by
    intro B₁ hB₁ B₂ hB₂ hne
    rw [Finset.disjoint_left]
    intro A hA₁ hA₂
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < A.card by rw [(hFsub B₁ A hA₁).2]; omega)
    exact (Finset.disjoint_left.mp (hdisj hB₁ hB₂ hne) ((hFsub B₁ A hA₁).1 hx))
      ((hFsub B₂ A hA₂).1 hx)
  have hFam_card : Fam.card = ∑ B ∈ S, (B.card / u) := by
    dsimp [Fam]
    rw [Finset.card_biUnion hdisj_fam]
    exact Finset.sum_congr rfl fun B _ ↦ hFcard B
  have hFam_valid : IsDisjointIndepFamilyGe G u Fam := by
    refine ⟨?_, ?_⟩
    · intro A hA
      obtain ⟨B, hBS, hAF⟩ := Finset.mem_biUnion.mp hA
      obtain ⟨hAB, hAu⟩ := hFsub B A hAF
      exact ⟨hAu.symm.le, Set.Pairwise.mono (by simpa using hAB) (hind B hBS)⟩
    · intro A₁ hA₁ A₂ hA₂ hne
      obtain ⟨B₁, hB₁S, hA₁F⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hA₁)
      obtain ⟨B₂, hB₂S, hA₂F⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hA₂)
      by_cases hBB : B₁ = B₂
      · subst hBB
        exact hFdisj B₁ hA₁F hA₂F hne
      · exact Disjoint.mono (hFsub B₁ A₁ hA₁F).1 (hFsub B₂ A₂ hA₂F).1
          (hdisj hB₁S hB₂S hBB)
  rw [← hFam_card]
  exact card_le_maxDisjointIndepGe hFam_valid

/-- **Unconditional colouring refinement of Lemma 1.1 (`lem:disjoint-packing`):**
if `2 ≤ u`, `k + 2 * d ≤ n`, `D_u(G) ≤ d`, and `χ(G) ≤ k` (with **no** hypothesis
on `α(G)`), then `G` admits an exact `(k + 2 * d)`-block proper-colouring
partition into nonempty classes of size at most `u - 1`. -/
theorem exists_unconditional_bounded_coloring_partition_of_maxDisjointIndepGe_le
    {n u k d : ℕ} (hu : 2 ≤ u) (hk2d : k + 2 * d ≤ n)
    (G : LabeledGraph n)
    (hDu : maxDisjointIndepGe G u ≤ d)
    (hchi : chromaticNumberNat G ≤ k) :
    ∃ Q : VertexPartition n,
      Q.parts.card = k + 2 * d ∧
        G ∈ partitionColoringEvent Q ∧
        ∀ D ∈ Q.parts, D.card ≤ u - 1 := by
  classical
  obtain ⟨P, hPcard, hPcol⟩ :=
    exists_coloring_partition_card_le_of_chromaticNumberNat_le G hchi
  obtain ⟨P', hP'le, hP'card, hP'small⟩ :=
    exists_finpartition_unconditional_split_large_parts hu P
  have hcost_le : ∑ B ∈ P.parts, splitCost u B.card ≤ 2 * d := by
    calc ∑ B ∈ P.parts, splitCost u B.card
        ≤ ∑ B ∈ P.parts, 2 * (B.card / u) := by
          refine Finset.sum_le_sum fun B hB ↦ ?_
          have hBpos : 1 ≤ B.card := Finset.card_pos.mpr (P.nonempty_of_mem_parts hB)
          exact (splitCost_eq_natCeil_sub_one_and_le_two_mul_div hu hBpos).2
      _ = 2 * ∑ B ∈ P.parts, (B.card / u) := (Finset.mul_sum ..).symm
      _ ≤ 2 * maxDisjointIndepGe G u :=
          Nat.mul_le_mul_left 2
            (sum_div_le_maxDisjointIndepGe (by omega) G P.parts P.disjoint hPcol)
      _ ≤ 2 * d := Nat.mul_le_mul_left 2 hDu
  have hP'col : G ∈ partitionColoringEvent P' := by
    intro D hD
    obtain ⟨B, hBP, hDB⟩ := hP'le hD
    exact Set.Pairwise.mono (by simpa using hDB) (hPcol B hBP)
  have hlo : P'.parts.card ≤ k + 2 * d := by omega
  have hhi : k + 2 * d ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hk2d
  obtain ⟨Q, hQcard, hQP'⟩ := exists_finpartition_refinement_card_eq P' hlo hhi
  refine ⟨Q, hQcard, ?_, ?_⟩
  · intro D hD
    obtain ⟨C, hCP', hDC⟩ := hQP' hD
    exact Set.Pairwise.mono (by simpa using hDC) (hP'col C hCP')
  · intro D hD
    obtain ⟨C, hCP', hDC⟩ := hQP' hD
    exact (Finset.card_le_card hDC).trans (hP'small C hCP')

/-- **Unconditional cocolouring refinement of Lemma 1.1 (`lem:disjoint-packing`):**
if `2 ≤ u`, `k + 4 * d ≤ n`, `D_u(G) ≤ d`, `D_u(Gᶜ) ≤ d`, and `ζ(G) ≤ k` (with
**no** hypothesis on `α(G)` or `ω(G)`), then `G` admits an exact `(k + 4 * d)`-block
cocolouring partition into nonempty classes of size at most `u - 1`. -/
theorem exists_unconditional_bounded_cocoloring_partition_of_maxDisjointIndepGe_le
    {n u k d : ℕ} (hu : 2 ≤ u) (hk4d : k + 4 * d ≤ n)
    (G : LabeledGraph n)
    (hDu : maxDisjointIndepGe G u ≤ d)
    (hDuCompl : maxDisjointIndepGe Gᶜ u ≤ d)
    (hzeta : cochromaticNumber G ≤ k) :
    ∃ Q : VertexPartition n,
      Q.parts.card = k + 4 * d ∧
        G ∈ partitionCocoloringEvent Q ∧
        ∀ D ∈ Q.parts, D.card ≤ u - 1 := by
  classical
  obtain ⟨P, hPcard, hPco⟩ :=
    exists_exact_cocoloring_partition_of_cochromaticNumber_le G hzeta (by omega)
  obtain ⟨P', hP'le, hP'card, hP'small⟩ :=
    exists_finpartition_unconditional_split_large_parts hu P
  let IndParts : Finset (Finset (Fin n)) :=
    P.parts.filter (fun B ↦ G.IsIndepSet (B : Set (Fin n)))
  let ClqParts : Finset (Finset (Fin n)) :=
    P.parts.filter (fun B ↦ ¬ G.IsIndepSet (B : Set (Fin n)))
  have hpart_sum :
      ∑ B ∈ P.parts, splitCost u B.card =
        (∑ B ∈ IndParts, splitCost u B.card) + ∑ B ∈ ClqParts, splitCost u B.card := by
    simpa [IndParts, ClqParts] using
      (Finset.sum_filter_add_sum_filter_not P.parts
        (fun B ↦ G.IsIndepSet (B : Set (Fin n))) (fun B ↦ splitCost u B.card)).symm
  have hind_cost : ∑ B ∈ IndParts, splitCost u B.card ≤ 2 * d := by
    calc ∑ B ∈ IndParts, splitCost u B.card
        ≤ ∑ B ∈ IndParts, 2 * (B.card / u) := by
          refine Finset.sum_le_sum fun B hB ↦ ?_
          have hBP : B ∈ P.parts := (Finset.mem_filter.mp hB).1
          have hBpos : 1 ≤ B.card := Finset.card_pos.mpr (P.nonempty_of_mem_parts hBP)
          exact (splitCost_eq_natCeil_sub_one_and_le_two_mul_div hu hBpos).2
      _ = 2 * ∑ B ∈ IndParts, (B.card / u) := (Finset.mul_sum ..).symm
      _ ≤ 2 * maxDisjointIndepGe G u :=
          Nat.mul_le_mul_left 2
            (sum_div_le_maxDisjointIndepGe (by omega) G IndParts
              (P.disjoint.subset fun B hB ↦ (Finset.mem_filter.mp hB).1)
              (fun B hB ↦ (Finset.mem_filter.mp hB).2))
      _ ≤ 2 * d := Nat.mul_le_mul_left 2 hDu
  have hclq_cost : ∑ B ∈ ClqParts, splitCost u B.card ≤ 2 * d := by
    calc ∑ B ∈ ClqParts, splitCost u B.card
        ≤ ∑ B ∈ ClqParts, 2 * (B.card / u) := by
          refine Finset.sum_le_sum fun B hB ↦ ?_
          have hBP : B ∈ P.parts := (Finset.mem_filter.mp hB).1
          have hBpos : 1 ≤ B.card := Finset.card_pos.mpr (P.nonempty_of_mem_parts hBP)
          exact (splitCost_eq_natCeil_sub_one_and_le_two_mul_div hu hBpos).2
      _ = 2 * ∑ B ∈ ClqParts, (B.card / u) := (Finset.mul_sum ..).symm
      _ ≤ 2 * maxDisjointIndepGe Gᶜ u :=
          Nat.mul_le_mul_left 2
            (sum_div_le_maxDisjointIndepGe (by omega) Gᶜ ClqParts
              (P.disjoint.subset fun B hB ↦ (Finset.mem_filter.mp hB).1)
              (fun B hB ↦ by
                obtain ⟨hBP, hnot⟩ := Finset.mem_filter.mp hB
                rcases hPco B hBP with hind | hcl
                · exact (hnot hind).elim
                · intro x hx y hy hxy hadj
                  exact hadj.2 (hcl hx hy hxy)))
      _ ≤ 2 * d := Nat.mul_le_mul_left 2 hDuCompl
  have hP'co : G ∈ partitionCocoloringEvent P' := by
    intro D hD
    obtain ⟨B, hBP, hDB⟩ := hP'le hD
    rcases hPco B hBP with hind | hcl
    · exact Or.inl (Set.Pairwise.mono (by simpa using hDB) hind)
    · exact Or.inr (Set.Pairwise.mono (by simpa using hDB) hcl)
  have hlo : P'.parts.card ≤ k + 4 * d := by omega
  have hhi : k + 4 * d ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hk4d
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

/-! ## 2. Unconditional finite Proposition 4.1(i) lower-tail reductions -/

private theorem boundedProfileColoringExpectation_ne_top (n b parts : ℕ) :
    boundedProfileColoringExpectation n b parts ≠ ⊤ := by
  change (∑ G : LabeledGraph n,
    (boundedProfileColoringCount G b parts : ENNReal) * randomGraphMeasure n {G}) ≠ ⊤
  exact ENNReal.sum_ne_top.mpr fun G _ ↦
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top _ _)

private theorem randomGraph_maxDisjointIndepGe_compl_gt_mu_add_le_exp {n u : ℕ}
    (hn : 2 ≤ n) (hu : 1 ≤ u) {t : ℝ} (ht : 0 ≤ t) :
    (randomGraphMeasure n).real
        {G : LabeledGraph n | mu n u + t < (maxDisjointIndepGe Gᶜ u : ℝ)} ≤
      Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) := by
  have hle_enn :
      randomGraphMeasure n {G : LabeledGraph n | mu n u + t < (maxDisjointIndepGe Gᶜ u : ℝ)} ≤
        randomGraphMeasure n {G : LabeledGraph n | mu n u + t < (maxDisjointIndepGe G u : ℝ)} :=
    randomGraphMeasure_image_le_of_involutive (fun G : LabeledGraph n ↦ Gᶜ)
      compl_involutive (fun G hG ↦ hG)
  have hle_real :
      (randomGraphMeasure n).real
          {G : LabeledGraph n | mu n u + t < (maxDisjointIndepGe Gᶜ u : ℝ)} ≤
        (randomGraphMeasure n).real
          {G : LabeledGraph n | mu n u + t < (maxDisjointIndepGe G u : ℝ)} :=
    ENNReal.toReal_mono (measure_ne_top _ _) hle_enn
  exact le_trans hle_real (randomGraph_maxDisjointIndepGe_gt_mu_add_le_exp hn hu ht)

/-- **Unconditional finite Proposition 4.1(i) chromatic reduction (no `X_{α+2} ≥ 2` event):**
for `2 ≤ n`, `2 ≤ u`, `0 ≤ t`, `mu n u + t ≤ d`, and `k + 2 * d ≤ n`,
`P(χ(G_n) ≤ k) ≤ exp(-2 t² / (n - 1)) + E[∑_{k' ∈ 𝓚_{n, k + 2d}} X̄_{k'}]`. -/
theorem randomGraph_chromaticNumberAtMost_le_of_unconditional_splitting
    {n u k d : ℕ} (hn : 2 ≤ n) (hu : 2 ≤ u) {t : ℝ} (ht : 0 ≤ t)
    (hd : mu n u + t ≤ (d : ℝ)) (hk2d : k + 2 * d ≤ n) :
    (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k} ≤
      Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) +
        (boundedProfileColoringExpectation n (u - 1) (k + 2 * d)).toReal := by
  classical
  let Exc : Set (LabeledGraph n) := {G | mu n u + t < (maxDisjointIndepGe G u : ℝ)}
  have hcov :
      {G : LabeledGraph n | chromaticNumberNat G ≤ k} ⊆
        Exc ∪ boundedProfileColoringCountPositiveEvent n (u - 1) (k + 2 * d) := by
    intro G hchi
    by_cases hDu_le : maxDisjointIndepGe G u ≤ d
    · right
      obtain ⟨Q, hQcard, hQcol, hQsmall⟩ :=
        exists_unconditional_bounded_coloring_partition_of_maxDisjointIndepGe_le
          hu hk2d G hDu_le hchi
      exact boundedProfileColoringCount_pos_of_partition G (u - 1) (k + 2 * d)
        Q hQcol hQcard hQsmall
    · left
      have hgt_nat : d < maxDisjointIndepGe G u := not_le.mp hDu_le
      have hgt_real : (d : ℝ) < (maxDisjointIndepGe G u : ℝ) := by exact_mod_cast hgt_nat
      exact lt_of_le_of_lt hd hgt_real
  have hpos_le :
      (randomGraphMeasure n).real
          (boundedProfileColoringCountPositiveEvent n (u - 1) (k + 2 * d)) ≤
        (boundedProfileColoringExpectation n (u - 1) (k + 2 * d)).toReal :=
    ENNReal.toReal_mono (boundedProfileColoringExpectation_ne_top n (u - 1) (k + 2 * d))
      (randomGraphMeasure_boundedProfileColoringCountPositive_le_expectation n (u - 1) (k + 2 * d))
  calc (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k}
      ≤ (randomGraphMeasure n).real
          (Exc ∪ boundedProfileColoringCountPositiveEvent n (u - 1) (k + 2 * d)) :=
        measureReal_mono hcov
    _ ≤ (randomGraphMeasure n).real Exc +
          (randomGraphMeasure n).real
            (boundedProfileColoringCountPositiveEvent n (u - 1) (k + 2 * d)) :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) +
          (boundedProfileColoringExpectation n (u - 1) (k + 2 * d)).toReal :=
        add_le_add (randomGraph_maxDisjointIndepGe_gt_mu_add_le_exp hn (by omega) ht) hpos_le

/-- **Unconditional finite Proposition 4.1(i) cochromatic reduction (no `X_{α+2} ≥ 2` event):**
for `2 ≤ n`, `2 ≤ u`, `0 ≤ t`, `mu n u + t ≤ d`, and `k + 4 * d ≤ n`,
`P(ζ(G_n) ≤ k) ≤ 2 exp(-2 t² / (n - 1)) + 2^(k + 4d) * E[∑_{k' ∈ 𝓚_{n, k + 4d}} X̄_{k'}]`. -/
theorem randomGraph_cochromaticNumberAtMost_le_of_unconditional_splitting
    {n u k d : ℕ} (hn : 2 ≤ n) (hu : 2 ≤ u) {t : ℝ} (ht : 0 ≤ t)
    (hd : mu n u + t ≤ (d : ℝ)) (hk4d : k + 4 * d ≤ n) :
    (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k} ≤
      2 * Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) +
        (2 : ℝ) ^ (k + 4 * d) *
          (boundedProfileColoringExpectation n (u - 1) (k + 4 * d)).toReal := by
  classical
  let Exc₁ : Set (LabeledGraph n) := {G | mu n u + t < (maxDisjointIndepGe G u : ℝ)}
  let Exc₂ : Set (LabeledGraph n) := {G | mu n u + t < (maxDisjointIndepGe Gᶜ u : ℝ)}
  let GoodCo : Set (LabeledGraph n) :=
    ⋃ kp ∈ boundedColoringProfiles n (u - 1) (k + 4 * d),
      ⋃ P : ProfilePartition n kp, partitionCocoloringEvent P.1
  have hcov :
      {G : LabeledGraph n | cochromaticNumber G ≤ k} ⊆ (Exc₁ ∪ Exc₂) ∪ GoodCo := by
    intro G hzeta
    by_cases hDu₁ : maxDisjointIndepGe G u ≤ d
    · by_cases hDu₂ : maxDisjointIndepGe Gᶜ u ≤ d
      · right
        obtain ⟨Q, hQcard, hQco, hQsmall⟩ :=
          exists_unconditional_bounded_cocoloring_partition_of_maxDisjointIndepGe_le
            hu hk4d G hDu₁ hDu₂ hzeta
        let kp : ColoringProfile (u - 1) := vertexPartitionProfile (u - 1) Q
        let Qp : ProfilePartition n kp := vertexPartitionAsProfilePartition Q hQsmall
        have hkp : kp ∈ boundedColoringProfiles n (u - 1) (k + 4 * d) :=
          mem_boundedColoringProfiles_of_constraints Qp.vertexMass_eq
            (Qp.card_parts_eq.symm.trans hQcard)
        exact Set.mem_biUnion hkp (Set.mem_iUnion.mpr ⟨Qp, hQco⟩)
      · left; right
        have hgt : (d : ℝ) < (maxDisjointIndepGe Gᶜ u : ℝ) := by exact_mod_cast not_le.mp hDu₂
        exact lt_of_le_of_lt hd hgt
    · left; left
      have hgt : (d : ℝ) < (maxDisjointIndepGe G u : ℝ) := by exact_mod_cast not_le.mp hDu₁
      exact lt_of_le_of_lt hd hgt
  have hGoodCo_enn :
      randomGraphMeasure n GoodCo ≤
        (2 : ENNReal) ^ (k + 4 * d) *
          boundedProfileColoringExpectation n (u - 1) (k + 4 * d) := by
    calc randomGraphMeasure n GoodCo
        ≤ ∑ kp ∈ boundedColoringProfiles n (u - 1) (k + 4 * d),
            randomGraphMeasure n
              (⋃ P : ProfilePartition n kp, partitionCocoloringEvent P.1) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ kp ∈ boundedColoringProfiles n (u - 1) (k + 4 * d),
            ∑ P : ProfilePartition n kp,
              randomGraphMeasure n (partitionCocoloringEvent P.1) :=
          Finset.sum_le_sum fun kp _ ↦ measure_iUnion_fintype_le _ _
      _ ≤ ∑ kp ∈ boundedColoringProfiles n (u - 1) (k + 4 * d),
            ∑ P : ProfilePartition n kp,
              (2 : ENNReal) ^ (k + 4 * d) *
                randomGraphMeasure n (partitionColoringEvent P.1) := by
          refine Finset.sum_le_sum fun kp hkp ↦ Finset.sum_le_sum fun P _ ↦ ?_
          have hkparts : P.1.parts.card = k + 4 * d :=
            P.card_parts_eq.trans ((mem_boundedColoringProfiles kp).mp hkp).2
          simpa [hkparts] using
            randomGraphMeasure_partitionCocoloringEvent_le_two_pow_mul P.1
      _ = (2 : ENNReal) ^ (k + 4 * d) *
            boundedProfileColoringExpectation n (u - 1) (k + 4 * d) := by
          rw [boundedProfileColoringExpectation_eq_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun kp _ ↦ ?_
          rw [← Finset.mul_sum, profileColoringExpectation_eq_card_mul]
          simp_rw [randomGraphMeasure_partitionColoringEvent]
          simp [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hrhs_ne_top :
      (2 : ENNReal) ^ (k + 4 * d) *
        boundedProfileColoringExpectation n (u - 1) (k + 4 * d) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
      (boundedProfileColoringExpectation_ne_top n (u - 1) (k + 4 * d))
  have hGoodCo_real :
      (randomGraphMeasure n).real GoodCo ≤
        (2 : ℝ) ^ (k + 4 * d) *
          (boundedProfileColoringExpectation n (u - 1) (k + 4 * d)).toReal := by
    have h := ENNReal.toReal_mono hrhs_ne_top hGoodCo_enn
    simpa [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow] using h
  calc (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k}
      ≤ (randomGraphMeasure n).real ((Exc₁ ∪ Exc₂) ∪ GoodCo) := measureReal_mono hcov
    _ ≤ (randomGraphMeasure n).real (Exc₁ ∪ Exc₂) + (randomGraphMeasure n).real GoodCo :=
        measureReal_union_le _ _
    _ ≤ ((randomGraphMeasure n).real Exc₁ + (randomGraphMeasure n).real Exc₂) +
          (randomGraphMeasure n).real GoodCo :=
        add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ (Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) +
          Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ))) +
          (2 : ℝ) ^ (k + 4 * d) *
            (boundedProfileColoringExpectation n (u - 1) (k + 4 * d)).toReal :=
        add_le_add
          (add_le_add
            (randomGraph_maxDisjointIndepGe_gt_mu_add_le_exp hn (by omega) ht)
            (randomGraph_maxDisjointIndepGe_compl_gt_mu_add_le_exp hn (by omega) ht))
          hGoodCo_real
    _ = 2 * Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) +
          (2 : ℝ) ^ (k + 4 * d) *
            (boundedProfileColoringExpectation n (u - 1) (k + 4 * d)).toReal := by
        ring

/-! ## 3. Proposition 5.3 two-coordinate (`Δk₃, Δk₄`) integer profile rounding -/

/-- Proposition 5.3 deterministic integer rounding of a continuous probability
vector `p` on `S_{m,M} = {m + 1, ..., m + M}` (`{3, 4} ⊆ S_{m,M}`): floors every
coordinate `⌊k * p_i⌋` and applies `Δk₃ = e₁ - 4 e₀`, `Δk₄ = 3 e₀ - e₁`. -/
def roundedWindowProfile (m M α k n : ℕ) (p : ℕ → ℝ) (i : ℕ) : ℤ :=
  let W := Finset.Icc (m + 1) (m + M)
  let kTilde : ℕ → ℤ := fun j ↦ ⌊(k : ℝ) * p j⌋
  let e0 : ℤ := (∑ j ∈ W, kTilde j) - (k : ℤ)
  let e1 : ℤ := (∑ j ∈ W, (j : ℤ) * kTilde j) - ((α : ℤ) * (k : ℤ) - (n : ℤ))
  if i ∈ W then
    kTilde i + (if i = 3 then e1 - 4 * e0 else if i = 4 then 3 * e0 - e1 else 0)
  else 0

/-- **Exact conservation and `O_M(1)` error for Proposition 5.3's integer profile rounding:**
when `m ≤ 1`, `4 ≤ M`, `1 ≤ k`, `∑_{i ∈ S_{m,M}} p_i = 1`, and
`∑_{i ∈ S_{m,M}} i p_i = α - n / k`, `roundedWindowProfile` satisfies exact class-count
conservation `∑_i k_i = k`, exact vertex-mass conservation `∑_i (α - i) k_i = n`, and
uniform `ℓ_∞` rounding error `|k_i - k p_i| ≤ (m + M + 4) * M + 1` on `S_{m,M}`. -/
theorem roundedWindowProfile_conservation_and_error
    {m M α k n : ℕ} (hm : m ≤ 1) (hM : 4 ≤ M) (hk : 1 ≤ k)
    {p : ℕ → ℝ}
    (hp_sum : ∑ i ∈ Finset.Icc (m + 1) (m + M), p i = 1)
    (hp_mean : ∑ i ∈ Finset.Icc (m + 1) (m + M), (i : ℝ) * p i =
      (α : ℝ) - (n : ℝ) / (k : ℝ)) :
    let W := Finset.Icc (m + 1) (m + M)
    (∑ i ∈ W, roundedWindowProfile m M α k n p i = (k : ℤ)) ∧
      (∑ i ∈ W, ((α : ℤ) - (i : ℤ)) * roundedWindowProfile m M α k n p i = (n : ℤ)) ∧
      ∀ i ∈ W,
        |((roundedWindowProfile m M α k n p i : ℤ) : ℝ) - (k : ℝ) * p i| ≤
          (((m + M + 4) * M + 1 : ℕ) : ℝ) := by
  intro W
  have h3W : 3 ∈ W := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h4W : 4 ∈ W := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  let kTilde : ℕ → ℤ := fun j ↦ ⌊(k : ℝ) * p j⌋
  let e0 : ℤ := (∑ j ∈ W, kTilde j) - (k : ℤ)
  let e1 : ℤ := (∑ j ∈ W, (j : ℤ) * kTilde j) - ((α : ℤ) * (k : ℤ) - (n : ℤ))
  let delta : ℕ → ℤ := fun i ↦
    if i = 3 then e1 - 4 * e0 else if i = 4 then 3 * e0 - e1 else 0
  have hprof_eq : ∀ i ∈ W, roundedWindowProfile m M α k n p i = kTilde i + delta i := by
    intro i hi
    simp [roundedWindowProfile, W, kTilde, e0, e1, delta, hi]
  -- Evaluate `∑_{i ∈ W} delta i = -e0` and `∑_{i ∈ W} i * delta i = -e1`
  have hdelta_sum : ∑ i ∈ W, delta i = -e0 := by
    have hrest : ∑ i ∈ (W.erase 3).erase 4, delta i = 0 := by
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      have hi4 : i ≠ 4 := (Finset.mem_erase.mp hi).1
      have hi3 : i ≠ 3 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      simp [delta, hi3, hi4]
    have h4mem : 4 ∈ W.erase 3 := Finset.mem_erase.mpr ⟨by omega, h4W⟩
    rw [← Finset.insert_erase h3W, Finset.sum_insert (Finset.notMem_erase 3 W),
      ← Finset.insert_erase h4mem, Finset.sum_insert (Finset.notMem_erase 4 _), hrest]
    dsimp [delta]
    omega
  have hdelta_mom : ∑ i ∈ W, (i : ℤ) * delta i = -e1 := by
    have hrest : ∑ i ∈ (W.erase 3).erase 4, (i : ℤ) * delta i = 0 := by
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      have hi4 : i ≠ 4 := (Finset.mem_erase.mp hi).1
      have hi3 : i ≠ 3 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      simp [delta, hi3, hi4]
    have h4mem : 4 ∈ W.erase 3 := Finset.mem_erase.mpr ⟨by omega, h4W⟩
    rw [← Finset.insert_erase h3W, Finset.sum_insert (Finset.notMem_erase 3 W),
      ← Finset.insert_erase h4mem, Finset.sum_insert (Finset.notMem_erase 4 _), hrest]
    dsimp [delta]
    omega
  -- Conservation of class sum `∑ k_i = k`
  have hsum_k : ∑ i ∈ W, roundedWindowProfile m M α k n p i = (k : ℤ) := by
    rw [Finset.sum_congr rfl hprof_eq, Finset.sum_add_distrib, hdelta_sum]
    dsimp [e0]
    omega
  -- Conservation of vertex mass `∑ (α - i) k_i = n`
  have hsum_n : ∑ i ∈ W, ((α : ℤ) - (i : ℤ)) * roundedWindowProfile m M α k n p i = (n : ℤ) := by
    have hexpand :
        ∑ i ∈ W, ((α : ℤ) - (i : ℤ)) * roundedWindowProfile m M α k n p i =
          (α : ℤ) * (∑ i ∈ W, roundedWindowProfile m M α k n p i) -
            ∑ i ∈ W, (i : ℤ) * roundedWindowProfile m M α k n p i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    have hmom_k : ∑ i ∈ W, (i : ℤ) * roundedWindowProfile m M α k n p i =
        (α : ℤ) * (k : ℤ) - (n : ℤ) := by
      have hcongr : ∑ i ∈ W, (i : ℤ) * roundedWindowProfile m M α k n p i =
          (∑ i ∈ W, (i : ℤ) * kTilde i) + ∑ i ∈ W, (i : ℤ) * delta i := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [hprof_eq i hi, mul_add]
      rw [hcongr, hdelta_mom]
      dsimp [e1]
      omega
    rw [hexpand, hsum_k, hmom_k]
    omega
  refine ⟨hsum_k, hsum_n, ?_⟩
  -- Uniform `ℓ_∞` error bound across `W`
  intro i hi
  have hkR_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hW_card : W.card = M := by
    dsimp [W]
    rw [Nat.card_Icc]
    omega
  have hkp_sum : ∑ j ∈ W, (k : ℝ) * p j = (k : ℝ) := by
    rw [← Finset.mul_sum, hp_sum, mul_one]
  have hkp_mom : ∑ j ∈ W, (j : ℝ) * ((k : ℝ) * p j) = (α : ℝ) * (k : ℝ) - (n : ℝ) := by
    have hmul := congrArg (fun x : ℝ ↦ (k : ℝ) * x) hp_mean
    have hlhs : (k : ℝ) * ∑ j ∈ W, (j : ℝ) * p j = ∑ j ∈ W, (j : ℝ) * ((k : ℝ) * p j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    have hrhs : (k : ℝ) * ((α : ℝ) - (n : ℝ) / (k : ℝ)) =
        (α : ℝ) * (k : ℝ) - (n : ℝ) := by
      field_simp [hkR_pos.ne']
    exact hlhs.symm.trans (hmul.trans hrhs)
  have he0_abs : |(e0 : ℝ)| ≤ (M : ℝ) := by
    have he0_R : (e0 : ℝ) = ∑ j ∈ W, ((kTilde j : ℝ) - (k : ℝ) * p j) := by
      dsimp [e0]
      push_cast
      rw [Finset.sum_sub_distrib, hkp_sum]
    rw [he0_R]
    calc |∑ j ∈ W, ((kTilde j : ℝ) - (k : ℝ) * p j)|
        ≤ ∑ j ∈ W, |(kTilde j : ℝ) - (k : ℝ) * p j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ W, (1 : ℝ) := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          rw [abs_le]
          have hfl_le : (kTilde j : ℝ) ≤ (k : ℝ) * p j := Int.floor_le _
          have hlt_fl : (k : ℝ) * p j < (kTilde j : ℝ) + 1 := Int.lt_floor_add_one _
          exact ⟨by linarith, by linarith⟩
      _ = (M : ℝ) := by simp [hW_card]
  have he1_abs : |(e1 : ℝ)| ≤ ((m + M) * M : ℝ) := by
    have he1_R : (e1 : ℝ) = ∑ j ∈ W, (j : ℝ) * ((kTilde j : ℝ) - (k : ℝ) * p j) := by
      dsimp [e1]
      push_cast
      rw [← hkp_mom, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    rw [he1_R]
    calc |∑ j ∈ W, (j : ℝ) * ((kTilde j : ℝ) - (k : ℝ) * p j)|
        ≤ ∑ j ∈ W, |(j : ℝ) * ((kTilde j : ℝ) - (k : ℝ) * p j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ W, ((m + M : ℕ) : ℝ) := by
          refine Finset.sum_le_sum fun j hj ↦ ?_
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
          have hj_le : (j : ℝ) ≤ ((m + M : ℕ) : ℝ) := by
            exact_mod_cast (Finset.mem_Icc.mp hj).2
          have herr_le : |(kTilde j : ℝ) - (k : ℝ) * p j| ≤ 1 := by
            rw [abs_le]
            exact ⟨by linarith [Int.lt_floor_add_one ((k : ℝ) * p j)],
              by linarith [Int.floor_le ((k : ℝ) * p j)]⟩
          calc (j : ℝ) * |(kTilde j : ℝ) - (k : ℝ) * p j|
              ≤ ((m + M : ℕ) : ℝ) * 1 :=
                mul_le_mul hj_le herr_le (abs_nonneg _) (Nat.cast_nonneg _)
            _ = ((m + M : ℕ) : ℝ) := mul_one _
      _ = ((m + M) * M : ℝ) := by
          simp [hW_card]
          ring
  have hdelta_abs : |(delta i : ℝ)| ≤ ((m + M + 4) * M : ℝ) := by
    dsimp [delta]
    split_ifs with h3 h4
    · push_cast
      have htri := abs_sub (e1 : ℝ) (4 * (e0 : ℝ))
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at htri
      linarith
    · push_cast
      have htri := abs_sub (3 * (e0 : ℝ)) (e1 : ℝ)
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at htri
      have hmM_nn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      linarith
    · simp only [Int.cast_zero, abs_zero]
      positivity
  rw [hprof_eq i hi]
  push_cast
  have hbase : |(kTilde i : ℝ) - (k : ℝ) * p i| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [Int.lt_floor_add_one ((k : ℝ) * p i)],
      by linarith [Int.floor_le ((k : ℝ) * p i)]⟩
  have htri : |(kTilde i : ℝ) + (delta i : ℝ) - (k : ℝ) * p i| ≤
      |(kTilde i : ℝ) - (k : ℝ) * p i| + |(delta i : ℝ)| := by
    rw [show (kTilde i : ℝ) + (delta i : ℝ) - (k : ℝ) * p i =
      ((kTilde i : ℝ) - (k : ℝ) * p i) + (delta i : ℝ) by ring]
    exact abs_add_le _ _
  linarith

/-! ## 4. Universal `2 n / (log n)^5` allowance, `exp(-2 n / (log n)^10)` tails, and MGF convergence -/

/-- Universal Section 4 / Section 8 shift `t_n := n / (log n)^5`. -/
def universalShift (n : ℕ) : ℝ :=
  (n : ℝ) / (Real.log (n : ℝ)) ^ 5

/-- Universal Corollary 8.1 concentration allowance `a_n := 2 n / (log n)^5`. -/
def universalAllowance (n : ℕ) : ℝ :=
  2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 5

/-- Universal quasi-exponential tail `exp(-2 n / (log n)^10)`. -/
def quasiExpTail (n : ℕ) : ℝ :=
  Real.exp (-2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10)

private theorem quasiExpTail_pos (n : ℕ) : 0 < quasiExpTail n :=
  Real.exp_pos _

/-- **Universal allowance asymptotic (`Corollary 8.1`):**
`2 n / (log n)^5 = o(n log log n / (log n)^4)`. -/
theorem universalAllowance_isLittleO :
    universalAllowance =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4) := by
  rw [Asymptotics.isLittleO_iff]
  intro eps heps
  have hll1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (Real.log (n : ℝ)) :=
    tendsto_logLogOrder_atTop.eventually (eventually_ge_atTop 1)
  have hLbig : ∀ᶠ n : ℕ in atTop, 2 / eps < Real.log (n : ℝ) :=
    tendsto_logOrder_atTop.eventually (eventually_gt_atTop (2 / eps))
  filter_upwards [eventually_gt_atTop 2, hll1, hLbig] with n hn2 hlln hLn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have h2_le : 2 ≤ eps * Real.log (n : ℝ) := by
    have := (div_lt_iff₀ heps).mp hLn
    linarith
  unfold universalAllowance
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity),
    abs_of_pos (div_pos (mul_pos hn_pos (by linarith)) (pow_pos hL_pos 4)),
    div_le_iff₀ (pow_pos hL_pos 5)]
  calc 2 * (n : ℝ)
      ≤ (eps * Real.log (n : ℝ)) * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
        calc 2 * (n : ℝ)
            ≤ (eps * Real.log (n : ℝ)) * (n : ℝ) :=
              mul_le_mul_of_nonneg_right h2_le hn_pos.le
          _ = (eps * Real.log (n : ℝ)) * (n : ℝ) * 1 := (mul_one _).symm
          _ ≤ (eps * Real.log (n : ℝ)) * (n : ℝ) * Real.log (Real.log (n : ℝ)) :=
              mul_le_mul_of_nonneg_left hlln (by positivity)
    _ = eps * ((n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4) *
          (Real.log (n : ℝ)) ^ 5 := by
        field_simp [hL_pos.ne']

private theorem exp_neg_le_twentySeven_div_cube {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 27 / x ^ 3 := by
  have hx3 : x / 3 ≤ Real.exp (x / 3) := by
    linarith [Real.add_one_le_exp (x / 3)]
  have hpow : (x / 3) ^ 3 ≤ Real.exp x := by
    calc (x / 3) ^ 3
        ≤ (Real.exp (x / 3)) ^ 3 := pow_le_pow_left₀ (by positivity) hx3 3
      _ = Real.exp ((3 : ℝ) * (x / 3)) := (Real.exp_nat_mul (x / 3) 3).symm
      _ = Real.exp x := by congr 1; ring
  have hmul : Real.exp (-x) * (x ^ 3 / 27) ≤ 1 := by
    have h1 : x ^ 3 / 27 = (x / 3) ^ 3 := by ring
    rw [h1]
    calc Real.exp (-x) * (x / 3) ^ 3
        ≤ Real.exp (-x) * Real.exp x :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = Real.exp (-x + x) := (Real.exp_add (-x) x).symm
      _ = 1 := by simp
  rw [le_div_iff₀ (pow_pos hx 3)]
  linarith

/-- **Dominance of `exp(-2 n / (log n)^10)` over the v6 polylog tail:**
`exp(-2 n / (log n)^10) = O(n^(-3/2) (log n)^(β + 5/2))`. -/
theorem quasiExpTail_isBigO_polylogTail :
    quasiExpTail =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ)) *
        (Real.log (n : ℝ)) ^ (phaseTailBeta + 5 / 2)) := by
  apply IsBigO.of_bound 4
  have ho : (fun x : ℝ ↦ (Real.log x) ^ (30 : ℝ)) =o[atTop]
      (fun x : ℝ ↦ x ^ (3 / 2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop (30 : ℝ) (by norm_num : (0 : ℝ) < 3 / 2)
  have hb := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Asymptotics.isLittleO_iff.mp ho one_pos)
  have hL1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 3, hb, hL1] with n hn3 hbn hLn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hL_pos : 0 < Real.log (n : ℝ) := by linarith
  have ht_pos : 0 < 2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10 := by positivity
  have hcube := exp_neg_le_twentySeven_div_cube ht_pos
  have hexp_rw : quasiExpTail n = Real.exp (-(2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10)) := by
    unfold quasiExpTail
    congr 1; ring
  have hlog30_le : (Real.log (n : ℝ)) ^ 30 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
    change ‖(Real.log (n : ℝ)) ^ (30 : ℝ)‖ ≤ 1 * ‖(n : ℝ) ^ (3 / 2 : ℝ)‖ at hbn
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hL_pos _),
      abs_of_pos (Real.rpow_pos_of_pos hn_pos _), one_mul] at hbn
    simpa [Real.rpow_natCast] using hbn
  have hbeta_pos : 0 ≤ phaseTailBeta + 5 / 2 := by
    unfold phaseTailBeta Erdos625.q
    have := Real.log_pos one_lt_two
    positivity
  have h1_le_Lpow : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ (phaseTailBeta + 5 / 2) :=
    Real.one_le_rpow hLn hbeta_pos
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (quasiExpTail_pos n),
    abs_of_pos (mul_pos (Real.rpow_pos_of_pos hn_pos _) (Real.rpow_pos_of_pos hL_pos _)),
    hexp_rw]
  calc Real.exp (-(2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10))
      ≤ 27 / (2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10) ^ 3 := hcube
    _ = (27 / 8 : ℝ) * ((Real.log (n : ℝ)) ^ 30 / (n : ℝ) ^ 3) := by
        field_simp [hn_pos.ne', hL_pos.ne']
        ring
    _ ≤ 4 * ((n : ℝ) ^ (3 / 2 : ℝ) / (n : ℝ) ^ 3) := by
        have hdiv : (Real.log (n : ℝ)) ^ 30 / (n : ℝ) ^ 3 ≤
            (n : ℝ) ^ (3 / 2 : ℝ) / (n : ℝ) ^ 3 :=
          div_le_div_of_nonneg_right hlog30_le (pow_nonneg hn_pos.le 3)
        have hnn : 0 ≤ (Real.log (n : ℝ)) ^ 30 / (n : ℝ) ^ 3 := by positivity
        linarith
    _ = 4 * ((n : ℝ) ^ (-(3 / 2 : ℝ)) * 1) := by
        congr 1
        rw [mul_one, ← Real.rpow_natCast (n : ℝ) 3, ← Real.rpow_sub hn_pos]
        congr 1; norm_num
    _ ≤ 4 * ((n : ℝ) ^ (-(3 / 2 : ℝ)) *
          (Real.log (n : ℝ)) ^ (phaseTailBeta + 5 / 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h1_le_Lpow (Real.rpow_nonneg hn_pos.le _))
          (by norm_num)

/-- **Unconditional summability of `exp(-2 n / (log n)^10)` (`Main Theorem`):**
`∑_{n : ℕ} exp(-2 n / (log n)^10) < ∞`. -/
theorem summable_quasiExpTail : Summable quasiExpTail := by
  obtain ⟨C, hC_ev⟩ := quasiExpTail_isBigO_polylogTail.bound
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hC_ev.and (eventually_ge_atTop 2))
  have hdom : Summable (fun k : ℕ ↦
      |C| * ((k + N₀ : ℕ) ^ (-(3 / 2 : ℝ)) *
        (Real.log (k + N₀ : ℕ)) ^ (phaseTailBeta + 5 / 2))) :=
    ((summable_polylog_three_halves (phaseTailBeta + 5 / 2)).comp_injective
      (add_left_injective N₀)).mul_left |C|
  have hshift : Summable (fun k : ℕ ↦ quasiExpTail (k + N₀)) := by
    refine Summable.of_nonneg_of_le (fun k ↦ (quasiExpTail_pos _).le) (fun k ↦ ?_) hdom
    obtain ⟨hCk, hk2⟩ := hN₀ (k + N₀) (Nat.le_add_left N₀ k)
    have hn_pos : (0 : ℝ) < ((k + N₀ : ℕ) : ℝ) := by positivity
    have hL_pos : 0 < Real.log ((k + N₀ : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < k + N₀ by omega))
    have hrhs_nn : 0 ≤ ((k + N₀ : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) *
        (Real.log ((k + N₀ : ℕ) : ℝ)) ^ (phaseTailBeta + 5 / 2) :=
      mul_nonneg (Real.rpow_nonneg hn_pos.le _) (Real.rpow_nonneg hL_pos.le _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (quasiExpTail_pos _),
      abs_of_nonneg hrhs_nn] at hCk
    exact le_trans hCk (mul_le_mul_of_nonneg_right (le_abs_self C) hrhs_nn)
  exact (summable_nat_add_iff N₀).mp hshift

private theorem exp_universalShift_le_quasiExpTail {n : ℕ} (hn : 2 ≤ n) :
    Real.exp (-2 * (universalShift n) ^ 2 / ((n - 1 : ℕ) : ℝ)) ≤ quasiExpTail n := by
  unfold universalShift quasiExpTail
  apply Real.exp_le_exp.mpr
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  have hn1_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  by_cases hL0 : Real.log (n : ℝ) = 0
  · simp [hL0]
  · have hL10_pos : 0 < (Real.log (n : ℝ)) ^ 10 := pow_pos (Real.log_pos (by exact_mod_cast hn)) 10
    rw [div_pow, ← pow_mul, show 5 * 2 = 10 by rfl]
    rw [div_le_div_iff₀ hn1_pos hL10_pos]
    have h1 : -2 * ((n : ℝ) ^ 2 / (Real.log (n : ℝ)) ^ 10) * (Real.log (n : ℝ)) ^ 10 =
        -2 * (n : ℝ) ^ 2 := by
      field_simp [hL10_pos.ne']
    rw [h1]
    nlinarith

/-- **Proposition 4.1 packing-pair exceptional tail (`𝓔_n = 2 exp(-2 n / (log n)^10)`):**
for `2 ≤ n` and `1 ≤ u`, the probability that `D_u(G_n)` or `D_u(G_nᶜ)` exceeds
`μ_u + n / (log n)^5` is at most `2 * exp(-2 n / (log n)^10)`. -/
theorem randomGraph_packingPair_gt_universalShift_le {n u : ℕ}
    (hn : 2 ≤ n) (hu : 1 ≤ u) :
    (randomGraphMeasure n).real
        ({G : LabeledGraph n | mu n u + universalShift n < (maxDisjointIndepGe G u : ℝ)} ∪
          {G : LabeledGraph n | mu n u + universalShift n < (maxDisjointIndepGe Gᶜ u : ℝ)}) ≤
      2 * quasiExpTail n := by
  have ht_nn : 0 ≤ universalShift n := by
    unfold universalShift
    have hL_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    positivity
  calc (randomGraphMeasure n).real
          ({G | mu n u + universalShift n < (maxDisjointIndepGe G u : ℝ)} ∪
            {G | mu n u + universalShift n < (maxDisjointIndepGe Gᶜ u : ℝ)})
      ≤ (randomGraphMeasure n).real
            {G | mu n u + universalShift n < (maxDisjointIndepGe G u : ℝ)} +
          (randomGraphMeasure n).real
            {G | mu n u + universalShift n < (maxDisjointIndepGe Gᶜ u : ℝ)} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-2 * (universalShift n) ^ 2 / ((n - 1 : ℕ) : ℝ)) +
          Real.exp (-2 * (universalShift n) ^ 2 / ((n - 1 : ℕ) : ℝ)) :=
        add_le_add
          (randomGraph_maxDisjointIndepGe_gt_mu_add_le_exp hn hu ht_nn)
          (randomGraph_maxDisjointIndepGe_compl_gt_mu_add_le_exp hn hu ht_nn)
    _ ≤ quasiExpTail n + quasiExpTail n :=
        add_le_add (exp_universalShift_le_quasiExpTail hn) (exp_universalShift_le_quasiExpTail hn)
    _ = 2 * quasiExpTail n := by ring

/-- **v7 Corollary 8.1 (`cor:zeta-upper`, universal `2 n / (log n)^5` allowance & quasi-exponential tail):**
along any regime index set `Nset : Set ℕ`, if `δ_- > 0`, `c₀ = min(δ_- / 2, 1 / 60)`,
and the Paley–Zygmund + Proposition 7.3 rare-seed lower bounds
`≥ exp(-C_sm n^(1 - c₀) / log n)` hold, then uniformly for all sufficiently large
`n ∈ Nset`, with universal `a_n = 2 n / (log n)^5`:
`P(ζ(G_n) > k_co(n) + a_n) ≤ exp(-2 n / (log n)^10)` and
`P(χ(G_n) > k_ch(n) + a_n) ≤ exp(-2 n / (log n)^10)`. -/
theorem regime_cochromatic_and_chromatic_upperTail_quasiExp_of_secondMoment_seed
    (Nset : Set ℕ) {deltaMinus : ℝ} (hd : 0 < deltaMinus)
    (C_sm : ℝ) (kCo kCh : ℕ → ℕ)
    (hSeedCo : ∀ᶠ (n : ℕ) in atTop ⊓ 𝓟 Nset,
      Real.exp (-C_sm * (n : ℝ) ^ (1 - secondMomentExponent deltaMinus) / Real.log (n : ℝ)) ≤
        (randomGraphMeasure n).real {G | cochromaticNumber G ≤ kCo n})
    (hSeedCh : ∀ᶠ (n : ℕ) in atTop ⊓ 𝓟 Nset,
      Real.exp (-C_sm * (n : ℝ) ^ (1 - secondMomentExponent deltaMinus) / Real.log (n : ℝ)) ≤
        (randomGraphMeasure n).real {G | chromaticNumberNat G ≤ kCh n}) :
    ∀ᶠ (n : ℕ) in atTop ⊓ 𝓟 Nset,
      (randomGraphMeasure n).real
          {G | (kCo n : ℝ) + universalAllowance n < (cochromaticNumber G : ℝ)} ≤
        quasiExpTail n ∧
      (randomGraphMeasure n).real
          {G | (kCh n : ℝ) + universalAllowance n < (chromaticNumberNat G : ℝ)} ≤
        quasiExpTail n := by
  set c₀ := secondMomentExponent deltaMinus
  have hc₀_pos : 0 < c₀ := lt_min (half_pos hd) (by norm_num)
  have hbeat : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧
        C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ) <
          2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10 := by
    have ho : (fun x : ℝ ↦ (Real.log x) ^ (9 : ℝ)) =o[atTop]
        (fun x : ℝ ↦ x ^ c₀) :=
      isLittleO_log_rpow_rpow_atTop (9 : ℝ) hc₀_pos
    let c_eps : ℝ := 1 / (|C_sm| + 1)
    have hc_eps : 0 < c_eps := by dsimp [c_eps]; positivity
    have hb := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Asymptotics.isLittleO_iff.mp ho hc_eps)
    have hL1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
      tendsto_logOrder_atTop.eventually (eventually_ge_atTop 1)
    filter_upwards [eventually_ge_atTop 3, hb, hL1] with n hn3 hbn hLn
    refine ⟨by omega, ?_⟩
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hL_pos : 0 < Real.log (n : ℝ) := by linarith
    have hlog9 : (Real.log (n : ℝ)) ^ 9 ≤ c_eps * (n : ℝ) ^ c₀ := by
      change ‖(Real.log (n : ℝ)) ^ (9 : ℝ)‖ ≤ c_eps * ‖(n : ℝ) ^ c₀‖ at hbn
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hL_pos _),
        abs_of_pos (Real.rpow_pos_of_pos hn_pos _)] at hbn
      simpa [Real.rpow_natCast] using hbn
    have hmul_c : (|C_sm| + 1) * (Real.log (n : ℝ)) ^ 9 ≤ (n : ℝ) ^ c₀ := by
      have h := mul_le_mul_of_nonneg_left hlog9 (show (0 : ℝ) ≤ |C_sm| + 1 by positivity)
      have hc_cancel : (|C_sm| + 1) * (c_eps * (n : ℝ) ^ c₀) = (n : ℝ) ^ c₀ := by
        dsimp [c_eps]
        field_simp [(show (0 : ℝ) < |C_sm| + 1 by positivity).ne']
      linarith
    have hstrict_log9 : C_sm * (Real.log (n : ℝ)) ^ 9 < 2 * (n : ℝ) ^ c₀ := by
      have hC_lt : C_sm < |C_sm| + 1 := lt_of_le_of_lt (le_abs_self C_sm) (by linarith)
      have hpow_pos : 0 < (Real.log (n : ℝ)) ^ 9 := pow_pos hL_pos 9
      have hrp_pos : 0 < (n : ℝ) ^ c₀ := Real.rpow_pos_of_pos hn_pos c₀
      calc C_sm * (Real.log (n : ℝ)) ^ 9
          < (|C_sm| + 1) * (Real.log (n : ℝ)) ^ 9 :=
            mul_lt_mul_of_pos_right hC_lt hpow_pos
        _ ≤ (n : ℝ) ^ c₀ := hmul_c
        _ < 2 * (n : ℝ) ^ c₀ := by linarith
    rw [div_lt_div_iff₀ hL_pos (pow_pos hL_pos 10)]
    have hlhs : C_sm * (n : ℝ) ^ (1 - c₀) * (Real.log (n : ℝ)) ^ 10 =
        (C_sm * (Real.log (n : ℝ)) ^ 9) * ((n : ℝ) ^ (1 - c₀) * Real.log (n : ℝ)) := by ring
    have hrhs : 2 * (n : ℝ) * Real.log (n : ℝ) =
        (2 * (n : ℝ) ^ c₀) * ((n : ℝ) ^ (1 - c₀) * Real.log (n : ℝ)) := by
      have hn_split : (n : ℝ) ^ c₀ * (n : ℝ) ^ (1 - c₀) = (n : ℝ) := by
        rw [← Real.rpow_add hn_pos]
        norm_num [Real.rpow_one]
      calc 2 * (n : ℝ) * Real.log (n : ℝ)
          = 2 * ((n : ℝ) ^ c₀ * (n : ℝ) ^ (1 - c₀)) * Real.log (n : ℝ) := by rw [hn_split]
        _ = (2 * (n : ℝ) ^ c₀) * ((n : ℝ) ^ (1 - c₀) * Real.log (n : ℝ)) := by ring
    rw [hlhs, hrhs]
    exact mul_lt_mul_of_pos_right hstrict_log9
      (mul_pos (Real.rpow_pos_of_pos hn_pos _) hL_pos)
  filter_upwards [hbeat.filter_mono inf_le_left, hSeedCo, hSeedCh] with n ⟨hn2, hbn⟩ hSCo hSCh
  have ht_nn : 0 ≤ universalShift n := by
    unfold universalShift
    have hL_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    positivity
  have h2t : universalAllowance n = 2 * universalShift n := by
    unfold universalAllowance universalShift; ring
  have hexp_le : Real.exp (-2 * (universalShift n) ^ 2 / ((n - 1 : ℕ) : ℝ)) ≤ quasiExpTail n :=
    exp_universalShift_le_quasiExpTail hn2
  have hstrict :
      Real.exp (-2 * (universalShift n) ^ 2 / ((n - 1 : ℕ) : ℝ)) <
        Real.exp (-C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) := by
    refine lt_of_le_of_lt hexp_le ?_
    unfold quasiExpTail
    apply Real.exp_lt_exp.mpr
    rw [show -C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ) =
        -(C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) by ring,
      show -2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10 =
        -(2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10) by ring]
    linarith
  rw [h2t]
  exact ⟨le_trans (cochromatic_upperTail_of_seed hn2 ht_nn (lt_of_lt_of_le hstrict hSCo)) hexp_le,
    le_trans (chromatic_upperTail_of_seed hn2 ht_nn (lt_of_lt_of_le hstrict hSCh)) hexp_le⟩

private theorem abs_exp_sub_one_le_exp_abs_sub_one (z : ℝ) :
    |Real.exp z - 1| ≤ Real.exp |z| - 1 := by
  rcases le_or_gt 0 z with hz | hz
  · rw [abs_of_nonneg hz, abs_of_nonneg (by linarith [Real.one_le_exp hz])]
  · have hneg : -z = |z| := (abs_of_neg hz).symm
    have hexp_le1 : Real.exp z ≤ 1 := Real.exp_le_one_iff.mpr hz.le
    rw [abs_of_nonpos (by linarith)]
    have hsum_ge2 : 2 ≤ Real.exp z + Real.exp (-z) := by
      have hprod : Real.exp z * Real.exp (-z) = 1 := by
        rw [← Real.exp_add]; simp
      have hsq : 0 ≤ (Real.exp z - 1) ^ 2 := sq_nonneg _
      nlinarith [Real.exp_pos z, Real.exp_pos (-z)]
    linarith [hneg ▸ hsum_ge2]

/-- **Moment-generating-function convergence (`Main Theorem`):**
from the `O_ε(exp(-2 n / (log n)^10))` single-`n` deviation tail, for **every**
`t : ℝ`, `lim_{n → ∞} E[exp(t · ((log₂ n)³ / n)(χ(G_n) - ζ(G_n)))] = exp(t / 4)`. -/
theorem tendsto_mgf_normalizedGap_of_quasiExp_tail
    (htail : ∀ eps : ℝ, 0 < eps →
      (fun n : ℕ ↦ (randomGraphMeasure n).real
        {G : LabeledGraph n |
          eps < |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4|})
        =O[atTop] quasiExpTail)
    (t : ℝ) :
    Tendsto (fun n : ℕ ↦
      ∫ G : LabeledGraph n,
        Real.exp (t * ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
          ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))))
        ∂randomGraphMeasure n)
      atTop (nhds (Real.exp (t / 4))) := by
  let Y (n : ℕ) (G : LabeledGraph n) : ℝ :=
    (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
      ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
  -- Step 1: For any `eps > 0`, `2 * exp(|t| * ((log₂ n)³ + 1/4)) * P(|Y_n - 1/4| > eps) → 0`
  have htail_mgf_zero : ∀ eps : ℝ, 0 < eps →
      Tendsto (fun n : ℕ ↦
        2 * Real.exp (|t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4)) *
          (randomGraphMeasure n).real {G | eps < |Y n G - 1 / 4|})
        atTop (nhds 0) := by
    intro eps heps
    obtain ⟨C, hC_pos, hC_ev⟩ := (htail eps heps).exists_pos
    rw [Asymptotics.IsBigOWith] at hC_ev
    have ho13 : (fun x : ℝ ↦ (Real.log x) ^ (13 : ℝ)) =o[atTop]
        (fun x : ℝ ↦ x ^ (1 : ℝ)) :=
      isLittleO_log_rpow_rpow_atTop (13 : ℝ) one_pos
    let c_t : ℝ := 1 / (9 * |t| + 1)
    have hc_t : 0 < c_t := by dsimp [c_t]; positivity
    have hb13 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Asymptotics.isLittleO_iff.mp ho13 hc_t)
    have hL2 : ∀ᶠ n : ℕ in atTop, 2 ≤ Real.log (n : ℝ) :=
      tendsto_logOrder_atTop.eventually (eventually_ge_atTop 2)
    have hdom_zero : Tendsto (fun n : ℕ ↦
        (2 * C) * ((Real.log (n : ℝ)) ^ 10 / (n : ℝ))) atTop (nhds 0) := by
      have ho10 : (fun x : ℝ ↦ (Real.log x) ^ (10 : ℝ)) =o[atTop]
          (fun x : ℝ ↦ x ^ (1 : ℝ)) :=
        isLittleO_log_rpow_rpow_atTop (10 : ℝ) one_pos
      have hdiv := (ho10.tendsto_div_nhds_zero).comp (tendsto_natCast_atTop_atTop (R := ℝ))
      have hmul := hdiv.const_mul (2 * C)
      rw [mul_zero] at hmul
      refine hmul.congr fun n ↦ ?_
      dsimp [Function.comp_def]
      simp [Real.rpow_one]
    refine squeeze_zero' ?_ ?_ hdom_zero
    · exact Filter.Eventually.of_forall fun _ ↦ by positivity
    · filter_upwards [eventually_ge_atTop 3, hC_ev, hb13, hL2] with n hn3 hCn hbn hLn2
      have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      have hL_pos : 0 < Real.log (n : ℝ) := by linarith
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg,
        abs_of_pos (quasiExpTail_pos n)] at hCn
      -- Bound `|t| * ((log₂ n)³ + 1/4) ≤ n / (log n)^10`
      have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hlb2_le : Real.logb 2 (n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
        rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
        nlinarith
      have hlb2_nn : 0 ≤ Real.logb 2 (n : ℝ) := by
        rw [Real.logb]; exact div_nonneg hL_pos.le (Real.log_pos one_lt_two).le
      have hcube_le : (Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4 ≤ 9 * (Real.log (n : ℝ)) ^ 3 := by
        have hc : (Real.logb 2 (n : ℝ)) ^ 3 ≤ 8 * (Real.log (n : ℝ)) ^ 3 := by
          calc (Real.logb 2 (n : ℝ)) ^ 3
              ≤ (2 * Real.log (n : ℝ)) ^ 3 := pow_le_pow_left₀ hlb2_nn hlb2_le 3
            _ = 8 * (Real.log (n : ℝ)) ^ 3 := by ring
        have h1_le_L3 : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := by
          calc (1 : ℝ) = 1 ^ 3 := by norm_num
            _ ≤ (Real.log (n : ℝ)) ^ 3 := pow_le_pow_left₀ zero_le_one (by linarith) 3
        linarith
      have hlog13 : (Real.log (n : ℝ)) ^ 13 ≤ c_t * (n : ℝ) := by
        change ‖(Real.log (n : ℝ)) ^ (13 : ℝ)‖ ≤ c_t * ‖(n : ℝ) ^ (1 : ℝ)‖ at hbn
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (Real.rpow_pos_of_pos hL_pos _),
          abs_of_pos (Real.rpow_pos_of_pos hn_pos _)] at hbn
        simpa [Real.rpow_natCast, Real.rpow_one] using hbn
      have hmul_t : |t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4) ≤
          (n : ℝ) / (Real.log (n : ℝ)) ^ 10 := by
        rw [le_div_iff₀ (pow_pos hL_pos 10)]
        calc |t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4) * (Real.log (n : ℝ)) ^ 10
            ≤ |t| * (9 * (Real.log (n : ℝ)) ^ 3) * (Real.log (n : ℝ)) ^ 10 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hcube_le (abs_nonneg t))
                (pow_nonneg hL_pos.le 10)
          _ = (9 * |t|) * (Real.log (n : ℝ)) ^ 13 := by ring
          _ ≤ (9 * |t| + 1) * (Real.log (n : ℝ)) ^ 13 :=
              mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hL_pos.le 13)
          _ ≤ (9 * |t| + 1) * (c_t * (n : ℝ)) :=
              mul_le_mul_of_nonneg_left hlog13 (by positivity)
          _ = (n : ℝ) := by
              dsimp [c_t]
              field_simp [(show (0 : ℝ) < 9 * |t| + 1 by positivity).ne']
      have hexp_prod :
          Real.exp (|t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4)) * quasiExpTail n ≤
            (Real.log (n : ℝ)) ^ 10 / (n : ℝ) := by
        unfold quasiExpTail
        rw [← Real.exp_add]
        have hsum_exp : |t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4) +
            (-2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10) ≤
              -((n : ℝ) / (Real.log (n : ℝ)) ^ 10) := by
          have : -2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10 =
              -2 * ((n : ℝ) / (Real.log (n : ℝ)) ^ 10) := by ring
          linarith
        have hs_pos : 0 < (n : ℝ) / (Real.log (n : ℝ)) ^ 10 := by positivity
        have hs_inv : Real.exp (-((n : ℝ) / (Real.log (n : ℝ)) ^ 10)) ≤
            (Real.log (n : ℝ)) ^ 10 / (n : ℝ) := by
          have h1 : (n : ℝ) / (Real.log (n : ℝ)) ^ 10 ≤
              Real.exp ((n : ℝ) / (Real.log (n : ℝ)) ^ 10) := by
            linarith [Real.add_one_le_exp ((n : ℝ) / (Real.log (n : ℝ)) ^ 10)]
          have hmul1 : Real.exp (-((n : ℝ) / (Real.log (n : ℝ)) ^ 10)) *
              ((n : ℝ) / (Real.log (n : ℝ)) ^ 10) ≤ 1 := by
            calc Real.exp (-((n : ℝ) / (Real.log (n : ℝ)) ^ 10)) *
                    ((n : ℝ) / (Real.log (n : ℝ)) ^ 10)
                ≤ Real.exp (-((n : ℝ) / (Real.log (n : ℝ)) ^ 10)) *
                    Real.exp ((n : ℝ) / (Real.log (n : ℝ)) ^ 10) :=
                  mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
              _ = Real.exp (-((n : ℝ) / (Real.log (n : ℝ)) ^ 10) +
                    (n : ℝ) / (Real.log (n : ℝ)) ^ 10) := (Real.exp_add ..).symm
              _ = 1 := by simp
          rw [le_div_iff₀ hn_pos]
          have h2 := mul_le_mul_of_nonneg_right hmul1 (pow_nonneg hL_pos.le 10)
          have h3 : ((n : ℝ) / (Real.log (n : ℝ)) ^ 10) * (Real.log (n : ℝ)) ^ 10 = (n : ℝ) :=
            div_mul_cancel₀ _ (pow_pos hL_pos 10).ne'
          rw [mul_assoc, h3, one_mul] at h2
          exact h2
        exact le_trans (Real.exp_le_exp.mpr hsum_exp) hs_inv
      calc 2 * Real.exp (|t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4)) *
              (randomGraphMeasure n).real {G | eps < |Y n G - 1 / 4|}
          ≤ 2 * Real.exp (|t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4)) *
              (C * quasiExpTail n) :=
            mul_le_mul_of_nonneg_left hCn (by positivity)
        _ = (2 * C) * (Real.exp (|t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4)) *
              quasiExpTail n) := by ring
        _ ≤ (2 * C) * ((Real.log (n : ℝ)) ^ 10 / (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hexp_prod (by positivity)
  -- Step 2: Epsilon-delta squeeze on `|∫ exp(t Y_n) - exp(t/4)|`
  rw [Metric.tendsto_nhds]
  intro delta hdelta
  have hd2_pos : 0 < delta / 2 := half_pos hdelta
  -- Choose `eps > 0` so `exp(t/4) * (exp(|t| * eps) - 1) < delta / 2`
  let eps : ℝ := Real.log (1 + delta / (4 * Real.exp (t / 4))) / (|t| + 1)
  have heps_pos : 0 < eps := by
    dsimp [eps]
    apply div_pos
    · exact Real.log_pos (by linarith [div_pos hdelta (by positivity : (0 : ℝ) < 4 * Real.exp (t / 4))])
    · positivity
  have hsmall_term : Real.exp (t / 4) * (Real.exp (|t| * eps) - 1) < delta / 2 := by
    have h1 : |t| * eps ≤ Real.log (1 + delta / (4 * Real.exp (t / 4))) := by
      dsimp [eps]
      have hlog_nn : 0 ≤ Real.log (1 + delta / (4 * Real.exp (t / 4))) :=
        Real.log_nonneg (by linarith [div_pos hdelta (by positivity : (0 : ℝ) < 4 * Real.exp (t / 4))])
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg t]
    have h2 : Real.exp (|t| * eps) ≤ 1 + delta / (4 * Real.exp (t / 4)) := by
      calc Real.exp (|t| * eps)
          ≤ Real.exp (Real.log (1 + delta / (4 * Real.exp (t / 4)))) :=
            Real.exp_le_exp.mpr h1
        _ = 1 + delta / (4 * Real.exp (t / 4)) :=
            Real.exp_log (by linarith [div_pos hdelta (by positivity : (0 : ℝ) < 4 * Real.exp (t / 4))])
    have h3 : Real.exp (t / 4) * (Real.exp (|t| * eps) - 1) ≤ delta / 4 := by
      have hexp_pos := Real.exp_pos (t / 4)
      have hm := mul_le_mul_of_nonneg_left
        (show Real.exp (|t| * eps) - 1 ≤ delta / (4 * Real.exp (t / 4)) by linarith)
        hexp_pos.le
      have hcancel : Real.exp (t / 4) * (delta / (4 * Real.exp (t / 4))) = delta / 4 := by
        field_simp [hexp_pos.ne']
      linarith
    linarith
  have htail_lt : ∀ᶠ n : ℕ in atTop,
      2 * Real.exp (|t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4)) *
        (randomGraphMeasure n).real {G | eps < |Y n G - 1 / 4|} < delta / 2 :=
    (htail_mgf_zero eps heps_pos).eventually (gt_mem_nhds hd2_pos)
  filter_upwards [eventually_ge_atTop 2, htail_lt] with n hn2 htl
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  let Eset : Set (LabeledGraph n) := {G | eps < |Y n G - 1 / 4|}
  have hpointwise : ∀ G : LabeledGraph n,
      |Real.exp (t * Y n G) - Real.exp (t / 4)| ≤
        Real.exp (t / 4) * (Real.exp (|t| * eps) - 1) +
          Eset.indicator
            (fun _ ↦ 2 * Real.exp (|t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4))) G := by
    intro G
    by_cases hG : G ∈ Eset
    · rw [Set.indicator_of_mem hG]
      have hdiff_nn : 0 ≤ (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ) :=
        sub_nonneg.mpr (by exact_mod_cast cochromaticNumber_le_chromaticNumber G)
      have hdiff_le : (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ) ≤ (n : ℝ) := by
        have hchi_le : chromaticNumberNat G ≤ n := by
          simpa [Fintype.card_fin] using chromaticNumberNat_le_card G
        have hchi_R : (chromaticNumberNat G : ℝ) ≤ (n : ℝ) := by exact_mod_cast hchi_le
        have hzeta_nn : (0 : ℝ) ≤ (cochromaticNumber G : ℝ) := Nat.cast_nonneg _
        linarith
      have hlb2_nn : 0 ≤ Real.logb 2 (n : ℝ) := by
        rw [Real.logb]
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
          (Real.log_pos one_lt_two).le
      have hY_nn : 0 ≤ Y n G := by dsimp [Y]; positivity
      have hY_le : Y n G ≤ (Real.logb 2 (n : ℝ)) ^ 3 := by
        dsimp [Y]
        calc (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
                ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
            ≤ (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) * (n : ℝ) :=
              mul_le_mul_of_nonneg_left hdiff_le (by positivity)
          _ = (Real.logb 2 (n : ℝ)) ^ 3 := div_mul_cancel₀ _ hn_pos.ne'
      have htY_le : t * Y n G ≤ |t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4) := by
        calc t * Y n G ≤ |t * Y n G| := le_abs_self _
          _ = |t| * |Y n G| := abs_mul t (Y n G)
          _ = |t| * Y n G := by rw [abs_of_nonneg hY_nn]
          _ ≤ |t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4) :=
              mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
      have ht4_le : t / 4 ≤ |t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4) := by
        have ht_le : t ≤ |t| := le_abs_self t
        have hc_nn : 0 ≤ (Real.logb 2 (n : ℝ)) ^ 3 := pow_nonneg hlb2_nn 3
        nlinarith [abs_nonneg t]
      have habs_exp : |Real.exp (t * Y n G) - Real.exp (t / 4)| ≤
          2 * Real.exp (|t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4)) := by
        calc |Real.exp (t * Y n G) - Real.exp (t / 4)|
            ≤ |Real.exp (t * Y n G)| + |Real.exp (t / 4)| := abs_sub _ _
          _ = Real.exp (t * Y n G) + Real.exp (t / 4) := by
              rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
          _ ≤ Real.exp (|t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4)) +
                Real.exp (|t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4)) :=
              add_le_add (Real.exp_le_exp.mpr htY_le) (Real.exp_le_exp.mpr ht4_le)
          _ = 2 * Real.exp (|t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4)) := by ring
      have hfirst_nn : 0 ≤ Real.exp (t / 4) * (Real.exp (|t| * eps) - 1) :=
        mul_nonneg (Real.exp_pos _).le
          (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg (abs_nonneg t) heps_pos.le)))
      linarith
    · rw [Set.indicator_of_notMem hG, add_zero]
      have hle : |Y n G - 1 / 4| ≤ eps := not_lt.mp hG
      have hfactor : Real.exp (t * Y n G) - Real.exp (t / 4) =
          Real.exp (t / 4) * (Real.exp (t * (Y n G - 1 / 4)) - 1) := by
        rw [mul_sub, mul_one, ← Real.exp_add,
          show t / 4 + t * (Y n G - 1 / 4) = t * Y n G by ring]
      rw [hfactor, abs_mul, abs_of_pos (Real.exp_pos (t / 4))]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos (t / 4)).le
      calc |Real.exp (t * (Y n G - 1 / 4)) - 1|
          ≤ Real.exp |t * (Y n G - 1 / 4)| - 1 :=
            abs_exp_sub_one_le_exp_abs_sub_one _
        _ = Real.exp (|t| * |Y n G - 1 / 4|) - 1 := by rw [abs_mul]
        _ ≤ Real.exp (|t| * eps) - 1 :=
            sub_le_sub_right
              (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle (abs_nonneg t))) 1
  have hint_diff :
      |(∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n) -
          Real.exp (t / 4)| ≤
        Real.exp (t / 4) * (Real.exp (|t| * eps) - 1) +
          2 * Real.exp (|t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4)) *
            (randomGraphMeasure n).real Eset := by
    have heq :
        (∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n) -
            Real.exp (t / 4) =
          ∫ G : LabeledGraph n, (Real.exp (t * Y n G) - Real.exp (t / 4))
            ∂randomGraphMeasure n := by
      symm
      rw [integral_sub (Integrable.of_finite) (Integrable.of_finite),
        integral_const, probReal_univ, one_smul]
    rw [heq]
    calc |∫ G : LabeledGraph n, (Real.exp (t * Y n G) - Real.exp (t / 4))
            ∂randomGraphMeasure n|
        ≤ ∫ G : LabeledGraph n, |Real.exp (t * Y n G) - Real.exp (t / 4)|
            ∂randomGraphMeasure n := abs_integral_le_integral_abs
      _ ≤ ∫ G : LabeledGraph n,
            (Real.exp (t / 4) * (Real.exp (|t| * eps) - 1) +
              Eset.indicator
                (fun _ ↦ 2 * Real.exp (|t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4))) G)
            ∂randomGraphMeasure n :=
          integral_mono (Integrable.of_finite) (Integrable.of_finite) hpointwise
      _ = (∫ _G : LabeledGraph n,
              Real.exp (t / 4) * (Real.exp (|t| * eps) - 1) ∂randomGraphMeasure n) +
            ∫ G : LabeledGraph n,
              Eset.indicator
                (fun _ ↦ 2 * Real.exp (|t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4))) G
              ∂randomGraphMeasure n :=
          integral_add (Integrable.of_finite) (Integrable.of_finite)
      _ = Real.exp (t / 4) * (Real.exp (|t| * eps) - 1) +
            2 * Real.exp (|t| * ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4)) *
              (randomGraphMeasure n).real Eset := by
          rw [integral_const, probReal_univ, one_smul,
            integral_indicator_const _ (Set.toFinite Eset).measurableSet,
            smul_eq_mul]
          ring
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hint_diff (by linarith)

/-- **Complete v7 Main Theorem assembly from the `O_ε(exp(-2 n / (log n)^10))` tail:**
proves simultaneously:
1. arbitrary-coupling almost-sure convergence in natural and base-`2` logarithms;
2. `L^p` convergence `E[|Y_n - 1/4|^p] → 0` for every `1 ≤ p < ∞`;
3. expectation asymptotic `((log₂ n)³ / n) E[χ(G_n) - ζ(G_n)] → 1 / 4`;
4. moment-generating-function convergence `E[exp(t Y_n)] → exp(t / 4)` for every `t ∈ ℝ`. -/
theorem mainTheorem_ae_lp_expectation_and_mgf_of_quasiExp_tail
    (htail : ∀ eps : ℝ, 0 < eps →
      (fun n : ℕ ↦ (randomGraphMeasure n).real
        {G : LabeledGraph n |
          eps < |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4|})
        =O[atTop] quasiExpTail) :
    (∀ {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
      (G : ∀ n : ℕ, Ω → LabeledGraph n),
      (∀ n : ℕ, Measure.map (G n) ℙ = randomGraphMeasure n) →
      ∀ᵐ ω ∂ℙ,
        Tendsto (fun n : ℕ ↦
          (Real.log n) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ)))
          atTop (nhds sharpGapConstant) ∧
        Tendsto (fun n : ℕ ↦
          (Real.logb 2 n) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ)))
          atTop (nhds (1 / 4 : ℝ))) ∧
    (∀ {p : ℝ}, 1 ≤ p →
      Tendsto (fun n : ℕ ↦
        ∫ G : LabeledGraph n,
          |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4| ^ p
          ∂randomGraphMeasure n)
        atTop (nhds 0)) ∧
    Tendsto (fun n : ℕ ↦
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
        ∫ G : LabeledGraph n,
          ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
          ∂randomGraphMeasure n)
      atTop (nhds (1 / 4 : ℝ)) ∧
    ∀ t : ℝ,
      Tendsto (fun n : ℕ ↦
        ∫ G : LabeledGraph n,
          Real.exp (t * ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))))
          ∂randomGraphMeasure n)
        atTop (nhds (Real.exp (t / 4))) := by
  have hpoly : ∀ eps : ℝ, 0 < eps →
      (fun n : ℕ ↦ (randomGraphMeasure n).real
        {G : LabeledGraph n |
          eps < |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4|})
        =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ)) *
        (Real.log (n : ℝ)) ^ ((2 / Real.log 2 + 1 / 2 : ℝ) + 5 / 2)) := by
    intro eps heps
    simpa [phaseTailBeta, Erdos625.q] using
      (htail eps heps).trans quasiExpTail_isBigO_polylogTail
  have hsum_compl : ∀ eta : ℝ, 0 < eta →
      Summable (fun n : ℕ ↦ (randomGraphMeasure n).real
        (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n)ᶜ) := by
    intro eta heta
    have hq3_pos : 0 < (Real.log 2) ^ 3 := pow_pos (Real.log_pos one_lt_two) 3
    let eps : ℝ := eta / (Real.log 2) ^ 3
    have heps : 0 < eps := div_pos heta hq3_pos
    obtain ⟨C, hC_ev⟩ := (htail eps heps).bound
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hC_ev.and (eventually_ge_atTop 2))
    have hdom : Summable (fun k : ℕ ↦ |C| * quasiExpTail (k + N₀)) :=
      (summable_quasiExpTail.comp_injective (add_left_injective N₀)).mul_left |C|
    have hshift : Summable (fun k : ℕ ↦ (randomGraphMeasure (k + N₀)).real
        (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) (k + N₀))ᶜ) := by
      refine Summable.of_nonneg_of_le (fun _ ↦ measureReal_nonneg) (fun k ↦ ?_) hdom
      set n := k + N₀
      obtain ⟨hCn, hn2⟩ := hN₀ n (Nat.le_add_left N₀ k)
      have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hsub :
          (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n)ᶜ ⊆
            {G : LabeledGraph n |
              eps < |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
                ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4|} := by
        intro G hGnot
        rw [Set.mem_setOf_eq]
        by_contra hle_not
        have hle_abs : |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4| ≤ eps :=
          not_lt.mp hle_not
        rw [abs_le] at hle_abs
        apply hGnot
        unfold twoSidedGapEvent sharpGapConstant
        rw [Set.mem_setOf_eq]
        have hrel : (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) =
            1 / ((Real.log 2) ^ 3 * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)) := by
          rw [Real.logb]
          field_simp [hn_pos.ne', hL_pos.ne', hq3_pos.ne']
        have hscale_pos : 0 < (Real.log 2) ^ 3 * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) := by
          positivity
        set D : ℝ := (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)
        have hlo1 := mul_le_mul_of_nonneg_left hle_abs.1 hscale_pos.le
        have hhi1 := mul_le_mul_of_nonneg_left hle_abs.2 hscale_pos.le
        have hmid : (Real.log 2) ^ 3 * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) *
            ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) * D - 1 / 4) =
              D - (Real.log 2) ^ 3 / 4 * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) := by
          rw [hrel]
          field_simp [hscale_pos.ne']
        have heps_mul : (Real.log 2) ^ 3 * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) * eps =
            eta * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) := by
          dsimp [eps]
          field_simp [hq3_pos.ne']
        have heps_neg : (Real.log 2) ^ 3 * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) * (-eps) =
            -(eta * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)) := by
          rw [mul_neg, heps_mul]
        rw [hmid, heps_neg] at hlo1
        rw [hmid, heps_mul] at hhi1
        exact ⟨by linarith, by linarith⟩
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg,
        abs_of_pos (quasiExpTail_pos n)] at hCn
      exact le_trans (measureReal_mono hsub)
        (le_trans hCn (mul_le_mul_of_nonneg_right (le_abs_self C) (quasiExpTail_pos n).le))
    exact (summable_nat_add_iff N₀).mp hshift
  refine ⟨fun ℙ _ G hMarg ↦ ae_tendsto_normalizedGap_of_summable_failures ℙ G hMarg hsum_compl,
    fun hp ↦ tendsto_integral_abs_sub_rpow_normalizedGap_of_polylog_tail hpoly hp,
    tendsto_expected_normalizedGap_of_polylog_tail hpoly,
    tendsto_mgf_normalizedGap_of_quasiExp_tail htail⟩

/-- **Complete v7 Phase Refinement assembly (quasi-exponential exit tail + expectation sandwich + a.s.):**
under an `O(exp(-2 n / (log n)^10))` exit tail from the `tildeEps = O(log log n / log n)`
phase interval, setting `ε_n := tildeEps n + 1 / log n` (`n ≥ 3`, `0` otherwise) yields:
1. `0 ≤ ε_n` for all `n` and `ε_n ≤ C₁ log log n / log n` for all `n ≥ 3`;
2. `P(G_n ∉ twoSidedGapEvent (lower - ε_n) (upper + ε_n) n) = O(exp(-2 n / (log n)^10))`;
3. `((log n)³ / n) E[χ(G_n) - ζ(G_n)] ∈ [lower - ε_n, upper + ε_n]` eventually;
4. for every `c' ≤ 0.080` and `C' ≥ 0.086`, `[c', C'] · n / (log n)³` holds eventually
   both in expectation and almost surely under every `G(n, 1/2)` coupling. -/
theorem phaseRefinement_expectation_and_ae_of_quasiExp_tail
    (tildeEps : ℕ → ℝ)
    (htilde_nn : ∀ n, 0 ≤ tildeEps n)
    (htilde_O : tildeEps =O[atTop]
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)))
    (htail : (fun n : ℕ ↦ (randomGraphMeasure n).real
        (twoSidedGapEvent
          (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - tildeEps n)
          (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + tildeEps n) n)ᶜ)
      =O[atTop] quasiExpTail) :
    let eps : ℕ → ℝ := fun n ↦ if 3 ≤ n then tildeEps n + 1 / Real.log (n : ℝ) else 0
    (∃ C₁ : ℝ, 0 < C₁ ∧ (∀ n, 0 ≤ eps n) ∧
      ∀ n ≥ 3, eps n ≤ C₁ * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) ∧
    ((fun n : ℕ ↦ (randomGraphMeasure n).real
        (twoSidedGapEvent
          (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n)
          (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) n)ᶜ)
      =O[atTop] quasiExpTail) ∧
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
          upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) ∧
    (∀ c' C' : ℝ, c' ≤ 80 / 1000 → 86 / 1000 ≤ C' →
      (∀ᶠ n : ℕ in atTop,
        c' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) ≤
            (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ∧
          (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ≤
            C' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)) ∧
      (∀ {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
        (G : ∀ n : ℕ, Ω → LabeledGraph n),
        (∀ n : ℕ, Measure.map (G n) ℙ = randomGraphMeasure n) →
        ∀ᵐ ω ∂ℙ, ∀ᶠ n : ℕ in atTop,
          c' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) ≤
              (chromaticNumberNat (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ) ∧
            (chromaticNumberNat (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ) ≤
              C' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3))) := by
  intro eps
  obtain ⟨h1, _, h3, h4⟩ :=
    phaseRefinement_expectation_and_ae_of_polylog_tail tildeEps htilde_nn htilde_O
      (htail.trans quasiExpTail_isBigO_polylogTail)
  refine ⟨h1, ?_, h3, h4⟩
  refine IsBigO.trans ?_ htail
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 3] with n hn3
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hsub :
      (twoSidedGapEvent
        (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n)
        (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) n)ᶜ ⊆
      (twoSidedGapEvent
        (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - tildeEps n)
        (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + tildeEps n) n)ᶜ := by
    apply Set.compl_subset_compl.mpr
    intro G ⟨hlo, hhi⟩
    have heps_ge : tildeEps n ≤ eps n := by
      dsimp [eps]; rw [if_pos hn3]
      linarith [div_pos one_pos hL_pos]
    have hfac_nn : 0 ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by positivity
    refine ⟨?_, ?_⟩
    · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hfac_nn) hlo
    · exact le_trans hhi (mul_le_mul_of_nonneg_right (by linarith) hfac_nn)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg,
    abs_of_nonneg measureReal_nonneg, one_mul]
  exact measureReal_mono hsub

end

end Erdos625HP
