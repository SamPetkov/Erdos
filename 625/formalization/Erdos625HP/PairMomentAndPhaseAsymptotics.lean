import Erdos625.MuVertexScaling
import Erdos625.PhaseConsequences
import Erdos625HP.BoundedLowerTailsAndMomentCore
import Erdos625HP.DisjointLargeSetOscillation
import Erdos625HP.ShiftedSevenSizeCertificate

/-!
# Pair moments, uniform phase expansions, shift equivariance, and `L¹`/almost-sure assemblies

This module completes the remaining unconditional and conditional pillars of the
15-page v6 manuscript:

1. **Section 1 (`lem:independent-pair-tail`) & Section 4 (`prop:lower-tails` exceptional event):**
   * `integral_independentSetCount_mul_sub_one_le`: for `1 ≤ u < n`,
     `E[X_u(G_n)(X_u(G_n) - 1)] ≤ μ_u² exp(J_u) + μ_u (exp(K_u) - 1)`
     with `J_u = u² · 2^(u/4) / (n - u)` and `K_u = √2 · u · n · 2^(-3u/4)`.
   * `randomGraph_independentSetCount_ge_two_le`: Markov tail
     `P(X_u(G_n) ≥ 2) ≤ 1/2 · (μ_u² exp(J_u) + μ_u (exp(K_u) - 1))`.
   * `randomGraph_lowerTailExceptional_le`: Proposition 4.1's four-event exceptional
     union bound `P({X_u(G) ≥ 2} ∪ {X_u(Gᶜ) ≥ 2} ∪ {D_{u_m}(G) > d_{n,m}} ∪ {D_{u_m}(Gᶜ) > d_{n,m}}) ≤ 𝓔_u`.

2. **Section 2 (`lem:phase-expansion`, `(2.2)`–`(2.4)`) & Section 9 summability of `𝓔_{α+2}`:**
   * `exists_uniform_phaseExpansion_and_adjacent_bounds`: all six displays of Lemma 2.1
     uniformly across `δ_n ∈ [0, 1)`, including the phase-retaining `n^(1 + δ_n)` and
     `n^(2 + δ_n)` lower bounds on `μ_{α-1}` and `μ_{α-2}`, `μ_{α+1} ≤ C₂ (log n)^(2/q - 1/2)`,
     `log μ_{α+2} = (δ_n - 2) L + (2/q + 3/2 - δ_n) ℓ + O(1)`, and `μ_{α+2} ≤ exp(-L + C₂ ℓ)`.
   * `lowerTailExceptionalBound_phaseNat_add_two_isBigO`:
     `𝓔_{α+2}(n) = O(n^(-3/2) (log n)^(β + 5/2))` with `β = 2/q + 1/2`.
   * `summable_polylog_three_halves` and `summable_lowerTailExceptionalBound_phaseNat_add_two`:
     `∑_n n^(-3/2) (log n)^γ < ∞` for every `γ : ℝ`, hence `∑_n 𝓔_{α+2}(n) < ∞`.

3. **Section 3 (`eq:shift-equivariance`, full Gibbs probability and mean equivariance):**
   * `gibbsProb_shiftSupportOne`: `p_{S+1,λ}(i + 1) = p_{S,λ - log 2}(i)` for all `S ⊆ ℤ`.
   * `gibbsMean_shiftSupportOne`: `M_{S+1}(λ) = M_S(λ - log 2) + 1` for every nonempty `S ⊆ ℤ`.
   * `unique_gibbsMean_shiftSupportOne_and_prob_eq` and `dualValue_diff_shiftSupportOne`.

4. **Section 6 (`lemma-7.1-all-common-subprofiles(ii)`, unconditional asymptotic full-corner decay):**
   * `eventually_mu_vertexCap_le_rpow_neg_five_halves`: uniformly over
     `u ∈ [α - (M + 1), α]` and `w ≤ 2^(-(M + 5)) n`, `μ_w(u) ≤ n^(-5/2)` eventually.
   * `eventually_partialDiagonalWeight_subprofile_le_exp_neg_half` and
     `eventually_unmarkedDiagonalWeight_subprofile_le_exp_neg_half`: both unconditional
     asymptotic chains of Lemma 6.1(ii) for `W(ν)` and `F₁^ch(ν)` when `n - m_ν ≤ 2^(-(M+5)) n`.

5. **Section 8 (`cor:zeta-upper`) & Section 9 (`Phase Refinement` expectation + almost-sure assembly):**
   * `concentrationAllowance_isLittleO` and `regime_cochromatic_and_chromatic_upperTail_of_secondMoment_seed`.
   * `phaseGain7_le_log_two` (`A₇(td) ≤ log 2` on `[0, 207/200]`) and
     `phaseRefinement_expectation_and_ae_of_polylog_tail`.
-/

namespace Erdos625HP

open Erdos625 Erdos625.FiveSizeEntropyGap Filter Asymptotics MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

/-! ## 1. Lemma 1.3 (`lem:independent-pair-tail`) & Proposition 4.1 exceptional event -/

/-- Overlap kernel `J_u = u² · 2^(u / 4) / (n - u)` from Lemma 1.3 (`lem:independent-pair-tail`). -/
def pairKernelJ (n u : ℕ) : ℝ :=
  (u : ℝ) ^ 2 * (2 : ℝ) ^ ((u : ℝ) / 4) / ((n - u : ℕ) : ℝ)

/-- Overlap kernel `K_u = √2 · u · n · 2^(-3 u / 4)` from Lemma 1.3 (`lem:independent-pair-tail`). -/
def pairKernelK (n u : ℕ) : ℝ :=
  Real.sqrt 2 * (u : ℝ) * (n : ℝ) * (2 : ℝ) ^ (-3 * (u : ℝ) / 4)

/-- Exceptional-event bound `𝓔_u = μ_u² e^{J_u} + μ_u (e^{K_u} - 1) + 2 e^{-2 (log n)⁴}`
from Proposition 4.1 (`prop:lower-tails`). -/
def lowerTailExceptionalBound (n u : ℕ) : ℝ :=
  (mu n u) ^ 2 * Real.exp (pairKernelJ n u) +
    mu n u * (Real.exp (pairKernelK n u) - 1) +
    2 * Real.exp (-2 * (Real.log (n : ℝ)) ^ 4)

private theorem pairKernelJ_nonneg (n u : ℕ) : 0 ≤ pairKernelJ n u := by
  unfold pairKernelJ
  positivity

private theorem pairKernelK_nonneg (n u : ℕ) : 0 ≤ pairKernelK n u := by
  unfold pairKernelK
  positivity

private theorem sum_pow_div_factorial_le_exp {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    ∑ k ∈ Finset.range m, x ^ k / (k.factorial : ℝ) ≤ Real.exp x :=
  Real.sum_le_exp_of_nonneg hx m

private theorem completeOn_adj_iff {n : ℕ} (U : Finset (Fin n)) (x y : Fin n) :
    (completeOn U).Adj x y ↔ x ≠ y ∧ x ∈ U ∧ y ∈ U := by
  unfold completeOn
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨a, b, hne, rfl, rfl⟩
    exact ⟨fun h ↦ hne (Subtype.ext h), a.2, b.2⟩
  · rintro ⟨hne, hx, hy⟩
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h ↦ hne (congrArg Subtype.val h), rfl, rfl⟩

private theorem completeOn_inf_eq_inter {n : ℕ} (U₁ U₂ : Finset (Fin n)) :
    completeOn U₁ ⊓ completeOn U₂ = completeOn (U₁ ∩ U₂) := by
  ext x y
  rw [SimpleGraph.inf_adj, completeOn_adj_iff, completeOn_adj_iff, completeOn_adj_iff,
    Finset.mem_inter, Finset.mem_inter]
  tauto

private theorem ncard_edgeSet_completeOn_sup {n : ℕ} (U₁ U₂ : Finset (Fin n)) :
    (completeOn U₁ ⊔ completeOn U₂).edgeSet.ncard =
      U₁.card.choose 2 + U₂.card.choose 2 - (U₁ ∩ U₂).card.choose 2 := by
  have hunion :
      ((completeOn U₁).edgeSet ∪ (completeOn U₂).edgeSet).ncard +
        ((completeOn U₁).edgeSet ∩ (completeOn U₂).edgeSet).ncard =
      (completeOn U₁).edgeSet.ncard + (completeOn U₂).edgeSet.ncard :=
    Set.ncard_union_add_ncard_inter (completeOn U₁).edgeSet (completeOn U₂).edgeSet
  have hsup :
      (completeOn U₁ ⊔ completeOn U₂).edgeSet =
        (completeOn U₁).edgeSet ∪ (completeOn U₂).edgeSet :=
    SimpleGraph.edgeSet_sup (completeOn U₁) (completeOn U₂)
  have hinf :
      (completeOn (U₁ ∩ U₂)).edgeSet =
        (completeOn U₁).edgeSet ∩ (completeOn U₂).edgeSet := by
    rw [← completeOn_inf_eq_inter, SimpleGraph.edgeSet_inf]
  rw [← hsup, ← hinf, ncard_edgeSet_completeOn, ncard_edgeSet_completeOn,
    ncard_edgeSet_completeOn] at hunion
  have hle : (U₁ ∩ U₂).card.choose 2 ≤ U₁.card.choose 2 :=
    Nat.choose_le_choose 2 (Finset.card_le_card Finset.inter_subset_left)
  omega

private theorem integral_mul_independentIndicatorNat {n : ℕ}
    (U₁ U₂ : Finset (Fin n)) :
    ∫ G : LabeledGraph n,
        (independentIndicatorNat G U₁ : ℝ) * (independentIndicatorNat G U₂ : ℝ)
        ∂randomGraphMeasure n =
      ((1 / 2 : ℝ) ^ (U₁.card.choose 2 + U₂.card.choose 2 - (U₁ ∩ U₂).card.choose 2)) := by
  classical
  let E : Set (LabeledGraph n) := {G | G ≤ (completeOn U₁ ⊔ completeOn U₂)ᶜ}
  have hpoint : ∀ G : LabeledGraph n,
      (independentIndicatorNat G U₁ : ℝ) * (independentIndicatorNat G U₂ : ℝ) =
        E.indicator 1 G := by
    intro G
    by_cases h₁ : G.IsIndepSet (U₁ : Set (Fin n)) <;>
      by_cases h₂ : G.IsIndepSet (U₂ : Set (Fin n))
    · have hE : G ∈ E := by
        rw [Set.mem_setOf_eq, le_compl_iff_disjoint_right, disjoint_sup_right]
        exact ⟨(isIndepSet_iff_disjoint_completeOn G U₁).mp h₁,
          (isIndepSet_iff_disjoint_completeOn G U₂).mp h₂⟩
      simp [independentIndicatorNat, h₁, h₂, hE]
    · have hE : G ∉ E := by
        intro hm
        rw [Set.mem_setOf_eq, le_compl_iff_disjoint_right, disjoint_sup_right] at hm
        exact h₂ ((isIndepSet_iff_disjoint_completeOn G U₂).mpr hm.2)
      simp [independentIndicatorNat, h₁, h₂, hE]
    · have hE : G ∉ E := by
        intro hm
        rw [Set.mem_setOf_eq, le_compl_iff_disjoint_right, disjoint_sup_right] at hm
        exact h₁ ((isIndepSet_iff_disjoint_completeOn G U₁).mpr hm.1)
      simp [independentIndicatorNat, h₁, h₂, hE]
    · have hE : G ∉ E := by
        intro hm
        rw [Set.mem_setOf_eq, le_compl_iff_disjoint_right, disjoint_sup_right] at hm
        exact h₁ ((isIndepSet_iff_disjoint_completeOn G U₁).mpr hm.1)
      simp [independentIndicatorNat, h₁, h₂, hE]
  simp_rw [hpoint]
  rw [integral_indicator_one (Set.toFinite E).measurableSet]
  have hmeas : randomGraphMeasure n E =
      (1 / 2 : ENNReal) ^ (completeOn U₁ ⊔ completeOn U₂).edgeSet.ncard :=
    randomGraphMeasure_le_compl (completeOn U₁ ⊔ completeOn U₂)
  rw [Measure.real, hmeas, ncard_edgeSet_completeOn_sup, ENNReal.toReal_pow]
  norm_num

private theorem independentSetCount_mul_sub_one_eq_sum {n u : ℕ} (G : LabeledGraph n) :
    (independentSetCount G u : ℝ) * ((independentSetCount G u : ℝ) - 1) =
      ∑ U₁ ∈ (Finset.univ : Finset (Fin n)).powersetCard u,
        ∑ U₂ ∈ ((Finset.univ : Finset (Fin n)).powersetCard u).erase U₁,
          (independentIndicatorNat G U₁ : ℝ) * (independentIndicatorNat G U₂ : ℝ) := by
  classical
  set P := (Finset.univ : Finset (Fin n)).powersetCard u
  let f : Finset (Fin n) → ℝ := fun U ↦ (independentIndicatorNat G U : ℝ)
  have hf_sq : ∀ U : Finset (Fin n), f U * f U = f U := by
    intro U
    dsimp [f]
    unfold independentIndicatorNat
    split_ifs <;> norm_num
  have hcast : (independentSetCount G u : ℝ) = ∑ U ∈ P, f U := by
    unfold independentSetCount
    push_cast
    rfl
  rw [hcast]
  have hsq :
      (∑ U₁ ∈ P, f U₁) * (∑ U₂ ∈ P, f U₂) =
        ∑ U₁ ∈ P, (f U₁ + ∑ U₂ ∈ P.erase U₁, f U₁ * f U₂) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun U₁ hU₁ ↦ ?_
    rw [Finset.mul_sum, ← Finset.add_sum_erase P (fun U₂ ↦ f U₁ * f U₂) hU₁, hf_sq U₁]
  calc (∑ U ∈ P, f U) * ((∑ U ∈ P, f U) - 1)
      = (∑ U₁ ∈ P, f U₁) * (∑ U₂ ∈ P, f U₂) - ∑ U₁ ∈ P, f U₁ := by ring
    _ = (∑ U₁ ∈ P, (f U₁ + ∑ U₂ ∈ P.erase U₁, f U₁ * f U₂)) - ∑ U₁ ∈ P, f U₁ := by rw [hsq]
    _ = ∑ U₁ ∈ P, ∑ U₂ ∈ P.erase U₁, f U₁ * f U₂ := by
        rw [Finset.sum_add_distrib, add_sub_cancel_left]

private theorem card_filter_inter_eq_le {n u j : ℕ}
    {U₁ : Finset (Fin n)} (hU₁ : U₁.card = u) :
    ((((Finset.univ : Finset (Fin n)).powersetCard u).erase U₁).filter
      (fun U₂ ↦ (U₁ ∩ U₂).card = j)).card ≤
      u.choose j * (n - u).choose (u - j) := by
  classical
  let F := ((((Finset.univ : Finset (Fin n)).powersetCard u).erase U₁).filter
    (fun U₂ ↦ (U₁ ∩ U₂).card = j))
  let Target := U₁.powersetCard j ×ˢ ((Finset.univ : Finset (Fin n)) \ U₁).powersetCard (u - j)
  let split : Finset (Fin n) → Finset (Fin n) × Finset (Fin n) :=
    fun U₂ ↦ (U₁ ∩ U₂, U₂ \ U₁)
  have hinj : Set.InjOn split (F : Set (Finset (Fin n))) := by
    intro A _ B _ hAB
    have h1 := Finset.ext_iff.mp (congrArg Prod.fst hAB)
    have h2 := Finset.ext_iff.mp (congrArg Prod.snd hAB)
    ext x
    specialize h1 x
    specialize h2 x
    dsimp [split] at h1 h2
    simp only [Finset.mem_inter, Finset.mem_sdiff] at h1 h2
    by_cases hx : x ∈ U₁
    · exact ⟨fun hA ↦ (h1.mp ⟨hx, hA⟩).2, fun hB ↦ (h1.mpr ⟨hx, hB⟩).2⟩
    · exact ⟨fun hA ↦ (h2.mp ⟨hA, hx⟩).1, fun hB ↦ (h2.mpr ⟨hB, hx⟩).1⟩
  have himg : F.image split ⊆ Target := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨U₂, hU₂, rfl⟩
    simp only [F, Finset.mem_filter, Finset.mem_erase, Finset.mem_powersetCard,
      Finset.subset_univ, true_and] at hU₂
    obtain ⟨⟨_, hU₂card⟩, hinter⟩ := hU₂
    simp only [Target, split, Finset.mem_product, Finset.mem_powersetCard]
    refine ⟨⟨Finset.inter_subset_left, hinter⟩, ⟨?_, ?_⟩⟩
    · intro x hx
      rw [Finset.mem_sdiff] at hx ⊢
      exact ⟨Finset.mem_univ x, hx.2⟩
    · have hpart := Finset.card_inter_add_card_sdiff U₂ U₁
      rw [Finset.inter_comm, hinter, hU₂card] at hpart
      omega
  calc F.card = (F.image split).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Target.card := Finset.card_le_card himg
    _ = u.choose j * (n - u).choose (u - j) := by
        rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
          Finset.card_sdiff_of_subset (Finset.subset_univ U₁),
          Finset.card_univ, Fintype.card_fin, hU₁]

private theorem pow_sub_le_descFactorial {n u j : ℕ} (hju : j ≤ u) :
    (n - u) ^ j ≤ n.descFactorial j := by
  have hp : (n - u) ^ j = ∏ _k ∈ Finset.range j, (n - u) := by simp
  rw [hp, Nat.descFactorial_eq_prod_range]
  refine Finset.prod_le_prod' fun k hk ↦ ?_
  have hk_lt : k < j := Finset.mem_range.mp hk
  omega

private theorem descFactorial_mono_left {a b k : ℕ} (hab : a ≤ b) :
    a.descFactorial k ≤ b.descFactorial k := by
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
  exact Finset.prod_le_prod' fun i _ ↦ Nat.sub_le_sub_right hab i

private theorem descFactorial_split_add (n a b : ℕ) :
    n.descFactorial (a + b) = n.descFactorial a * (n - a).descFactorial b := by
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_eq_prod_range, Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  omega

private theorem pair_choose_mul_pow_le {n u j : ℕ} (hju : j ≤ u) :
    j.factorial * (u.choose j * (n - u).choose (u - j)) * (n - u) ^ j ≤
      n.choose u * u ^ (2 * j) := by
  have hfac_pos : 0 < (u - j).factorial := Nat.factorial_pos _
  apply Nat.le_of_mul_le_mul_left _ hfac_pos
  have h1 : j.factorial * u.choose j ≤ u ^ j := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow u j
  have h2 : (u - j).factorial * (n - u).choose (u - j) ≤ (n - j).descFactorial (u - j) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact descFactorial_mono_left (by omega)
  have h3 : (n - u) ^ j ≤ n.descFactorial j := pow_sub_le_descFactorial hju
  have h23 :
      ((u - j).factorial * (n - u).choose (u - j)) * (n - u) ^ j ≤
        u.factorial * n.choose u := by
    calc ((u - j).factorial * (n - u).choose (u - j)) * (n - u) ^ j
        ≤ (n - j).descFactorial (u - j) * n.descFactorial j := Nat.mul_le_mul h2 h3
      _ = n.descFactorial j * (n - j).descFactorial (u - j) := Nat.mul_comm _ _
      _ = n.descFactorial (j + (u - j)) := (descFactorial_split_add n j (u - j)).symm
      _ = n.descFactorial u := by rw [Nat.add_sub_of_le hju]
      _ = u.factorial * n.choose u := Nat.descFactorial_eq_factorial_mul_choose n u
  have hufac : u.factorial ≤ u ^ j * (u - j).factorial := by
    have heq : u.factorial = u.descFactorial j * (u - j).factorial := by
      have h := Nat.descFactorial_eq_factorial_mul_choose u j
      have hc := Nat.choose_mul_factorial_mul_factorial hju
      calc u.factorial = u.choose j * j.factorial * (u - j).factorial := hc.symm
        _ = (j.factorial * u.choose j) * (u - j).factorial := by ring
        _ = u.descFactorial j * (u - j).factorial := by rw [h]
    rw [heq]
    exact Nat.mul_le_mul_right _ (Nat.descFactorial_le_pow u j)
  calc (u - j).factorial * (j.factorial * (u.choose j * (n - u).choose (u - j)) * (n - u) ^ j)
      = (j.factorial * u.choose j) *
          (((u - j).factorial * (n - u).choose (u - j)) * (n - u) ^ j) := by ring
    _ ≤ u ^ j * (u.factorial * n.choose u) := Nat.mul_le_mul h1 h23
    _ ≤ u ^ j * ((u ^ j * (u - j).factorial) * n.choose u) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hufac)
    _ = (u - j).factorial * (n.choose u * (u ^ j * u ^ j)) := by ring
    _ = (u - j).factorial * (n.choose u * u ^ (2 * j)) := by rw [two_mul, pow_add]

private theorem two_pow_choose_two_le_quarter {u j : ℕ} (h2j : 2 * j ≤ u) :
    ((2 : ℝ) ^ (j.choose 2)) ≤ ((2 : ℝ) ^ ((u : ℝ) / 4)) ^ j := by
  have hnat : 4 * j.choose 2 ≤ u * j := by
    have hc : 2 * j.choose 2 = j * (j - 1) := by
      rw [Nat.choose_two_right, Nat.mul_comm 2]
      exact Nat.div_mul_cancel (Nat.even_mul_pred_self j).two_dvd
    calc 4 * j.choose 2 = 2 * (2 * j.choose 2) := by ring
      _ = 2 * (j * (j - 1)) := by rw [hc]
      _ = j * (2 * (j - 1)) := by ring
      _ ≤ j * (2 * j) := Nat.mul_le_mul_left j (by omega)
      _ ≤ j * u := Nat.mul_le_mul_left j h2j
      _ = u * j := Nat.mul_comm j u
  have hexp : (j.choose 2 : ℝ) ≤ (u : ℝ) / 4 * (j : ℝ) := by
    have hR : (4 : ℝ) * (j.choose 2 : ℝ) ≤ (u : ℝ) * (j : ℝ) := by exact_mod_cast hnat
    linarith
  calc ((2 : ℝ) ^ (j.choose 2))
      = (2 : ℝ) ^ ((j.choose 2 : ℝ)) := (Real.rpow_natCast 2 (j.choose 2)).symm
    _ ≤ (2 : ℝ) ^ ((u : ℝ) / 4 * (j : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = ((2 : ℝ) ^ ((u : ℝ) / 4)) ^ ((j : ℝ)) :=
        Real.rpow_mul (by positivity) ((u : ℝ) / 4) (j : ℝ)
    _ = ((2 : ℝ) ^ ((u : ℝ) / 4)) ^ j := Real.rpow_natCast _ j

private theorem pair_small_overlap_term_le {n u j : ℕ}
    (hun : u < n) (hju : j ≤ u) (h2j : 2 * j ≤ u) :
    (n.choose u : ℝ) * (u.choose j : ℝ) * ((n - u).choose (u - j) : ℝ) *
        ((1 / 2 : ℝ) ^ (2 * u.choose 2 - j.choose 2)) ≤
      (mu n u) ^ 2 * ((pairKernelJ n u) ^ j / (j.factorial : ℝ)) := by
  have hsub_pos : 0 < ((n - u : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - u by omega)
  have hfac_pos : 0 < (j.factorial : ℝ) := by positivity
  have hchoose_le :
      (u.choose j : ℝ) * ((n - u).choose (u - j) : ℝ) ≤
        (n.choose u : ℝ) * ((u : ℝ) ^ 2 / ((n - u : ℕ) : ℝ)) ^ j / (j.factorial : ℝ) := by
    have hnatR :
        (j.factorial : ℝ) * ((u.choose j : ℝ) * ((n - u).choose (u - j) : ℝ)) *
            ((n - u : ℕ) : ℝ) ^ j ≤
          (n.choose u : ℝ) * (u : ℝ) ^ (2 * j) := by
      exact_mod_cast pair_choose_mul_pow_le (n := n) hju
    rw [div_pow, ← mul_div_assoc, div_div, le_div_iff₀ (mul_pos (pow_pos hsub_pos j) hfac_pos)]
    calc (u.choose j : ℝ) * ((n - u).choose (u - j) : ℝ) *
            (((n - u : ℕ) : ℝ) ^ j * (j.factorial : ℝ))
        = (j.factorial : ℝ) * ((u.choose j : ℝ) * ((n - u).choose (u - j) : ℝ)) *
            ((n - u : ℕ) : ℝ) ^ j := by ring
      _ ≤ (n.choose u : ℝ) * (u : ℝ) ^ (2 * j) := hnatR
      _ = (n.choose u : ℝ) * ((u : ℝ) ^ 2) ^ j := by rw [pow_mul]
  have h2pow_eq :
      ((1 / 2 : ℝ) ^ (2 * u.choose 2 - j.choose 2)) =
        (((2 : ℝ) ^ (u.choose 2))⁻¹) ^ 2 * (2 : ℝ) ^ (j.choose 2) := by
    have hjle : j.choose 2 ≤ 2 * u.choose 2 :=
      le_trans (Nat.choose_le_choose 2 hju) (by omega)
    have hsplit : 2 * u.choose 2 = (2 * u.choose 2 - j.choose 2) + j.choose 2 :=
      (Nat.sub_add_cancel hjle).symm
    calc ((1 / 2 : ℝ) ^ (2 * u.choose 2 - j.choose 2))
        = ((2 : ℝ)⁻¹) ^ (2 * u.choose 2 - j.choose 2) *
            (((2 : ℝ)⁻¹ * 2) ^ (j.choose 2)) := by
          rw [one_div, inv_mul_cancel₀ (by norm_num), one_pow, mul_one]
      _ = ((2 : ℝ)⁻¹) ^ ((2 * u.choose 2 - j.choose 2) + j.choose 2) *
            (2 : ℝ) ^ (j.choose 2) := by
          rw [mul_pow, pow_add]; ring
      _ = (((2 : ℝ) ^ (u.choose 2))⁻¹) ^ 2 * (2 : ℝ) ^ (j.choose 2) := by
          rw [← hsplit, Nat.mul_comm 2 (u.choose 2), pow_mul, inv_pow]
  have h2pow_le := two_pow_choose_two_le_quarter h2j
  rw [h2pow_eq]
  calc (n.choose u : ℝ) * (u.choose j : ℝ) * ((n - u).choose (u - j) : ℝ) *
          ((((2 : ℝ) ^ u.choose 2)⁻¹) ^ 2 * (2 : ℝ) ^ j.choose 2)
      = (n.choose u : ℝ) * (((2 : ℝ) ^ u.choose 2)⁻¹) ^ 2 *
          ((u.choose j : ℝ) * ((n - u).choose (u - j) : ℝ)) * (2 : ℝ) ^ j.choose 2 := by ring
    _ ≤ (n.choose u : ℝ) * (((2 : ℝ) ^ u.choose 2)⁻¹) ^ 2 *
          ((n.choose u : ℝ) * ((u : ℝ) ^ 2 / ((n - u : ℕ) : ℝ)) ^ j / (j.factorial : ℝ)) *
          ((2 : ℝ) ^ ((u : ℝ) / 4)) ^ j := by
        refine mul_le_mul ?_ h2pow_le (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hchoose_le (by positivity)
    _ = (mu n u) ^ 2 * ((pairKernelJ n u) ^ j / (j.factorial : ℝ)) := by
        unfold mu pairKernelJ
        have hpow_j :
            ((u : ℝ) ^ 2 * (2 : ℝ) ^ ((u : ℝ) / 4) / ((n - u : ℕ) : ℝ)) ^ j =
              ((u : ℝ) ^ 2 / ((n - u : ℕ) : ℝ)) ^ j * ((2 : ℝ) ^ ((u : ℝ) / 4)) ^ j := by
          rw [mul_div_right_comm, mul_pow]
        rw [hpow_j]
        ring

private theorem choose_le_pow_div_factorial (m r : ℕ) :
    (m.choose r : ℝ) ≤ (m : ℝ) ^ r / (r.factorial : ℝ) := by
  have hpos : 0 < (r.factorial : ℝ) := by positivity
  rw [le_div_iff₀ hpos, mul_comm]
  have hnat : r.factorial * m.choose r ≤ m ^ r := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow m r
  exact_mod_cast hnat

private theorem pair_large_overlap_term_le {n u j : ℕ}
    (hju : j < u) (h2j : u < 2 * j) :
    (n.choose u : ℝ) * (u.choose j : ℝ) * ((n - u).choose (u - j) : ℝ) *
        ((1 / 2 : ℝ) ^ (2 * u.choose 2 - j.choose 2)) ≤
      mu n u * ((pairKernelK n u) ^ (u - j) / ((u - j).factorial : ℝ)) := by
  set r : ℕ := u - j
  have hr_pos : 1 ≤ r := by omega
  have hru : r ≤ u := Nat.sub_le u j
  have h2r : 2 * r ≤ u := by omega
  have hj_eq : j = u - r := by omega
  have hsymm : u.choose j = u.choose r := by
    rw [hj_eq]
    exact Nat.choose_symm hru
  have h2pow_split :
      ((1 / 2 : ℝ) ^ (2 * u.choose 2 - j.choose 2)) =
        ((2 : ℝ) ^ (u.choose 2))⁻¹ * (2 : ℝ) ^ (-((u.choose 2 - j.choose 2 : ℕ) : ℝ)) := by
    have hjle : j.choose 2 ≤ u.choose 2 := Nat.choose_le_choose 2 hju.le
    have hsplit : 2 * u.choose 2 - j.choose 2 = u.choose 2 + (u.choose 2 - j.choose 2) := by omega
    rw [hsplit, pow_add, one_div, inv_pow, Real.rpow_neg (by positivity),
      Real.rpow_natCast, inv_pow]
  have hexp_le :
      -((u.choose 2 - j.choose 2 : ℕ) : ℝ) ≤
        (r : ℝ) * (1 / 2 - 3 * (u : ℝ) / 4) := by
    have hjle : j.choose 2 ≤ u.choose 2 := Nat.choose_le_choose 2 hju.le
    rw [Nat.cast_sub hjle, hj_eq]
    have hcu : (u.choose 2 : ℝ) = (u : ℝ) * ((u : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ u
    have hcj : ((u - r).choose 2 : ℝ) =
        ((u : ℝ) - (r : ℝ)) * (((u : ℝ) - (r : ℝ)) - 1) / 2 := by
      rw [Nat.cast_choose_two ℝ (u - r), Nat.cast_sub hru]
    rw [hcu, hcj]
    have hrR : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    have h2rR : 2 * (r : ℝ) ≤ (u : ℝ) := by exact_mod_cast h2r
    have hdiff :
        0 ≤ (r : ℝ) * ((u : ℝ) - 2 * (r : ℝ)) :=
      mul_nonneg hrR (by linarith)
    linarith
  have hrpow_le :
      (2 : ℝ) ^ (-((u.choose 2 - j.choose 2 : ℕ) : ℝ)) ≤
        (Real.sqrt 2 * (2 : ℝ) ^ (-3 * (u : ℝ) / 4)) ^ r := by
    have hsqrt : Real.sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 2
    calc (2 : ℝ) ^ (-((u.choose 2 - j.choose 2 : ℕ) : ℝ))
        ≤ (2 : ℝ) ^ ((r : ℝ) * (1 / 2 - 3 * (u : ℝ) / 4)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
      _ = ((2 : ℝ) ^ (1 / 2 - 3 * (u : ℝ) / 4)) ^ (r : ℝ) := by
          rw [mul_comm, Real.rpow_mul (by positivity)]
      _ = ((2 : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (-3 * (u : ℝ) / 4)) ^ r := by
          rw [Real.rpow_natCast, show (1 / 2 : ℝ) - 3 * (u : ℝ) / 4 =
            1 / 2 + (-3 * (u : ℝ) / 4) by ring, Real.rpow_add two_pos]
      _ = (Real.sqrt 2 * (2 : ℝ) ^ (-3 * (u : ℝ) / 4)) ^ r := by rw [hsqrt]
  have hchoose_u : (u.choose r : ℝ) ≤ (u : ℝ) ^ r / (r.factorial : ℝ) :=
    choose_le_pow_div_factorial u r
  have hchoose_n : ((n - u).choose r : ℝ) ≤ (n : ℝ) ^ r / (r.factorial : ℝ) := by
    calc ((n - u).choose r : ℝ)
        ≤ ((n - u : ℕ) : ℝ) ^ r / (r.factorial : ℝ) := choose_le_pow_div_factorial (n - u) r
      _ ≤ (n : ℝ) ^ r / (r.factorial : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.sub_le n u) r
  have hfac_ge1 : (1 : ℝ) ≤ (r.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos r
  have hfac_sq : (r.factorial : ℝ) ≤ (r.factorial : ℝ) * (r.factorial : ℝ) :=
    le_mul_of_one_le_left (by positivity) hfac_ge1
  rw [hsymm, h2pow_split]
  calc (n.choose u : ℝ) * (u.choose r : ℝ) * ((n - u).choose r : ℝ) *
          (((2 : ℝ) ^ u.choose 2)⁻¹ * (2 : ℝ) ^ (-((u.choose 2 - j.choose 2 : ℕ) : ℝ)))
      = mu n u * (((u.choose r : ℝ) * ((n - u).choose r : ℝ)) *
          (2 : ℝ) ^ (-((u.choose 2 - j.choose 2 : ℕ) : ℝ))) := by
        unfold mu; ring
    _ ≤ mu n u * ((((u : ℝ) ^ r / (r.factorial : ℝ)) * ((n : ℝ) ^ r / (r.factorial : ℝ))) *
          (Real.sqrt 2 * (2 : ℝ) ^ (-3 * (u : ℝ) / 4)) ^ r) := by
        refine mul_le_mul_of_nonneg_left ?_ (mu_nonneg n u)
        exact mul_le_mul (mul_le_mul hchoose_u hchoose_n (by positivity) (by positivity))
          hrpow_le (by positivity) (by positivity)
    _ = mu n u * ((pairKernelK n u) ^ r / ((r.factorial : ℝ) * (r.factorial : ℝ))) := by
        unfold pairKernelK
        rw [div_mul_div_comm, div_mul_eq_mul_div]
        congr 2
        rw [mul_pow, mul_pow, mul_pow]
        ring
    _ ≤ mu n u * ((pairKernelK n u) ^ r / (r.factorial : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mu_nonneg n u)
        exact div_le_div_of_nonneg_left (pow_nonneg (pairKernelK_nonneg n u) r)
          (by positivity) hfac_sq

/-- **Lemma 1.3 (`lem:independent-pair-tail`):** for `1 ≤ u < n`,
`E[X_u(G_n)(X_u(G_n) - 1)] ≤ μ_u² exp(J_u) + μ_u (exp(K_u) - 1)`. -/
theorem integral_independentSetCount_mul_sub_one_le {n u : ℕ}
    (hu : 1 ≤ u) (hun : u < n) :
    ∫ G : LabeledGraph n,
        (independentSetCount G u : ℝ) * ((independentSetCount G u : ℝ) - 1)
        ∂randomGraphMeasure n ≤
      (mu n u) ^ 2 * Real.exp (pairKernelJ n u) +
        mu n u * (Real.exp (pairKernelK n u) - 1) := by
  classical
  set P := (Finset.univ : Finset (Fin n)).powersetCard u
  have hint_eq :
      ∫ G : LabeledGraph n,
          (independentSetCount G u : ℝ) * ((independentSetCount G u : ℝ) - 1)
          ∂randomGraphMeasure n =
        ∑ U₁ ∈ P, ∑ U₂ ∈ P.erase U₁,
          ((1 / 2 : ℝ) ^ (2 * u.choose 2 - (U₁ ∩ U₂).card.choose 2)) := by
    simp_rw [independentSetCount_mul_sub_one_eq_sum]
    rw [MeasureTheory.integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
    refine Finset.sum_congr rfl fun U₁ hU₁ ↦ ?_
    rw [MeasureTheory.integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
    refine Finset.sum_congr rfl fun U₂ hU₂ ↦ ?_
    have hc₁ : U₁.card = u := (Finset.mem_powersetCard.mp hU₁).2
    have hc₂ : U₂.card = u := (Finset.mem_powersetCard.mp (Finset.mem_of_mem_erase hU₂)).2
    rw [integral_mul_independentIndicatorNat, hc₁, hc₂, two_mul]
  rw [hint_eq]
  have Dinner : ∀ U₁ ∈ P,
      ∑ U₂ ∈ P.erase U₁, ((1 / 2 : ℝ) ^ (2 * u.choose 2 - (U₁ ∩ U₂).card.choose 2)) ≤
        ∑ j ∈ Finset.range u,
          (u.choose j : ℝ) * ((n - u).choose (u - j) : ℝ) *
            ((1 / 2 : ℝ) ^ (2 * u.choose 2 - j.choose 2)) := by
    intro U₁ hU₁
    have hc₁ : U₁.card = u := (Finset.mem_powersetCard.mp hU₁).2
    have hmaps : ∀ U₂ ∈ P.erase U₁, (U₁ ∩ U₂).card ∈ Finset.range u := by
      intro U₂ hU₂
      obtain ⟨hne, hU₂P⟩ := Finset.mem_erase.mp hU₂
      have hc₂ : U₂.card = u := (Finset.mem_powersetCard.mp hU₂P).2
      rw [Finset.mem_range]
      have hle : (U₁ ∩ U₂).card ≤ u :=
        hc₁ ▸ Finset.card_le_card Finset.inter_subset_left
      rcases eq_or_lt_of_le hle with heq | hlt
      · exfalso
        have hsub₁ : U₁ ∩ U₂ = U₁ :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
        have hsub₂ : U₁ ∩ U₂ = U₂ :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
        exact hne (hsub₂.symm.trans hsub₁)
      · exact hlt
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    have hconst :
        ∑ U₂ ∈ (P.erase U₁).filter (fun U₂ ↦ (U₁ ∩ U₂).card = j),
            ((1 / 2 : ℝ) ^ (2 * u.choose 2 - (U₁ ∩ U₂).card.choose 2)) =
          (((P.erase U₁).filter (fun U₂ ↦ (U₁ ∩ U₂).card = j)).card : ℝ) *
            ((1 / 2 : ℝ) ^ (2 * u.choose 2 - j.choose 2)) := by
      calc _ = ∑ _U₂ ∈ (P.erase U₁).filter (fun U₂ ↦ (U₁ ∩ U₂).card = j),
              ((1 / 2 : ℝ) ^ (2 * u.choose 2 - j.choose 2)) := by
            refine Finset.sum_congr rfl fun U₂ hU₂ ↦ ?_
            rw [(Finset.mem_filter.mp hU₂).2]
        _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    have hcard :
        (((P.erase U₁).filter (fun U₂ ↦ (U₁ ∩ U₂).card = j)).card : ℝ) ≤
          (u.choose j : ℝ) * ((n - u).choose (u - j) : ℝ) := by
      exact_mod_cast card_filter_inter_eq_le hc₁
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  have hPcard : (P.card : ℝ) = (n.choose u : ℝ) := by
    simp [P, Finset.card_powersetCard]
  have htotal :
      (∑ U₁ ∈ P, ∑ U₂ ∈ P.erase U₁,
          ((1 / 2 : ℝ) ^ (2 * u.choose 2 - (U₁ ∩ U₂).card.choose 2))) ≤
        ∑ j ∈ Finset.range u,
          (n.choose u : ℝ) * (u.choose j : ℝ) * ((n - u).choose (u - j) : ℝ) *
            ((1 / 2 : ℝ) ^ (2 * u.choose 2 - j.choose 2)) := by
    calc _ ≤ ∑ _U₁ ∈ P, ∑ j ∈ Finset.range u,
            (u.choose j : ℝ) * ((n - u).choose (u - j) : ℝ) *
              ((1 / 2 : ℝ) ^ (2 * u.choose 2 - j.choose 2)) :=
          Finset.sum_le_sum Dinner
      _ = (n.choose u : ℝ) * ∑ j ∈ Finset.range u,
            (u.choose j : ℝ) * ((n - u).choose (u - j) : ℝ) *
              ((1 / 2 : ℝ) ^ (2 * u.choose 2 - j.choose 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hPcard]
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ ↦ by ring
  refine le_trans htotal ?_
  let term : ℕ → ℝ := fun j ↦
    (n.choose u : ℝ) * (u.choose j : ℝ) * ((n - u).choose (u - j) : ℝ) *
      ((1 / 2 : ℝ) ^ (2 * u.choose 2 - j.choose 2))
  have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.range u)
    (fun j ↦ 2 * j ≤ u) term).symm
  rw [hsplit]
  have hsmall :
      ∑ j ∈ (Finset.range u).filter (fun j ↦ 2 * j ≤ u), term j ≤
        (mu n u) ^ 2 * Real.exp (pairKernelJ n u) := by
    calc ∑ j ∈ (Finset.range u).filter (fun j ↦ 2 * j ≤ u), term j
        ≤ ∑ j ∈ (Finset.range u).filter (fun j ↦ 2 * j ≤ u),
            (mu n u) ^ 2 * ((pairKernelJ n u) ^ j / (j.factorial : ℝ)) := by
          refine Finset.sum_le_sum fun j hj ↦ ?_
          rw [Finset.mem_filter, Finset.mem_range] at hj
          exact pair_small_overlap_term_le hun hj.1.le hj.2
      _ ≤ ∑ j ∈ Finset.range u,
            (mu n u) ^ 2 * ((pairKernelJ n u) ^ j / (j.factorial : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ ↦ ?_
          exact mul_nonneg (sq_nonneg _) (div_nonneg (pow_nonneg (pairKernelJ_nonneg n u) j)
            (by positivity))
      _ = (mu n u) ^ 2 * ∑ j ∈ Finset.range u, (pairKernelJ n u) ^ j / (j.factorial : ℝ) := by
          rw [← Finset.mul_sum]
      _ ≤ (mu n u) ^ 2 * Real.exp (pairKernelJ n u) :=
          mul_le_mul_of_nonneg_left (sum_pow_div_factorial_le_exp (pairKernelJ_nonneg n u) u)
            (sq_nonneg _)
  have hlarge :
      ∑ j ∈ (Finset.range u).filter (fun j ↦ ¬ 2 * j ≤ u), term j ≤
        mu n u * (Real.exp (pairKernelK n u) - 1) := by
    let gK : ℕ → ℝ := fun r ↦ mu n u * ((pairKernelK n u) ^ r / (r.factorial : ℝ))
    have hstep1 :
        ∑ j ∈ (Finset.range u).filter (fun j ↦ ¬ 2 * j ≤ u), term j ≤
          ∑ j ∈ (Finset.range u).filter (fun j ↦ ¬ 2 * j ≤ u), gK (u - j) := by
      refine Finset.sum_le_sum fun j hj ↦ ?_
      rw [Finset.mem_filter, Finset.mem_range] at hj
      exact pair_large_overlap_term_le hj.1 (not_le.mp hj.2)
    have hinj : Set.InjOn (fun j : ℕ ↦ u - j)
        (((Finset.range u).filter (fun j ↦ ¬ 2 * j ≤ u)) : Set ℕ) := by
      intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
      dsimp only at hab
      omega
    have himg_sub :
        ((Finset.range u).filter (fun j ↦ ¬ 2 * j ≤ u)).image (fun j ↦ u - j) ⊆
          (Finset.range u).erase 0 := by
      intro r hr
      rcases Finset.mem_image.mp hr with ⟨j, hj, rfl⟩
      rw [Finset.mem_filter, Finset.mem_range] at hj
      rw [Finset.mem_erase, Finset.mem_range]
      have : u < 2 * j := not_le.mp hj.2
      omega
    have hstep2 :
        ∑ j ∈ (Finset.range u).filter (fun j ↦ ¬ 2 * j ≤ u), gK (u - j) ≤
          ∑ r ∈ (Finset.range u).erase 0, gK r := by
      rw [← Finset.sum_image hinj]
      refine Finset.sum_le_sum_of_subset_of_nonneg himg_sub fun r _ _ ↦ ?_
      exact mul_nonneg (mu_nonneg n u)
        (div_nonneg (pow_nonneg (pairKernelK_nonneg n u) r) (by positivity))
    have h0mem : (0 : ℕ) ∈ Finset.range u := Finset.mem_range.mpr hu
    have herase :
        ∑ r ∈ (Finset.range u).erase 0, (pairKernelK n u) ^ r / (r.factorial : ℝ) =
          (∑ r ∈ Finset.range u, (pairKernelK n u) ^ r / (r.factorial : ℝ)) - 1 := by
      have hadd := Finset.add_sum_erase (Finset.range u)
        (fun r ↦ (pairKernelK n u) ^ r / (r.factorial : ℝ)) h0mem
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hadd
      linarith
    calc ∑ j ∈ (Finset.range u).filter (fun j ↦ ¬ 2 * j ≤ u), term j
        ≤ ∑ r ∈ (Finset.range u).erase 0, gK r := le_trans hstep1 hstep2
      _ = mu n u * ∑ r ∈ (Finset.range u).erase 0,
            (pairKernelK n u) ^ r / (r.factorial : ℝ) := by
          dsimp [gK]; rw [← Finset.mul_sum]
      _ = mu n u *
            ((∑ r ∈ Finset.range u, (pairKernelK n u) ^ r / (r.factorial : ℝ)) - 1) := by
          rw [herase]
      _ ≤ mu n u * (Real.exp (pairKernelK n u) - 1) :=
          mul_le_mul_of_nonneg_left
            (sub_le_sub_right (sum_pow_div_factorial_le_exp (pairKernelK_nonneg n u) u) 1)
            (mu_nonneg n u)
  exact add_le_add hsmall hlarge

/-- **Markov pair tail (`lem:independent-pair-tail` / `prop:lower-tails`):**
for `1 ≤ u < n`,
`P(X_u(G_n) ≥ 2) ≤ 1/2 · (μ_u² exp(J_u) + μ_u (exp(K_u) - 1))`. -/
theorem randomGraph_independentSetCount_ge_two_le {n u : ℕ}
    (hu : 1 ≤ u) (hun : u < n) :
    (randomGraphMeasure n).real {G : LabeledGraph n | 2 ≤ independentSetCount G u} ≤
      1 / 2 * ((mu n u) ^ 2 * Real.exp (pairKernelJ n u) +
        mu n u * (Real.exp (pairKernelK n u) - 1)) := by
  let E : Set (LabeledGraph n) := {G | 2 ≤ independentSetCount G u}
  have hpoint : ∀ G : LabeledGraph n,
      E.indicator (fun _ ↦ (2 : ℝ)) G ≤
        (independentSetCount G u : ℝ) * ((independentSetCount G u : ℝ) - 1) := by
    intro G
    by_cases hG : G ∈ E
    · rw [Set.indicator_of_mem hG]
      have hx : (2 : ℝ) ≤ (independentSetCount G u : ℝ) := by exact_mod_cast hG
      nlinarith
    · rw [Set.indicator_of_notMem hG]
      rcases Nat.eq_zero_or_pos (independentSetCount G u) with h0 | hpos
      · simp [h0]
      · have h1 : (1 : ℝ) ≤ (independentSetCount G u : ℝ) := by exact_mod_cast hpos
        nlinarith
  have hint :
      2 * (randomGraphMeasure n).real E ≤
        ∫ G : LabeledGraph n,
          (independentSetCount G u : ℝ) * ((independentSetCount G u : ℝ) - 1)
          ∂randomGraphMeasure n := by
    have hmono := integral_mono (μ := randomGraphMeasure n)
      (Integrable.of_finite) (Integrable.of_finite) hpoint
    rw [integral_indicator_const (μ := randomGraphMeasure n) (2 : ℝ)
      (Set.toFinite E).measurableSet, smul_eq_mul, mul_comm] at hmono
    exact hmono
  linarith [integral_independentSetCount_mul_sub_one_le hu hun]

private theorem randomGraph_measureReal_complGraph_le {n : ℕ}
    (P : LabeledGraph n → Prop) :
    (randomGraphMeasure n).real {G : LabeledGraph n | P Gᶜ} ≤
      (randomGraphMeasure n).real {G : LabeledGraph n | P G} := by
  have h := randomGraphMeasure_image_le_of_involutive (fun G : LabeledGraph n ↦ Gᶜ)
    compl_involutive (S := {G | P Gᶜ}) (T := {G | P G})
    (fun G hG ↦ by simpa only [Set.mem_setOf_eq, compl_compl] using hG)
  exact ENNReal.toReal_mono (measure_ne_top _ _) h

/-- **Proposition 4.1 (`prop:lower-tails`, exceptional-event probability bound):**
for `2 ≤ n`, `1 ≤ u < n`, `1 ≤ u_m`, and `d = ⌈μ_{u_m} + √n (log n)²⌉` (`= d_{n,m}`),
the four-event exceptional union
`{X_u(G) ≥ 2} ∪ {X_u(Gᶜ) ≥ 2} ∪ {D_{u_m}(G) > d} ∪ {D_{u_m}(Gᶜ) > d}`
has `G(n, 1/2)` probability at most `𝓔_u = lowerTailExceptionalBound n u`. -/
theorem randomGraph_lowerTailExceptional_le {n u u_m : ℕ}
    (hn : 2 ≤ n) (hu : 1 ≤ u) (hun : u < n) (hum : 1 ≤ u_m) :
    (randomGraphMeasure n).real
        ({G : LabeledGraph n | 2 ≤ independentSetCount G u} ∪
          {G : LabeledGraph n | 2 ≤ independentSetCount Gᶜ u} ∪
          {G : LabeledGraph n |
            Nat.ceil (mu n u_m + Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 2) <
              maxDisjointIndepGe G u_m} ∪
          {G : LabeledGraph n |
            Nat.ceil (mu n u_m + Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 2) <
              maxDisjointIndepGe Gᶜ u_m}) ≤
      lowerTailExceptionalBound n u := by
  set t : ℝ := Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 2
  set d : ℕ := Nat.ceil (mu n u_m + t)
  have ht_nn : 0 ≤ t := by dsimp [t]; positivity
  have hE1 := randomGraph_independentSetCount_ge_two_le hu hun
  have hE2 :
      (randomGraphMeasure n).real {G : LabeledGraph n | 2 ≤ independentSetCount Gᶜ u} ≤
        1 / 2 * ((mu n u) ^ 2 * Real.exp (pairKernelJ n u) +
          mu n u * (Real.exp (pairKernelK n u) - 1)) :=
    le_trans (randomGraph_measureReal_complGraph_le (fun H ↦ 2 ≤ independentSetCount H u)) hE1
  have hexp_t :
      Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) ≤
        Real.exp (-2 * (Real.log (n : ℝ)) ^ 4) := by
    apply Real.exp_le_exp.mpr
    have hn1_pos : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
    have hn1_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    have ht_sq : t ^ 2 = (n : ℝ) * (Real.log (n : ℝ)) ^ 4 := by
      dsimp [t]
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), ← pow_mul]
    rw [ht_sq, div_le_iff₀ hn1_pos]
    have hlog4_nn : 0 ≤ (Real.log (n : ℝ)) ^ 4 := by positivity
    calc -2 * ((n : ℝ) * (Real.log (n : ℝ)) ^ 4)
        ≤ -2 * (((n - 1 : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 4) := by
          have := mul_le_mul_of_nonneg_right hn1_le hlog4_nn
          linarith
      _ = -2 * (Real.log (n : ℝ)) ^ 4 * ((n - 1 : ℕ) : ℝ) := by ring
  have hE3 :
      (randomGraphMeasure n).real {G : LabeledGraph n | d < maxDisjointIndepGe G u_m} ≤
        Real.exp (-2 * (Real.log (n : ℝ)) ^ 4) := by
    have hsub :
        {G : LabeledGraph n | d < maxDisjointIndepGe G u_m} ⊆
          {G : LabeledGraph n | mu n u_m + t < (maxDisjointIndepGe G u_m : ℝ)} := by
      intro G hG
      simp only [Set.mem_setOf_eq] at hG ⊢
      have hdR : (d : ℝ) < (maxDisjointIndepGe G u_m : ℝ) := by exact_mod_cast hG
      exact lt_of_le_of_lt (Nat.le_ceil (mu n u_m + t)) hdR
    exact le_trans (measureReal_mono hsub)
      (le_trans (randomGraph_maxDisjointIndepGe_gt_mu_add_le_exp hn hum ht_nn) hexp_t)
  have hE4 :
      (randomGraphMeasure n).real {G : LabeledGraph n | d < maxDisjointIndepGe Gᶜ u_m} ≤
        Real.exp (-2 * (Real.log (n : ℝ)) ^ 4) :=
    le_trans (randomGraph_measureReal_complGraph_le (fun H ↦ d < maxDisjointIndepGe H u_m)) hE3
  have hu1 := measureReal_union_le (μ := randomGraphMeasure n)
    ({G : LabeledGraph n | 2 ≤ independentSetCount G u} ∪
      {G : LabeledGraph n | 2 ≤ independentSetCount Gᶜ u} ∪
      {G : LabeledGraph n | d < maxDisjointIndepGe G u_m})
    {G : LabeledGraph n | d < maxDisjointIndepGe Gᶜ u_m}
  have hu2 := measureReal_union_le (μ := randomGraphMeasure n)
    ({G : LabeledGraph n | 2 ≤ independentSetCount G u} ∪
      {G : LabeledGraph n | 2 ≤ independentSetCount Gᶜ u})
    {G : LabeledGraph n | d < maxDisjointIndepGe G u_m}
  have hu3 := measureReal_union_le (μ := randomGraphMeasure n)
    {G : LabeledGraph n | 2 ≤ independentSetCount G u}
    {G : LabeledGraph n | 2 ≤ independentSetCount Gᶜ u}
  unfold lowerTailExceptionalBound
  linarith

/-! ## 2. Lemma 2.1 (`lem:phase-expansion`, `(2.2)`–`(2.4)`) & summability of `𝓔_{α+2}` -/

/-- Manuscript exponent `β = 2 / q + 1 / 2` from Section 9 (`sec:final-assembly`). -/
def phaseTailBeta : ℝ := 2 / q + 1 / 2

private theorem exists_eventually_abs_log_mu_phaseNat_sub_le :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ n : ℕ in atTop,
      |Real.log (mu n (phaseNat n)) -
        (phaseDelta n * logOrder n + (2 / q - 1 / 2 - phaseDelta n) * logLogOrder n)| ≤ C₀ := by
  obtain ⟨M, hM⟩ := exists_phaseK_abs_bound
  have hRes : ∀ᶠ n : ℕ in atTop, |phaseExpansionResidual n| < 1 := by
    simpa [Real.dist_eq] using
      (Metric.tendsto_nhds.mp phaseExpansionResidual_tendsto_zero) 1 one_pos
  have hMnn : 0 ≤ M :=
    le_trans (abs_nonneg _) (hM 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨M + 1, by linarith, ?_⟩
  filter_upwards [hRes] with n hnRes
  have hK : |phaseK (phaseDelta n)| ≤ M :=
    hM _ ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩
  have heq :
      Real.log (mu n (phaseNat n)) -
          (phaseDelta n * logOrder n + (2 / q - 1 / 2 - phaseDelta n) * logLogOrder n) =
        phaseExpansionResidual n + phaseK (phaseDelta n) := by
    unfold phaseExpansionResidual phaseExpansionMain
    ring
  rw [heq]
  exact le_trans (abs_add_le _ _) (by linarith)

private theorem eventually_logLogOrder_le_logOrder_hp :
    ∀ᶠ n : ℕ in atTop, logLogOrder n ≤ logOrder n := by
  have hb := logLogOrder_isLittleO_logOrder.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hpos : ∀ᶠ n : ℕ in atTop, 0 ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop 0)
  filter_upwards [hb, hpos] with n hbn hposn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hposn] at hbn
  exact le_trans (le_abs_self _) (by linarith)

private theorem phaseNat_mul_q_eq {n : ℕ} (hn : PhaseDomain n) :
    (phaseNat n : ℝ) * q =
      2 * logOrder n - 2 * logLogOrder n + 2 * phaseC + (1 - phaseDelta n) * q := by
  rw [phaseNat_cast_eq_two_phaseS_div_q_add_phaseB hn]
  simp only [phaseS, phaseB]
  field_simp [q_ne_zero]

/-- **Lemma 2.1 (`lem:phase-expansion`, all six displays `(2.2)`–`(2.4)`):**
there exist absolute constants `C₂, c₂ > 0` such that, uniformly across all
induced phases `δ_n ∈ [0, 1)` for all sufficiently large `n`:
1. `|log μ_α - (δ_n L + (2/q - 1/2 - δ_n) ℓ)| ≤ C₂`,
2. `μ_{α+1} ≤ C₂ (log n)^(2/q - 1/2)`,
3. `|log μ_{α+2} - ((δ_n - 2) L + (2/q + 3/2 - δ_n) ℓ)| ≤ C₂`,
4. `μ_{α+2} ≤ exp(-L + C₂ ℓ)`,
5. `c₂ n^(1 + δ_n) (log n)^(2/q - 3/2 - δ_n) ≤ μ_{α-1}`,
6. `c₂ n^(2 + δ_n) (log n)^(2/q - 5/2 - δ_n) ≤ μ_{α-2}`. -/
theorem exists_uniform_phaseExpansion_and_adjacent_bounds :
    ∃ C₂ c₂ : ℝ, 0 < C₂ ∧ 0 < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      |Real.log (mu n (phaseNat n)) -
          (phaseDelta n * logOrder n + (2 / q - 1 / 2 - phaseDelta n) * logLogOrder n)| ≤ C₂ ∧
      mu n (phaseNat n + 1) ≤ C₂ * (logOrder n) ^ (2 / q - 1 / 2 : ℝ) ∧
      |Real.log (mu n (phaseNat n + 2)) -
          ((phaseDelta n - 2) * logOrder n +
            (2 / q + 3 / 2 - phaseDelta n) * logLogOrder n)| ≤ C₂ ∧
      mu n (phaseNat n + 2) ≤ Real.exp (-logOrder n + C₂ * logLogOrder n) ∧
      c₂ * (n : ℝ) ^ (1 + phaseDelta n) *
          (logOrder n) ^ (2 / q - 3 / 2 - phaseDelta n) ≤ mu n (phaseNat n - 1) ∧
      c₂ * (n : ℝ) ^ (2 + phaseDelta n) *
          (logOrder n) ^ (2 / q - 5 / 2 - phaseDelta n) ≤ mu n (phaseNat n - 2) := by
  obtain ⟨C₀, hC₀_pos, hBase⟩ := exists_eventually_abs_log_mu_phaseNat_sub_le
  have h2mul_add2 : ∀ᶠ n : ℕ in atTop, 2 * (phaseNat n + 2) ≤ n := by
    have hsmall : (fun n : ℕ ↦ (2 * ((phaseNat n : ℝ) + 2))) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ)) := by
      have h1 := phaseNat_isTheta_logOrder.1.trans_isLittleO logOrder_isLittleO_natCast
      have h2 : (fun _n : ℕ ↦ (2 : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
        simpa only [Function.comp_def, id_eq] using
          (isLittleO_const_id_atTop (2 : ℝ)).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
      exact (h1.add h2).const_mul_left 2
    filter_upwards [hsmall.bound (by norm_num : (0 : ℝ) < 1)] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (Nat.cast_nonneg n), one_mul] at hn
    have hnNat : (2 * (phaseNat n + 2) : ℕ) ≤ n := by
      exact_mod_cast (show ((2 * (phaseNat n + 2) : ℕ) : ℝ) ≤ (n : ℝ) by push_cast; linarith)
    exact hnNat
  have hL_ge2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop 2)
  have hll_ge1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually (eventually_ge_atTop 1)
  let C_add2 : ℝ := C₀ + 2 * q + 2 * Real.log 5 + 4 * |phaseC| + 3 * q
  let C_up1 : ℝ := Real.exp (C₀ + 2 * |phaseC| + q)
  let C₂ : ℝ := max (max C_add2 C_up1) (2 / q + 1 / 2 + C_add2)
  let D₁ : ℝ := 2 * phaseC - q - C₀
  let D₂ : ℝ := 4 * phaseC - 4 * q - C₀
  let c₂ : ℝ := min (Real.exp D₁) (Real.exp D₂)
  have hC_add2_pos : 0 < C_add2 := by
    dsimp [C_add2]
    have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
    have := q_pos
    have := abs_nonneg phaseC
    linarith
  have hC₂_pos : 0 < C₂ := lt_of_lt_of_le hC_add2_pos
    (le_trans (le_max_left _ _) (le_max_left _ _))
  have hc₂_pos : 0 < c₂ := lt_min (Real.exp_pos D₁) (Real.exp_pos D₂)
  refine ⟨C₂, c₂, hC₂_pos, hc₂_pos, ?_⟩
  filter_upwards [hBase, eventually_phaseDomain,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    h2mul_add2, hL_ge2, hll_ge1, eventually_logLogOrder_le_logOrder_hp] with
    n hBasen hnDom hPhBnd h2add2 hL2 hll1 hllLeL
  set a : ℕ := phaseNat n
  have hLpos : 0 < logOrder n := lt_of_lt_of_le (by norm_num) hL2
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by have := hnDom.1; omega)
  have ha_ge2 : 2 ≤ a := by
    have : (2 : ℝ) ≤ (a : ℝ) := le_trans hL2 hPhBnd.1
    exact_mod_cast this
  have ha_add2_le : a + 2 ≤ n := by omega
  have ha_add1_le : a + 1 ≤ n := by omega
  have ha_le : a ≤ n := by omega
  have hd0 : 0 ≤ phaseDelta n := phaseDelta_nonneg n
  have hd1 : phaseDelta n < 1 := phaseDelta_lt_one n
  have haq := phaseNat_mul_q_eq hnDom
  have habsC : -|phaseC| ≤ phaseC ∧ phaseC ≤ |phaseC| := abs_le.mp (le_refl |phaseC|)
  obtain ⟨hBase_lo, hBase_hi⟩ := abs_le.mp hBasen
  -- Claim 1: |log μ_α - main| ≤ C₂
  have hClaim1 :
      |Real.log (mu n a) -
        (phaseDelta n * logOrder n + (2 / q - 1 / 2 - phaseDelta n) * logLogOrder n)| ≤ C₂ := by
    have hle : C₀ ≤ C₂ := by
      refine le_trans ?_ (le_trans (le_max_left C_add2 C_up1) (le_max_left _ _))
      dsimp [C_add2]
      have := q_pos
      have : 0 < Real.log 5 := Real.log_pos (by norm_num)
      have := abs_nonneg phaseC
      linarith
    exact le_trans hBasen hle
  -- Bounds on log(n - a), log(n - (a + 1)), log(a + 1), log(a + 2)
  have hlog_na_hi : Real.log ((n - a : ℕ) : ℝ) ≤ logOrder n :=
    Real.log_le_log (by exact_mod_cast (show 0 < n - a by omega))
      (by exact_mod_cast Nat.sub_le n a)
  have hlog_na_lo : logOrder n - q ≤ Real.log ((n - a : ℕ) : ℝ) := by
    have hhalf : (n : ℝ) / 2 ≤ ((n - a : ℕ) : ℝ) := by
      rw [Nat.cast_sub ha_le]
      have : 2 * (a : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 2 * a ≤ n by omega)
      linarith
    have hlog_half : Real.log ((n : ℝ) / 2) = logOrder n - q := by
      rw [Real.log_div hn_pos.ne' (by norm_num)]; rfl
    rw [← hlog_half]
    exact Real.log_le_log (half_pos hn_pos) hhalf
  have hlog_na1_hi : Real.log ((n - (a + 1) : ℕ) : ℝ) ≤ logOrder n :=
    Real.log_le_log (by exact_mod_cast (show 0 < n - (a + 1) by omega))
      (by exact_mod_cast Nat.sub_le n (a + 1))
  have hlog_na1_lo : logOrder n - q ≤ Real.log ((n - (a + 1) : ℕ) : ℝ) := by
    have hhalf : (n : ℝ) / 2 ≤ ((n - (a + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub ha_add1_le]
      have : 2 * ((a + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (show 2 * (a + 1) ≤ n by omega)
      push_cast at this ⊢
      linarith
    have hlog_half : Real.log ((n : ℝ) / 2) = logOrder n - q := by
      rw [Real.log_div hn_pos.ne' (by norm_num)]; rfl
    rw [← hlog_half]
    exact Real.log_le_log (half_pos hn_pos) hhalf
  have hlog_a1_lo : logLogOrder n ≤ Real.log ((a + 1 : ℕ) : ℝ) :=
    Real.log_le_log hLpos (le_trans hPhBnd.1 (by exact_mod_cast Nat.le_succ a))
  have hlog_a1_hi : Real.log ((a + 1 : ℕ) : ℝ) ≤ logLogOrder n + Real.log 5 := by
    have hle5 : ((a + 1 : ℕ) : ℝ) ≤ 5 * logOrder n := by
      push_cast; linarith [hPhBnd.2, hL2]
    have h5 : Real.log (5 * logOrder n) = logLogOrder n + Real.log 5 := by
      rw [Real.log_mul (by norm_num) hLpos.ne', add_comm]; rfl
    rw [← h5]
    exact Real.log_le_log (by positivity) hle5
  have hlog_a2_lo : logLogOrder n ≤ Real.log ((a + 2 : ℕ) : ℝ) :=
    Real.log_le_log hLpos (le_trans hPhBnd.1 (by exact_mod_cast Nat.le_add_right a 2))
  have hlog_a2_hi : Real.log ((a + 2 : ℕ) : ℝ) ≤ logLogOrder n + Real.log 5 := by
    have hle5 : ((a + 2 : ℕ) : ℝ) ≤ 5 * logOrder n := by
      push_cast; linarith [hPhBnd.2, hL2]
    have h5 : Real.log (5 * logOrder n) = logLogOrder n + Real.log 5 := by
      rw [Real.log_mul (by norm_num) hLpos.ne', add_comm]; rfl
    rw [← h5]
    exact Real.log_le_log (by positivity) hle5
  -- Claim 2: μ_{α+1} ≤ C₂ (log n)^(2/q - 1/2)
  have hStep1 := log_mu_succ_sub_log_mu ha_add1_le
  have hClaim2 : mu n (a + 1) ≤ C₂ * (logOrder n) ^ (2 / q - 1 / 2 : ℝ) := by
    have h1md_pos : 0 ≤ (1 - phaseDelta n) * (logOrder n - logLogOrder n) :=
      mul_nonneg (by linarith) (by linarith)
    have h1md_q : 0 ≤ (1 - phaseDelta n) * q := mul_nonneg (by linarith) q_pos.le
    have hlog_up1 :
        Real.log (mu n (a + 1)) ≤
          (2 / q - 1 / 2 : ℝ) * logLogOrder n + (C₀ + 2 * |phaseC| + q) := by
      linarith [hStep1, hBase_hi, hlog_na_hi, hlog_a1_lo, haq, habsC.1]
    calc mu n (a + 1)
        = Real.exp (Real.log (mu n (a + 1))) := (Real.exp_log (mu_pos ha_add1_le)).symm
      _ ≤ Real.exp ((2 / q - 1 / 2 : ℝ) * logLogOrder n + (C₀ + 2 * |phaseC| + q)) :=
          Real.exp_le_exp.mpr hlog_up1
      _ = C_up1 * (logOrder n) ^ (2 / q - 1 / 2 : ℝ) := by
          dsimp [C_up1, logLogOrder]
          rw [add_comm, Real.exp_add, mul_comm (2 / q - 1 / 2 : ℝ),
            ← Real.rpow_def_of_pos hLpos]
      _ ≤ C₂ * (logOrder n) ^ (2 / q - 1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right
            (le_trans (le_max_right C_add2 C_up1) (le_max_left _ _))
            (Real.rpow_nonneg hLpos.le _)
  -- Claim 3 & 4: |log μ_{α+2} - main₂| ≤ C₂ and μ_{α+2} ≤ exp(-L + C₂ ℓ)
  have hStep2 := log_mu_succ_sub_log_mu (s := a + 1) (by omega)
  have hDiff2 :
      |Real.log (mu n (a + 2)) -
        ((phaseDelta n - 2) * logOrder n +
          (2 / q + 3 / 2 - phaseDelta n) * logLogOrder n)| ≤ C_add2 := by
    have ha1_cast : ((a + 1 : ℕ) : ℝ) * q = (a : ℝ) * q + q := by push_cast; ring
    have h1md_q0 : 0 ≤ (1 - phaseDelta n) * q := mul_nonneg (by linarith) q_pos.le
    have h1md_q1 : (1 - phaseDelta n) * q ≤ q := by
      nlinarith [q_pos]
    rw [show a + 1 + 1 = a + 2 by rfl] at hStep2
    rw [abs_le]
    dsimp [C_add2]
    constructor
    · linarith [hStep1, hStep2, ha1_cast, hBase_lo, hlog_na_lo, hlog_na1_lo,
        hlog_a1_hi, hlog_a2_hi, haq, habsC.2, h1md_q1, q_pos]
    · linarith [hStep1, hStep2, ha1_cast, hBase_hi, hlog_na_hi, hlog_na1_hi,
        hlog_a1_lo, hlog_a2_lo, haq, habsC.1, h1md_q0, q_pos, Real.log_pos (by norm_num : (1 : ℝ) < 5)]
  have hClaim3 :
      |Real.log (mu n (a + 2)) -
        ((phaseDelta n - 2) * logOrder n +
          (2 / q + 3 / 2 - phaseDelta n) * logLogOrder n)| ≤ C₂ :=
    le_trans hDiff2 (le_trans (le_max_left _ _) (le_max_left _ _))
  have hClaim4 : mu n (a + 2) ≤ Real.exp (-logOrder n + C₂ * logLogOrder n) := by
    have hhi2 := (abs_le.mp hDiff2).2
    have h1md_L : 0 ≤ (1 - phaseDelta n) * (logOrder n - logLogOrder n) :=
      mul_nonneg (by linarith) (by linarith)
    have hC2_ge : 2 / q + 1 / 2 + C_add2 ≤ C₂ := le_max_right _ _
    have hC_mul : C_add2 ≤ C_add2 * logLogOrder n :=
      le_mul_of_one_le_right hC_add2_pos.le hll1
    have hlog_le : Real.log (mu n (a + 2)) ≤ -logOrder n + C₂ * logLogOrder n := by
      have hlin :
          (phaseDelta n - 2) * logOrder n +
              (2 / q + 3 / 2 - phaseDelta n) * logLogOrder n + C_add2 ≤
            -logOrder n + (2 / q + 1 / 2 + C_add2) * logLogOrder n := by
        linarith
      have hmono : (2 / q + 1 / 2 + C_add2) * logLogOrder n ≤ C₂ * logLogOrder n :=
        mul_le_mul_of_nonneg_right hC2_ge (by linarith)
      linarith
    calc mu n (a + 2)
        = Real.exp (Real.log (mu n (a + 2))) := (Real.exp_log (mu_pos ha_add2_le)).symm
      _ ≤ Real.exp (-logOrder n + C₂ * logLogOrder n) := Real.exp_le_exp.mpr hlog_le
  -- Claim 5 & 6: phase-retaining lower bounds on μ_{α-1} and μ_{α-2}
  have ha_pos : 0 < a := by omega
  have ha1_pos : 0 < a - 1 := by omega
  have ha1_le : a - 1 ≤ n := by omega
  have ha2_le : a - 2 ≤ n := by omega
  have hPred1 := log_mu_pred_sub_log_mu ha_pos ha_le
  have hPred2 := log_mu_pred_sub_log_mu ha1_pos ha1_le
  have hlog_a_lo : logLogOrder n ≤ Real.log (a : ℝ) :=
    Real.log_le_log hLpos hPhBnd.1
  have hlog_den1 : Real.log (((n - a : ℕ) + 1 : ℕ) : ℝ) ≤ logOrder n :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show n - a + 1 ≤ n by omega))
  have hlog_den2 : Real.log (((n - (a - 1) : ℕ) + 1 : ℕ) : ℝ) ≤ logOrder n :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show n - (a - 1) + 1 ≤ n by omega))
  have ha_pred_cast : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have ha_sub2_cast : ((a - 2 : ℕ) : ℝ) = (a : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hlog_apred_lo : logLogOrder n - q ≤ Real.log ((a - 1 : ℕ) : ℝ) := by
    have hhalf : logOrder n / 2 ≤ ((a - 1 : ℕ) : ℝ) := by
      rw [ha_pred_cast]; linarith [hPhBnd.1, hL2]
    have hlog_half : Real.log (logOrder n / 2) = logLogOrder n - q := by
      rw [Real.log_div hLpos.ne' (by norm_num)]; rfl
    rw [← hlog_half]
    exact Real.log_le_log (half_pos hLpos) hhalf
  have h1md_q0 : 0 ≤ (1 - phaseDelta n) * q := mul_nonneg (by linarith) q_pos.le
  have hlog_pred1_lo :
      (1 + phaseDelta n) * logOrder n +
          (2 / q - 3 / 2 - phaseDelta n) * logLogOrder n + D₁ ≤
        Real.log (mu n (a - 1)) := by
    have ha1q : ((a - 1 : ℕ) : ℝ) * q = (a : ℝ) * q - q := by rw [ha_pred_cast]; ring
    dsimp [D₁]
    linarith [hPred1, hBase_lo, hlog_a_lo, hlog_den1, ha1q, haq, h1md_q0]
  have hClaim5 :
      c₂ * (n : ℝ) ^ (1 + phaseDelta n) *
          (logOrder n) ^ (2 / q - 3 / 2 - phaseDelta n) ≤ mu n (a - 1) := by
    calc c₂ * (n : ℝ) ^ (1 + phaseDelta n) * (logOrder n) ^ (2 / q - 3 / 2 - phaseDelta n)
        ≤ Real.exp D₁ * (n : ℝ) ^ (1 + phaseDelta n) *
            (logOrder n) ^ (2 / q - 3 / 2 - phaseDelta n) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hn_pos.le _))
            (Real.rpow_nonneg hLpos.le _)
      _ = Real.exp ((1 + phaseDelta n) * logOrder n +
            (2 / q - 3 / 2 - phaseDelta n) * logLogOrder n + D₁) := by
          rw [Real.rpow_def_of_pos hn_pos, Real.rpow_def_of_pos hLpos]
          simp only [logOrder, logLogOrder]
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (Real.log (mu n (a - 1))) := Real.exp_le_exp.mpr hlog_pred1_lo
      _ = mu n (a - 1) := Real.exp_log (mu_pos ha1_le)
  have hSubSub : (a - 1 : ℕ) - 1 = a - 2 := by omega
  rw [hSubSub] at hPred2
  have hlog_pred2_lo :
      (2 + phaseDelta n) * logOrder n +
          (2 / q - 5 / 2 - phaseDelta n) * logLogOrder n + D₂ ≤
        Real.log (mu n (a - 2)) := by
    have ha2q : ((a - 2 : ℕ) : ℝ) * q = (a : ℝ) * q - 2 * q := by rw [ha_sub2_cast]; ring
    dsimp [D₂]
    linarith [hPred2, hlog_pred1_lo, hlog_apred_lo, hlog_den2, ha2q, haq, h1md_q0]
  have hClaim6 :
      c₂ * (n : ℝ) ^ (2 + phaseDelta n) *
          (logOrder n) ^ (2 / q - 5 / 2 - phaseDelta n) ≤ mu n (a - 2) := by
    calc c₂ * (n : ℝ) ^ (2 + phaseDelta n) * (logOrder n) ^ (2 / q - 5 / 2 - phaseDelta n)
        ≤ Real.exp D₂ * (n : ℝ) ^ (2 + phaseDelta n) *
            (logOrder n) ^ (2 / q - 5 / 2 - phaseDelta n) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hn_pos.le _))
            (Real.rpow_nonneg hLpos.le _)
      _ = Real.exp ((2 + phaseDelta n) * logOrder n +
            (2 / q - 5 / 2 - phaseDelta n) * logLogOrder n + D₂) := by
          rw [Real.rpow_def_of_pos hn_pos, Real.rpow_def_of_pos hLpos]
          simp only [logOrder, logLogOrder]
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (Real.log (mu n (a - 2))) := Real.exp_le_exp.mpr hlog_pred2_lo
      _ = mu n (a - 2) := Real.exp_log (mu_pos ha2_le)
  exact ⟨hClaim1, hClaim2, hClaim3, hClaim4, hClaim5, hClaim6⟩

private theorem exp_sub_one_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp x - 1 ≤ 2 * x := by
  have h1mx : 0 < 1 - x := by linarith
  have h1 : (1 - x) * Real.exp x ≤ 1 := by
    calc (1 - x) * Real.exp x
        ≤ Real.exp (-x) * Real.exp x :=
          mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (-x)]) (Real.exp_pos x).le
      _ = 1 := by rw [← Real.exp_add]; norm_num
  have h2 : Real.exp x ≤ 1 / (1 - x) := (le_div_iff₀ h1mx).mpr (by linarith)
  have h3 : 1 / (1 - x) - 1 ≤ 2 * x := by
    rw [div_sub_one h1mx.ne', div_le_iff₀ h1mx]
    nlinarith
  linarith

private theorem log_rpow_isLittleO_rpow_pos (γ ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ γ) =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ ε) := by
  let m : ℕ := Nat.ceil |γ| + 1
  have hm_pos : 0 < (m : ℝ) := by positivity
  have h1 : (fun x : ℝ ↦ Real.log x) =o[atTop] (fun x : ℝ ↦ x ^ (ε / (m : ℝ))) :=
    isLittleO_log_rpow_atTop (div_pos hε hm_pos)
  have h1n : (fun n : ℕ ↦ Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (ε / (m : ℝ))) :=
    h1.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  refine isLittleO_iff.mpr fun c hc ↦ ?_
  have hc_pow : 0 < c ^ (1 / (m : ℝ)) := Real.rpow_pos_of_pos hc _
  have hb_c := h1n.bound hc_pow
  have hL1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hb_c, hL1, eventually_gt_atTop 0] with n hbn hLn hn0
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hγ_le_m : γ ≤ (m : ℝ) := by
    dsimp [m]
    have : γ ≤ |γ| := le_abs_self γ
    have hceil : |γ| ≤ (Nat.ceil |γ| : ℝ) := Nat.le_ceil |γ|
    push_cast
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by linarith) γ),
    abs_of_nonneg (Real.rpow_nonneg hn_pos.le ε)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
    abs_of_nonneg (Real.rpow_nonneg hn_pos.le _)] at hbn
  calc (Real.log (n : ℝ)) ^ γ
      ≤ (Real.log (n : ℝ)) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hLn hγ_le_m
    _ = (Real.log (n : ℝ)) ^ m := Real.rpow_natCast _ m
    _ ≤ (c ^ (1 / (m : ℝ)) * (n : ℝ) ^ (ε / (m : ℝ))) ^ m :=
        pow_le_pow_left₀ (by linarith) hbn m
    _ = (c ^ (1 / (m : ℝ))) ^ (m : ℝ) * ((n : ℝ) ^ (ε / (m : ℝ))) ^ (m : ℝ) := by
        rw [mul_pow, Real.rpow_natCast, Real.rpow_natCast]
    _ = c * (n : ℝ) ^ ε := by
        rw [← Real.rpow_mul hc.le, ← Real.rpow_mul hn_pos.le,
          one_div_mul_cancel hm_pos.ne', div_mul_cancel₀ _ hm_pos.ne', Real.rpow_one]

private theorem eventually_mu_phaseNat_add_two_le_polylog :
    ∃ Cμ : ℝ, 0 < Cμ ∧ ∀ᶠ n : ℕ in atTop,
      mu n (phaseNat n + 2) ≤
        Cμ * (Real.log (n : ℝ)) ^ phaseTailBeta * (n : ℝ) ^ (-1 : ℝ) := by
  obtain ⟨C₂, _, _, _, hLem21⟩ := exists_uniform_phaseExpansion_and_adjacent_bounds
  refine ⟨Real.exp C₂, Real.exp_pos C₂, ?_⟩
  filter_upwards [hLem21, eventually_phaseDomain, eventually_phaseNat_add_two_le,
    eventually_logLogOrder_le_logOrder_hp,
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop 2)] with
    n h21 hnDom ha2 hllLeL hL2
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by have := hnDom.1; omega)
  have hL_pos : 0 < Real.log (n : ℝ) := by dsimp [logOrder] at hL2; linarith
  have hhi := (abs_le.mp h21.2.2.1).2
  have h1md_L : 0 ≤ (1 - phaseDelta n) * (logOrder n - logLogOrder n) :=
    mul_nonneg (by linarith [phaseDelta_lt_one n]) (by linarith)
  have hlog_le : Real.log (mu n (phaseNat n + 2)) ≤
      C₂ + phaseTailBeta * logLogOrder n + (-1 : ℝ) * logOrder n := by
    unfold phaseTailBeta
    linarith
  calc mu n (phaseNat n + 2)
      = Real.exp (Real.log (mu n (phaseNat n + 2))) := (Real.exp_log (mu_pos ha2)).symm
    _ ≤ Real.exp (C₂ + phaseTailBeta * logLogOrder n + (-1 : ℝ) * logOrder n) :=
        Real.exp_le_exp.mpr hlog_le
    _ = Real.exp C₂ * (Real.log (n : ℝ)) ^ phaseTailBeta * (n : ℝ) ^ (-1 : ℝ) := by
        dsimp [logOrder, logLogOrder]
        rw [Real.exp_add, Real.exp_add, mul_comm phaseTailBeta, mul_comm (-1 : ℝ),
          ← Real.rpow_def_of_pos hL_pos, ← Real.rpow_def_of_pos hn_pos]

private theorem eventually_pairKernelJ_phaseNat_add_two_le_one :
    ∀ᶠ n : ℕ in atTop, pairKernelJ n (phaseNat n + 2) ≤ 1 := by
  have h2mul_add2 : ∀ᶠ n : ℕ in atTop, 2 * (phaseNat n + 2) ≤ n := by
    have hsmall : (fun n : ℕ ↦ (2 * ((phaseNat n : ℝ) + 2))) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ)) := by
      have h1 := phaseNat_isTheta_logOrder.1.trans_isLittleO logOrder_isLittleO_natCast
      have h2 : (fun _n : ℕ ↦ (2 : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
        simpa only [Function.comp_def, id_eq] using
          (isLittleO_const_id_atTop (2 : ℝ)).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
      exact (h1.add h2).const_mul_left 2
    filter_upwards [hsmall.bound one_pos] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (Nat.cast_nonneg n), one_mul] at hn
    exact_mod_cast (show ((2 * (phaseNat n + 2) : ℕ) : ℝ) ≤ (n : ℝ) by push_cast; linarith)
  let CJ : ℝ := 50 * Real.exp (phaseC / 2 + 3 * q / 4)
  have hCJ_pos : 0 < CJ := by dsimp [CJ]; positivity
  have hCJ_small : ∀ᶠ n : ℕ in atTop,
      CJ * (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    have ho := (log_rpow_isLittleO_rpow_pos (3 / 2) (1 / 2) (by norm_num)).bound
      (one_div_pos.mpr hCJ_pos)
    filter_upwards [ho, tendsto_logOrder_atTop.eventually (eventually_ge_atTop 2),
      eventually_gt_atTop 0] with n hb hL hn0
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by dsimp [logOrder] at hL; linarith) _),
      abs_of_nonneg (Real.rpow_nonneg hn_pos.le _)] at hb
    have hmul := mul_le_mul_of_nonneg_left hb hCJ_pos.le
    rw [← mul_assoc, mul_one_div_cancel hCJ_pos.ne', one_mul] at hmul
    exact hmul
  filter_upwards [eventually_phaseDomain,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    h2mul_add2, tendsto_logOrder_atTop.eventually (eventually_ge_atTop 2),
    hCJ_small] with n hnDom hPhBnd h2add2 hL2 hCJn
  let u : ℕ := phaseNat n + 2
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by have := hnDom.1; omega)
  have hL_pos : 0 < Real.log (n : ℝ) := by dsimp [logOrder] at hL2; linarith
  have hu_le5L : (u : ℝ) ≤ 5 * Real.log (n : ℝ) := by
    dsimp [u]; push_cast; dsimp [logOrder] at hPhBnd hL2; linarith [hPhBnd.2]
  have haq := phaseNat_mul_q_eq hnDom
  have h1md_le : (1 - phaseDelta n) * q ≤ q :=
    mul_le_of_le_one_left q_pos.le (by linarith [phaseDelta_nonneg n])
  have h2u4_sharp : (2 : ℝ) ^ ((u : ℝ) / 4) ≤
      Real.exp (phaseC / 2 + 3 * q / 4) * (n : ℝ) ^ (1 / 2 : ℝ) *
        (Real.log (n : ℝ)) ^ (-(1 / 2 : ℝ)) := by
    have hlog2u : Real.log 2 * ((u : ℝ) / 4) ≤
        (phaseC / 2 + 3 * q / 4) + (1 / 2 : ℝ) * Real.log (n : ℝ) +
          (-(1 / 2 : ℝ)) * Real.log (Real.log (n : ℝ)) := by
      have hcomm : Real.log 2 * ((u : ℝ) / 4) = ((u : ℝ) / 4) * q := by unfold q; ring
      rw [hcomm]
      dsimp [u, logOrder, logLogOrder] at haq ⊢
      push_cast
      linarith
    calc (2 : ℝ) ^ ((u : ℝ) / 4)
        = Real.exp (Real.log 2 * ((u : ℝ) / 4)) := Real.rpow_def_of_pos two_pos _
      _ ≤ Real.exp ((phaseC / 2 + 3 * q / 4) + (1 / 2 : ℝ) * Real.log (n : ℝ) +
            (-(1 / 2 : ℝ)) * Real.log (Real.log (n : ℝ))) := Real.exp_le_exp.mpr hlog2u
      _ = Real.exp (phaseC / 2 + 3 * q / 4) * (n : ℝ) ^ (1 / 2 : ℝ) *
            (Real.log (n : ℝ)) ^ (-(1 / 2 : ℝ)) := by
          rw [Real.exp_add, Real.exp_add, mul_comm (1 / 2 : ℝ), mul_comm (-(1 / 2 : ℝ)),
            ← Real.rpow_def_of_pos hn_pos, ← Real.rpow_def_of_pos hL_pos]
  have hnu_ge : (n : ℝ) / 2 ≤ ((n - u : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    have : 2 * (u : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2add2
    linarith
  have hu_sq : (u : ℝ) ^ 2 ≤ 25 * (Real.log (n : ℝ)) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    calc (u : ℝ) ^ 2 ≤ (5 * Real.log (n : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg u) hu_le5L 2
      _ = 25 * (Real.log (n : ℝ)) ^ 2 := by ring
  unfold pairKernelJ
  have hnu_pos : 0 < ((n - u : ℕ) : ℝ) := lt_of_lt_of_le (half_pos hn_pos) hnu_ge
  rw [div_le_one hnu_pos]
  calc (u : ℝ) ^ 2 * (2 : ℝ) ^ ((u : ℝ) / 4)
      ≤ (25 * (Real.log (n : ℝ)) ^ (2 : ℝ)) *
          (Real.exp (phaseC / 2 + 3 * q / 4) * (n : ℝ) ^ (1 / 2 : ℝ) *
            (Real.log (n : ℝ)) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul hu_sq h2u4_sharp (by positivity) (by positivity)
    _ = (CJ / 2) * ((Real.log (n : ℝ)) ^ (2 : ℝ) * (Real.log (n : ℝ)) ^ (-(1 / 2 : ℝ))) *
          (n : ℝ) ^ (1 / 2 : ℝ) := by
        dsimp [CJ]; ring
    _ = (CJ / 2) * (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hL_pos]; norm_num
    _ ≤ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
        have hhalf_CJ : (CJ / 2) * (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) ≤
            (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by linarith [hCJn]
        exact mul_le_mul_of_nonneg_right hhalf_CJ (Real.rpow_nonneg hn_pos.le _)
    _ = (n : ℝ) / 2 := by
        rw [mul_assoc, ← Real.rpow_add hn_pos]; norm_num [Real.rpow_one]; ring
    _ ≤ ((n - u : ℕ) : ℝ) := hnu_ge

private theorem eventually_pairKernelK_phaseNat_add_two_le :
    ∃ CK : ℝ, 0 < CK ∧ ∀ᶠ n : ℕ in atTop,
      pairKernelK n (phaseNat n + 2) ≤
          CK * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ (5 / 2 : ℝ) ∧
        pairKernelK n (phaseNat n + 2) ≤ 1 / 2 := by
  let CK : ℝ := Real.sqrt 2 * 5 * Real.exp (-3 / 2 * phaseC)
  have hCK_pos : 0 < CK := by dsimp [CK]; positivity
  refine ⟨CK, hCK_pos, ?_⟩
  have hK_half : ∀ᶠ n : ℕ in atTop,
      CK * (Real.log (n : ℝ)) ^ (5 / 2 : ℝ) ≤ 1 / 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    have ho := (log_rpow_isLittleO_rpow_pos (5 / 2) (1 / 2) (by norm_num)).bound
      (div_pos (by norm_num : (0 : ℝ) < 1 / 2) hCK_pos)
    filter_upwards [ho, tendsto_logOrder_atTop.eventually (eventually_ge_atTop 2),
      eventually_gt_atTop 0] with n hb hL hn0
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by dsimp [logOrder] at hL; linarith) _),
      abs_of_nonneg (Real.rpow_nonneg hn_pos.le _)] at hb
    have hmul := mul_le_mul_of_nonneg_left hb hCK_pos.le
    rw [← mul_assoc, mul_div_cancel₀ _ hCK_pos.ne'] at hmul
    exact hmul
  filter_upwards [eventually_phaseDomain,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop 2), hK_half] with
    n hnDom hPhBnd hL2 hCKn
  let u : ℕ := phaseNat n + 2
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by have := hnDom.1; omega)
  have hL_pos : 0 < Real.log (n : ℝ) := by dsimp [logOrder] at hL2; linarith
  have hu_le5L : (u : ℝ) ≤ 5 * Real.log (n : ℝ) := by
    dsimp [u]; push_cast; dsimp [logOrder] at hPhBnd hL2; linarith [hPhBnd.2]
  have haq := phaseNat_mul_q_eq hnDom
  have h1md_nn : 0 ≤ (1 - phaseDelta n) * q :=
    mul_nonneg (by linarith [phaseDelta_lt_one n]) q_pos.le
  have h2neg : (2 : ℝ) ^ (-3 * (u : ℝ) / 4) ≤
      Real.exp (-3 / 2 * phaseC) * (n : ℝ) ^ (-(3 / 2 : ℝ)) *
        (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) := by
    have hlog : Real.log 2 * (-3 * (u : ℝ) / 4) ≤
        (-3 / 2 * phaseC) + (-(3 / 2 : ℝ)) * Real.log (n : ℝ) +
          (3 / 2 : ℝ) * Real.log (Real.log (n : ℝ)) := by
      have hcomm : Real.log 2 * (-3 * (u : ℝ) / 4) = (-3 * (u : ℝ) / 4) * q := by unfold q; ring
      rw [hcomm]
      dsimp [u, logOrder, logLogOrder] at haq ⊢
      push_cast
      linarith [q_pos]
    calc (2 : ℝ) ^ (-3 * (u : ℝ) / 4)
        = Real.exp (Real.log 2 * (-3 * (u : ℝ) / 4)) := Real.rpow_def_of_pos two_pos _
      _ ≤ Real.exp ((-3 / 2 * phaseC) + (-(3 / 2 : ℝ)) * Real.log (n : ℝ) +
            (3 / 2 : ℝ) * Real.log (Real.log (n : ℝ))) := Real.exp_le_exp.mpr hlog
      _ = Real.exp (-3 / 2 * phaseC) * (n : ℝ) ^ (-(3 / 2 : ℝ)) *
            (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) := by
          rw [Real.exp_add, Real.exp_add, mul_comm (-(3 / 2 : ℝ)), mul_comm (3 / 2 : ℝ),
            ← Real.rpow_def_of_pos hn_pos, ← Real.rpow_def_of_pos hL_pos]
  have hK_bound : pairKernelK n u ≤
      CK * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ (5 / 2 : ℝ) := by
    unfold pairKernelK
    calc Real.sqrt 2 * (u : ℝ) * (n : ℝ) * (2 : ℝ) ^ (-3 * (u : ℝ) / 4)
        ≤ Real.sqrt 2 * (5 * Real.log (n : ℝ)) * (n : ℝ) *
            (Real.exp (-3 / 2 * phaseC) * (n : ℝ) ^ (-(3 / 2 : ℝ)) *
              (Real.log (n : ℝ)) ^ (3 / 2 : ℝ)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hu_le5L (Real.sqrt_nonneg 2)) hn_pos.le)
            h2neg (by positivity) (by positivity)
      _ = CK * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ))) *
            ((Real.log (n : ℝ)) ^ (1 : ℝ) * (Real.log (n : ℝ)) ^ (3 / 2 : ℝ)) := by
          dsimp [CK]; rw [Real.rpow_one, Real.rpow_one]; ring
      _ = CK * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ (5 / 2 : ℝ) := by
          rw [← Real.rpow_add hn_pos, ← Real.rpow_add hL_pos]; norm_num
  refine ⟨hK_bound, ?_⟩
  calc pairKernelK n u
      ≤ (CK * (Real.log (n : ℝ)) ^ (5 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        linarith [hK_bound]
    _ ≤ (1 / 2 * (n : ℝ) ^ (1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hCKn (Real.rpow_nonneg hn_pos.le _)
    _ = 1 / 2 := by rw [mul_assoc, ← Real.rpow_add hn_pos]; norm_num

/-- **Section 9 asymptotic bound on Proposition 4.1's exceptional probability:**
`𝓔_{α+2}(n) = O(n^(-3/2) (log n)^(β + 5/2))` uniformly across all phases,
where `β = 2 / log 2 + 1 / 2`. -/
theorem lowerTailExceptionalBound_phaseNat_add_two_isBigO :
    (fun n : ℕ ↦ lowerTailExceptionalBound n (phaseNat n + 2)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ)) *
        (Real.log (n : ℝ)) ^ (phaseTailBeta + 5 / 2)) := by
  obtain ⟨Cμ, hCμ_pos, hmu_ev⟩ := eventually_mu_phaseNat_add_two_le_polylog
  obtain ⟨CK, hCK_pos, hK_ev⟩ := eventually_pairKernelK_phaseNat_add_two_le
  have hL_ge2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ Real.log (n : ℝ) :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop 2)
  have hmu2_dom : ∀ᶠ n : ℕ in atTop,
      (Real.log (n : ℝ)) ^ (phaseTailBeta - 5 / 2) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    filter_upwards [(log_rpow_isLittleO_rpow_pos (phaseTailBeta - 5 / 2) (1 / 2)
      (by norm_num)).bound one_pos, hL_ge2, eventually_gt_atTop 0] with n hb hL hn0
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_nonneg (Real.rpow_nonneg hn_pos.le _), one_mul] at hb
    exact hb
  apply IsBigO.of_bound (Cμ ^ 2 * Real.exp 1 + 2 * Cμ * CK + 2)
  filter_upwards [hmu_ev, eventually_pairKernelJ_phaseNat_add_two_le_one,
    hK_ev, hL_ge2, hmu2_dom, eventually_gt_atTop 1] with
    n hmu_le hJ_le1 ⟨hK_bound, hK_le_half⟩ hL2 hmu2n hn1
  let u : ℕ := phaseNat n + 2
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hL_pos : 0 < Real.log (n : ℝ) := by linarith
  let scale : ℝ := (n : ℝ) ^ (-(3 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ (phaseTailBeta + 5 / 2)
  have hterm1 : (mu n u) ^ 2 * Real.exp (pairKernelJ n u) ≤ Cμ ^ 2 * Real.exp 1 * scale := by
    have hmu_sq : (mu n u) ^ 2 ≤
        Cμ ^ 2 * (Real.log (n : ℝ)) ^ (2 * phaseTailBeta) * (n : ℝ) ^ (-2 : ℝ) := by
      calc (mu n u) ^ 2
          ≤ (Cμ * (Real.log (n : ℝ)) ^ phaseTailBeta * (n : ℝ) ^ (-1 : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (mu_nonneg n u) hmu_le 2
        _ = Cμ ^ 2 * ((Real.log (n : ℝ)) ^ phaseTailBeta) ^ (2 : ℝ) *
              ((n : ℝ) ^ (-1 : ℝ)) ^ (2 : ℝ) := by
            rw [Real.rpow_two, Real.rpow_two]; ring
        _ = Cμ ^ 2 * (Real.log (n : ℝ)) ^ (2 * phaseTailBeta) * (n : ℝ) ^ (-2 : ℝ) := by
            rw [← Real.rpow_mul hL_pos.le, ← Real.rpow_mul hn_pos.le,
              show phaseTailBeta * 2 = 2 * phaseTailBeta by ring,
              show (-1 : ℝ) * 2 = -2 by norm_num]
    have hdom_mul :
        (Real.log (n : ℝ)) ^ (2 * phaseTailBeta) * (n : ℝ) ^ (-2 : ℝ) ≤ scale := by
      dsimp [scale]
      calc (Real.log (n : ℝ)) ^ (2 * phaseTailBeta) * (n : ℝ) ^ (-2 : ℝ)
          = ((Real.log (n : ℝ)) ^ (phaseTailBeta + 5 / 2) *
              (Real.log (n : ℝ)) ^ (phaseTailBeta - 5 / 2)) * (n : ℝ) ^ (-2 : ℝ) := by
            rw [← Real.rpow_add hL_pos]; congr 2; ring
        _ ≤ ((Real.log (n : ℝ)) ^ (phaseTailBeta + 5 / 2) * (n : ℝ) ^ (1 / 2 : ℝ)) *
              (n : ℝ) ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hmu2n (Real.rpow_nonneg hL_pos.le _))
              (Real.rpow_nonneg hn_pos.le _)
        _ = (Real.log (n : ℝ)) ^ (phaseTailBeta + 5 / 2) *
              ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-2 : ℝ)) := by ring
        _ = (n : ℝ) ^ (-(3 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ (phaseTailBeta + 5 / 2) := by
            rw [← Real.rpow_add hn_pos, mul_comm]; norm_num
    calc (mu n u) ^ 2 * Real.exp (pairKernelJ n u)
        ≤ (Cμ ^ 2 * (Real.log (n : ℝ)) ^ (2 * phaseTailBeta) * (n : ℝ) ^ (-2 : ℝ)) *
            Real.exp 1 :=
          mul_le_mul hmu_sq (Real.exp_le_exp.mpr hJ_le1) (Real.exp_pos _).le (by positivity)
      _ = Cμ ^ 2 * Real.exp 1 *
            ((Real.log (n : ℝ)) ^ (2 * phaseTailBeta) * (n : ℝ) ^ (-2 : ℝ)) := by ring
      _ ≤ Cμ ^ 2 * Real.exp 1 * scale :=
          mul_le_mul_of_nonneg_left hdom_mul (by positivity)
  have hterm2 : mu n u * (Real.exp (pairKernelK n u) - 1) ≤ 2 * Cμ * CK * scale := by
    have hexpK : Real.exp (pairKernelK n u) - 1 ≤
        2 * CK * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ (5 / 2 : ℝ) := by
      have h1 := exp_sub_one_le_two_mul (pairKernelK_nonneg n u) hK_le_half
      linarith [hK_bound]
    have hexpK_nn : 0 ≤ Real.exp (pairKernelK n u) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp (pairKernelK_nonneg n u))
    calc mu n u * (Real.exp (pairKernelK n u) - 1)
        ≤ (Cμ * (Real.log (n : ℝ)) ^ phaseTailBeta * (n : ℝ) ^ (-1 : ℝ)) *
            (2 * CK * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ (5 / 2 : ℝ)) :=
          mul_le_mul hmu_le hexpK hexpK_nn (by positivity)
      _ = 2 * Cμ * CK * ((n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))) *
            ((Real.log (n : ℝ)) ^ phaseTailBeta * (Real.log (n : ℝ)) ^ (5 / 2 : ℝ)) := by ring
      _ = 2 * Cμ * CK * scale := by
          dsimp [scale]
          rw [← Real.rpow_add hn_pos, ← Real.rpow_add hL_pos]
          norm_num
          ring
  have hterm3 : 2 * Real.exp (-2 * (Real.log (n : ℝ)) ^ 4) ≤ 2 * scale := by
    have hL4_ge : (3 / 2 : ℝ) * Real.log (n : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 4 := by
      have h8 : (8 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := by
        calc (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
          _ ≤ (Real.log (n : ℝ)) ^ 3 := pow_le_pow_left₀ (by norm_num) hL2 3
      calc (3 / 2 : ℝ) * Real.log (n : ℝ)
          ≤ 16 * Real.log (n : ℝ) := mul_le_mul_of_nonneg_right (by norm_num) hL_pos.le
        _ = 2 * (8 * Real.log (n : ℝ)) := by ring
        _ ≤ 2 * ((Real.log (n : ℝ)) ^ 3 * Real.log (n : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h8 hL_pos.le) (by norm_num)
        _ = 2 * (Real.log (n : ℝ)) ^ 4 := by ring
    have hexp_le : Real.exp (-2 * (Real.log (n : ℝ)) ^ 4) ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [Real.rpow_def_of_pos hn_pos, mul_comm (Real.log (n : ℝ))]
      exact Real.exp_le_exp.mpr (by linarith)
    have hLpow_ge1 : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ (phaseTailBeta + 5 / 2) := by
      have hβ_nn : 0 ≤ phaseTailBeta + 5 / 2 := by
        unfold phaseTailBeta; have := q_pos; positivity
      exact Real.one_le_rpow (by linarith) hβ_nn
    dsimp [scale]
    calc 2 * Real.exp (-2 * (Real.log (n : ℝ)) ^ 4)
        ≤ 2 * ((n : ℝ) ^ (-(3 / 2 : ℝ)) * 1) := by linarith
      _ ≤ 2 * ((n : ℝ) ^ (-(3 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ (phaseTailBeta + 5 / 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hLpow_ge1 (Real.rpow_nonneg hn_pos.le _)) (by norm_num)
  have hEnn : 0 ≤ lowerTailExceptionalBound n u := by
    unfold lowerTailExceptionalBound
    have hexpK_nn : 0 ≤ Real.exp (pairKernelK n u) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp (pairKernelK_nonneg n u))
    have hmu_nn : 0 ≤ mu n u := mu_nonneg n u
    exact add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      (mul_nonneg hmu_nn hexpK_nn)) (by positivity)
  have hscale_nn : 0 ≤ scale := by dsimp [scale]; positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hEnn, abs_of_nonneg hscale_nn]
  change lowerTailExceptionalBound n u ≤ (Cμ ^ 2 * Real.exp 1 + 2 * Cμ * CK + 2) * scale
  unfold lowerTailExceptionalBound
  linarith

/-- **Summability of `n^(-3/2) (log n)^γ` for every real `γ`:**
comparing against `n^(-5/4)` establishes Borel–Cantelli summability for all
polylogarithmic `n^(-3/2)` failure tails in Sections 4 and 9. -/
theorem summable_polylog_three_halves (γ : ℝ) :
    Summable (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ γ) := by
  have ho := (log_rpow_isLittleO_rpow_pos γ (1 / 4) (by norm_num)).bound one_pos
  have hL1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop 1)
  have hev : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (-(3 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ γ ≤ (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
    filter_upwards [ho, hL1, eventually_gt_atTop 0] with n hb hL hn0
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) γ),
      abs_of_nonneg (Real.rpow_nonneg hn_pos.le _), one_mul] at hb
    calc (n : ℝ) ^ (-(3 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ γ
        ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) * (n : ℝ) ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hn_pos.le _)
      _ = (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
          rw [← Real.rpow_add hn_pos]; norm_num
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hev.and hL1)
  rw [← summable_nat_add_iff N]
  have hp : Summable (fun k : ℕ ↦ ((k + N : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) :=
    (summable_nat_add_iff N).mpr (Real.summable_nat_rpow.mpr (by norm_num))
  refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ (hN (k + N) (Nat.le_add_left N k)).1) hp
  have hLk := (hN (k + N) (Nat.le_add_left N k)).2
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg (by linarith) γ)

/-- **Summability of `𝓔_{α+2}(n)` (`Section 9`):**
`∑_n lowerTailExceptionalBound n (phaseNat n + 2) < ∞`. -/
theorem summable_lowerTailExceptionalBound_phaseNat_add_two :
    Summable (fun n : ℕ ↦ lowerTailExceptionalBound n (phaseNat n + 2)) := by
  obtain ⟨C, hC⟩ := lowerTailExceptionalBound_phaseNat_add_two_isBigO.bound
  have hL1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop 1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hC.and hL1)
  rw [← summable_nat_add_iff N]
  have hdom : Summable (fun k : ℕ ↦
      |C| * (((k + N : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) *
        (Real.log ((k + N : ℕ) : ℝ)) ^ (phaseTailBeta + 5 / 2))) :=
    ((summable_nat_add_iff N).mpr (summable_polylog_three_halves (phaseTailBeta + 5 / 2))).mul_left |C|
  refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_) hdom
  · unfold lowerTailExceptionalBound
    have hexpK_nn : 0 ≤ Real.exp (pairKernelK (k + N) (phaseNat (k + N) + 2)) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp (pairKernelK_nonneg _ _))
    have hmu_nn : 0 ≤ mu (k + N) (phaseNat (k + N) + 2) := mu_nonneg _ _
    exact add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      (mul_nonneg hmu_nn hexpK_nn)) (by positivity)
  · obtain ⟨hCk, hLk⟩ := hN (k + N) (Nat.le_add_left N k)
    have hrhs_nn : 0 ≤ ((k + N : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) *
        (Real.log ((k + N : ℕ) : ℝ)) ^ (phaseTailBeta + 5 / 2) :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg (by linarith) _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hrhs_nn] at hCk
    exact le_trans (le_abs_self _) (le_trans hCk
      (mul_le_mul_of_nonneg_right (le_abs_self C) hrhs_nn))

/-! ## 3. Full `\eqref{eq:shift-equivariance}` (`Lemma 3.2(iii)` Gibbs law & mean shift) -/

/-- Tilted Gaussian Gibbs probability `p_{S,λ}(i) = e^{λ i - (log 2) i² / 2} / Z_S(λ)` on `S ⊆ ℤ`. -/
def gibbsProb (S : Set ℤ) (lambda : ℝ) (i : ℤ) : ℝ :=
  gaussWeight lambda i / partitionFn S lambda

/-- Mean `M_S(λ) = ∑_{i ∈ S} i · p_{S,λ}(i)` of the tilted Gaussian Gibbs law on `S ⊆ ℤ`. -/
def gibbsMean (S : Set ℤ) (lambda : ℝ) : ℝ :=
  ∑' i : S, (i.1 : ℝ) * gibbsProb S lambda i.1

/-- **Gibbs probability shift equivariance (`eq:shift-equivariance`, `(3.13)` right):**
for every `S ⊆ ℤ`, `λ ∈ ℝ`, and `i ∈ ℤ`,
`p_{S+1, λ}(i + 1) = p_{S, λ - log 2}(i)`. -/
theorem gibbsProb_shiftSupportOne (S : Set ℤ) (lambda : ℝ) (i : ℤ) :
    gibbsProb (shiftSupportOne S) lambda (i + 1) =
      gibbsProb S (lambda - Real.log 2) i := by
  unfold gibbsProb
  rw [gaussWeight_add_one, partitionFn_shiftSupportOne,
    mul_div_mul_left _ _ (Real.exp_pos _).ne']

private theorem summable_mul_gaussWeight_subtype (S : Set ℤ) (mu : ℝ) :
    Summable (fun i : S ↦ (i.1 : ℝ) * gaussWeight mu i.1) := by
  have h1 : Summable (fun i : S ↦ gaussWeight (mu + 1) i.1) :=
    (summable_gaussWeight (mu + 1)).subtype S
  have h2 : Summable (fun i : S ↦ gaussWeight (mu - 1) i.1) :=
    (summable_gaussWeight (mu - 1)).subtype S
  refine Summable.of_norm_bounded (h1.add h2) fun i ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gaussWeight_pos mu i.1)]
  have habs_le : |(i.1 : ℝ)| ≤ Real.exp (i.1 : ℝ) + Real.exp (-(i.1 : ℝ)) := by
    rcases le_or_gt 0 (i.1 : ℝ) with hi | hi
    · rw [abs_of_nonneg hi]
      have h1e := Real.add_one_le_exp (i.1 : ℝ)
      have h2e := (Real.exp_pos (-(i.1 : ℝ))).le
      linarith
    · rw [abs_of_neg hi]
      have h1e := Real.add_one_le_exp (-(i.1 : ℝ))
      have h2e := (Real.exp_pos (i.1 : ℝ)).le
      linarith
  calc |(i.1 : ℝ)| * gaussWeight mu i.1
      ≤ (Real.exp (i.1 : ℝ) + Real.exp (-(i.1 : ℝ))) * gaussWeight mu i.1 :=
        mul_le_mul_of_nonneg_right habs_le (gaussWeight_pos mu i.1).le
    _ = gaussWeight (mu + 1) i.1 + gaussWeight (mu - 1) i.1 := by
        unfold gaussWeight
        rw [add_mul, ← Real.exp_add, ← Real.exp_add,
          show (i.1 : ℝ) + (mu * (i.1 : ℝ) - Real.log 2 / 2 * (i.1 : ℝ) ^ 2) =
            (mu + 1) * (i.1 : ℝ) - Real.log 2 / 2 * (i.1 : ℝ) ^ 2 by ring,
          show -(i.1 : ℝ) + (mu * (i.1 : ℝ) - Real.log 2 / 2 * (i.1 : ℝ) ^ 2) =
            (mu - 1) * (i.1 : ℝ) - Real.log 2 / 2 * (i.1 : ℝ) ^ 2 by ring]

/-- **Gibbs mean shift identity (`Lemma 3.2(iii)`):**
for every nonempty `S ⊆ ℤ` and `λ ∈ ℝ`, `M_{S+1}(λ) = M_S(λ - log 2) + 1`. -/
theorem gibbsMean_shiftSupportOne {S : Set ℤ} (hS : S.Nonempty) (lambda : ℝ) :
    gibbsMean (shiftSupportOne S) lambda = gibbsMean S (lambda - Real.log 2) + 1 := by
  unfold gibbsMean
  let e : S ≃ shiftSupportOne S :=
    { toFun := fun i ↦ ⟨i.1 + 1, by simp [shiftSupportOne]⟩
      invFun := fun j ↦ ⟨j.1 - 1, j.2⟩
      left_inv := fun i ↦ Subtype.ext (by dsimp only; omega)
      right_inv := fun j ↦ Subtype.ext (by dsimp only; omega) }
  rw [← e.tsum_eq]
  have hterm : ∀ i : S,
      ((e i).1 : ℝ) * gibbsProb (shiftSupportOne S) lambda (e i).1 =
        (i.1 : ℝ) * gibbsProb S (lambda - Real.log 2) i.1 +
          gibbsProb S (lambda - Real.log 2) i.1 := by
    intro i
    have he : ((e i).1 : ℝ) = (i.1 : ℝ) + 1 := by dsimp [e]; push_cast; ring
    rw [he, show (e i).1 = i.1 + 1 from rfl, gibbsProb_shiftSupportOne]
    ring
  simp_rw [hterm]
  have hs1 : Summable (fun i : S ↦ (i.1 : ℝ) * gibbsProb S (lambda - Real.log 2) i.1) := by
    have heq_fn : (fun i : S ↦ (i.1 : ℝ) * gibbsProb S (lambda - Real.log 2) i.1) =
        (fun i : S ↦ ((i.1 : ℝ) * gaussWeight (lambda - Real.log 2) i.1) /
          partitionFn S (lambda - Real.log 2)) := by
      funext i; unfold gibbsProb; ring
    rw [heq_fn]
    exact (summable_mul_gaussWeight_subtype S (lambda - Real.log 2)).div_const _
  have hs2 : Summable (fun i : S ↦ gibbsProb S (lambda - Real.log 2) i.1) := by
    unfold gibbsProb
    exact ((hasSum_partitionFn S (lambda - Real.log 2)).summable).div_const _
  obtain ⟨x, hx⟩ := hS
  have hZpos : 0 < partitionFn S (lambda - Real.log 2) :=
    lt_of_lt_of_le (gaussWeight_pos _ x)
      ((hasSum_partitionFn S (lambda - Real.log 2)).summable.le_tsum ⟨x, hx⟩
        (fun j _ ↦ (gaussWeight_pos _ j.1).le))
  have hsum_prob : ∑' i : S, gibbsProb S (lambda - Real.log 2) i.1 = 1 := by
    unfold gibbsProb
    rw [tsum_div_const]
    exact div_self hZpos.ne'
  rw [Summable.tsum_add hs1 hs2, hsum_prob]

/-- **Mean-parameterized Gibbs shift equivariance (`eq:shift-equivariance`, `(3.13)` right):**
if `μ = λ_S(T)` is the unique tilt on a nonempty `S ⊆ ℤ` solving `M_S(μ) = T`,
then `μ + log 2 = λ_{S+1}(T + 1)` uniquely solves `M_{S+1}(λ) = T + 1`, and at
these mean-matched tilts `p_{S+1, μ + log 2}(i + 1) = p_{S, μ}(i)` for all `i ∈ ℤ`. -/
theorem unique_gibbsMean_shiftSupportOne_and_prob_eq {S : Set ℤ} (hS : S.Nonempty)
    {T mu : ℝ} (hmean : gibbsMean S mu = T)
    (huniq : ∀ mu' : ℝ, gibbsMean S mu' = T → mu' = mu) :
    gibbsMean (shiftSupportOne S) (mu + Real.log 2) = T + 1 ∧
      (∀ l : ℝ, gibbsMean (shiftSupportOne S) l = T + 1 → l = mu + Real.log 2) ∧
      (∀ i : ℤ, gibbsProb (shiftSupportOne S) (mu + Real.log 2) (i + 1) = gibbsProb S mu i) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gibbsMean_shiftSupportOne hS, add_sub_cancel_right, hmean]
  · intro l hl
    rw [gibbsMean_shiftSupportOne hS] at hl
    have := huniq (l - Real.log 2) (by linarith)
    linarith
  · intro i
    simpa [add_sub_cancel_right] using gibbsProb_shiftSupportOne S (mu + Real.log 2) i

/-- **Dual difference invariance under `+1` support/mean shift (`Lemma 3.2(iii)`):**
`𝓕_{R+1}(T + 1) - 𝓕_{S+1}(T + 1) = 𝓕_R(T) - 𝓕_S(T)`. -/
theorem dualValue_diff_shiftSupportOne {R S : Set ℤ}
    (hR : R.Nonempty) (hS : S.Nonempty) {T : ℝ}
    (hbddR : BddBelow (Set.range fun mu : ℝ ↦ Real.log (partitionFn R mu) - mu * T))
    (hbddS : BddBelow (Set.range fun mu : ℝ ↦ Real.log (partitionFn S mu) - mu * T)) :
    dualValue (shiftSupportOne R) (T + 1) - dualValue (shiftSupportOne S) (T + 1) =
      dualValue R T - dualValue S T := by
  rw [dualValue_shiftSupportOne hR hbddR, dualValue_shiftSupportOne hS hbddS]
  ring

/-! ## 4. Unconditional Asymptotic Lemma 6.1(ii) (`lemma-7.1-all-common-subprofiles(ii)`) -/

private theorem eventually_log_mu_phaseNat_sub_le (M : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ r ≤ M + 1,
      Real.log (mu n (phaseNat n - r)) ≤ ((M : ℝ) + 5 / 2) * Real.log (n : ℝ) := by
  obtain ⟨C₂, _, hC₂_pos, _, hLem21⟩ := exists_uniform_phaseExpansion_and_adjacent_bounds
  have h2mul : ∀ᶠ n : ℕ in atTop, 2 * phaseNat n ≤ n := eventually_two_mul_phaseNat_le
  have hPh_gt : ∀ᶠ n : ℕ in atTop, M + 2 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually
      (eventually_ge_atTop (((M + 2 : ℕ) : ℝ))),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hLM hPh
    exact_mod_cast le_trans hLM hPh.1
  have hL_large : ∀ᶠ n : ℕ in atTop,
      max 2 (2 * C₂) ≤ logOrder n ∧
        (2 / q - 1 / 2) * logLogOrder n + C₂ ≤ 1 / 2 * logOrder n ∧
        Real.log 4 + 2 * |phaseC| + 2 * q ≤ logLogOrder n := by
    have h1 := tendsto_logOrder_atTop.eventually (eventually_ge_atTop (max 2 (2 * C₂)))
    have h2 : ∀ᶠ n : ℕ in atTop,
        (2 / q - 1 / 2) * logLogOrder n + C₂ ≤ 1 / 2 * logOrder n := by
      have ho : (fun n : ℕ ↦ (2 / q - 1 / 2) * logLogOrder n + C₂) =o[atTop] logOrder := by
        have hc : (fun _n : ℕ ↦ C₂) =o[atTop] logOrder := by
          simpa only [Function.comp_def, id_eq] using
            (isLittleO_const_id_atTop C₂).comp_tendsto tendsto_logOrder_atTop
        exact (logLogOrder_isLittleO_logOrder.const_mul_left (2 / q - 1 / 2)).add hc
      filter_upwards [ho.bound (by norm_num : (0 : ℝ) < 1 / 2),
        tendsto_logOrder_atTop.eventually (eventually_ge_atTop 0)] with n hb hnn
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn] at hb
      exact le_trans (le_abs_self _) hb
    have h3 := tendsto_logLogOrder_atTop.eventually
      (eventually_ge_atTop (Real.log 4 + 2 * |phaseC| + 2 * q))
    exact h1.and (h2.and h3)
  filter_upwards [hLem21, eventually_phaseDomain,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    h2mul, hPh_gt, hL_large] with n h21 hnDom hPh h2n hMph ⟨hLmax, htop_sub, hstep_sub⟩
  have hL_pos : 0 < logOrder n := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) hLmax)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by have := hnDom.1; omega)
  have htop : Real.log (mu n (phaseNat n)) ≤ (3 / 2 : ℝ) * logOrder n := by
    have hhi := (abs_le.mp h21.1).2
    have hd1 : phaseDelta n < 1 := phaseDelta_lt_one n
    have hd0 : 0 ≤ phaseDelta n := phaseDelta_nonneg n
    have hll_nn : 0 ≤ logLogOrder n := by
      have : 0 ≤ Real.log 4 + 2 * |phaseC| + 2 * q := by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
        have := q_pos; have := abs_nonneg phaseC; linarith
      linarith
    have hdL : phaseDelta n * logOrder n ≤ logOrder n :=
      mul_le_of_le_one_left hL_pos.le hd1.le
    have hdll : 0 ≤ phaseDelta n * logLogOrder n := mul_nonneg hd0 hll_nn
    linarith
  have hone_step : ∀ t : ℕ, 0 < t → t ≤ phaseNat n →
      Real.log (mu n (t - 1)) - Real.log (mu n t) ≤ logOrder n := by
    intro t ht_pos ht_le
    rw [log_mu_pred_sub_log_mu ht_pos (by omega)]
    have hlog_t : Real.log (t : ℝ) ≤ Real.log 4 + logLogOrder n := by
      have htR : (t : ℝ) ≤ 4 * logOrder n :=
        le_trans (by exact_mod_cast ht_le) hPh.2
      have h4L : Real.log (4 * logOrder n) = Real.log 4 + logLogOrder n := by
        rw [Real.log_mul (by norm_num) hL_pos.ne']; rfl
      rw [← h4L]
      exact Real.log_le_log (by exact_mod_cast ht_pos) htR
    have hlog_den : logOrder n - q ≤ Real.log (((n - t : ℕ) + 1 : ℕ) : ℝ) := by
      have hhalf : (n : ℝ) / 2 ≤ (((n - t : ℕ) + 1 : ℕ) : ℝ) := by
        have h2a : 2 * (t : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 2 * t ≤ n by omega)
        have hsub : ((n - t : ℕ) : ℝ) = (n : ℝ) - (t : ℝ) := Nat.cast_sub (by omega)
        push_cast [hsub]
        linarith
      have hlog_half : Real.log ((n : ℝ) / 2) = logOrder n - q := by
        rw [Real.log_div hn_pos.ne' (by norm_num)]; rfl
      rw [← hlog_half]
      exact Real.log_le_log (half_pos hn_pos) hhalf
    have htq : ((t - 1 : ℕ) : ℝ) * q ≤
        2 * logOrder n - 2 * logLogOrder n + 2 * |phaseC| + q := by
      have hle_a : ((t - 1 : ℕ) : ℝ) ≤ (phaseNat n : ℝ) := by exact_mod_cast (by omega : t - 1 ≤ phaseNat n)
      have hmul := mul_le_mul_of_nonneg_right hle_a q_pos.le
      rw [phaseNat_mul_q_eq hnDom] at hmul
      have h1md : (1 - phaseDelta n) * q ≤ q := by
        nlinarith [phaseDelta_nonneg n, q_pos]
      have hC : phaseC ≤ |phaseC| := le_abs_self phaseC
      linarith
    linarith
  have hind : ∀ r : ℕ, r ≤ M + 1 →
      Real.log (mu n (phaseNat n - r)) ≤ (3 / 2 + (r : ℝ)) * logOrder n := by
    intro r hr
    induction r with
    | zero => simpa using htop
    | succ r ih =>
      have hr_le : r ≤ M + 1 := Nat.le_of_succ_le hr
      have ht_pos : 0 < phaseNat n - r := by omega
      have ht_le : phaseNat n - r ≤ phaseNat n := Nat.sub_le _ _
      have hstep := hone_step (phaseNat n - r) ht_pos ht_le
      have hsub_eq : phaseNat n - r - 1 = phaseNat n - (r + 1) := by omega
      rw [hsub_eq] at hstep
      have hih := ih hr_le
      push_cast
      linarith
  intro r hr
  have hrR : (r : ℝ) ≤ (M : ℝ) + 1 := by exact_mod_cast hr
  have h1 := hind r hr
  have h2 : (3 / 2 + (r : ℝ)) * logOrder n ≤ ((M : ℝ) + 5 / 2) * logOrder n :=
    mul_le_mul_of_nonneg_right (by linarith) hL_pos.le
  simpa [logOrder] using le_trans h1 h2

/-- **Unconditional asymptotic `μ`-cap for Lemma 6.1(ii):**
for any fixed window parameter `M : ℕ`, uniformly over all sufficiently large `n`,
all vertex budgets `w : ℕ` with `w ≤ 2^(-(M + 5)) n`, and all active sizes
`s ∈ [phaseNat n - (M + 1), phaseNat n]`, one has `μ_w(s) ≤ n^(-5/2)`. -/
theorem eventually_mu_vertexCap_le_rpow_neg_five_halves (M : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ w s : ℕ, (w : ℝ) ≤ ((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ) →
        phaseNat n - (M + 1) ≤ s → s ≤ phaseNat n →
        mu w s ≤ (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
  have hsq_lo : ∀ᶠ n : ℕ in atTop,
      (3 / 2 : ℝ) * Real.log (n : ℝ) ≤ ((phaseNat n - (M + 1) : ℕ) : ℝ) * q := by
    have hlim := tendsto_phaseNat_add_mul_q_div_logOrder_two 0
    have hlo : ∀ᶠ n : ℕ in atTop,
        (7 / 4 : ℝ) < (((phaseNat n + 0 : ℕ) : ℝ) * q) / logOrder n :=
      (tendsto_order.1 hlim).1 (7 / 4) (by norm_num)
    have hL_big : ∀ᶠ n : ℕ in atTop, 4 * ((M + 1 : ℕ) : ℝ) * q ≤ logOrder n :=
      tendsto_logOrder_atTop.eventually (eventually_ge_atTop _)
    have hPh_gt : ∀ᶠ n : ℕ in atTop, M + 1 ≤ phaseNat n := by
      filter_upwards [tendsto_logOrder_atTop.eventually (eventually_ge_atTop ((M + 1 : ℕ) : ℝ)),
        eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hLM hPh
      exact_mod_cast le_trans hLM hPh.1
    filter_upwards [hlo, hL_big, hPh_gt, eventually_gt_atTop 1] with n hlon hLb hPhn hn1
    have hL_pos : 0 < logOrder n := Real.log_pos (by exact_mod_cast hn1)
    rw [Nat.add_zero, lt_div_iff₀ hL_pos] at hlon
    rw [Nat.cast_sub hPhn, sub_mul]
    dsimp [logOrder] at hlon hLb
    linarith
  filter_upwards [eventually_log_mu_phaseNat_sub_le M, hsq_lo, eventually_gt_atTop 1,
    eventually_two_mul_phaseNat_le] with n hlog_mu hsq hn1 h2ph w s hw hs_lo hs_hi
  have hn_pos : 0 < n := by omega
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
  by_cases hsw : s ≤ w
  · have hwn : w ≤ n := by
      have hinv_le1 : ((2 : ℝ) ^ (M + 5))⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      have hwR : (w : ℝ) ≤ (n : ℝ) :=
        le_trans hw (mul_le_of_le_one_left hnR_pos.le hinv_le1)
      exact_mod_cast hwR
    have hscale := mu_le_mu_mul_vertex_ratio_pow hn_pos hsw hwn
    have hratio : (w : ℝ) / (n : ℝ) ≤ ((2 : ℝ) ^ (M + 5))⁻¹ :=
      (div_le_iff₀ hnR_pos).mpr hw
    have hpow_le : ((w : ℝ) / (n : ℝ)) ^ s ≤ (((2 : ℝ) ^ (M + 5))⁻¹) ^ s :=
      pow_le_pow_left₀ (by positivity) hratio s
    have hr_le : phaseNat n - s ≤ M + 1 := by omega
    have hs_eq : phaseNat n - (phaseNat n - s) = s := Nat.sub_sub_self hs_hi
    have hmu_n_log : Real.log (mu n s) ≤ ((M : ℝ) + 5 / 2) * Real.log (n : ℝ) := by
      simpa [hs_eq] using hlog_mu (phaseNat n - s) hr_le
    have hmu_n_le : mu n s ≤ Real.exp (((M : ℝ) + 5 / 2) * Real.log (n : ℝ)) := by
      have hsn : s ≤ n := by omega
      calc mu n s = Real.exp (Real.log (mu n s)) := (Real.exp_log (mu_pos hsn)).symm
        _ ≤ Real.exp (((M : ℝ) + 5 / 2) * Real.log (n : ℝ)) := Real.exp_le_exp.mpr hmu_n_log
    have hsq_s : (3 / 2 : ℝ) * Real.log (n : ℝ) ≤ (s : ℝ) * q :=
      le_trans hsq (mul_le_mul_of_nonneg_right (by exact_mod_cast hs_lo) q_pos.le)
    have hpow_exp :
        (((2 : ℝ) ^ (M + 5))⁻¹) ^ s ≤
          Real.exp (-(3 / 2 : ℝ) * ((M : ℝ) + 5) * Real.log (n : ℝ)) := by
      have heq : (((2 : ℝ) ^ (M + 5))⁻¹) ^ s = Real.exp (-((M + 5 : ℕ) : ℝ) * ((s : ℝ) * q)) := by
        rw [inv_pow, ← pow_mul, ← Real.exp_log (by positivity : (0 : ℝ) < ((2 : ℝ) ^ ((M + 5) * s))⁻¹),
          Real.log_inv, Real.log_pow]
        unfold q
        congr 1
        push_cast
        ring
      rw [heq]
      apply Real.exp_le_exp.mpr
      have hM5_nn : 0 ≤ ((M : ℝ) + 5) := by positivity
      have hm := mul_le_mul_of_nonneg_left hsq_s hM5_nn
      push_cast
      linarith
    have hexp_sum :
        ((M : ℝ) + 5 / 2) * Real.log (n : ℝ) +
            (-(3 / 2 : ℝ) * ((M : ℝ) + 5) * Real.log (n : ℝ)) ≤
          -(5 / 2 : ℝ) * Real.log (n : ℝ) := by
      have hM_nn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      have hcoeff : ((M : ℝ) + 5 / 2) + (-(3 / 2 : ℝ) * ((M : ℝ) + 5)) ≤ -(5 / 2 : ℝ) := by
        linarith
      exact mul_le_mul_of_nonneg_right hcoeff hL_pos.le |>.trans_eq' (by ring)
    calc mu w s
        ≤ mu n s * (((2 : ℝ) ^ (M + 5))⁻¹) ^ s :=
          le_trans hscale (mul_le_mul_of_nonneg_left hpow_le (mu_nonneg n s))
      _ ≤ Real.exp (((M : ℝ) + 5 / 2) * Real.log (n : ℝ)) *
            Real.exp (-(3 / 2 : ℝ) * ((M : ℝ) + 5) * Real.log (n : ℝ)) :=
          mul_le_mul hmu_n_le hpow_exp (by positivity) (Real.exp_pos _).le
      _ = Real.exp (((M : ℝ) + 5 / 2) * Real.log (n : ℝ) +
            (-(3 / 2 : ℝ) * ((M : ℝ) + 5) * Real.log (n : ℝ))) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-(5 / 2 : ℝ) * Real.log (n : ℝ)) := Real.exp_le_exp.mpr hexp_sum
      _ = (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
          rw [Real.rpow_def_of_pos hnR_pos, mul_comm]
  · have hchoose0 : w.choose s = 0 := Nat.choose_eq_zero_of_lt (not_le.mp hsw)
    unfold mu
    rw [hchoose0, Nat.cast_zero, zero_mul]
    exact Real.rpow_nonneg hnR_pos.le _

private theorem eventually_phaseNat_le_289_div_100_log :
    ∀ᶠ n : ℕ in atTop, (phaseNat n : ℝ) ≤ (289 / 100 : ℝ) * Real.log (n : ℝ) := by
  have hlim := tendsto_phaseNat_add_mul_q_div_logOrder_two 0
  have h289q : (2 : ℝ) < (289 / 100 : ℝ) * q := by
    have hqlo : (0.6931471803 : ℝ) < q := Real.log_two_gt_d9
    linarith
  have hhi : ∀ᶠ n : ℕ in atTop,
      (((phaseNat n + 0 : ℕ) : ℝ) * q) / logOrder n < (289 / 100 : ℝ) * q :=
    (tendsto_order.1 hlim).2 _ h289q
  filter_upwards [hhi, eventually_gt_atTop 1] with n hhin hn1
  have hL_pos : 0 < logOrder n := Real.log_pos (by exact_mod_cast hn1)
  rw [Nat.add_zero, div_lt_iff₀ hL_pos] at hhin
  have hmul : (phaseNat n : ℝ) * q ≤ ((289 / 100 : ℝ) * logOrder n) * q := by linarith
  exact le_of_mul_le_mul_right hmul q_pos

private theorem complementaryProfile_involutive {I : Type*}
    {k nu : I → ℕ} (hnu : IsPartialSubprofile k nu) :
    complementaryProfile k (complementaryProfile k nu) = nu := by
  funext i
  exact Nat.sub_sub_self (hnu i)

private theorem residualVertexMass_complementaryProfile {I : Type*} [Fintype I]
    {n : ℕ} {u k nu : I → ℕ} (hnu : IsPartialSubprofile k nu)
    (hfull : selectedVertexMass u k = n) :
    residualVertexMass u (complementaryProfile k nu) = n - selectedVertexMass u nu := by
  have hadd :
      selectedVertexMass u nu + residualVertexMass u (complementaryProfile k nu) = n := by
    change (∑ i, u i * nu i) + (∑ i, u i * (k i - nu i)) = n
    rw [← Finset.sum_add_distrib]
    calc ∑ i, (u i * nu i + u i * (k i - nu i))
        = ∑ i, u i * k i := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [← Nat.mul_add, Nat.add_sub_of_le (hnu i)]
      _ = n := hfull
  omega

/-- **Unconditional asymptotic Lemma 6.1(ii) (`lemma-7.1-all-common-subprofiles(ii)`, marked `W(ν)`):**
for any fixed `M : ℕ`, uniformly over all sufficiently large `n`, any finite index
type `I`, active sizes `u : I → ℕ` in `[phaseNat n - (M + 1), phaseNat n]` (`1 ≤ u_i`),
profile `k : I → ℕ` with `∑ u_i k_i = n`, subprofile `ν ≤ k` with
`n - m_ν ≤ 2^(-(M + 5)) n`, and `cZ ≥ 0` with `exp(cZ (log n)²) ≤ E[Z_k^mk]`, both
inequalities of Lemma 6.1(ii) hold:
`W(ν) ≤ (2 n^(-3/2))^(∑ (k_i - ν_i)) exp(-cZ (log n)²) ≤ exp(-(n - m_ν) / 2)`. -/
theorem eventually_partialDiagonalWeight_subprofile_le_exp_neg_half (M : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {I : Type} [Fintype I] [DecidableEq I]
        (u k nu : I → ℕ) (cZ : ℝ),
        0 ≤ cZ →
        (∀ i, 1 ≤ u i ∧ phaseNat n - (M + 1) ≤ u i ∧ u i ≤ phaseNat n) →
        selectedVertexMass u k = n →
        IsPartialSubprofile k nu →
        (((n - selectedVertexMass u nu : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ)) →
        Real.exp (cZ * (Real.log (n : ℝ)) ^ 2) ≤ completeSignedFirstMoment u k →
        partialDiagonalWeight n u k nu ≤
            (2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ i, (k i - nu i)) *
              Real.exp (-cZ * (Real.log (n : ℝ)) ^ 2) ∧
          (2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ i, (k i - nu i)) *
              Real.exp (-cZ * (Real.log (n : ℝ)) ^ 2) ≤
            Real.exp (-(((n - selectedVertexMass u nu : ℕ) : ℝ) / 2)) := by
  have hL_q : ∀ᶠ n : ℕ in atTop, 20 * q ≤ Real.log (n : ℝ) :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop (20 * q))
  filter_upwards [eventually_mu_vertexCap_le_rpow_neg_five_halves M,
    eventually_phaseNat_le_289_div_100_log, hL_q, eventually_gt_atTop 1] with
    n hmuCap hPh289 hLq hn1 I _ _ u k nu cZ hcZ hu hfull hnu hrem hMom
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
  set h : I → ℕ := complementaryProfile k nu
  set w : ℕ := n - selectedVertexMass u nu
  have hh_sub : IsPartialSubprofile k h := fun i ↦ Nat.sub_le (k i) (nu i)
  have hmass : residualVertexMass u h ≤ w :=
    (residualVertexMass_complementaryProfile hnu hfull).le
  have hk_le_n : ∀ i : I, (k i : ℝ) ≤ (n : ℝ) := by
    intro i
    have h1 : k i ≤ u i * k i := Nat.le_mul_of_pos_left (k i) (hu i).1
    have h2 : u i * k i ≤ selectedVertexMass u k :=
      Finset.single_le_sum (f := fun j ↦ u j * k j) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    rw [hfull] at h2
    exact_mod_cast le_trans h1 h2
  have hsharp : ∀ i : I, 2 * (k i : ℝ) * mu w (u i) ≤ 2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro i
    have hmu_i := hmuCap w (u i) hrem (hu i).2.1 (hu i).2.2
    calc 2 * (k i : ℝ) * mu w (u i)
        ≤ 2 * (n : ℝ) * (n : ℝ) ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hk_le_n i) (by norm_num))
            hmu_i (mu_nonneg _ _) (by positivity)
      _ = 2 * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(5 / 2 : ℝ))) := by rw [Real.rpow_one]; ring
      _ = 2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hn_pos]; norm_num
  have hW1 := partialDiagonalWeight_complement_le_pow_div_of_sharp_mu_cap
    n u k h w (2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) (by positivity) hh_sub hfull hmass hsharp
  rw [complementaryProfile_involutive hnu] at hW1
  have hfirst :
      partialDiagonalWeight n u k nu ≤
        (2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ i, h i) *
          Real.exp (-cZ * (Real.log (n : ℝ)) ^ 2) := by
    calc partialDiagonalWeight n u k nu
        ≤ (2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ i, h i) / completeSignedFirstMoment u k := hW1
      _ ≤ (2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ i, h i) /
            Real.exp (cZ * (Real.log (n : ℝ)) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hMom
      _ = (2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ i, h i) *
            Real.exp (-cZ * (Real.log (n : ℝ)) ^ 2) := by
          rw [div_eq_mul_inv, ← Real.exp_neg, neg_mul]
  -- Second inequality: (2 n^(-3/2))^(∑ h_i) * exp(-cZ L²) ≤ exp(-w / 2)
  have hbase_le : 2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤
      Real.exp (-(29 / 20 : ℝ) * Real.log (n : ℝ)) := by
    calc 2 * (n : ℝ) ^ (-(3 / 2 : ℝ))
        = Real.exp q * Real.exp (Real.log (n : ℝ) * (-(3 / 2 : ℝ))) := by
          rw [q, Real.exp_log two_pos, ← Real.rpow_def_of_pos hn_pos]
      _ = Real.exp (q + Real.log (n : ℝ) * (-(3 / 2 : ℝ))) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-(29 / 20 : ℝ) * Real.log (n : ℝ)) :=
          Real.exp_le_exp.mpr (by linarith [hLq])
  have hw_le_alpha : (w : ℝ) ≤ (phaseNat n : ℝ) * ((∑ i, h i : ℕ) : ℝ) := by
    have hw_eq : w = residualVertexMass u h :=
      (residualVertexMass_complementaryProfile hnu hfull).symm
    have hnat : w ≤ phaseNat n * ∑ i, h i := by
      rw [hw_eq]
      unfold residualVertexMass selectedVertexMass
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ ↦ Nat.mul_le_mul_right (h i) (hu i).2.2
    exact_mod_cast hnat
  have hw_half : (w : ℝ) / 2 ≤ (29 / 20 : ℝ) * Real.log (n : ℝ) * ((∑ i, h i : ℕ) : ℝ) := by
    have hH_nn : 0 ≤ ((∑ i, h i : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : (w : ℝ) ≤ (289 / 100 : ℝ) * Real.log (n : ℝ) * ((∑ i, h i : ℕ) : ℝ) :=
      le_trans hw_le_alpha (mul_le_mul_of_nonneg_right hPh289 hH_nn)
    have h2 : (289 / 200 : ℝ) * (Real.log (n : ℝ) * ((∑ i, h i : ℕ) : ℝ)) ≤
        (29 / 20 : ℝ) * (Real.log (n : ℝ) * ((∑ i, h i : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hL_pos.le hH_nn)
    linarith
  have hexp_cZ_le1 : Real.exp (-cZ * (Real.log (n : ℝ)) ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (Real.log (n : ℝ))])
  have hsecond :
      (2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ i, h i) *
          Real.exp (-cZ * (Real.log (n : ℝ)) ^ 2) ≤
        Real.exp (-((w : ℝ) / 2)) := by
    calc (2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ i, h i) *
            Real.exp (-cZ * (Real.log (n : ℝ)) ^ 2)
        ≤ (Real.exp (-(29 / 20 : ℝ) * Real.log (n : ℝ))) ^ (∑ i, h i) * 1 :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hbase_le _)
            hexp_cZ_le1 (Real.exp_pos _).le (by positivity)
      _ = Real.exp (((∑ i, h i : ℕ) : ℝ) * (-(29 / 20 : ℝ) * Real.log (n : ℝ))) := by
          rw [mul_one, ← Real.exp_nat_mul]
      _ ≤ Real.exp (-((w : ℝ) / 2)) := Real.exp_le_exp.mpr (by linarith)
  exact ⟨hfirst, hsecond⟩

/-- **Unconditional asymptotic Lemma 6.1(ii) (`lemma-7.1-all-common-subprofiles(ii)`, unmarked `F₁^ch(ν)`):**
under the same hypotheses with `exp(cZ (log n)³) ≤ E[X̄_k]` (`completeUnmarkedFirstMoment u k`),
`F₁^ch(ν) ≤ (n^(-3/2))^(∑ (k_i - ν_i)) exp(-cZ (log n)³) ≤ exp(-(n - m_ν) / 2)`. -/
theorem eventually_unmarkedDiagonalWeight_subprofile_le_exp_neg_half (M : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {I : Type} [Fintype I] [DecidableEq I]
        (u k nu : I → ℕ) (cZ : ℝ),
        0 ≤ cZ →
        (∀ i, 1 ≤ u i ∧ phaseNat n - (M + 1) ≤ u i ∧ u i ≤ phaseNat n) →
        selectedVertexMass u k = n →
        IsPartialSubprofile k nu →
        (((n - selectedVertexMass u nu : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ)) →
        Real.exp (cZ * (Real.log (n : ℝ)) ^ 3) ≤ completeUnmarkedFirstMoment u k →
        unmarkedDiagonalWeight n u k nu ≤
            ((n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ i, (k i - nu i)) *
              Real.exp (-cZ * (Real.log (n : ℝ)) ^ 3) ∧
          ((n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ i, (k i - nu i)) *
              Real.exp (-cZ * (Real.log (n : ℝ)) ^ 3) ≤
            Real.exp (-(((n - selectedVertexMass u nu : ℕ) : ℝ) / 2)) := by
  have hL_q : ∀ᶠ n : ℕ in atTop, 20 * q ≤ Real.log (n : ℝ) :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop (20 * q))
  filter_upwards [eventually_mu_vertexCap_le_rpow_neg_five_halves M,
    eventually_phaseNat_le_289_div_100_log, hL_q, eventually_gt_atTop 1] with
    n hmuCap hPh289 hLq hn1 I _ _ u k nu cZ hcZ hu hfull hnu hrem hMom
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
  set h : I → ℕ := complementaryProfile k nu
  set w : ℕ := n - selectedVertexMass u nu
  have hh_sub : IsPartialSubprofile k h := fun i ↦ Nat.sub_le (k i) (nu i)
  have hmass : residualVertexMass u h ≤ w :=
    (residualVertexMass_complementaryProfile hnu hfull).le
  have hk_le_n : ∀ i : I, (k i : ℝ) ≤ (n : ℝ) := by
    intro i
    have h1 : k i ≤ u i * k i := Nat.le_mul_of_pos_left (k i) (hu i).1
    have h2 : u i * k i ≤ selectedVertexMass u k :=
      Finset.single_le_sum (f := fun j ↦ u j * k j) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    rw [hfull] at h2
    exact_mod_cast le_trans h1 h2
  have hsharp : ∀ i : I, (k i : ℝ) * mu w (u i) ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro i
    have hmu_i := hmuCap w (u i) hrem (hu i).2.1 (hu i).2.2
    calc (k i : ℝ) * mu w (u i)
        ≤ (n : ℝ) * (n : ℝ) ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul (hk_le_n i) hmu_i (mu_nonneg _ _) hn_pos.le
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(5 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hn_pos]; norm_num
  have hF1 := unmarkedDiagonalWeight_complement_le_pow_div_of_sharp_mu_cap
    n u k h w ((n : ℝ) ^ (-(3 / 2 : ℝ))) (by positivity) hh_sub hfull hmass hsharp
  rw [complementaryProfile_involutive hnu] at hF1
  have hfirst :
      unmarkedDiagonalWeight n u k nu ≤
        ((n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ i, h i) *
          Real.exp (-cZ * (Real.log (n : ℝ)) ^ 3) := by
    calc unmarkedDiagonalWeight n u k nu
        ≤ ((n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ i, h i) / completeUnmarkedFirstMoment u k := hF1
      _ ≤ ((n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ i, h i) /
            Real.exp (cZ * (Real.log (n : ℝ)) ^ 3) :=
          div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hMom
      _ = ((n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ i, h i) *
            Real.exp (-cZ * (Real.log (n : ℝ)) ^ 3) := by
          rw [div_eq_mul_inv, ← Real.exp_neg, neg_mul]
  have hbase_le : (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤
      Real.exp (-(29 / 20 : ℝ) * Real.log (n : ℝ)) := by
    rw [Real.rpow_def_of_pos hn_pos, mul_comm]
    exact Real.exp_le_exp.mpr (by linarith)
  have hw_le_alpha : (w : ℝ) ≤ (phaseNat n : ℝ) * ((∑ i, h i : ℕ) : ℝ) := by
    have hw_eq : w = residualVertexMass u h :=
      (residualVertexMass_complementaryProfile hnu hfull).symm
    have hnat : w ≤ phaseNat n * ∑ i, h i := by
      rw [hw_eq]
      unfold residualVertexMass selectedVertexMass
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ ↦ Nat.mul_le_mul_right (h i) (hu i).2.2
    exact_mod_cast hnat
  have hw_half : (w : ℝ) / 2 ≤ (29 / 20 : ℝ) * Real.log (n : ℝ) * ((∑ i, h i : ℕ) : ℝ) := by
    have hH_nn : 0 ≤ ((∑ i, h i : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : (w : ℝ) ≤ (289 / 100 : ℝ) * Real.log (n : ℝ) * ((∑ i, h i : ℕ) : ℝ) :=
      le_trans hw_le_alpha (mul_le_mul_of_nonneg_right hPh289 hH_nn)
    have h2 : (289 / 200 : ℝ) * (Real.log (n : ℝ) * ((∑ i, h i : ℕ) : ℝ)) ≤
        (29 / 20 : ℝ) * (Real.log (n : ℝ) * ((∑ i, h i : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hL_pos.le hH_nn)
    linarith
  have hexp_cZ_le1 : Real.exp (-cZ * (Real.log (n : ℝ)) ^ 3) ≤ 1 := by
    have hL3_nn : 0 ≤ (Real.log (n : ℝ)) ^ 3 := pow_nonneg hL_pos.le 3
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hsecond :
      ((n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ i, h i) *
          Real.exp (-cZ * (Real.log (n : ℝ)) ^ 3) ≤
        Real.exp (-((w : ℝ) / 2)) := by
    calc ((n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ i, h i) *
            Real.exp (-cZ * (Real.log (n : ℝ)) ^ 3)
        ≤ (Real.exp (-(29 / 20 : ℝ) * Real.log (n : ℝ))) ^ (∑ i, h i) * 1 :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hbase_le _)
            hexp_cZ_le1 (Real.exp_pos _).le (by positivity)
      _ = Real.exp (((∑ i, h i : ℕ) : ℝ) * (-(29 / 20 : ℝ) * Real.log (n : ℝ))) := by
          rw [mul_one, ← Real.exp_nat_mul]
      _ ≤ Real.exp (-((w : ℝ) / 2)) := Real.exp_le_exp.mpr (by linarith)
  exact ⟨hfirst, hsecond⟩

/-! ## 5. General-regime Corollary 8.1 (`cor:zeta-upper`) & v6 Phase Refinement assembly -/

/-- Second-moment exponent `c₀ = min(δ_- / 2, 1 / 60)` of Proposition 7.3 & Corollary 8.1. -/
def secondMomentExponent (deltaMinus : ℝ) : ℝ :=
  min (deltaMinus / 2) (1 / 60)

/-- Vertex-exposure allowance `a_n = 2 n^(1 - c₀ / 3)` of Corollary 8.1 (`cor:zeta-upper`). -/
def concentrationAllowance (deltaMinus : ℝ) (n : ℕ) : ℝ :=
  2 * (n : ℝ) ^ (1 - secondMomentExponent deltaMinus / 3)

/-- **Unconditional negligibly-small allowance check (`cor:zeta-upper`):**
for every `δ_- > 0`, `a_n = 2 n^(1 - c₀/3) = o(n log log n / (log n)⁴)`. -/
theorem concentrationAllowance_isLittleO {deltaMinus : ℝ} (hd : 0 < deltaMinus) :
    concentrationAllowance deltaMinus =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4) := by
  set c₀ := secondMomentExponent deltaMinus
  have hc₀_pos : 0 < c₀ := lt_min (half_pos hd) (by norm_num)
  have hlog4 := log_rpow_isLittleO_rpow_pos (4 : ℝ) (c₀ / 3) (by positivity)
  refine isLittleO_iff.mpr fun eps heps ↦ ?_
  have hb := hlog4.bound (half_pos heps)
  have hll1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (Real.log (n : ℝ)) :=
    tendsto_logLogOrder_atTop.eventually (eventually_ge_atTop 1)
  have hL1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hb, hll1, hL1, eventually_gt_atTop 0] with n hbn hlln hLn hn0
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hL4_pos : 0 < (Real.log (n : ℝ)) ^ 4 := by positivity
  have hbn' : (Real.log (n : ℝ)) ^ 4 ≤ eps / 2 * (n : ℝ) ^ (c₀ / 3) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_pos (Real.rpow_pos_of_pos hn_pos _)] at hbn
    simpa [Real.rpow_natCast] using hbn
  unfold concentrationAllowance
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (div_nonneg (mul_nonneg hn_pos.le (by linarith)) hL4_pos.le),
    ← mul_div_assoc, le_div_iff₀ hL4_pos]
  calc 2 * (n : ℝ) ^ (1 - c₀ / 3) * (Real.log (n : ℝ)) ^ 4
      ≤ 2 * (n : ℝ) ^ (1 - c₀ / 3) * (eps / 2 * (n : ℝ) ^ (c₀ / 3)) :=
        mul_le_mul_of_nonneg_left hbn' (by positivity)
    _ = eps * ((n : ℝ) ^ (1 - c₀ / 3) * (n : ℝ) ^ (c₀ / 3)) := by ring
    _ = eps * ((n : ℝ) * 1) := by
        rw [← Real.rpow_add hn_pos]; norm_num [Real.rpow_one]
    _ ≤ eps * ((n : ℝ) * Real.log (Real.log (n : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hlln hn_pos.le) heps.le
    _ = eps * ((n : ℝ) * Real.log (Real.log (n : ℝ))) := rfl

/-- **General-regime Corollary 8.1 (`cor:zeta-upper`):**
along any regime index set `Nset : Set ℕ`, if `δ_- > 0`, `c₀ = min(δ_- / 2, 1/60)`,
and the Paley–Zygmund + second-moment seeds satisfy
`P(ζ(G_n) ≤ k_co(n)) ≥ exp(-C_sm n^(1 - c₀) / log n)` and
`P(χ(G_n) ≤ k_ch(n)) ≥ exp(-C_sm n^(1 - c₀) / log n)`, then uniformly for all
sufficiently large `n ∈ Nset`, with `a_n = 2 n^(1 - c₀/3)`:
`P(ζ(G_n) > k_co(n) + a_n) ≤ exp(-2 n^(1 - 2 c₀ / 3))` and
`P(χ(G_n) > k_ch(n) + a_n) ≤ exp(-2 n^(1 - 2 c₀ / 3))`. -/
theorem regime_cochromatic_and_chromatic_upperTail_of_secondMoment_seed
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
          {G | (kCo n : ℝ) + concentrationAllowance deltaMinus n < (cochromaticNumber G : ℝ)} ≤
        Real.exp (-2 * (n : ℝ) ^ (1 - 2 * secondMomentExponent deltaMinus / 3)) ∧
      (randomGraphMeasure n).real
          {G | (kCh n : ℝ) + concentrationAllowance deltaMinus n < (chromaticNumberNat G : ℝ)} ≤
        Real.exp (-2 * (n : ℝ) ^ (1 - 2 * secondMomentExponent deltaMinus / 3)) := by
  set c₀ := secondMomentExponent deltaMinus
  have hc₀_pos : 0 < c₀ := lt_min (half_pos hd) (by norm_num)
  have hbeat : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧
        C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ) <
          2 * (n : ℝ) ^ (1 - 2 * c₀ / 3) := by
    have hL1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
      tendsto_logOrder_atTop.eventually (eventually_ge_atTop 1)
    have hrp : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (c₀ / 3)) atTop atTop :=
      (tendsto_rpow_atTop (div_pos hc₀_pos (by norm_num))).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    have hbig : ∀ᶠ n : ℕ in atTop, max 1 (|C_sm| + 1) < 2 * (n : ℝ) ^ (c₀ / 3) :=
      hrp.const_mul_atTop two_pos |>.eventually (eventually_gt_atTop _)
    filter_upwards [eventually_ge_atTop 2, hL1, hbig] with n hn2 hLn hbign
    refine ⟨hn2, ?_⟩
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have h1 : C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ) ≤
        |C_sm| * (n : ℝ) ^ (1 - c₀) := by
      calc C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)
          ≤ |C_sm| * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_abs_self C_sm) (Real.rpow_nonneg hn_pos.le _))
              (by linarith)
        _ ≤ |C_sm| * (n : ℝ) ^ (1 - c₀) / 1 :=
            div_le_div_of_nonneg_left (by positivity) one_pos hLn
        _ = |C_sm| * (n : ℝ) ^ (1 - c₀) := div_one _
    have h2 : |C_sm| * (n : ℝ) ^ (1 - c₀) < 2 * (n : ℝ) ^ (1 - 2 * c₀ / 3) := by
      have hlt_c : |C_sm| < 2 * (n : ℝ) ^ (c₀ / 3) :=
        lt_of_le_of_lt (by linarith [le_max_right 1 (|C_sm| + 1)]) hbign
      calc |C_sm| * (n : ℝ) ^ (1 - c₀)
          < (2 * (n : ℝ) ^ (c₀ / 3)) * (n : ℝ) ^ (1 - c₀) :=
            mul_lt_mul_of_pos_right hlt_c (Real.rpow_pos_of_pos hn_pos _)
        _ = 2 * ((n : ℝ) ^ (c₀ / 3) * (n : ℝ) ^ (1 - c₀)) := by ring
        _ = 2 * (n : ℝ) ^ (1 - 2 * c₀ / 3) := by
            rw [← Real.rpow_add hn_pos]; congr 2; ring
    exact lt_of_le_of_lt h1 h2
  filter_upwards [hbeat.filter_mono inf_le_left, hSeedCo, hSeedCh] with n ⟨hn2, hbn⟩ hSCo hSCh
  set t : ℝ := (n : ℝ) ^ (1 - c₀ / 3)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have ht_nn : 0 ≤ t := Real.rpow_nonneg hn_pos.le _
  have h2t : concentrationAllowance deltaMinus n = 2 * t := rfl
  have hexp_t_le :
      Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) ≤
        Real.exp (-2 * (n : ℝ) ^ (1 - 2 * c₀ / 3)) := by
    apply Real.exp_le_exp.mpr
    have hn1_pos : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
    have hn1_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    have ht2 : t ^ 2 = (n : ℝ) * (n : ℝ) ^ (1 - 2 * c₀ / 3) := by
      calc t ^ 2 = (n : ℝ) ^ ((1 - c₀ / 3) * (2 : ℝ)) := by
            dsimp [t]; rw [← Real.rpow_two, ← Real.rpow_mul hn_pos.le]
        _ = (n : ℝ) ^ (1 + (1 - 2 * c₀ / 3)) := by congr 1; ring
        _ = (n : ℝ) * (n : ℝ) ^ (1 - 2 * c₀ / 3) := by
            rw [Real.rpow_add hn_pos, Real.rpow_one]
    rw [ht2, div_le_iff₀ hn1_pos]
    have hrp_nn : 0 ≤ (n : ℝ) ^ (1 - 2 * c₀ / 3) := Real.rpow_nonneg hn_pos.le _
    have hmul := mul_le_mul_of_nonneg_right hn1_le hrp_nn
    linarith
  have hstrict :
      Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) <
        Real.exp (-C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) := by
    refine lt_of_le_of_lt hexp_t_le (Real.exp_lt_exp.mpr ?_)
    rw [show -C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ) =
      -(C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) by ring]
    linarith
  rw [h2t]
  exact ⟨le_trans (cochromatic_upperTail_of_seed hn2 ht_nn (lt_of_lt_of_le hstrict hSCo)) hexp_t_le,
    le_trans (chromatic_upperTail_of_seed hn2 ht_nn (lt_of_lt_of_le hstrict hSCh)) hexp_t_le⟩

/-- **Unconditional upper bound `A₇(td) ≤ log 2` on `[0, 207 / 200]` (`Section 9`):**
since `S_{0,7} ⊆ S_{≥ 0}` implies `𝓕_{S_{0,7}}(T) ≤ 𝓕_{S_{≥ 0}}(T)` on `(2, 5)`,
the seven-size phase gain never exceeds `log 2`. -/
theorem phaseGain7_le_log_two {td : ℝ} (htd : td ∈ Set.Icc (0 : ℝ) (207 / 200)) :
    phaseGain7 td ≤ Real.log 2 := by
  have hqpos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hA : (288 / 100 : ℝ) < 2 / Real.log 2 := by
    rw [lt_div_iff₀ hqpos]
    linarith [Real.log_two_lt_d9]
  have hB : 2 / Real.log 2 < (289 / 100 : ℝ) := by
    rw [div_lt_iff₀ hqpos]
    linarith [Real.log_two_gt_d9]
  have hT25 : phaseTarget td ∈ Set.Ioo (2 : ℝ) 5 := by
    unfold phaseTarget
    exact ⟨by linarith [htd.2], by linarith [htd.1]⟩
  have hm := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
  have hmono := dualValue_mono S4_subset_S07 S07_subset_Sge0 hm
  unfold phaseGain7
  linarith

/-- **Full v6 Phase Refinement assembly (probability + expectation sandwich + almost-sure bounds):**
given `tildeEps : ℕ → ℝ` (`≥ 0`, `= O(log log n / log n)`) such that the exit probability
of `(log n)³ / n · (χ(G_n) - ζ(G_n))` from
`[lowerPhaseCoeff7 (shiftedPhase δ_n) - tildeEps n, upperPhaseCoeff7 (shiftedPhase δ_n) + tildeEps n]`
is `O(n^(-3/2) (log n)^(β + 5/2))`, setting `ε_n := tildeEps n + 1 / log n` (`n ≥ 3`, `0` otherwise)
yields `C₁ > 0` such that:
1. `0 ≤ ε_n` for all `n`, and `ε_n ≤ C₁ log log n / log n` for all `n ≥ 3`;
2. `P(G_n ∉ twoSidedGapEvent (lower - ε_n) (upper + ε_n) n) = O(n^(-3/2) (log n)^(β + 5/2))`;
3. `((log n)³ / n) E[χ(G_n) - ζ(G_n)] ∈ [lower - ε_n, upper + ε_n]` eventually;
4. for every `c' ≤ 0.080` and `C' ≥ 0.086`, `c' n / (log n)³ ≤ E[χ(G_n) - ζ(G_n)] ≤ C' n / (log n)³`
   eventually, and under every `G(n, 1/2)` coupling `(Ω, ℙ, G)`, almost surely
   `c' n / (log n)³ ≤ χ(G_n) - ζ(G_n) ≤ C' n / (log n)³` eventually. -/
theorem phaseRefinement_expectation_and_ae_of_polylog_tail
    (tildeEps : ℕ → ℝ)
    (htilde_nn : ∀ n, 0 ≤ tildeEps n)
    (htilde_O : tildeEps =O[atTop]
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)))
    (htail : (fun n : ℕ ↦ (randomGraphMeasure n).real
        (twoSidedGapEvent
          (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - tildeEps n)
          (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + tildeEps n) n)ᶜ)
      =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ)) *
        (Real.log (n : ℝ)) ^ (phaseTailBeta + 5 / 2))) :
    let eps : ℕ → ℝ := fun n ↦ if 3 ≤ n then tildeEps n + 1 / Real.log (n : ℝ) else 0
    (∃ C₁ : ℝ, 0 < C₁ ∧ (∀ n, 0 ≤ eps n) ∧
      ∀ n ≥ 3, eps n ≤ C₁ * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) ∧
    ((fun n : ℕ ↦ (randomGraphMeasure n).real
        (twoSidedGapEvent
          (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n)
          (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) n)ᶜ)
      =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ)) *
        (Real.log (n : ℝ)) ^ (phaseTailBeta + 5 / 2))) ∧
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
  have hlog3_gt1 : 1 < Real.log (3 : ℝ) := by
    rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    exact lt_trans Real.exp_one_lt_d9 (by norm_num)
  have heps_nn : ∀ n, 0 ≤ eps n := by
    intro n
    dsimp [eps]
    split_ifs with hn3
    · have hL_pos : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      exact add_nonneg (htilde_nn n) (by positivity)
    · rfl
  -- Part 1: ∃ C₁ > 0, ∀ n ≥ 3, eps n ≤ C₁ log log n / log n
  have heps_O : eps =O[atTop]
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) := by
    have hinv_O : (fun n : ℕ ↦ 1 / Real.log (n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) := by
      apply IsBigO.of_bound 1
      filter_upwards [tendsto_logLogOrder_atTop.eventually (eventually_ge_atTop 1),
        eventually_gt_atTop 2] with n hll hn2
      have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      dsimp [logLogOrder, logOrder] at hll
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity),
        abs_of_pos (div_pos (by linarith) hL_pos), one_mul]
      exact div_le_div_of_nonneg_right hll hL_pos.le
    refine (htilde_O.add hinv_O).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop 3] with n hn3
    simp [eps, hn3]
  obtain ⟨C₀, hC₀_ev⟩ := heps_O.bound
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hC₀_ev
  set N₁ : ℕ := max 3 N₀
  let ratio : ℕ → ℝ := fun k ↦
    if 3 ≤ k then eps k / (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ)) else 0
  let C_fin : ℝ := (Finset.range N₁).sup' ⟨0, Finset.mem_range.mpr (by positivity)⟩ ratio
  let C₁ : ℝ := max 1 (max |C₀| C_fin)
  have hPart1 : ∃ C₁ : ℝ, 0 < C₁ ∧ (∀ n, 0 ≤ eps n) ∧
      ∀ n ≥ 3, eps n ≤ C₁ * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
    refine ⟨C₁, lt_of_lt_of_le one_pos (le_max_left _ _), heps_nn, fun n hn3 ↦ ?_⟩
    have hn_ge3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have hLn_gt1 : 1 < Real.log (n : ℝ) :=
      lt_of_lt_of_le hlog3_gt1 (Real.log_le_log (by norm_num) hn_ge3R)
    have hll_pos : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos hLn_gt1
    have hquo_pos : 0 < Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) :=
      div_pos hll_pos (by linarith)
    rcases lt_or_ge n N₁ with hlt | hge
    · have hle_sup : ratio n ≤ C_fin :=
        Finset.le_sup' ratio (Finset.mem_range.mpr hlt)
      have hr_eq : ratio n = eps n / (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) := by
        simp [ratio, hn3]
      rw [hr_eq, div_le_iff₀ hquo_pos] at hle_sup
      have hCfin_le : C_fin ≤ C₁ := le_trans (le_max_right _ _) (le_max_right _ _)
      rw [mul_div_assoc]
      exact le_trans hle_sup (mul_le_mul_of_nonneg_right hCfin_le hquo_pos.le)
    · have hb := hN₀ n (le_trans (le_max_right 3 N₀) hge)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (heps_nn n),
        abs_of_pos hquo_pos] at hb
      have hC0_le : C₀ ≤ C₁ :=
        le_trans (le_abs_self C₀) (le_trans (le_max_left _ _) (le_max_right _ _))
      rw [mul_div_assoc]
      exact le_trans hb (mul_le_mul_of_nonneg_right hC0_le hquo_pos.le)
  -- Event monotonicity: tildeEps ≤ eps for n ≥ 3
  have hsub_compl : ∀ n ≥ 3,
      (twoSidedGapEvent
          (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n)
          (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) n)ᶜ ⊆
        (twoSidedGapEvent
          (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - tildeEps n)
          (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + tildeEps n) n)ᶜ := by
    intro n hn3 G hG hGin
    apply hG
    have hL_pos : 0 < Real.log (n : ℝ) :=
      lt_trans zero_lt_one (lt_of_lt_of_le hlog3_gt1 (Real.log_le_log (by norm_num) (by exact_mod_cast hn3)))
    have hscale_nn : 0 ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by positivity
    have heps_ge : tildeEps n ≤ eps n := by simp [eps, hn3]; positivity
    obtain ⟨h1, h2⟩ := hGin
    exact ⟨le_trans (mul_le_mul_of_nonneg_right (by linarith) hscale_nn) h1,
      le_trans h2 (mul_le_mul_of_nonneg_right (by linarith) hscale_nn)⟩
  -- Part 2: exit probability from I_n is O(n^(-3/2) L^(β + 5/2))
  have hPart2 :
      ((fun n : ℕ ↦ (randomGraphMeasure n).real
        (twoSidedGapEvent
          (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n)
          (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) n)ᶜ)
      =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ)) *
        (Real.log (n : ℝ)) ^ (phaseTailBeta + 5 / 2))) := by
    refine (IsBigO.of_bound 1 ?_).trans htail
    filter_upwards [eventually_ge_atTop 3] with n hn3
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg,
      abs_of_nonneg measureReal_nonneg, one_mul]
    exact measureReal_mono (hsub_compl n hn3)
  -- Part 3: Expectation sandwich ((log n)³ / n) E[χ - ζ] ∈ I_n eventually
  have hpn_small : ∀ᶠ n : ℕ in atTop,
      ((Real.log (n : ℝ)) ^ 3 + 1) *
        (randomGraphMeasure n).real
          (twoSidedGapEvent
            (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - tildeEps n)
            (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + tildeEps n) n)ᶜ ≤
        1 / Real.log (n : ℝ) := by
    obtain ⟨Ct, hCt⟩ := htail.bound
    have ho := (log_rpow_isLittleO_rpow_pos (phaseTailBeta + 13 / 2) (3 / 2)
      (by norm_num)).bound (one_div_pos.mpr (by positivity : 0 < 2 * (|Ct| + 1)))
    have hL1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
      tendsto_logOrder_atTop.eventually (eventually_ge_atTop 1)
    filter_upwards [hCt, ho, hL1, eventually_gt_atTop 0] with n hCtn hon hLn hn0
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    have hL_pos : 0 < Real.log (n : ℝ) := by linarith
    have hrhs_nn : 0 ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) *
        (Real.log (n : ℝ)) ^ (phaseTailBeta + 5 / 2) :=
      mul_nonneg (Real.rpow_nonneg hn_pos.le _) (Real.rpow_nonneg hL_pos.le _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg,
      abs_of_nonneg hrhs_nn] at hCtn
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hL_pos.le _),
      abs_of_nonneg (Real.rpow_nonneg hn_pos.le _)] at hon
    have hL3p1 : (Real.log (n : ℝ)) ^ 3 + 1 ≤ 2 * (Real.log (n : ℝ)) ^ (3 : ℝ) := by
      have hcast : (Real.log (n : ℝ)) ^ (3 : ℝ) = (Real.log (n : ℝ)) ^ 3 :=
        Real.rpow_natCast (Real.log (n : ℝ)) 3
      rw [hcast]
      have : 1 ≤ (Real.log (n : ℝ)) ^ 3 := one_le_pow₀ hLn
      linarith
    rw [le_div_iff₀ hL_pos]
    calc ((Real.log (n : ℝ)) ^ 3 + 1) *
            (randomGraphMeasure n).real _ * Real.log (n : ℝ)
        ≤ (2 * (Real.log (n : ℝ)) ^ (3 : ℝ)) *
            ((|Ct| + 1) * ((n : ℝ) ^ (-(3 / 2 : ℝ)) *
              (Real.log (n : ℝ)) ^ (phaseTailBeta + 5 / 2))) *
            (Real.log (n : ℝ)) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
          refine mul_le_mul_of_nonneg_right ?_ hL_pos.le
          refine mul_le_mul hL3p1 ?_ measureReal_nonneg (by positivity)
          exact le_trans hCtn (mul_le_mul_of_nonneg_right (by linarith [le_abs_self Ct]) hrhs_nn)
      _ = (2 * (|Ct| + 1)) * (n : ℝ) ^ (-(3 / 2 : ℝ)) *
            ((Real.log (n : ℝ)) ^ (3 : ℝ) * (Real.log (n : ℝ)) ^ (phaseTailBeta + 5 / 2) *
              (Real.log (n : ℝ)) ^ (1 : ℝ)) := by ring
      _ = (2 * (|Ct| + 1)) * (n : ℝ) ^ (-(3 / 2 : ℝ)) *
            (Real.log (n : ℝ)) ^ (phaseTailBeta + 13 / 2) := by
          rw [← Real.rpow_add hL_pos, ← Real.rpow_add hL_pos]
          congr 2; ring
      _ ≤ (2 * (|Ct| + 1)) * (n : ℝ) ^ (-(3 / 2 : ℝ)) *
            (1 / (2 * (|Ct| + 1)) * (n : ℝ) ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hon (by positivity)
      _ = ((2 * (|Ct| + 1)) * (1 / (2 * (|Ct| + 1)))) *
            ((n : ℝ) ^ (-(3 / 2 : ℝ)) * (n : ℝ) ^ (3 / 2 : ℝ)) := by ring
      _ = 1 := by
          rw [mul_one_div_cancel (by positivity), ← Real.rpow_add hn_pos]
          norm_num
  have hPart3 :
      ∀ᶠ n : ℕ in atTop,
        lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n ≤
            (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
              (∫ G : LabeledGraph n,
                ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
                ∂randomGraphMeasure n) ∧
          (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
              (∫ G : LabeledGraph n,
                ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
                ∂randomGraphMeasure n) ≤
            upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n := by
    filter_upwards [eventually_ge_atTop 3, hpn_small] with n hn3 hpn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hL_pos : 0 < Real.log (n : ℝ) :=
      lt_trans zero_lt_one (lt_of_lt_of_le hlog3_gt1 (Real.log_le_log (by norm_num) (by exact_mod_cast hn3)))
    set td := shiftedPhase (phaseDelta n)
    have htd := shiftedPhase_mem_Icc_wide (phaseDelta_mem_Ico n)
    have hA_le_q := phaseGain7_le_log_two htd
    have hq_lt1 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
    have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    set a_n := lowerPhaseCoeff7 td - tildeEps n
    set b_n := upperPhaseCoeff7 td + tildeEps n
    let E : Set (LabeledGraph n) := twoSidedGapEvent a_n b_n n
    let W : LabeledGraph n → ℝ := fun G ↦
      (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
        ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
    have ha_le1 : a_n ≤ 1 := by
      dsimp [a_n]
      unfold lowerPhaseCoeff7
      have h1 : (Real.log 2) ^ 2 / 4 * phaseGain7 td ≤ 1 * 1 := by nlinarith
      linarith [htilde_nn n]
    have hb_nn : 0 ≤ b_n := by
      dsimp [b_n]
      unfold upperPhaseCoeff7
      have : 0 ≤ 2 * Real.log 2 - phaseGain7 td := by linarith
      exact add_nonneg (by positivity) (htilde_nn n)
    have hW_bounds : ∀ G : LabeledGraph n, 0 ≤ W G ∧ W G ≤ (Real.log (n : ℝ)) ^ 3 := by
      intro G
      have hdiff_nn : 0 ≤ (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ) :=
        sub_nonneg.mpr (by exact_mod_cast cochromaticNumber_le_chromaticNumber G)
      have hdiff_le : (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ) ≤ (n : ℝ) := by
        have hchi_le : chromaticNumberNat G ≤ n := by
          simpa [Fintype.card_fin] using chromaticNumberNat_le_card G
        have hchi_R : (chromaticNumberNat G : ℝ) ≤ (n : ℝ) := by exact_mod_cast hchi_le
        have hzeta_nn : (0 : ℝ) ≤ (cochromaticNumber G : ℝ) := Nat.cast_nonneg _
        linarith
      refine ⟨by dsimp [W]; positivity, ?_⟩
      dsimp [W]
      calc (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
          ≤ (Real.log (n : ℝ)) ^ 3 / (n : ℝ) * (n : ℝ) :=
            mul_le_mul_of_nonneg_left hdiff_le (by positivity)
        _ = (Real.log (n : ℝ)) ^ 3 := div_mul_cancel₀ _ hn_pos.ne'
    have hW_mem : ∀ G ∈ E, a_n ≤ W G ∧ W G ≤ b_n := by
      intro G ⟨hlo, hhi⟩
      have hfac_nn : 0 ≤ (Real.log (n : ℝ)) ^ 3 / (n : ℝ) := by positivity
      have hm1 := mul_le_mul_of_nonneg_left hlo hfac_nn
      have hm2 := mul_le_mul_of_nonneg_left hhi hfac_nn
      have hcancel : ∀ x : ℝ,
          (Real.log (n : ℝ)) ^ 3 / (n : ℝ) * (x * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)) = x := by
        intro x
        field_simp [hn_pos.ne', (pow_pos hL_pos 3).ne']
      rw [hcancel] at hm1 hm2
      exact ⟨hm1, hm2⟩
    have hpt_lo : ∀ G : LabeledGraph n,
        a_n - Eᶜ.indicator (fun _ ↦ (1 : ℝ)) G ≤ W G := by
      intro G
      by_cases hG : G ∈ E
      · rw [Set.indicator_of_notMem (not_not.mpr hG), sub_zero]
        exact (hW_mem G hG).1
      · rw [Set.indicator_of_mem hG]
        linarith [(hW_bounds G).1]
    have hpt_hi : ∀ G : LabeledGraph n,
        W G ≤ b_n + Eᶜ.indicator (fun _ ↦ (Real.log (n : ℝ)) ^ 3) G := by
      intro G
      by_cases hG : G ∈ E
      · rw [Set.indicator_of_notMem (not_not.mpr hG), add_zero]
        exact (hW_mem G hG).2
      · rw [Set.indicator_of_mem hG]
        linarith [(hW_bounds G).2, hb_nn]
    have hint_W :
        ∫ G : LabeledGraph n, W G ∂randomGraphMeasure n =
          (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
            ∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n :=
      integral_const_mul _ _
    have hlo_int : a_n - (randomGraphMeasure n).real Eᶜ ≤
        ∫ G : LabeledGraph n, W G ∂randomGraphMeasure n := by
      have hm := integral_mono (μ := randomGraphMeasure n)
        (Integrable.of_finite) (Integrable.of_finite) hpt_lo
      rw [integral_sub (Integrable.of_finite) (Integrable.of_finite),
        integral_const (μ := randomGraphMeasure n), probReal_univ, one_smul,
        integral_indicator_const (μ := randomGraphMeasure n) _ (Set.toFinite Eᶜ).measurableSet,
        smul_eq_mul, mul_one] at hm
      exact hm
    have hhi_int :
        ∫ G : LabeledGraph n, W G ∂randomGraphMeasure n ≤
          b_n + (Real.log (n : ℝ)) ^ 3 * (randomGraphMeasure n).real Eᶜ := by
      have hm := integral_mono (μ := randomGraphMeasure n)
        (Integrable.of_finite) (Integrable.of_finite) hpt_hi
      rw [integral_add (Integrable.of_finite) (Integrable.of_finite),
        integral_const (μ := randomGraphMeasure n), probReal_univ, one_smul,
        integral_indicator_const (μ := randomGraphMeasure n) _ (Set.toFinite Eᶜ).measurableSet,
        smul_eq_mul, mul_comm] at hm
      exact hm
    have hp1 : (randomGraphMeasure n).real Eᶜ ≤ 1 / Real.log (n : ℝ) := by
      have : 1 * (randomGraphMeasure n).real Eᶜ ≤
          ((Real.log (n : ℝ)) ^ 3 + 1) * (randomGraphMeasure n).real Eᶜ :=
        mul_le_mul_of_nonneg_right (by linarith [pow_nonneg hL_pos.le 3]) measureReal_nonneg
      linarith
    have hpL3 : (Real.log (n : ℝ)) ^ 3 * (randomGraphMeasure n).real Eᶜ ≤
        1 / Real.log (n : ℝ) := by
      have : (Real.log (n : ℝ)) ^ 3 * (randomGraphMeasure n).real Eᶜ ≤
          ((Real.log (n : ℝ)) ^ 3 + 1) * (randomGraphMeasure n).real Eᶜ :=
        mul_le_mul_of_nonneg_right (by linarith) measureReal_nonneg
      linarith
    have heps_eq : eps n = tildeEps n + 1 / Real.log (n : ℝ) := by simp [eps, hn3]
    rw [← hint_W]
    refine ⟨?_, ?_⟩
    · dsimp [a_n] at hlo_int; rw [heps_eq]; linarith
    · dsimp [b_n] at hhi_int; rw [heps_eq]; linarith
  -- Part 4: Fixed constants c' ≤ 0.080 and C' ≥ 0.086 in expectation and almost surely
  refine ⟨hPart1, hPart2, hPart3, fun c' C' hc' hC' ↦ ?_⟩
  have heps_zero : Tendsto eps atTop (nhds 0) := by
    obtain ⟨C₁, hC₁_pos, heps_nn', hC₁_le⟩ := hPart1
    have hll_div_zero : Tendsto
        (fun n : ℕ ↦ C₁ * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) atTop (nhds 0) := by
      have h0 := logLogOrder_isLittleO_logOrder.tendsto_div_nhds_zero.const_mul C₁
      simpa [logLogOrder, logOrder, mul_div_assoc] using h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hll_div_zero
      (Eventually.of_forall heps_nn') ?_
    filter_upwards [eventually_ge_atTop 3] with n hn3
    exact hC₁_le n hn3
  have heps_lt : ∀ᶠ n : ℕ in atTop, eps n < 1 / 100000 :=
    (tendsto_order.1 heps_zero).2 (1 / 100000) (by norm_num)
  have hmargin : ∀ n : ℕ,
      (805 / 10000 : ℝ) < lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) ∧
        upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) < (8599 / 100000 : ℝ) := by
    intro n
    have htd := shiftedPhase_mem_Icc_wide (phaseDelta_mem_Ico n)
    have hA : (268155713 / 400000000 : ℝ) < phaseGain7 (shiftedPhase (phaseDelta n)) :=
      lt_trans log_391_div_200_gt (log_391_div_200_lt_phaseGain7 _ htd)
    have hqlo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hqhi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
    have hqsq_lo : (0.6931471803 : ℝ) ^ 2 < (Real.log 2) ^ 2 := by nlinarith
    have hqsq_hi : (Real.log 2) ^ 2 < (0.6931471808 : ℝ) ^ 2 := by nlinarith
    constructor
    · unfold lowerPhaseCoeff7; nlinarith
    · unfold upperPhaseCoeff7
      have hspan : 2 * Real.log 2 - phaseGain7 (shiftedPhase (phaseDelta n)) <
          2 * 0.6931471808 - 268155713 / 400000000 := by linarith
      by_cases hnn : 0 ≤ 2 * Real.log 2 - phaseGain7 (shiftedPhase (phaseDelta n))
      · have hmul :
            (Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - phaseGain7 (shiftedPhase (phaseDelta n))) ≤
              (0.6931471808 : ℝ) ^ 2 / 4 * (2 * 0.6931471808 - 268155713 / 400000000) :=
          mul_le_mul (by linarith) hspan.le hnn (by norm_num)
        linarith
      · have hneg : (Real.log 2) ^ 2 / 4 *
            (2 * Real.log 2 - phaseGain7 (shiftedPhase (phaseDelta n))) < 0 :=
          mul_neg_of_pos_of_neg (by positivity) (not_le.mp hnn)
        linarith
  refine ⟨?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 3, hPart3, heps_lt] with n hn3 ⟨hElo, hEhi⟩ hepsn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hL_pos : 0 < Real.log (n : ℝ) :=
      lt_trans zero_lt_one (lt_of_lt_of_le hlog3_gt1 (Real.log_le_log (by norm_num) (by exact_mod_cast hn3)))
    have hscale_pos : 0 < (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by positivity
    obtain ⟨hmlo, hmhi⟩ := hmargin n
    have hc_lo : c' ≤ lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n := by linarith
    have hc_hi : upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n ≤ C' := by linarith
    have hm1 := mul_le_mul_of_nonneg_right (le_trans hc_lo hElo) hscale_pos.le
    have hm2 := mul_le_mul_of_nonneg_right (le_trans hEhi hc_hi) hscale_pos.le
    have hcancel :
        ((Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
            ∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) *
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) =
        ∫ G : LabeledGraph n,
          ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
          ∂randomGraphMeasure n := by
      field_simp [hn_pos.ne', (pow_pos hL_pos 3).ne']
    rw [hcancel] at hm1 hm2
    exact ⟨hm1, hm2⟩
  · intro Ω _ ℙ _ G hMarg
    have hsum_I : Summable (fun n : ℕ ↦ (randomGraphMeasure n).real
        (twoSidedGapEvent
          (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n)
          (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) n)ᶜ) := by
      obtain ⟨Cb, hCb⟩ := hPart2.bound
      have hL1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
        tendsto_logOrder_atTop.eventually (eventually_ge_atTop 1)
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hCb.and hL1)
      rw [← summable_nat_add_iff N]
      have hdom := ((summable_nat_add_iff N).mpr
        (summable_polylog_three_halves (phaseTailBeta + 5 / 2))).mul_left |Cb|
      refine Summable.of_nonneg_of_le (fun _ ↦ measureReal_nonneg) (fun k ↦ ?_) hdom
      obtain ⟨hCbk, hLk⟩ := hN (k + N) (Nat.le_add_left N k)
      have hrhs_nn : 0 ≤ ((k + N : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) *
          (Real.log ((k + N : ℕ) : ℝ)) ^ (phaseTailBeta + 5 / 2) :=
        mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (Real.rpow_nonneg (by linarith) _)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg,
        abs_of_nonneg hrhs_nn] at hCbk
      exact le_trans hCbk (mul_le_mul_of_nonneg_right (le_abs_self Cb) hrhs_nn)
    filter_upwards [ae_eventually_twoSidedGap_of_summable_compl ℙ G hMarg hsum_I] with ω hω
    filter_upwards [eventually_ge_atTop 3, heps_lt, hω] with n hn3 hepsn ⟨hlo, hhi⟩
    have hL_pos : 0 < Real.log (n : ℝ) :=
      lt_trans zero_lt_one (lt_of_lt_of_le hlog3_gt1 (Real.log_le_log (by norm_num) (by exact_mod_cast hn3)))
    have hscale_nn : 0 ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by positivity
    obtain ⟨hmlo, hmhi⟩ := hmargin n
    have hc_lo : c' ≤ lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n := by linarith
    have hc_hi : upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n ≤ C' := by linarith
    exact ⟨le_trans (mul_le_mul_of_nonneg_right hc_lo hscale_nn) hlo,
      le_trans hhi (mul_le_mul_of_nonneg_right hc_hi hscale_nn)⟩

end

end Erdos625HP
