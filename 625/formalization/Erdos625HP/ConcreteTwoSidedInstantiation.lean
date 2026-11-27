import Erdos625HP.UnconditionalOneSixteenth
import Erdos625HP.ConcreteCochromaticLowerBound
import Erdos625HP.Amplification
import Erdos625HP.TwoSidedAssembly

/-!
# Concrete five-size roots, Section 8 amplification scales, and two-sided `[0.063, 0.104]` instantiation

This module constructs the manuscript's **concrete** five-size first-moment
roots `r₅^co(n)` and `r₅(n)`, concrete integer thresholds `k_co(n)` and
`k_ch(n)` (totalized on finite prefixes via `.toNat` / `phaseRootCenter`), and
concrete Section 8 allowances `a_n = 2 n^{29/30}` and `b_n = 2 √n (log n)²`.
Items 1–3 below are proved **unconditionally** (zero external hypotheses), while
items 4–5 prove the **rare-seed-to-upper-tail amplification implications** and
final two-sided assembly isolating as hypotheses the two `G(n, 1/2)` rare-seed
probability lower bounds obtained from Proposition 7.7 via Paley–Zygmund:

1. **Five-size finite dual convergence and continuity (Lemma 3.2 for `S₅`):**
   `abs_fiveSizeFiniteEntropy_sub_dualValue_le` and
   `continuousOn_fiveSizeFiniteEntropy_Icc`.
2. **Strict monotonicity, existence, and uniqueness of corridor roots `r₅^co(n)`, `r₅(n)` (Lemma 3.1):**
   `eventually_fiveSizePhaseObjective_strictMonoOn_logLogCorridor`,
   `exists_pos_eventually_existsUnique_fiveSizePhaseObjective_zero_logLogCorridor`,
   `fiveSizeCochromaticRootSelected`, `fiveSizeChromaticRootSelected`, and
   `eventually_fiveSizeRoots_spec_unique`.
3. **Unconditional two-sided threshold separations `(A)` (Proposition 5.2 & (5.20)):**
   `exists_concrete_fiveSize_twoSided_location_error` proves both the inner gap
   `(lowerPhaseCoeff (δ_n) - ε_n) · n / (log n)³ ≤ k_χ^-(n) - k_co(n) - a_n` and
   the outer span
   `k_ch(n) + b_n - k_ζ^-(n) ≤ (upperPhaseCoeff (δ_n) + ε_n) · n / (log n)³`
   for a deterministic sequence `ε_n ≥ 0` with `ε_n → 0`.
4. **Concrete Corollary 8.1 (`cor:zeta-upper`) seed-to-upper-tail implications:**
   `hp_cochromatic_upperTail_of_secondMoment_seed` (`≤ exp(-2 n^{14/15})`) and
   `hp_chromatic_upperTail_of_secondMoment_seed` (`≤ exp(-2 (log n)⁴)`),
   conditional on the respective rare-seed lower bounds.
5. **Concrete two-sided Phase Refinement and `[0.063, 0.104]` Main Theorem
   (`concrete_twoSided_phase_and_uniform_gap_of_hp_seeds`):**
   Combining the unconditional lower bounds `(B)` (`Erdos625` for `χ > k_χ^-` and
   `Erdos625HP.ConcreteCochromaticLowerBound` for `ζ > k_ζ^-`), the unconditional
   separations `(A)`, and Corollary 8.1 isolates as hypotheses the two
   `G(n, 1/2)` rare-seed probability lower bounds obtained from Proposition 7.7
   via Paley–Zygmund.
-/

namespace Erdos625HP

open Erdos625 FiveSizeEntropyGap Filter MeasureTheory Set Asymptotics
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

noncomputable section

/-! ## 1. Genuine five-size finite scores, partition function, and dual convergence -/

/-- The five manuscript deficits `2, 3, 4, 5, 6`, indexed by `Fin 5`. -/
def fiveDeficit (i : Fin 5) : ℕ := i.1 + 2

/-- Exact finite descending-factorial score on `S₅ = {2, 3, 4, 5, 6}` after
removing the affine profile terms (equation `(3.1a)` of the manuscript). -/
def fiveDeficitScore (alpha : ℕ) (i : Fin 5) : ℝ :=
  Real.log (alpha.descFactorial (fiveDeficit i) : ℝ) -
    (fiveDeficit i : ℝ) * Real.log (alpha : ℝ) -
    q / 2 * (fiveDeficit i : ℝ) ^ 2

/-- Limiting Gaussian score `-(log 2 / 2) d²` on `S₅ = {2, 3, 4, 5, 6}`. -/
def fiveGaussianScore (i : Fin 5) : ℝ :=
  -(q / 2) * (fiveDeficit i : ℝ) ^ 2

theorem profileDeficitResidualScore_rev_succ_eq_fiveDeficitScore
    (alpha : ℕ) (i : Fin 5) (h : fiveDeficit i < alpha) :
    profileDeficitResidualScore alpha
        (Fin.rev ((⟨fiveDeficit i, h⟩ : Fin alpha).succ)) =
      fiveDeficitScore alpha i := by
  have hsize : (Fin.rev ((⟨fiveDeficit i, h⟩ : Fin alpha).succ)).1 + 1 ≤ alpha := by
    rw [Fin.val_rev, Fin.val_succ]; omega
  have hsub : alpha - ((Fin.rev ((⟨fiveDeficit i, h⟩ : Fin alpha).succ)).1 + 1) =
      fiveDeficit i := by
    rw [Fin.val_rev, Fin.val_succ]
    change alpha - (alpha + 1 - (fiveDeficit i + 1 + 1) + 1) = fiveDeficit i
    omega
  rw [profileDeficitResidualScore_eq_descFactorial alpha _ hsize, hsub]
  rfl

theorem tendsto_fiveDeficitScore (i : Fin 5) :
    Tendsto (fun alpha : ℕ ↦ fiveDeficitScore alpha i) atTop (nhds (fiveGaussianScore i)) := by
  have hcorr := tendsto_log_descFactorial_sub_mul_log (fiveDeficit i)
  simpa [fiveDeficitScore, fiveGaussianScore] using
    hcorr.sub_const (q / 2 * (fiveDeficit i : ℝ) ^ 2)

theorem eventually_uniform_fiveDeficitScore :
    ∀ epsilon > 0, ∃ N : ℕ, ∀ alpha ≥ N, ∀ i : Fin 5,
      |fiveDeficitScore alpha i - fiveGaussianScore i| < epsilon := by
  intro epsilon hepsilon
  obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.mp (tendsto_fiveDeficitScore 0)) epsilon hepsilon
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp (tendsto_fiveDeficitScore 1)) epsilon hepsilon
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp (tendsto_fiveDeficitScore 2)) epsilon hepsilon
  obtain ⟨N3, hN3⟩ := (Metric.tendsto_atTop.mp (tendsto_fiveDeficitScore 3)) epsilon hepsilon
  obtain ⟨N4, hN4⟩ := (Metric.tendsto_atTop.mp (tendsto_fiveDeficitScore 4)) epsilon hepsilon
  refine ⟨max (max (max N0 N1) (max N2 N3)) N4, fun alpha halpha i ↦ ?_⟩
  fin_cases i
  · simpa [Real.dist_eq] using hN0 alpha (by omega)
  · simpa [Real.dist_eq] using hN1 alpha (by omega)
  · simpa [Real.dist_eq] using hN2 alpha (by omega)
  · simpa [Real.dist_eq] using hN3 alpha (by omega)
  · simpa [Real.dist_eq] using hN4 alpha (by omega)

/-- Finite five-size partition function `Z_{n, S₅}(λ)` (before `(3.8a)`). -/
def fiveSizeFinitePartition (alpha : ℕ) (l : ℝ) : ℝ :=
  ∑ i : Fin 5, Real.exp (l * (fiveDeficit i : ℝ) + fiveDeficitScore alpha i)

/-- Finite five-size dual value `𝓕_{n, S₅}(T)` (`(3.8a)` of the manuscript). -/
def fiveSizeFiniteEntropy (alpha : ℕ) (T : ℝ) : ℝ :=
  ⨅ l : ℝ, (Real.log (fiveSizeFinitePartition alpha l) - l * T)

theorem fiveSizeFinitePartition_pos (alpha : ℕ) (l : ℝ) :
    0 < fiveSizeFinitePartition alpha l :=
  Finset.sum_pos (fun _ _ ↦ Real.exp_pos _) Finset.univ_nonempty

private theorem sum_fiveGaussian_eq_partitionFn_S5 (l : ℝ) :
    (∑ i : Fin 5, Real.exp (l * (fiveDeficit i : ℝ) + fiveGaussianScore i)) =
      partitionFn S5 l := by
  rw [partitionFn_S5, sum_F5, Fin.sum_univ_five]
  have h (k : Fin 5) (z : ℤ) (hz : (fiveDeficit k : ℝ) = (z : ℝ)) :
      Real.exp (l * (fiveDeficit k : ℝ) + fiveGaussianScore k) = gaussWeight l z := by
    unfold fiveGaussianScore gaussWeight q
    rw [hz]
    congr 1; ring
  rw [h 0 2 (by unfold fiveDeficit; norm_num),
      h 1 3 (by unfold fiveDeficit; norm_num),
      h 2 4 (by unfold fiveDeficit; norm_num),
      h 3 5 (by unfold fiveDeficit; norm_num),
      h 4 6 (by unfold fiveDeficit; norm_num)]

private theorem log_fiveSizeFinitePartition_bounds
    {alpha : ℕ} {eps : ℝ}
    (hscore : ∀ i : Fin 5, |fiveDeficitScore alpha i - fiveGaussianScore i| ≤ eps)
    (l : ℝ) :
    Real.log (partitionFn S5 l) - eps ≤ Real.log (fiveSizeFinitePartition alpha l) ∧
      Real.log (fiveSizeFinitePartition alpha l) ≤ Real.log (partitionFn S5 l) + eps := by
  have hZ5pos : 0 < partitionFn S5 l := by
    rw [partitionFn_S5]; exact sum_gaussWeight_pos F5 F5_nonempty l
  have hPpos := fiveSizeFinitePartition_pos alpha l
  have hlo : Real.exp (-eps) * partitionFn S5 l ≤ fiveSizeFinitePartition alpha l := by
    rw [← sum_fiveGaussian_eq_partitionFn_S5 l, Finset.mul_sum]
    unfold fiveSizeFinitePartition
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hscore i)).1])
  have hhi : fiveSizeFinitePartition alpha l ≤ Real.exp eps * partitionFn S5 l := by
    rw [← sum_fiveGaussian_eq_partitionFn_S5 l, Finset.mul_sum]
    unfold fiveSizeFinitePartition
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hscore i)).2])
  constructor
  · have h1 := Real.log_le_log (mul_pos (Real.exp_pos _) hZ5pos) hlo
    rw [Real.log_mul (Real.exp_pos _).ne' hZ5pos.ne', Real.log_exp] at h1
    linarith
  · have h1 := Real.log_le_log hPpos hhi
    rw [Real.log_mul (Real.exp_pos _).ne' hZ5pos.ne', Real.log_exp] at h1
    linarith

private theorem bddBelow_fiveSizeFiniteDual {alpha : ℕ} {eps : ℝ}
    (hscore : ∀ i : Fin 5, |fiveDeficitScore alpha i - fiveGaussianScore i| ≤ eps)
    {T : ℝ} (hT : T ∈ Ioo (2 : ℝ) 5) :
    BddBelow (Set.range fun l : ℝ ↦ Real.log (fiveSizeFinitePartition alpha l) - l * T) := by
  have hm := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT)
  obtain ⟨B, hB⟩ := bddBelow_dual S4_subset_S5 hm
  refine ⟨B - eps, ?_⟩
  rintro _ ⟨l, rfl⟩
  have h1 : B ≤ Real.log (partitionFn S5 l) - l * T := hB ⟨l, rfl⟩
  have h2 := (log_fiveSizeFinitePartition_bounds hscore l).1
  linarith

/-- **Uniform 1-Lipschitz comparison `|𝓕_{n, S₅}(T) - 𝓕_{S₅}(T)| ≤ ε` on `(2, 5)`.** -/
theorem abs_fiveSizeFiniteEntropy_sub_dualValue_le
    {alpha : ℕ} {eps : ℝ}
    (hscore : ∀ i : Fin 5, |fiveDeficitScore alpha i - fiveGaussianScore i| ≤ eps)
    {T : ℝ} (hT : T ∈ Ioo (2 : ℝ) 5) :
    |fiveSizeFiniteEntropy alpha T - dualValue S5 T| ≤ eps := by
  have hm := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT)
  have hbdd5 := bddBelow_fiveSizeFiniteDual hscore hT
  have hbddLim := bddBelow_dual S4_subset_S5 hm
  rw [abs_le]
  constructor
  · -- `dualValue S5 T - eps ≤ fiveSizeFiniteEntropy alpha T`
    suffices dualValue S5 T - eps ≤ fiveSizeFiniteEntropy alpha T by linarith
    refine le_ciInf fun l ↦ ?_
    have h1 : dualValue S5 T ≤ Real.log (partitionFn S5 l) - l * T :=
      ciInf_le hbddLim l
    have h2 := (log_fiveSizeFinitePartition_bounds hscore l).1
    linarith
  · -- `fiveSizeFiniteEntropy alpha T ≤ dualValue S5 T + eps`
    suffices fiveSizeFiniteEntropy alpha T - eps ≤ dualValue S5 T by linarith
    refine le_ciInf fun l ↦ ?_
    have h1 : fiveSizeFiniteEntropy alpha T ≤
        Real.log (fiveSizeFinitePartition alpha l) - l * T := ciInf_le hbdd5 l
    have h2 := (log_fiveSizeFinitePartition_bounds hscore l).2
    linarith

/-- Concavity and continuity of `fiveSizeFiniteEntropy alpha` on `[9/4, 17/4]`
once the score error is at most `1`. -/
theorem continuousOn_fiveSizeFiniteEntropy_Icc {alpha : ℕ}
    (hscore : ∀ i : Fin 5, |fiveDeficitScore alpha i - fiveGaussianScore i| ≤ 1) :
    ContinuousOn (fiveSizeFiniteEntropy alpha) (Icc (9 / 4 : ℝ) (17 / 4)) := by
  have hconc : ∀ {T₁ T₂ a b : ℝ}, T₁ ∈ Ioo (2 : ℝ) 5 → T₂ ∈ Ioo (2 : ℝ) 5 →
      0 ≤ a → 0 ≤ b → a + b = 1 →
      a * fiveSizeFiniteEntropy alpha T₁ + b * fiveSizeFiniteEntropy alpha T₂ ≤
        fiveSizeFiniteEntropy alpha (a * T₁ + b * T₂) := by
    intro T₁ T₂ a b hT₁ hT₂ ha hb hab
    have hb1 := bddBelow_fiveSizeFiniteDual hscore hT₁
    have hb2 := bddBelow_fiveSizeFiniteDual hscore hT₂
    refine le_ciInf fun l ↦ ?_
    show _ ≤ Real.log (fiveSizeFinitePartition alpha l) - l * (a * T₁ + b * T₂)
    have e1 := mul_le_mul_of_nonneg_left (ciInf_le hb1 l) ha
    have e2 := mul_le_mul_of_nonneg_left (ciInf_le hb2 l) hb
    calc a * fiveSizeFiniteEntropy alpha T₁ + b * fiveSizeFiniteEntropy alpha T₂
        ≤ a * (Real.log (fiveSizeFinitePartition alpha l) - l * T₁) +
            b * (Real.log (fiveSizeFinitePartition alpha l) - l * T₂) := add_le_add e1 e2
      _ = (a + b) * Real.log (fiveSizeFinitePartition alpha l) - l * (a * T₁ + b * T₂) := by ring
      _ = Real.log (fiveSizeFinitePartition alpha l) - l * (a * T₁ + b * T₂) := by
            rw [hab, one_mul]
  set U0 : ℝ := Real.log (partitionFn Splus 0) + 1
  set L0 : ℝ := min (Real.log (fourPartY (1 / 4)) -
        FiveSizePhaseGainSharp.yTilt (1 / 4) * fourMeanY (1 / 4))
      (Real.log (fourPartY 32) -
        FiveSizePhaseGainSharp.yTilt 32 * fourMeanY 32) - 1
  have hbds : ∀ {T : ℝ}, T ∈ Icc (17 / 8 : ℝ) (35 / 8) →
      L0 ≤ fiveSizeFiniteEntropy alpha T ∧ fiveSizeFiniteEntropy alpha T ≤ U0 := by
    intro T hT
    have hT25 : T ∈ Ioo (2 : ℝ) 5 := ⟨by linarith [hT.1], by linarith [hT.2]⟩
    have hcmp := abs_le.mp (abs_fiveSizeFiniteEntropy_sub_dualValue_le hscore hT25)
    -- Bound `dualValue S5 T` via `dualValue S4 T ≤ dualValue S5 T ≤ Real.log (partitionFn Splus 0)`
    have hm := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
    have hup : dualValue S5 T ≤ Real.log (partitionFn Splus 0) := by
      have h0 := dualValue_le_at S4_subset_S5 hm 0
      have hpos : 0 < partitionFn S5 0 := by
        rw [partitionFn_S5]; exact sum_gaussWeight_pos F5 F5_nonempty 0
      linarith [Real.log_le_log hpos (partitionFn_mono S5_subset_Splus 0)]
    have hbr : fourMeanY (1 / 4) ≤ 17 / 8 ∧ (35 / 8 : ℝ) ≤ fourMeanY 32 ∧
        fourMeanY (1 / 4) < fourMeanY 32 := by
      unfold fourMeanY fourFirstY fourPartY; norm_num
    have h4 := four_dual_interp (ya := 1 / 4) (yb := 32) (by norm_num) (by norm_num)
      (hbr.1.trans hT.1) (hT.2.trans hbr.2.1) hbr.2.2
    have hD : 0 < fourMeanY 32 - fourMeanY (1 / 4) := by linarith [hbr.2.2]
    have hLa : L0 + 1 ≤ Real.log (fourPartY (1 / 4)) -
        FiveSizePhaseGainSharp.yTilt (1 / 4) * fourMeanY (1 / 4) := by
      dsimp [L0]; linarith [min_le_left
        (Real.log (fourPartY (1 / 4)) - FiveSizePhaseGainSharp.yTilt (1 / 4) * fourMeanY (1 / 4))
        (Real.log (fourPartY 32) - FiveSizePhaseGainSharp.yTilt 32 * fourMeanY 32)]
    have hLb : L0 + 1 ≤ Real.log (fourPartY 32) -
        FiveSizePhaseGainSharp.yTilt 32 * fourMeanY 32 := by
      dsimp [L0]; linarith [min_le_right
        (Real.log (fourPartY (1 / 4)) - FiveSizePhaseGainSharp.yTilt (1 / 4) * fourMeanY (1 / 4))
        (Real.log (fourPartY 32) - FiveSizePhaseGainSharp.yTilt 32 * fourMeanY 32)]
    have hα : 0 ≤ fourMeanY 32 - T := by linarith [hT.2, hbr.2.1]
    have hβ : 0 ≤ T - fourMeanY (1 / 4) := by linarith [hT.1, hbr.1]
    have hLmul : (L0 + 1) * (fourMeanY 32 - fourMeanY (1 / 4)) ≤
        dualValue S4 T * (fourMeanY 32 - fourMeanY (1 / 4)) := by
      have e1 := mul_le_mul_of_nonneg_left hLa hα
      have e2 := mul_le_mul_of_nonneg_left hLb hβ
      linarith
    have hlo : L0 + 1 ≤ dualValue S5 T :=
      (le_of_mul_le_mul_right hLmul hD).trans (dualValue_mono subset_rfl S4_subset_S5 hm)
    exact ⟨by linarith [hcmp.1], by dsimp [U0]; linarith [hcmp.2, hup]⟩
  set Mspan : ℝ := U0 - L0
  have hMspan : 0 ≤ Mspan := by
    have h3 := hbds (T := 3) (by norm_num)
    dsimp [Mspan]; linarith [h3.1, h3.2]
  rw [Metric.continuousOn_iff]
  intro x hx eps heps
  let K : ℝ := 8 * Mspan + 1
  have hKpos : 0 < K := by dsimp [K]; linarith
  refine ⟨eps / K, div_pos heps hKpos, fun y hy hdist ↦ ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have step : ∀ {u v : ℝ}, u ∈ Icc (9 / 4 : ℝ) (17 / 4) →
      v ∈ Icc (9 / 4 : ℝ) (17 / 4) → u ≤ v →
      fiveSizeFiniteEntropy alpha v - fiveSizeFiniteEntropy alpha u ≤ 8 * Mspan * (v - u) ∧
      fiveSizeFiniteEntropy alpha u - fiveSizeFiniteEntropy alpha v ≤ 8 * Mspan * (v - u) := by
    intro u v hu hv huv
    have hu25 : u ∈ Ioo (2 : ℝ) 5 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hv25 : v ∈ Ioo (2 : ℝ) 5 := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hul : u - 1 / 8 ∈ Icc (17 / 8 : ℝ) (35 / 8) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hvr : v + 1 / 8 ∈ Icc (17 / 8 : ℝ) (35 / 8) := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hul25 : u - 1 / 8 ∈ Ioo (2 : ℝ) 5 := ⟨by linarith [hul.1], by linarith [hul.2]⟩
    have hvr25 : v + 1 / 8 ∈ Ioo (2 : ℝ) 5 := ⟨by linarith [hvr.1], by linarith [hvr.2]⟩
    have hbu := hbds (T := u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hbv := hbds (T := v) ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hbul := hbds hul
    have hbvr := hbds hvr
    set D : ℝ := 1 / 8 + (v - u)
    have hDpos : 0 < D := by dsimp [D]; linarith
    have ha : 0 ≤ (1 / 8 : ℝ) / D := div_nonneg (by norm_num) hDpos.le
    have hb : 0 ≤ (v - u) / D := div_nonneg (by linarith) hDpos.le
    have hab : (1 / 8 : ℝ) / D + (v - u) / D = 1 := by rw [← add_div, div_self hDpos.ne']
    constructor
    · have hcomb : (1 / 8 : ℝ) / D * v + (v - u) / D * (u - 1 / 8) = u := by
        apply mul_right_cancel₀ hDpos.ne'
        have h1 : (1 / 8 : ℝ) / D * D = 1 / 8 := div_mul_cancel₀ _ hDpos.ne'
        have h2 : (v - u) / D * D = v - u := div_mul_cancel₀ _ hDpos.ne'
        calc ((1 / 8 : ℝ) / D * v + (v - u) / D * (u - 1 / 8)) * D
            = ((1 / 8 : ℝ) / D * D) * v + ((v - u) / D * D) * (u - 1 / 8) := by ring
          _ = (1 / 8) * v + (v - u) * (u - 1 / 8) := by rw [h1, h2]
          _ = u * D := by dsimp [D]; ring
      have hc := hconc hv25 hul25 ha hb hab
      rw [hcomb] at hc
      have hdiv : ((1 / 8 : ℝ) * fiveSizeFiniteEntropy alpha v +
          (v - u) * fiveSizeFiniteEntropy alpha (u - 1 / 8)) / D ≤
          fiveSizeFiniteEntropy alpha u := by
        rwa [add_div, mul_div_right_comm, mul_div_right_comm]
      have hmul := (div_le_iff₀ hDpos).mp hdiv
      dsimp [D] at hmul
      have hsp : fiveSizeFiniteEntropy alpha u - fiveSizeFiniteEntropy alpha (u - 1 / 8) ≤ Mspan := by
        dsimp [Mspan]; linarith [hbu.2, hbul.1]
      have hpr := mul_le_mul_of_nonneg_left hsp (by linarith : 0 ≤ v - u)
      linarith
    · have hcomb : (1 / 8 : ℝ) / D * u + (v - u) / D * (v + 1 / 8) = v := by
        apply mul_right_cancel₀ hDpos.ne'
        have h1 : (1 / 8 : ℝ) / D * D = 1 / 8 := div_mul_cancel₀ _ hDpos.ne'
        have h2 : (v - u) / D * D = v - u := div_mul_cancel₀ _ hDpos.ne'
        calc ((1 / 8 : ℝ) / D * u + (v - u) / D * (v + 1 / 8)) * D
            = ((1 / 8 : ℝ) / D * D) * u + ((v - u) / D * D) * (v + 1 / 8) := by ring
          _ = (1 / 8) * u + (v - u) * (v + 1 / 8) := by rw [h1, h2]
          _ = v * D := by dsimp [D]; ring
      have hc := hconc hu25 hvr25 ha hb hab
      rw [hcomb] at hc
      have hdiv : ((1 / 8 : ℝ) * fiveSizeFiniteEntropy alpha u +
          (v - u) * fiveSizeFiniteEntropy alpha (v + 1 / 8)) / D ≤
          fiveSizeFiniteEntropy alpha v := by
        rwa [add_div, mul_div_right_comm, mul_div_right_comm]
      have hmul := (div_le_iff₀ hDpos).mp hdiv
      dsimp [D] at hmul
      have hsp : fiveSizeFiniteEntropy alpha v - fiveSizeFiniteEntropy alpha (v + 1 / 8) ≤ Mspan := by
        dsimp [Mspan]; linarith [hbv.2, hbvr.1]
      have hpr := mul_le_mul_of_nonneg_left hsp (by linarith : 0 ≤ v - u)
      linarith
  have hlip : |fiveSizeFiniteEntropy alpha y - fiveSizeFiniteEntropy alpha x| ≤
      8 * Mspan * |y - x| := by
    rcases le_total y x with hyx | hxy
    · obtain ⟨h1, h2⟩ := step hy hx hyx
      rw [abs_sub_comm y x, abs_of_nonneg (sub_nonneg.mpr hyx), abs_le]
      exact ⟨by linarith, by linarith⟩
    · obtain ⟨h1, h2⟩ := step hx hy hxy
      have habs : |y - x| = y - x := abs_of_nonneg (sub_nonneg.mpr hxy)
      rw [habs, abs_le]
      exact ⟨by linarith, by linarith⟩
  have h1 : 8 * Mspan * |y - x| ≤ K * |y - x| := by
    dsimp [K]; linarith [abs_nonneg (y - x)]
  have h2 : K * |y - x| < K * (eps / K) := mul_lt_mul_of_pos_left hdist hKpos
  rw [mul_div_cancel₀ _ hKpos.ne'] at h2
  linarith

/-! ## 2. Genuine five-size phase objectives and concrete corridor roots `r₅^co(n)`, `r₅(n)` -/

/-- The manuscript's five-size phase objective `𝓛_{S₅}(n, s) + τ s` (`τ = log 2`
for marked five-size cocolourings `r₅^co`, `τ = 0` for five-size colourings `r₅`). -/
def fiveSizePhaseObjective (n : ℕ) (tau s : ℝ) : ℝ :=
  (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
    s * (profileDeficitAffineA (phaseNat n) +
      profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
      fiveSizeFiniteEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s) + tau)

/-- Exact identity `(3.8)` relating `fiveSizePhaseObjective` and `unrestrictedPhaseObjective`. -/
theorem fiveSizePhaseObjective_eq_unrestricted_add_margin
    (n : ℕ) (tau : ℝ) {s : ℝ} (hs : s ≠ 0) :
    fiveSizePhaseObjective n tau s =
      unrestrictedPhaseObjective n s +
        s * (tau -
          finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s) +
          fiveSizeFiniteEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s)) := by
  have h := unrestrictedPhaseObjective_div_eq_deficitCentered n hs
  have hmul := (div_eq_iff hs).mp h
  unfold profileDeficitTarget at hmul
  unfold fiveSizePhaseObjective finiteUnrestrictedDeficitEntropy fourSizeTarget
  rw [hmul]
  have hd1 : (n : ℝ) * Real.log (n : ℝ) / s * s = (n : ℝ) * Real.log (n : ℝ) :=
    div_mul_cancel₀ _ hs
  have hd2 : (n : ℝ) / s * s = (n : ℝ) := div_mul_cancel₀ _ hs
  calc (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
        s * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * ((phaseNat n : ℝ) - (n : ℝ) / s) +
          fiveSizeFiniteEntropy (phaseNat n) ((phaseNat n : ℝ) - (n : ℝ) / s) + tau)
      = ((n : ℝ) * Real.log (n : ℝ) / s * s) - ((n : ℝ) / s * s) + s - s * Real.log s +
          s * (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * ((phaseNat n : ℝ) - (n : ℝ) / s) +
            fiveSizeFiniteEntropy (phaseNat n) ((phaseNat n : ℝ) - (n : ℝ) / s) + tau) := by
        rw [hd1, hd2]
    _ = _ := by ring

/-- Bounds on a near-minimizing tilt `l` of `fiveSizeFiniteEntropy` on `[9/4, 17/4]`. -/
private theorem abs_tilt_and_linear_lower_of_fiveSizeFiniteDual_le
    {alpha : ℕ}
    (hscore : ∀ i : Fin 5, |fiveDeficitScore alpha i - fiveGaussianScore i| ≤ 1)
    {T l U : ℝ} (hT : T ∈ Icc (9 / 4 : ℝ) (17 / 4))
    (hl : Real.log (fiveSizeFinitePartition alpha l) - l * T ≤ U) :
    let M := max 0 (max (4 * (U + 1 - fiveGaussianScore 0))
                        (U + 1 - fiveGaussianScore 4))
    |l| ≤ M ∧
      -M * ((alpha : ℝ) + 2) + fiveGaussianScore 0 - 1 ≤
        Real.log (fiveSizeFinitePartition alpha l) - l * (alpha : ℝ) := by
  intro M
  have h0le : Real.exp (l * (fiveDeficit 0 : ℝ) + fiveDeficitScore alpha 0) ≤
      fiveSizeFinitePartition alpha l := by
    unfold fiveSizeFinitePartition
    exact Finset.single_le_sum
      (f := fun i : Fin 5 ↦ Real.exp (l * (fiveDeficit i : ℝ) + fiveDeficitScore alpha i))
      (fun _ _ ↦ (Real.exp_pos _).le) (Finset.mem_univ (0 : Fin 5))
  have h0log : l * 2 + fiveDeficitScore alpha 0 ≤ Real.log (fiveSizeFinitePartition alpha l) := by
    have h := Real.log_le_log (Real.exp_pos _) h0le
    rw [Real.log_exp] at h; unfold fiveDeficit at h; norm_num at h; exact h
  have h4le : Real.exp (l * (fiveDeficit 4 : ℝ) + fiveDeficitScore alpha 4) ≤
      fiveSizeFinitePartition alpha l := by
    unfold fiveSizeFinitePartition
    exact Finset.single_le_sum
      (f := fun i : Fin 5 ↦ Real.exp (l * (fiveDeficit i : ℝ) + fiveDeficitScore alpha i))
      (fun _ _ ↦ (Real.exp_pos _).le) (Finset.mem_univ (4 : Fin 5))
  have h4log : l * 6 + fiveDeficitScore alpha 4 ≤ Real.log (fiveSizeFinitePartition alpha l) := by
    have h := Real.log_le_log (Real.exp_pos _) h4le
    rw [Real.log_exp] at h; unfold fiveDeficit at h; norm_num at h; exact h
  have hs0 : fiveGaussianScore 0 - 1 ≤ fiveDeficitScore alpha 0 := by
    linarith [(abs_le.mp (hscore 0)).1]
  have hs4 : fiveGaussianScore 4 - 1 ≤ fiveDeficitScore alpha 4 := by
    linarith [(abs_le.mp (hscore 4)).1]
  have hM1 : 4 * (U + 1 - fiveGaussianScore 0) ≤ M :=
    (le_max_left _ _).trans (le_max_right 0 _)
  have hM2 : U + 1 - fiveGaussianScore 4 ≤ M :=
    (le_max_right _ _).trans (le_max_right 0 _)
  have habs : |l| ≤ M := by
    rcases le_total l 0 with hl0 | hl0
    · rw [abs_of_nonpos hl0]
      have hmul : l * T ≤ l * (9 / 4) := mul_le_mul_of_nonpos_left hT.1 hl0
      linarith
    · rw [abs_of_nonneg hl0]
      have hmul : l * T ≤ l * (17 / 4) := mul_le_mul_of_nonneg_left hT.2 hl0
      linarith
  have hlA : l * (alpha : ℝ) ≤ M * (alpha : ℝ) :=
    mul_le_mul_of_nonneg_right (abs_le.mp habs).2 (Nat.cast_nonneg alpha)
  refine ⟨habs, ?_⟩
  linarith [(abs_le.mp habs).1]

private theorem hasDerivAt_branchObjective (c m : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun x : ℝ ↦ c + x - x * Real.log x + m * x) (-Real.log s + m) s := by
  have hTotal := (((hasDerivAt_const s c).add (hasDerivAt_id s)).sub
    ((hasDerivAt_id s).mul (Real.hasDerivAt_log hs.ne'))).add
    ((hasDerivAt_id s).const_mul m)
  have hObj := hTotal.congr_of_eventuallyEq
    (f₁ := fun x : ℝ ↦ c + x - x * Real.log x + m * x)
    (Filter.Eventually.of_forall fun x ↦ by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq])
  apply hObj.congr_deriv
  dsimp only [id_eq]
  rw [mul_inv_cancel₀ hs.ne']
  ring

/-- **Strict monotonicity of `fiveSizePhaseObjective` across every fixed log-log corridor:**
for every `C ≥ 0`, eventually for all `τ ∈ [0, log 2]`, `fiveSizePhaseObjective n τ`
is strictly increasing on `[c_n - C Δ_n, c_n + C Δ_n]`. -/
theorem eventually_fiveSizePhaseObjective_strictMonoOn_logLogCorridor
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      ∀ tau ∈ Icc (0 : ℝ) q,
        StrictMonoOn (fiveSizePhaseObjective n tau)
          (Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
               (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n)) := by
  obtain ⟨K, hKnn, hKlog⟩ := eventually_corridor_abs_log_linear C hC
  obtain ⟨N5, hN5⟩ := eventually_uniform_fiveDeficitScore 1 zero_lt_one
  set Uent : ℝ := |Real.log (partitionFn Splus 0)| + 2
  set Ml : ℝ := max 0 (max (4 * (Uent + 1 - fiveGaussianScore 0))
                            (Uent + 1 - fiveGaussianScore 4))
  have hMlnn : 0 ≤ Ml := le_max_left 0 _
  let C0 : ℝ := q + 5 + 2 * Ml + |fiveGaussianScore 0|
  let C1 : ℝ := K + Ml
  have hC0pos : 0 < C0 := by dsimp [C0]; linarith [q_pos, abs_nonneg (fiveGaussianScore 0)]
  have hC1nn : 0 ≤ C1 := add_nonneg hKnn hMlnn
  have hphaseN5 : ∀ᶠ n : ℕ in atTop, N5 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (N5 : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  have hphaseBig : ∀ᶠ n : ℕ in atTop, 4 * (C0 + C1) / q + 1 ≤ (phaseNat n : ℝ) := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (4 * (C0 + C1) / q + 1),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact hn.trans hph.1
  filter_upwards
    [hKlog, hphaseN5, hphaseBig,
      eventually_phaseRootLogLogCorridor_fourSize_domain C hC,
      eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hC,
      eventually_five_lt_phaseNat] with
      n hLogN hN5le hBig hDom hTarget hfive tau htau s₁ hs₁ s₂ hs₂ hlt
  set a : ℝ := (phaseNat n : ℝ)
  have haSix : (6 : ℝ) ≤ a := by
    change (6 : ℝ) ≤ (phaseNat n : ℝ); exact_mod_cast (Nat.succ_le_of_lt hfive)
  have haPos : 0 < a := by linarith
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
  have hs₁pos : 0 < s₁ := (hDom s₁ hs₁).1
  have hs₂pos : 0 < s₂ := (hDom s₂ hs₂).1
  set T₁ : ℝ := fourSizeTarget n (phaseNat n) s₁
  set T₂ : ℝ := fourSizeTarget n (phaseNat n) s₂
  have hTK₁ : T₁ ∈ Icc (9 / 4 : ℝ) (17 / 4) := hTarget s₁ hs₁
  have hTK₂ : T₂ ∈ Icc (9 / 4 : ℝ) (17 / 4) := hTarget s₂ hs₂
  have hT₁25 : T₁ ∈ Ioo (2 : ℝ) 5 := ⟨by linarith [hTK₁.1], by linarith [hTK₁.2]⟩
  have hT₂25 : T₂ ∈ Ioo (2 : ℝ) 5 := ⟨by linarith [hTK₂.1], by linarith [hTK₂.2]⟩
  have hscore5 : ∀ i : Fin 5, |fiveDeficitScore (phaseNat n) i - fiveGaussianScore i| ≤ 1 :=
    fun i ↦ (hN5 (phaseNat n) hN5le i).le
  have hent₂ : fiveSizeFiniteEntropy (phaseNat n) T₂ ≤ Uent - 1 := by
    have hcmp := (abs_le.mp (abs_fiveSizeFiniteEntropy_sub_dualValue_le hscore5 hT₂25)).2
    have hm := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT₂25)
    have h0 := dualValue_le_at S4_subset_S5 hm 0
    have hpos5 : 0 < partitionFn S5 0 := by
      rw [partitionFn_S5]; exact sum_gaussWeight_pos F5 F5_nonempty 0
    have h5hi : dualValue S5 T₂ ≤ |Real.log (partitionFn Splus 0)| := by
      linarith [Real.log_le_log hpos5 (partitionFn_mono S5_subset_Splus 0),
        le_abs_self (Real.log (partitionFn Splus 0))]
    dsimp [Uent]; linarith
  set δ : ℝ := min 1 ((q / 8 * a ^ 2) * (s₂ - s₁) / s₂)
  have hδpos : 0 < δ := lt_min zero_lt_one
    (div_pos (mul_pos (mul_pos (div_pos q_pos (by norm_num)) haSqPos) (sub_pos.mpr hlt)) hs₂pos)
  have hδle1 : δ ≤ 1 := min_le_left _ _
  have hs₂δ : s₂ * δ ≤ (q / 8 * a ^ 2) * (s₂ - s₁) := by
    have h := mul_le_mul_of_nonneg_left (min_le_right 1 ((q / 8 * a ^ 2) * (s₂ - s₁) / s₂)) hs₂pos.le
    rwa [mul_div_cancel₀ _ hs₂pos.ne'] at h
  obtain ⟨l, hlLt⟩ := exists_lt_of_ciInf_lt
    (lt_add_of_pos_right (fiveSizeFiniteEntropy (phaseNat n) T₂) hδpos)
  have hlU : Real.log (fiveSizeFinitePartition (phaseNat n) l) - l * T₂ ≤ Uent := by linarith
  have hLinLo : -Ml * (a + 2) + fiveGaussianScore 0 - 1 ≤
      Real.log (fiveSizeFinitePartition (phaseNat n) l) - l * a :=
    (abs_tilt_and_linear_lower_of_fiveSizeFiniteDual_le hscore5 hTK₂ hlU).2
  set m_slope : ℝ := profileDeficitAffineA (phaseNat n) + profileDeficitAffineB (phaseNat n) * a +
    tau + Real.log (fiveSizeFinitePartition (phaseNat n) l) - l * a
  set c_const : ℝ := (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) +
    (l - profileDeficitAffineB (phaseNat n)) * (n : ℝ)
  set g : ℝ → ℝ := fun x ↦ c_const + x - x * Real.log x + m_slope * x
  have g_eq : ∀ {x : ℝ}, x ≠ 0 →
      g x = (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + x - x * Real.log x +
        x * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) x +
          (Real.log (fiveSizeFinitePartition (phaseNat n) l) -
            l * fourSizeTarget n (phaseNat n) x) + tau) := by
    intro x hx
    have hnx : x * ((n : ℝ) / x) = (n : ℝ) := mul_div_cancel₀ _ hx
    dsimp [g, c_const, m_slope, a]
    unfold fourSizeTarget
    calc (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (l - profileDeficitAffineB (phaseNat n)) * (n : ℝ) +
          x - x * Real.log x +
          (profileDeficitAffineA (phaseNat n) + profileDeficitAffineB (phaseNat n) * (phaseNat n : ℝ) +
            tau + Real.log (fiveSizeFinitePartition (phaseNat n) l) - l * (phaseNat n : ℝ)) * x
        = (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (l - profileDeficitAffineB (phaseNat n)) * (x * ((n : ℝ) / x)) +
            x - x * Real.log x +
            (profileDeficitAffineA (phaseNat n) + profileDeficitAffineB (phaseNat n) * (phaseNat n : ℝ) +
              tau + Real.log (fiveSizeFinitePartition (phaseNat n) l) - l * (phaseNat n : ℝ)) * x := by
          rw [hnx]
      _ = _ := by ring
  have hAt1 : fiveSizePhaseObjective n tau s₁ ≤ g s₁ := by
    rw [g_eq hs₁pos.ne']; unfold fiveSizePhaseObjective
    have hle1 : fiveSizeFiniteEntropy (phaseNat n) T₁ ≤
        Real.log (fiveSizeFinitePartition (phaseNat n) l) - l * T₁ :=
      ciInf_le (bddBelow_fiveSizeFiniteDual hscore5 hT₁25) l
    have hm1 := mul_le_mul_of_nonneg_left hle1 hs₁pos.le
    dsimp [T₁] at hm1; linarith
  have hAt2 : g s₂ - s₂ * δ < fiveSizePhaseObjective n tau s₂ := by
    rw [g_eq hs₂pos.ne']; unfold fiveSizePhaseObjective
    have hm2 := mul_lt_mul_of_pos_left hlLt hs₂pos
    dsimp [T₂] at hm2; linarith
  -- Affine core & slope lower bound on `[s₁, s₂]`
  have hAff : q / 2 * a ^ 2 - 4 ≤
      profileDeficitAffineA (phaseNat n) + profileDeficitAffineB (phaseNat n) * a := by
    have hcore := (abs_le.mp (abs_profileDeficitAffineCore_sub_quadratic_le (phaseNat n) (by omega))).1
    have hfac : factorialLogErrorBound (phaseNat n) ≤ a + 4 := by
      have h := Real.log_le_sub_one_of_pos (x := ((phaseNat n + 1 : ℕ) : ℝ)) (by positivity)
      have hEq : factorialLogErrorBound (phaseNat n) = Real.log ((phaseNat n + 1 : ℕ) : ℝ) + 4 := rfl
      rw [hEq]; push_cast at h ⊢; linarith
    dsimp [a] at hfac ⊢; linarith
  have hRemLe : C0 + C1 * a ≤ q / 4 * a ^ 2 := by
    have h1 : 4 * (C0 + C1) ≤ a * q := (div_le_iff₀ q_pos).mp (by linarith [hBig])
    have h2 : C0 + C1 * a ≤ (C0 + C1) * a := by
      have hc0a : C0 ≤ C0 * a := by
        calc C0 = C0 * 1 := (mul_one C0).symm
          _ ≤ C0 * a := mul_le_mul_of_nonneg_left (by linarith) hC0pos.le
      linarith
    have h3 : 4 * (C0 + C1) * a ≤ (a * q) * a :=
      mul_le_mul_of_nonneg_right h1 haPos.le
    linarith [show 4 * ((C0 + C1) * a) = 4 * (C0 + C1) * a by ring,
      show (a * q) * a = 4 * (q / 4 * a ^ 2) by ring]
  have hSubIcc : Icc s₁ s₂ ⊆ Icc
      (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) :=
    fun x hx ↦ ⟨hs₁.1.trans hx.1, hx.2.trans hs₂.2⟩
  have hHasDerivG : ∀ x ∈ Icc s₁ s₂, HasDerivAt g (-Real.log x + m_slope) x :=
    fun x hx ↦ hasDerivAt_branchObjective c_const m_slope (lt_of_lt_of_le hs₁pos hx.1)
  have hContG : ContinuousOn g (Icc s₁ s₂) :=
    fun x hx ↦ (hHasDerivG x hx).continuousAt.continuousWithinAt
  have hDiffG : DifferentiableOn ℝ g (Ioo s₁ s₂) :=
    fun x hx ↦ (hHasDerivG x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
  have hSlopeG : ∀ x ∈ Ioo s₁ s₂, q / 4 * a ^ 2 ≤ deriv g x := by
    intro x hx
    have hxIcc := Ioo_subset_Icc_self hx
    rw [(hHasDerivG x hxIcc).deriv]
    have hlogx := (abs_le.mp (hLogN x (hSubIcc hxIcc))).2
    have hfg : -|fiveGaussianScore 0| ≤ fiveGaussianScore 0 := neg_abs_le _
    dsimp [m_slope, C0, C1] at hRemLe ⊢
    linarith [htau.1]
  have hIncG := derivative_lower_bound_mul_sub_le_sub hlt.le hContG hDiffG hSlopeG
  have hPosGain : 0 < (q / 8 * a ^ 2) * (s₂ - s₁) :=
    mul_pos (mul_pos (div_pos q_pos (by norm_num)) haSqPos) (sub_pos.mpr hlt)
  linarith

/-- Eventual existence and uniqueness of zeros of `fiveSizePhaseObjective n tau`
in a fixed open log-log corridor for every `tau ∈ [0, log 2]` (Lemma 3.1). -/
theorem exists_pos_eventually_existsUnique_fiveSizePhaseObjective_zero_logLogCorridor :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ tau ∈ Icc (0 : ℝ) q,
          ∃! r : ℝ,
            r ∈ Ioo
                (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) ∧
              fiveSizePhaseObjective n tau r = 0 := by
  obtain ⟨B, hBpos, hB⟩ :=
    unrestrictedPhaseObjective_center_div_isBigO_logLogOrder.exists_pos
  have hAlow : (-1 : ℝ) < 9 / 4 := by norm_num
  have hAB : (9 / 4 : ℝ) ≤ 17 / 4 := by norm_num
  obtain ⟨Mtilt, hMtiltnn, huniformTilt⟩ :=
    exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le hAlow hAB
  obtain ⟨Ntilt, hNtilt⟩ := eventually_atTop.1 huniformTilt
  obtain ⟨N5, hN5⟩ := eventually_uniform_fiveDeficitScore 1 zero_lt_one
  let C : ℝ := 16 * (B + 2) / q
  have hCpos : 0 < C := div_pos (mul_pos (by norm_num) (by linarith)) q_pos
  refine ⟨C, hCpos, ?_⟩
  let Gbound : ℝ := q + 5 * Mtilt + |Real.log (partitionFn Splus 0)| +
    (|min (Real.log (fourPartY (1 / 4)) -
        FiveSizePhaseGainSharp.yTilt (1 / 4) * fourMeanY (1 / 4))
      (Real.log (fourPartY 32) -
        FiveSizePhaseGainSharp.yTilt 32 * fourMeanY 32)| + 2)
  have hLLBig : ∀ᶠ n : ℕ in atTop, max 1 (2 * Gbound + 1) ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop _
  have hLLC : ∀ᶠ n : ℕ in atTop,
      ‖logLogOrder n‖ ≤ (1 / (64 * (1 + C))) * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound (by positivity)
  have hLogPos : ∀ᶠ n : ℕ in atTop, 0 < logOrder n :=
    tendsto_logOrder_atTop.eventually_gt_atTop 0
  have hphaseN : ∀ᶠ n : ℕ in atTop, max Ntilt N5 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop ((max Ntilt N5 : ℕ) : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  filter_upwards
    [hB.bound, hLLBig, hLLC, hLogPos, hphaseN,
      eventually_fiveSizePhaseObjective_strictMonoOn_logLogCorridor C hCpos.le,
      eventually_phaseRootLogLogCorridor_fourSize_domain C hCpos.le,
      eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hCpos.le,
      eventually_unrestrictedPhaseObjective_deriv_logLogCorridor_lower C hCpos.le,
      eventually_phaseRoot_domain_pos_and_target_corridor,
      eventually_five_lt_phaseNat,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
      n hcenterBound hLL hllc hpos hphN hStrict5 hdomain htarget hderiv hcenterDom hfive hphase
      tau htau
  set s0 : ℝ := phaseRootCenter n
  set a : ℝ := (phaseNat n : ℝ)
  set Delta : ℝ := C * logLogOrder n * phaseRootGapRadius n
  have hLL1 : 1 ≤ logLogOrder n := (le_max_left _ _).trans hLL
  have hLLG : 2 * Gbound + 1 ≤ logLogOrder n := (le_max_right _ _).trans hLL
  have hLLPos : 0 < logLogOrder n := lt_of_lt_of_le zero_lt_one hLL1
  have hs0Pos : 0 < s0 :=
    div_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hcenterDom.1.1)) hcenterDom.2.1
  have haPos : 0 < a := Nat.cast_pos.mpr (lt_trans (by omega : 0 < 5) hfive)
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
  have hDeltaPos : 0 < Delta :=
    mul_pos (mul_pos hCpos hLLPos) (div_pos hs0Pos haSqPos)
  -- `Delta ≤ s0 / 2`, so every `s ∈ [s0 - Delta, s0 + Delta]` satisfies `0 < s ≤ 2 * s0`
  rw [Real.norm_eq_abs, abs_of_pos hLLPos, Real.norm_eq_abs, abs_of_pos hpos] at hllc
  have hDeltaHalf : Delta ≤ s0 / 2 := by
    have h1 : C * logLogOrder n ≤ (1 + C) * logLogOrder n :=
      mul_le_mul_of_nonneg_right (by linarith) hLLPos.le
    have h2 : (1 + C) * logLogOrder n ≤ logOrder n / 64 := by
      have hm := mul_le_mul_of_nonneg_left hllc (by linarith : (0 : ℝ) ≤ 1 + C)
      have hs' : (1 + C) * (1 / (64 * (1 + C)) * logOrder n) = logOrder n / 64 := by field_simp
      linarith
    have haSix : (6 : ℝ) ≤ a := by
      change (6 : ℝ) ≤ (phaseNat n : ℝ); exact_mod_cast (Nat.succ_le_of_lt hfive)
    have h3 : C * logLogOrder n ≤ a / 64 := h1.trans (h2.trans (by linarith [hphase.1]))
    have hfrac : C * logLogOrder n / a ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ haSqPos]
      have haa2 : a ≤ a ^ 2 := by
        calc a = a * 1 := (mul_one a).symm
          _ ≤ a * a := mul_le_mul_of_nonneg_left (by linarith) haPos.le
          _ = a ^ 2 := (sq a).symm
      linarith
    have hrew : Delta = s0 * (C * logLogOrder n / a ^ 2) := by
      dsimp [Delta, s0, a]; unfold phaseRootGapRadius; ring
    rw [hrew]
    have hm := mul_le_mul_of_nonneg_left hfrac hs0Pos.le
    linarith
  -- Score bound for `fiveSizeFiniteEntropy`
  have hscore5 : ∀ i : Fin 5, |fiveDeficitScore (phaseNat n) i - fiveGaussianScore i| ≤ 1 :=
    fun i ↦ (hN5 (phaseNat n) ((le_max_right _ _).trans hphN) i).le
  -- Continuity of `fiveSizePhaseObjective n tau` on `[s0 - Delta, s0 + Delta]`
  have hCont5 : ContinuousOn (fiveSizePhaseObjective n tau) (Icc (s0 - Delta) (s0 + Delta)) := by
    have hPosOn : ∀ s ∈ Icc (s0 - Delta) (s0 + Delta), s ≠ 0 :=
      fun s hs ↦ (by linarith [hs.1, hDeltaHalf, hs0Pos] : 0 < s).ne'
    have hTargetCont : ContinuousOn (fourSizeTarget n (phaseNat n))
        (Icc (s0 - Delta) (s0 + Delta)) := by
      unfold fourSizeTarget
      exact continuousOn_const.sub (continuousOn_const.div continuousOn_id hPosOn)
    have hMaps : MapsTo (fourSizeTarget n (phaseNat n))
        (Icc (s0 - Delta) (s0 + Delta)) (Icc (9 / 4 : ℝ) (17 / 4)) :=
      fun s hs ↦ htarget s (by simpa [s0, Delta] using hs)
    have hEntCont := (continuousOn_fiveSizeFiniteEntropy_Icc hscore5).comp hTargetCont hMaps
    unfold fiveSizePhaseObjective
    refine (((continuousOn_const.add continuousOn_id).sub
      (continuousOn_id.mul (continuousOn_id.log hPosOn))).add
      (continuousOn_id.mul (((continuousOn_const.add
        (continuousOn_const.mul hTargetCont)).add hEntCont).add continuousOn_const)))
  -- Uniform bound on the shift `|s * (tau - F_{n,S_+} + F_{n,S_5})| ≤ 2 * s0 * Gbound`
  have hShiftBound : ∀ s ∈ Icc (s0 - Delta) (s0 + Delta),
      |s * (tau - finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s) +
          fiveSizeFiniteEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s))| ≤
        logLogOrder n * s0 := by
    intro s hs
    have hsPos : 0 < s := by linarith [hs.1, hDeltaHalf, hs0Pos]
    have hsLe2 : s ≤ 2 * s0 := by linarith [hs.2, hDeltaHalf]
    set T : ℝ := fourSizeTarget n (phaseNat n) s
    have hTK : T ∈ Icc (9 / 4 : ℝ) (17 / 4) := htarget s (by simpa [s0, Delta] using hs)
    have hT25 : T ∈ Ioo (2 : ℝ) 5 := ⟨by linarith [hTK.1], by linarith [hTK.2]⟩
    -- Bound `finiteUnrestrictedDeficitEntropy`
    have hUnrestHi : finiteUnrestrictedDeficitEntropy (phaseNat n) T ≤
        |Real.log (partitionFn Splus 0)| := by
      have h1 := (finiteProfileDeficitEntropy_le_extendedGaussianEntropyValue
        (phaseNat n) hfive hT25).trans (extendedGaussianEntropyValue_le_dualValue_Splus hT25)
      have hm := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
      have h2 := dualValue_le_at S4_subset_Splus hm 0
      unfold finiteUnrestrictedDeficitEntropy
      linarith [le_abs_self (Real.log (partitionFn Splus 0))]
    have hUnrestLo : -(5 * Mtilt) ≤ finiteUnrestrictedDeficitEntropy (phaseNat n) T := by
      obtain ⟨_, htiltB⟩ := hNtilt (phaseNat n) ((le_max_left _ _).trans hphN) T hTK
      have hp1 := one_le_profileDeficitPartition (phaseNat n) (by omega)
        (profileDeficitTilt (phaseNat n) T)
      have hlognn := Real.log_nonneg hp1
      have hmul : |profileDeficitTilt (phaseNat n) T * T| ≤ 5 * Mtilt := by
        rw [abs_mul, abs_of_pos (by linarith [hTK.1] : 0 < T)]
        have := mul_le_mul htiltB (show T ≤ 5 by linarith [hTK.2]) (by linarith [hTK.1]) hMtiltnn
        linarith
      unfold finiteUnrestrictedDeficitEntropy
      linarith [(abs_le.mp hmul).2]
    -- Bound `fiveSizeFiniteEntropy`
    have h5cmp := abs_le.mp (abs_fiveSizeFiniteEntropy_sub_dualValue_le hscore5 hT25)
    have hm := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
    have h5hi : dualValue S5 T ≤ |Real.log (partitionFn Splus 0)| := by
      have h0 := dualValue_le_at S4_subset_S5 hm 0
      have hpos5 : 0 < partitionFn S5 0 := by
        rw [partitionFn_S5]; exact sum_gaussWeight_pos F5 F5_nonempty 0
      linarith [Real.log_le_log hpos5 (partitionFn_mono S5_subset_Splus 0),
        le_abs_self (Real.log (partitionFn Splus 0))]
    have hbr : fourMeanY (1 / 4) ≤ 17 / 8 ∧ (35 / 8 : ℝ) ≤ fourMeanY 32 ∧
        fourMeanY (1 / 4) < fourMeanY 32 := by
      unfold fourMeanY fourFirstY fourPartY; norm_num
    have hTlo : fourMeanY (1 / 4) ≤ T := by linarith [hbr.1, hTK.1]
    have hThi : T ≤ fourMeanY 32 := by linarith [hbr.2.1, hTK.2]
    have h4 := four_dual_interp (T := T) (ya := 1 / 4) (yb := 32)
      (by norm_num) (by norm_num) hTlo hThi hbr.2.2
    set m0 := min (Real.log (fourPartY (1 / 4)) -
          FiveSizePhaseGainSharp.yTilt (1 / 4) * fourMeanY (1 / 4))
        (Real.log (fourPartY 32) -
          FiveSizePhaseGainSharp.yTilt 32 * fourMeanY 32)
    have hα : 0 ≤ fourMeanY 32 - T := by linarith
    have hβ : 0 ≤ T - fourMeanY (1 / 4) := by linarith
    have hm0a : m0 ≤ Real.log (fourPartY (1 / 4)) -
        FiveSizePhaseGainSharp.yTilt (1 / 4) * fourMeanY (1 / 4) := min_le_left _ _
    have hm0b : m0 ≤ Real.log (fourPartY 32) -
        FiveSizePhaseGainSharp.yTilt 32 * fourMeanY 32 := min_le_right _ _
    have h4mul : m0 * (fourMeanY 32 - fourMeanY (1 / 4)) ≤
        dualValue S4 T * (fourMeanY 32 - fourMeanY (1 / 4)) := by
      have e1 := mul_le_mul_of_nonneg_left hm0a hα
      have e2 := mul_le_mul_of_nonneg_left hm0b hβ
      linarith
    have h5lo : -|m0| ≤ dualValue S5 T := by
      have h1 : m0 ≤ dualValue S4 T := le_of_mul_le_mul_right h4mul (by linarith [hbr.2.2])
      have h2 := dualValue_mono subset_rfl S4_subset_S5 hm
      linarith [neg_abs_le m0]
    have hInnerAbs :
        |tau - finiteUnrestrictedDeficitEntropy (phaseNat n) T +
          fiveSizeFiniteEntropy (phaseNat n) T| ≤ Gbound := by
      rw [abs_le]
      dsimp [Gbound, m0] at h5lo ⊢
      exact ⟨by linarith [htau.1, hUnrestHi, h5cmp.1, h5lo, abs_nonneg m0, q_pos, hMtiltnn],
             by linarith [htau.2, hUnrestLo, h5cmp.2, h5hi, hMtiltnn, abs_nonneg m0]⟩
    rw [abs_mul, abs_of_pos hsPos]
    have hGnn : 0 ≤ Gbound := (abs_nonneg _).trans hInnerAbs
    calc s * |tau - finiteUnrestrictedDeficitEntropy (phaseNat n) T +
            fiveSizeFiniteEntropy (phaseNat n) T|
        ≤ (2 * s0) * Gbound := mul_le_mul hsLe2 hInnerAbs (abs_nonneg _) (by positivity)
      _ = (2 * Gbound) * s0 := by ring
      _ ≤ logLogOrder n * s0 :=
          mul_le_mul_of_nonneg_right (by linarith [hLLG]) hs0Pos.le
  -- Bound `unrestrictedPhaseObjective n` at `s0 - Delta` and `s0 + Delta`
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hLLPos] at hcenterBound
  have hCenterAbs : |unrestrictedPhaseObjective n s0| ≤ B * logLogOrder n * s0 := by
    calc |unrestrictedPhaseObjective n s0|
        = |unrestrictedPhaseObjective n s0 / s0| * s0 := by
          rw [abs_div, abs_of_pos hs0Pos, div_mul_cancel₀ _ hs0Pos.ne']
      _ ≤ (B * logLogOrder n) * s0 := mul_le_mul_of_nonneg_right hcenterBound hs0Pos.le
  have hKeyU : ∀ x ∈ Icc (s0 - Delta) (s0 + Delta),
      HasDerivAt (unrestrictedPhaseObjective n)
        (Real.log (profileDualPartition (phaseNat n + 1)
            (profileDualTilt (phaseNat n + 1) ((n : ℝ) / x))) - Real.log x) x := by
    intro x hx
    obtain ⟨hxpos, htar⟩ := hdomain x (by simpa [s0, Delta] using hx)
    rw [fourSizeTarget, mem_Ioo] at htar
    have hsix : (6 : ℝ) ≤ phaseNat n := by exact_mod_cast (Nat.succ_le_of_lt hfive)
    exact hasDerivAt_profileDualOptimalValue_parts (by omega) hxpos (by
      rw [mem_Ioo, show (((phaseNat n + 1 : ℕ)) : ℝ) = (phaseNat n : ℝ) + 1 by push_cast; ring]
      exact ⟨by linarith [htar.2], by linarith [htar.1]⟩)
  have hContU : ContinuousOn (unrestrictedPhaseObjective n) (Icc (s0 - Delta) (s0 + Delta)) :=
    fun x hx ↦ (hKeyU x hx).continuousAt.continuousWithinAt
  have hDiffU : DifferentiableOn ℝ (unrestrictedPhaseObjective n)
      (Ioo (s0 - Delta) (s0 + Delta)) :=
    fun x hx ↦ (hKeyU x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
  have hDerivLo : ∀ x ∈ Ioo (s0 - Delta) (s0 + Delta),
      q / 8 * a ^ 2 ≤ deriv (unrestrictedPhaseObjective n) x :=
    fun x hx ↦ hderiv x (Ioo_subset_Icc_self (by simpa [s0, Delta] using hx))
  have hProdSlope : (q / 8 * a ^ 2) * Delta = 2 * (B + 2) * logLogOrder n * s0 := by
    dsimp [Delta, C, s0, a]; unfold phaseRootGapRadius
    field_simp [q_ne_zero, haPos.ne']; ring
  have hLeftInc := derivative_lower_bound_mul_sub_le_sub
    (show s0 - Delta ≤ s0 by linarith)
    (hContU.mono fun x hx ↦ ⟨hx.1, hx.2.trans (by linarith)⟩)
    (hDiffU.mono fun x hx ↦ ⟨hx.1, lt_of_lt_of_le hx.2 (by linarith)⟩)
    (fun x hx ↦ hDerivLo x ⟨hx.1, lt_of_lt_of_le hx.2 (by linarith)⟩)
  have hRightInc := derivative_lower_bound_mul_sub_le_sub
    (show s0 ≤ s0 + Delta by linarith)
    (hContU.mono fun x hx ↦ ⟨(by linarith : s0 - Delta ≤ s0).trans hx.1, hx.2⟩)
    (hDiffU.mono fun x hx ↦ ⟨lt_of_le_of_lt (by linarith) hx.1, hx.2⟩)
    (fun x hx ↦ hDerivLo x ⟨lt_of_le_of_lt (by linarith) hx.1, hx.2⟩)
  have hCenterBounds := abs_le.mp hCenterAbs
  have hLeftPos : 0 < s0 - Delta := by linarith [hDeltaHalf, hs0Pos]
  have hRightPos : 0 < s0 + Delta := by linarith [hDeltaPos, hs0Pos]
  have hValLeft : fiveSizePhaseObjective n tau (s0 - Delta) < 0 := by
    rw [fiveSizePhaseObjective_eq_unrestricted_add_margin n tau hLeftPos.ne']
    have hsh := (abs_le.mp (hShiftBound (s0 - Delta) ⟨le_rfl, by linarith⟩)).2
    have hsub : s0 - (s0 - Delta) = Delta := by ring
    rw [hsub, hProdSlope] at hLeftInc
    linarith [hCenterBounds.2, mul_pos hLLPos hs0Pos]
  have hValRight : 0 < fiveSizePhaseObjective n tau (s0 + Delta) := by
    rw [fiveSizePhaseObjective_eq_unrestricted_add_margin n tau hRightPos.ne']
    have hsh := (abs_le.mp (hShiftBound (s0 + Delta) ⟨by linarith, le_rfl⟩)).1
    have hsub : s0 + Delta - s0 = Delta := by ring
    rw [hsub, hProdSlope] at hRightInc
    linarith [hCenterBounds.1, mul_pos hLLPos hs0Pos]
  have hZeroMem : (0 : ℝ) ∈ Icc (fiveSizePhaseObjective n tau (s0 - Delta))
      (fiveSizePhaseObjective n tau (s0 + Delta)) := ⟨hValLeft.le, hValRight.le⟩
  obtain ⟨r, hrMem, hrZero⟩ := intermediate_value_Icc (by linarith : s0 - Delta ≤ s0 + Delta)
    hCont5 hZeroMem
  have hrGt : s0 - Delta < r := lt_of_le_of_ne hrMem.1 fun hEq ↦ by
    rw [← hEq] at hrZero; linarith [hValLeft]
  have hrLt : r < s0 + Delta := lt_of_le_of_ne hrMem.2 fun hEq ↦ by
    rw [hEq] at hrZero; linarith [hValRight]
  have hrOpen : r ∈ Ioo
      (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) := ⟨hrGt, hrLt⟩
  refine ⟨r, ⟨hrOpen, hrZero⟩, fun y hy ↦ ?_⟩
  exact (hStrict5 tau htau).injOn (Ioo_subset_Icc_self hy.1) (Ioo_subset_Icc_self hrOpen)
    (hy.2.trans hrZero.symm)

/-- Corridor coefficient for the five-size roots `r₅^co(n)` and `r₅(n)`. -/
def fiveSizeRootCorridorCoefficient : ℝ :=
  Classical.choose exists_pos_eventually_existsUnique_fiveSizePhaseObjective_zero_logLogCorridor

theorem fiveSizeRootCorridorCoefficient_pos :
    0 < fiveSizeRootCorridorCoefficient :=
  (Classical.choose_spec
    exists_pos_eventually_existsUnique_fiveSizePhaseObjective_zero_logLogCorridor).1

/-- Concrete five-size marked-cocolouring root `r₅^co(n)` (`τ = log 2`), selecting
the unique zero in the open log-log corridor (falling back to `phaseRootCenter n`
on at most finitely many small `n`). -/
def fiveSizeCochromaticRootSelected (n : ℕ) : ℝ := by
  classical
  exact if h : ∃ r : ℝ,
      r ∈ Ioo
          (phaseRootCenter n - fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n + fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n) ∧
        fiveSizePhaseObjective n q r = 0 then
    Classical.choose h
  else
    phaseRootCenter n

/-- Concrete five-size colouring root `r₅(n)` (`τ = 0`), selecting the unique zero
in the open log-log corridor (falling back to `phaseRootCenter n` on at most
finitely many small `n`). -/
def fiveSizeChromaticRootSelected (n : ℕ) : ℝ := by
  classical
  exact if h : ∃ r : ℝ,
      r ∈ Ioo
          (phaseRootCenter n - fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n + fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n) ∧
        fiveSizePhaseObjective n 0 r = 0 then
    Classical.choose h
  else
    phaseRootCenter n

/-- Eventual open-corridor specification and **uniqueness** of `r₅^co(n)` and `r₅(n)`. -/
theorem eventually_fiveSizeRoots_spec_unique :
    ∀ᶠ n : ℕ in atTop,
      ((fiveSizeCochromaticRootSelected n ∈ Ioo
            (phaseRootCenter n -
              fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n)
            (phaseRootCenter n +
              fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n) ∧
          fiveSizePhaseObjective n q (fiveSizeCochromaticRootSelected n) = 0) ∧
        ∀ r : ℝ,
          r ∈ Ioo
              (phaseRootCenter n -
                fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n)
              (phaseRootCenter n +
                fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n) ∧
            fiveSizePhaseObjective n q r = 0 →
          r = fiveSizeCochromaticRootSelected n) ∧
      ((fiveSizeChromaticRootSelected n ∈ Ioo
            (phaseRootCenter n -
              fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n)
            (phaseRootCenter n +
              fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n) ∧
          fiveSizePhaseObjective n 0 (fiveSizeChromaticRootSelected n) = 0) ∧
        ∀ r : ℝ,
          r ∈ Ioo
              (phaseRootCenter n -
                fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n)
              (phaseRootCenter n +
                fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n) ∧
            fiveSizePhaseObjective n 0 r = 0 →
          r = fiveSizeChromaticRootSelected n) := by
  filter_upwards [(Classical.choose_spec
    exists_pos_eventually_existsUnique_fiveSizePhaseObjective_zero_logLogCorridor).2] with n hn
  obtain ⟨rq, hrq, hunique_q⟩ := hn q ⟨q_pos.le, le_rfl⟩
  obtain ⟨r0, hr0, hunique_0⟩ := hn 0 ⟨le_rfl, q_pos.le⟩
  have hex_q : ∃ r : ℝ,
      r ∈ Ioo
          (phaseRootCenter n - fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n + fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n) ∧
        fiveSizePhaseObjective n q r = 0 := ⟨rq, hrq⟩
  have hex_0 : ∃ r : ℝ,
      r ∈ Ioo
          (phaseRootCenter n - fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n + fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n) ∧
        fiveSizePhaseObjective n 0 r = 0 := ⟨r0, hr0⟩
  have hspec_q : fiveSizeCochromaticRootSelected n ∈ Ioo
        (phaseRootCenter n - fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n) ∧
      fiveSizePhaseObjective n q (fiveSizeCochromaticRootSelected n) = 0 := by
    classical
    rw [fiveSizeCochromaticRootSelected, dif_pos hex_q]
    exact Classical.choose_spec hex_q
  have hspec_0 : fiveSizeChromaticRootSelected n ∈ Ioo
        (phaseRootCenter n - fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n) ∧
      fiveSizePhaseObjective n 0 (fiveSizeChromaticRootSelected n) = 0 := by
    classical
    rw [fiveSizeChromaticRootSelected, dif_pos hex_0]
    exact Classical.choose_spec hex_0
  exact ⟨⟨hspec_q, fun y hy ↦ (hunique_q y hy).trans (hunique_q _ hspec_q).symm⟩,
         ⟨hspec_0, fun y hy ↦ (hunique_0 y hy).trans (hunique_0 _ hspec_0).symm⟩⟩

theorem eventually_fiveSizeRoots_spec :
    ∀ᶠ n : ℕ in atTop,
      (fiveSizeCochromaticRootSelected n ∈ Icc
          (phaseRootCenter n -
            fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n) ∧
        fiveSizePhaseObjective n q (fiveSizeCochromaticRootSelected n) = 0) ∧
      (fiveSizeChromaticRootSelected n ∈ Icc
          (phaseRootCenter n -
            fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n) ∧
        fiveSizePhaseObjective n 0 (fiveSizeChromaticRootSelected n) = 0) :=
  eventually_fiveSizeRoots_spec_unique.mono fun _ hn ↦
    ⟨⟨Ioo_subset_Icc_self hn.1.1.1, hn.1.1.2⟩,
     ⟨Ioo_subset_Icc_self hn.2.1.1, hn.2.1.2⟩⟩

/-- Concrete integer threshold `k_co(n) = ⌈r₅^co(n)⌉ + 16`. -/
def hpCochromaticIndex (n : ℕ) : ℕ :=
  (⌈fiveSizeCochromaticRootSelected n⌉ + 16).toNat

/-- Concrete integer threshold `k_ch(n) = ⌈r₅(n)⌉ + ⌈log n⌉`. -/
def hpChromaticIndex (n : ℕ) : ℕ :=
  (⌈fiveSizeChromaticRootSelected n⌉ + ⌈Real.log (n : ℝ)⌉).toNat

/-! ## 3. Concrete Section 8 allowances `a_n`, `b_n` and exact Corollary 8.1 -/

/-- Concrete cochromatic amplification allowance `a_n = 2 n^{29/30}`. -/
def hpCochromaticAllowance (n : ℕ) : ℝ :=
  2 * (n : ℝ) ^ (29 / 30 : ℝ)

/-- Concrete chromatic amplification allowance `b_n = 2 √n (log n)²`. -/
def hpChromaticAllowance (n : ℕ) : ℝ :=
  2 * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 2

theorem hpCochromaticAllowance_div_baseScale_tendsto_zero :
    Tendsto (fun n : ℕ ↦ hpCochromaticAllowance n / baseScale n) atTop (nhds 0) := by
  have hexp : Tendsto (fun x : ℝ ↦ 2 * ((30 : ℝ) ^ 3 * (x ^ 3 * Real.exp (-x))))
      atTop (nhds 0) := by
    have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3
    simpa using (h0.const_mul ((30 : ℝ) ^ 3)).const_mul 2
  have hsub : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / 30) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
  refine (hexp.comp hsub).congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn2
  have hnpos : 0 < (n : ℝ) := by positivity
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
  dsimp [Function.comp_def]
  unfold hpCochromaticAllowance baseScale
  rw [Real.rpow_def_of_pos hnpos]
  have hexpId : Real.exp (Real.log (n : ℝ) * (29 / 30)) / (n : ℝ) =
      Real.exp (-(Real.log (n : ℝ) / 30)) := by
    calc Real.exp (Real.log (n : ℝ) * (29 / 30)) / (n : ℝ)
        = Real.exp (Real.log (n : ℝ) * (29 / 30)) / Real.exp (Real.log (n : ℝ)) := by
            rw [Real.exp_log hnpos]
      _ = Real.exp (Real.log (n : ℝ) * (29 / 30) - Real.log (n : ℝ)) :=
            (Real.exp_sub _ _).symm
      _ = Real.exp (-(Real.log (n : ℝ) / 30)) := by congr 1; ring
  have halg : 2 * Real.exp (Real.log (n : ℝ) * (29 / 30)) / ((n : ℝ) / Real.log (n : ℝ) ^ 3) =
      2 * Real.log (n : ℝ) ^ 3 * (Real.exp (Real.log (n : ℝ) * (29 / 30)) / (n : ℝ)) := by
    field_simp [hnpos.ne', hlogpos.ne']
  rw [halg, hexpId]
  ring

theorem hpChromaticAllowance_div_baseScale_tendsto_zero :
    Tendsto (fun n : ℕ ↦ hpChromaticAllowance n / baseScale n) atTop (nhds 0) := by
  have hexp : Tendsto (fun x : ℝ ↦ 2 * ((2 : ℝ) ^ 5 * (x ^ 5 * Real.exp (-x))))
      atTop (nhds 0) := by
    have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 5
    simpa using (h0.const_mul ((2 : ℝ) ^ 5)).const_mul 2
  have hsub : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / 2) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
  refine (hexp.comp hsub).congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn2
  have hnpos : 0 < (n : ℝ) := by positivity
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
  dsimp [Function.comp_def]
  unfold hpChromaticAllowance baseScale
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnpos]
  have hexpId : Real.exp (Real.log (n : ℝ) * (1 / 2)) / (n : ℝ) =
      Real.exp (-(Real.log (n : ℝ) / 2)) := by
    calc Real.exp (Real.log (n : ℝ) * (1 / 2)) / (n : ℝ)
        = Real.exp (Real.log (n : ℝ) * (1 / 2)) / Real.exp (Real.log (n : ℝ)) := by
            rw [Real.exp_log hnpos]
      _ = Real.exp (Real.log (n : ℝ) * (1 / 2) - Real.log (n : ℝ)) :=
            (Real.exp_sub _ _).symm
      _ = Real.exp (-(Real.log (n : ℝ) / 2)) := by congr 1; ring
  have halg :
      2 * Real.exp (Real.log (n : ℝ) * (1 / 2)) * Real.log (n : ℝ) ^ 2 /
          ((n : ℝ) / Real.log (n : ℝ) ^ 3) =
        2 * Real.log (n : ℝ) ^ 5 * (Real.exp (Real.log (n : ℝ) * (1 / 2)) / (n : ℝ)) := by
    field_simp [hnpos.ne', hlogpos.ne']
  rw [halg, hexpId]
  ring

/-- **Corollary 8.1 (`cor:zeta-upper`, concrete cochromatic part):** if
`P(ζ(G_n) ≤ k_co(n)) ≥ exp(-C_sm · n^{9/10} / log n)` eventually, then
eventually `P(ζ(G_n) > k_co(n) + 2 n^{29/30}) ≤ exp(-2 n^{14/15})`, and hence
`P(ζ(G_n) ≤ k_co(n) + 2 n^{29/30}) → 1`. -/
theorem hp_cochromatic_upperTail_of_secondMoment_seed
    (kCo : ℕ → ℕ) {C_sm : ℝ} (hC : 0 < C_sm)
    (hSeed : ∀ᶠ n : ℕ in atTop,
      Real.exp (-C_sm * (n : ℝ) ^ (9 / 10 : ℝ) / Real.log (n : ℝ)) ≤
        (randomGraphMeasure n).real {G | cochromaticNumber G ≤ kCo n}) :
    (∀ᶠ n : ℕ in atTop,
      (randomGraphMeasure n).real
        {G | (kCo n : ℝ) + hpCochromaticAllowance n < (cochromaticNumber G : ℝ)} ≤
        Real.exp (-2 * (n : ℝ) ^ (14 / 15 : ℝ))) ∧
    Tendsto (fun n ↦ randomGraphMeasure n
      {G | (cochromaticNumber G : ℝ) ≤ (kCo n : ℝ) + hpCochromaticAllowance n})
      atTop (nhds 1) := by
  have hDom : ∀ᶠ n : ℕ in atTop,
      C_sm * (n : ℝ) ^ (9 / 10 : ℝ) / Real.log (n : ℝ) < 2 * (n : ℝ) ^ (14 / 15 : ℝ) := by
    have h1 : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 / 30 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 30)).comp tendsto_natCast_atTop_atTop
    have hBig : ∀ᶠ n : ℕ in atTop, C_sm ≤ (n : ℝ) ^ (1 / 30 : ℝ) :=
      h1.eventually_ge_atTop C_sm
    filter_upwards [hBig, eventually_ge_atTop (3 : ℕ)] with n hN hn3
    have hnpos : 0 < (n : ℝ) := by positivity
    have hlog1 : 1 < Real.log (n : ℝ) := by
      have he3 : Real.exp 1 < (n : ℝ) :=
        lt_of_lt_of_le (Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3))
          (by exact_mod_cast hn3)
      simpa using Real.log_lt_log (Real.exp_pos 1) he3
    have hrpow : (n : ℝ) ^ (14 / 15 : ℝ) =
        (n : ℝ) ^ (1 / 30 : ℝ) * (n : ℝ) ^ (9 / 10 : ℝ) := by
      rw [← Real.rpow_add hnpos]; norm_num
    have h910pos : 0 < (n : ℝ) ^ (9 / 10 : ℝ) := Real.rpow_pos_of_pos hnpos _
    have hdiv : C_sm * (n : ℝ) ^ (9 / 10 : ℝ) / Real.log (n : ℝ) <
        C_sm * (n : ℝ) ^ (9 / 10 : ℝ) :=
      div_lt_self (mul_pos hC h910pos) hlog1
    have hmul : C_sm * (n : ℝ) ^ (9 / 10 : ℝ) ≤ (n : ℝ) ^ (14 / 15 : ℝ) := by
      rw [hrpow]; exact mul_le_mul_of_nonneg_right hN h910pos.le
    have h1415pos : 0 < (n : ℝ) ^ (14 / 15 : ℝ) := Real.rpow_pos_of_pos hnpos _
    linarith
  have hQuant : ∀ᶠ n : ℕ in atTop,
      (randomGraphMeasure n).real
        {G | (kCo n : ℝ) + hpCochromaticAllowance n < (cochromaticNumber G : ℝ)} ≤
        Real.exp (-2 * (n : ℝ) ^ (14 / 15 : ℝ)) := by
    filter_upwards [hSeed, hDom, eventually_ge_atTop (2 : ℕ)] with n hSn hDn hn2
    have hnpos : 0 < (n : ℝ) := by positivity
    let t : ℝ := (n : ℝ) ^ (29 / 30 : ℝ)
    have ht : 0 ≤ t := Real.rpow_nonneg hnpos.le _
    have ht2 : t ^ 2 = (n : ℝ) ^ (29 / 15 : ℝ) := by
      dsimp [t]; rw [sq, ← Real.rpow_add hnpos]; norm_num
    have hn1pos : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
    have hn1le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    have hquot : (n : ℝ) ^ (14 / 15 : ℝ) ≤ t ^ 2 / ((n - 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hn1pos, ht2]
      calc (n : ℝ) ^ (14 / 15 : ℝ) * ((n - 1 : ℕ) : ℝ)
          ≤ (n : ℝ) ^ (14 / 15 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
            exact mul_le_mul_of_nonneg_left hn1le (Real.rpow_nonneg hnpos.le _)
        _ = (n : ℝ) ^ (29 / 15 : ℝ) := by rw [← Real.rpow_add hnpos]; norm_num
    have hexpLe : Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) ≤
        Real.exp (-2 * (n : ℝ) ^ (14 / 15 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      rw [mul_div_assoc]
      linarith
    have hexpLt : Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) <
        (randomGraphMeasure n).real {G | cochromaticNumber G ≤ kCo n} := by
      refine lt_of_le_of_lt hexpLe (lt_of_lt_of_le ?_ hSn)
      apply Real.exp_lt_exp.mpr
      linarith [show -C_sm * (n : ℝ) ^ (9 / 10 : ℝ) / Real.log (n : ℝ) =
        -(C_sm * (n : ℝ) ^ (9 / 10 : ℝ) / Real.log (n : ℝ)) by ring]
    have hAmp := cochromatic_upperTail_of_seed hn2 ht hexpLt
    unfold hpCochromaticAllowance
    exact hAmp.trans hexpLe
  refine ⟨hQuant, ?_⟩
  apply tendsto_measure_one_of_compl_real_tendsto_zero randomGraphMeasure _
    (fun n ↦ (Set.toFinite _).measurableSet)
  have hZero : Tendsto (fun n : ℕ ↦ Real.exp (-2 * (n : ℝ) ^ (14 / 15 : ℝ))) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (14 / 15 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 14 / 15)).comp tendsto_natCast_atTop_atTop
    exact Real.tendsto_exp_atBot.comp (h1.const_mul_atTop_of_neg (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hZero
    (Filter.Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_
  refine hQuant.mono fun n hn ↦ ?_
  have hcompl : ({G : LabeledGraph n |
      (cochromaticNumber G : ℝ) ≤ (kCo n : ℝ) + hpCochromaticAllowance n})ᶜ =
      {G : LabeledGraph n |
        (kCo n : ℝ) + hpCochromaticAllowance n < (cochromaticNumber G : ℝ)} := by
    ext G; simp [not_le]
  rwa [hcompl]

/-- **Corollary 8.1 (`cor:zeta-upper`, concrete chromatic part):** if
`P(χ(G_n) ≤ k_ch(n)) ≥ exp(-C'_sm · (log n)²)` eventually, then eventually
`P(χ(G_n) > k_ch(n) + 2 √n (log n)²) ≤ exp(-2 (log n)⁴)`, and hence
`P(χ(G_n) ≤ k_ch(n) + 2 √n (log n)²) → 1`. -/
theorem hp_chromatic_upperTail_of_secondMoment_seed
    (kCh : ℕ → ℕ) {C_sm : ℝ} (hC : 0 < C_sm)
    (hSeed : ∀ᶠ n : ℕ in atTop,
      Real.exp (-C_sm * (Real.log (n : ℝ)) ^ 2) ≤
        (randomGraphMeasure n).real {G | chromaticNumberNat G ≤ kCh n}) :
    (∀ᶠ n : ℕ in atTop,
      (randomGraphMeasure n).real
        {G | (kCh n : ℝ) + hpChromaticAllowance n < (chromaticNumberNat G : ℝ)} ≤
        Real.exp (-2 * (Real.log (n : ℝ)) ^ 4)) ∧
    Tendsto (fun n ↦ randomGraphMeasure n
      {G | (chromaticNumberNat G : ℝ) ≤ (kCh n : ℝ) + hpChromaticAllowance n})
      atTop (nhds 1) := by
  have hLogBig : ∀ᶠ n : ℕ in atTop, C_sm + 1 ≤ (Real.log (n : ℝ)) ^ 2 := by
    have h1 : Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact h1.eventually_ge_atTop (C_sm + 1)
  have hQuant : ∀ᶠ n : ℕ in atTop,
      (randomGraphMeasure n).real
        {G | (kCh n : ℝ) + hpChromaticAllowance n < (chromaticNumberNat G : ℝ)} ≤
        Real.exp (-2 * (Real.log (n : ℝ)) ^ 4) := by
    filter_upwards [hSeed, hLogBig, eventually_ge_atTop (2 : ℕ)] with n hSn hLn hn2
    have hnpos : 0 < (n : ℝ) := by positivity
    let t : ℝ := Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 2
    have ht : 0 ≤ t := by positivity
    have hn1pos : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
    have hn1le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    have ht2 : t ^ 2 = (n : ℝ) * (Real.log (n : ℝ)) ^ 4 := by
      dsimp [t]; rw [mul_pow, Real.sq_sqrt hnpos.le]; ring
    have hquot : (Real.log (n : ℝ)) ^ 4 ≤ t ^ 2 / ((n - 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hn1pos, ht2, mul_comm]
      exact mul_le_mul_of_nonneg_right hn1le (pow_nonneg (Real.log_pos (by exact_mod_cast hn2)).le 4)
    have hexpLe : Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) ≤
        Real.exp (-2 * (Real.log (n : ℝ)) ^ 4) := by
      apply Real.exp_le_exp.mpr
      rw [mul_div_assoc]
      linarith
    have hL2pos : 0 < (Real.log (n : ℝ)) ^ 2 :=
      sq_pos_of_pos (Real.log_pos (by exact_mod_cast hn2))
    have hL4gt : C_sm * (Real.log (n : ℝ)) ^ 2 < 2 * (Real.log (n : ℝ)) ^ 4 := by
      have h1 : (C_sm + 1) * (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ 4 := by
        calc (C_sm + 1) * (Real.log (n : ℝ)) ^ 2
            ≤ (Real.log (n : ℝ)) ^ 2 * (Real.log (n : ℝ)) ^ 2 :=
              mul_le_mul_of_nonneg_right hLn hL2pos.le
          _ = (Real.log (n : ℝ)) ^ 4 := by ring
      have hL4pos : 0 < (Real.log (n : ℝ)) ^ 4 :=
        pow_pos (Real.log_pos (by exact_mod_cast hn2)) 4
      linarith
    have hexpLt : Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) <
        (randomGraphMeasure n).real {G | chromaticNumberNat G ≤ kCh n} :=
      lt_of_le_of_lt hexpLe (lt_of_lt_of_le
        (Real.exp_lt_exp.mpr (by linarith)) hSn)
    have hAmp := chromatic_upperTail_of_seed hn2 ht hexpLt
    have h2t : 2 * t = hpChromaticAllowance n := by dsimp [t, hpChromaticAllowance]; ring
    rw [← h2t]
    exact hAmp.trans hexpLe
  refine ⟨hQuant, ?_⟩
  apply tendsto_measure_one_of_compl_real_tendsto_zero randomGraphMeasure _
    (fun n ↦ (Set.toFinite _).measurableSet)
  have hZero : Tendsto (fun n : ℕ ↦ Real.exp (-2 * (Real.log (n : ℝ)) ^ 4)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ 4) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact Real.tendsto_exp_atBot.comp (h1.const_mul_atTop_of_neg (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hZero
    (Filter.Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_
  refine hQuant.mono fun n hn ↦ ?_
  have hcompl : ({G : LabeledGraph n |
      (chromaticNumberNat G : ℝ) ≤ (kCh n : ℝ) + hpChromaticAllowance n})ᶜ =
      {G : LabeledGraph n |
        (kCh n : ℝ) + hpChromaticAllowance n < (chromaticNumberNat G : ℝ)} := by
    ext G; simp [not_le]
  rwa [hcompl]

/-! ## 4. Unconditional two-sided separations `(A)` and concrete `[0.063, 0.104]` theorem -/

theorem phaseGain5_le_log_two (delta : ℝ) (hdelta : delta ∈ Icc (0 : ℝ) 1) :
    phaseGain5 delta ≤ Real.log 2 := by
  obtain ⟨hT25, -⟩ := phaseTarget_bounds delta hdelta
  have hm := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
  have hmono := dualValue_mono S4_subset_S5 S5_subset_Splus hm
  unfold phaseGain5
  linarith

private theorem upperCoeff_quotient_le {delta t0 : ℝ}
    (hdelta : delta ∈ Icc (0 : ℝ) 1) (ht0Pos : 0 < t0) (ht0Cap : t0 ≤ 1) :
    let eta := min (1 / 4) ((t0 / 3) * q / 32)
    let eps := min (q / 4) (q * (t0 / 3) / 64)
    (((2 * Real.log 2 - phaseGain5 delta) + eta) / (q / 2 - eps)) *
      (q ^ 3 / 8 + eps) ≤ upperPhaseCoeff delta + t0 / 3 := by
  intro eta eps
  have hetaPos : 0 < eta := lt_min (by norm_num)
    (div_pos (mul_pos (div_pos ht0Pos (by norm_num)) q_pos) (by norm_num))
  have hepsPos : 0 < eps := lt_min (div_pos q_pos (by norm_num))
    (div_pos (mul_pos q_pos (div_pos ht0Pos (by norm_num))) (by norm_num))
  have hepsLeQ4 : eps ≤ q / 4 := min_le_left _ _
  have hDenLoPos : 0 < q / 2 - eps := by linarith [hepsLeQ4, q_pos]
  rw [div_mul_eq_mul_div, div_le_iff₀ hDenLoPos]
  unfold upperPhaseCoeff
  have hqeq : Real.log 2 = q := rfl
  rw [hqeq]
  have hq1 : q < 1 := Real.log_two_lt_d9.trans (by norm_num)
  have hq2le1 : q ^ 2 ≤ 1 := pow_le_one₀ q_pos.le hq1.le
  have hq3le1 : q ^ 3 ≤ 1 := pow_le_one₀ q_pos.le hq1.le
  have hA5pos : 0 < phaseGain5 delta := lt_trans (by norm_num : (0 : ℝ) < 5247 / 10000)
    (lt_trans log_169_div_100_gt
      (FiveSizePhaseGainCertificate.log_169_div_100_lt_phaseGain5 _ hdelta))
  have hA5hi : phaseGain5 delta ≤ q := phaseGain5_le_log_two _ hdelta
  have heta1 : eta ≤ 1 / 4 := min_le_left _ _
  have heta2 : eta ≤ (t0 / 3) * q / 32 := min_le_right _ _
  have heps2 : eps ≤ q * (t0 / 3) / 64 := min_le_right _ _
  have hterm1 : eta * (q ^ 3 / 8) ≤ (t0 / 3) * (q / 256) := by
    have h1 : eta * (q ^ 3 / 8) ≤ ((t0 / 3) * q / 32) * (1 / 8) :=
      mul_le_mul heta2 (by linarith) (div_nonneg (pow_nonneg q_pos.le 3) (by norm_num))
        (div_nonneg (mul_nonneg (div_nonneg ht0Pos.le (by norm_num)) q_pos.le) (by norm_num))
    linarith
  have hterm2 : (2 * q - phaseGain5 delta + eta) * eps ≤ (t0 / 3) * (3 * q / 64) := by
    have hb1 : 2 * q - phaseGain5 delta + eta ≤ 3 := by linarith
    have h1 := mul_le_mul hb1 heps2 hepsPos.le (by norm_num)
    linarith
  have hterm3 : (q ^ 2 / 4 * (2 * q - phaseGain5 delta) + t0 / 3) * eps ≤
      (t0 / 3) * (3 * q / 64) := by
    have hSnn : 0 ≤ 2 * q - phaseGain5 delta := by linarith
    have hS2 : 2 * q - phaseGain5 delta ≤ 2 := by linarith
    have hqS : q ^ 2 / 4 * (2 * q - phaseGain5 delta) ≤ (1 / 4 : ℝ) * 2 :=
      mul_le_mul (by linarith) hS2 hSnn (by norm_num)
    have hb2 : q ^ 2 / 4 * (2 * q - phaseGain5 delta) + t0 / 3 ≤ 3 := by linarith
    have h1 := mul_le_mul hb2 heps2 hepsPos.le (by norm_num)
    linarith
  have htq : 0 < (t0 / 3) * q := mul_pos (div_pos ht0Pos (by norm_num)) q_pos
  linarith [show ((2 * q - phaseGain5 delta) + eta) * (q ^ 3 / 8 + eps) =
              (2 * q - phaseGain5 delta) * (q ^ 3 / 8) + eta * (q ^ 3 / 8) +
                (2 * q - phaseGain5 delta + eta) * eps by ring,
            show (q ^ 2 / 4 * (2 * q - phaseGain5 delta) + t0 / 3) * (q / 2 - eps) =
              (2 * q - phaseGain5 delta) * (q ^ 3 / 8) + (t0 / 3) * (q / 2) -
                (q ^ 2 / 4 * (2 * q - phaseGain5 delta) + t0 / 3) * eps by ring]

private theorem eventually_concrete_fiveSize_lower_separation
    {theta : ℝ} (htheta : 0 < theta) :
    ∀ᶠ n : ℕ in atTop,
      (lowerPhaseCoeff (phaseDelta n) - theta) * baseScale n ≤
        (phaseChromaticLowerIndex n : ℝ) - (hpCochromaticIndex n : ℝ) -
          hpCochromaticAllowance n := by
  let C : ℝ := unrestrictedPhaseRootCorridorCoefficient +
    cocoloringUnrestrictedRootCorridorCoefficient + fiveSizeRootCorridorCoefficient
  have hCpos : 0 < C := add_pos
    (add_pos unrestrictedPhaseRootCorridorCoefficient_pos
      cocoloringUnrestrictedRootCorridorCoefficient_pos)
    fiveSizeRootCorridorCoefficient_pos
  have hMain : ∀ᶠ n : ℕ in atTop,
      (lowerPhaseCoeff (phaseDelta n) - theta) * baseScale n ≤
        (phaseChromaticLowerIndex n : ℝ) - (hpCochromaticIndex n : ℝ) -
          hpCochromaticAllowance n := by
    let t0 : ℝ := min theta (1 / 32)
    have ht0Pos : 0 < t0 := lt_min htheta (by norm_num)
    have ht0Le : t0 ≤ theta := min_le_left _ _
    have ht0Cap : t0 ≤ 1 / 32 := min_le_right _ _
    let eta : ℝ := min (1 / 4) ((t0 / 3) / (q ^ 2 + 1))
    have hetaPos : 0 < eta := lt_min (by norm_num) (div_pos (div_pos ht0Pos (by norm_num)) (by positivity))
    let epsSlope : ℝ := q * (t0 / 3) / 4
    have hepsSlopePos : 0 < epsSlope := div_pos (mul_pos q_pos (div_pos ht0Pos (by norm_num))) (by norm_num)
    let KLip : ℝ := 16 * dualLipschitzSpan + 1
    have hKLipPos : 0 < KLip := by dsimp [KLip]; linarith [dualLipschitzSpan_nonneg]
    have hTrans := eventually_uniform_phaseRootLogLogCorridor_fourSizeTarget_tendsto_center
      C hCpos.le ((eta / 2) / KLip) (div_pos (half_pos hetaPos) hKLipPos)
    obtain ⟨N5, hN5⟩ := eventually_uniform_fiveDeficitScore (eta / 2) (half_pos hetaPos)
    have hphN5 : ∀ᶠ n : ℕ in atTop, N5 ≤ phaseNat n := by
      filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (N5 : ℝ),
        eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
      exact_mod_cast hn.trans hph.1
    have hBudLt : ∀ᶠ n : ℕ in atTop, fixedOffsetRoundingBudget n < t0 / 3 :=
      fixedOffset_rounding_budget_spec.1.eventually
        (Iio_mem_nhds (div_pos ht0Pos (by norm_num)))
    have haSmall : ∀ᶠ n : ℕ in atTop, hpCochromaticAllowance n / baseScale n < t0 / 3 :=
      hpCochromaticAllowance_div_baseScale_tendsto_zero.eventually
        (Iio_mem_nhds (div_pos ht0Pos (by norm_num)))
    have hLLPos : ∀ᶠ n : ℕ in atTop, 0 < logLogOrder n :=
      tendsto_logLogOrder_atTop.eventually_gt_atTop 0
    filter_upwards
      [eventually_unrestrictedPhaseRootSelected_spec_unique,
        eventually_fiveSizeRoots_spec,
        eventually_unrestrictedPhaseObjective_deriv_logLogCorridor_sharp C hCpos.le
          (hepsilon := hepsSlopePos),
        eventually_phaseRootLogLogCorridor_fourSize_domain C hCpos.le,
        eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hCpos.le,
        eventually_phaseRootLogLogCorridor_part_div_phaseNat_sq_lower C hCpos.le,
        eventually_phaseRoot_domain_pos_and_target_corridor,
        eventually_five_lt_phaseNat,
        eventually_ge_atTop (2 : ℕ),
        hTrans, hphN5, fixedOffset_rounding_budget_spec.2, hBudLt, haSmall, hLLPos] with
        n hUnrest hFive hDeriv hDom hTarget hScaleLo hCenterDom hfive hn2
          hMove hN5le hRound hBud haN hLL
    set rPlus : ℝ := unrestrictedPhaseRootSelected n
    set r5Co : ℝ := fiveSizeCochromaticRootSelected n
    set center : ℝ := phaseRootCenter n
    set width : ℝ := logLogOrder n * phaseRootGapRadius n
    set lower : ℝ := phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n
    set upper : ℝ := phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n
    set a : ℝ := (phaseNat n : ℝ)
    have haPos : 0 < a := Nat.cast_pos.mpr (lt_trans (by omega : 0 < 5) hfive)
    have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
    have hBasePos : 0 < baseScale n := by
      rw [baseScale]
      have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
      have hnpos : 0 < (n : ℝ) := by positivity
      positivity
    have hs0Pos : 0 < center :=
      div_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hCenterDom.1.1)) hCenterDom.2.1
    have hWidthPos : 0 < width := mul_pos hLL (div_pos hs0Pos haSqPos)
    have hPlusMem : rPlus ∈ Icc lower upper := by
      have h1 := hUnrest.1.1
      have hpad : 0 ≤ (cocoloringUnrestrictedRootCorridorCoefficient +
          fiveSizeRootCorridorCoefficient) * width :=
        mul_nonneg (add_nonneg cocoloringUnrestrictedRootCorridorCoefficient_pos.le
          fiveSizeRootCorridorCoefficient_pos.le) hWidthPos.le
      rw [mem_Ioo] at h1; rw [mem_Icc]
      exact ⟨by dsimp [rPlus, lower, width, C] at hpad h1 ⊢
                linarith [show (unrestrictedPhaseRootCorridorCoefficient +
                  cocoloringUnrestrictedRootCorridorCoefficient +
                  fiveSizeRootCorridorCoefficient) * logLogOrder n * phaseRootGapRadius n =
                  unrestrictedPhaseRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n +
                  (cocoloringUnrestrictedRootCorridorCoefficient +
                    fiveSizeRootCorridorCoefficient) * (logLogOrder n * phaseRootGapRadius n) by ring],
             by dsimp [rPlus, upper, width, C] at hpad h1 ⊢
                linarith [show (unrestrictedPhaseRootCorridorCoefficient +
                  cocoloringUnrestrictedRootCorridorCoefficient +
                  fiveSizeRootCorridorCoefficient) * logLogOrder n * phaseRootGapRadius n =
                  unrestrictedPhaseRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n +
                  (cocoloringUnrestrictedRootCorridorCoefficient +
                    fiveSizeRootCorridorCoefficient) * (logLogOrder n * phaseRootGapRadius n) by ring]⟩
    have h5CoMem : r5Co ∈ Icc lower upper := by
      have h1 := hFive.1.1
      have hpad : 0 ≤ (unrestrictedPhaseRootCorridorCoefficient +
          cocoloringUnrestrictedRootCorridorCoefficient) * width :=
        mul_nonneg (add_nonneg unrestrictedPhaseRootCorridorCoefficient_pos.le
          cocoloringUnrestrictedRootCorridorCoefficient_pos.le) hWidthPos.le
      rw [mem_Icc] at h1 ⊢
      exact ⟨by dsimp [r5Co, lower, width, C] at hpad h1 ⊢
                linarith [show (unrestrictedPhaseRootCorridorCoefficient +
                  cocoloringUnrestrictedRootCorridorCoefficient +
                  fiveSizeRootCorridorCoefficient) * logLogOrder n * phaseRootGapRadius n =
                  fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n +
                  (unrestrictedPhaseRootCorridorCoefficient +
                    cocoloringUnrestrictedRootCorridorCoefficient) * (logLogOrder n * phaseRootGapRadius n) by ring],
             by dsimp [r5Co, upper, width, C] at hpad h1 ⊢
                linarith [show (unrestrictedPhaseRootCorridorCoefficient +
                  cocoloringUnrestrictedRootCorridorCoefficient +
                  fiveSizeRootCorridorCoefficient) * logLogOrder n * phaseRootGapRadius n =
                  fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n +
                  (unrestrictedPhaseRootCorridorCoefficient +
                    cocoloringUnrestrictedRootCorridorCoefficient) * (logLogOrder n * phaseRootGapRadius n) by ring]⟩
    have hDom' : ∀ x ∈ Icc lower upper, 0 < x ∧ fourSizeTarget n (phaseNat n) x ∈ Ioo (2 : ℝ) 5 :=
      hDom
    have hr5CoPos : 0 < r5Co := (hDom' r5Co h5CoMem).1
    -- Margin at `r5Co`
    set T : ℝ := fourSizeTarget n (phaseNat n) r5Co
    have hTK : T ∈ Icc (9 / 4 : ℝ) (17 / 4) := hTarget r5Co h5CoMem
    have hT25 : T ∈ Ioo (2 : ℝ) 5 := ⟨by linarith [hTK.1], by linarith [hTK.2]⟩
    have hdelta : phaseDelta n ∈ Icc (0 : ℝ) 1 :=
      ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩
    have hCenterEq : phaseRootDeficitTarget n = phaseTarget (phaseDelta n) := by
      rw [phaseRootDeficitTarget_eq hCenterDom.1]; rfl
    have hCenterK : phaseTarget (phaseDelta n) ∈ Icc (9 / 4 : ℝ) (17 / 4) := by
      obtain ⟨hA, hB⟩ := FiveSizePhaseGainCertificate.two_div_log_two_bounds
      unfold phaseTarget; exact ⟨by linarith [hdelta.2], by linarith [hdelta.1]⟩
    have hdist : |T - phaseTarget (phaseDelta n)| < (eta / 2) / KLip := by
      rw [← hCenterEq, ← Real.dist_eq]
      exact hMove r5Co h5CoMem
    have hLipSp := abs_dualValue_sub_le_of_mem_Icc S4_subset_Splus subset_rfl hTK hCenterK
    have hLipS5 := abs_dualValue_sub_le_of_mem_Icc S4_subset_S5 S5_subset_Splus hTK hCenterK
    have hLipLt : 16 * dualLipschitzSpan * |T - phaseTarget (phaseDelta n)| < eta / 2 := by
      have h1 : 16 * dualLipschitzSpan * |T - phaseTarget (phaseDelta n)| ≤
          KLip * |T - phaseTarget (phaseDelta n)| := by
        dsimp [KLip]; linarith [abs_nonneg (T - phaseTarget (phaseDelta n))]
      have h2 := mul_lt_mul_of_pos_left hdist hKLipPos
      rw [mul_div_cancel₀ _ hKLipPos.ne'] at h2; linarith
    have hUnrestLe : finiteUnrestrictedDeficitEntropy (phaseNat n) T ≤ dualValue Splus T :=
      (finiteProfileDeficitEntropy_le_extendedGaussianEntropyValue (phaseNat n) hfive hT25).trans
        (extendedGaussianEntropyValue_le_dualValue_Splus hT25)
    have hScore5 : ∀ i : Fin 5, |fiveDeficitScore (phaseNat n) i - fiveGaussianScore i| ≤ eta / 2 :=
      fun i ↦ (hN5 (phaseNat n) hN5le i).le
    have h5Ge : dualValue S5 T - eta / 2 ≤ fiveSizeFiniteEntropy (phaseNat n) T := by
      linarith [(abs_le.mp (abs_fiveSizeFiniteEntropy_sub_dualValue_le hScore5 hT25)).1]
    have hMargin5 : phaseGain5 (phaseDelta n) - eta ≤
        q - finiteUnrestrictedDeficitEntropy (phaseNat n) T +
          fiveSizeFiniteEntropy (phaseNat n) T := by
      unfold phaseGain5 q
      linarith [(abs_le.mp hLipSp).2, (abs_le.mp hLipS5).1, hLipLt, hUnrestLe, h5Ge]
    have hA5lo : (1 / 2 : ℝ) < phaseGain5 (phaseDelta n) := by
      have h := lt_trans log_169_div_100_gt
        (FiveSizePhaseGainCertificate.log_169_div_100_lt_phaseGain5 _ hdelta)
      linarith
    have hAdvPos : 0 < phaseGain5 (phaseDelta n) - eta := by
      linarith [min_le_left (1 / 4) ((t0 / 3) / (q ^ 2 + 1))]
    -- At `r5Co`, `unrestrictedPhaseObjective n r5Co ≤ -r5Co * (phaseGain5 - eta) < 0`
    have hZero5 := hFive.1.2
    rw [fiveSizePhaseObjective_eq_unrestricted_add_margin n q hr5CoPos.ne'] at hZero5
    have hUR5Co : unrestrictedPhaseObjective n r5Co ≤
        -(r5Co * (phaseGain5 (phaseDelta n) - eta)) := by
      have hm := mul_le_mul_of_nonneg_left hMargin5 hr5CoPos.le
      dsimp [T] at hm; linarith
    -- MVT on `unrestrictedPhaseObjective n` between `r5Co` and `rPlus`
    have hKeyU : ∀ x ∈ Icc lower upper,
        HasDerivAt (unrestrictedPhaseObjective n)
          (Real.log (profileDualPartition (phaseNat n + 1)
              (profileDualTilt (phaseNat n + 1) ((n : ℝ) / x))) - Real.log x) x := by
      intro x hx
      have htar := (hDom' x hx).2
      rw [fourSizeTarget, mem_Ioo] at htar
      have hsix : (6 : ℝ) ≤ phaseNat n := by exact_mod_cast (Nat.succ_le_of_lt hfive)
      exact hasDerivAt_profileDualOptimalValue_parts (by omega) (hDom' x hx).1 (by
        rw [mem_Ioo, show (((phaseNat n + 1 : ℕ)) : ℝ) = (phaseNat n : ℝ) + 1 by push_cast; ring]
        exact ⟨by linarith [htar.2], by linarith [htar.1]⟩)
    have hContU : ContinuousOn (unrestrictedPhaseObjective n) (Icc lower upper) :=
      fun x hx ↦ (hKeyU x hx).continuousAt.continuousWithinAt
    have hStrictU : StrictMonoOn (unrestrictedPhaseObjective n) (Icc lower upper) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc lower upper) hContU
      intro x hx
      rw [interior_Icc] at hx
      have hsh := (hDeriv x ⟨hx.1.le, hx.2.le⟩).1
      have hepsSmall : epsSlope < q / 4 := by
        dsimp [epsSlope]
        have := mul_le_mul_of_nonneg_left ht0Cap q_pos.le
        linarith [q_pos]
      have hposSlope : 0 < (q / 2 - epsSlope) * a ^ 2 := mul_pos (by linarith) haSqPos
      linarith
    have hUPlus : unrestrictedPhaseObjective n rPlus = 0 := hUnrest.1.2
    have hOrder : r5Co ≤ rPlus := by
      by_contra hNot
      have hMono := hStrictU hPlusMem h5CoMem (lt_of_not_ge hNot)
      linarith [mul_pos hr5CoPos hAdvPos]
    have hSub : Icc r5Co rPlus ⊆ Icc lower upper :=
      fun x hx ↦ ⟨h5CoMem.1.trans hx.1, hx.2.trans hPlusMem.2⟩
    let G : ℝ → ℝ := fun x ↦ unrestrictedPhaseObjective n x - unrestrictedPhaseObjective n r5Co
    have hGCont : ContinuousOn G (Icc r5Co rPlus) :=
      (hContU.mono hSub).sub continuousOn_const
    have hGDiff : DifferentiableOn ℝ G (Ioo r5Co rPlus) := fun x hx ↦
      ((hKeyU x (hSub (Ioo_subset_Icc_self hx))).sub_const _).differentiableAt.differentiableWithinAt
    have hDenPos : 0 < q / 2 + epsSlope := by linarith [q_pos]
    have hGSlope : ∀ x ∈ Ioo r5Co rPlus, deriv G x ≤ (q / 2 + epsSlope) * a ^ 2 := by
      intro x hx
      have hxC := hSub (Ioo_subset_Icc_self hx)
      have hdG := ((hKeyU x hxC).sub_const (unrestrictedPhaseObjective n r5Co)).deriv
      have hdU := (hKeyU x hxC).deriv
      have hup := (hDeriv x hxC).2
      rw [hdG, ← hdU]; exact hup
    have hGAdv : r5Co * (phaseGain5 (phaseDelta n) - eta) ≤ G rPlus := by
      dsimp [G]
      linarith [hUPlus, hUR5Co]
    have hGGap := signed_root_separation_of_advantage_and_slope
      (advantage := r5Co * (phaseGain5 (phaseDelta n) - eta))
      hOrder hGCont hGDiff (mul_pos hDenPos haSqPos) hGSlope (sub_self _) hGAdv
    have hSlo : q ^ 3 / 8 * baseScale n ≤ r5Co / a ^ 2 := hScaleLo r5Co h5CoMem
    have hCoeffLe :
        lowerPhaseCoeff (phaseDelta n) - t0 / 3 ≤
          q ^ 3 / 8 * (phaseGain5 (phaseDelta n) - eta) / (q / 2 + epsSlope) := by
      unfold lowerPhaseCoeff
      exact lowerCoeff_quotient_le (by linarith [hA5lo])
        (phaseGain5_le_log_two _ hdelta) (div_pos ht0Pos (by norm_num))
    have hRealRootGap :
        (lowerPhaseCoeff (phaseDelta n) - t0 / 3) * baseScale n ≤ rPlus - r5Co := by
      calc (lowerPhaseCoeff (phaseDelta n) - t0 / 3) * baseScale n
          ≤ (q ^ 3 / 8 * (phaseGain5 (phaseDelta n) - eta) / (q / 2 + epsSlope)) * baseScale n :=
            mul_le_mul_of_nonneg_right hCoeffLe hBasePos.le
        _ = (q ^ 3 / 8 * baseScale n) *
              ((phaseGain5 (phaseDelta n) - eta) / (q / 2 + epsSlope)) := by ring
        _ ≤ (r5Co / a ^ 2) * ((phaseGain5 (phaseDelta n) - eta) / (q / 2 + epsSlope)) :=
            mul_le_mul_of_nonneg_right hSlo (div_nonneg hAdvPos.le hDenPos.le)
        _ = (r5Co * (phaseGain5 (phaseDelta n) - eta)) / ((q / 2 + epsSlope) * a ^ 2) := by
            rw [div_mul_div_comm, mul_comm (a ^ 2)]
        _ ≤ rPlus - r5Co := hGGap
    -- Integer rounding & allowance `a_n`
    have hCoeff5Lo : (63 / 1000 : ℝ) < lowerPhaseCoeff (phaseDelta n) :=
      lowerPhaseCoeff_gt_0063 _ hdelta
    have hPosSurplus : fixedOffsetRoundingBudget n < lowerPhaseCoeff (phaseDelta n) - t0 / 3 := by
      linarith
    have hRound' : Real.log (n : ℝ) + 19 ≤ fixedOffsetRoundingBudget n * baseScale n := hRound
    have hBudMul := mul_le_mul_of_nonneg_right hPosSurplus.le hBasePos.le
    have hRPlusLarge : Real.log (n : ℝ) + 19 < rPlus := by linarith
    have hChiNonneg : 0 ≤ rootChromaticIndex rPlus (Real.log (n : ℝ)) := by
      unfold rootChromaticIndex; rw [sub_nonneg]; apply Int.le_floor.mpr
      linarith [Int.ceil_lt_add_one (Real.log (n : ℝ))]
    have hCoNonneg : 0 ≤ rootCochromaticFixedOffsetIndex r5Co := by
      unfold rootCochromaticFixedOffsetIndex
      have := Int.ceil_nonneg hr5CoPos.le; omega
    have hRounded := root_fixedOffset_rounding_gap_toNat rPlus r5Co (Real.log (n : ℝ))
      (lowerPhaseCoeff (phaseDelta n) - t0 / 3) (baseScale n) (fixedOffsetRoundingBudget n)
      hRealRootGap hRound hChiNonneg hCoNonneg
    have hIdxGap :
        (lowerPhaseCoeff (phaseDelta n) - t0 / 3 - fixedOffsetRoundingBudget n) * baseScale n ≤
          (phaseChromaticLowerIndex n : ℝ) - (hpCochromaticIndex n : ℝ) := hRounded
    have haLe : hpCochromaticAllowance n ≤ (t0 / 3) * baseScale n :=
      ((div_lt_iff₀ hBasePos).mp haN).le
    have h1 : (lowerPhaseCoeff (phaseDelta n) - 2 * (t0 / 3)) * baseScale n ≤
        (lowerPhaseCoeff (phaseDelta n) - t0 / 3 - fixedOffsetRoundingBudget n) * baseScale n :=
      mul_le_mul_of_nonneg_right (by linarith) hBasePos.le
    have h2 : (lowerPhaseCoeff (phaseDelta n) - theta) * baseScale n ≤
        (lowerPhaseCoeff (phaseDelta n) - t0) * baseScale n :=
      mul_le_mul_of_nonneg_right (by linarith) hBasePos.le
    linarith
  exact hMain

private theorem eventually_concrete_fiveSize_upper_separation
    {theta : ℝ} (htheta : 0 < theta) :
    ∀ᶠ n : ℕ in atTop,
      (-upperPhaseCoeff (phaseDelta n) - theta) * baseScale n ≤
        -((hpChromaticIndex n : ℝ) + hpChromaticAllowance n -
          (phaseCochromaticLowerIndex n : ℝ)) := by
  let C : ℝ := unrestrictedPhaseRootCorridorCoefficient +
    cocoloringUnrestrictedRootCorridorCoefficient + fiveSizeRootCorridorCoefficient
  have hCpos : 0 < C := add_pos
    (add_pos unrestrictedPhaseRootCorridorCoefficient_pos
      cocoloringUnrestrictedRootCorridorCoefficient_pos)
    fiveSizeRootCorridorCoefficient_pos
  let spanHi : ℕ → ℝ := fun n ↦
    (hpChromaticIndex n : ℝ) + hpChromaticAllowance n - (phaseCochromaticLowerIndex n : ℝ)
  have hMain : ∀ᶠ n : ℕ in atTop, (-upperPhaseCoeff (phaseDelta n) - theta) * baseScale n ≤ -spanHi n := by
    let t0 : ℝ := min theta 1
    have ht0Pos : 0 < t0 := lt_min htheta zero_lt_one
    have ht0Le : t0 ≤ theta := min_le_left _ _
    have ht0Cap : t0 ≤ 1 := min_le_right _ _
    let eta : ℝ := min (1 / 4) ((t0 / 3) * q / 32)
    have hetaPos : 0 < eta := lt_min (by norm_num)
      (div_pos (mul_pos (div_pos ht0Pos (by norm_num)) q_pos) (by norm_num))
    let eps : ℝ := min (q / 4) (q * (t0 / 3) / 64)
    have hepsPos : 0 < eps := lt_min (div_pos q_pos (by norm_num))
      (div_pos (mul_pos q_pos (div_pos ht0Pos (by norm_num))) (by norm_num))
    have hepsLeQ4 : eps ≤ q / 4 := min_le_left _ _
    let KLip : ℝ := 16 * dualLipschitzSpan + 1
    have hKLipPos : 0 < KLip := by dsimp [KLip]; linarith [dualLipschitzSpan_nonneg]
    have hTrans := eventually_uniform_phaseRootLogLogCorridor_fourSizeTarget_tendsto_center
      C hCpos.le ((eta / 2) / KLip) (div_pos (half_pos hetaPos) hKLipPos)
    obtain ⟨N5, hN5⟩ := eventually_uniform_fiveDeficitScore (eta / 2) (half_pos hetaPos)
    have hphN5 : ∀ᶠ n : ℕ in atTop, N5 ≤ phaseNat n := by
      filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (N5 : ℝ),
        eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
      exact_mod_cast hn.trans hph.1
    have hBudLt : ∀ᶠ n : ℕ in atTop, fixedOffsetRoundingBudget n < t0 / 6 :=
      fixedOffset_rounding_budget_spec.1.eventually
        (Iio_mem_nhds (div_pos ht0Pos (by norm_num)))
    have hbSmall : ∀ᶠ n : ℕ in atTop, hpChromaticAllowance n / baseScale n < t0 / 3 :=
      hpChromaticAllowance_div_baseScale_tendsto_zero.eventually
        (Iio_mem_nhds (div_pos ht0Pos (by norm_num)))
    have hLLPos : ∀ᶠ n : ℕ in atTop, 0 < logLogOrder n :=
      tendsto_logLogOrder_atTop.eventually_gt_atTop 0
    filter_upwards
      [eventually_cocoloringUnrestrictedPhaseRootSelected_spec_unique,
        eventually_fiveSizeRoots_spec,
        eventually_phaseCochromaticLowerIndex_geometry,
        eventually_unrestrictedPhaseObjective_deriv_logLogCorridor_sharp C hCpos.le
          (hepsilon := hepsPos),
        eventually_phaseRootLogLogCorridor_fourSize_domain C hCpos.le,
        eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hCpos.le,
        eventually_phaseRootLogLogCorridor_part_div_phaseNat_sq_upper C hCpos.le
          (hepsilon := hepsPos),
        eventually_phaseRoot_domain_pos_and_target_corridor,
        eventually_five_lt_phaseNat,
        eventually_ge_atTop (2 : ℕ),
        hTrans, hphN5, fixedOffset_rounding_budget_spec.2, hBudLt, hbSmall, hLLPos] with
        n hCoRoot hFive hCoGeom hDeriv hDom hTarget hScaleHi hCenterDom hfive hn2
          hMove hN5le hRound hBud hbN hLL
    set rCoPlus : ℝ := cocoloringUnrestrictedPhaseRootSelected n
    set r5Ch : ℝ := fiveSizeChromaticRootSelected n
    set center : ℝ := phaseRootCenter n
    set width : ℝ := logLogOrder n * phaseRootGapRadius n
    set lower : ℝ := phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n
    set upper : ℝ := phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n
    set F : ℝ → ℝ := cocoloringUnrestrictedPhaseObjective n
    set a : ℝ := (phaseNat n : ℝ)
    have haPos : 0 < a := Nat.cast_pos.mpr (lt_trans (by omega : 0 < 5) hfive)
    have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
    have hBasePos : 0 < baseScale n := by
      rw [baseScale]
      have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
      have hnpos : 0 < (n : ℝ) := by positivity
      positivity
    have hs0Pos : 0 < center :=
      div_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hCenterDom.1.1)) hCenterDom.2.1
    have hWidthPos : 0 < width := mul_pos hLL (div_pos hs0Pos haSqPos)
    have hCoMem : rCoPlus ∈ Icc lower upper := by
      have h1 := hCoRoot.1.1
      have hpad : 0 ≤ (unrestrictedPhaseRootCorridorCoefficient +
          fiveSizeRootCorridorCoefficient) * width :=
        mul_nonneg (add_nonneg unrestrictedPhaseRootCorridorCoefficient_pos.le
          fiveSizeRootCorridorCoefficient_pos.le) hWidthPos.le
      rw [mem_Ioo] at h1; rw [mem_Icc]
      exact ⟨by dsimp [rCoPlus, lower, width, C] at hpad h1 ⊢
                linarith [show (unrestrictedPhaseRootCorridorCoefficient +
                  cocoloringUnrestrictedRootCorridorCoefficient +
                  fiveSizeRootCorridorCoefficient) * logLogOrder n * phaseRootGapRadius n =
                  cocoloringUnrestrictedRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n +
                  (unrestrictedPhaseRootCorridorCoefficient +
                    fiveSizeRootCorridorCoefficient) * (logLogOrder n * phaseRootGapRadius n) by ring],
             by dsimp [rCoPlus, upper, width, C] at hpad h1 ⊢
                linarith [show (unrestrictedPhaseRootCorridorCoefficient +
                  cocoloringUnrestrictedRootCorridorCoefficient +
                  fiveSizeRootCorridorCoefficient) * logLogOrder n * phaseRootGapRadius n =
                  cocoloringUnrestrictedRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n +
                  (unrestrictedPhaseRootCorridorCoefficient +
                    fiveSizeRootCorridorCoefficient) * (logLogOrder n * phaseRootGapRadius n) by ring]⟩
    have h5ChMem : r5Ch ∈ Icc lower upper := by
      have h1 := hFive.2.1
      have hpad : 0 ≤ (unrestrictedPhaseRootCorridorCoefficient +
          cocoloringUnrestrictedRootCorridorCoefficient) * width :=
        mul_nonneg (add_nonneg unrestrictedPhaseRootCorridorCoefficient_pos.le
          cocoloringUnrestrictedRootCorridorCoefficient_pos.le) hWidthPos.le
      rw [mem_Icc] at h1 ⊢
      exact ⟨by dsimp [r5Ch, lower, width, C] at hpad h1 ⊢
                linarith [show (unrestrictedPhaseRootCorridorCoefficient +
                  cocoloringUnrestrictedRootCorridorCoefficient +
                  fiveSizeRootCorridorCoefficient) * logLogOrder n * phaseRootGapRadius n =
                  fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n +
                  (unrestrictedPhaseRootCorridorCoefficient +
                    cocoloringUnrestrictedRootCorridorCoefficient) * (logLogOrder n * phaseRootGapRadius n) by ring],
             by dsimp [r5Ch, upper, width, C] at hpad h1 ⊢
                linarith [show (unrestrictedPhaseRootCorridorCoefficient +
                  cocoloringUnrestrictedRootCorridorCoefficient +
                  fiveSizeRootCorridorCoefficient) * logLogOrder n * phaseRootGapRadius n =
                  fiveSizeRootCorridorCoefficient * logLogOrder n * phaseRootGapRadius n +
                  (unrestrictedPhaseRootCorridorCoefficient +
                    cocoloringUnrestrictedRootCorridorCoefficient) * (logLogOrder n * phaseRootGapRadius n) by ring]⟩
    have hDom' : ∀ x ∈ Icc lower upper, 0 < x ∧ fourSizeTarget n (phaseNat n) x ∈ Ioo (2 : ℝ) 5 :=
      hDom
    have hr5ChPos : 0 < r5Ch := (hDom' r5Ch h5ChMem).1
    -- Span margin at `r5Ch`
    set T : ℝ := fourSizeTarget n (phaseNat n) r5Ch
    have hTK : T ∈ Icc (9 / 4 : ℝ) (17 / 4) := hTarget r5Ch h5ChMem
    have hT25 : T ∈ Ioo (2 : ℝ) 5 := ⟨by linarith [hTK.1], by linarith [hTK.2]⟩
    have hdelta : phaseDelta n ∈ Icc (0 : ℝ) 1 :=
      ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩
    have hCenterEq : phaseRootDeficitTarget n = phaseTarget (phaseDelta n) := by
      rw [phaseRootDeficitTarget_eq hCenterDom.1]; rfl
    have hCenterK : phaseTarget (phaseDelta n) ∈ Icc (9 / 4 : ℝ) (17 / 4) := by
      obtain ⟨hA, hB⟩ := FiveSizePhaseGainCertificate.two_div_log_two_bounds
      unfold phaseTarget; exact ⟨by linarith [hdelta.2], by linarith [hdelta.1]⟩
    have hdist : |T - phaseTarget (phaseDelta n)| < (eta / 2) / KLip := by
      rw [← hCenterEq, ← Real.dist_eq]
      exact hMove r5Ch h5ChMem
    have hLipSp := abs_dualValue_sub_le_of_mem_Icc S4_subset_Splus subset_rfl hTK hCenterK
    have hLipS5 := abs_dualValue_sub_le_of_mem_Icc S4_subset_S5 S5_subset_Splus hTK hCenterK
    have hLipLt : 16 * dualLipschitzSpan * |T - phaseTarget (phaseDelta n)| < eta / 2 := by
      have h1 : 16 * dualLipschitzSpan * |T - phaseTarget (phaseDelta n)| ≤
          KLip * |T - phaseTarget (phaseDelta n)| := by
        dsimp [KLip]; linarith [abs_nonneg (T - phaseTarget (phaseDelta n))]
      have h2 := mul_lt_mul_of_pos_left hdist hKLipPos
      rw [mul_div_cancel₀ _ hKLipPos.ne'] at h2; linarith
    have hUnrestLe : finiteUnrestrictedDeficitEntropy (phaseNat n) T ≤ dualValue Splus T :=
      (finiteProfileDeficitEntropy_le_extendedGaussianEntropyValue (phaseNat n) hfive hT25).trans
        (extendedGaussianEntropyValue_le_dualValue_Splus hT25)
    have hScore5 : ∀ i : Fin 5, |fiveDeficitScore (phaseNat n) i - fiveGaussianScore i| ≤ eta / 2 :=
      fun i ↦ (hN5 (phaseNat n) hN5le i).le
    have h5Ge : dualValue S5 T - eta / 2 ≤ fiveSizeFiniteEntropy (phaseNat n) T := by
      linarith [(abs_le.mp (abs_fiveSizeFiniteEntropy_sub_dualValue_le hScore5 hT25)).1]
    have hSpanMargin :
        q + finiteUnrestrictedDeficitEntropy (phaseNat n) T -
          fiveSizeFiniteEntropy (phaseNat n) T ≤
        (2 * Real.log 2 - phaseGain5 (phaseDelta n)) + eta := by
      unfold phaseGain5 q
      linarith [(abs_le.mp hLipSp).2, (abs_le.mp hLipS5).1, hLipLt, hUnrestLe, h5Ge]
    have hZero5Ch := hFive.2.2
    rw [fiveSizePhaseObjective_eq_unrestricted_add_margin n 0 hr5ChPos.ne', zero_sub] at hZero5Ch
    have hFR5Ch : F r5Ch ≤ r5Ch * ((2 * Real.log 2 - phaseGain5 (phaseDelta n)) + eta) := by
      have hEq : F r5Ch = r5Ch * (q + finiteUnrestrictedDeficitEntropy (phaseNat n) T -
          fiveSizeFiniteEntropy (phaseNat n) T) := by
        dsimp [F, cocoloringUnrestrictedPhaseObjective, T]
        linarith [hZero5Ch]
      rw [hEq]
      exact mul_le_mul_of_nonneg_left hSpanMargin hr5ChPos.le
    -- MVT on `F` (`cocoloringUnrestrictedPhaseObjective n`) when `rCoPlus ≤ r5Ch` (and trivial if `r5Ch < rCoPlus`!)
    have hSpanNonneg : 0 ≤ (2 * Real.log 2 - phaseGain5 (phaseDelta n)) + eta := by
      have hA5hi := phaseGain5_le_log_two _ hdelta
      have hqeq : Real.log 2 = q := rfl
      linarith [q_pos, hetaPos, hqeq]
    have hDenLoPos : 0 < q / 2 - eps := by linarith [hepsLeQ4, q_pos]
    have hRealGapHi : r5Ch - rCoPlus ≤
        (r5Ch * ((2 * Real.log 2 - phaseGain5 (phaseDelta n)) + eta)) /
          ((q / 2 - eps) * a ^ 2) := by
      rcases le_or_gt rCoPlus r5Ch with hOrd | hOrd
      · have hHasDeriv : ∀ x ∈ Icc lower upper,
            HasDerivAt F
              (q + (Real.log (profileDualPartition (phaseNat n + 1)
                  (profileDualTilt (phaseNat n + 1) ((n : ℝ) / x))) - Real.log x)) x :=
          fun x hx ↦ hasDerivAt_cocoloringUnrestrictedPhaseObjective hfive
            (hDom' x hx).1 (hDom' x hx).2
        have hSub : Icc rCoPlus r5Ch ⊆ Icc lower upper :=
          fun x hx ↦ ⟨hCoMem.1.trans hx.1, hx.2.trans h5ChMem.2⟩
        have hContF : ContinuousOn F (Icc lower upper) :=
          fun x hx ↦ (hHasDeriv x hx).continuousAt.continuousWithinAt
        have hContSub : ContinuousOn F (Icc rCoPlus r5Ch) := hContF.mono hSub
        have hDiffSub : DifferentiableOn ℝ F (Ioo rCoPlus r5Ch) := fun x hx ↦
          (hHasDeriv x (hSub (Ioo_subset_Icc_self hx))).differentiableAt.differentiableWithinAt
        have hDerivSub : ∀ x ∈ Ioo rCoPlus r5Ch, (q / 2 - eps) * a ^ 2 ≤ deriv F x := by
          intro x hx
          have hxC := hSub (Ioo_subset_Icc_self hx)
          have hdF := (hHasDeriv x hxC).deriv
          have htar := (hDom' x hxC).2
          rw [fourSizeTarget, mem_Ioo] at htar
          have hsix : (6 : ℝ) ≤ phaseNat n := by exact_mod_cast (Nat.succ_le_of_lt hfive)
          have hdU := (hasDerivAt_profileDualOptimalValue_parts (by omega : 2 ≤ phaseNat n + 1)
            (hDom' x hxC).1 (by
              rw [mem_Ioo, show (((phaseNat n + 1 : ℕ)) : ℝ) = (phaseNat n : ℝ) + 1 by push_cast; ring]
              exact ⟨by linarith [htar.2], by linarith [htar.1]⟩)).deriv
          have hlo := (hDeriv x hxC).1
          unfold unrestrictedPhaseObjective at hlo
          rw [hdU] at hlo; rw [hdF]; linarith [q_pos]
        have hinc := derivative_lower_bound_mul_sub_le_sub hOrd hContSub hDiffSub hDerivSub
        rw [hCoRoot.1.2, sub_zero] at hinc
        apply (le_div_iff₀ (mul_pos hDenLoPos haSqPos)).mpr
        rw [mul_comm]
        exact hinc.trans hFR5Ch
      · have hneg : r5Ch - rCoPlus < 0 := by linarith
        exact hneg.le.trans (div_nonneg (mul_nonneg hr5ChPos.le hSpanNonneg)
          (mul_pos hDenLoPos haSqPos).le)
    have hShi : r5Ch / a ^ 2 ≤ (q ^ 3 / 8 + eps) * baseScale n := hScaleHi r5Ch h5ChMem
    have hCoeffHi :
        (((2 * Real.log 2 - phaseGain5 (phaseDelta n)) + eta) / (q / 2 - eps)) *
          (q ^ 3 / 8 + eps) ≤ upperPhaseCoeff (phaseDelta n) + t0 / 3 :=
      upperCoeff_quotient_le hdelta ht0Pos ht0Cap
    have hRealSpan : r5Ch - rCoPlus ≤ (upperPhaseCoeff (phaseDelta n) + t0 / 3) * baseScale n := by
      calc r5Ch - rCoPlus
          ≤ (r5Ch * ((2 * Real.log 2 - phaseGain5 (phaseDelta n)) + eta)) /
              ((q / 2 - eps) * a ^ 2) := hRealGapHi
        _ = (((2 * Real.log 2 - phaseGain5 (phaseDelta n)) + eta) / (q / 2 - eps)) *
              (r5Ch / a ^ 2) := by rw [mul_comm r5Ch, div_mul_div_comm]
        _ ≤ (((2 * Real.log 2 - phaseGain5 (phaseDelta n)) + eta) / (q / 2 - eps)) *
              ((q ^ 3 / 8 + eps) * baseScale n) :=
            mul_le_mul_of_nonneg_left hShi (div_nonneg hSpanNonneg hDenLoPos.le)
        _ = ((((2 * Real.log 2 - phaseGain5 (phaseDelta n)) + eta) / (q / 2 - eps)) *
              (q ^ 3 / 8 + eps)) * baseScale n := by ring
        _ ≤ (upperPhaseCoeff (phaseDelta n) + t0 / 3) * baseScale n :=
            mul_le_mul_of_nonneg_right hCoeffHi hBasePos.le
    -- Integer rounding for `hpChromaticIndex n - phaseCochromaticLowerIndex n`
    have hlognn : 0 ≤ Real.log (n : ℝ) :=
      (Real.log_pos (by exact_mod_cast hn2)).le
    have hChCast : (hpChromaticIndex n : ℝ) ≤ r5Ch + Real.log (n : ℝ) + 2 := by
      unfold hpChromaticIndex
      have hposInt : 0 ≤ ⌈r5Ch⌉ + ⌈Real.log (n : ℝ)⌉ :=
        add_nonneg (Int.ceil_nonneg hr5ChPos.le) (Int.ceil_nonneg hlognn)
      have hcast : ((⌈r5Ch⌉ + ⌈Real.log (n : ℝ)⌉).toNat : ℝ) =
          ((⌈r5Ch⌉ + ⌈Real.log (n : ℝ)⌉ : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hposInt
      rw [hcast]; push_cast
      linarith [Int.ceil_lt_add_one r5Ch, Int.ceil_lt_add_one (Real.log (n : ℝ))]
    -- `phaseCochromaticLowerIndex n > rCoPlus - log n - 2`
    have hCoZPos : 0 < rootChromaticIndex rCoPlus (Real.log (n : ℝ)) := by
      have h1 : (0 : ℝ) < (phaseCochromaticLowerIndex n : ℝ) := by exact_mod_cast hCoGeom.1
      unfold phaseCochromaticLowerIndex at h1
      by_contra hle
      have h0 : (rootChromaticIndex rCoPlus (Real.log (n : ℝ))).toNat = 0 :=
        Int.toNat_of_nonpos (not_lt.mp hle)
      rw [h0] at h1; norm_num at h1
    have hCoCast : rCoPlus - Real.log (n : ℝ) - 2 ≤ (phaseCochromaticLowerIndex n : ℝ) := by
      unfold phaseCochromaticLowerIndex
      have hcast : ((rootChromaticIndex rCoPlus (Real.log (n : ℝ))).toNat : ℝ) =
          (rootChromaticIndex rCoPlus (Real.log (n : ℝ)) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hCoZPos.le
      rw [hcast]; unfold rootChromaticIndex; push_cast
      linarith [Int.lt_floor_add_one rCoPlus, Int.ceil_lt_add_one (Real.log (n : ℝ))]
    have h2Log4 : 2 * Real.log (n : ℝ) + 4 ≤ (t0 / 3) * baseScale n := by
      have hRound' : Real.log (n : ℝ) + 19 ≤ fixedOffsetRoundingBudget n * baseScale n := hRound
      have h2R : 2 * Real.log (n : ℝ) + 4 ≤ 2 * (fixedOffsetRoundingBudget n * baseScale n) := by
        linarith
      have hbm := mul_le_mul_of_nonneg_right (by linarith [hBud] :
        2 * fixedOffsetRoundingBudget n ≤ t0 / 3) hBasePos.le
      linarith
    have hbLe : hpChromaticAllowance n ≤ (t0 / 3) * baseScale n :=
      ((div_lt_iff₀ hBasePos).mp hbN).le
    have hSpanBound : spanHi n ≤ (upperPhaseCoeff (phaseDelta n) + theta) * baseScale n := by
      have ht0Cmp : (upperPhaseCoeff (phaseDelta n) + t0) * baseScale n ≤
          (upperPhaseCoeff (phaseDelta n) + theta) * baseScale n :=
        mul_le_mul_of_nonneg_right (by linarith) hBasePos.le
      dsimp [spanHi]
      linarith
    linarith
  exact hMain

/-- **Unconditional Proposition 5.2 / `(A)` closure:** for the concrete manuscript
sequences `(phaseCochromaticLowerIndex, hpCochromaticIndex, phaseChromaticLowerIndex,
hpChromaticIndex, hpCochromaticAllowance, hpChromaticAllowance)`, there exists a
deterministic sequence `eps n ≥ 0` with `eps n → 0` satisfying both the inner
lower separation and the outer upper separation of `TwoSidedAssembly`. -/
theorem exists_concrete_fiveSize_twoSided_location_error :
    ∃ eps : ℕ → ℝ,
      (∀ n, 0 ≤ eps n) ∧
      Tendsto eps atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        (lowerPhaseCoeff (phaseDelta n) - eps n) * ((n : ℝ) / (Real.log n) ^ 3) ≤
          (phaseChromaticLowerIndex n : ℝ) - (hpCochromaticIndex n : ℝ) -
            hpCochromaticAllowance n ∧
        (hpChromaticIndex n : ℝ) + hpChromaticAllowance n -
            (phaseCochromaticLowerIndex n : ℝ) ≤
          (upperPhaseCoeff (phaseDelta n) + eps n) * ((n : ℝ) / (Real.log n) ^ 3) := by
  let gapLo : ℕ → ℝ := fun n ↦
    (phaseChromaticLowerIndex n : ℝ) - (hpCochromaticIndex n : ℝ) - hpCochromaticAllowance n
  let spanHi : ℕ → ℝ := fun n ↦
    (hpChromaticIndex n : ℝ) + hpChromaticAllowance n - (phaseCochromaticLowerIndex n : ℝ)
  obtain ⟨epsLo, hLoNn, hLoZero, hLoEv⟩ :=
    exists_nonneg_tendsto_zero_envelope (fun n ↦ lowerPhaseCoeff (phaseDelta n)) gapLo
      eventually_concrete_fiveSize_lower_separation
  obtain ⟨epsHi, hHiNn, hHiZero, hHiEv⟩ :=
    exists_nonneg_tendsto_zero_envelope (fun n ↦ -upperPhaseCoeff (phaseDelta n)) (-spanHi)
      eventually_concrete_fiveSize_upper_separation
  refine ⟨fun n ↦ max (epsLo n) (epsHi n),
    fun n ↦ (hLoNn n).trans (le_max_left _ _),
    by simpa using hLoZero.max hHiZero, ?_⟩
  filter_upwards [hLoEv, hHiEv, eventually_ge_atTop (2 : ℕ)] with n hL hH hn2
  have hBaseNonneg : 0 ≤ (n : ℝ) / (Real.log n) ^ 3 := by
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
    have hnpos : 0 < (n : ℝ) := by positivity
    positivity
  have hBaseEq : baseScale n = (n : ℝ) / (Real.log n) ^ 3 := rfl
  rw [hBaseEq] at hL hH
  dsimp [gapLo, spanHi] at hL hH
  have hMaxL := mul_le_mul_of_nonneg_right
    (sub_le_sub_left (le_max_left (epsLo n) (epsHi n)) (lowerPhaseCoeff (phaseDelta n)))
    hBaseNonneg
  have hMaxH := mul_le_mul_of_nonneg_right
    (sub_le_sub_left (le_max_right (epsLo n) (epsHi n)) (-upperPhaseCoeff (phaseDelta n)))
    hBaseNonneg
  exact ⟨hMaxL.trans hL, by linarith⟩

/-- **Concrete Two-Sided Phase Refinement and `[0.063, 0.104]` Main Theorem:**
instantiated at the manuscript's actual concrete sequences
`(phaseCochromaticLowerIndex, hpCochromaticIndex, phaseChromaticLowerIndex,
hpChromaticIndex, hpCochromaticAllowance, hpChromaticAllowance)`, with `(A)`,
`(B)` (both first-moment lower tails), and Section 8 amplification discharged
unconditionally, isolating as hypotheses the two `G(n, 1/2)` rare-seed
probability lower bounds obtained from Proposition 7.7 via Paley–Zygmund. -/
theorem concrete_twoSided_phase_and_uniform_gap_of_hp_seeds
    {C_sm C'_sm : ℝ} (hC_sm : 0 < C_sm) (hC'_sm : 0 < C'_sm)
    (hSeedCo : ∀ᶠ n : ℕ in atTop,
      Real.exp (-C_sm * (n : ℝ) ^ (9 / 10 : ℝ) / Real.log (n : ℝ)) ≤
        (randomGraphMeasure n).real {G | cochromaticNumber G ≤ hpCochromaticIndex n})
    (hSeedCh : ∀ᶠ n : ℕ in atTop,
      Real.exp (-C'_sm * (Real.log (n : ℝ)) ^ 2) ≤
        (randomGraphMeasure n).real {G | chromaticNumberNat G ≤ hpChromaticIndex n}) :
    (∃ eps : ℕ → ℝ,
      (∀ n, 0 ≤ eps n) ∧
      Tendsto eps atTop (nhds 0) ∧
      Tendsto (fun n ↦ randomGraphMeasure n
        (twoSidedGapEvent (lowerPhaseCoeff (phaseDelta n) - eps n)
          (upperPhaseCoeff (phaseDelta n) + eps n) n)) atTop (nhds 1)) ∧
    Tendsto (fun n ↦ randomGraphMeasure n
      (twoSidedGapEvent (63 / 1000) (104 / 1000) n)) atTop (nhds 1) := by
  obtain ⟨eps, hepsNn, hepsZero, hLoc⟩ := exists_concrete_fiveSize_twoSided_location_error
  have hChiLow :=
    chromaticLowerEvent_probability_tendsto_one_of_atMost_tendsto_zero
      phaseChromaticLowerIndex
      randomGraphMeasure_chromaticNumberAtMost_phaseChromaticLowerIndex_tendsto_zero
  have hZetaLow := randomGraphMeasure_phaseCochromaticLowerIndex_lt_cochromaticNumber_tendsto_one
  have hZetaUp := (hp_cochromatic_upperTail_of_secondMoment_seed
    hpCochromaticIndex hC_sm hSeedCo).2
  have hChiUp := (hp_chromatic_upperTail_of_secondMoment_seed
    hpChromaticIndex hC'_sm hSeedCh).2
  have hBoth := twoSided_phase_and_uniform_gap_tendsto_one
    phaseCochromaticLowerIndex hpCochromaticIndex
    phaseChromaticLowerIndex hpChromaticIndex
    hpCochromaticAllowance hpChromaticAllowance eps
    hepsZero hLoc hChiLow hZetaUp hZetaLow hChiUp
  exact ⟨⟨eps, hepsNn, hepsZero, hBoth.1⟩, hBoth.2⟩

end

end Erdos625HP
