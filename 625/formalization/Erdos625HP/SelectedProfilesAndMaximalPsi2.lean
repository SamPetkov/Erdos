import Erdos625HP.InfiniteDualsLowerTailsAndCompleteRegularity

/-!
# v13 Running-supremum `ψ₂` / `L^p` maximal bounds, finite-window slopes & Gibbs optimizers, and unconditional Proposition 5.3 & Lemma 6.1

This module formalizes the first half of the v13 end-to-end unconditional closure using **zero**
public definitions (`0` public `def`/`abbrev`/`structure` declarations) and only the standard Lean
kernel foundations (`propext`, `Classical.choice`, `Quot.sound`):

1. **Main Theorem `(i)` & `(iv)` and Corollary 8.1 — Coupling-uniform running-supremum Orlicz `ψ₂`,
   square-exponential moment, and `L^p` bounds:**
   - `coupling_orliczPsi2_sup_normalizedGap_center_le`: for all couplings `(Ω, ℙ, G)` with marginals
     `G(m, 1/2)` (`m ≥ 2`) and all `n : ℕ` with `exp 12 ≤ (n : ℝ)`, proves almost-sure boundedness
     and `AEStronglyMeasurable` of `sup_{m ≥ n} |Y_m - E[Y_m]|` and the non-asymptotic Orlicz `ψ₂`
     bound `‖sup_{m ≥ n} |Y_m - E[Y_m]|‖_{ψ₂} ≤ 4 (log₂ n)³ √((log n) / n)`.
   - `tendsto_lp_zero_of_orliczPsi2_tendsto_zero`: on arbitrary probability spaces `(Ω_n, ℙ_n)`,
     `‖Z_n‖_{ψ₂} → 0` implies `E[|Z_n|^p] → 0` for every `1 ≤ p < ∞`.
   - `coupling_orliczPsi2_and_moments_sup_normalizedGap_sub_quarter`: derives from `E[Y_n] → 1/4`
     and any coupling of `(G_m)_{m ≥ 2}` the Main Theorem `(iv)` non-asymptotic running-supremum
     `ψ₂` bound `‖S_n‖_{ψ₂} ≤ 4 (log₂ n)³ √((log n) / n) + sup_{m ≥ n} |E[Y_m] - 1/4| / √(log 2)`,
     `‖S_n‖_{ψ₂} → 0`, `E[exp(M S_n²)] → 1` (`M ≥ 0`), and `E[S_n^p] → 0` (`1 ≤ p < ∞`).

2. **Section 3 — Lemma 3.1 finite-window & capped corridor slopes `(3.7)` + objective difference
   `(3.8)`, and Lemma 3.2(i)–(ii) finite-block tilts & simplex optimizers (`(3.10)`–`(3.12)`):**
   - `existsUnique_windowFiniteGibbsTilt_and_optimizer_bounds_lemma32_ii`
   - `eventually_window_and_capped_phaseObjective_deriv_and_diff_lemma31`

3. **Section 5.2 & Section 6 — Complete unconditional Proposition 5.3(i)–(ii) selected integer
   profiles and unconditional Lemma 6.1(i)–(ii) + Scrambled/Middle common-class subprofile sums:**
   - `eventually_selectedProfiles_prop53_regimeU`
   - `eventually_selectedProfiles_prop53_regimeC`
   - `eventually_selectedProfiles_lemma61_and_commonClass_sums_regimeU`
   - `eventually_selectedProfiles_lemma61_and_commonClass_sums_regimeC`
-/

namespace Erdos625HP

open Erdos625 Erdos625.FiveSizeEntropyGap FiveSizePhaseGainSharp FiveSizePhaseGainCertificate
open Filter Asymptotics MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

/-!
## 1. Coupling-uniform running-supremum Orlicz `ψ₂`, square-exponential, and `L^p` bounds
-/

private theorem monotoneOn_sqrt_div_log_pow_six :
    MonotoneOn (fun x : ℝ ↦ Real.sqrt x / (Real.log x) ^ 6) (Set.Ici (Real.exp 12)) := by
  have hexp12_gt1 : 1 < Real.exp 12 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hcont : ContinuousOn (fun x : ℝ ↦ Real.sqrt x / (Real.log x) ^ 6)
      (Set.Ici (Real.exp 12)) := by
    refine Real.continuous_sqrt.continuousOn.div ?_ ?_
    · refine ContinuousOn.pow ?_ 6
      exact Real.continuousOn_log.mono fun x hx ↦
        (lt_trans zero_lt_one (lt_of_lt_of_le hexp12_gt1 hx)).ne'
    · intro x hx
      have hlog12 : (12 : ℝ) ≤ Real.log x := by
        have h := Real.log_le_log (Real.exp_pos 12) hx
        rwa [Real.log_exp] at h
      exact pow_ne_zero 6 (by linarith)
  have hderiv : ∀ x > Real.exp 12,
      HasDerivAt (fun y : ℝ ↦ Real.sqrt y / (Real.log y) ^ 6)
        (((1 / (2 * Real.sqrt x)) * (Real.log x) ^ 6 -
            Real.sqrt x * (((6 : ℕ) * (Real.log x) ^ (6 - 1)) * x⁻¹)) /
          ((Real.log x) ^ 6) ^ 2) x := by
    intro x hx
    have hx_pos : 0 < x := lt_trans (Real.exp_pos 12) hx
    have hlog12 : 12 < Real.log x := by
      have h := Real.log_lt_log (Real.exp_pos 12) hx
      rwa [Real.log_exp] at h
    have hd1 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
      Real.hasDerivAt_sqrt hx_pos.ne'
    have hd2 : HasDerivAt (fun y : ℝ ↦ (Real.log y) ^ 6)
        (((6 : ℕ) * (Real.log x) ^ (6 - 1)) * x⁻¹) x :=
      (Real.hasDerivAt_log hx_pos.ne').pow 6
    exact hd1.div hd2 (pow_pos (by linarith) 6).ne'
  apply monotoneOn_of_deriv_nonneg (convex_Ici (Real.exp 12)) hcont
  · intro x hx
    rw [interior_Ici] at hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx_pos : 0 < x := lt_trans (Real.exp_pos 12) hx
    have hs_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
    have hlog12 : 12 < Real.log x := by
      have h := Real.log_lt_log (Real.exp_pos 12) hx
      rwa [Real.log_exp] at h
    have hlog_pos : 0 < Real.log x := by linarith
    rw [(hderiv x hx).deriv]
    have hx_sq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx_pos.le
    have hnum :
        (1 / (2 * Real.sqrt x)) * (Real.log x) ^ 6 -
            Real.sqrt x * (((6 : ℕ) * (Real.log x) ^ (6 - 1)) * x⁻¹) =
          ((Real.log x) ^ 5 * (Real.log x - 12)) / (2 * Real.sqrt x) := by
      push_cast
      field_simp [hs_pos.ne', hx_pos.ne']
      rw [hx_sq]
      ring
    rw [hnum]
    exact div_nonneg (div_nonneg (mul_nonneg (pow_nonneg hlog_pos.le 5) (by linarith))
      (by positivity)) (sq_nonneg _)

private theorem exp_neg_le_256_div_pow_four {y : ℝ} (hy : 0 < y) :
    Real.exp (-y) ≤ 256 / y ^ 4 := by
  have h1 : y / 4 ≤ Real.exp (y / 4) := by linarith [Real.add_one_le_exp (y / 4)]
  have hpow : (y / 4) ^ 4 ≤ Real.exp y := by
    calc (y / 4) ^ 4
        ≤ (Real.exp (y / 4)) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
      _ = Real.exp (((4 : ℕ) : ℝ) * (y / 4)) := (Real.exp_nat_mul (y / 4) 4).symm
      _ = Real.exp y := by push_cast; congr 1; ring
  have hmul : Real.exp (-y) * (y ^ 4 / 256) ≤ 1 := by
    have hq : y ^ 4 / 256 = (y / 4) ^ 4 := by ring
    rw [hq]
    calc Real.exp (-y) * (y / 4) ^ 4
        ≤ Real.exp (-y) * Real.exp y := mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = Real.exp (-y + y) := (Real.exp_add (-y) y).symm
      _ = 1 := by simp
  rw [le_div_iff₀ (pow_pos hy 4)]
  linarith

private theorem scale_a_bounds_v13 {n m : ℕ} (hn12 : Real.exp 12 ≤ (n : ℝ)) (hnm : n ≤ m) :
    let s_n : ℝ := 4 * (Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (Real.log (n : ℝ) / (n : ℝ))
    let a_m : ℝ := s_n ^ 2 * (m : ℝ) / (2 * (Real.logb 2 (m : ℝ)) ^ 6)
    2 ≤ n ∧ 0 < s_n ∧
      8 * Real.log (n : ℝ) * Real.sqrt ((m : ℝ) / (n : ℝ)) ≤ a_m ∧
      96 ≤ a_m ∧
      2 * Real.exp (-a_m / 4) ≤ (2 / 81 : ℝ) * (n : ℝ) / (m : ℝ) ^ 2 := by
  intro s_n a_m
  have hexp1_gt2 : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hexp12_gt2 : (2 : ℝ) < Real.exp 12 :=
    lt_trans hexp1_gt2 (Real.exp_lt_exp.mpr (by norm_num))
  have hn_gt2 : (2 : ℝ) < (n : ℝ) := lt_of_lt_of_le hexp12_gt2 hn12
  have hn2 : 2 ≤ n := by
    have hlt : 2 < n := by exact_mod_cast hn_gt2
    omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hnm_cast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hm_pos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hn_pos hnm_cast
  have hLn12 : (12 : ℝ) ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 12) hn12
    rwa [Real.log_exp] at h
  have hLn_pos : 0 < Real.log (n : ℝ) := by linarith
  have hLm12 : (12 : ℝ) ≤ Real.log (m : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 12) (hn12.trans hnm_cast)
    rwa [Real.log_exp] at h
  have hLm_pos : 0 < Real.log (m : ℝ) := by linarith
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlbn_pos : 0 < Real.logb 2 (n : ℝ) := by
    rw [Real.logb]; exact div_pos hLn_pos hq_pos
  have hlbm_pos : 0 < Real.logb 2 (m : ℝ) := by
    rw [Real.logb]; exact div_pos hLm_pos hq_pos
  have hs_pos : 0 < s_n := by
    dsimp [s_n]
    exact mul_pos (mul_pos (by norm_num) (pow_pos hlbn_pos 3))
      (Real.sqrt_pos.mpr (div_pos hLn_pos hn_pos))
  have hs_sq : s_n ^ 2 = 16 * (Real.logb 2 (n : ℝ)) ^ 6 * (Real.log (n : ℝ) / (n : ℝ)) := by
    dsimp [s_n]
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hLn_pos.le hn_pos.le)]
    ring
  have ha_eq :
      a_m = 8 * Real.log (n : ℝ) *
        (((Real.log (n : ℝ)) ^ 6 / (n : ℝ)) * ((m : ℝ) / (Real.log (m : ℝ)) ^ 6)) := by
    dsimp [a_m]
    rw [hs_sq, Real.logb, Real.logb, div_pow, div_pow]
    field_simp [hn_pos.ne', hLm_pos.ne', hq_pos.ne']
    ring
  have hmono := monotoneOn_sqrt_div_log_pow_six hn12 (hn12.trans hnm_cast) hnm_cast
  have hratio :
      Real.sqrt ((m : ℝ) / (n : ℝ)) ≤
        ((Real.log (n : ℝ)) ^ 6 / (n : ℝ)) * ((m : ℝ) / (Real.log (m : ℝ)) ^ 6) := by
    have hmul := mul_le_mul_of_nonneg_left hmono
      (div_nonneg (mul_nonneg (pow_pos hLn_pos 6).le (Real.sqrt_nonneg (m : ℝ))) hn_pos.le)
    have hlhs :
        ((Real.log (n : ℝ)) ^ 6 * Real.sqrt (m : ℝ) / (n : ℝ)) *
            (Real.sqrt (n : ℝ) / (Real.log (n : ℝ)) ^ 6) =
          Real.sqrt ((m : ℝ) / (n : ℝ)) := by
      rw [Real.sqrt_div hm_pos.le]
      have hsn_ne : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn_pos).ne'
      field_simp [hn_pos.ne', hLn_pos.ne', hsn_ne]
      exact Real.sq_sqrt hn_pos.le
    have hrhs :
        ((Real.log (n : ℝ)) ^ 6 * Real.sqrt (m : ℝ) / (n : ℝ)) *
            (Real.sqrt (m : ℝ) / (Real.log (m : ℝ)) ^ 6) =
          ((Real.log (n : ℝ)) ^ 6 / (n : ℝ)) * ((m : ℝ) / (Real.log (m : ℝ)) ^ 6) := by
      field_simp [hn_pos.ne', hLm_pos.ne']
      exact Real.sq_sqrt hm_pos.le
    rwa [hlhs, hrhs] at hmul
  have ha_ge : 8 * Real.log (n : ℝ) * Real.sqrt ((m : ℝ) / (n : ℝ)) ≤ a_m := by
    rw [ha_eq]
    exact mul_le_mul_of_nonneg_left hratio (by positivity)
  have hsqrt_ge1 : 1 ≤ Real.sqrt ((m : ℝ) / (n : ℝ)) := by
    rw [Real.le_sqrt zero_le_one (div_nonneg hm_pos.le hn_pos.le), one_pow]
    exact (one_le_div hn_pos).mpr hnm_cast
  have ha_ge96 : 96 ≤ a_m := by
    have h1 : (96 : ℝ) ≤ 8 * Real.log (n : ℝ) * 1 := by linarith
    have h2 : 8 * Real.log (n : ℝ) * 1 ≤ 8 * Real.log (n : ℝ) * Real.sqrt ((m : ℝ) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hsqrt_ge1 (by positivity)
    linarith
  refine ⟨hn2, hs_pos, ha_ge, ha_ge96, ?_⟩
  have ha8_ge_Ln : Real.log (n : ℝ) ≤ a_m / 8 := by
    have h1 : 8 * Real.log (n : ℝ) * 1 ≤ a_m :=
      (mul_le_mul_of_nonneg_left hsqrt_ge1 (by positivity)).trans ha_ge
    linarith
  have hexp1 : Real.exp (-(a_m / 8)) ≤ (n : ℝ)⁻¹ := by
    calc Real.exp (-(a_m / 8))
        ≤ Real.exp (-Real.log (n : ℝ)) := Real.exp_le_exp.mpr (by linarith)
      _ = (Real.exp (Real.log (n : ℝ)))⁻¹ := Real.exp_neg _
      _ = (n : ℝ)⁻¹ := by rw [Real.exp_log hn_pos]
  have ha8_ge_12 : 12 * Real.sqrt ((m : ℝ) / (n : ℝ)) ≤ a_m / 8 := by
    have h1 : 12 * Real.sqrt ((m : ℝ) / (n : ℝ)) ≤ Real.log (n : ℝ) * Real.sqrt ((m : ℝ) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hLn12 (Real.sqrt_nonneg _)
    linarith
  have ha8_pos : 0 < a_m / 8 := by linarith
  have hpow4 :
      20736 * ((m : ℝ) / (n : ℝ)) ^ 2 ≤ (a_m / 8) ^ 4 := by
    have hsq_r : (Real.sqrt ((m : ℝ) / (n : ℝ))) ^ 4 = ((m : ℝ) / (n : ℝ)) ^ 2 := by
      calc (Real.sqrt ((m : ℝ) / (n : ℝ))) ^ 4
          = ((Real.sqrt ((m : ℝ) / (n : ℝ))) ^ 2) ^ 2 := by ring
        _ = ((m : ℝ) / (n : ℝ)) ^ 2 := by rw [Real.sq_sqrt (div_nonneg hm_pos.le hn_pos.le)]
    calc 20736 * ((m : ℝ) / (n : ℝ)) ^ 2
        = (12 * Real.sqrt ((m : ℝ) / (n : ℝ))) ^ 4 := by rw [mul_pow, hsq_r]; norm_num
      _ ≤ (a_m / 8) ^ 4 := pow_le_pow_left₀ (by positivity) ha8_ge_12 4
  have hexp2 : Real.exp (-(a_m / 8)) ≤ (1 / 81 : ℝ) * (n : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
    calc Real.exp (-(a_m / 8))
        ≤ 256 / (a_m / 8) ^ 4 := exp_neg_le_256_div_pow_four ha8_pos
      _ ≤ 256 / (20736 * ((m : ℝ) / (n : ℝ)) ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow4
      _ = (1 / 81 : ℝ) * (n : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
          field_simp [hn_pos.ne', hm_pos.ne']; ring
  have hsplit_exp : Real.exp (-a_m / 4) = Real.exp (-(a_m / 8)) * Real.exp (-(a_m / 8)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit_exp]
  calc 2 * (Real.exp (-(a_m / 8)) * Real.exp (-(a_m / 8)))
      ≤ 2 * ((n : ℝ)⁻¹ * ((1 / 81 : ℝ) * (n : ℝ) ^ 2 / (m : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hexp1 hexp2 (Real.exp_pos _).le (inv_nonneg.mpr hn_pos.le)) zero_le_two
    _ = (2 / 81 : ℝ) * (n : ℝ) / (m : ℝ) ^ 2 := by
        field_simp [hn_pos.ne', hm_pos.ne']

private theorem marginal_excess_integral_le_v13 {n m : ℕ}
    (hn12 : Real.exp 12 ≤ (n : ℝ)) (hnm : n ≤ m) :
    let s_n : ℝ := 4 * (Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (Real.log (n : ℝ) / (n : ℝ))
    let Y_m : LabeledGraph m → ℝ := fun H ↦
      (Real.logb 2 (m : ℝ)) ^ 3 / (m : ℝ) *
        ((chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ))
    let μ_m : ℝ := ∫ H : LabeledGraph m, Y_m H ∂randomGraphMeasure m
    let u_m : LabeledGraph m → ℝ := fun H ↦ Real.exp ((Y_m H - μ_m) ^ 2 / s_n ^ 2)
    (∫ H : LabeledGraph m, max 0 (u_m H - 7 / 4) ∂randomGraphMeasure m) ≤
      (2 / 81 : ℝ) * (n : ℝ) / (m : ℝ) ^ 2 := by
  intro s_n Y_m μ_m u_m
  obtain ⟨hn2, hs_pos, -, ha_ge96, hdecay⟩ := scale_a_bounds_v13 hn12 hnm
  have hm2 : 2 ≤ m := le_trans hn2 hnm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hlbm_pos : 0 < Real.logb 2 (m : ℝ) :=
    Real.logb_pos one_lt_two (by exact_mod_cast (show 1 < m by omega))
  set a_m : ℝ := s_n ^ 2 * (m : ℝ) / (2 * (Real.logb 2 (m : ℝ)) ^ 6)
  have ha_pos : 0 < a_m := by linarith
  -- Factor 1: P(u_m > 7/4) ≤ 2 exp(-a_m / 2)
  have hexp_half_lt : Real.exp (1 / 2 : ℝ) < 7 / 4 := by
    have hsq : (Real.exp (1 / 2 : ℝ)) ^ 2 < (7 / 4 : ℝ) ^ 2 := by
      have h1 : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
        rw [sq, ← Real.exp_add]; norm_num
      rw [h1]
      exact lt_trans Real.exp_one_lt_d9 (by norm_num)
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  set u_thr : ℝ := s_n / Real.sqrt 2
  have huthr_nn : 0 ≤ u_thr := div_nonneg hs_pos.le (Real.sqrt_nonneg 2)
  have hsub_tail :
      {H : LabeledGraph m | (7 / 4 : ℝ) < u_m H} ⊆
        {H : LabeledGraph m | u_thr ≤ |Y_m H - μ_m|} := by
    intro H hH
    rw [Set.mem_setOf_eq] at hH ⊢
    have hexp_lt : Real.exp (1 / 2 : ℝ) < Real.exp ((Y_m H - μ_m) ^ 2 / s_n ^ 2) :=
      lt_trans hexp_half_lt hH
    have hhalf_lt : (1 / 2 : ℝ) < (Y_m H - μ_m) ^ 2 / s_n ^ 2 := Real.exp_lt_exp.mp hexp_lt
    have hsq_le : u_thr ^ 2 ≤ |Y_m H - μ_m| ^ 2 := by
      dsimp [u_thr]
      rw [div_pow, Real.sq_sqrt zero_le_two, sq_abs]
      have hm := (lt_div_iff₀ (sq_pos_of_pos hs_pos)).mp hhalf_lt
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num : 2 ≠ 0) (abs_nonneg _) hsq_le
  have hprob_le :
      (randomGraphMeasure m).real {H : LabeledGraph m | (7 / 4 : ℝ) < u_m H} ≤
        2 * Real.exp (-a_m / 2) := by
    have ht := (measureReal_mono hsub_tail).trans
      (randomGraph_abs_normalizedGap_sub_mean_ge_le hm2 huthr_nn)
    have hexp_eq :
        -u_thr ^ 2 * (m : ℝ) / (2 * (Real.logb 2 (m : ℝ)) ^ 6) = -a_m / 2 := by
      dsimp [u_thr, a_m]
      rw [div_pow, Real.sq_sqrt zero_le_two]
      field_simp [hlbm_pos.ne']
    rwa [hexp_eq] at ht
  -- Factor 2: ∫ (u_m H)^2 ≤ 2 via θ = 3 / 8
  have hint_sq_le :
      (∫ H : LabeledGraph m, (u_m H) ^ 2 ∂randomGraphMeasure m) ≤ 2 := by
    have hpt : ∀ H : LabeledGraph m,
        (u_m H) ^ 2 ≤
          Real.exp ((3 / 8 : ℝ) * (m : ℝ) * (Y_m H - μ_m) ^ 2 / (Real.logb 2 (m : ℝ)) ^ 6) := by
      intro H
      dsimp [u_m]
      rw [sq, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hrew : (Y_m H - μ_m) ^ 2 / s_n ^ 2 + (Y_m H - μ_m) ^ 2 / s_n ^ 2 =
          (1 / a_m) * ((m : ℝ) * (Y_m H - μ_m) ^ 2 / (Real.logb 2 (m : ℝ)) ^ 6) := by
        dsimp [a_m]
        field_simp [hs_pos.ne', hm_pos.ne', hlbm_pos.ne']
        ring
      rw [hrew]
      have h1a : 1 / a_m ≤ 3 / 8 := by
        rw [div_le_iff₀ ha_pos]
        linarith
      have hfac_nn : 0 ≤ (m : ℝ) * (Y_m H - μ_m) ^ 2 / (Real.logb 2 (m : ℝ)) ^ 6 := by positivity
      calc (1 / a_m) * ((m : ℝ) * (Y_m H - μ_m) ^ 2 / (Real.logb 2 (m : ℝ)) ^ 6)
          ≤ (3 / 8 : ℝ) * ((m : ℝ) * (Y_m H - μ_m) ^ 2 / (Real.logb 2 (m : ℝ)) ^ 6) :=
            mul_le_mul_of_nonneg_right h1a hfac_nn
        _ = (3 / 8 : ℝ) * (m : ℝ) * (Y_m H - μ_m) ^ 2 / (Real.logb 2 (m : ℝ)) ^ 6 := by ring
    have hsq38 := sqExpMoment_normalizedGap_le hm2
      (show (3 / 8 : ℝ) ∈ Set.Ico (0 : ℝ) (1 / 2) by constructor <;> norm_num)
    have htwo : ((1 : ℝ) - 2 * (3 / 8 : ℝ)) ^ (-(1 / 2 : ℝ)) = 2 := by
      have h1 : (1 : ℝ) - 2 * (3 / 8 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by norm_num
      rw [h1, ← Real.rpow_mul two_pos.le]; norm_num
    rw [htwo] at hsq38
    exact (integral_mono Integrable.of_finite Integrable.of_finite hpt).trans hsq38
  -- Finite Cauchy-Schwarz on `LabeledGraph m`
  classical
  let w : LabeledGraph m → ℝ := fun H ↦ (randomGraphMeasure m).real {H}
  let ind : LabeledGraph m → ℝ := fun H ↦ if (7 / 4 : ℝ) < u_m H then 1 else 0
  have hw_nn : ∀ H, 0 ≤ w H := fun _ ↦ measureReal_nonneg
  have hmax_le : ∀ H : LabeledGraph m,
      w H * max 0 (u_m H - 7 / 4) ≤
        (Real.sqrt (w H) * ind H) * (Real.sqrt (w H) * u_m H) := by
    intro H
    have hsqw : Real.sqrt (w H) * Real.sqrt (w H) = w H := Real.mul_self_sqrt (hw_nn H)
    have h1 : (Real.sqrt (w H) * ind H) * (Real.sqrt (w H) * u_m H) =
        w H * (ind H * u_m H) := by
      calc (Real.sqrt (w H) * ind H) * (Real.sqrt (w H) * u_m H)
          = (Real.sqrt (w H) * Real.sqrt (w H)) * (ind H * u_m H) := by ring
        _ = w H * (ind H * u_m H) := by rw [hsqw]
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ (hw_nn H)
    dsimp [ind]
    split_ifs with hgt
    · rw [one_mul, max_eq_right (by linarith)]
      linarith
    · rw [zero_mul, max_eq_left (by linarith)]
  have hint_lhs :
      (∫ H : LabeledGraph m, max 0 (u_m H - 7 / 4) ∂randomGraphMeasure m) =
        ∑ H : LabeledGraph m, w H * max 0 (u_m H - 7 / 4) := by
    rw [integral_fintype Integrable.of_finite]
    simp_rw [smul_eq_mul, w]
  have hsum_ind :
      (∑ H : LabeledGraph m, (Real.sqrt (w H) * ind H) ^ 2) =
        (randomGraphMeasure m).real {H : LabeledGraph m | (7 / 4 : ℝ) < u_m H} := by
    have hpt_i : ∀ H : LabeledGraph m,
        (Real.sqrt (w H) * ind H) ^ 2 =
          ({H' : LabeledGraph m | (7 / 4 : ℝ) < u_m H'}.indicator (fun _ ↦ (1 : ℝ)) H) * w H := by
      intro H
      rw [mul_pow, Real.sq_sqrt (hw_nn H)]
      dsimp [ind]
      by_cases hgt : (7 / 4 : ℝ) < u_m H
      · have hmem : H ∈ {H' : LabeledGraph m | (7 / 4 : ℝ) < u_m H'} := hgt
        rw [if_pos hgt, Set.indicator_of_mem hmem]; ring
      · have hnot : H ∉ {H' : LabeledGraph m | (7 / 4 : ℝ) < u_m H'} := hgt
        rw [if_neg hgt, Set.indicator_of_notMem hnot]; ring
    simp_rw [hpt_i, mul_comm _ (w _)]
    have hi :
        (∑ H : LabeledGraph m,
            w H * ({H' : LabeledGraph m | (7 / 4 : ℝ) < u_m H'}.indicator (fun _ ↦ (1 : ℝ)) H)) =
          ∫ H : LabeledGraph m,
            ({H' : LabeledGraph m | (7 / 4 : ℝ) < u_m H'}.indicator (fun _ ↦ (1 : ℝ)) H)
            ∂randomGraphMeasure m := by
      rw [integral_fintype Integrable.of_finite]
      simp_rw [smul_eq_mul, w]
    rw [hi, integral_indicator_const _ (Set.toFinite _).measurableSet, smul_eq_mul, mul_one]
  have hsum_u2 :
      (∑ H : LabeledGraph m, (Real.sqrt (w H) * u_m H) ^ 2) =
        ∫ H : LabeledGraph m, (u_m H) ^ 2 ∂randomGraphMeasure m := by
    rw [integral_fintype Integrable.of_finite]
    refine Finset.sum_congr rfl fun H _ ↦ ?_
    rw [mul_pow, Real.sq_sqrt (hw_nn H), smul_eq_mul]
  have hint_nn : 0 ≤ ∫ H : LabeledGraph m, max 0 (u_m H - 7 / 4) ∂randomGraphMeasure m :=
    integral_nonneg fun H ↦ le_max_left 0 _
  have hcs_sq :
      (∫ H : LabeledGraph m, max 0 (u_m H - 7 / 4) ∂randomGraphMeasure m) ^ 2 ≤
        (2 * Real.exp (-a_m / 4)) ^ 2 := by
    have hle1 :
        (∫ H : LabeledGraph m, max 0 (u_m H - 7 / 4) ∂randomGraphMeasure m) ≤
          ∑ H : LabeledGraph m, (Real.sqrt (w H) * ind H) * (Real.sqrt (w H) * u_m H) := by
      rw [hint_lhs]
      exact Finset.sum_le_sum fun H _ ↦ hmax_le H
    calc (∫ H : LabeledGraph m, max 0 (u_m H - 7 / 4) ∂randomGraphMeasure m) ^ 2
        ≤ (∑ H : LabeledGraph m, (Real.sqrt (w H) * ind H) * (Real.sqrt (w H) * u_m H)) ^ 2 :=
          pow_le_pow_left₀ hint_nn hle1 2
      _ ≤ (∑ H : LabeledGraph m, (Real.sqrt (w H) * ind H) ^ 2) *
            (∑ H : LabeledGraph m, (Real.sqrt (w H) * u_m H) ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
      _ = ((randomGraphMeasure m).real {H : LabeledGraph m | (7 / 4 : ℝ) < u_m H}) *
            (∫ H : LabeledGraph m, (u_m H) ^ 2 ∂randomGraphMeasure m) := by
          rw [hsum_ind, hsum_u2]
      _ ≤ (2 * Real.exp (-a_m / 2)) * 2 :=
          mul_le_mul hprob_le hint_sq_le
            (integral_nonneg fun _ ↦ sq_nonneg _) (by positivity)
      _ = (2 * Real.exp (-a_m / 4)) ^ 2 := by
          have hexp_sq : (Real.exp (-a_m / 4)) ^ 2 = Real.exp (-a_m / 2) := by
            rw [sq, ← Real.exp_add]; congr 1; ring
          rw [mul_pow, hexp_sq]
          ring
  have hle_exp4 :
      (∫ H : LabeledGraph m, max 0 (u_m H - 7 / 4) ∂randomGraphMeasure m) ≤
        2 * Real.exp (-a_m / 4) :=
    le_of_pow_le_pow_left₀ (by norm_num : 2 ≠ 0) (by positivity) hcs_sq
  exact hle_exp4.trans hdecay

private theorem sum_inv_sq_range_le_two_div {n : ℕ} (hn2 : 2 ≤ n) (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1), (1 / ((n + k : ℕ) : ℝ) ^ 2)) ≤ 2 / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  have hterm : ∀ k : ℕ,
      1 / ((n + k : ℕ) : ℝ) ^ 2 ≤
        1 / ((n + k - 1 : ℕ) : ℝ) - 1 / ((n + k : ℕ) : ℝ) := by
    intro k
    set m : ℕ := n + k
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by dsimp [m]; omega)
    have hm1_pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < m - 1 by dsimp [m]; omega)
    have hm1_eq : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by dsimp [m]; omega : 1 ≤ m), Nat.cast_one]
    have hdiff : 1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ) = 1 / (((m - 1 : ℕ) : ℝ) * (m : ℝ)) := by
      field_simp [hm1_pos.ne', hm_pos.ne']
      rw [hm1_eq]; ring
    rw [hdiff]
    refine div_le_div_of_nonneg_left zero_le_one (mul_pos hm1_pos hm_pos) ?_
    rw [hm1_eq]; nlinarith
  let g : ℕ → ℝ := fun k ↦ 1 / ((n - 1 + k : ℕ) : ℝ)
  have htel :
      (∑ k ∈ Finset.range (K + 1), (1 / ((n + k - 1 : ℕ) : ℝ) - 1 / ((n + k : ℕ) : ℝ))) =
        1 / ((n - 1 : ℕ) : ℝ) - 1 / ((n + K : ℕ) : ℝ) := by
    have hcongr : ∀ k : ℕ,
        1 / ((n + k - 1 : ℕ) : ℝ) - 1 / ((n + k : ℕ) : ℝ) = g k - g (k + 1) := by
      intro k
      dsimp [g]
      have h1 : n + k - 1 = n - 1 + k := by omega
      have h2 : n + k = n - 1 + (k + 1) := by omega
      rw [h1, h2]
    simp_rw [hcongr]
    have hs := Finset.sum_range_sub' g (K + 1)
    dsimp [g] at hs
    have h3 : n - 1 + (K + 1) = n + K := by omega
    simpa only [Nat.add_zero, h3] using hs
  calc (∑ k ∈ Finset.range (K + 1), (1 / ((n + k : ℕ) : ℝ) ^ 2))
      ≤ ∑ k ∈ Finset.range (K + 1), (1 / ((n + k - 1 : ℕ) : ℝ) - 1 / ((n + k : ℕ) : ℝ)) :=
        Finset.sum_le_sum fun k _ ↦ hterm k
    _ = 1 / ((n - 1 : ℕ) : ℝ) - 1 / ((n + K : ℕ) : ℝ) := htel
    _ ≤ 1 / ((n - 1 : ℕ) : ℝ) := by
        have : 0 ≤ 1 / ((n + K : ℕ) : ℝ) := by positivity
        linarith
    _ ≤ 2 / (n : ℝ) := by
        rw [div_le_div_iff₀ hn1_pos hn_pos]
        have hn1_eq : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
        rw [hn1_eq]
        have hn_ge2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
        linarith

private def prefixMaxSeq (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => |f 0|
  | K + 1 => max (prefixMaxSeq f K) |f (K + 1)|

private theorem prefixMaxSeq_nonneg (f : ℕ → ℝ) (K : ℕ) : 0 ≤ prefixMaxSeq f K := by
  induction K with
  | zero => exact abs_nonneg _
  | succ K ih => exact ih.trans (le_max_left _ _)

private theorem prefixMaxSeq_mono (f : ℕ → ℝ) : Monotone (prefixMaxSeq f) :=
  monotone_nat_of_le_succ fun _ ↦ le_max_left _ _

private theorem abs_le_prefixMaxSeq (f : ℕ → ℝ) {j K : ℕ} (hj : j ≤ K) :
    |f j| ≤ prefixMaxSeq f K := by
  induction K with
  | zero =>
    have hj0 : j = 0 := by omega
    subst hj0; exact le_rfl
  | succ K ih =>
    rcases Nat.of_le_succ hj with hle | rfl
    · exact (ih hle).trans (le_max_left _ _)
    · exact le_max_right _ _

private theorem prefixMaxSeq_le_of_forall (f : ℕ → ℝ) {B : ℝ} (K : ℕ)
    (h : ∀ j ≤ K, |f j| ≤ B) : prefixMaxSeq f K ≤ B := by
  induction K with
  | zero => exact h 0 le_rfl
  | succ K ih =>
    exact max_le (ih fun j hj ↦ h j (Nat.le_succ_of_le hj)) (h (K + 1) le_rfl)

private theorem measurable_prefixMaxSeq {Ω : Type*} [MeasurableSpace Ω]
    {f : ℕ → Ω → ℝ} (hf : ∀ k, Measurable (f k)) (K : ℕ) :
    Measurable (fun ω ↦ prefixMaxSeq (fun k ↦ f k ω) K) := by
  induction K with
  | zero => exact (hf 0).abs
  | succ K ih => exact ih.max (hf (K + 1)).abs

private theorem exp_prefixMaxSeq_le_sum_excess (f : ℕ → ℝ) {s : ℝ} (_hs : 0 < s) (K : ℕ) :
    Real.exp ((prefixMaxSeq f K) ^ 2 / s ^ 2) ≤
      (7 / 4 : ℝ) +
        ∑ k ∈ Finset.range (K + 1), max 0 (Real.exp (|f k| ^ 2 / s ^ 2) - 7 / 4) := by
  induction K with
  | zero =>
    rw [prefixMaxSeq, Nat.zero_add, Finset.range_one, Finset.sum_singleton]
    have h1 : Real.exp (|f 0| ^ 2 / s ^ 2) - 7 / 4 ≤
        max 0 (Real.exp (|f 0| ^ 2 / s ^ 2) - 7 / 4) := le_max_right _ _
    linarith
  | succ K ih =>
    rw [prefixMaxSeq, Finset.sum_range_succ]
    have hexp_max :
        Real.exp ((max (prefixMaxSeq f K) |f (K + 1)|) ^ 2 / s ^ 2) =
          max (Real.exp ((prefixMaxSeq f K) ^ 2 / s ^ 2))
            (Real.exp (|f (K + 1)| ^ 2 / s ^ 2)) := by
      rcases le_total (prefixMaxSeq f K) |f (K + 1)| with hle | hle
      · have hsq : (prefixMaxSeq f K) ^ 2 / s ^ 2 ≤ |f (K + 1)| ^ 2 / s ^ 2 :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (prefixMaxSeq_nonneg f K) hle 2) (sq_nonneg s)
        rw [max_eq_right hle, max_eq_right (Real.exp_le_exp.mpr hsq)]
      · have hsq : |f (K + 1)| ^ 2 / s ^ 2 ≤ (prefixMaxSeq f K) ^ 2 / s ^ 2 :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hle 2) (sq_nonneg s)
        rw [max_eq_left hle, max_eq_left (Real.exp_le_exp.mpr hsq)]
    rw [hexp_max]
    refine max_le ?_ ?_
    · have hnn : 0 ≤ max 0 (Real.exp (|f (K + 1)| ^ 2 / s ^ 2) - 7 / 4) := le_max_left 0 _
      linarith
    · have hsum_nn :
          0 ≤ ∑ k ∈ Finset.range (K + 1), max 0 (Real.exp (|f k| ^ 2 / s ^ 2) - 7 / 4) :=
        Finset.sum_nonneg fun _ _ ↦ le_max_left 0 _
      have hlast : Real.exp (|f (K + 1)| ^ 2 / s ^ 2) - 7 / 4 ≤
          max 0 (Real.exp (|f (K + 1)| ^ 2 / s ^ 2) - 7 / 4) := le_max_right _ _
      linarith

/-- **Main Theorem `(i)` & Corollary 8.1 non-asymptotic coupling-uniform running-supremum Orlicz `ψ₂`
bound (`main.tex` lines 114–116, 1149–1150):**
for every joint coupling `(Ω, ℙ, G)` with marginals `G_m ∼ G(m, 1/2)` (`m ≥ 2`) and every `n : ℕ`
with `exp 12 ≤ (n : ℝ)`:
1. almost surely `(m ≥ n) ↦ |Y_m(G_m(ω)) - E[Y_m]|` is bounded above;
2. `SupCenter(ω) := ⨆ m : {m : ℕ // n ≤ m}, |Y_m(G_m(ω)) - E[Y_m]|` is `AEStronglyMeasurable`;
3. the Orlicz `ψ₂` scale set `S_sup` is nonempty, bounded below, and satisfies
   `sInf S_sup ≤ 4 (log₂ n)³ √((log n) / n)`. -/
theorem coupling_orliczPsi2_sup_normalizedGap_center_le
    {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (G : ∀ m : ℕ, Ω → LabeledGraph m)
    (hMarg : ∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m)
    {n : ℕ} (hn12 : Real.exp 12 ≤ (n : ℝ)) :
    let Y : ∀ m : ℕ, LabeledGraph m → ℝ := fun m H ↦
      (Real.logb 2 (m : ℝ)) ^ 3 / (m : ℝ) *
        ((chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ))
    let meanY : ℕ → ℝ := fun m ↦ ∫ H : LabeledGraph m, Y m H ∂randomGraphMeasure m
    let SupCenter : Ω → ℝ := fun ω ↦ ⨆ m : {m : ℕ // n ≤ m}, |Y m.1 (G m.1 ω) - meanY m.1|
    let S_sup : Set ℝ := {s : ℝ | 0 < s ∧
      Integrable (fun ω ↦ Real.exp ((SupCenter ω) ^ 2 / s ^ 2)) ℙ ∧
      (∫ ω : Ω, Real.exp ((SupCenter ω) ^ 2 / s ^ 2) ∂ℙ) ≤ 2}
    (∀ᵐ ω ∂ℙ, BddAbove (Set.range fun m : {m : ℕ // n ≤ m} ↦ |Y m.1 (G m.1 ω) - meanY m.1|)) ∧
      AEStronglyMeasurable SupCenter ℙ ∧
      S_sup.Nonempty ∧ BddBelow S_sup ∧
      sInf S_sup ≤ 4 * (Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) := by
  intro Y meanY SupCenter S_sup
  obtain ⟨hn2, hs_pos, -, -, -⟩ := scale_a_bounds_v13 hn12 le_rfl
  set s_n : ℝ := 4 * (Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (Real.log (n : ℝ) / (n : ℝ))
  -- Step 1: Almost-sure boundedness via `ae_limsup_chromaticSubCochromatic_and_normalizedGap_le_one`
  have hb_zero : Tendsto (fun m : ℕ ↦
      (1 + (1 : ℝ)) * (Real.logb 2 (m : ℝ)) ^ 3 * Real.sqrt (2 * Real.log (m : ℝ) / (m : ℝ)))
      atTop (nhds 0) := by
    have ho : (fun x : ℝ ↦ (Real.log x) ^ ((7 / 2 : ℝ))) =o[atTop]
        (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) :=
      isLittleO_log_rpow_rpow_atTop (7 / 2 : ℝ) (by norm_num)
    have ht0 := (ho.comp_tendsto tendsto_natCast_atTop_atTop).tendsto_div_nhds_zero
    have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have ht1 := ht0.const_mul (2 * Real.sqrt 2 / (Real.log 2) ^ 3)
    rw [mul_zero] at ht1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht1
      (by filter_upwards [eventually_ge_atTop 2] with m hm2
          have hL_nn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
          have hlb_nn : 0 ≤ Real.logb 2 (m : ℝ) := div_nonneg hL_nn hq_pos.le
          positivity)
      (by filter_upwards [eventually_ge_atTop 3] with m hm3
          have hL_gt1 : 1 < Real.log (m : ℝ) := by
            have he_lt3 : Real.exp 1 < (m : ℝ) :=
              lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286 : ℝ) < 3))
                (show (3 : ℝ) ≤ (m : ℝ) by exact_mod_cast hm3)
            simpa using Real.log_lt_log (Real.exp_pos 1) he_lt3
          have hL_pos : 0 < Real.log (m : ℝ) := lt_trans zero_lt_one hL_gt1
          rw [Real.logb, div_pow, Real.sqrt_div (by positivity), Real.sqrt_mul zero_le_two,
            Real.sqrt_eq_rpow (Real.log (m : ℝ)), Real.sqrt_eq_rpow (m : ℝ),
            ← Real.rpow_natCast (Real.log (m : ℝ)) 3]
          have hadd_p : (Real.log (m : ℝ)) ^ ((3 : ℕ) : ℝ) * (Real.log (m : ℝ)) ^ (1 / 2 : ℝ) =
              (Real.log (m : ℝ)) ^ (7 / 2 : ℝ) := by
            rw [← Real.rpow_add hL_pos]; norm_num
          calc (1 + (1 : ℝ)) * ((Real.log (m : ℝ)) ^ ((3 : ℕ) : ℝ) / (Real.log 2) ^ 3) *
                  (Real.sqrt 2 * (Real.log (m : ℝ)) ^ (1 / 2 : ℝ) / (m : ℝ) ^ (1 / 2 : ℝ))
              = (2 * Real.sqrt 2 / (Real.log 2) ^ 3) *
                  (((Real.log (m : ℝ)) ^ ((3 : ℕ) : ℝ) * (Real.log (m : ℝ)) ^ (1 / 2 : ℝ)) /
                    (m : ℝ) ^ (1 / 2 : ℝ)) := by ring
            _ = (2 * Real.sqrt 2 / (Real.log 2) ^ 3) *
                  ((Real.log (m : ℝ)) ^ (7 / 2 : ℝ) / (m : ℝ) ^ (1 / 2 : ℝ)) := by rw [hadd_p]
            _ ≤ _ := le_rfl)
  have hdet_le1 := hb_zero.eventually (ge_mem_nhds zero_lt_one)
  have hae_env := (ae_limsup_chromaticSubCochromatic_and_normalizedGap_le_one ℙ G hMarg).1 zero_lt_one
  have hae_bdd :
      ∀ᵐ ω ∂ℙ, BddAbove (Set.range fun m : {m : ℕ // n ≤ m} ↦ |Y m.1 (G m.1 ω) - meanY m.1|) := by
    filter_upwards [hae_env] with ω hω
    obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp (hω.and hdet_le1)
    let B : ℝ := max 1 (prefixMaxSeq (fun k ↦ |Y (n + k) (G (n + k) ω) - meanY (n + k)|) M₀)
    refine ⟨B, ?_⟩
    rintro _ ⟨⟨m, hmn⟩, rfl⟩
    by_cases hmM : m ≤ n + M₀
    · have hk : m - n ≤ M₀ := by omega
      have h1 := abs_le_prefixMaxSeq (fun k ↦ |Y (n + k) (G (n + k) ω) - meanY (n + k)|) hk
      rw [Nat.add_sub_of_le hmn, abs_abs] at h1
      exact h1.trans (le_max_right _ _)
    · have hm_ge : M₀ ≤ m := by omega
      obtain ⟨⟨-, hYm⟩, hb1⟩ := hM₀ m hm_ge
      exact (hYm.trans hb1).trans (le_max_left _ _)
  -- Step 2: Measurable representatives `A'_k` and monotone prefix maxima `M'_K`
  let A : ℕ → Ω → ℝ := fun k ω ↦ |Y (n + k) (G (n + k) ω) - meanY (n + k)|
  have hA_aem : ∀ k : ℕ, AEMeasurable (A k) ℙ := by
    intro k
    have hm2 : 2 ≤ n + k := by omega
    have hGm := aemeasurable_of_map_eq_randomGraphMeasure (hMarg (n + k) hm2)
    exact (measurable_of_finite (fun H : LabeledGraph (n + k) ↦ |Y (n + k) H - meanY (n + k)|)).comp_aemeasurable hGm
  let A' : ℕ → Ω → ℝ := fun k ↦ (hA_aem k).mk (A k)
  have hA'_meas : ∀ k : ℕ, Measurable (A' k) := fun k ↦ (hA_aem k).measurable_mk
  have hA'_ae_all : ∀ᵐ ω ∂ℙ, ∀ k : ℕ, A' k ω = A k ω :=
    ae_all_iff.mpr fun k ↦ (hA_aem k).ae_eq_mk.symm
  let M' : ℕ → Ω → ℝ := fun K ω ↦ prefixMaxSeq (fun k ↦ A' k ω) K
  have hM'_meas : ∀ K : ℕ, Measurable (M' K) := fun K ↦ measurable_prefixMaxSeq hA'_meas K
  have hM'_tendsto_ae : ∀ᵐ ω ∂ℙ,
      SupCenter ω = (⨆ K : ℕ, M' K ω) ∧ Tendsto (fun K ↦ M' K ω) atTop (nhds (SupCenter ω)) := by
    filter_upwards [hae_bdd, hA'_ae_all] with ω hBdd hEq
    have hA'_abs : ∀ k : ℕ, |A' k ω| = A k ω := fun k ↦ by
      rw [hEq k]; exact abs_of_nonneg (abs_nonneg _)
    have hM'_le_sup : ∀ K : ℕ, M' K ω ≤ SupCenter ω := by
      intro K
      refine prefixMaxSeq_le_of_forall _ K fun j _ ↦ ?_
      rw [hA'_abs j]
      exact le_ciSup hBdd (⟨n + j, Nat.le_add_right n j⟩ : {m : ℕ // n ≤ m})
    have hBddM' : BddAbove (Set.range fun K : ℕ ↦ M' K ω) :=
      ⟨SupCenter ω, by rintro _ ⟨K, rfl⟩; exact hM'_le_sup K⟩
    have hsup_eq : SupCenter ω = ⨆ K : ℕ, M' K ω := by
      apply le_antisymm
      · refine ciSup_le fun ⟨m, hmn⟩ ↦ ?_
        have hm_eq : n + (m - n) = m := Nat.add_sub_of_le hmn
        have h1 : A (m - n) ω ≤ M' (m - n) ω := by
          rw [← hA'_abs (m - n)]
          exact abs_le_prefixMaxSeq (fun k ↦ A' k ω) le_rfl
        have h2 : M' (m - n) ω ≤ ⨆ K : ℕ, M' K ω := le_ciSup hBddM' (m - n)
        dsimp [A] at h1
        rw [hm_eq] at h1
        exact h1.trans h2
      · exact ciSup_le hM'_le_sup
    refine ⟨hsup_eq, ?_⟩
    rw [hsup_eq]
    exact tendsto_atTop_ciSup (fun a b hab ↦ prefixMaxSeq_mono _ hab) hBddM'
  have hSup_aem : AEStronglyMeasurable SupCenter ℙ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun K ↦ (hM'_meas K).aestronglyMeasurable)
      (hM'_tendsto_ae.mono fun _ h ↦ h.2)
  -- Step 3: Finite-`K` lintegral bound ≤ 2 and monotone convergence
  let V' : ℕ → Ω → ℝ := fun K ω ↦ Real.exp ((M' K ω) ^ 2 / s_n ^ 2)
  have hV'_meas : ∀ K : ℕ, Measurable (V' K) := by
    intro K
    have hc : Continuous (fun x : ℝ ↦ Real.exp (x ^ 2 / s_n ^ 2)) := by fun_prop
    exact hc.measurable.comp (hM'_meas K)
  have hV'_lint_le : ∀ K : ℕ, (∫⁻ ω : Ω, ENNReal.ofReal (V' K ω) ∂ℙ) ≤ 2 := by
    intro K
    let exc : ℕ → Ω → ℝ := fun k ω ↦ max 0 (Real.exp ((A k ω) ^ 2 / s_n ^ 2) - 7 / 4)
    have hexc_int : ∀ k : ℕ, Integrable (exc k) ℙ ∧
        (∫ ω : Ω, exc k ω ∂ℙ) ≤ (2 / 81 : ℝ) * (n : ℝ) / ((n + k : ℕ) : ℝ) ^ 2 := by
      intro k
      set m : ℕ := n + k
      have hnm : n ≤ m := Nat.le_add_right n k
      have hm2 : 2 ≤ m := le_trans hn2 hnm
      have hGm := aemeasurable_of_map_eq_randomGraphMeasure (hMarg m hm2)
      let φ : LabeledGraph m → ℝ := fun H ↦
        max 0 (Real.exp ((Y m H - meanY m) ^ 2 / s_n ^ 2) - 7 / 4)
      have hφ_int_map : Integrable φ (Measure.map (G m) ℙ) := by
        rw [hMarg m hm2]; exact Integrable.of_finite
      have hexc_eq : exc k = φ ∘ G m := by
        funext ω
        dsimp [exc, φ, A, m]
        rw [sq_abs]
      rw [hexc_eq]
      refine ⟨hφ_int_map.comp_aemeasurable hGm, ?_⟩
      have hmap_eq : (∫ ω : Ω, φ (G m ω) ∂ℙ) = ∫ H : LabeledGraph m, φ H ∂randomGraphMeasure m := by
        rw [← integral_map hGm hφ_int_map.aestronglyMeasurable, hMarg m hm2]
      dsimp only [Function.comp_apply]
      rw [hmap_eq]
      exact marginal_excess_integral_le_v13 hn12 hnm
    let maj : Ω → ℝ := fun ω ↦ (7 / 4 : ℝ) + ∑ k ∈ Finset.range (K + 1), exc k ω
    have hmaj_int : Integrable maj ℙ :=
      (integrable_const (7 / 4 : ℝ)).add
        (integrable_finsetSum (Finset.range (K + 1)) fun k _ ↦ (hexc_int k).1)
    have hV'_le_maj : ∀ᵐ ω ∂ℙ, V' K ω ≤ maj ω := by
      filter_upwards [hA'_ae_all] with ω hEq
      have hb := exp_prefixMaxSeq_le_sum_excess (fun k ↦ A' k ω) hs_pos K
      have hsum_eq :
          (∑ k ∈ Finset.range (K + 1), max 0 (Real.exp (|A' k ω| ^ 2 / s_n ^ 2) - 7 / 4)) =
            ∑ k ∈ Finset.range (K + 1), exc k ω := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [hEq k, sq_abs]
      dsimp [V', M', maj]
      rwa [hsum_eq] at hb
    have hmaj_int_le2 : (∫ ω : Ω, maj ω ∂ℙ) ≤ 2 := by
      have hint_eq : (∫ ω : Ω, maj ω ∂ℙ) =
          (7 / 4 : ℝ) + ∑ k ∈ Finset.range (K + 1), ∫ ω : Ω, exc k ω ∂ℙ := by
        dsimp [maj]
        rw [integral_add (integrable_const _)
          (integrable_finsetSum _ fun k _ ↦ (hexc_int k).1),
          integral_finsetSum _ fun k _ ↦ (hexc_int k).1]
        simp [integral_const, probReal_univ]
      rw [hint_eq]
      have hsum_le :
          (∑ k ∈ Finset.range (K + 1), ∫ ω : Ω, exc k ω ∂ℙ) ≤ 4 / 81 := by
        calc (∑ k ∈ Finset.range (K + 1), ∫ ω : Ω, exc k ω ∂ℙ)
            ≤ ∑ k ∈ Finset.range (K + 1), ((2 / 81 : ℝ) * (n : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) :=
              Finset.sum_le_sum fun k _ ↦ (hexc_int k).2
          _ = ((2 / 81 : ℝ) * (n : ℝ)) *
                ∑ k ∈ Finset.range (K + 1), (1 / ((n + k : ℕ) : ℝ) ^ 2) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun _ _ ↦ by ring
          _ ≤ ((2 / 81 : ℝ) * (n : ℝ)) * (2 / (n : ℝ)) :=
              mul_le_mul_of_nonneg_left (sum_inv_sq_range_le_two_div hn2 K) (by positivity)
          _ = 4 / 81 := by
              have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
              field_simp [hn_pos.ne']; ring
      linarith
    have hmaj_nn : ∀ ω : Ω, 0 ≤ maj ω := fun ω ↦ by
      dsimp [maj]
      exact add_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦ le_max_left 0 _)
    calc (∫⁻ ω : Ω, ENNReal.ofReal (V' K ω) ∂ℙ)
        ≤ ∫⁻ ω : Ω, ENNReal.ofReal (maj ω) ∂ℙ :=
          lintegral_mono_ae (hV'_le_maj.mono fun _ h ↦ ENNReal.ofReal_le_ofReal h)
      _ = ENNReal.ofReal (∫ ω : Ω, maj ω ∂ℙ) :=
          (ofReal_integral_eq_lintegral_ofReal hmaj_int (Eventually.of_forall hmaj_nn)).symm
      _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hmaj_int_le2
      _ = 2 := by norm_num
  have hmono_enn : Monotone (fun K ω ↦ ENNReal.ofReal (V' K ω)) := by
    intro a b hab ω
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (prefixMaxSeq_nonneg _ a) (prefixMaxSeq_mono _ hab) 2) (sq_nonneg s_n)
  have hSup_enn_ae : ∀ᵐ ω ∂ℙ,
      ENNReal.ofReal (Real.exp ((SupCenter ω) ^ 2 / s_n ^ 2)) =
        ⨆ K : ℕ, ENNReal.ofReal (V' K ω) := by
    filter_upwards [hM'_tendsto_ae] with ω ⟨_, hM'_lim⟩
    have hc : Continuous (fun x : ℝ ↦ ENNReal.ofReal (Real.exp (x ^ 2 / s_n ^ 2))) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    have ht1 : Tendsto (fun K ↦ ENNReal.ofReal (V' K ω)) atTop
        (nhds (ENNReal.ofReal (Real.exp ((SupCenter ω) ^ 2 / s_n ^ 2)))) :=
      (hc.tendsto (SupCenter ω)).comp hM'_lim
    have ht2 : Tendsto (fun K ↦ ENNReal.ofReal (V' K ω)) atTop
        (nhds (⨆ K : ℕ, ENNReal.ofReal (V' K ω))) :=
      tendsto_atTop_iSup fun a b hab ↦ hmono_enn hab ω
    exact tendsto_nhds_unique ht1 ht2
  have hlint_sup_le2 :
      (∫⁻ ω : Ω, ENNReal.ofReal (Real.exp ((SupCenter ω) ^ 2 / s_n ^ 2)) ∂ℙ) ≤ 2 := by
    rw [lintegral_congr_ae hSup_enn_ae,
      lintegral_iSup (fun K ↦ (hV'_meas K).ennreal_ofReal) hmono_enn]
    exact iSup_le hV'_lint_le
  have hexp_aem : AEStronglyMeasurable (fun ω ↦ Real.exp ((SupCenter ω) ^ 2 / s_n ^ 2)) ℙ := by
    have hc : Continuous (fun x : ℝ ↦ Real.exp (x ^ 2 / s_n ^ 2)) := by fun_prop
    exact hc.comp_aestronglyMeasurable hSup_aem
  have hexp_int : Integrable (fun ω ↦ Real.exp ((SupCenter ω) ^ 2 / s_n ^ 2)) ℙ := by
    refine ⟨hexp_aem, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)]
    exact lt_of_le_of_lt hlint_sup_le2 (by norm_num)
  have hint_le2 : (∫ ω : Ω, Real.exp ((SupCenter ω) ^ 2 / s_n ^ 2) ∂ℙ) ≤ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun _ ↦ (Real.exp_pos _).le) hexp_aem]
    have htr := ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hlint_sup_le2
    simpa using htr
  have hs_mem : s_n ∈ S_sup := ⟨hs_pos, hexp_int, hint_le2⟩
  have hbdd : BddBelow S_sup := ⟨0, fun s hs ↦ hs.1.le⟩
  exact ⟨hae_bdd, hSup_aem, ⟨s_n, hs_mem⟩, hbdd, csInf_le hbdd hs_mem⟩

private theorem rpow_le_const_mul_exp_sq {u s p : ℝ} (hu : 0 ≤ u) (hs : 0 < s) (hp : 1 ≤ p) :
    u ^ p ≤ s ^ p * (1 + (p / Real.exp 1) ^ p) * Real.exp (u ^ 2 / s ^ 2) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  set v : ℝ := u / s
  have hv_nn : 0 ≤ v := div_nonneg hu hs.le
  have huv : u = s * v := by dsimp [v]; exact (mul_div_cancel₀ u hs.ne').symm
  have hvp : v ^ p ≤ (1 + (p / Real.exp 1) ^ p) * Real.exp (v ^ 2) := by
    rcases le_or_gt v 1 with hv1 | hv1
    · have hv_le1 : v ^ p ≤ 1 := Real.rpow_le_one hv_nn hv1 hp_pos.le
      have hc_ge1 : 1 ≤ 1 + (p / Real.exp 1) ^ p :=
        le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) p)
      have hexp_ge1 : 1 ≤ Real.exp (v ^ 2) := Real.one_le_exp (sq_nonneg v)
      calc v ^ p ≤ 1 := hv_le1
        _ = 1 * 1 := (mul_one 1).symm
        _ ≤ (1 + (p / Real.exp 1) ^ p) * Real.exp (v ^ 2) :=
            mul_le_mul hc_ge1 hexp_ge1 zero_le_one (by positivity)
    · have hv_le_sq : v ≤ v ^ 2 := by nlinarith
      have hvp_le : v ^ p ≤ (v ^ 2) ^ p := Real.rpow_le_rpow hv_nn hv_le_sq hp_pos.le
      have ht_pos : 0 < v ^ 2 := sq_pos_of_pos (lt_trans zero_lt_one hv1)
      have hlin : v ^ 2 / p ≤ Real.exp (v ^ 2 / p - 1) := by
        linarith [Real.add_one_le_exp (v ^ 2 / p - 1)]
      have hrp := Real.rpow_le_rpow (div_nonneg ht_pos.le hp_pos.le) hlin hp_pos.le
      rw [Real.div_rpow ht_pos.le hp_pos.le, ← Real.exp_mul] at hrp
      have hm := (div_le_iff₀ (Real.rpow_pos_of_pos hp_pos p)).mp hrp
      have hrhs_eq :
          Real.exp ((v ^ 2 / p - 1) * p) * p ^ p =
            (p / Real.exp 1) ^ p * Real.exp (v ^ 2) := by
        have h1 : (v ^ 2 / p - 1) * p = v ^ 2 + (-p) := by field_simp [hp_pos.ne']; ring
        rw [h1, Real.exp_add, Real.div_rpow hp_pos.le (Real.exp_pos 1).le]
        have hexp_p : (Real.exp 1) ^ p = Real.exp p := by
          rw [Real.rpow_def_of_pos (Real.exp_pos 1), Real.log_exp, one_mul]
        have hexp_neg_p : Real.exp (-p) = (Real.exp p)⁻¹ := Real.exp_neg p
        rw [hexp_p, hexp_neg_p]
        field_simp [(Real.exp_pos p).ne']
      rw [hrhs_eq] at hm
      calc v ^ p ≤ (v ^ 2) ^ p := hvp_le
        _ ≤ (p / Real.exp 1) ^ p * Real.exp (v ^ 2) := hm
        _ ≤ (1 + (p / Real.exp 1) ^ p) * Real.exp (v ^ 2) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  rw [huv, Real.mul_rpow hs.le hv_nn]
  have hv_sq : (s * v) ^ 2 / s ^ 2 = v ^ 2 := by field_simp [hs.ne']
  rw [hv_sq, mul_assoc]
  exact mul_le_mul_of_nonneg_left hvp (Real.rpow_nonneg hs.le p)

/-- **Main Theorem `(iv)` & Section 9 general Orlicz `ψ₂ → L^p` convergence (`main.tex` lines 135, 1301–1302):**
if a sequence `Z_n` on probability spaces `(Ω_n, ℙ_n)` satisfies `‖Z_n‖_{ψ₂} → 0` (with
`S_n.Nonempty` eventually), then for every `1 ≤ p < ∞`, `|Z_n|^p` is eventually integrable and
`lim_{n → ∞} E[|Z_n|^p] = 0`. -/
theorem tendsto_lp_zero_of_orliczPsi2_tendsto_zero
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (ℙ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (ℙ n)]
    (Z : ∀ n, Ω n → ℝ) (hZ : ∀ n, AEStronglyMeasurable (Z n) (ℙ n))
    (hNe : ∀ᶠ n : ℕ in atTop,
      ({s : ℝ | 0 < s ∧
        Integrable (fun ω ↦ Real.exp ((Z n ω) ^ 2 / s ^ 2)) (ℙ n) ∧
        (∫ ω, Real.exp ((Z n ω) ^ 2 / s ^ 2) ∂ℙ n) ≤ 2}).Nonempty)
    (hPsi2 : Tendsto (fun n : ℕ ↦
      sInf {s : ℝ | 0 < s ∧
        Integrable (fun ω ↦ Real.exp ((Z n ω) ^ 2 / s ^ 2)) (ℙ n) ∧
        (∫ ω, Real.exp ((Z n ω) ^ 2 / s ^ 2) ∂ℙ n) ≤ 2}) atTop (nhds 0))
    {p : ℝ} (hp : 1 ≤ p) :
    (∀ᶠ n : ℕ in atTop, Integrable (fun ω ↦ |Z n ω| ^ p) (ℙ n)) ∧
      Tendsto (fun n : ℕ ↦ ∫ ω, |Z n ω| ^ p ∂ℙ n) atTop (nhds 0) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  set C_p : ℝ := 2 * (1 + (p / Real.exp 1) ^ p)
  have hCp_pos : 0 < C_p := by
    dsimp [C_p]
    have : 0 ≤ (p / Real.exp 1) ^ p := Real.rpow_nonneg (by positivity) p
    positivity
  have hstep : ∀ s₀ : ℝ, 0 < s₀ →
      ∀ᶠ n : ℕ in atTop,
        Integrable (fun ω ↦ |Z n ω| ^ p) (ℙ n) ∧
        0 ≤ ∫ ω, |Z n ω| ^ p ∂ℙ n ∧
        (∫ ω, |Z n ω| ^ p ∂ℙ n) ≤ C_p * s₀ ^ p := by
    intro s₀ hs₀
    filter_upwards [hNe, hPsi2.eventually (gt_mem_nhds hs₀)] with n hSn_ne hinf_lt
    obtain ⟨s, ⟨hs_pos, hInt_s, hle2⟩, hs_lt⟩ := exists_lt_of_csInf_lt hSn_ne hinf_lt
    have hc_abs : Continuous (fun t : ℝ ↦ |t| ^ p) :=
      continuous_abs.rpow_const fun _ ↦ Or.inr hp_pos.le
    have haesm_p : AEStronglyMeasurable (fun ω ↦ |Z n ω| ^ p) (ℙ n) :=
      hc_abs.comp_aestronglyMeasurable (hZ n)
    have hpt : ∀ ω : Ω n,
        |Z n ω| ^ p ≤
          (s ^ p * (1 + (p / Real.exp 1) ^ p)) * Real.exp ((Z n ω) ^ 2 / s ^ 2) := by
      intro ω
      have hb := rpow_le_const_mul_exp_sq (abs_nonneg (Z n ω)) hs_pos hp
      rwa [sq_abs] at hb
    have hInt_maj : Integrable
        (fun ω ↦ (s ^ p * (1 + (p / Real.exp 1) ^ p)) * Real.exp ((Z n ω) ^ 2 / s ^ 2)) (ℙ n) :=
      hInt_s.const_mul _
    have hInt_p : Integrable (fun ω ↦ |Z n ω| ^ p) (ℙ n) := by
      refine hInt_maj.mono' haesm_p (Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
      exact hpt ω
    refine ⟨hInt_p, integral_nonneg fun ω ↦ Real.rpow_nonneg (abs_nonneg _) p, ?_⟩
    calc (∫ ω, |Z n ω| ^ p ∂ℙ n)
        ≤ ∫ ω, (s ^ p * (1 + (p / Real.exp 1) ^ p)) * Real.exp ((Z n ω) ^ 2 / s ^ 2) ∂ℙ n :=
          integral_mono hInt_p hInt_maj hpt
      _ = (s ^ p * (1 + (p / Real.exp 1) ^ p)) * ∫ ω, Real.exp ((Z n ω) ^ 2 / s ^ 2) ∂ℙ n :=
          integral_const_mul _ _
      _ ≤ (s ^ p * (1 + (p / Real.exp 1) ^ p)) * 2 :=
          mul_le_mul_of_nonneg_left hle2 (by positivity)
      _ = C_p * s ^ p := by dsimp [C_p]; ring
      _ ≤ C_p * s₀ ^ p :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs_pos.le hs_lt.le hp_pos.le) hCp_pos.le
  refine ⟨(hstep 1 zero_lt_one).mono fun _ h ↦ h.1, ?_⟩
  rw [Metric.tendsto_nhds]
  intro eps heps
  set s₀ : ℝ := (eps / (2 * C_p)) ^ (1 / p)
  have hs₀_pos : 0 < s₀ := Real.rpow_pos_of_pos (div_pos heps (mul_pos two_pos hCp_pos)) _
  have hs₀_pow : C_p * s₀ ^ p = eps / 2 := by
    dsimp [s₀]
    rw [← Real.rpow_mul (div_nonneg heps.le (mul_pos two_pos hCp_pos).le),
      one_div_mul_cancel hp_pos.ne', Real.rpow_one]
    field_simp [hCp_pos.ne']
  filter_upwards [hstep s₀ hs₀_pos] with n ⟨_, hnn, hle⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

/-- **Main Theorem `(iv)` running-supremum Orlicz `ψ₂`, square-exponential moment, and `L^p`
convergence package (`main.tex` lines 130–135, 1296–1302):**
given `E[Y_n] → 1/4` and any coupling `(Ω, ℙ, G)` of `(G_m)_{m ≥ 2}` with marginals `G(m, 1/2)`:
1. for all `n ≥ 2`, `SupMeanErr n := ⨆ m ≥ n, |E[Y_m] - 1/4|` is well-defined (`BddAbove`), and
   `SupQuarter n ω := ⨆ m ≥ n, |Y_m(G_m(ω)) - 1/4|` is a.s. `BddAbove` and `AEStronglyMeasurable`;
2. for all `n : ℕ` with `exp 12 ≤ (n : ℝ)`, `S_supQ n` is nonempty, bounded below, and obeys
   `sInf (S_supQ n) ≤ 4 (log₂ n)³ √((log n) / n) + SupMeanErr n / √(log 2)`;
3. `lim_{n → ∞} sInf (S_supQ n) = 0`;
4. for every `M ≥ 0`, `exp(M S_n²)` is eventually integrable and `lim_{n → ∞} E[exp(M S_n²)] = 1`;
5. for every `1 ≤ p < ∞`, `S_n^p` is eventually integrable and `lim_{n → ∞} E[S_n^p] = 0`. -/
theorem coupling_orliczPsi2_and_moments_sup_normalizedGap_sub_quarter
    (hMeanLim : Tendsto (fun m : ℕ ↦
        ∫ H : LabeledGraph m,
          ((Real.logb 2 (m : ℝ)) ^ 3 / (m : ℝ) *
            ((chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ)))
          ∂randomGraphMeasure m)
      atTop (nhds (1 / 4 : ℝ)))
    {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (G : ∀ m : ℕ, Ω → LabeledGraph m)
    (hMarg : ∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m) :
    let Y : ∀ m : ℕ, LabeledGraph m → ℝ := fun m H ↦
      (Real.logb 2 (m : ℝ)) ^ 3 / (m : ℝ) *
        ((chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ))
    let meanY : ℕ → ℝ := fun m ↦ ∫ H : LabeledGraph m, Y m H ∂randomGraphMeasure m
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
        Tendsto (fun n : ℕ ↦ ∫ ω : Ω, (SupQuarter n ω) ^ p ∂ℙ) atTop (nhds 0)) := by
  intro Y meanY SupMeanErr SupQuarter S_supQ
  have herr_zero : Tendsto (fun m : ℕ ↦ |meanY m - 1 / 4|) atTop (nhds 0) := by
    have h := (hMeanLim.sub (tendsto_const_nhds (x := (1 / 4 : ℝ)))).abs
    rwa [sub_self, abs_zero] at h
  -- Boundedness of `|meanY m - 1/4|` for all `n`
  have hBddMean_all : ∀ n : ℕ,
      BddAbove (Set.range fun m : {m : ℕ // n ≤ m} ↦ |meanY m.1 - 1 / 4|) := by
    intro n
    obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp (herr_zero.eventually (ge_mem_nhds zero_lt_one))
    refine ⟨max 1 (prefixMaxSeq (fun k ↦ |meanY (n + k) - 1 / 4|) M₀), ?_⟩
    rintro _ ⟨⟨m, hmn⟩, rfl⟩
    by_cases hmM : m ≤ n + M₀
    · have hk : m - n ≤ M₀ := by omega
      have h1 := abs_le_prefixMaxSeq (fun k ↦ |meanY (n + k) - 1 / 4|) hk
      rw [Nat.add_sub_of_le hmn, abs_abs] at h1
      exact h1.trans (le_max_right _ _)
    · exact (hM₀ m (by omega)).trans (le_max_left _ _)
  have hSupMean_tendsto : Tendsto SupMeanErr atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro eps heps
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (herr_zero.eventually (ge_mem_nhds (half_pos heps)))
    filter_upwards [eventually_ge_atTop N₀] with n hn
    have hnn : 0 ≤ SupMeanErr n := Real.iSup_nonneg fun _ ↦ abs_nonneg _
    have hle : SupMeanErr n ≤ eps / 2 :=
      ciSup_le fun ⟨m, hmn⟩ ↦ hN₀ m (hn.trans hmn)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    linarith
  -- Measurability & a.s. boundedness of `SupQuarter n` for `n ≥ 2` (and a.e. Measurable for all `n`)
  have hReg_ge2 : ∀ {n : ℕ}, 2 ≤ n →
      BddAbove (Set.range fun m : {m : ℕ // n ≤ m} ↦ |meanY m.1 - 1 / 4|) ∧
      (∀ᵐ ω ∂ℙ, BddAbove (Set.range fun m : {m : ℕ // n ≤ m} ↦ |Y m.1 (G m.1 ω) - 1 / 4|)) ∧
      AEStronglyMeasurable (SupQuarter n) ℙ ∧
      (∀ᵐ ω ∂ℙ, SupQuarter n ω ≤
        (⨆ m : {m : ℕ // n ≤ m}, |Y m.1 (G m.1 ω) - meanY m.1|) + SupMeanErr n) := by
    intro n hn2
    set N_big : ℕ := max n (Nat.ceil (Real.exp 12))
    have hN_12 : Real.exp 12 ≤ (N_big : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right n _)
    obtain ⟨hae_bddN, -, -, -, -⟩ :=
      coupling_orliczPsi2_sup_normalizedGap_center_le ℙ G hMarg hN_12
    have hae_bdd_center :
        ∀ᵐ ω ∂ℙ, BddAbove (Set.range fun m : {m : ℕ // n ≤ m} ↦ |Y m.1 (G m.1 ω) - meanY m.1|) := by
      filter_upwards [hae_bddN] with ω ⟨BN, hBN⟩
      refine ⟨max BN (prefixMaxSeq (fun k ↦ |Y (n + k) (G (n + k) ω) - meanY (n + k)|) (N_big - n)), ?_⟩
      rintro _ ⟨⟨m, hmn⟩, rfl⟩
      by_cases hmN : m ≤ N_big
      · have hk : m - n ≤ N_big - n := by omega
        have h1 := abs_le_prefixMaxSeq (fun k ↦ |Y (n + k) (G (n + k) ω) - meanY (n + k)|) hk
        rw [Nat.add_sub_of_le hmn, abs_abs] at h1
        exact h1.trans (le_max_right _ _)
      · exact (hBN ⟨⟨m, by omega⟩, rfl⟩).trans (le_max_left _ _)
    have hae_bddQ_and_le :
        ∀ᵐ ω ∂ℙ,
          BddAbove (Set.range fun m : {m : ℕ // n ≤ m} ↦ |Y m.1 (G m.1 ω) - 1 / 4|) ∧
          SupQuarter n ω ≤
            (⨆ m : {m : ℕ // n ≤ m}, |Y m.1 (G m.1 ω) - meanY m.1|) + SupMeanErr n := by
      filter_upwards [hae_bdd_center] with ω hBddC
      have hpt : ∀ m : {m : ℕ // n ≤ m},
          |Y m.1 (G m.1 ω) - 1 / 4| ≤
            (⨆ j : {j : ℕ // n ≤ j}, |Y j.1 (G j.1 ω) - meanY j.1|) + SupMeanErr n := by
        intro m
        have htri : |Y m.1 (G m.1 ω) - 1 / 4| ≤
            |Y m.1 (G m.1 ω) - meanY m.1| + |meanY m.1 - 1 / 4| := by
          rw [show Y m.1 (G m.1 ω) - 1 / 4 =
            (Y m.1 (G m.1 ω) - meanY m.1) + (meanY m.1 - 1 / 4) by ring]
          exact abs_add_le _ _
        exact htri.trans (add_le_add (le_ciSup hBddC m) (le_ciSup (hBddMean_all n) m))
      have hBddQ : BddAbove (Set.range fun m : {m : ℕ // n ≤ m} ↦ |Y m.1 (G m.1 ω) - 1 / 4|) :=
        ⟨_, by rintro _ ⟨m, rfl⟩; exact hpt m⟩
      exact ⟨hBddQ, ciSup_le hpt⟩
    let Qk : ℕ → Ω → ℝ := fun k ω ↦ |Y (n + k) (G (n + k) ω) - 1 / 4|
    have hQk_aem : ∀ k : ℕ, AEMeasurable (Qk k) ℙ := by
      intro k
      have hGm := aemeasurable_of_map_eq_randomGraphMeasure (hMarg (n + k) (by omega))
      exact (measurable_of_finite (fun H : LabeledGraph (n + k) ↦ |Y (n + k) H - 1 / 4|)).comp_aemeasurable hGm
    let Qk' : ℕ → Ω → ℝ := fun k ↦ (hQk_aem k).mk (Qk k)
    have hQk'_meas : ∀ k : ℕ, Measurable (Qk' k) := fun k ↦ (hQk_aem k).measurable_mk
    have hQk'_ae : ∀ᵐ ω ∂ℙ, ∀ k : ℕ, Qk' k ω = Qk k ω :=
      ae_all_iff.mpr fun k ↦ (hQk_aem k).ae_eq_mk.symm
    let MQ' : ℕ → Ω → ℝ := fun K ω ↦ prefixMaxSeq (fun k ↦ Qk' k ω) K
    have hMQ'_meas : ∀ K : ℕ, Measurable (MQ' K) := fun K ↦ measurable_prefixMaxSeq hQk'_meas K
    have hMQ'_lim : ∀ᵐ ω ∂ℙ, Tendsto (fun K ↦ MQ' K ω) atTop (nhds (SupQuarter n ω)) := by
      filter_upwards [hae_bddQ_and_le, hQk'_ae] with ω ⟨hBddQ, _⟩ hEq
      have habs_k : ∀ k : ℕ, |Qk' k ω| = Qk k ω := fun k ↦ by
        rw [hEq k]; exact abs_of_nonneg (abs_nonneg _)
      have hle_sup : ∀ K : ℕ, MQ' K ω ≤ SupQuarter n ω := by
        intro K
        refine prefixMaxSeq_le_of_forall _ K fun j _ ↦ ?_
        rw [habs_k j]
        exact le_ciSup hBddQ (⟨n + j, Nat.le_add_right n j⟩ : {m : ℕ // n ≤ m})
      have hBddMQ : BddAbove (Set.range fun K : ℕ ↦ MQ' K ω) :=
        ⟨SupQuarter n ω, by rintro _ ⟨K, rfl⟩; exact hle_sup K⟩
      have hsup_eq : SupQuarter n ω = ⨆ K : ℕ, MQ' K ω := by
        apply le_antisymm
        · refine ciSup_le fun ⟨m, hmn⟩ ↦ ?_
          have hm_eq : n + (m - n) = m := Nat.add_sub_of_le hmn
          have h1 : Qk (m - n) ω ≤ MQ' (m - n) ω := by
            rw [← habs_k (m - n)]; exact abs_le_prefixMaxSeq (fun k ↦ Qk' k ω) le_rfl
          dsimp [Qk] at h1
          rw [hm_eq] at h1
          exact h1.trans (le_ciSup hBddMQ (m - n))
        · exact ciSup_le hle_sup
      rw [hsup_eq]
      exact tendsto_atTop_ciSup (fun a b hab ↦ prefixMaxSeq_mono _ hab) hBddMQ
    have hSupQ_aem : AEStronglyMeasurable (SupQuarter n) ℙ :=
      aestronglyMeasurable_of_tendsto_ae atTop (fun K ↦ (hMQ'_meas K).aestronglyMeasurable) hMQ'_lim
    exact ⟨hBddMean_all n, hae_bddQ_and_le.mono fun _ h ↦ h.1, hSupQ_aem,
      hae_bddQ_and_le.mono fun _ h ↦ h.2⟩
  -- Non-asymptotic Orlicz ψ₂ bound for `n ≥ exp 12`
  have hPsi2_12 : ∀ {n : ℕ}, Real.exp 12 ≤ (n : ℝ) →
      (S_supQ n).Nonempty ∧ BddBelow (S_supQ n) ∧
        sInf (S_supQ n) ≤
          4 * (Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) +
            SupMeanErr n / Real.sqrt (Real.log 2) := by
    intro n hn12
    obtain ⟨hn2, -, -, -, -⟩ := scale_a_bounds_v13 hn12 le_rfl
    obtain ⟨-, -, hSupQ_aem, hae_dom⟩ := hReg_ge2 hn2
    obtain ⟨-, hSupC_aem, hSC_ne, _, hSC_le⟩ :=
      coupling_orliczPsi2_sup_normalizedGap_center_le ℙ G hMarg hn12
    obtain ⟨hconst, hsubadd⟩ := orliczPsi2_const_and_add_le ℙ
    obtain ⟨hSm_ne, _, hSm_eq⟩ := hconst (SupMeanErr n)
    let X : Ω → ℝ := fun ω ↦ ⨆ m : {m : ℕ // n ≤ m}, |Y m.1 (G m.1 ω) - meanY m.1|
    let C : Ω → ℝ := fun _ ↦ SupMeanErr n
    have hSC_const_eq :
        {s : ℝ | 0 < s ∧ Integrable (fun ω ↦ Real.exp ((C ω) ^ 2 / s ^ 2)) ℙ ∧
          (∫ ω : Ω, Real.exp ((C ω) ^ 2 / s ^ 2) ∂ℙ) ≤ 2} =
        {s : ℝ | 0 < s ∧ (∫ _ : Ω, Real.exp ((SupMeanErr n) ^ 2 / s ^ 2) ∂ℙ) ≤ 2} := by
      ext s; simp only [Set.mem_setOf_eq, C, integrable_const, true_and]
    obtain ⟨hSXC_ne, _, hSXC_le⟩ :=
      hsubadd hSupC_aem aestronglyMeasurable_const hSC_ne (by rwa [hSC_const_eq])
    rw [hSC_const_eq, hSm_eq, abs_of_nonneg (Real.iSup_nonneg fun _ ↦ abs_nonneg _)] at hSXC_le
    -- Monotonicity from `SupQuarter n ≤ X + C` a.e.
    have hsub_set :
        {s : ℝ | 0 < s ∧ Integrable (fun ω ↦ Real.exp ((X ω + C ω) ^ 2 / s ^ 2)) ℙ ∧
          (∫ ω : Ω, Real.exp ((X ω + C ω) ^ 2 / s ^ 2) ∂ℙ) ≤ 2} ⊆ S_supQ n := by
      rintro s ⟨hs_pos, hInt_XC, hle2⟩
      have hc : Continuous (fun t : ℝ ↦ Real.exp (t ^ 2 / s ^ 2)) := by fun_prop
      have haesm_Q : AEStronglyMeasurable (fun ω ↦ Real.exp ((SupQuarter n ω) ^ 2 / s ^ 2)) ℙ :=
        hc.comp_aestronglyMeasurable hSupQ_aem
      have hpt_ae : ∀ᵐ ω ∂ℙ,
          Real.exp ((SupQuarter n ω) ^ 2 / s ^ 2) ≤ Real.exp ((X ω + C ω) ^ 2 / s ^ 2) := by
        filter_upwards [hae_dom] with ω hdom
        have hQ_nn : 0 ≤ SupQuarter n ω := Real.iSup_nonneg fun _ ↦ abs_nonneg _
        apply Real.exp_le_exp.mpr
        exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hQ_nn hdom 2) (sq_nonneg s)
      have hInt_Q : Integrable (fun ω ↦ Real.exp ((SupQuarter n ω) ^ 2 / s ^ 2)) ℙ := by
        refine hInt_XC.mono' haesm_Q (hpt_ae.mono fun ω h ↦ ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact h
      refine ⟨hs_pos, hInt_Q, (integral_mono_ae hInt_Q hInt_XC hpt_ae).trans hle2⟩
    have hSQ_ne : (S_supQ n).Nonempty := hSXC_ne.mono hsub_set
    have hSQ_bdd : BddBelow (S_supQ n) := ⟨0, fun s hs ↦ hs.1.le⟩
    have hSQ_le : sInf (S_supQ n) ≤
        sInf {s : ℝ | 0 < s ∧ Integrable (fun ω ↦ Real.exp ((X ω + C ω) ^ 2 / s ^ 2)) ℙ ∧
          (∫ ω : Ω, Real.exp ((X ω + C ω) ^ 2 / s ^ 2) ∂ℙ) ≤ 2} :=
      csInf_le_csInf hSQ_bdd hSXC_ne hsub_set
    exact ⟨hSQ_ne, hSQ_bdd, by linarith [hSQ_le, hSXC_le, hSC_le]⟩
  -- `sInf (S_supQ n) → 0`
  have hPsi2_tendsto : Tendsto (fun n : ℕ ↦ sInf (S_supQ n)) atTop (nhds 0) := by
    have hterm1 : Tendsto (fun n : ℕ ↦
        4 * (Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (Real.log (n : ℝ) / (n : ℝ))) atTop (nhds 0) := by
      have ho : (fun x : ℝ ↦ (Real.log x) ^ (7 / 2 : ℝ)) =o[atTop]
          (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) :=
        isLittleO_log_rpow_rpow_atTop (7 / 2 : ℝ) (by norm_num)
      have ht0 := (ho.comp_tendsto tendsto_natCast_atTop_atTop).tendsto_div_nhds_zero
      have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
      have ht1 := ht0.const_mul (4 / (Real.log 2) ^ 3)
      rw [mul_zero] at ht1
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht1
        (by filter_upwards [eventually_ge_atTop 2] with n hn2
            have hL_nn : 0 ≤ Real.log (n : ℝ) :=
              Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
            have hlb_nn : 0 ≤ Real.logb 2 (n : ℝ) := div_nonneg hL_nn hq_pos.le
            positivity)
        (by filter_upwards [eventually_ge_atTop 3] with n hn3
            have hL_gt1 : 1 < Real.log (n : ℝ) := by
              have he_lt3 : Real.exp 1 < (n : ℝ) :=
                lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286 : ℝ) < 3))
                  (show (3 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn3)
              simpa using Real.log_lt_log (Real.exp_pos 1) he_lt3
            have hL_pos : 0 < Real.log (n : ℝ) := lt_trans zero_lt_one hL_gt1
            rw [Real.logb, div_pow, Real.sqrt_div hL_pos.le,
              Real.sqrt_eq_rpow (Real.log (n : ℝ)), Real.sqrt_eq_rpow (n : ℝ),
              ← Real.rpow_natCast (Real.log (n : ℝ)) 3]
            have hadd_p : (Real.log (n : ℝ)) ^ ((3 : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) =
                (Real.log (n : ℝ)) ^ (7 / 2 : ℝ) := by
              rw [← Real.rpow_add hL_pos]; norm_num
            calc 4 * ((Real.log (n : ℝ)) ^ ((3 : ℕ) : ℝ) / (Real.log 2) ^ 3) *
                    ((Real.log (n : ℝ)) ^ (1 / 2 : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ))
                = (4 / (Real.log 2) ^ 3) *
                    (((Real.log (n : ℝ)) ^ ((3 : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ)) /
                      (n : ℝ) ^ (1 / 2 : ℝ)) := by ring
              _ = (4 / (Real.log 2) ^ 3) *
                    ((Real.log (n : ℝ)) ^ (7 / 2 : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ)) := by rw [hadd_p]
              _ ≤ _ := le_rfl)
    have hterm2 : Tendsto (fun n : ℕ ↦ SupMeanErr n / Real.sqrt (Real.log 2)) atTop (nhds 0) := by
      have hd := hSupMean_tendsto.div_const (Real.sqrt (Real.log 2))
      rwa [zero_div] at hd
    have hsum := hterm1.add hterm2
    rw [add_zero] at hsum
    have hev12 : ∀ᶠ n : ℕ in atTop, Real.exp 12 ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp 12)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (hev12.mono fun n hn ↦ le_csInf (hPsi2_12 hn).1 fun s hs ↦ hs.1.le)
      (hev12.mono fun n hn ↦ (hPsi2_12 hn).2.2)
  -- Prepare truncated measurable wrapper `Z_q n := if 2 ≤ n then SupQuarter n else 0`
  let Z_q : ℕ → Ω → ℝ := fun n ω ↦ if 2 ≤ n then SupQuarter n ω else 0
  have hZq_aem : ∀ n : ℕ, AEStronglyMeasurable (Z_q n) ℙ := by
    intro n
    dsimp [Z_q]
    split_ifs with hn2
    · exact (hReg_ge2 hn2).2.2.1
    · exact aestronglyMeasurable_const
  have hSZq_ev : ∀ᶠ n : ℕ in atTop,
      {s : ℝ | 0 < s ∧ Integrable (fun ω ↦ Real.exp ((Z_q n ω) ^ 2 / s ^ 2)) ℙ ∧
        (∫ ω, Real.exp ((Z_q n ω) ^ 2 / s ^ 2) ∂ℙ) ≤ 2} = S_supQ n := by
    filter_upwards [eventually_ge_atTop 2] with n hn2
    ext s; simp only [Z_q, if_pos hn2, S_supQ]
  have hNe_Zq : ∀ᶠ n : ℕ in atTop,
      ({s : ℝ | 0 < s ∧ Integrable (fun ω ↦ Real.exp ((Z_q n ω) ^ 2 / s ^ 2)) ℙ ∧
        (∫ ω, Real.exp ((Z_q n ω) ^ 2 / s ^ 2) ∂ℙ) ≤ 2}).Nonempty := by
    filter_upwards [hSZq_ev, tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp 12)]
      with n hEq hn12
    rw [hEq]; exact (hPsi2_12 hn12).1
  have hPsi2_Zq : Tendsto (fun n : ℕ ↦
      sInf {s : ℝ | 0 < s ∧ Integrable (fun ω ↦ Real.exp ((Z_q n ω) ^ 2 / s ^ 2)) ℙ ∧
        (∫ ω, Real.exp ((Z_q n ω) ^ 2 / s ^ 2) ∂ℙ) ≤ 2}) atTop (nhds 0) :=
    hPsi2_tendsto.congr' (hSZq_ev.mono fun n hEq ↦ congrArg sInf hEq.symm)
  refine ⟨fun hn2 ↦ ⟨(hReg_ge2 hn2).1, (hReg_ge2 hn2).2.1, (hReg_ge2 hn2).2.2.1⟩,
    hPsi2_12, hPsi2_tendsto, ?_, ?_⟩
  · intro M hM
    obtain ⟨hInt_ev, hLim⟩ := tendsto_sqExpMoment_one_of_orliczPsi2_tendsto_zero
      (Ω := fun _ ↦ Ω) (ℙ := fun _ ↦ ℙ) Z_q hZq_aem hNe_Zq hPsi2_Zq hM
    refine ⟨?_, ?_⟩
    · filter_upwards [eventually_ge_atTop 2, hInt_ev] with n hn2 hI
      simpa only [Z_q, if_pos hn2] using hI
    · refine hLim.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with n hn2
      simp only [Z_q, if_pos hn2]
  · intro p hp
    obtain ⟨hInt_ev, hLim⟩ := tendsto_lp_zero_of_orliczPsi2_tendsto_zero
      (Ω := fun _ ↦ Ω) (ℙ := fun _ ↦ ℙ) Z_q hZq_aem hNe_Zq hPsi2_Zq hp
    have hnn_all : ∀ n ω, 0 ≤ SupQuarter n ω := fun _ _ ↦ Real.iSup_nonneg fun _ ↦ abs_nonneg _
    refine ⟨?_, ?_⟩
    · filter_upwards [eventually_ge_atTop 2, hInt_ev] with n hn2 hI
      have heq : (fun ω : Ω ↦ |Z_q n ω| ^ p) = (fun ω : Ω ↦ (SupQuarter n ω) ^ p) := by
        funext ω; simp only [Z_q, if_pos hn2, abs_of_nonneg (hnn_all n ω)]
      rwa [heq] at hI
    · refine hLim.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with n hn2
      refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
      simp only [Z_q, if_pos hn2, abs_of_nonneg (hnn_all n ω)]

/-!
## 2. Section 3 finite-window tilts, optimizers, `(3.7)` slopes, and `(3.8)` objective differences
-/

private def wPart_v13 (W : Finset ℕ) (sc : ℕ → ℝ) (l : ℝ) : ℝ :=
  ∑ i ∈ W, Real.exp (l * (i : ℝ) + sc i)

private def wProb_v13 (W : Finset ℕ) (sc : ℕ → ℝ) (l : ℝ) (i : ℕ) : ℝ :=
  if i ∈ W then Real.exp (l * (i : ℝ) + sc i) / wPart_v13 W sc l else 0

private def wMean_v13 (W : Finset ℕ) (sc : ℕ → ℝ) (l : ℝ) : ℝ :=
  (∑ i ∈ W, (i : ℝ) * Real.exp (l * (i : ℝ) + sc i)) / wPart_v13 W sc l

private def wVar_v13 (W : Finset ℕ) (sc : ℕ → ℝ) (l : ℝ) : ℝ :=
  ∑ i ∈ W, ((i : ℝ) - wMean_v13 W sc l) ^ 2 * wProb_v13 W sc l i

private theorem wPart_v13_pos {W : Finset ℕ} (hW : W.Nonempty) (sc : ℕ → ℝ) (l : ℝ) :
    0 < wPart_v13 W sc l :=
  Finset.sum_pos (fun _ _ ↦ Real.exp_pos _) hW

private theorem sum_wProb_v13 {W : Finset ℕ} (hW : W.Nonempty) (sc : ℕ → ℝ) (l : ℝ) :
    ∑ i ∈ W, wProb_v13 W sc l i = 1 := by
  have hZ := wPart_v13_pos hW sc l
  calc ∑ i ∈ W, wProb_v13 W sc l i
      = ∑ i ∈ W, (Real.exp (l * (i : ℝ) + sc i) / wPart_v13 W sc l) :=
        Finset.sum_congr rfl fun i hi ↦ by simp [wProb_v13, hi]
    _ = (∑ i ∈ W, Real.exp (l * (i : ℝ) + sc i)) / wPart_v13 W sc l := (Finset.sum_div _ _ _).symm
    _ = 1 := div_self hZ.ne'

private theorem sum_mul_wProb_v13 (W : Finset ℕ) (sc : ℕ → ℝ) (l : ℝ) :
    ∑ i ∈ W, (i : ℝ) * wProb_v13 W sc l i = wMean_v13 W sc l := by
  unfold wMean_v13
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  simp only [wProb_v13, hi, ↓reduceIte, mul_div_assoc]

private theorem hasDerivAt_wMean_v13 {W : Finset ℕ} (hW : W.Nonempty) (sc : ℕ → ℝ) (l : ℝ) :
    HasDerivAt (wMean_v13 W sc) (wVar_v13 W sc l) l := by
  have hZ := wPart_v13_pos hW sc l
  have hterm : ∀ i : ℕ,
      HasDerivAt (fun x : ℝ ↦ Real.exp (x * (i : ℝ) + sc i))
        ((i : ℝ) * Real.exp (l * (i : ℝ) + sc i)) l := by
    intro i
    have hlin : HasDerivAt (fun x : ℝ ↦ x * (i : ℝ) + sc i) (i : ℝ) l := by
      simpa using ((hasDerivAt_id l).mul_const (i : ℝ)).add_const (sc i)
    exact (hlin.exp).congr_deriv (by ring)
  have hd_sum : ∀ (S : Finset ℕ) {g : ℕ → ℝ → ℝ} {g' : ℕ → ℝ},
      (∀ i ∈ S, HasDerivAt (g i) (g' i) l) →
      HasDerivAt (fun x ↦ ∑ i ∈ S, g i x) (∑ i ∈ S, g' i) l := by
    intro S g g' hg
    classical
    induction S using Finset.induction_on with
    | empty => simpa using hasDerivAt_const l (0 : ℝ)
    | @insert a s ha ih =>
      have hfn : (fun x ↦ ∑ i ∈ insert a s, g i x) = fun x ↦ g a x + ∑ i ∈ s, g i x := by
        funext x; exact Finset.sum_insert ha
      rw [hfn, Finset.sum_insert ha]
      exact (hg a (Finset.mem_insert_self a s)).add
        (ih fun i hi ↦ hg i (Finset.mem_insert_of_mem hi))
  have hd_num : HasDerivAt (fun x ↦ ∑ i ∈ W, (i : ℝ) * Real.exp (x * (i : ℝ) + sc i))
      (∑ i ∈ W, (i : ℝ) ^ 2 * Real.exp (l * (i : ℝ) + sc i)) l := by
    refine (hd_sum W fun i _ ↦ (hterm i).const_mul (i : ℝ)).congr_deriv ?_
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hd_den : HasDerivAt (wPart_v13 W sc)
      (∑ i ∈ W, (i : ℝ) * Real.exp (l * (i : ℝ) + sc i)) l :=
    hd_sum W fun i _ ↦ hterm i
  refine (hd_num.div hd_den hZ.ne').congr_deriv ?_
  set m_val : ℝ := wMean_v13 W sc l
  have hN1 : ∑ i ∈ W, (i : ℝ) * Real.exp (l * (i : ℝ) + sc i) = m_val * wPart_v13 W sc l := by
    dsimp [m_val]; unfold wMean_v13; exact (div_mul_cancel₀ _ hZ.ne').symm
  have hvar_eq :
      wVar_v13 W sc l * wPart_v13 W sc l =
        ∑ i ∈ W, ((i : ℝ) - m_val) ^ 2 * Real.exp (l * (i : ℝ) + sc i) := by
    unfold wVar_v13
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp only [wProb_v13, hi, ↓reduceIte, m_val]
    field_simp [hZ.ne']
  have hexp_sum :
      ∑ i ∈ W, ((i : ℝ) - m_val) ^ 2 * Real.exp (l * (i : ℝ) + sc i) =
        (∑ i ∈ W, (i : ℝ) ^ 2 * Real.exp (l * (i : ℝ) + sc i)) -
          2 * m_val * (∑ i ∈ W, (i : ℝ) * Real.exp (l * (i : ℝ) + sc i)) +
          m_val ^ 2 * wPart_v13 W sc l := by
    unfold wPart_v13
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [div_eq_iff (pow_pos hZ 2).ne']
  calc ((∑ i ∈ W, (i : ℝ) ^ 2 * Real.exp (l * (i : ℝ) + sc i)) * wPart_v13 W sc l -
          (∑ i ∈ W, (i : ℝ) * Real.exp (l * (i : ℝ) + sc i)) *
            (∑ i ∈ W, (i : ℝ) * Real.exp (l * (i : ℝ) + sc i)))
      = ((∑ i ∈ W, (i : ℝ) ^ 2 * Real.exp (l * (i : ℝ) + sc i)) -
          2 * m_val * (∑ i ∈ W, (i : ℝ) * Real.exp (l * (i : ℝ) + sc i)) +
          m_val ^ 2 * wPart_v13 W sc l) * wPart_v13 W sc l := by
        rw [hN1]; ring
    _ = (wVar_v13 W sc l * wPart_v13 W sc l) * wPart_v13 W sc l := by
        rw [← hexp_sum, hvar_eq]
    _ = wVar_v13 W sc l * wPart_v13 W sc l ^ 2 := by ring

private def wMasterBsc (M : ℕ) : ℝ :=
  ((1 + M : ℕ) : ℝ) ^ 2 + 1

private def wMasterLambda (M : ℕ) : ℝ :=
  wMasterBsc M + Real.log (8 * (M : ℝ) ^ 2 + 1) + 2

private def wMasterCstar (M : ℕ) : ℝ :=
  Real.exp (-2 * wMasterLambda M * ((1 + M : ℕ) : ℝ) - wMasterBsc M) / (2 * (M : ℝ))

private theorem windowGibbs_master_v13
    {m M : ℕ} (hm : m ≤ 1) (hM : 7 ≤ M) {sc : ℕ → ℝ}
    (hsc : ∀ i ∈ Finset.Icc (m + 1) (m + M),
      -(((1 + M : ℕ) : ℝ) ^ 2 + 1) ≤ sc i ∧ sc i ≤ 0) :
    let W := Finset.Icc (m + 1) (m + M)
    0 < wMasterLambda M ∧ 0 < wMasterCstar M ∧
      StrictMono (wMean_v13 W sc) ∧
      (∀ l ∈ Set.Icc (-(wMasterLambda M)) (wMasterLambda M),
        (∀ i ∈ W, 2 * wMasterCstar M ≤ wProb_v13 W sc l i) ∧ wMasterCstar M ≤ wVar_v13 W sc l) ∧
      (∀ T ∈ Set.Icc (9 / 4 : ℝ) (9 / 2),
        (∃! l : ℝ, wMean_v13 W sc l = T) ∧
        (∀ l : ℝ, wMean_v13 W sc l = T →
          l ∈ Set.Icc (-(wMasterLambda M)) (wMasterLambda M) ∧
          (⨅ μ : ℝ, (Real.log (wPart_v13 W sc μ) - μ * T)) =
            Real.log (wPart_v13 W sc l) - l * T ∧
          (⨅ μ : ℝ, (Real.log (wPart_v13 W sc μ) - μ * T)) =
            -(∑ i ∈ W, wProb_v13 W sc l i * Real.log (wProb_v13 W sc l i)) +
              ∑ i ∈ W, wProb_v13 W sc l i * sc i ∧
          ∀ q : ℕ → ℝ,
            (∀ i ∈ W, 0 ≤ q i) →
            ∑ i ∈ W, q i = 1 →
            ∑ i ∈ W, (i : ℝ) * q i = T →
            -(∑ i ∈ W, q i * Real.log (q i)) + ∑ i ∈ W, q i * sc i ≤
                (⨅ μ : ℝ, (Real.log (wPart_v13 W sc μ) - μ * T)) ∧
              (-(∑ i ∈ W, q i * Real.log (q i)) + ∑ i ∈ W, q i * sc i =
                  (⨅ μ : ℝ, (Real.log (wPart_v13 W sc μ) - μ * T)) ↔
                ∀ i ∈ W, q i = wProb_v13 W sc l i))) := by
  intro W
  unfold wMasterCstar wMasterLambda wMasterBsc
  set B_sc : ℝ := ((1 + M : ℕ) : ℝ) ^ 2 + 1
  set Λ_M : ℝ := B_sc + Real.log (8 * (M : ℝ) ^ 2 + 1) + 2
  set c_star : ℝ := Real.exp (-2 * Λ_M * ((1 + M : ℕ) : ℝ) - B_sc) / (2 * (M : ℝ))
  have hW_ne : W.Nonempty := ⟨m + 1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have hW_card : W.card = M := by dsimp [W]; rw [Nat.card_Icc]; omega
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hBsc_pos : 0 < B_sc := by dsimp [B_sc]; positivity
  have hlog8_pos : 0 < Real.log (8 * (M : ℝ) ^ 2 + 1) :=
    Real.log_pos (by nlinarith)
  have hΛ_pos : 0 < Λ_M := by dsimp [Λ_M]; positivity
  have hc_pos : 0 < c_star := by dsimp [c_star]; positivity
  have hm1_mem : m + 1 ∈ W := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hm2_mem : m + 2 ∈ W := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hmM_mem : m + M ∈ W := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  -- Variance > 0 everywhere on ℝ, hence `StrictMono`
  have hvar_pos : ∀ l : ℝ, 0 < wVar_v13 W sc l := by
    intro l
    have hZ := wPart_v13_pos hW_ne sc l
    set μ := wMean_v13 W sc l
    have hp1 : 0 < wProb_v13 W sc l (m + 1) := by
      simp only [wProb_v13, hm1_mem, ↓reduceIte]; exact div_pos (Real.exp_pos _) hZ
    have hp2 : 0 < wProb_v13 W sc l (m + 2) := by
      simp only [wProb_v13, hm2_mem, ↓reduceIte]; exact div_pos (Real.exp_pos _) hZ
    have h12_sub : ({m + 1, m + 2} : Finset ℕ) ⊆ W := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hpair :
        (((m + 1 : ℕ) : ℝ) - μ) ^ 2 * wProb_v13 W sc l (m + 1) +
            (((m + 2 : ℕ) : ℝ) - μ) ^ 2 * wProb_v13 W sc l (m + 2) ≤
          wVar_v13 W sc l := by
      unfold wVar_v13
      have hpair_eq := Finset.sum_pair
        (f := fun i : ℕ ↦ ((i : ℝ) - wMean_v13 W sc l) ^ 2 * wProb_v13 W sc l i)
        (by omega : m + 1 ≠ m + 2)
      dsimp only [μ]
      rw [← hpair_eq]
      exact Finset.sum_le_sum_of_subset_of_nonneg h12_sub fun i hi _ ↦ by
        simp only [wProb_v13, hi, ↓reduceIte]
        exact mul_nonneg (sq_nonneg _) (div_nonneg (Real.exp_pos _).le hZ.le)
    have hsum_sq : (1 / 2 : ℝ) ≤ (((m + 1 : ℕ) : ℝ) - μ) ^ 2 + (((m + 2 : ℕ) : ℝ) - μ) ^ 2 := by
      have hid : (((m + 1 : ℕ) : ℝ) - μ) ^ 2 + (((m + 2 : ℕ) : ℝ) - μ) ^ 2 =
          2 * (μ - ((m + 1 : ℕ) : ℝ) - 1 / 2) ^ 2 + 1 / 2 := by push_cast; ring
      rw [hid]; linarith [sq_nonneg (μ - ((m + 1 : ℕ) : ℝ) - 1 / 2)]
    have hmin_pos : 0 < min (wProb_v13 W sc l (m + 1)) (wProb_v13 W sc l (m + 2)) :=
      lt_min hp1 hp2
    have hlo :
        (1 / 2 : ℝ) * min (wProb_v13 W sc l (m + 1)) (wProb_v13 W sc l (m + 2)) ≤
          (((m + 1 : ℕ) : ℝ) - μ) ^ 2 * wProb_v13 W sc l (m + 1) +
            (((m + 2 : ℕ) : ℝ) - μ) ^ 2 * wProb_v13 W sc l (m + 2) := by
      calc (1 / 2 : ℝ) * min (wProb_v13 W sc l (m + 1)) (wProb_v13 W sc l (m + 2))
          ≤ ((((m + 1 : ℕ) : ℝ) - μ) ^ 2 + (((m + 2 : ℕ) : ℝ) - μ) ^ 2) *
              min (wProb_v13 W sc l (m + 1)) (wProb_v13 W sc l (m + 2)) :=
            mul_le_mul_of_nonneg_right hsum_sq hmin_pos.le
        _ ≤ (((m + 1 : ℕ) : ℝ) - μ) ^ 2 * wProb_v13 W sc l (m + 1) +
              (((m + 2 : ℕ) : ℝ) - μ) ^ 2 * wProb_v13 W sc l (m + 2) := by
            rw [add_mul]
            exact add_le_add
              (mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg _))
              (mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg _))
    exact lt_of_lt_of_le (by positivity) (hlo.trans hpair)
  have hStrict : StrictMono (wMean_v13 W sc) := by
    apply strictMono_of_deriv_pos
    intro l
    rw [(hasDerivAt_wMean_v13 hW_ne sc l).deriv]
    exact hvar_pos l
  -- Lower bounds on `wProb` and `wVar` across `[-Λ_M, Λ_M]`
  have hBox : ∀ l ∈ Set.Icc (-Λ_M) Λ_M,
      (∀ i ∈ W, 2 * c_star ≤ wProb_v13 W sc l i) ∧ c_star ≤ wVar_v13 W sc l := by
    intro l hl
    have hl_abs : |l| ≤ Λ_M := abs_le.mpr hl
    have hZ_hi : wPart_v13 W sc l ≤ (M : ℝ) * Real.exp (Λ_M * ((1 + M : ℕ) : ℝ)) := by
      calc wPart_v13 W sc l
          ≤ ∑ _i ∈ W, Real.exp (Λ_M * ((1 + M : ℕ) : ℝ)) := by
            refine Finset.sum_le_sum fun i hi ↦ Real.exp_le_exp.mpr ?_
            have hi_le : (i : ℝ) ≤ ((1 + M : ℕ) : ℝ) := by
              exact_mod_cast (le_trans (Finset.mem_Icc.mp hi).2 (by omega : m + M ≤ 1 + M))
            have hli : l * (i : ℝ) ≤ Λ_M * ((1 + M : ℕ) : ℝ) := by
              calc l * (i : ℝ) ≤ |l| * (i : ℝ) :=
                    mul_le_mul_of_nonneg_right (le_abs_self l) (Nat.cast_nonneg i)
                _ ≤ Λ_M * ((1 + M : ℕ) : ℝ) :=
                    mul_le_mul hl_abs hi_le (Nat.cast_nonneg i) hΛ_pos.le
            linarith [(hsc i hi).2]
        _ = (M : ℝ) * Real.exp (Λ_M * ((1 + M : ℕ) : ℝ)) := by
            rw [Finset.sum_const, hW_card, nsmul_eq_mul]
    have hp_lo : ∀ i ∈ W, 2 * c_star ≤ wProb_v13 W sc l i := by
      intro i hi
      simp only [wProb_v13, hi, ↓reduceIte]
      have hi_le : (i : ℝ) ≤ ((1 + M : ℕ) : ℝ) := by
        exact_mod_cast (le_trans (Finset.mem_Icc.mp hi).2 (by omega : m + M ≤ 1 + M))
      have hli : -Λ_M * ((1 + M : ℕ) : ℝ) ≤ l * (i : ℝ) := by
        have h1 : |l * (i : ℝ)| ≤ Λ_M * ((1 + M : ℕ) : ℝ) := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg i : (0 : ℝ) ≤ (i : ℝ))]
          exact mul_le_mul hl_abs hi_le (Nat.cast_nonneg i) hΛ_pos.le
        linarith [(abs_le.mp h1).1]
      have hnum_lo : Real.exp (-Λ_M * ((1 + M : ℕ) : ℝ) - B_sc) ≤ Real.exp (l * (i : ℝ) + sc i) :=
        Real.exp_le_exp.mpr (by linarith [(hsc i hi).1])
      calc 2 * c_star
          = Real.exp (-Λ_M * ((1 + M : ℕ) : ℝ) - B_sc) /
              ((M : ℝ) * Real.exp (Λ_M * ((1 + M : ℕ) : ℝ))) := by
            dsimp [c_star]
            have h1 : -2 * Λ_M * ((1 + M : ℕ) : ℝ) - B_sc =
                (-Λ_M * ((1 + M : ℕ) : ℝ) - B_sc) - Λ_M * ((1 + M : ℕ) : ℝ) := by ring
            rw [h1, Real.exp_sub]
            field_simp [hM_pos.ne', (Real.exp_pos _).ne']
        _ ≤ Real.exp (l * (i : ℝ) + sc i) / wPart_v13 W sc l :=
            div_le_div₀ (Real.exp_pos _).le hnum_lo (wPart_v13_pos hW_ne sc l) hZ_hi
    refine ⟨hp_lo, ?_⟩
    set μ := wMean_v13 W sc l
    have h12_sub : ({m + 1, m + 2} : Finset ℕ) ⊆ W := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hpair :
        (((m + 1 : ℕ) : ℝ) - μ) ^ 2 * wProb_v13 W sc l (m + 1) +
            (((m + 2 : ℕ) : ℝ) - μ) ^ 2 * wProb_v13 W sc l (m + 2) ≤
          wVar_v13 W sc l := by
      unfold wVar_v13
      have hZ := wPart_v13_pos hW_ne sc l
      have hpair_eq := Finset.sum_pair
        (f := fun i : ℕ ↦ ((i : ℝ) - wMean_v13 W sc l) ^ 2 * wProb_v13 W sc l i)
        (by omega : m + 1 ≠ m + 2)
      dsimp only [μ]
      rw [← hpair_eq]
      exact Finset.sum_le_sum_of_subset_of_nonneg h12_sub fun i hi _ ↦ by
        simp only [wProb_v13, hi, ↓reduceIte]
        exact mul_nonneg (sq_nonneg _) (div_nonneg (Real.exp_pos _).le hZ.le)
    have hsum_sq : (1 / 2 : ℝ) ≤ (((m + 1 : ℕ) : ℝ) - μ) ^ 2 + (((m + 2 : ℕ) : ℝ) - μ) ^ 2 := by
      have hid : (((m + 1 : ℕ) : ℝ) - μ) ^ 2 + (((m + 2 : ℕ) : ℝ) - μ) ^ 2 =
          2 * (μ - ((m + 1 : ℕ) : ℝ) - 1 / 2) ^ 2 + 1 / 2 := by push_cast; ring
      rw [hid]; linarith [sq_nonneg (μ - ((m + 1 : ℕ) : ℝ) - 1 / 2)]
    have hm1_lo := hp_lo (m + 1) hm1_mem
    have hm2_lo := hp_lo (m + 2) hm2_mem
    calc c_star
        = (1 / 2 : ℝ) * (2 * c_star) := by ring
      _ ≤ ((((m + 1 : ℕ) : ℝ) - μ) ^ 2 + (((m + 2 : ℕ) : ℝ) - μ) ^ 2) * (2 * c_star) :=
          mul_le_mul_of_nonneg_right hsum_sq (by positivity)
      _ ≤ (((m + 1 : ℕ) : ℝ) - μ) ^ 2 * wProb_v13 W sc l (m + 1) +
            (((m + 2 : ℕ) : ℝ) - μ) ^ 2 * wProb_v13 W sc l (m + 2) := by
          rw [add_mul]
          exact add_le_add
            (mul_le_mul_of_nonneg_left hm1_lo (sq_nonneg _))
            (mul_le_mul_of_nonneg_left hm2_lo (sq_nonneg _))
      _ ≤ wVar_v13 W sc l := hpair
  -- Endpoint bounds: `wMean(-Λ_M) < 9/4` and `9/2 < wMean(Λ_M)`
  have hLeft_lt : wMean_v13 W sc (-Λ_M) < 9 / 4 := by
    have hZ := wPart_v13_pos hW_ne sc (-Λ_M)
    have hdiff :
        wMean_v13 W sc (-Λ_M) - ((m + 1 : ℕ) : ℝ) =
          (∑ i ∈ W, ((i : ℝ) - ((m + 1 : ℕ) : ℝ)) * Real.exp ((-Λ_M) * (i : ℝ) + sc i)) /
            wPart_v13 W sc (-Λ_M) := by
      have hmul :
          (wMean_v13 W sc (-Λ_M) - ((m + 1 : ℕ) : ℝ)) * wPart_v13 W sc (-Λ_M) =
            ∑ i ∈ W, ((i : ℝ) - ((m + 1 : ℕ) : ℝ)) * Real.exp ((-Λ_M) * (i : ℝ) + sc i) := by
        rw [sub_mul]
        unfold wMean_v13
        rw [div_mul_cancel₀ _ hZ.ne']
        unfold wPart_v13
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      exact (eq_div_iff hZ.ne').mpr hmul
    have hw_m1 : Real.exp ((-Λ_M) * ((m + 1 : ℕ) : ℝ) - B_sc) ≤ wPart_v13 W sc (-Λ_M) := by
      calc Real.exp ((-Λ_M) * ((m + 1 : ℕ) : ℝ) - B_sc)
          ≤ Real.exp ((-Λ_M) * ((m + 1 : ℕ) : ℝ) + sc (m + 1)) :=
            Real.exp_le_exp.mpr (by linarith [(hsc (m + 1) hm1_mem).1])
        _ ≤ wPart_v13 W sc (-Λ_M) :=
            Finset.single_le_sum (f := fun i : ℕ ↦ Real.exp ((-Λ_M) * (i : ℝ) + sc i))
              (fun _ _ ↦ (Real.exp_pos _).le) hm1_mem
    have hnum_le :
        (∑ i ∈ W, ((i : ℝ) - ((m + 1 : ℕ) : ℝ)) * Real.exp ((-Λ_M) * (i : ℝ) + sc i)) ≤
          (M : ℝ) ^ 2 * Real.exp ((-Λ_M) * ((m + 1 : ℕ) : ℝ) - Λ_M) := by
      calc (∑ i ∈ W, ((i : ℝ) - ((m + 1 : ℕ) : ℝ)) * Real.exp ((-Λ_M) * (i : ℝ) + sc i))
          ≤ ∑ _i ∈ W, (M : ℝ) * Real.exp ((-Λ_M) * ((m + 1 : ℕ) : ℝ) - Λ_M) := by
            refine Finset.sum_le_sum fun i hi ↦ ?_
            obtain ⟨hi_lo, hi_hi⟩ := Finset.mem_Icc.mp hi
            by_cases heq : i = m + 1
            · subst heq; simp; positivity
            · have hi_ge : ((m + 1 : ℕ) : ℝ) + 1 ≤ (i : ℝ) := by
                exact_mod_cast (show m + 1 + 1 ≤ i by omega)
              have hi_diff : (i : ℝ) - ((m + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by
                have : (i : ℝ) ≤ ((m + M : ℕ) : ℝ) := by exact_mod_cast hi_hi
                push_cast at this ⊢; linarith
              have hexp_i : Real.exp ((-Λ_M) * (i : ℝ) + sc i) ≤
                  Real.exp ((-Λ_M) * ((m + 1 : ℕ) : ℝ) - Λ_M) := by
                apply Real.exp_le_exp.mpr
                have hm_l := mul_le_mul_of_nonneg_left hi_ge hΛ_pos.le
                linarith [(hsc i hi).2]
              exact mul_le_mul hi_diff hexp_i (Real.exp_pos _).le (by positivity)
        _ = (M : ℝ) ^ 2 * Real.exp ((-Λ_M) * ((m + 1 : ℕ) : ℝ) - Λ_M) := by
            rw [Finset.sum_const, hW_card, nsmul_eq_mul]; ring
    have hquot_lt :
        (wMean_v13 W sc (-Λ_M) - ((m + 1 : ℕ) : ℝ)) < 1 / 8 := by
      rw [hdiff]
      have hle1 :
          (∑ i ∈ W, ((i : ℝ) - ((m + 1 : ℕ) : ℝ)) * Real.exp ((-Λ_M) * (i : ℝ) + sc i)) /
              wPart_v13 W sc (-Λ_M) ≤
            (M : ℝ) ^ 2 * Real.exp (-Λ_M + B_sc) := by
        have hnn_num : 0 ≤ ∑ i ∈ W, ((i : ℝ) - ((m + 1 : ℕ) : ℝ)) * Real.exp ((-Λ_M) * (i : ℝ) + sc i) :=
          Finset.sum_nonneg fun i hi ↦ mul_nonneg
            (sub_nonneg.mpr (by exact_mod_cast (Finset.mem_Icc.mp hi).1)) (Real.exp_pos _).le
        calc _ ≤ ((M : ℝ) ^ 2 * Real.exp ((-Λ_M) * ((m + 1 : ℕ) : ℝ) - Λ_M)) /
                Real.exp ((-Λ_M) * ((m + 1 : ℕ) : ℝ) - B_sc) :=
              div_le_div₀ (by positivity) hnum_le (Real.exp_pos _) hw_m1
          _ = (M : ℝ) ^ 2 * Real.exp (-Λ_M + B_sc) := by
              rw [mul_div_assoc, ← Real.exp_sub]; congr 2; ring
      refine lt_of_le_of_lt hle1 ?_
      have hexp_lt : Real.exp (-Λ_M + B_sc) < 1 / (8 * (M : ℝ) ^ 2 + 1) := by
        have hlt : -Λ_M + B_sc < -Real.log (8 * (M : ℝ) ^ 2 + 1) := by dsimp [Λ_M]; linarith
        calc Real.exp (-Λ_M + B_sc)
            < Real.exp (-Real.log (8 * (M : ℝ) ^ 2 + 1)) := Real.exp_lt_exp.mpr hlt
          _ = 1 / (8 * (M : ℝ) ^ 2 + 1) := by
              rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
      calc (M : ℝ) ^ 2 * Real.exp (-Λ_M + B_sc)
          < (M : ℝ) ^ 2 * (1 / (8 * (M : ℝ) ^ 2 + 1)) :=
            mul_lt_mul_of_pos_left hexp_lt (sq_pos_of_pos hM_pos)
        _ < 1 / 8 := by
            rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
            linarith
    have hm1_le2 : ((m + 1 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show m + 1 ≤ 2 by omega)
    linarith
  have hRight_gt : 9 / 2 < wMean_v13 W sc Λ_M := by
    have hZ := wPart_v13_pos hW_ne sc Λ_M
    have hdiff :
        ((m + M : ℕ) : ℝ) - wMean_v13 W sc Λ_M =
          (∑ i ∈ W, (((m + M : ℕ) : ℝ) - (i : ℝ)) * Real.exp (Λ_M * (i : ℝ) + sc i)) /
            wPart_v13 W sc Λ_M := by
      have hmul :
          (((m + M : ℕ) : ℝ) - wMean_v13 W sc Λ_M) * wPart_v13 W sc Λ_M =
            ∑ i ∈ W, (((m + M : ℕ) : ℝ) - (i : ℝ)) * Real.exp (Λ_M * (i : ℝ) + sc i) := by
        rw [sub_mul]
        unfold wMean_v13
        rw [div_mul_cancel₀ _ hZ.ne']
        unfold wPart_v13
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      exact (eq_div_iff hZ.ne').mpr hmul
    have hw_mM : Real.exp (Λ_M * ((m + M : ℕ) : ℝ) - B_sc) ≤ wPart_v13 W sc Λ_M := by
      calc Real.exp (Λ_M * ((m + M : ℕ) : ℝ) - B_sc)
          ≤ Real.exp (Λ_M * ((m + M : ℕ) : ℝ) + sc (m + M)) :=
            Real.exp_le_exp.mpr (by linarith [(hsc (m + M) hmM_mem).1])
        _ ≤ wPart_v13 W sc Λ_M :=
            Finset.single_le_sum (f := fun i : ℕ ↦ Real.exp (Λ_M * (i : ℝ) + sc i))
              (fun _ _ ↦ (Real.exp_pos _).le) hmM_mem
    have hnum_le :
        (∑ i ∈ W, (((m + M : ℕ) : ℝ) - (i : ℝ)) * Real.exp (Λ_M * (i : ℝ) + sc i)) ≤
          (M : ℝ) ^ 2 * Real.exp (Λ_M * ((m + M : ℕ) : ℝ) - Λ_M) := by
      calc (∑ i ∈ W, (((m + M : ℕ) : ℝ) - (i : ℝ)) * Real.exp (Λ_M * (i : ℝ) + sc i))
          ≤ ∑ _i ∈ W, (M : ℝ) * Real.exp (Λ_M * ((m + M : ℕ) : ℝ) - Λ_M) := by
            refine Finset.sum_le_sum fun i hi ↦ ?_
            obtain ⟨hi_lo, hi_hi⟩ := Finset.mem_Icc.mp hi
            by_cases heq : i = m + M
            · subst heq; simp; positivity
            · have hi_le : (i : ℝ) + 1 ≤ ((m + M : ℕ) : ℝ) := by
                exact_mod_cast (show i + 1 ≤ m + M by omega)
              have hi_diff : ((m + M : ℕ) : ℝ) - (i : ℝ) ≤ (M : ℝ) := by
                have : ((m + 1 : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi_lo
                push_cast at this ⊢; linarith
              have hexp_i : Real.exp (Λ_M * (i : ℝ) + sc i) ≤
                  Real.exp (Λ_M * ((m + M : ℕ) : ℝ) - Λ_M) := by
                apply Real.exp_le_exp.mpr
                have hm_l := mul_le_mul_of_nonneg_left hi_le hΛ_pos.le
                linarith [(hsc i hi).2]
              exact mul_le_mul hi_diff hexp_i (Real.exp_pos _).le (by positivity)
        _ = (M : ℝ) ^ 2 * Real.exp (Λ_M * ((m + M : ℕ) : ℝ) - Λ_M) := by
            rw [Finset.sum_const, hW_card, nsmul_eq_mul]; ring
    have hquot_lt : (((m + M : ℕ) : ℝ) - wMean_v13 W sc Λ_M) < 1 / 8 := by
      rw [hdiff]
      have hle1 :
          (∑ i ∈ W, (((m + M : ℕ) : ℝ) - (i : ℝ)) * Real.exp (Λ_M * (i : ℝ) + sc i)) /
              wPart_v13 W sc Λ_M ≤
            (M : ℝ) ^ 2 * Real.exp (-Λ_M + B_sc) := by
        calc _ ≤ ((M : ℝ) ^ 2 * Real.exp (Λ_M * ((m + M : ℕ) : ℝ) - Λ_M)) /
                Real.exp (Λ_M * ((m + M : ℕ) : ℝ) - B_sc) :=
              div_le_div₀ (by positivity) hnum_le (Real.exp_pos _) hw_mM
          _ = (M : ℝ) ^ 2 * Real.exp (-Λ_M + B_sc) := by
              rw [mul_div_assoc, ← Real.exp_sub]; congr 2; ring
      refine lt_of_le_of_lt hle1 ?_
      have hexp_lt : Real.exp (-Λ_M + B_sc) < 1 / (8 * (M : ℝ) ^ 2 + 1) := by
        have hlt : -Λ_M + B_sc < -Real.log (8 * (M : ℝ) ^ 2 + 1) := by dsimp [Λ_M]; linarith
        calc Real.exp (-Λ_M + B_sc)
            < Real.exp (-Real.log (8 * (M : ℝ) ^ 2 + 1)) := Real.exp_lt_exp.mpr hlt
          _ = 1 / (8 * (M : ℝ) ^ 2 + 1) := by
              rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
      calc (M : ℝ) ^ 2 * Real.exp (-Λ_M + B_sc)
          < (M : ℝ) ^ 2 * (1 / (8 * (M : ℝ) ^ 2 + 1)) :=
            mul_lt_mul_of_pos_left hexp_lt (sq_pos_of_pos hM_pos)
        _ < 1 / 8 := by
            rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
            linarith
    have hmM_ge7 : (7 : ℝ) ≤ ((m + M : ℕ) : ℝ) := by exact_mod_cast (show 7 ≤ m + M by omega)
    linarith
  refine ⟨hΛ_pos, hc_pos, hStrict, hBox, ?_⟩
  intro T hT
  have hCont : Continuous (wMean_v13 W sc) :=
    continuous_iff_continuousAt.mpr fun l ↦ (hasDerivAt_wMean_v13 hW_ne sc l).continuousAt
  obtain ⟨l₀, hl₀_icc, hl₀_eq⟩ := intermediate_value_Icc (by linarith : -Λ_M ≤ Λ_M)
    hCont.continuousOn ⟨hLeft_lt.le.trans hT.1, hT.2.trans hRight_gt.le⟩
  have hexu : ∃! l : ℝ, wMean_v13 W sc l = T :=
    ⟨l₀, hl₀_eq, fun l hl ↦ hStrict.injective (hl.trans hl₀_eq.symm)⟩
  refine ⟨hexu, ?_⟩
  intro l hl_eq
  have hl_eq_l₀ : l = l₀ := hStrict.injective (hl_eq.trans hl₀_eq.symm)
  subst hl_eq_l₀
  -- Prove dual attainment & KL identity at `l`
  have hZ_l := wPart_v13_pos hW_ne sc l
  have hdual_le_all : ∀ μ : ℝ,
      Real.log (wPart_v13 W sc l) - l * T ≤ Real.log (wPart_v13 W sc μ) - μ * T := by
    intro μ
    have hZ_μ := wPart_v13_pos hW_ne sc μ
    have hkl_i : ∀ i ∈ W,
        wProb_v13 W sc l i *
            ((μ - l) * (i : ℝ) - Real.log (wPart_v13 W sc μ) + Real.log (wPart_v13 W sc l)) ≤
          wProb_v13 W sc μ i - wProb_v13 W sc l i := by
      intro i hi
      have hp_pos : 0 < wProb_v13 W sc l i := by
        simp only [wProb_v13, hi, ↓reduceIte]; exact div_pos (Real.exp_pos _) hZ_l
      have hq_pos : 0 < wProb_v13 W sc μ i := by
        simp only [wProb_v13, hi, ↓reduceIte]; exact div_pos (Real.exp_pos _) hZ_μ
      have hlog := Real.log_le_sub_one_of_pos (div_pos hq_pos hp_pos)
      have hm := mul_le_mul_of_nonneg_left hlog hp_pos.le
      have hrhs : wProb_v13 W sc l i * (wProb_v13 W sc μ i / wProb_v13 W sc l i - 1) =
          wProb_v13 W sc μ i - wProb_v13 W sc l i := by
        field_simp [hp_pos.ne']
      have hlhs : Real.log (wProb_v13 W sc μ i / wProb_v13 W sc l i) =
          (μ - l) * (i : ℝ) - Real.log (wPart_v13 W sc μ) + Real.log (wPart_v13 W sc l) := by
        simp only [wProb_v13, hi, ↓reduceIte]
        rw [Real.log_div (div_pos (Real.exp_pos _) hZ_μ).ne' (div_pos (Real.exp_pos _) hZ_l).ne',
          Real.log_div (Real.exp_pos _).ne' hZ_μ.ne',
          Real.log_div (Real.exp_pos _).ne' hZ_l.ne',
          Real.log_exp, Real.log_exp]
        ring
      rwa [hlhs, hrhs] at hm
    have hsum := Finset.sum_le_sum hkl_i
    have hrhs_zero : ∑ i ∈ W, (wProb_v13 W sc μ i - wProb_v13 W sc l i) = 0 := by
      rw [Finset.sum_sub_distrib, sum_wProb_v13 hW_ne, sum_wProb_v13 hW_ne, sub_self]
    have hlhs_eval :
        ∑ i ∈ W, wProb_v13 W sc l i *
            ((μ - l) * (i : ℝ) - Real.log (wPart_v13 W sc μ) + Real.log (wPart_v13 W sc l)) =
          (μ - l) * T - Real.log (wPart_v13 W sc μ) + Real.log (wPart_v13 W sc l) := by
      have h1 : ∀ i ∈ W,
          wProb_v13 W sc l i *
              ((μ - l) * (i : ℝ) - Real.log (wPart_v13 W sc μ) + Real.log (wPart_v13 W sc l)) =
            (μ - l) * ((i : ℝ) * wProb_v13 W sc l i) +
              (-Real.log (wPart_v13 W sc μ) + Real.log (wPart_v13 W sc l)) * wProb_v13 W sc l i :=
        fun _ _ ↦ by ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        sum_mul_wProb_v13, hl_eq, sum_wProb_v13 hW_ne]
      ring
    linarith
  have hbdd_inf : BddBelow (Set.range fun μ : ℝ ↦ Real.log (wPart_v13 W sc μ) - μ * T) :=
    ⟨Real.log (wPart_v13 W sc l) - l * T, by rintro _ ⟨μ, rfl⟩; exact hdual_le_all μ⟩
  have hinf_eq :
      (⨅ μ : ℝ, (Real.log (wPart_v13 W sc μ) - μ * T)) = Real.log (wPart_v13 W sc l) - l * T :=
    le_antisymm (ciInf_le hbdd_inf l) (le_ciInf hdual_le_all)
  have hent_eq :
      -(∑ i ∈ W, wProb_v13 W sc l i * Real.log (wProb_v13 W sc l i)) +
          ∑ i ∈ W, wProb_v13 W sc l i * sc i =
        Real.log (wPart_v13 W sc l) - l * T := by
    have hpt : ∀ i ∈ W,
        -(wProb_v13 W sc l i * Real.log (wProb_v13 W sc l i)) + wProb_v13 W sc l i * sc i =
          Real.log (wPart_v13 W sc l) * wProb_v13 W sc l i -
            l * ((i : ℝ) * wProb_v13 W sc l i) := by
      intro i hi
      have hp_def : wProb_v13 W sc l i = Real.exp (l * (i : ℝ) + sc i) / wPart_v13 W sc l := by
        simp [wProb_v13, hi]
      rw [hp_def, Real.log_div (Real.exp_pos _).ne' hZ_l.ne', Real.log_exp]
      ring
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Finset.sum_congr rfl hpt,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_wProb_v13 hW_ne, sum_mul_wProb_v13, hl_eq, mul_one]
  refine ⟨hl₀_icc, hinf_eq, hinf_eq.trans hent_eq.symm, ?_⟩
  intro q hq_nn hq_sum hq_mean
  -- KL divergence of `q` relative to `p := wProb_v13 W sc l`
  have hterm_kl : ∀ i ∈ W,
      -(q i * Real.log (q i)) + q i * sc i -
          (Real.log (wPart_v13 W sc l) * q i - l * ((i : ℝ) * q i)) ≤
        wProb_v13 W sc l i - q i := by
    intro i hi
    have hp_pos : 0 < wProb_v13 W sc l i := by
      simp only [wProb_v13, hi, ↓reduceIte]; exact div_pos (Real.exp_pos _) hZ_l
    have hp_log : Real.log (wProb_v13 W sc l i) =
        l * (i : ℝ) + sc i - Real.log (wPart_v13 W sc l) := by
      simp only [wProb_v13, hi, ↓reduceIte]
      rw [Real.log_div (Real.exp_pos _).ne' hZ_l.ne', Real.log_exp]
    rcases eq_or_lt_of_le (hq_nn i hi) with hq0 | hq_pos
    · rw [← hq0]; simp; exact hp_pos.le
    · have hlog := Real.log_le_sub_one_of_pos (div_pos hp_pos hq_pos)
      have hm := mul_le_mul_of_nonneg_left hlog hq_pos.le
      have hrhs : q i * (wProb_v13 W sc l i / q i - 1) = wProb_v13 W sc l i - q i := by
        field_simp [hq_pos.ne']
      rw [Real.log_div hp_pos.ne' hq_pos.ne', hp_log, hrhs] at hm
      linarith
  have hsum_kl := Finset.sum_le_sum hterm_kl
  have hrhs_z : ∑ i ∈ W, (wProb_v13 W sc l i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, sum_wProb_v13 hW_ne, hq_sum, sub_self]
  have hlhs_q :
      ∑ i ∈ W,
          (-(q i * Real.log (q i)) + q i * sc i -
            (Real.log (wPart_v13 W sc l) * q i - l * ((i : ℝ) * q i))) =
        (-(∑ i ∈ W, q i * Real.log (q i)) + ∑ i ∈ W, q i * sc i) -
          (Real.log (wPart_v13 W sc l) - l * T) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hq_sum, hq_mean, mul_one]
  have hle_opt :
      -(∑ i ∈ W, q i * Real.log (q i)) + ∑ i ∈ W, q i * sc i ≤
        ⨅ μ : ℝ, (Real.log (wPart_v13 W sc μ) - μ * T) := by
    rw [hinf_eq]; linarith
  refine ⟨hle_opt, ?_⟩
  constructor
  · intro heq_opt i hi
    rw [hinf_eq] at heq_opt
    have hsum_eq0 :
        ∑ j ∈ W,
            ((wProb_v13 W sc l j - q j) -
              (-(q j * Real.log (q j)) + q j * sc j -
                (Real.log (wPart_v13 W sc l) * q j - l * ((j : ℝ) * q j)))) = 0 := by
      rw [Finset.sum_sub_distrib, hrhs_z, hlhs_q]; linarith
    have hnn_term : ∀ j ∈ W,
        0 ≤ (wProb_v13 W sc l j - q j) -
            (-(q j * Real.log (q j)) + q j * sc j -
              (Real.log (wPart_v13 W sc l) * q j - l * ((j : ℝ) * q j))) :=
      fun j hj ↦ sub_nonneg.mpr (hterm_kl j hj)
    have hi_zero := (Finset.sum_eq_zero_iff_of_nonneg hnn_term).mp hsum_eq0 i hi
    have hp_pos : 0 < wProb_v13 W sc l i := by
      simp only [wProb_v13, hi, ↓reduceIte]; exact div_pos (Real.exp_pos _) hZ_l
    have hp_log : Real.log (wProb_v13 W sc l i) =
        l * (i : ℝ) + sc i - Real.log (wPart_v13 W sc l) := by
      simp only [wProb_v13, hi, ↓reduceIte]
      rw [Real.log_div (Real.exp_pos _).ne' hZ_l.ne', Real.log_exp]
    rcases eq_or_lt_of_le (hq_nn i hi) with hq0 | hq_pos
    · rw [← hq0] at hi_zero; simp at hi_zero; linarith
    · by_contra hne
      have hdiv_ne : wProb_v13 W sc l i / q i ≠ 1 :=
        fun hd ↦ hne ((div_eq_one_iff_eq hq_pos.ne').mp hd).symm
      have hlog_lt := Real.log_lt_sub_one_of_pos (div_pos hp_pos hq_pos) hdiv_ne
      have hm := mul_lt_mul_of_pos_left hlog_lt hq_pos
      have hrhs : q i * (wProb_v13 W sc l i / q i - 1) = wProb_v13 W sc l i - q i := by
        field_simp [hq_pos.ne']
      rw [Real.log_div hp_pos.ne' hq_pos.ne', hp_log, hrhs] at hm
      linarith
  · intro hq_eq
    rw [hinf_eq, ← hent_eq]
    have h1 : ∑ i ∈ W, q i * Real.log (q i) =
        ∑ i ∈ W, wProb_v13 W sc l i * Real.log (wProb_v13 W sc l i) :=
      Finset.sum_congr rfl fun i hi ↦ by rw [hq_eq i hi]
    have h2 : ∑ i ∈ W, q i * sc i = ∑ i ∈ W, wProb_v13 W sc l i * sc i :=
      Finset.sum_congr rfl fun i hi ↦ by rw [hq_eq i hi]
    rw [h1, h2]

private theorem wProb_and_wMean_perturbation_v13
    {W : Finset ℕ} (hW : W.Nonempty) {sc₁ sc₂ : ℕ → ℝ} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ_hi : δ ≤ 1 / 4)
    (hdiff : ∀ i ∈ W, |sc₁ i - sc₂ i| ≤ δ) (l : ℝ) :
    (∀ i ∈ W, |wProb_v13 W sc₁ l i - wProb_v13 W sc₂ l i| ≤ 4 * δ * wProb_v13 W sc₂ l i) ∧
      |wMean_v13 W sc₁ l - wMean_v13 W sc₂ l| ≤
        4 * (∑ i ∈ W, (i : ℝ) * wProb_v13 W sc₂ l i) * δ := by
  have hZ₁ := wPart_v13_pos hW sc₁ l
  have hZ₂ := wPart_v13_pos hW sc₂ l
  have hZ_lo : Real.exp (-δ) * wPart_v13 W sc₂ l ≤ wPart_v13 W sc₁ l := by
    unfold wPart_v13
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hdiff i hi)).1])
  have hZ_hi : wPart_v13 W sc₁ l ≤ Real.exp δ * wPart_v13 W sc₂ l := by
    unfold wPart_v13
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hdiff i hi)).2])
  have hexp_neg2 : 1 - 2 * δ ≤ Real.exp (-2 * δ) := by
    linarith [Real.add_one_le_exp (-2 * δ)]
  have hexp_pos2 : Real.exp (2 * δ) ≤ 1 + 4 * δ := by
    have h1 : 1 - 2 * δ ≤ Real.exp (-2 * δ) := hexp_neg2
    have hpos_1m : 0 < 1 - 2 * δ := by linarith
    have hmul : Real.exp (2 * δ) * (1 - 2 * δ) ≤ 1 := by
      calc Real.exp (2 * δ) * (1 - 2 * δ)
          ≤ Real.exp (2 * δ) * Real.exp (-2 * δ) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = Real.exp (2 * δ + (-2 * δ)) := (Real.exp_add _ _).symm
        _ = 1 := by simp
    have hdiv := (le_div_iff₀ hpos_1m).mpr hmul
    refine hdiv.trans ?_
    rw [div_le_iff₀ hpos_1m]
    nlinarith
  have hp_diff : ∀ i ∈ W,
      |wProb_v13 W sc₁ l i - wProb_v13 W sc₂ l i| ≤ 4 * δ * wProb_v13 W sc₂ l i := by
    intro i hi
    have hp₂_nn : 0 ≤ wProb_v13 W sc₂ l i := by
      simp only [wProb_v13, hi, ↓reduceIte]; exact div_nonneg (Real.exp_pos _).le hZ₂.le
    have hratio_lo : Real.exp (-2 * δ) * wProb_v13 W sc₂ l i ≤ wProb_v13 W sc₁ l i := by
      simp only [wProb_v13, hi, ↓reduceIte]
      have hw_lo : Real.exp (-δ) * Real.exp (l * (i : ℝ) + sc₂ i) ≤
          Real.exp (l * (i : ℝ) + sc₁ i) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hdiff i hi)).1])
      calc Real.exp (-2 * δ) * (Real.exp (l * (i : ℝ) + sc₂ i) / wPart_v13 W sc₂ l)
          = (Real.exp (-δ) * Real.exp (l * (i : ℝ) + sc₂ i)) /
              (Real.exp δ * wPart_v13 W sc₂ l) := by
            have h1 : Real.exp (-2 * δ) = Real.exp (-δ) / Real.exp δ := by
              rw [← Real.exp_sub]; congr 1; ring
            rw [h1]; field_simp [(Real.exp_pos _).ne', hZ₂.ne']
        _ ≤ Real.exp (l * (i : ℝ) + sc₁ i) / wPart_v13 W sc₁ l :=
            div_le_div₀ (Real.exp_pos _).le hw_lo hZ₁ hZ_hi
    have hratio_hi : wProb_v13 W sc₁ l i ≤ Real.exp (2 * δ) * wProb_v13 W sc₂ l i := by
      simp only [wProb_v13, hi, ↓reduceIte]
      have hw_hi : Real.exp (l * (i : ℝ) + sc₁ i) ≤
          Real.exp δ * Real.exp (l * (i : ℝ) + sc₂ i) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hdiff i hi)).2])
      calc Real.exp (l * (i : ℝ) + sc₁ i) / wPart_v13 W sc₁ l
          ≤ (Real.exp δ * Real.exp (l * (i : ℝ) + sc₂ i)) /
              (Real.exp (-δ) * wPart_v13 W sc₂ l) :=
            div_le_div₀ (by positivity) hw_hi (mul_pos (Real.exp_pos _) hZ₂) hZ_lo
        _ = Real.exp (2 * δ) * (Real.exp (l * (i : ℝ) + sc₂ i) / wPart_v13 W sc₂ l) := by
            have h1 : Real.exp (2 * δ) = Real.exp δ / Real.exp (-δ) := by
              rw [← Real.exp_sub]; congr 1; ring
            rw [h1]; field_simp [(Real.exp_pos _).ne', hZ₂.ne']
    rw [abs_le]
    have hlo' := mul_le_mul_of_nonneg_right hexp_neg2 hp₂_nn
    have hhi' := mul_le_mul_of_nonneg_right hexp_pos2 hp₂_nn
    exact ⟨by nlinarith, by nlinarith⟩
  refine ⟨hp_diff, ?_⟩
  rw [← sum_mul_wProb_v13 W sc₁ l, ← sum_mul_wProb_v13 W sc₂ l, ← Finset.sum_sub_distrib]
  calc |∑ i ∈ W, ((i : ℝ) * wProb_v13 W sc₁ l i - (i : ℝ) * wProb_v13 W sc₂ l i)|
      ≤ ∑ i ∈ W, |(i : ℝ) * (wProb_v13 W sc₁ l i - wProb_v13 W sc₂ l i)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
        exact Finset.sum_congr rfl fun _ _ ↦ by rw [← mul_sub]
    _ ≤ ∑ i ∈ W, (i : ℝ) * (4 * δ * wProb_v13 W sc₂ l i) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg i : (0 : ℝ) ≤ (i : ℝ))]
        exact mul_le_mul_of_nonneg_left (hp_diff i hi) (Nat.cast_nonneg i)
    _ = 4 * (∑ i ∈ W, (i : ℝ) * wProb_v13 W sc₂ l i) * δ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **Lemma 3.2(i)–(ii) (`main.tex` lines 561–587, eqs. `(3.4)`, `(3.10)`–`(3.12)`):**
for every `M ≥ 7`, there exist deterministic `M`-dependent constants `Λ_M > 0`, `c_star > 0`, and
`C_opt > 0` such that for every `α : ℕ` with `4 * (1 + M)² ≤ α`, `m ≤ 1`, and `T ∈ [9/4, 9/2]`
(covering `K_*`):
1. `M_S(λ) = T` and `M_{n,S}(λ) = T` (`S = S_{m, M}`) have unique solutions
   `λ_S(T), λ_{n, S}(T) ∈ [-Λ_M, Λ_M]`, with `|λ_{n, S}(T) - λ_S(T)| ≤ C_opt / α`;
2. `p_{n, S, T}(i) := exp(λ_{n, S}(T) i + h_n(i)) / Z_{n, S}(λ_{n, S}(T))` is the **unique**
   probability vector on `S_{m, M}` with mean `T` maximizing `-∑ p_i log p_i + ∑ p_i h_n(i)`
   (attaining `𝓕_{n, S_{m, M}}(T)`), and satisfies `p_{n, S, T}(i) ≥ 2 c_star` and
   `|p_{n, S, T}(i) - p_{S, T}(i)| ≤ C_opt / α` for all `i ∈ S_{m, M}` (`(3.12)`). -/
theorem existsUnique_windowFiniteGibbsTilt_and_optimizer_bounds_lemma32_ii
    {M : ℕ} (hM : 7 ≤ M) :
    ∃ Λ_M c_star C_opt : ℝ, 0 < Λ_M ∧ 0 < c_star ∧ 0 < C_opt ∧
      ∀ {alpha m : ℕ}, 4 * (1 + M) ^ 2 ≤ alpha → m ≤ 1 →
        let W : Finset ℕ := Finset.Icc (m + 1) (m + M)
        let h_sc : ℕ → ℝ := fun i ↦
          Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) -
            Real.log 2 / 2 * (i : ℝ) ^ 2
        let g_sc : ℕ → ℝ := fun i ↦ -Real.log 2 / 2 * (i : ℝ) ^ 2
        let Z_fin : ℝ → ℝ := fun l ↦ ∑ i ∈ W, Real.exp (l * (i : ℝ) + h_sc i)
        let M_fin : ℝ → ℝ := fun l ↦ (∑ i ∈ W, (i : ℝ) * Real.exp (l * (i : ℝ) + h_sc i)) / Z_fin l
        let Z_lim : ℝ → ℝ := fun l ↦ ∑ i ∈ W, Real.exp (l * (i : ℝ) + g_sc i)
        let M_lim : ℝ → ℝ := fun l ↦ (∑ i ∈ W, (i : ℝ) * Real.exp (l * (i : ℝ) + g_sc i)) / Z_lim l
        let F_fin : ℝ → ℝ := fun T ↦ ⨅ l : ℝ, (Real.log (Z_fin l) - l * T)
        ∀ {T : ℝ}, T ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) →
          (∃! l_lim : ℝ, M_lim l_lim = T) ∧
          (∃! l_fin : ℝ, M_fin l_fin = T) ∧
          (∀ {l_lim l_fin : ℝ}, M_lim l_lim = T → M_fin l_fin = T →
            l_lim ∈ Set.Icc (-Λ_M) Λ_M ∧
            l_fin ∈ Set.Icc (-Λ_M) Λ_M ∧
            |l_fin - l_lim| ≤ C_opt / (alpha : ℝ) ∧
            F_fin T = Real.log (Z_fin l_fin) - l_fin * T ∧
            let p_fin : ℕ → ℝ := fun i ↦
              if i ∈ W then Real.exp (l_fin * (i : ℝ) + h_sc i) / Z_fin l_fin else 0
            let p_lim : ℕ → ℝ := fun i ↦
              if i ∈ W then Real.exp (l_lim * (i : ℝ) + g_sc i) / Z_lim l_lim else 0
            (∑ i ∈ W, p_fin i = 1) ∧
            (∑ i ∈ W, (i : ℝ) * p_fin i = T) ∧
            F_fin T = -(∑ i ∈ W, p_fin i * Real.log (p_fin i)) + ∑ i ∈ W, p_fin i * h_sc i ∧
            (∀ q : ℕ → ℝ,
              (∀ i ∈ W, 0 ≤ q i) →
              ∑ i ∈ W, q i = 1 →
              ∑ i ∈ W, (i : ℝ) * q i = T →
              -(∑ i ∈ W, q i * Real.log (q i)) + ∑ i ∈ W, q i * h_sc i ≤ F_fin T ∧
                (-(∑ i ∈ W, q i * Real.log (q i)) + ∑ i ∈ W, q i * h_sc i = F_fin T ↔
                  ∀ i ∈ W, q i = p_fin i)) ∧
            (∀ i ∈ W,
              2 * c_star ≤ p_fin i ∧
              2 * c_star ≤ p_lim i ∧
              |p_fin i - p_lim i| ≤ C_opt / (alpha : ℝ))) := by
  let B_sc : ℝ := ((1 + M : ℕ) : ℝ) ^ 2 + 1
  let Λ_M : ℝ := wMasterLambda M
  let c_star : ℝ := wMasterCstar M
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hΛ_pos : 0 < Λ_M := by
    have : 0 < Real.log (8 * (M : ℝ) ^ 2 + 1) := Real.log_pos (by nlinarith)
    dsimp [Λ_M, wMasterLambda, wMasterBsc]; positivity
  have hc_pos : 0 < c_star := by dsimp [c_star, wMasterCstar]; positivity
  let C_tilt : ℝ := 4 * ((1 + M : ℕ) : ℝ) ^ 3 / c_star
  let C_opt : ℝ := max C_tilt (4 * ((1 + M : ℕ) : ℝ) ^ 2 + 2 * ((1 + M : ℕ) : ℝ) * C_tilt + 1)
  have hC_opt_pos : 0 < C_opt := by dsimp [C_opt, C_tilt]; positivity
  refine ⟨Λ_M, c_star, C_opt, hΛ_pos, hc_pos, hC_opt_pos, ?_⟩
  intro alpha m halpha hm W h_sc g_sc Z_fin M_fin Z_lim M_lim F_fin T hT
  have ha_pos : (0 : ℝ) < (alpha : ℝ) := by
    exact_mod_cast (show 0 < alpha by
      have := Nat.le_self_pow (by norm_num : 2 ≠ 0) (1 + M); omega)
  have hW_ne : W.Nonempty := ⟨m + 1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have h_sc_bds : ∀ i ∈ W, -B_sc ≤ h_sc i ∧ h_sc i ≤ 0 := by
    intro i hi
    obtain ⟨_, hi_hi⟩ := Finset.mem_Icc.mp hi
    have hi_lt : i < alpha := by
      have : (1 + M) ^ 2 ≥ 1 + M := Nat.le_self_pow (by norm_num) (1 + M)
      omega
    have h2i : 2 * i ≤ alpha := by
      have : (1 + M) ^ 2 ≥ 1 + M := Nat.le_self_pow (by norm_num) (1 + M)
      omega
    obtain ⟨hid, hle0, hge⟩ := finiteDeficitResidualScore_bounds hi_lt
    dsimp [h_sc]
    rw [hid]
    have hsq_le : (i : ℝ) ^ 2 ≤ ((1 + M : ℕ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg i) (by exact_mod_cast (show i ≤ 1 + M by omega)) 2
    have ha_ge_sq : ((1 + M : ℕ) : ℝ) ^ 2 ≤ (alpha : ℝ) := by
      have h4 : 4 * ((1 + M : ℕ) : ℝ) ^ 2 ≤ (alpha : ℝ) := by exact_mod_cast halpha
      linarith [sq_nonneg ((1 + M : ℕ) : ℝ)]
    have hdiv_ge : (-1 : ℝ) ≤ -(i : ℝ) ^ 2 / (alpha : ℝ) := by
      have h1 : (i : ℝ) ^ 2 / (alpha : ℝ) ≤ 1 :=
        (div_le_one ha_pos).mpr (hsq_le.trans ha_ge_sq)
      rw [neg_div]; linarith
    have hge' := hdiv_ge.trans (hge h2i)
    have hq_i : Real.log 2 / 2 * (i : ℝ) ^ 2 ≤ 1 * ((1 + M : ℕ) : ℝ) ^ 2 :=
      mul_le_mul (by linarith [Real.log_two_lt_d9]) hsq_le (sq_nonneg _) zero_le_one
    have hq_nn : 0 ≤ Real.log 2 / 2 * (i : ℝ) ^ 2 :=
      mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le zero_le_two) (sq_nonneg _)
    dsimp [B_sc]
    exact ⟨by linarith, by linarith⟩
  have hg_sc_bds : ∀ i ∈ W, -B_sc ≤ g_sc i ∧ g_sc i ≤ 0 := by
    intro i hi
    dsimp [g_sc, B_sc]
    have hsq_le : (i : ℝ) ^ 2 ≤ ((1 + M : ℕ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg i)
        (by exact_mod_cast (le_trans (Finset.mem_Icc.mp hi).2 (by omega : m + M ≤ 1 + M))) 2
    have hq_i : (Real.log 2 / 2) * (i : ℝ) ^ 2 ≤ 1 * ((1 + M : ℕ) : ℝ) ^ 2 :=
      mul_le_mul (by linarith [Real.log_two_lt_d9]) hsq_le (sq_nonneg _) zero_le_one
    have hq_nn : 0 ≤ (Real.log 2 / 2) * (i : ℝ) ^ 2 :=
      mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le zero_le_two) (sq_nonneg _)
    have hneg_eq : -Real.log 2 / 2 * (i : ℝ) ^ 2 = -((Real.log 2 / 2) * (i : ℝ) ^ 2) := by ring
    rw [hneg_eq]
    exact ⟨by linarith, by linarith⟩
  have hm_fin := windowGibbs_master_v13 hm hM h_sc_bds
  have hm_lim := windowGibbs_master_v13 hm hM hg_sc_bds
  obtain ⟨hexu_lim, hspec_lim⟩ := hm_lim.2.2.2.2 T hT
  obtain ⟨hexu_fin, hspec_fin⟩ := hm_fin.2.2.2.2 T hT
  refine ⟨hexu_lim, hexu_fin, ?_⟩
  intro l_lim l_fin hl_lim hl_fin
  obtain ⟨hlim_icc, -, -, -⟩ := hspec_lim l_lim hl_lim
  obtain ⟨hfin_icc, hF_eq1, hF_eq2, hopt_q⟩ := hspec_fin l_fin hl_fin
  -- Perturbation bound `δ := (1 + M)² / α ≤ 1 / 4`
  set δ : ℝ := ((1 + M : ℕ) : ℝ) ^ 2 / (alpha : ℝ)
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ_hi : δ ≤ 1 / 4 := by
    dsimp [δ]
    rw [div_le_iff₀ ha_pos]
    have ha_ge : 4 * ((1 + M : ℕ) : ℝ) ^ 2 ≤ (alpha : ℝ) := by exact_mod_cast halpha
    linarith
  have hsc_diff : ∀ i ∈ W, |h_sc i - g_sc i| ≤ δ := by
    intro i hi
    obtain ⟨_, hi_hi⟩ := Finset.mem_Icc.mp hi
    have hi_lt : i < alpha := by
      have : (1 + M) ^ 2 ≥ 1 + M := Nat.le_self_pow (by norm_num) (1 + M)
      omega
    have h2i : 2 * i ≤ alpha := by
      have : (1 + M) ^ 2 ≥ 1 + M := Nat.le_self_pow (by norm_num) (1 + M)
      omega
    obtain ⟨hid, hle0, hge⟩ := finiteDeficitResidualScore_bounds hi_lt
    have hsub : h_sc i - g_sc i = Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) := by
      dsimp [h_sc, g_sc]; ring
    rw [hsub, hid, abs_le]
    have hsq : (i : ℝ) ^ 2 ≤ ((1 + M : ℕ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg i) (by exact_mod_cast (show i ≤ 1 + M by omega)) 2
    have hlo : -δ ≤ -(i : ℝ) ^ 2 / (alpha : ℝ) := by
      dsimp [δ]
      have h1 := div_le_div_of_nonneg_right hsq ha_pos.le
      rw [neg_div]; linarith
    exact ⟨hlo.trans (hge h2i), hle0.trans hδ0⟩
  obtain ⟨hp_pert_at_lim, hm_pert_at_lim⟩ :=
    wProb_and_wMean_perturbation_v13 hW_ne hδ0 hδ_hi hsc_diff l_lim
  have hmean_diff : |wMean_v13 W h_sc l_lim - wMean_v13 W h_sc l_fin| ≤
      4 * ((1 + M : ℕ) : ℝ) ^ 3 / (alpha : ℝ) := by
    change wMean_v13 W h_sc l_fin = T at hl_fin
    change wMean_v13 W g_sc l_lim = T at hl_lim
    rw [hl_fin, ← hl_lim]
    have hsum_le : ∑ i ∈ W, (i : ℝ) * wProb_v13 W g_sc l_lim i ≤ ((1 + M : ℕ) : ℝ) := by
      rw [sum_mul_wProb_v13, hl_lim]
      have hM8 : (8 : ℝ) ≤ ((1 + M : ℕ) : ℝ) := by exact_mod_cast (show 8 ≤ 1 + M by omega)
      linarith only [hT.2, hM8]
    calc |wMean_v13 W h_sc l_lim - wMean_v13 W g_sc l_lim|
        ≤ 4 * (∑ i ∈ W, (i : ℝ) * wProb_v13 W g_sc l_lim i) * δ := hm_pert_at_lim
      _ ≤ 4 * ((1 + M : ℕ) : ℝ) * δ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum_le (by norm_num)) hδ0
      _ = 4 * ((1 + M : ℕ) : ℝ) ^ 3 / (alpha : ℝ) := by dsimp [δ]; ring
  -- Mean-value lower bound `c_star * |l_fin - l_lim| ≤ |M_fin l_fin - M_fin l_lim|`
  have hl_diff_le : |l_fin - l_lim| ≤ C_tilt / (alpha : ℝ) := by
    have hmvt_step : ∀ {a b : ℝ}, a ∈ Set.Icc (-Λ_M) Λ_M → b ∈ Set.Icc (-Λ_M) Λ_M → a ≤ b →
        c_star * (b - a) ≤ wMean_v13 W h_sc b - wMean_v13 W h_sc a := by
      intro a b ha hb hab
      have hsub_box : Set.Icc a b ⊆ Set.Icc (-Λ_M) Λ_M :=
        fun x hx ↦ ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
      exact derivative_lower_bound_mul_sub_le_sub hab
        (fun x _ ↦ (hasDerivAt_wMean_v13 hW_ne h_sc x).continuousAt.continuousWithinAt)
        (fun x _ ↦ (hasDerivAt_wMean_v13 hW_ne h_sc x).differentiableAt.differentiableWithinAt)
        (fun x hx ↦ by
          rw [(hasDerivAt_wMean_v13 hW_ne h_sc x).deriv]
          exact (hm_fin.2.2.2.1 x (hsub_box (Ioo_subset_Icc_self hx))).2)
    have hmul_le : c_star * |l_fin - l_lim| ≤ |wMean_v13 W h_sc l_lim - wMean_v13 W h_sc l_fin| := by
      rcases le_total l_lim l_fin with hle | hle
      · rw [abs_of_nonneg (sub_nonneg.mpr hle), abs_sub_comm,
          abs_of_nonneg (sub_nonneg.mpr (hm_fin.2.2.1.monotone hle))]
        exact hmvt_step hlim_icc hfin_icc hle
      · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle),
          abs_of_nonneg (sub_nonneg.mpr (hm_fin.2.2.1.monotone hle))]
        exact hmvt_step hfin_icc hlim_icc hle
    have hdiv := (le_div_iff₀' hc_pos).mpr (hmul_le.trans hmean_diff)
    refine hdiv.trans_eq ?_
    dsimp [C_tilt]; ring
  have hl_diff_opt : |l_fin - l_lim| ≤ C_opt / (alpha : ℝ) :=
    hl_diff_le.trans (div_le_div_of_nonneg_right (le_max_left _ _) ha_pos.le)
  refine ⟨hlim_icc, hfin_icc, hl_diff_opt, hF_eq1, ?_⟩
  intro p_fin p_lim
  refine ⟨sum_wProb_v13 hW_ne h_sc l_fin, (sum_mul_wProb_v13 W h_sc l_fin).trans hl_fin,
    hF_eq2, hopt_q, ?_⟩
  -- Lipschitz bound on `l ↦ wProb_v13 W h_sc l i` (`|∂_l p_i| = |i - M_fin l| p_i ≤ 2(1 + M)`)
  intro i hi
  have hp_fin_lo := (hm_fin.2.2.2.1 l_fin hfin_icc).1 i hi
  have hp_lim_lo := (hm_lim.2.2.2.1 l_lim hlim_icc).1 i hi
  have hp_lip_l :
      |wProb_v13 W h_sc l_fin i - wProb_v13 W h_sc l_lim i| ≤
        2 * ((1 + M : ℕ) : ℝ) * |l_fin - l_lim| := by
    have hd_prob : ∀ x : ℝ,
        HasDerivAt (fun μ ↦ wProb_v13 W h_sc μ i)
          (((i : ℝ) - wMean_v13 W h_sc x) * wProb_v13 W h_sc x i) x := by
      intro x
      have hZ := wPart_v13_pos hW_ne h_sc x
      have hfn : (fun μ ↦ wProb_v13 W h_sc μ i) =
          fun μ ↦ Real.exp (μ * (i : ℝ) + h_sc i) / wPart_v13 W h_sc μ := by
        funext μ; simp [wProb_v13, hi]
      rw [hfn]
      have hd1 : HasDerivAt (fun μ : ℝ ↦ Real.exp (μ * (i : ℝ) + h_sc i))
          ((i : ℝ) * Real.exp (x * (i : ℝ) + h_sc i)) x := by
        have hlin : HasDerivAt (fun μ : ℝ ↦ μ * (i : ℝ) + h_sc i) (i : ℝ) x := by
          simpa using ((hasDerivAt_id x).mul_const (i : ℝ)).add_const (h_sc i)
        exact (hlin.exp).congr_deriv (by ring)
      have hd2 : HasDerivAt (wPart_v13 W h_sc)
          (∑ j ∈ W, (j : ℝ) * Real.exp (x * (j : ℝ) + h_sc j)) x := by
        classical
        unfold wPart_v13
        have hstep : ∀ s : Finset ℕ,
            HasDerivAt (fun μ ↦ ∑ j ∈ s, Real.exp (μ * (j : ℝ) + h_sc j))
              (∑ j ∈ s, (j : ℝ) * Real.exp (x * (j : ℝ) + h_sc j)) x := by
          intro s
          induction s using Finset.induction_on with
          | empty => simpa using hasDerivAt_const x (0 : ℝ)
          | @insert a t ha ih =>
            have hf_eq : (fun μ ↦ ∑ j ∈ insert a t, Real.exp (μ * (j : ℝ) + h_sc j)) =
                fun μ ↦ Real.exp (μ * (a : ℝ) + h_sc a) +
                  ∑ j ∈ t, Real.exp (μ * (j : ℝ) + h_sc j) := by
              funext μ; exact Finset.sum_insert ha
            rw [hf_eq, Finset.sum_insert ha]
            have hda : HasDerivAt (fun μ : ℝ ↦ Real.exp (μ * (a : ℝ) + h_sc a))
                ((a : ℝ) * Real.exp (x * (a : ℝ) + h_sc a)) x := by
              have hl : HasDerivAt (fun μ : ℝ ↦ μ * (a : ℝ) + h_sc a) (a : ℝ) x := by
                simpa using ((hasDerivAt_id x).mul_const (a : ℝ)).add_const (h_sc a)
              exact (hl.exp).congr_deriv (by ring)
            exact hda.add ih
        exact hstep W
      refine (hd1.div hd2 hZ.ne').congr_deriv ?_
      simp only [wProb_v13, hi, ↓reduceIte, wMean_v13]
      field_simp [hZ.ne']
    have hnorm_deriv : ∀ x : ℝ,
        ‖((i : ℝ) - wMean_v13 W h_sc x) * wProb_v13 W h_sc x i‖ ≤ 2 * ((1 + M : ℕ) : ℝ) := by
      intro x
      have hZ := wPart_v13_pos hW_ne h_sc x
      have hp_nn : 0 ≤ wProb_v13 W h_sc x i := by
        simp only [wProb_v13, hi, ↓reduceIte]; exact div_nonneg (Real.exp_pos _).le hZ.le
      have hp_le1 : wProb_v13 W h_sc x i ≤ 1 := by
        rw [← sum_wProb_v13 hW_ne h_sc x]
        exact Finset.single_le_sum (fun j hj ↦ by
          simp only [wProb_v13, hj, ↓reduceIte]; exact div_nonneg (Real.exp_pos _).le hZ.le) hi
      have hm_nn : 0 ≤ wMean_v13 W h_sc x :=
        div_nonneg (Finset.sum_nonneg fun j _ ↦ mul_nonneg (Nat.cast_nonneg j) (Real.exp_pos _).le) hZ.le
      have hm_hi : wMean_v13 W h_sc x ≤ ((1 + M : ℕ) : ℝ) := by
        rw [← sum_mul_wProb_v13]
        calc ∑ j ∈ W, (j : ℝ) * wProb_v13 W h_sc x j
            ≤ ∑ j ∈ W, ((1 + M : ℕ) : ℝ) * wProb_v13 W h_sc x j := by
              refine Finset.sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_right ?_ ?_
              · exact_mod_cast (le_trans (Finset.mem_Icc.mp hj).2 (by omega : m + M ≤ 1 + M))
              · simp only [wProb_v13, hj, ↓reduceIte]; exact div_nonneg (Real.exp_pos _).le hZ.le
          _ = ((1 + M : ℕ) : ℝ) := by rw [← Finset.mul_sum, sum_wProb_v13 hW_ne, mul_one]
      have hi_hi : (i : ℝ) ≤ ((1 + M : ℕ) : ℝ) :=
        by exact_mod_cast (le_trans (Finset.mem_Icc.mp hi).2 (by omega : m + M ≤ 1 + M))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp_nn]
      have habs_im : |(i : ℝ) - wMean_v13 W h_sc x| ≤ 2 * ((1 + M : ℕ) : ℝ) := by
        rw [abs_le]
        have hi_nn : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        exact ⟨by linarith, by linarith⟩
      calc |(i : ℝ) - wMean_v13 W h_sc x| * wProb_v13 W h_sc x i
          ≤ (2 * ((1 + M : ℕ) : ℝ)) * 1 := mul_le_mul habs_im hp_le1 hp_nn (by positivity)
        _ = 2 * ((1 + M : ℕ) : ℝ) := mul_one _
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun μ ↦ wProb_v13 W h_sc μ i)
      (fun x _ ↦ (hd_prob x).hasDerivWithinAt)
      (fun x _ ↦ hnorm_deriv x) convex_univ (Set.mem_univ l_lim) (Set.mem_univ l_fin)
    simpa only [Real.norm_eq_abs] using hmvt
  have hp_lim_le1 : wProb_v13 W g_sc l_lim i ≤ 1 := by
    rw [← sum_wProb_v13 hW_ne g_sc l_lim]
    have hZ := wPart_v13_pos hW_ne g_sc l_lim
    exact Finset.single_le_sum (fun j hj ↦ by
      simp only [wProb_v13, hj, ↓reduceIte]; exact div_nonneg (Real.exp_pos _).le hZ.le) hi
  have hpert_i : |wProb_v13 W h_sc l_lim i - wProb_v13 W g_sc l_lim i| ≤
      4 * ((1 + M : ℕ) : ℝ) ^ 2 / (alpha : ℝ) := by
    calc |wProb_v13 W h_sc l_lim i - wProb_v13 W g_sc l_lim i|
        ≤ 4 * δ * wProb_v13 W g_sc l_lim i := hp_pert_at_lim i hi
      _ ≤ 4 * δ * 1 := mul_le_mul_of_nonneg_left hp_lim_le1 (by positivity)
      _ = 4 * ((1 + M : ℕ) : ℝ) ^ 2 / (alpha : ℝ) := by dsimp [δ]; ring
  refine ⟨hp_fin_lo, hp_lim_lo, ?_⟩
  change |wProb_v13 W h_sc l_fin i - wProb_v13 W g_sc l_lim i| ≤ C_opt / (alpha : ℝ)
  calc |wProb_v13 W h_sc l_fin i - wProb_v13 W g_sc l_lim i|
      ≤ |wProb_v13 W h_sc l_fin i - wProb_v13 W h_sc l_lim i| +
          |wProb_v13 W h_sc l_lim i - wProb_v13 W g_sc l_lim i| := abs_sub_le _ _ _
    _ ≤ 2 * ((1 + M : ℕ) : ℝ) * (C_tilt / (alpha : ℝ)) +
          4 * ((1 + M : ℕ) : ℝ) ^ 2 / (alpha : ℝ) :=
        add_le_add (hp_lip_l.trans (mul_le_mul_of_nonneg_left hl_diff_le (by positivity))) hpert_i
    _ ≤ C_opt / (alpha : ℝ) := by
        have h1 : 2 * ((1 + M : ℕ) : ℝ) * (C_tilt / (alpha : ℝ)) +
            4 * ((1 + M : ℕ) : ℝ) ^ 2 / (alpha : ℝ) =
          (4 * ((1 + M : ℕ) : ℝ) ^ 2 + 2 * ((1 + M : ℕ) : ℝ) * C_tilt) / (alpha : ℝ) := by ring
        rw [h1]
        apply div_le_div_of_nonneg_right _ ha_pos.le
        have hle_max := le_max_right C_tilt
          (4 * ((1 + M : ℕ) : ℝ) ^ 2 + 2 * ((1 + M : ℕ) : ℝ) * C_tilt + 1)
        dsimp [C_opt]; linarith

private theorem hasDerivAt_wDual_v13
    {m M : ℕ} (hm : m ≤ 1) (hM : 7 ≤ M) {sc : ℕ → ℝ}
    (hsc : ∀ i ∈ Finset.Icc (m + 1) (m + M),
      -(((1 + M : ℕ) : ℝ) ^ 2 + 1) ≤ sc i ∧ sc i ≤ 0)
    {T l₀ : ℝ} (hT : T ∈ Set.Ioo (9 / 4 : ℝ) (9 / 2))
    (hl₀ : wMean_v13 (Finset.Icc (m + 1) (m + M)) sc l₀ = T) :
    let W := Finset.Icc (m + 1) (m + M)
    HasDerivAt (fun t : ℝ ↦ ⨅ l : ℝ, (Real.log (wPart_v13 W sc l) - l * t)) (-l₀) T := by
  intro W
  have hW_ne : W.Nonempty := ⟨m + 1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have hm_all := windowGibbs_master_v13 hm hM hsc
  set c_star := wMasterCstar M
  have hc_pos : 0 < c_star := hm_all.2.1
  let F : ℝ → ℝ := fun t ↦ ⨅ l : ℝ, (Real.log (wPart_v13 W sc l) - l * t)
  have hF_T : F T = Real.log (wPart_v13 W sc l₀) - l₀ * T :=
    ((hm_all.2.2.2.2 T (Ioo_subset_Icc_self hT)).2 l₀ hl₀).2.1
  have hl₀_icc := ((hm_all.2.2.2.2 T (Ioo_subset_Icc_self hT)).2 l₀ hl₀).1
  -- Squeeze `|F T' - F T - (-l₀) * (T' - T)| ≤ (1 / c_star) * (T' - T)^2` on `Ioo (9/4) (9/2)`
  have hquad : ∀ T' ∈ Set.Ioo (9 / 4 : ℝ) (9 / 2),
      |F T' - F T - (-l₀) * (T' - T)| ≤ (1 / c_star) * |T' - T| ^ 2 := by
    intro T' hT'
    have hT'_icc := Ioo_subset_Icc_self hT'
    obtain ⟨⟨l', hl', _⟩, hspec'⟩ := hm_all.2.2.2.2 T' hT'_icc
    obtain ⟨hl'_icc, hF_T', -, -⟩ := hspec' l' hl'
    have hbdd_T' : BddBelow (Set.range fun l : ℝ ↦ Real.log (wPart_v13 W sc l) - l * T') := by
      refine ⟨F T', ?_⟩
      rintro _ ⟨l, rfl⟩
      by_contra hlt
      have : F T' < F T' := by
        -- Use `hF_T'` + KL inequality at `l'`
        have hZ' := wPart_v13_pos hW_ne sc l'
        have hZ_l := wPart_v13_pos hW_ne sc l
        have hkl : ∀ i ∈ W,
            wProb_v13 W sc l' i *
                ((l - l') * (i : ℝ) - Real.log (wPart_v13 W sc l) + Real.log (wPart_v13 W sc l')) ≤
              wProb_v13 W sc l i - wProb_v13 W sc l' i := by
          intro i hi
          have hp : 0 < wProb_v13 W sc l' i := by
            simp only [wProb_v13, hi, ↓reduceIte]; exact div_pos (Real.exp_pos _) hZ'
          have hq : 0 < wProb_v13 W sc l i := by
            simp only [wProb_v13, hi, ↓reduceIte]; exact div_pos (Real.exp_pos _) hZ_l
          have hlog := Real.log_le_sub_one_of_pos (div_pos hq hp)
          have hm := mul_le_mul_of_nonneg_left hlog hp.le
          have hrhs : wProb_v13 W sc l' i * (wProb_v13 W sc l i / wProb_v13 W sc l' i - 1) =
              wProb_v13 W sc l i - wProb_v13 W sc l' i := by field_simp [hp.ne']
          have hlhs : Real.log (wProb_v13 W sc l i / wProb_v13 W sc l' i) =
              (l - l') * (i : ℝ) - Real.log (wPart_v13 W sc l) + Real.log (wPart_v13 W sc l') := by
            simp only [wProb_v13, hi, ↓reduceIte]
            rw [Real.log_div (div_pos (Real.exp_pos _) hZ_l).ne' (div_pos (Real.exp_pos _) hZ').ne',
              Real.log_div (Real.exp_pos _).ne' hZ_l.ne',
              Real.log_div (Real.exp_pos _).ne' hZ'.ne', Real.log_exp, Real.log_exp]
            ring
          rwa [hlhs, hrhs] at hm
        have hsum := Finset.sum_le_sum hkl
        have hr0 : ∑ i ∈ W, (wProb_v13 W sc l i - wProb_v13 W sc l' i) = 0 := by
          rw [Finset.sum_sub_distrib, sum_wProb_v13 hW_ne, sum_wProb_v13 hW_ne, sub_self]
        have hle0 :
            (l - l') * T' - Real.log (wPart_v13 W sc l) + Real.log (wPart_v13 W sc l') ≤ 0 := by
          have h1 : ∀ i ∈ W,
              wProb_v13 W sc l' i *
                  ((l - l') * (i : ℝ) - Real.log (wPart_v13 W sc l) + Real.log (wPart_v13 W sc l')) =
                (l - l') * ((i : ℝ) * wProb_v13 W sc l' i) +
                  (-Real.log (wPart_v13 W sc l) + Real.log (wPart_v13 W sc l')) * wProb_v13 W sc l' i :=
            fun _ _ ↦ by ring
          rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            sum_mul_wProb_v13, hl', sum_wProb_v13 hW_ne, mul_one, hr0] at hsum
          linarith only [hsum]
        linarith [hF_T']
      exact lt_irrefl _ this
    have hbdd_T : BddBelow (Set.range fun l : ℝ ↦ Real.log (wPart_v13 W sc l) - l * T) := by
      refine ⟨F T, ?_⟩
      rintro _ ⟨l, rfl⟩
      -- Same bound via `hF_T` at `l₀`
      have hZ₀ := wPart_v13_pos hW_ne sc l₀
      have hZ_l := wPart_v13_pos hW_ne sc l
      have hkl : ∀ i ∈ W,
          wProb_v13 W sc l₀ i *
              ((l - l₀) * (i : ℝ) - Real.log (wPart_v13 W sc l) + Real.log (wPart_v13 W sc l₀)) ≤
            wProb_v13 W sc l i - wProb_v13 W sc l₀ i := by
        intro i hi
        have hp : 0 < wProb_v13 W sc l₀ i := by
          simp only [wProb_v13, hi, ↓reduceIte]; exact div_pos (Real.exp_pos _) hZ₀
        have hq : 0 < wProb_v13 W sc l i := by
          simp only [wProb_v13, hi, ↓reduceIte]; exact div_pos (Real.exp_pos _) hZ_l
        have hlog := Real.log_le_sub_one_of_pos (div_pos hq hp)
        have hm := mul_le_mul_of_nonneg_left hlog hp.le
        have hrhs : wProb_v13 W sc l₀ i * (wProb_v13 W sc l i / wProb_v13 W sc l₀ i - 1) =
            wProb_v13 W sc l i - wProb_v13 W sc l₀ i := by field_simp [hp.ne']
        have hlhs : Real.log (wProb_v13 W sc l i / wProb_v13 W sc l₀ i) =
            (l - l₀) * (i : ℝ) - Real.log (wPart_v13 W sc l) + Real.log (wPart_v13 W sc l₀) := by
          simp only [wProb_v13, hi, ↓reduceIte]
          rw [Real.log_div (div_pos (Real.exp_pos _) hZ_l).ne' (div_pos (Real.exp_pos _) hZ₀).ne',
            Real.log_div (Real.exp_pos _).ne' hZ_l.ne',
            Real.log_div (Real.exp_pos _).ne' hZ₀.ne', Real.log_exp, Real.log_exp]
          ring
        rwa [hlhs, hrhs] at hm
      have hsum := Finset.sum_le_sum hkl
      have hr0 : ∑ i ∈ W, (wProb_v13 W sc l i - wProb_v13 W sc l₀ i) = 0 := by
        rw [Finset.sum_sub_distrib, sum_wProb_v13 hW_ne, sum_wProb_v13 hW_ne, sub_self]
      have h1 : ∀ i ∈ W,
          wProb_v13 W sc l₀ i *
              ((l - l₀) * (i : ℝ) - Real.log (wPart_v13 W sc l) + Real.log (wPart_v13 W sc l₀)) =
            (l - l₀) * ((i : ℝ) * wProb_v13 W sc l₀ i) +
              (-Real.log (wPart_v13 W sc l) + Real.log (wPart_v13 W sc l₀)) * wProb_v13 W sc l₀ i :=
        fun _ _ ↦ by ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        sum_mul_wProb_v13, hl₀, sum_wProb_v13 hW_ne, mul_one, hr0] at hsum
      linarith [hF_T]
    have hhi : F T' - F T ≤ -l₀ * (T' - T) := by
      have h1 : F T' ≤ Real.log (wPart_v13 W sc l₀) - l₀ * T' := ciInf_le hbdd_T' l₀
      linarith [hF_T]
    have hlo : -l' * (T' - T) ≤ F T' - F T := by
      have h1 : F T ≤ Real.log (wPart_v13 W sc l') - l' * T := ciInf_le hbdd_T l'
      linarith [hF_T']
    -- Bound `|l' - l₀| ≤ (1 / c_star) * |T' - T|`
    have hl_lip : c_star * |l' - l₀| ≤ |T' - T| := by
      have hmvt_s : ∀ {a b : ℝ},
          a ∈ Set.Icc (-wMasterLambda M) (wMasterLambda M) →
          b ∈ Set.Icc (-wMasterLambda M) (wMasterLambda M) → a ≤ b →
          c_star * (b - a) ≤ wMean_v13 W sc b - wMean_v13 W sc a := by
        intro a b ha hb hab
        exact derivative_lower_bound_mul_sub_le_sub hab
          (fun x _ ↦ (hasDerivAt_wMean_v13 hW_ne sc x).continuousAt.continuousWithinAt)
          (fun x _ ↦ (hasDerivAt_wMean_v13 hW_ne sc x).differentiableAt.differentiableWithinAt)
          (fun x hx ↦ by
            rw [(hasDerivAt_wMean_v13 hW_ne sc x).deriv]
            exact (hm_all.2.2.2.1 x ⟨ha.1.trans (Ioo_subset_Icc_self hx).1,
              (Ioo_subset_Icc_self hx).2.trans hb.2⟩).2)
      rw [← hl', ← hl₀]
      rcases le_total l₀ l' with hle | hle
      · rw [abs_of_nonneg (sub_nonneg.mpr hle),
          abs_of_nonneg (sub_nonneg.mpr (hm_all.2.2.1.monotone hle))]
        exact hmvt_s hl₀_icc hl'_icc hle
      · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle), abs_sub_comm,
          abs_of_nonneg (sub_nonneg.mpr (hm_all.2.2.1.monotone hle))]
        exact hmvt_s hl'_icc hl₀_icc hle
    have habs_rem : |F T' - F T - (-l₀) * (T' - T)| ≤ |l' - l₀| * |T' - T| := by
      have hnonpos : F T' - F T - (-l₀) * (T' - T) ≤ 0 := by linarith
      have hge_prod : (l₀ - l') * (T' - T) ≤ F T' - F T - (-l₀) * (T' - T) := by linarith
      rw [abs_of_nonpos hnonpos]
      have h1 : -(F T' - F T - (-l₀) * (T' - T)) ≤ (l' - l₀) * (T' - T) := by linarith
      exact h1.trans ((le_abs_self _).trans_eq (abs_mul (l' - l₀) (T' - T)))
    have hl_div : |l' - l₀| ≤ (1 / c_star) * |T' - T| := by
      rw [one_div_mul_eq_div, le_div_iff₀' hc_pos]; exact hl_lip
    calc |F T' - F T - (-l₀) * (T' - T)|
        ≤ ((1 / c_star) * |T' - T|) * |T' - T| :=
          habs_rem.trans (mul_le_mul_of_nonneg_right hl_div (abs_nonneg _))
      _ = (1 / c_star) * |T' - T| ^ 2 := by ring
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro eps heps
  set r₀ : ℝ := min (min (T - 9 / 4) (9 / 2 - T)) (eps * c_star)
  have hr₀_pos : 0 < r₀ :=
    lt_min (lt_min (by linarith [hT.1]) (by linarith [hT.2])) (mul_pos heps hc_pos)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr₀_pos] with h hh
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh
  have hTh_mem : T + h ∈ Set.Ioo (9 / 4 : ℝ) (9 / 2) := by
    have h1 : |h| < T - 9 / 4 := lt_of_lt_of_le hh (le_trans (min_le_left _ _) (min_le_left _ _))
    have h2 : |h| < 9 / 2 - T := lt_of_lt_of_le hh (le_trans (min_le_left _ _) (min_le_right _ _))
    exact ⟨by linarith [(abs_lt.mp h1).1], by linarith [(abs_lt.mp h2).2]⟩
  have hhq := hquad (T + h) hTh_mem
  rw [show (T + h) - T = h by ring] at hhq
  have hh_le_eps : (1 / c_star) * |h| ≤ eps := by
    have h3 : |h| ≤ eps * c_star := (lt_of_lt_of_le hh (min_le_right _ _)).le
    rw [one_div_mul_eq_div, div_le_iff₀ hc_pos]; exact h3
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  simpa only [smul_eq_mul, mul_comm (-l₀) h] using
    hhq.trans (by
      calc (1 / c_star) * |h| ^ 2 = ((1 / c_star) * |h|) * |h| := by ring
        _ ≤ eps * |h| := mul_le_mul_of_nonneg_right hh_le_eps (abs_nonneg h))

private theorem h_sc_window_bounds_v13
    {alpha m' M' : ℕ} (hm' : m' ≤ 1) (halpha : 4 * (1 + M') ^ 2 ≤ alpha) :
    ∀ i ∈ Finset.Icc (m' + 1) (m' + M'),
      -(((1 + M' : ℕ) : ℝ) ^ 2 + 1) ≤
          Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) -
            Real.log 2 / 2 * (i : ℝ) ^ 2 ∧
        Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) -
            Real.log 2 / 2 * (i : ℝ) ^ 2 ≤ 0 := by
  intro i hi
  obtain ⟨_, hi_hi⟩ := Finset.mem_Icc.mp hi
  have h1M_sq : 1 + M' ≤ (1 + M') ^ 2 := Nat.le_self_pow (by norm_num) (1 + M')
  have hi_lt : i < alpha := by omega
  have h2i : 2 * i ≤ alpha := by omega
  obtain ⟨hid, hle0, hge⟩ := finiteDeficitResidualScore_bounds hi_lt
  rw [hid]
  have hsq : (i : ℝ) ^ 2 ≤ ((1 + M' : ℕ) : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg i) (by exact_mod_cast (show i ≤ 1 + M' by omega)) 2
  have ha_pos : (0 : ℝ) < (alpha : ℝ) := by exact_mod_cast (show 0 < alpha by omega)
  have ha_ge_sq : ((1 + M' : ℕ) : ℝ) ^ 2 ≤ (alpha : ℝ) := by
    have h4 : 4 * ((1 + M' : ℕ) : ℝ) ^ 2 ≤ (alpha : ℝ) := by exact_mod_cast halpha
    linarith only [h4, sq_nonneg ((1 + M' : ℕ) : ℝ)]
  have hdiv : (-1 : ℝ) ≤ -(i : ℝ) ^ 2 / (alpha : ℝ) := by
    have h1 := (div_le_one ha_pos).mpr (hsq.trans ha_ge_sq)
    rw [neg_div]; linarith only [h1]
  have hge' := hdiv.trans (hge h2i)
  have hq_i : Real.log 2 / 2 * (i : ℝ) ^ 2 ≤ 1 * ((1 + M' : ℕ) : ℝ) ^ 2 :=
    mul_le_mul (by linarith [Real.log_two_lt_d9]) hsq (sq_nonneg _) zero_le_one
  have hq_nn : 0 ≤ Real.log 2 / 2 * (i : ℝ) ^ 2 :=
    mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le zero_le_two) (sq_nonneg _)
  exact ⟨by linarith only [hge', hq_i], by linarith only [hle0, hq_nn]⟩

private theorem eventually_lemma31_corridor_invariants_v13 (A_pad : ℝ) (hApad : 0 ≤ A_pad) :
    ∀ᶠ n : ℕ in atTop,
      PhaseDomain n ∧
      (∀ s ∈ Set.Icc
          (phaseRootCenter n - A_pad * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n + A_pad * logLogOrder n * phaseRootGapRadius n),
        0 < s ∧
        |Real.log s| ≤ Real.log 2 + 4 * logOrder n ∧
        fourSizeTarget n (phaseNat n) s ∈ Set.Ioo (9 / 4 : ℝ) (17 / 4) ∧
        (phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar →
          fourSizeTarget n (phaseNat n) s ∈ KcapInterval)) := by
  have hLLC : ∀ᶠ n : ℕ in atTop,
      ‖logLogOrder n‖ ≤ (1 / (80 * (1 + A_pad))) * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound (by positivity)
  have hL4 : ∀ᶠ n : ℕ in atTop, max 4 (Real.exp 2) ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually_ge_atTop _
  have hLL1 : ∀ᶠ n : ℕ in atTop, max 1 (|2 * phaseC| + 4) ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop _
  have hn_le_exp : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≥ 3 :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop 3
  filter_upwards [hLLC, hL4, hLL1, hn_le_exp,
    eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_five_lt_phaseNat,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
    n hllc hLn hlln hn3 hcenterDom hfive hphase
  obtain ⟨hdom, hs0Pos, _⟩ := hcenterDom
  refine ⟨hdom, fun s hs ↦ ?_⟩
  set c : ℝ := phaseRootCenter n
  set a : ℝ := (phaseNat n : ℝ)
  set s0 : ℝ := phaseRootS0 n
  have hnPos : (0 : ℝ) < (n : ℝ) := by linarith
  have hcPos : 0 < c := div_pos hnPos hs0Pos
  have haSix : (6 : ℝ) ≤ a := by dsimp [a]; exact_mod_cast (Nat.succ_le_of_lt hfive)
  have haPos : 0 < a := by linarith
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
  have hLPos : 0 < logOrder n := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hLn)
  have hLL_ge1 : 1 ≤ logLogOrder n := (le_max_left _ _).trans hlln
  rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le zero_lt_one hLL_ge1),
    Real.norm_eq_abs, abs_of_pos hLPos] at hllc
  have hDeltaHalf : A_pad * logLogOrder n * phaseRootGapRadius n ≤ c / 2 := by
    have h1 : A_pad * logLogOrder n ≤ (1 + A_pad) * logLogOrder n :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : (1 + A_pad) * logLogOrder n ≤ logOrder n / 80 := by
      have hm := mul_le_mul_of_nonneg_left hllc (by linarith : (0 : ℝ) ≤ 1 + A_pad)
      have hs' : (1 + A_pad) * (1 / (80 * (1 + A_pad)) * logOrder n) = logOrder n / 80 := by field_simp
      linarith
    have h3 : A_pad * logLogOrder n ≤ a / 80 := h1.trans (h2.trans (by linarith [hphase.1]))
    have hfrac : A_pad * logLogOrder n / a ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ haSqPos]; nlinarith
    have hrew : A_pad * logLogOrder n * phaseRootGapRadius n = c * (A_pad * logLogOrder n / a ^ 2) := by
      dsimp [c, a]; unfold phaseRootGapRadius; ring
    rw [hrew]
    exact (mul_le_mul_of_nonneg_left hfrac hcPos.le).trans_eq (by ring)
  have hs_lo : c / 2 ≤ s := by linarith [hs.1, hDeltaHalf]
  have hs_hi : s ≤ 2 * c := by linarith [hs.2, hDeltaHalf, hcPos]
  have hs_pos : 0 < s := by linarith [hs_lo, hcPos]
  have hs0_le_a : s0 ≤ a := by
    dsimp [s0, a]
    rw [phaseRootS0, alphaZero_eq_phaseNat_add_delta hdom]
    have h2q : (1 : ℝ) < 2 / q := by rw [lt_div_iff₀ q_pos]; unfold q; linarith [Real.log_two_lt_d9]
    linarith [phaseDelta_lt_one n]
  have hs0_ge1 : 1 ≤ s0 := by
    dsimp [s0]
    rw [phaseRootS0, alphaZero_eq_phaseNat_add_delta hdom]
    have h2q_hi : 2 / q < 3 := by rw [div_lt_iff₀ q_pos]; unfold q; linarith [Real.log_two_gt_d9]
    linarith [phaseDelta_nonneg n, haSix]
  have hc_le_n : c ≤ (n : ℝ) := div_le_self hnPos.le hs0_ge1
  have hs_le_2n : s ≤ 2 * (n : ℝ) := hs_hi.trans (mul_le_mul_of_nonneg_left hc_le_n zero_le_two)
  have hs_ge_div : (n : ℝ) / (8 * logOrder n) ≤ s := by
    have hc_ge : (n : ℝ) / (4 * logOrder n) ≤ c :=
      div_le_div_of_nonneg_left hnPos.le hs0Pos (hs0_le_a.trans hphase.2)
    calc (n : ℝ) / (8 * logOrder n) = (n : ℝ) / (4 * logOrder n) / 2 := by ring
      _ ≤ c / 2 := div_le_div_of_nonneg_right hc_ge zero_le_two
      _ ≤ s := hs_lo
  have hlog_s_hi : Real.log s ≤ Real.log 2 + logOrder n := by
    have h1 := Real.log_le_log hs_pos hs_le_2n
    rw [Real.log_mul two_pos.ne' hnPos.ne'] at h1
    exact h1
  have hlog_s_lo : -(Real.log 2 + 4 * logOrder n) ≤ Real.log s := by
    have h1 := Real.log_le_log (by positivity) hs_ge_div
    rw [Real.log_div hnPos.ne' (by positivity),
      Real.log_mul (by norm_num) hLPos.ne'] at h1
    have hlog8 : Real.log 8 = 3 * Real.log 2 := by
      have h8 : (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
      rw [h8, Real.log_pow]; push_cast; rfl
    rw [hlog8] at h1
    have hll_le_L : logLogOrder n ≤ logOrder n :=
      (Real.log_le_sub_one_of_pos hLPos).trans (by linarith)
    have hq_le1 : Real.log 2 ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)
    have hL4' : 4 ≤ logOrder n := (le_max_left _ _).trans hLn
    dsimp [logOrder, logLogOrder] at *
    linarith
  have hlogs_abs : |Real.log s| ≤ Real.log 2 + 4 * logOrder n :=
    abs_le.mpr ⟨hlog_s_lo, by linarith [hLPos, hlog_s_hi]⟩
  have hnc : (n : ℝ) = c * s0 := by
    dsimp [c, s0]; unfold phaseRootCenter; exact (div_mul_cancel₀ _ hs0Pos.ne').symm
  have hdiff_s0 : (n : ℝ) / s - s0 = s0 * (c - s) / s := by rw [hnc]; field_simp [hs_pos.ne']
  have habs_cs : |c - s| ≤ A_pad * logLogOrder n * (c / a ^ 2) := by
    rw [abs_sub_comm, abs_le]
    have hgap : phaseRootGapRadius n = c / a ^ 2 := rfl
    rw [hgap] at hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hbound_s0 : |(n : ℝ) / s - s0| ≤ 1 / 40 := by
    have hb1 : |(n : ℝ) / s - s0| ≤ 2 * A_pad * logLogOrder n / logOrder n := by
      rw [hdiff_s0, abs_div, abs_mul, abs_of_pos hs0Pos, abs_of_pos hs_pos]
      calc s0 * |c - s| / s
          ≤ s0 * (A_pad * logLogOrder n * (c / a ^ 2)) / (c / 2) :=
            div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left habs_cs hs0Pos.le) (half_pos hcPos) hs_lo
        _ = 2 * A_pad * logLogOrder n * (s0 / a) / a := by field_simp [hcPos.ne', haPos.ne']
        _ ≤ 2 * A_pad * logLogOrder n * 1 / a := by
            apply div_le_div_of_nonneg_right _ haPos.le
            exact mul_le_mul_of_nonneg_left ((div_le_one haPos).mpr hs0_le_a) (by positivity)
        _ = 2 * A_pad * logLogOrder n / a := by ring
        _ ≤ 2 * A_pad * logLogOrder n / logOrder n :=
            div_le_div_of_nonneg_left (by positivity) hLPos hphase.1
    refine hb1.trans ?_
    rw [div_le_iff₀ hLPos]
    have hm := mul_le_mul_of_nonneg_left hllc (show (0 : ℝ) ≤ 2 * (1 + A_pad) by positivity)
    have hs' : 2 * (1 + A_pad) * (1 / (80 * (1 + A_pad)) * logOrder n) = 1 / 40 * logOrder n := by
      field_simp; ring
    have hc' : 2 * A_pad * logLogOrder n ≤ 2 * (1 + A_pad) * logLogOrder n :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  have htarget_eq : fourSizeTarget n (phaseNat n) s - phaseTarget (phaseDelta n) =
      s0 - (n : ℝ) / s := by
    dsimp [s0]; unfold fourSizeTarget phaseTarget phaseRootS0 q
    rw [alphaZero_eq_phaseNat_add_delta hdom]; ring
  have htar_diff : |fourSizeTarget n (phaseNat n) s - phaseTarget (phaseDelta n)| ≤ 1 / 40 := by
    rw [htarget_eq, abs_sub_comm]; exact hbound_s0
  obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
  have htar_bds := abs_le.mp htar_diff
  have hT_ioo : fourSizeTarget n (phaseNat n) s ∈ Set.Ioo (9 / 4 : ℝ) (17 / 4) := by
    unfold phaseTarget at htar_bds
    exact ⟨by linarith [phaseDelta_lt_one n, h2lo, htar_bds.1],
      by linarith [phaseDelta_nonneg n, h2hi, htar_bds.2]⟩
  refine ⟨hs_pos, hlogs_abs, hT_ioo, fun hd ↦ ?_⟩
  unfold phaseTarget at htar_bds; unfold deltaStar at hd; unfold KcapInterval
  exact ⟨by linarith [hd.2, htar_bds.1], by linarith [hd.1, htar_bds.2]⟩

private theorem lemma31_window_pointwise_v13
    {n m M : ℕ} (hm : m ≤ 1) (hM : 7 ≤ M)
    (ha_M : 4 * (1 + M) ^ 2 ≤ phaseNat n)
    {Λ_all : ℝ} (hΛ_all_pos : 0 < Λ_all) (hΛM_le : wMasterLambda M ≤ Λ_all)
    (hL4 : 4 ≤ logOrder n) (hw1 : 1 ≤ logLogOrder n)
    (ha_le4L : (phaseNat n : ℝ) ≤ 4 * logOrder n)
    (hquad_diff : |q / 2 * (phaseNat n : ℝ) ^ 2 - 2 / q * (logOrder n) ^ 2| ≤
      (21 / q) * logOrder n * logLogOrder n)
    (haff_diff : |(profileDeficitAffineA (phaseNat n) +
        profileDeficitAffineB (phaseNat n) * (phaseNat n : ℝ)) -
        q / 2 * (phaseNat n : ℝ) ^ 2| ≤ 8 * logOrder n + 8)
    {tau s : ℝ} (htau : tau ∈ Set.Icc (0 : ℝ) (Real.log 2))
    (hs_pos : 0 < s) (hlogs_abs : |Real.log s| ≤ Real.log 2 + 4 * logOrder n)
    (hT_ioo : fourSizeTarget n (phaseNat n) s ∈ Set.Ioo (9 / 4 : ℝ) (17 / 4)) :
    let h_sc : ℕ → ℝ := fun i ↦
      Real.log ((phaseNat n).descFactorial i : ℝ) - (i : ℝ) * Real.log (phaseNat n : ℝ) -
        Real.log 2 / 2 * (i : ℝ) ^ 2
    let F_win : ℝ → ℝ := fun T ↦ ⨅ l : ℝ,
      (Real.log (∑ i ∈ Finset.Icc (m + 1) (m + M), Real.exp (l * (i : ℝ) + h_sc i)) - l * T)
    let obj_win : ℝ → ℝ := fun k ↦
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + k - k * Real.log k +
        k * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) k +
          F_win (fourSizeTarget n (phaseNat n) k) + tau)
    let B_sc : ℝ := ((1 + M : ℕ) : ℝ) ^ 2 + 1
    let CL_w : ℝ := Λ_all * ((1 + M : ℕ) : ℝ) + B_sc + Real.log ((M : ℝ) + 1) + 2
    let K_rem : ℝ := 8 * Λ_all + CL_w + 2 * Real.log 2 + 24
    let K_slope : ℝ := 21 / q + K_rem + 1
    DifferentiableAt ℝ obj_win s ∧
      |deriv obj_win s - (2 / Real.log 2) * (Real.log (n : ℝ)) ^ 2| ≤
        K_slope * Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
  intro h_sc F_win obj_win B_sc CL_w K_rem K_slope
  set a : ℝ := (phaseNat n : ℝ)
  set L : ℝ := logOrder n
  set w : ℝ := logLogOrder n
  have hL_pos : 0 < L := by linarith only [hL4]
  have hw_pos : 0 < w := by linarith only [hw1]
  have hLw_ge_L : L ≤ L * w := le_mul_of_one_le_right hL_pos.le hw1
  have ha_nn : 0 ≤ a := Nat.cast_nonneg _
  have hBsc_pos : 0 < B_sc := by dsimp [B_sc]; positivity
  have hCL_pos : 0 < CL_w := by
    have : 0 < Real.log ((M : ℝ) + 1) := Real.log_pos (by exact_mod_cast (show 1 < M + 1 by omega))
    dsimp [CL_w]; positivity
  have hKrem_pos : 0 < K_rem := by have := Real.log_pos one_lt_two; dsimp [K_rem]; positivity
  set T : ℝ := fourSizeTarget n (phaseNat n) s
  have hT_wide_ioo : T ∈ Set.Ioo (9 / 4 : ℝ) (9 / 2) := ⟨hT_ioo.1, by linarith only [hT_ioo.2]⟩
  have hsc_M := h_sc_window_bounds_v13 hm ha_M
  have hm_win := windowGibbs_master_v13 hm hM hsc_M
  obtain ⟨⟨l_fin, hl_fin_eq, _⟩, hspec_w⟩ := hm_win.2.2.2.2 T (Ioo_subset_Icc_self hT_wide_ioo)
  obtain ⟨hl_fin_icc, hF_eq, -, -⟩ := hspec_w l_fin hl_fin_eq
  clear hm_win hspec_w
  have hFwin_eq : F_win = fun t : ℝ ↦ ⨅ l : ℝ,
      (Real.log (wPart_v13 (Finset.Icc (m + 1) (m + M)) h_sc l) - l * t) := rfl
  have hd_F : HasDerivAt F_win (-l_fin) T := by
    rw [hFwin_eq]
    exact hasDerivAt_wDual_v13 hm hM hsc_M hT_wide_ioo hl_fin_eq
  have hd_tar : HasDerivAt (fourSizeTarget n (phaseNat n)) ((n : ℝ) / s ^ 2) s := by
    unfold fourSizeTarget
    have h1 : HasDerivAt (fun k : ℝ ↦ (n : ℝ) / k) (-((n : ℝ) / s ^ 2)) s := by
      have hd := (hasDerivAt_const s (n : ℝ)).div (hasDerivAt_id s) hs_pos.ne'
      change HasDerivAt (fun k : ℝ ↦ (n : ℝ) / k) _ s at hd
      exact hd.congr_deriv (by dsimp; ring)
    exact ((hasDerivAt_const s (phaseNat n : ℝ)).sub h1).congr_deriv (by ring)
  have hd_comp0 := hd_F.comp s hd_tar
  have hd_comp : HasDerivAt (fun k ↦ F_win (fourSizeTarget n (phaseNat n) k))
      ((-l_fin) * ((n : ℝ) / s ^ 2)) s := hd_comp0
  set D_val : ℝ :=
    -Real.log s + profileDeficitAffineA (phaseNat n) +
      profileDeficitAffineB (phaseNat n) * a +
      Real.log (wPart_v13 (Finset.Icc (m + 1) (m + M)) h_sc l_fin) - l_fin * a + tau
  have hd_obj : HasDerivAt obj_win D_val s := by
    have hd_base : HasDerivAt (fun k : ℝ ↦ (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + k - k * Real.log k)
        (-Real.log s) s := by
      have h := ((hasDerivAt_const s ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ))).add
        (hasDerivAt_id s)).sub ((hasDerivAt_id s).mul (Real.hasDerivAt_log hs_pos.ne'))
      apply h.congr_deriv; dsimp; rw [mul_inv_cancel₀ hs_pos.ne']; ring
    have hd_inner : HasDerivAt
        (fun k ↦ profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) k +
          F_win (fourSizeTarget n (phaseNat n) k) + tau)
        (profileDeficitAffineB (phaseNat n) * ((n : ℝ) / s ^ 2) +
          (-l_fin) * ((n : ℝ) / s ^ 2)) s :=
      ((((hasDerivAt_const s _).add (hd_tar.const_mul _)).add hd_comp).add (hasDerivAt_const s tau)).congr_deriv
        (by ring)
    have hd_prod := (hasDerivAt_id s).mul hd_inner
    refine (hd_base.add hd_prod).congr_deriv ?_
    have hF_T : F_win T = Real.log (wPart_v13 (Finset.Icc (m + 1) (m + M)) h_sc l_fin) - l_fin * T := hF_eq
    dsimp [D_val, id_eq]
    rw [hF_T]
    dsimp [T, a]; unfold fourSizeTarget
    field_simp [hs_pos.ne']; ring
  refine ⟨hd_obj.differentiableAt, ?_⟩
  rw [hd_obj.deriv]
  have hl_abs : |l_fin| ≤ Λ_all := (abs_le.mpr hl_fin_icc).trans hΛM_le
  have hlogZ_abs : |Real.log (wPart_v13 (Finset.Icc (m + 1) (m + M)) h_sc l_fin)| ≤ CL_w := by
    have hm1_in : m + 1 ∈ Finset.Icc (m + 1) (m + M) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    have hcard_W : (Finset.Icc (m + 1) (m + M)).card = M := by rw [Nat.card_Icc]; omega
    have hsc_m1 : -B_sc ≤ h_sc (m + 1) := (hsc_M (m + 1) hm1_in).1
    have hZ_lo : Real.exp (-Λ_all * ((1 + M : ℕ) : ℝ) - B_sc) ≤
        wPart_v13 (Finset.Icc (m + 1) (m + M)) h_sc l_fin := by
      calc Real.exp (-Λ_all * ((1 + M : ℕ) : ℝ) - B_sc)
          ≤ Real.exp (l_fin * ((m + 1 : ℕ) : ℝ) + h_sc (m + 1)) := by
            apply Real.exp_le_exp.mpr
            have hm1_le : ((m + 1 : ℕ) : ℝ) ≤ ((1 + M : ℕ) : ℝ) :=
              by exact_mod_cast (show m + 1 ≤ 1 + M by omega)
            have hprod : |l_fin * ((m + 1 : ℕ) : ℝ)| ≤ Λ_all * ((1 + M : ℕ) : ℝ) := by
              rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]
              exact mul_le_mul hl_abs hm1_le (Nat.cast_nonneg _) hΛ_all_pos.le
            have hp_lo := (abs_le.mp hprod).1
            linarith only [hp_lo, hsc_m1]
        _ ≤ wPart_v13 (Finset.Icc (m + 1) (m + M)) h_sc l_fin :=
            Finset.single_le_sum (f := fun i : ℕ ↦ Real.exp (l_fin * (i : ℝ) + h_sc i))
              (fun _ _ ↦ (Real.exp_pos _).le) hm1_in
    have hZ_hi : wPart_v13 (Finset.Icc (m + 1) (m + M)) h_sc l_fin ≤
        ((M : ℝ) + 1) * Real.exp (Λ_all * ((1 + M : ℕ) : ℝ)) := by
      calc wPart_v13 (Finset.Icc (m + 1) (m + M)) h_sc l_fin
          ≤ ∑ _i ∈ Finset.Icc (m + 1) (m + M), Real.exp (Λ_all * ((1 + M : ℕ) : ℝ)) := by
            refine Finset.sum_le_sum fun i hi ↦ Real.exp_le_exp.mpr ?_
            have hi_le : (i : ℝ) ≤ ((1 + M : ℕ) : ℝ) := by
              exact_mod_cast (le_trans (Finset.mem_Icc.mp hi).2 (by omega : m + M ≤ 1 + M))
            have hprod : l_fin * (i : ℝ) ≤ Λ_all * ((1 + M : ℕ) : ℝ) :=
              (mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg i)).trans
                (mul_le_mul hl_abs hi_le (Nat.cast_nonneg i) hΛ_all_pos.le)
            have hsc_i : h_sc i ≤ 0 := (hsc_M i hi).2
            linarith only [hprod, hsc_i]
        _ = (M : ℝ) * Real.exp (Λ_all * ((1 + M : ℕ) : ℝ)) := by
            rw [Finset.sum_const, hcard_W, nsmul_eq_mul]
        _ ≤ ((M : ℝ) + 1) * Real.exp (Λ_all * ((1 + M : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    have hZ_pos := wPart_v13_pos ⟨m + 1, hm1_in⟩ h_sc l_fin
    have hlog_lo := Real.log_le_log (Real.exp_pos _) hZ_lo
    have hlog_hi := Real.log_le_log hZ_pos hZ_hi
    rw [Real.log_exp] at hlog_lo
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hlog_hi
    rw [abs_le]; dsimp [CL_w]
    have hlogM_pos : 0 < Real.log ((M : ℝ) + 1) :=
      Real.log_pos (by exact_mod_cast (show 1 < M + 1 by omega))
    exact ⟨by linarith only [hlog_lo, hBsc_pos, hlogM_pos],
      by linarith only [hlog_hi, hBsc_pos, hlogM_pos]⟩
  have hla_abs : |l_fin * a| ≤ 4 * Λ_all * L := by
    rw [abs_mul, abs_of_nonneg ha_nn]
    calc |l_fin| * a ≤ Λ_all * (4 * L) := mul_le_mul hl_abs ha_le4L ha_nn hΛ_all_pos.le
      _ = 4 * Λ_all * L := by ring
  have htau_abs : |tau| ≤ Real.log 2 :=
    abs_le.mpr ⟨by linarith only [htau.1, Real.log_pos one_lt_two], htau.2⟩
  have hrem_abs : |D_val - q / 2 * a ^ 2| ≤ K_rem * (L * w) := by
    have hCL_L : CL_w ≤ CL_w * L := le_mul_of_one_le_right hCL_pos.le (by linarith only [hL4])
    have hq_L : Real.log 2 ≤ Real.log 2 * L :=
      le_mul_of_one_le_right (Real.log_pos one_lt_two).le (by linarith only [hL4])
    have hΛL_nn : 0 ≤ Λ_all * L := mul_nonneg hΛ_all_pos.le hL_pos.le
    have hsum_L : |D_val - q / 2 * a ^ 2| ≤ K_rem * L := by
      have h1 := abs_le.mp haff_diff
      have h2 := abs_le.mp hlogs_abs
      have h3 := abs_le.mp hlogZ_abs
      have h4 := abs_le.mp hla_abs
      have h5 := abs_le.mp htau_abs
      rw [abs_le]
      have hK_eq : K_rem * L =
          8 * (Λ_all * L) + CL_w * L + 2 * (Real.log 2 * L) + 24 * L := by
        dsimp [K_rem]; ring
      rw [hK_eq]; dsimp [D_val, L] at h2 hL4 ⊢
      exact ⟨by linarith only [h1.1, h2.2, h3.1, h4.2, h5.1, hCL_L, hq_L, hΛL_nn, hL4],
        by linarith only [h1.2, h2.1, h3.2, h4.1, h5.2, hCL_L, hq_L, hΛL_nn, hL4]⟩
    exact hsum_L.trans (mul_le_mul_of_nonneg_left hLw_ge_L hKrem_pos.le)
  have hql2 : q = Real.log 2 := rfl
  have hdecomp : D_val - (2 / Real.log 2) * (Real.log (n : ℝ)) ^ 2 =
      (q / 2 * a ^ 2 - 2 / q * L ^ 2) + (D_val - q / 2 * a ^ 2) := by
    dsimp [L]; unfold logOrder; rw [← hql2]; ring
  have htot : |D_val - (2 / Real.log 2) * (Real.log (n : ℝ)) ^ 2| ≤ K_slope * L * w := by
    rw [hdecomp]
    calc |(q / 2 * a ^ 2 - 2 / q * L ^ 2) + (D_val - q / 2 * a ^ 2)|
        ≤ |q / 2 * a ^ 2 - 2 / q * L ^ 2| + |D_val - q / 2 * a ^ 2| := abs_add_le _ _
      _ ≤ (21 / q) * L * w + K_rem * (L * w) := add_le_add hquad_diff hrem_abs
      _ ≤ K_slope * L * w := by
          have hid : K_slope * L * w = (21 / q) * L * w + K_rem * (L * w) + L * w := by
            dsimp [K_slope]; ring
          have hLw_nn := mul_nonneg hL_pos.le hw_pos.le
          linarith only [hid, hLw_nn]
  simpa only [L, w, logOrder, logLogOrder] using htot

private theorem lemma31_capped_pointwise_v13
    {n M : ℕ} (hM8 : 8 ≤ M)
    (ha_Mp : 4 * (1 + (M - 1)) ^ 2 ≤ phaseNat n)
    {Λ_all : ℝ} (hΛ_all_pos : 0 < Λ_all) (hΛMp_le : wMasterLambda (M - 1) ≤ Λ_all)
    (hL4 : 4 ≤ logOrder n) (hw1 : 1 ≤ logLogOrder n)
    (ha_le4L : (phaseNat n : ℝ) ≤ 4 * logOrder n)
    (hquad_diff : |q / 2 * (phaseNat n : ℝ) ^ 2 - 2 / q * (logOrder n) ^ 2| ≤
      (21 / q) * logOrder n * logLogOrder n)
    (haff_diff : |(profileDeficitAffineA (phaseNat n) +
        profileDeficitAffineB (phaseNat n) * (phaseNat n : ℝ)) -
        q / 2 * (phaseNat n : ℝ) ^ 2| ≤ 8 * logOrder n + 8)
    {theta tau s : ℝ} (htheta : theta ∈ Set.Icc (0 : ℝ) (1 / 20))
    (htau : tau ∈ Set.Icc (0 : ℝ) (Real.log 2))
    (hs_pos : 0 < s) (hlogs_abs : |Real.log s| ≤ Real.log 2 + 4 * logOrder n)
    (hTK : fourSizeTarget n (phaseNat n) s ∈ KcapInterval) :
    let h_sc : ℕ → ℝ := fun i ↦
      Real.log ((phaseNat n).descFactorial i : ℝ) - (i : ℝ) * Real.log (phaseNat n : ℝ) -
        Real.log 2 / 2 * (i : ℝ) ^ 2
    let F_cap : ℝ → ℝ := fun T ↦
      binEntropy theta - Real.log 2 / 2 * theta +
        (1 - theta) * (⨅ l : ℝ,
          (Real.log (∑ i ∈ Finset.Icc 2 M, Real.exp (l * (i : ℝ) + h_sc i)) -
            l * ((T - theta) / (1 - theta))))
    let obj_cap : ℝ → ℝ := fun k ↦
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + k - k * Real.log k +
        k * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) k +
          F_cap (fourSizeTarget n (phaseNat n) k) + tau)
    let B_sc : ℝ := ((1 + M : ℕ) : ℝ) ^ 2 + 1
    let CL_w : ℝ := Λ_all * ((1 + M : ℕ) : ℝ) + B_sc + Real.log ((M : ℝ) + 1) + 2
    let K_rem : ℝ := 8 * Λ_all + CL_w + 2 * Real.log 2 + 24
    let K_slope : ℝ := 21 / q + K_rem + 1
    DifferentiableAt ℝ obj_cap s ∧
      |deriv obj_cap s - (2 / Real.log 2) * (Real.log (n : ℝ)) ^ 2| ≤
        K_slope * Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
  intro h_sc F_cap obj_cap B_sc CL_w K_rem K_slope
  set a : ℝ := (phaseNat n : ℝ)
  set L : ℝ := logOrder n
  set w : ℝ := logLogOrder n
  have hL_pos : 0 < L := by linarith only [hL4]
  have hw_pos : 0 < w := by linarith only [hw1]
  have hLw_ge_L : L ≤ L * w := le_mul_of_one_le_right hL_pos.le hw1
  have ha_nn : 0 ≤ a := Nat.cast_nonneg _
  have hBsc_pos : 0 < B_sc := by dsimp [B_sc]; positivity
  have hCL_pos : 0 < CL_w := by
    have : 0 < Real.log ((M : ℝ) + 1) := Real.log_pos (by exact_mod_cast (show 1 < M + 1 by omega))
    dsimp [CL_w]; positivity
  have hKrem_pos : 0 < K_rem := by have := Real.log_pos one_lt_two; dsimp [K_rem]; positivity
  set T : ℝ := fourSizeTarget n (phaseNat n) s
  have h1m_pos : 0 < 1 - theta := by linarith only [htheta.2]
  have h1m_le1 : 1 - theta ≤ 1 := by linarith only [htheta.1]
  set u : ℝ := (T - theta) / (1 - theta)
  have hu_ioo : u ∈ Set.Ioo (9 / 4 : ℝ) (9 / 2) := by
    obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
    obtain ⟨hT_lo, hT_hi⟩ := hTK
    dsimp [u]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ h1m_pos]; linarith only [htheta.1, htheta.2, hT_lo, h2lo]
    · rw [div_lt_iff₀ h1m_pos]; linarith only [htheta.1, htheta.2, hT_hi, h2hi]
  have h1_Mp : 1 + (M - 1) = M := by omega
  have hM7_p : 7 ≤ M - 1 := by omega
  have hsc_p := h_sc_window_bounds_v13 (m' := 1) (M' := M - 1) le_rfl ha_Mp
  have hm_tail := windowGibbs_master_v13 (m := 1) (M := M - 1) le_rfl hM7_p hsc_p
  obtain ⟨⟨l_fin, hl_fin_eq, _⟩, hspec_t⟩ := hm_tail.2.2.2.2 u (Ioo_subset_Icc_self hu_ioo)
  obtain ⟨hl_fin_icc, hF_tail_eq, -, -⟩ := hspec_t l_fin hl_fin_eq
  clear hm_tail hspec_t
  have hd_tail : HasDerivAt
      (fun v : ℝ ↦ ⨅ l : ℝ,
        (Real.log (wPart_v13 (Finset.Icc (1 + 1) (1 + (M - 1))) h_sc l) - l * v))
      (-l_fin) u :=
    hasDerivAt_wDual_v13 (m := 1) (M := M - 1) le_rfl hM7_p hsc_p hu_ioo hl_fin_eq
  have hIcc_eq : Finset.Icc 2 M = Finset.Icc (1 + 1) (1 + (M - 1)) := by rw [h1_Mp]
  have hd_Fcap : HasDerivAt F_cap (-l_fin) T := by
    have hfn : F_cap = fun t ↦ binEntropy theta - Real.log 2 / 2 * theta +
        (1 - theta) * (⨅ l : ℝ,
          (Real.log (wPart_v13 (Finset.Icc (1 + 1) (1 + (M - 1))) h_sc l) -
            l * ((t - theta) / (1 - theta)))) := by
      funext t; dsimp [F_cap, wPart_v13]; rw [hIcc_eq]
    rw [hfn]
    have hd_u : HasDerivAt (fun t : ℝ ↦ (t - theta) / (1 - theta)) (1 / (1 - theta)) T := by
      simpa [one_div] using ((hasDerivAt_id T).sub_const theta).div_const (1 - theta)
    have hd_c := ((hd_tail.comp T hd_u).const_mul (1 - theta)).const_add
      (binEntropy theta - Real.log 2 / 2 * theta)
    apply hd_c.congr_deriv
    field_simp [h1m_pos.ne']
  have hd_tar : HasDerivAt (fourSizeTarget n (phaseNat n)) ((n : ℝ) / s ^ 2) s := by
    unfold fourSizeTarget
    have h1 : HasDerivAt (fun k : ℝ ↦ (n : ℝ) / k) (-((n : ℝ) / s ^ 2)) s := by
      have hd := (hasDerivAt_const s (n : ℝ)).div (hasDerivAt_id s) hs_pos.ne'
      change HasDerivAt (fun k : ℝ ↦ (n : ℝ) / k) _ s at hd
      exact hd.congr_deriv (by dsimp; ring)
    exact ((hasDerivAt_const s (phaseNat n : ℝ)).sub h1).congr_deriv (by ring)
  have hd_comp0 := hd_Fcap.comp s hd_tar
  have hd_comp : HasDerivAt (fun k ↦ F_cap (fourSizeTarget n (phaseNat n) k))
      ((-l_fin) * ((n : ℝ) / s ^ 2)) s := hd_comp0
  set Z_val : ℝ := wPart_v13 (Finset.Icc (1 + 1) (1 + (M - 1))) h_sc l_fin
  set D_val : ℝ :=
    -Real.log s + profileDeficitAffineA (phaseNat n) +
      profileDeficitAffineB (phaseNat n) * a +
      binEntropy theta - Real.log 2 / 2 * theta +
      (1 - theta) * Real.log Z_val - l_fin * (a - theta) + tau
  have hd_obj : HasDerivAt obj_cap D_val s := by
    have hd_base : HasDerivAt (fun k : ℝ ↦ (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + k - k * Real.log k)
        (-Real.log s) s := by
      have h := ((hasDerivAt_const s ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ))).add
        (hasDerivAt_id s)).sub ((hasDerivAt_id s).mul (Real.hasDerivAt_log hs_pos.ne'))
      apply h.congr_deriv; dsimp; rw [mul_inv_cancel₀ hs_pos.ne']; ring
    have hd_inner : HasDerivAt
        (fun k ↦ profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) k +
          F_cap (fourSizeTarget n (phaseNat n) k) + tau)
        (profileDeficitAffineB (phaseNat n) * ((n : ℝ) / s ^ 2) +
          (-l_fin) * ((n : ℝ) / s ^ 2)) s :=
      ((((hasDerivAt_const s _).add (hd_tar.const_mul _)).add hd_comp).add (hasDerivAt_const s tau)).congr_deriv
        (by ring)
    have hd_prod := (hasDerivAt_id s).mul hd_inner
    refine (hd_base.add hd_prod).congr_deriv ?_
    have hFcap_T : F_cap T = binEntropy theta - Real.log 2 / 2 * theta +
        (1 - theta) * (Real.log Z_val - l_fin * u) := by
      dsimp [F_cap, Z_val, u, wPart_v13]
      rw [hIcc_eq]
      exact congrArg (fun x ↦ binEntropy theta - Real.log 2 / 2 * theta + (1 - theta) * x) hF_tail_eq
    dsimp [D_val, id_eq]
    rw [hFcap_T]
    dsimp [u, T, a]; unfold fourSizeTarget
    field_simp [hs_pos.ne', h1m_pos.ne']; ring
  refine ⟨hd_obj.differentiableAt, ?_⟩
  rw [hd_obj.deriv]
  have hl_abs : |l_fin| ≤ Λ_all := (abs_le.mpr hl_fin_icc).trans hΛMp_le
  have hlogZ_abs : |Real.log Z_val| ≤ CL_w := by
    have hm1_in : 2 ∈ Finset.Icc (1 + 1) (1 + (M - 1)) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    have hcard_W : (Finset.Icc (1 + 1) (1 + (M - 1))).card = M - 1 := by rw [Nat.card_Icc]; omega
    have hsc_2 : -(((1 + (M - 1) : ℕ) : ℝ) ^ 2 + 1) ≤ h_sc 2 := (hsc_p 2 hm1_in).1
    have hZ_lo : Real.exp (-Λ_all * ((1 + M : ℕ) : ℝ) - B_sc) ≤ Z_val := by
      calc Real.exp (-Λ_all * ((1 + M : ℕ) : ℝ) - B_sc)
          ≤ Real.exp (l_fin * (2 : ℝ) + h_sc 2) := by
            apply Real.exp_le_exp.mpr
            have h2_le : (2 : ℝ) ≤ ((1 + M : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 1 + M by omega)
            have hprod : |l_fin * (2 : ℝ)| ≤ Λ_all * ((1 + M : ℕ) : ℝ) := by
              rw [abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)]
              exact mul_le_mul hl_abs h2_le zero_le_two hΛ_all_pos.le
            have hB_le : ((1 + (M - 1) : ℕ) : ℝ) ^ 2 + 1 ≤ B_sc := by
              dsimp [B_sc]
              have hle_sq : ((1 + (M - 1) : ℕ) : ℝ) ^ 2 ≤ ((1 + M : ℕ) : ℝ) ^ 2 :=
                pow_le_pow_left₀ (Nat.cast_nonneg _)
                  (by exact_mod_cast (show 1 + (M - 1) ≤ 1 + M by omega)) 2
              linarith only [hle_sq]
            have hp_lo := (abs_le.mp hprod).1
            linarith only [hp_lo, hsc_2, hB_le]
        _ ≤ Z_val :=
            Finset.single_le_sum (f := fun i : ℕ ↦ Real.exp (l_fin * (i : ℝ) + h_sc i))
              (fun _ _ ↦ (Real.exp_pos _).le) hm1_in
    have hZ_hi : Z_val ≤ ((M : ℝ) + 1) * Real.exp (Λ_all * ((1 + M : ℕ) : ℝ)) := by
      calc Z_val
          ≤ ∑ _i ∈ Finset.Icc (1 + 1) (1 + (M - 1)), Real.exp (Λ_all * ((1 + M : ℕ) : ℝ)) := by
            refine Finset.sum_le_sum fun i hi ↦ Real.exp_le_exp.mpr ?_
            have hi_le : (i : ℝ) ≤ ((1 + M : ℕ) : ℝ) := by
              exact_mod_cast (le_trans (Finset.mem_Icc.mp hi).2 (by omega : 1 + (M - 1) ≤ 1 + M))
            have hprod : l_fin * (i : ℝ) ≤ Λ_all * ((1 + M : ℕ) : ℝ) :=
              (mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg i)).trans
                (mul_le_mul hl_abs hi_le (Nat.cast_nonneg i) hΛ_all_pos.le)
            have hsc_i : h_sc i ≤ 0 := (hsc_p i hi).2
            linarith only [hprod, hsc_i]
        _ = ((M - 1 : ℕ) : ℝ) * Real.exp (Λ_all * ((1 + M : ℕ) : ℝ)) := by
            rw [Finset.sum_const, hcard_W, nsmul_eq_mul]
        _ ≤ ((M : ℝ) + 1) * Real.exp (Λ_all * ((1 + M : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast (show M - 1 ≤ M + 1 by omega)) (Real.exp_pos _).le
    have hZ_pos := wPart_v13_pos ⟨2, hm1_in⟩ h_sc l_fin
    have hlog_lo := Real.log_le_log (Real.exp_pos _) hZ_lo
    have hlog_hi := Real.log_le_log hZ_pos hZ_hi
    rw [Real.log_exp] at hlog_lo
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hlog_hi
    rw [abs_le]; dsimp [CL_w]
    have hlogM_pos : 0 < Real.log ((M : ℝ) + 1) :=
      Real.log_pos (by exact_mod_cast (show 1 < M + 1 by omega))
    exact ⟨by linarith only [hlog_lo, hBsc_pos, hlogM_pos],
      by linarith only [hlog_hi, hBsc_pos, hlogM_pos]⟩
  have h1m_logZ : |(1 - theta) * Real.log Z_val| ≤ CL_w := by
    rw [abs_mul, abs_of_pos h1m_pos]
    exact (mul_le_mul h1m_le1 hlogZ_abs (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hla_th : |l_fin * (a - theta)| ≤ 8 * Λ_all * L := by
    have hath : |a - theta| ≤ 8 * L := by
      rw [abs_le]
      exact ⟨by linarith only [htheta.2, hL4, ha_nn], by linarith only [htheta.1, ha_le4L, hL4]⟩
    rw [abs_mul]
    calc |l_fin| * |a - theta| ≤ Λ_all * (8 * L) := mul_le_mul hl_abs hath (abs_nonneg _) hΛ_all_pos.le
      _ = 8 * Λ_all * L := by ring
  have hbin_bds : 0 ≤ binEntropy theta ∧ binEntropy theta ≤ 1 := by
    unfold binEntropy
    rcases eq_or_lt_of_le htheta.1 with rfl | hpos
    · simp
    · have hlt1 : theta < 1 := by linarith only [htheta.2]
      have hlog_th : Real.log theta ≤ 0 := Real.log_nonpos hpos.le hlt1.le
      have hlog_1m : Real.log (1 - theta) ≤ 0 := Real.log_nonpos h1m_pos.le h1m_le1
      have hnn1 : 0 ≤ -theta * Real.log theta :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith only [hpos]) hlog_th
      have hnn2 : 0 ≤ -(1 - theta) * Real.log (1 - theta) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith only [h1m_pos]) hlog_1m
      have hinv1 : -theta * Real.log theta ≤ 1 - theta := by
        have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
        rw [Real.log_inv] at h
        have hm := mul_le_mul_of_nonneg_left h hpos.le
        have hc : theta * (theta⁻¹ - 1) = 1 - theta := by field_simp [hpos.ne']
        linarith only [hm, hc]
      have hinv2 : -(1 - theta) * Real.log (1 - theta) ≤ theta := by
        have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h1m_pos)
        rw [Real.log_inv] at h
        have hm := mul_le_mul_of_nonneg_left h h1m_pos.le
        have hc : (1 - theta) * ((1 - theta)⁻¹ - 1) = theta := by field_simp [h1m_pos.ne']; ring
        linarith only [hm, hc]
      exact ⟨by linarith only [hnn1, hnn2], by linarith only [hinv1, hinv2]⟩
  have hq_th : 0 ≤ Real.log 2 / 2 * theta ∧ Real.log 2 / 2 * theta ≤ 1 := by
    refine ⟨mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le zero_le_two) htheta.1, ?_⟩
    have hm := mul_le_mul_of_nonneg_left htheta.2 (div_pos (Real.log_pos one_lt_two) two_pos).le
    linarith only [hm, Real.log_two_lt_d9]
  have htau_abs : |tau| ≤ Real.log 2 :=
    abs_le.mpr ⟨by linarith only [htau.1, Real.log_pos one_lt_two], htau.2⟩
  have hrem_abs : |D_val - q / 2 * a ^ 2| ≤ K_rem * (L * w) := by
    have hCL_L : CL_w ≤ CL_w * L := le_mul_of_one_le_right hCL_pos.le (by linarith only [hL4])
    have hq_L : Real.log 2 ≤ Real.log 2 * L :=
      le_mul_of_one_le_right (Real.log_pos one_lt_two).le (by linarith only [hL4])
    have hsum_L : |D_val - q / 2 * a ^ 2| ≤ K_rem * L := by
      have h1 := abs_le.mp haff_diff
      have h2 := abs_le.mp hlogs_abs
      have h3 := abs_le.mp h1m_logZ
      have h4 := abs_le.mp hla_th
      have h5 := abs_le.mp htau_abs
      rw [abs_le]
      have hK_eq : K_rem * L =
          8 * Λ_all * L + CL_w * L + 2 * (Real.log 2 * L) + 24 * L := by
        dsimp [K_rem]; ring
      rw [hK_eq]; dsimp [D_val, L] at h2 hL4 ⊢
      exact ⟨by linarith only [h1.1, h2.2, h3.1, h4.2, h5.1, hbin_bds.1, hq_th.2, hCL_L, hq_L, hL4],
        by linarith only [h1.2, h2.1, h3.2, h4.1, h5.2, hbin_bds.2, hq_th.1, hCL_L, hq_L, hL4]⟩
    exact hsum_L.trans (mul_le_mul_of_nonneg_left hLw_ge_L hKrem_pos.le)
  have hql2 : q = Real.log 2 := rfl
  have hdecomp : D_val - (2 / Real.log 2) * (Real.log (n : ℝ)) ^ 2 =
      (q / 2 * a ^ 2 - 2 / q * L ^ 2) + (D_val - q / 2 * a ^ 2) := by
    dsimp [L]; unfold logOrder; rw [← hql2]; ring
  have htot : |D_val - (2 / Real.log 2) * (Real.log (n : ℝ)) ^ 2| ≤ K_slope * L * w := by
    rw [hdecomp]
    calc |(q / 2 * a ^ 2 - 2 / q * L ^ 2) + (D_val - q / 2 * a ^ 2)|
        ≤ |q / 2 * a ^ 2 - 2 / q * L ^ 2| + |D_val - q / 2 * a ^ 2| := abs_add_le _ _
      _ ≤ (21 / q) * L * w + K_rem * (L * w) := add_le_add hquad_diff hrem_abs
      _ ≤ K_slope * L * w := by
          have hid : K_slope * L * w = (21 / q) * L * w + K_rem * (L * w) + L * w := by
            dsimp [K_slope]; ring
          have hLw_nn := mul_nonneg hL_pos.le hw_pos.le
          linarith only [hid, hLw_nn]
  simpa only [L, w, logOrder, logLogOrder] using htot

/-- **Lemma 3.1, eqs. `(3.7)` & `(3.8)` (`main.tex` lines 537–555):**
1. for every `M ≥ 7` and `A ≥ 0`, there exists `K_slope > 0` such that eventually across the
   corridor `[c_n - A Δ_n, c_n + A Δ_n]`:
   - uniformly over `m ≤ 1` and `τ ∈ [0, log 2]`, `𝓛_{S_{m, M}}(n, ·) + τ ·` is differentiable at
     `s` with `|∂_k (𝓛_{S_{m, M}}(n, k) + τ k)|_{k=s} - (2 / log 2)(log n)²| ≤ K_slope (log n)(log log n)`,
   - when `8 ≤ M` and `δ_n ∈ [0, δ_*]`, uniformly over `ϑ ∈ [0, 1/20]` and `τ ∈ [0, log 2]`,
     `𝓛_{S_{0, M}}^{=ϑ}(n, ·) + τ ·` is differentiable at `s` with the same `(3.7)` bound;
2. `(3.8)` holds identically at every `k ≠ 0`: `(𝓛_R(n, k) - 𝓛_S(n, k)) / k = 𝓕_{n, R}(T) - 𝓕_{n, S}(T)`. -/
theorem eventually_window_and_capped_phaseObjective_deriv_and_diff_lemma31
    {M : ℕ} (hM : 7 ≤ M) (A : ℝ) (hA : 0 ≤ A) :
    (∀ {n : ℕ} {k : ℝ} (F_R F_S : ℝ → ℝ), k ≠ 0 →
      let T : ℝ := fourSizeTarget n (phaseNat n) k
      let L_of : (ℝ → ℝ) → ℝ := fun F ↦
        (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + k - k * Real.log k +
          k * (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * T + F T)
      (L_of F_R - L_of F_S) / k = F_R T - F_S T) ∧
    (∃ K_slope : ℝ, 0 < K_slope ∧ ∀ᶠ n : ℕ in atTop,
      let h_sc : ℕ → ℝ := fun i ↦
        Real.log ((phaseNat n).descFactorial i : ℝ) - (i : ℝ) * Real.log (phaseNat n : ℝ) -
          Real.log 2 / 2 * (i : ℝ) ^ 2
      (∀ {m : ℕ}, m ≤ 1 → ∀ tau ∈ Set.Icc (0 : ℝ) (Real.log 2),
        let F_win : ℝ → ℝ := fun T ↦ ⨅ l : ℝ,
          (Real.log (∑ i ∈ Finset.Icc (m + 1) (m + M), Real.exp (l * (i : ℝ) + h_sc i)) - l * T)
        let obj_win : ℝ → ℝ := fun k ↦
          (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + k - k * Real.log k +
            k * (profileDeficitAffineA (phaseNat n) +
              profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) k +
              F_win (fourSizeTarget n (phaseNat n) k) + tau)
        ∀ s ∈ Set.Icc
            (phaseRootCenter n - A * logLogOrder n * phaseRootGapRadius n)
            (phaseRootCenter n + A * logLogOrder n * phaseRootGapRadius n),
          DifferentiableAt ℝ obj_win s ∧
            |deriv obj_win s - (2 / Real.log 2) * (Real.log (n : ℝ)) ^ 2| ≤
              K_slope * Real.log (n : ℝ) * Real.log (Real.log (n : ℝ))) ∧
      (8 ≤ M → phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar →
        ∀ theta ∈ Set.Icc (0 : ℝ) (1 / 20), ∀ tau ∈ Set.Icc (0 : ℝ) (Real.log 2),
          let F_cap : ℝ → ℝ := fun T ↦
            binEntropy theta - Real.log 2 / 2 * theta +
              (1 - theta) * (⨅ l : ℝ,
                (Real.log (∑ i ∈ Finset.Icc 2 M, Real.exp (l * (i : ℝ) + h_sc i)) -
                  l * ((T - theta) / (1 - theta))))
          let obj_cap : ℝ → ℝ := fun k ↦
            (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + k - k * Real.log k +
              k * (profileDeficitAffineA (phaseNat n) +
                profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) k +
                F_cap (fourSizeTarget n (phaseNat n) k) + tau)
          ∀ s ∈ Set.Icc
              (phaseRootCenter n - A * logLogOrder n * phaseRootGapRadius n)
              (phaseRootCenter n + A * logLogOrder n * phaseRootGapRadius n),
            DifferentiableAt ℝ obj_cap s ∧
              |deriv obj_cap s - (2 / Real.log 2) * (Real.log (n : ℝ)) ^ 2| ≤
                K_slope * Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)))) := by
  refine ⟨fun {n k} F_R F_S hk ↦ by
    intro T L_of; dsimp [L_of]; field_simp [hk]; ring, ?_⟩
  set M_pred : ℕ := max 7 (M - 1)
  set Λ_all : ℝ := max (wMasterLambda M) (wMasterLambda M_pred)
  have hΛ_pos : 0 < wMasterLambda M := by
    have : 0 < Real.log (8 * (M : ℝ) ^ 2 + 1) := Real.log_pos (by
      have : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
      nlinarith)
    unfold wMasterLambda wMasterBsc; positivity
  have hΛ_all_pos : 0 < Λ_all := lt_of_lt_of_le hΛ_pos (le_max_left _ _)
  have hΛM_le_all : wMasterLambda M ≤ Λ_all := le_max_left _ _
  have hΛMp_le_all : wMasterLambda M_pred ≤ Λ_all := le_max_right _ _
  let B_sc : ℝ := ((1 + M : ℕ) : ℝ) ^ 2 + 1
  let CL_w : ℝ := Λ_all * ((1 + M : ℕ) : ℝ) + B_sc + Real.log ((M : ℝ) + 1) + 2
  let K_rem : ℝ := 8 * Λ_all + CL_w + 2 * Real.log 2 + 24
  let K_slope : ℝ := 21 / q + K_rem + 1
  have hK_slope_pos : 0 < K_slope := by
    have : 0 < Real.log ((M : ℝ) + 1) := Real.log_pos (by exact_mod_cast (show 1 < M + 1 by omega))
    have := Real.log_pos one_lt_two
    have := q_pos
    dsimp [K_slope, K_rem, CL_w, B_sc]; positivity
  refine ⟨K_slope, hK_slope_pos, ?_⟩
  set A_pad : ℝ := A + 1
  have halpha_big : ∀ᶠ n : ℕ in atTop, 4 * (1 + M) ^ 2 + 6 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop
        (((4 * (1 + M) ^ 2 + 6 : ℕ) : ℝ)),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  have hWn : ∀ᶠ n : ℕ in atTop, max 1 (|2 * phaseC| + q + 2) ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop _
  have hWL : ∀ᶠ n : ℕ in atTop, ‖logLogOrder n‖ ≤ 1 * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound zero_lt_one
  have hLn4 : ∀ᶠ n : ℕ in atTop, 4 ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually_ge_atTop 4
  filter_upwards [eventually_lemma31_corridor_invariants_v13 A_pad (by dsimp [A_pad]; linarith),
    halpha_big, hWn, hWL, hLn4,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
    n ⟨hdom, hCorr⟩ halpha hW_b hW_le hL4 hphase
  intro h_sc
  set a : ℝ := (phaseNat n : ℝ)
  set L : ℝ := logOrder n
  set w : ℝ := logLogOrder n
  have hw1 : 1 ≤ w := (le_max_left _ _).trans hW_b
  have hw_c : |2 * phaseC| + q + 2 ≤ w := (le_max_right _ _).trans hW_b
  have hL_pos : 0 < L := by linarith only [hL4]
  have hw_pos : 0 < w := by linarith only [hw1]
  have ha_le4L : a ≤ 4 * L := hphase.2
  have ha_nn : 0 ≤ a := Nat.cast_nonneg _
  have hCorr_sub :
      Set.Icc (phaseRootCenter n - A * logLogOrder n * phaseRootGapRadius n)
              (phaseRootCenter n + A * logLogOrder n * phaseRootGapRadius n) ⊆
      Set.Icc (phaseRootCenter n - A_pad * logLogOrder n * phaseRootGapRadius n)
              (phaseRootCenter n + A_pad * logLogOrder n * phaseRootGapRadius n) := by
    intro s hs
    have hrad_nn : 0 ≤ logLogOrder n * phaseRootGapRadius n := by
      unfold phaseRootGapRadius
      have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hdom.1)
      have hs0Pos : 0 < phaseRootS0 n := by
        unfold phaseRootS0
        rw [alphaZero_eq_phaseNat_add_delta hdom]
        have h2q : 2 / q < 3 := by rw [div_lt_iff₀ q_pos]; unfold q; linarith [Real.log_two_gt_d9]
        have ha6 : (6 : ℝ) ≤ (phaseNat n : ℝ) := by exact_mod_cast (show 6 ≤ phaseNat n by omega)
        linarith [phaseDelta_nonneg n]
      exact mul_nonneg hw_pos.le (div_nonneg (div_nonneg hnPos.le hs0Pos.le) (sq_nonneg _))
    have hm := mul_le_mul_of_nonneg_right (show A ≤ A_pad by dsimp [A_pad]; linarith) hrad_nn
    exact ⟨by linarith only [hs.1, hm], by linarith only [hs.2, hm]⟩
  rw [Real.norm_eq_abs, abs_of_pos hw_pos, Real.norm_eq_abs, abs_of_pos hL_pos, one_mul] at hW_le
  have hphaseExact : a * q = 2 * L - 2 * w + 2 * phaseC + q * phaseB n := by
    dsimp [a, L, w]
    rw [phaseNat_cast_eq_two_phaseS_div_q_add_phaseB hdom]
    unfold phaseS; field_simp [q_ne_zero]
  have haq_diff : |a * q - 2 * L| ≤ 3 * w := by
    have hb_pos : 0 ≤ q * phaseB n := mul_nonneg q_pos.le (phaseB_pos n).le
    have hb_hi : q * phaseB n ≤ q :=
      (mul_le_mul_of_nonneg_left (phaseB_le_one n) q_pos.le).trans_eq (mul_one q)
    have hc_abs := abs_le.mp (le_rfl : |2 * phaseC| ≤ |2 * phaseC|)
    rw [show a * q - 2 * L = -2 * w + 2 * phaseC + q * phaseB n by linarith only [hphaseExact], abs_le]
    exact ⟨by linarith only [hw_c, hb_pos, hc_abs.1, q_pos, hw1],
      by linarith only [hw_c, hb_hi, hc_abs.2, q_pos, hw1]⟩
  have hquad_diff : |q / 2 * a ^ 2 - 2 / q * L ^ 2| ≤ (21 / q) * L * w := by
    have hid_q : q / 2 * a ^ 2 - 2 / q * L ^ 2 = ((a * q - 2 * L) * (a * q + 2 * L)) / (2 * q) := by
      field_simp [q_ne_zero]; ring
    have haq_sum : |a * q + 2 * L| ≤ 7 * L := by
      have h1 := abs_add_le (a * q - 2 * L) (4 * L)
      rw [abs_of_pos (by positivity : 0 < 4 * L)] at h1
      have h2 : (a * q - 2 * L) + 4 * L = a * q + 2 * L := by ring
      rw [h2] at h1
      linarith only [h1, haq_diff, hW_le]
    rw [hid_q, abs_div, abs_mul, abs_of_pos (mul_pos two_pos q_pos)]
    calc |a * q - 2 * L| * |a * q + 2 * L| / (2 * q)
        ≤ (3 * w) * (7 * L) / (2 * q) := by
          apply div_le_div_of_nonneg_right _ (mul_pos two_pos q_pos).le
          exact mul_le_mul haq_diff haq_sum (abs_nonneg _) (by positivity)
      _ ≤ (21 / q) * L * w := by
          have h1 : (0 : ℝ) ≤ L * w / q := div_nonneg (mul_nonneg hL_pos.le hw_pos.le) q_pos.le
          have e1 : (3 * w) * (7 * L) / (2 * q) = (21 / 2) * (L * w / q) := by ring
          have e2 : (21 / q) * L * w = 21 * (L * w / q) := by ring
          linarith only [h1, e1, e2]
  have haff_diff :
      |(profileDeficitAffineA (phaseNat n) + profileDeficitAffineB (phaseNat n) * a) -
          q / 2 * a ^ 2| ≤ 8 * L + 8 := by
    have hcore := abs_le.mp (abs_profileDeficitAffineCore_sub_quadratic_le (phaseNat n) (by omega))
    have hfac : factorialLogErrorBound (phaseNat n) ≤ 4 * L + 4 := by
      have h := Real.log_le_sub_one_of_pos (x := ((phaseNat n + 1 : ℕ) : ℝ)) (by positivity)
      have hEq : factorialLogErrorBound (phaseNat n) = Real.log ((phaseNat n + 1 : ℕ) : ℝ) + 4 := rfl
      rw [hEq]; push_cast at h ⊢; linarith only [h, ha_le4L]
    have hfac_nn : 0 ≤ factorialLogErrorBound (phaseNat n) := by
      have hEq : factorialLogErrorBound (phaseNat n) = Real.log ((phaseNat n + 1 : ℕ) : ℝ) + 4 := rfl
      rw [hEq]
      have hnn : 0 ≤ Real.log ((phaseNat n + 1 : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ phaseNat n + 1 by omega))
      linarith only [hnn]
    rw [abs_le]
    dsimp [a] at hcore ha_nn ha_le4L ⊢
    exact ⟨by linarith only [hcore.1, hfac, ha_le4L], by linarith only [hcore.2, hfac, ha_le4L]⟩
  refine ⟨?_, ?_⟩
  · intro m hm tau htau F_win obj_win s hs
    obtain ⟨hs_pos, hlogs_abs, hT_ioo, -⟩ := hCorr s (hCorr_sub hs)
    exact lemma31_window_pointwise_v13 hm hM (by omega) hΛ_all_pos hΛM_le_all
      hL4 hw1 ha_le4L hquad_diff haff_diff htau hs_pos hlogs_abs hT_ioo
  · intro hM8 hd theta htheta tau htau F_cap obj_cap s hs
    obtain ⟨hs_pos, hlogs_abs, _, hTK_fn⟩ := hCorr s (hCorr_sub hs)
    have hMp_eq : M_pred = M - 1 := by dsimp [M_pred]; omega
    have hΛMp' : wMasterLambda (M - 1) ≤ Λ_all := by rwa [← hMp_eq]
    have ha_Mp : 4 * (1 + (M - 1)) ^ 2 ≤ phaseNat n := by
      have h1 := Nat.pow_le_pow_left (show 1 + (M - 1) ≤ 1 + M by omega) 2
      omega
    exact lemma31_capped_pointwise_v13 hM8 ha_Mp hΛ_all_pos hΛMp'
      hL4 hw1 ha_le4L hquad_diff haff_diff htheta htau hs_pos hlogs_abs (hTK_fn hd)

/-!
## 3. Unconditional Proposition 5.3(i)–(ii): selected integer profiles & first-moment growth
-/

private def embedWindowProfile_v13 (alpha m M : ℕ) (kv : Fin M → ℕ) : ColoringProfile alpha :=
  fun idx ↦ ∑ j : Fin M, if alpha - (m + 1 + j.1) = idx.1 + 1 then kv j else 0

private theorem embedWindowProfile_properties_v13
    {n alpha m M : ℕ} (halpha : m + M + 2 ≤ alpha)
    {kv : Fin M → ℕ}
    (hMass : selectedVertexMass (fun j : Fin M ↦ alpha - (m + 1 + j.1)) kv = n) :
    let u : Fin M → ℕ := fun j ↦ alpha - (m + 1 + j.1)
    let kp : ColoringProfile alpha := embedWindowProfile_v13 alpha m M kv
    (∀ j : Fin M, kp ⟨u j - 1, by dsimp [u]; omega⟩ = kv j) ∧
    ColoringProfile.partCount kp = selectedBlockCount kv ∧
    ColoringProfile.vertexMass kp = n ∧
    ColoringProfile.forbiddenEdges kp = selectedInternalEdgeCount u kv ∧
    (profileColoringExpectation n kp).toReal = completeUnmarkedFirstMoment u kv ∧
    (signedProfileExpectation n kp).toReal = completeSignedFirstMoment u kv ∧
    (∀ P : ProfilePartition n kp,
      P.1.parts.card = selectedBlockCount kv ∧
      ∀ D ∈ P.1.parts, alpha - (m + M) ≤ D.card ∧ D.card ≤ alpha - (m + 1)) ∧
    (∀ G : LabeledGraph n,
      ((∃ P : ProfilePartition n kp, G ∈ partitionCocoloringEvent P.1) →
        cochromaticNumber G ≤ selectedBlockCount kv) ∧
      ((∃ P : ProfilePartition n kp, G ∈ partitionColoringEvent P.1) →
        chromaticNumberNat G ≤ selectedBlockCount kv)) := by
  intro u kp
  have hu_ge2 : ∀ j : Fin M, 2 ≤ u j ∧ u j ≤ alpha - (m + 1) := fun j ↦ by
    dsimp [u]; exact ⟨by omega, by omega⟩
  let idxOf : Fin M → Fin alpha := fun j ↦ ⟨u j - 1, by have := hu_ge2 j; omega⟩
  have hidx_inj : Function.Injective idxOf := by
    intro j₁ j₂ heq
    have hv := congrArg Fin.val heq
    dsimp [idxOf, u] at hv
    ext; omega
  have hcond_iff : ∀ (j : Fin M) (idx : Fin alpha),
      (u j = idx.1 + 1) ↔ idx = idxOf j := by
    intro j idx
    have hu2 := (hu_ge2 j).1
    constructor
    · intro h; ext; dsimp [idxOf]; omega
    · intro h; rw [h]; dsimp [idxOf]; omega
  have hkp_at : ∀ j : Fin M, kp (idxOf j) = kv j := by
    intro j
    dsimp [kp, embedWindowProfile_v13]
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
    dsimp [kp, embedWindowProfile_v13]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [if_neg]
    intro heq
    apply hnot
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ((hcond_iff j idx).mp heq).symm⟩
  -- General sum/prod reduction along `idxOf`
  have hsum_nat : ∀ f : ℕ → ℕ → ℕ, (∀ s, f s 0 = 0) →
      (∑ idx : Fin alpha, f (idx.1 + 1) (kp idx)) = ∑ j : Fin M, f (u j) (kv j) := by
    intro f hf0
    have hsub : (∑ idx ∈ Finset.univ.image idxOf, f (idx.1 + 1) (kp idx)) =
        ∑ idx : Fin alpha, f (idx.1 + 1) (kp idx) :=
      Finset.sum_subset (Finset.subset_univ _) fun idx _ hnot ↦ by
        rw [hkp_zero_outside idx hnot, hf0]
    rw [← hsub, Finset.sum_image (fun a _ b _ hab ↦ hidx_inj hab)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hu1 : (idxOf j).1 + 1 = u j := by dsimp [idxOf]; have := (hu_ge2 j).1; omega
    rw [hu1, hkp_at j]
  have hprod_nat : ∀ f : ℕ → ℕ → ℕ, (∀ s, f s 0 = 1) →
      (∏ idx : Fin alpha, f (idx.1 + 1) (kp idx)) = ∏ j : Fin M, f (u j) (kv j) := by
    intro f hf1
    have hsub : (∏ idx ∈ Finset.univ.image idxOf, f (idx.1 + 1) (kp idx)) =
        ∏ idx : Fin alpha, f (idx.1 + 1) (kp idx) :=
      Finset.prod_subset (Finset.subset_univ _) fun idx _ hnot ↦ by
        rw [hkp_zero_outside idx hnot, hf1]
    rw [← hsub, Finset.prod_image (fun a _ b _ hab ↦ hidx_inj hab)]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    have hu1 : (idxOf j).1 + 1 = u j := by dsimp [idxOf]; have := (hu_ge2 j).1; omega
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
  have hden_eq :
      ((∏ idx : Fin alpha, (Nat.factorial (idx.1 + 1)) ^ (kp idx)) *
          ∏ idx : Fin alpha, Nat.factorial (kp idx)) =
        partialProfileFactorialProduct u kv := by
    rw [hprod_nat (fun s c ↦ s.factorial ^ c) (fun _ ↦ pow_zero _),
      hprod_nat (fun _ c ↦ c.factorial) (fun _ ↦ Nat.factorial_zero)]
    unfold partialProfileFactorialProduct
    rw [Finset.prod_mul_distrib]
  -- Exact first-moment equalities
  have hexp_unmarked : (profileColoringExpectation n kp).toReal = completeUnmarkedFirstMoment u kv := by
    have hmul_id := ColoringProfile.enumerativeCoefficient_mul_coordinateDenominator_eq kp
    rw [mul_assoc, hmass_kp, hden_eq] at hmul_id
    have hexp_enn := profileColoringExpectation_eq_enumerativeCoefficient_mul_of n kp
      (profileEnumerationStatement n kp hmass_kp)
    rw [hexp_enn, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow]
    have hpf_pos : (0 : ℝ) < (partialProfileFactorialProduct u kv : ℝ) := by
      unfold partialProfileFactorialProduct
      exact_mod_cast Finset.prod_pos fun j _ ↦ mul_pos (pow_pos (Nat.factorial_pos _) _) (Nat.factorial_pos _)
    have hmul_R : (ColoringProfile.enumerativeCoefficient kp : ℝ) *
        (partialProfileFactorialProduct u kv : ℝ) = (n.factorial : ℝ) := by exact_mod_cast hmul_id
    have henum_R : (ColoringProfile.enumerativeCoefficient kp : ℝ) =
        (n.factorial : ℝ) / (partialProfileFactorialProduct u kv : ℝ) :=
      (eq_div_iff hpf_pos.ne').mpr hmul_R
    rw [henum_R, hforb_eq]
    unfold completeUnmarkedFirstMoment completeSignedFirstMoment residualVertexMass
      partialSignedFirstMoment selectedBlockCount
    rw [hMass, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_mul]
    have h2b_ne : (2 : ℝ) ^ (∑ j : Fin M, kv j) ≠ 0 := by positivity
    have h2e_ne : (2 : ℝ) ^ selectedInternalEdgeCount u kv ≠ 0 := by positivity
    have h12 : ((1 / 2 : ENNReal).toReal) = (2 : ℝ)⁻¹ := by norm_num
    rw [h12, inv_pow]
    field_simp [hpf_pos.ne', h2b_ne, h2e_ne]
  have hexp_signed : (signedProfileExpectation n kp).toReal = completeSignedFirstMoment u kv := by
    rw [signedProfileExpectation_eq, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      hpart_eq, hexp_unmarked]
    unfold completeUnmarkedFirstMoment selectedBlockCount
    have h2b_ne : (2 : ℝ) ^ (∑ j : Fin M, kv j) ≠ 0 := by positivity
    field_simp [h2b_ne]
  refine ⟨hkp_at, hpart_eq, hmass_kp, hforb_eq, hexp_unmarked, hexp_signed, ?_, ?_⟩
  · intro P
    refine ⟨P.card_parts_eq.trans hpart_eq, ?_⟩
    intro D hD
    have hmem_shape : D.card ∈ partitionShape P.1 := by
      unfold partitionShape
      exact Multiset.mem_map.mpr ⟨D, hD, rfl⟩
    rw [P.2] at hmem_shape
    have hmem_fin : D.card ∈ (ColoringProfile.sizes kp).toFinset :=
      Multiset.mem_toFinset.mpr hmem_shape
    rw [ColoringProfile.toFinset_sizes] at hmem_fin
    obtain ⟨idx, hidx_supp, hcard_eq⟩ := Finset.mem_image.mp hmem_fin
    have hkp_ne0 : kp idx ≠ 0 := by simpa [ColoringProfile.support] using hidx_supp
    have hidx_im : idx ∈ Finset.univ.image idxOf := by
      by_contra hnot; exact hkp_ne0 (hkp_zero_outside idx hnot)
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hidx_im
    have hu_eq : (idxOf j).1 + 1 = u j := by dsimp [idxOf]; have := (hu_ge2 j).1; omega
    rw [← hcard_eq, hu_eq]
    dsimp [u]
    exact ⟨by omega, by omega⟩
  · intro G
    classical
    refine ⟨?_, ?_⟩
    · rintro ⟨P, hGco⟩
      let σ : P.1.parts → Bool := fun B ↦ decide (G.IsClique (B.1 : Set (Fin n)))
      have hvalid : profileSignValid G P σ := by
        intro B
        dsimp [σ]
        by_cases hcl : G.IsClique (B.1 : Set (Fin n))
        · rw [decide_eq_true hcl]; exact hcl
        · rw [decide_eq_false hcl]
          rcases hGco B.1 B.2 with hind | hcl'
          · exact hind
          · exact (hcl hcl').elim
      have hco : CoColorable G (ColoringProfile.partCount kp) :=
        profileSignValid_coColorable P σ hvalid
      rw [hpart_eq] at hco
      exact (coColorable_iff_cochromaticNumber_le G).mp hco
    · rintro ⟨P, hGcol⟩
      -- Construct proper `Coloring G (Fin (selectedBlockCount kv))` directly from `P`
      have hcard_P : P.1.parts.card = selectedBlockCount kv := P.card_parts_eq.trans hpart_eq
      let e := Finset.equivFinOfCardEq hcard_P
      let col : G.Coloring (Fin (selectedBlockCount kv)) :=
        SimpleGraph.Coloring.mk
          (fun v ↦ e ⟨P.1.part v, P.1.part_mem.mpr (Finset.mem_univ v)⟩)
          (by
            intro v w hadj heq
            have hsub_eq : P.1.part v = P.1.part w := congrArg Subtype.val (e.injective heq)
            have hw_in : w ∈ P.1.part v := by
              rw [hsub_eq]; exact P.1.mem_part (Finset.mem_univ w)
            have hv_in : v ∈ P.1.part v := P.1.mem_part (Finset.mem_univ v)
            have hind := hGcol (P.1.part v) (P.1.part_mem.mpr (Finset.mem_univ v))
            exact hind hv_in hw_in (G.ne_of_adj hadj) hadj)
      exact ENat.toNat_le_of_le_coe (G.chromaticNumber_le_iff_colorable.mpr ⟨col⟩)

private theorem abs_mul_log_sub_le_of_mem_Icc_v13
    {c_lo x y : ℝ} (hc : 0 < c_lo)
    (hx : x ∈ Set.Icc c_lo 1) (hy : y ∈ Set.Icc c_lo 1) :
    |x * Real.log x - y * Real.log y| ≤ (1 + |Real.log c_lo|) * |x - y| := by
  have hd : ∀ t ∈ Set.Icc c_lo 1, HasDerivAt (fun u : ℝ ↦ u * Real.log u) (1 + Real.log t) t := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le hc ht.1
    exact ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht_pos.ne')).congr_deriv (by
      dsimp; rw [mul_inv_cancel₀ ht_pos.ne']; ring)
  have hnorm : ∀ t ∈ Set.Icc c_lo 1, ‖1 + Real.log t‖ ≤ 1 + |Real.log c_lo| := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le hc ht.1
    have hlog_lo : Real.log c_lo ≤ Real.log t := Real.log_le_log hc ht.1
    have hlog_hi : Real.log t ≤ 0 := Real.log_nonpos ht_pos.le ht.2
    rw [Real.norm_eq_abs, abs_le]
    have habs_c := abs_le.mp (le_rfl : |Real.log c_lo| ≤ |Real.log c_lo|)
    exact ⟨by linarith [habs_c.1], by linarith [habs_c.2]⟩
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u : ℝ ↦ u * Real.log u)
    (fun t ht ↦ (hd t ht).hasDerivWithinAt)
    hnorm (convex_Icc c_lo 1) hy hx
  simpa only [Real.norm_eq_abs] using hmvt

private theorem log_completeUnmarkedFirstMoment_ge_of_integer_approx_v13
    {n alpha m M k : ℕ} (hm : m ≤ 1) (hM : 7 ≤ M)
    (hn : 1 ≤ n) (halpha : 4 * (1 + M) ^ 2 ≤ alpha) (hk_pos : 1 ≤ k)
    {c_lo B_err : ℝ} (hc_lo : 0 < c_lo)
    {p_opt : ℕ → ℝ} {kv : Fin M → ℕ}
    (hp_sum : ∑ i ∈ Finset.Icc (m + 1) (m + M), p_opt i = 1)
    (hp_lo : ∀ i ∈ Finset.Icc (m + 1) (m + M), c_lo ≤ p_opt i)
    (hkv_props : ∀ j : Fin M,
      0 < kv j ∧ c_lo ≤ (kv j : ℝ) / (k : ℝ) ∧
        |(kv j : ℝ) / (k : ℝ) - p_opt (m + 1 + j.1)| ≤ B_err / (k : ℝ))
    (hblock_eq : selectedBlockCount kv = k)
    (hmass_eq : selectedVertexMass (fun j : Fin M ↦ alpha - (m + 1 + j.1)) kv = n) :
    let W := Finset.Icc (m + 1) (m + M)
    let h_sc : ℕ → ℝ := fun i ↦
      Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) -
        Real.log 2 / 2 * (i : ℝ) ^ 2
    let u : Fin M → ℕ := fun j ↦ alpha - (m + 1 + j.1)
    let B_sc : ℝ := ((1 + M : ℕ) : ℝ) ^ 2 + 1
    let C_round : ℝ := (M : ℝ) * ((1 + |Real.log c_lo|) * B_err + B_sc * B_err)
    (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (k : ℝ) - (k : ℝ) * Real.log (k : ℝ) +
        (k : ℝ) * (profileDeficitAffineA alpha +
          profileDeficitAffineB alpha * fourSizeTarget n alpha (k : ℝ) +
          (-(∑ i ∈ W, p_opt i * Real.log (p_opt i)) + ∑ i ∈ W, p_opt i * h_sc i)) -
        C_round - (M : ℝ) * Real.log (Real.exp 1 * ((n : ℝ) + 1)) ≤
      Real.log (completeUnmarkedFirstMoment u kv) := by
  intro W h_sc u B_sc C_round
  have hkR_gt0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have ha_ge_self : 1 + M ≤ (1 + M) ^ 2 := Nat.le_self_pow (by norm_num) (1 + M)
  have hbij_W_R : ∀ f : ℕ → ℝ, ∑ j : Fin M, f (m + 1 + j.1) = ∑ i ∈ W, f i := by
    intro f
    refine Finset.sum_bij (fun (j : Fin M) _ ↦ m + 1 + j.1) ?_ ?_ ?_ (fun _ _ ↦ rfl)
    · intro j _; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a _ b _ h; ext; omega
    · intro i hi
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
      exact ⟨⟨i - (m + 1), by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
  have hpf_pos : (0 : ℝ) < (partialProfileFactorialProduct u kv : ℝ) := by
    unfold partialProfileFactorialProduct
    exact_mod_cast Finset.prod_pos fun j _ ↦ mul_pos (pow_pos (Nat.factorial_pos _) _) (Nat.factorial_pos _)
  have hlog_unm :
      Real.log (completeUnmarkedFirstMoment u kv) =
        Real.log (n.factorial : ℝ) -
          ∑ j : Fin M,
            ((kv j : ℝ) * Real.log ((u j).factorial : ℝ) +
              Real.log ((kv j).factorial : ℝ) +
              (kv j : ℝ) * (((u j).choose 2 : ℝ) * Real.log 2)) := by
    unfold completeUnmarkedFirstMoment completeSignedFirstMoment residualVertexMass
      partialSignedFirstMoment selectedBlockCount
    rw [hmass_eq, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_mul]
    have h2b_pos : (0 : ℝ) < (2 : ℝ) ^ (∑ j : Fin M, kv j) := by positivity
    have hnf_pos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have h2e_pos : (0 : ℝ) < (2 : ℝ) ^ selectedInternalEdgeCount u kv := by positivity
    have hsimp :
        ((2 : ℝ) ^ (∑ j : Fin M, kv j))⁻¹ *
            ((2 : ℝ) ^ (∑ j : Fin M, kv j) * (n.factorial : ℝ) /
              ((partialProfileFactorialProduct u kv : ℝ) *
                (2 : ℝ) ^ selectedInternalEdgeCount u kv)) =
          (n.factorial : ℝ) /
            ((partialProfileFactorialProduct u kv : ℝ) *
              (2 : ℝ) ^ selectedInternalEdgeCount u kv) := by
      field_simp [h2b_pos.ne', hpf_pos.ne', h2e_pos.ne']
    rw [hsimp, Real.log_div hnf_pos.ne' (mul_pos hpf_pos h2e_pos).ne',
      Real.log_mul hpf_pos.ne' h2e_pos.ne', Real.log_pow]
    unfold partialProfileFactorialProduct selectedInternalEdgeCount
    rw [Nat.cast_prod, Real.log_prod (fun j _ ↦ by
      exact_mod_cast (mul_pos (pow_pos (Nat.factorial_pos _) _) (Nat.factorial_pos _)).ne'),
      Nat.cast_sum, Finset.sum_mul]
    have hpt : ∀ j : Fin M,
        Real.log ((((u j).factorial ^ kv j * (kv j).factorial : ℕ) : ℝ)) +
            (((u j).choose 2 * kv j : ℕ) : ℝ) * Real.log 2 =
          (kv j : ℝ) * Real.log ((u j).factorial : ℝ) +
            Real.log ((kv j).factorial : ℝ) +
            (kv j : ℝ) * (((u j).choose 2 : ℝ) * Real.log 2) := by
      intro j
      rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity), Nat.cast_pow, Real.log_pow,
        Nat.cast_mul]
      ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun j _ ↦ hpt j]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog_nf_ge : (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) ≤ Real.log (n.factorial : ℝ) := by
    have hlow := pow_mul_exp_neg_le_factorial n
    have hlog := Real.log_le_log (by positivity) hlow
    rw [Real.log_mul (pow_pos hn_pos n).ne' (Real.exp_pos _).ne', Real.log_pow, Real.log_exp] at hlog
    linarith
  have hlog_kv_le : ∀ j : Fin M,
      Real.log ((kv j).factorial : ℝ) ≤
        (kv j : ℝ) * Real.log (kv j : ℝ) - (kv j : ℝ) + Real.log (Real.exp 1 * ((n : ℝ) + 1)) := by
    intro j
    have hpos_j := (hkv_props j).1
    have hjR_pos : (0 : ℝ) < (kv j : ℝ) := by exact_mod_cast hpos_j
    have hkv_le_n : kv j ≤ n := by
      have hu_pos : 1 ≤ u j := by dsimp [u]; omega
      calc kv j = 1 * kv j := (Nat.one_mul _).symm
        _ ≤ u j * kv j := Nat.mul_le_mul_right (kv j) hu_pos
        _ ≤ selectedVertexMass u kv :=
            Finset.single_le_sum (f := fun i ↦ u i * kv i) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
        _ = n := hmass_eq
    have hup := factorial_le_exp_mul_succ_mul_pow_mul_exp_neg (kv j)
    have hlog := Real.log_le_log (by exact_mod_cast Nat.factorial_pos _) hup
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_mul (by positivity) (pow_pos hjR_pos _).ne',
      Real.log_pow, Real.log_exp] at hlog
    have hmono : Real.log (Real.exp 1 * ((kv j : ℝ) + 1)) ≤ Real.log (Real.exp 1 * ((n : ℝ) + 1)) :=
      Real.log_le_log (by positivity)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hkv_le_n 1) (Real.exp_pos 1).le)
    linarith
  have hcost_j : ∀ j : Fin M,
      -(Real.log ((u j).factorial : ℝ) + ((u j).choose 2 : ℝ) * Real.log 2) =
        profileDeficitAffineA alpha + profileDeficitAffineB alpha * ((m + 1 + j.1 : ℕ) : ℝ) +
          h_sc (m + 1 + j.1) := by
    intro j
    let j_ext : Fin (alpha + 1) := ⟨u j - 1, by dsimp [u]; omega⟩
    have hu1 : j_ext.1 + 1 = u j := by dsimp [j_ext, u]; omega
    have h1 := profileDualScore_eq_deficitAffine_add_residual alpha j_ext
    have hdef : profileDeficit alpha j_ext = ((m + 1 + j.1 : ℕ) : ℝ) := by
      unfold profileDeficit profileClassSize
      rw [hu1]; dsimp [u]
      rw [Nat.cast_sub (by omega : m + 1 + j.1 ≤ alpha)]
      ring
    have hres : profileDeficitResidualScore alpha j_ext = h_sc (m + 1 + j.1) := by
      rw [profileDeficitResidualScore_eq_descFactorial alpha j_ext (by dsimp [j_ext, u]; omega)]
      dsimp [j_ext, u, h_sc]
      have hd_eq : alpha - (alpha - (m + 1 + j.1) - 1 + 1) = m + 1 + j.1 := by omega
      rw [hd_eq]; unfold q; rfl
    have hscore_lhs : profileDualScore j_ext =
        -(Real.log ((u j).factorial : ℝ) + ((u j).choose 2 : ℝ) * Real.log 2) := by
      unfold profileDualScore coloringClassLogCost
      rw [hu1]
    rw [← hscore_lhs, h1, hdef, hres]
  have hsum_kv_R : ∑ j : Fin M, (kv j : ℝ) = (k : ℝ) := by
    rw [← Nat.cast_sum]; exact_mod_cast hblock_eq
  have hsum_def_kv : ∑ j : Fin M, (kv j : ℝ) * ((m + 1 + j.1 : ℕ) : ℝ) =
      (k : ℝ) * fourSizeTarget n alpha (k : ℝ) := by
    have hpt : ∀ j : Fin M, (kv j : ℝ) * ((m + 1 + j.1 : ℕ) : ℝ) =
        (alpha : ℝ) * (kv j : ℝ) - ((u j * kv j : ℕ) : ℝ) := by
      intro j
      dsimp [u]
      rw [Nat.cast_mul, Nat.cast_sub (by omega : m + 1 + j.1 ≤ alpha)]
      ring
    rw [Finset.sum_congr rfl fun j _ ↦ hpt j, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hsum_kv_R, ← Nat.cast_sum, show (∑ j : Fin M, u j * kv j) = selectedVertexMass u kv from rfl,
      hmass_eq]
    unfold fourSizeTarget
    field_simp [hkR_gt0.ne']
  have hL_kv_ge :
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (k : ℝ) - (k : ℝ) * Real.log (k : ℝ) +
          (k : ℝ) * (profileDeficitAffineA alpha +
            profileDeficitAffineB alpha * fourSizeTarget n alpha (k : ℝ)) +
          (k : ℝ) * (∑ j : Fin M,
            (-((kv j : ℝ) / (k : ℝ)) * Real.log ((kv j : ℝ) / (k : ℝ)) +
              ((kv j : ℝ) / (k : ℝ)) * h_sc (m + 1 + j.1))) -
          (M : ℝ) * Real.log (Real.exp 1 * ((n : ℝ) + 1)) ≤
        Real.log (completeUnmarkedFirstMoment u kv) := by
    rw [hlog_unm]
    have hlog_div_j : ∀ j : Fin M,
        (kv j : ℝ) * Real.log (kv j : ℝ) =
          (kv j : ℝ) * Real.log (k : ℝ) +
            (k : ℝ) * (((kv j : ℝ) / (k : ℝ)) * Real.log ((kv j : ℝ) / (k : ℝ))) := by
      intro j
      have hj_pos : (0 : ℝ) < (kv j : ℝ) := by exact_mod_cast (hkv_props j).1
      rw [Real.log_div hj_pos.ne' hkR_gt0.ne']
      field_simp [hkR_gt0.ne']; ring
    have hmain_id :
        ∑ j : Fin M,
            ((kv j : ℝ) * Real.log ((u j).factorial : ℝ) +
              ((kv j : ℝ) * Real.log (kv j : ℝ) - (kv j : ℝ) +
                Real.log (Real.exp 1 * ((n : ℝ) + 1))) +
              (kv j : ℝ) * (((u j).choose 2 : ℝ) * Real.log 2)) =
          -(k : ℝ) + (k : ℝ) * Real.log (k : ℝ) -
            (k : ℝ) * (profileDeficitAffineA alpha +
              profileDeficitAffineB alpha * fourSizeTarget n alpha (k : ℝ)) -
            (k : ℝ) * (∑ j : Fin M,
              (-((kv j : ℝ) / (k : ℝ)) * Real.log ((kv j : ℝ) / (k : ℝ)) +
                ((kv j : ℝ) / (k : ℝ)) * h_sc (m + 1 + j.1))) +
            (M : ℝ) * Real.log (Real.exp 1 * ((n : ℝ) + 1)) := by
      have hterm_id : ∀ j : Fin M,
          (kv j : ℝ) * Real.log ((u j).factorial : ℝ) +
              ((kv j : ℝ) * Real.log (kv j : ℝ) - (kv j : ℝ) +
                Real.log (Real.exp 1 * ((n : ℝ) + 1))) +
              (kv j : ℝ) * (((u j).choose 2 : ℝ) * Real.log 2) =
            -(kv j : ℝ) + (kv j : ℝ) * Real.log (k : ℝ) -
              (kv j : ℝ) * profileDeficitAffineA alpha -
              profileDeficitAffineB alpha * ((kv j : ℝ) * ((m + 1 + j.1 : ℕ) : ℝ)) -
              (k : ℝ) * (-((kv j : ℝ) / (k : ℝ)) * Real.log ((kv j : ℝ) / (k : ℝ)) +
                ((kv j : ℝ) / (k : ℝ)) * h_sc (m + 1 + j.1)) +
              Real.log (Real.exp 1 * ((n : ℝ) + 1)) := by
        intro j
        have hc := hcost_j j
        have hl := hlog_div_j j
        rw [hl]
        have hkh : (k : ℝ) * (((kv j : ℝ) / (k : ℝ)) * h_sc (m + 1 + j.1)) =
            (kv j : ℝ) * h_sc (m + 1 + j.1) := by field_simp [hkR_gt0.ne']
        linarith [congrArg ((kv j : ℝ) * ·) hc, hkh]
      rw [Finset.sum_congr rfl fun j _ ↦ hterm_id j,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
        ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        hsum_kv_R, hsum_def_kv]
      ring
    have hsum_tot :
        ∑ j : Fin M,
            ((kv j : ℝ) * Real.log ((u j).factorial : ℝ) +
              Real.log ((kv j).factorial : ℝ) +
              (kv j : ℝ) * (((u j).choose 2 : ℝ) * Real.log 2)) ≤
          ∑ j : Fin M,
            ((kv j : ℝ) * Real.log ((u j).factorial : ℝ) +
              ((kv j : ℝ) * Real.log (kv j : ℝ) - (kv j : ℝ) +
                Real.log (Real.exp 1 * ((n : ℝ) + 1))) +
              (kv j : ℝ) * (((u j).choose 2 : ℝ) * Real.log 2)) :=
      Finset.sum_le_sum fun j _ ↦ by linarith [hlog_kv_le j]
    linarith [hlog_nf_ge, hsum_tot, hmain_id]
  have hround_diff :
      |(k : ℝ) * (∑ j : Fin M,
          (-((kv j : ℝ) / (k : ℝ)) * Real.log ((kv j : ℝ) / (k : ℝ)) +
             ((kv j : ℝ) / (k : ℝ)) * h_sc (m + 1 + j.1))) -
        (k : ℝ) * (-(∑ i ∈ W, p_opt i * Real.log (p_opt i)) +
          ∑ i ∈ W, p_opt i * h_sc i)| ≤ C_round := by
    have hrhs_bij :
        -(∑ i ∈ W, p_opt i * Real.log (p_opt i)) + ∑ i ∈ W, p_opt i * h_sc i =
          ∑ j : Fin M,
            (-p_opt (m + 1 + j.1) * Real.log (p_opt (m + 1 + j.1)) +
              p_opt (m + 1 + j.1) * h_sc (m + 1 + j.1)) := by
      rw [← hbij_W_R (fun i ↦ p_opt i * Real.log (p_opt i)),
        ← hbij_W_R (fun i ↦ p_opt i * h_sc i), ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hrhs_bij, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos hkR_gt0]
    have ha_pos : (0 : ℝ) < (alpha : ℝ) := by exact_mod_cast (show 0 < alpha by omega)
    have ha_ge_sq : ((1 + M : ℕ) : ℝ) ^ 2 ≤ (alpha : ℝ) := by
      have h4 : 4 * ((1 + M : ℕ) : ℝ) ^ 2 ≤ (alpha : ℝ) := by exact_mod_cast halpha
      linarith [sq_nonneg ((1 + M : ℕ) : ℝ)]
    have hcoord : ∀ j : Fin M,
        |(-((kv j : ℝ) / (k : ℝ)) * Real.log ((kv j : ℝ) / (k : ℝ)) +
              ((kv j : ℝ) / (k : ℝ)) * h_sc (m + 1 + j.1)) -
            (-p_opt (m + 1 + j.1) * Real.log (p_opt (m + 1 + j.1)) +
              p_opt (m + 1 + j.1) * h_sc (m + 1 + j.1))| ≤
          ((1 + |Real.log c_lo|) * B_err + B_sc * B_err) / (k : ℝ) := by
      intro j
      set qj : ℝ := (kv j : ℝ) / (k : ℝ)
      set pj : ℝ := p_opt (m + 1 + j.1)
      have hjW : m + 1 + j.1 ∈ W := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hqj_icc : qj ∈ Set.Icc c_lo 1 := by
        refine ⟨(hkv_props j).2.1, (div_le_one hkR_gt0).mpr ?_⟩
        have : kv j ≤ selectedBlockCount kv :=
          Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
        rw [hblock_eq] at this; exact_mod_cast this
      have hpj_icc : pj ∈ Set.Icc c_lo 1 := by
        refine ⟨hp_lo _ hjW, ?_⟩
        rw [← hp_sum]
        exact Finset.single_le_sum (fun i hi ↦ le_trans hc_lo.le (hp_lo i hi)) hjW
      have hent_j := abs_mul_log_sub_le_of_mem_Icc_v13 hc_lo hqj_icc hpj_icc
      have hsc_abs : |h_sc (m + 1 + j.1)| ≤ B_sc := by
        have hi_lt : m + 1 + j.1 < alpha := by omega
        have h2i : 2 * (m + 1 + j.1) ≤ alpha := by omega
        obtain ⟨hid, hle0, hge⟩ := finiteDeficitResidualScore_bounds hi_lt
        dsimp [h_sc]; rw [hid]
        have hsq : ((m + 1 + j.1 : ℕ) : ℝ) ^ 2 ≤ ((1 + M : ℕ) : ℝ) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (show m + 1 + j.1 ≤ 1 + M by omega)) 2
        have hdiv : (-1 : ℝ) ≤ -((m + 1 + j.1 : ℕ) : ℝ) ^ 2 / (alpha : ℝ) := by
          have h1 : ((m + 1 + j.1 : ℕ) : ℝ) ^ 2 / (alpha : ℝ) ≤ 1 :=
            (div_le_one ha_pos).mpr (hsq.trans ha_ge_sq)
          rw [neg_div]; linarith
        have hq_i : (Real.log 2 / 2) * ((m + 1 + j.1 : ℕ) : ℝ) ^ 2 ≤ 1 * ((1 + M : ℕ) : ℝ) ^ 2 :=
          mul_le_mul (by linarith [Real.log_two_lt_d9]) hsq (sq_nonneg _) zero_le_one
        have hq_nn : 0 ≤ (Real.log 2 / 2) * ((m + 1 + j.1 : ℕ) : ℝ) ^ 2 :=
          mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le zero_le_two) (sq_nonneg _)
        rw [abs_le]; dsimp [B_sc]
        exact ⟨by linarith [hdiv.trans (hge h2i)], by linarith⟩
      have herr_j := (hkv_props j).2.2
      have hrew_j :
          (-qj * Real.log qj + qj * h_sc (m + 1 + j.1)) -
              (-pj * Real.log pj + pj * h_sc (m + 1 + j.1)) =
            -(qj * Real.log qj - pj * Real.log pj) + (qj - pj) * h_sc (m + 1 + j.1) := by ring
      rw [hrew_j]
      calc |-(qj * Real.log qj - pj * Real.log pj) + (qj - pj) * h_sc (m + 1 + j.1)|
          ≤ |-(qj * Real.log qj - pj * Real.log pj)| + |(qj - pj) * h_sc (m + 1 + j.1)| :=
            abs_add_le _ _
        _ = |qj * Real.log qj - pj * Real.log pj| + |qj - pj| * |h_sc (m + 1 + j.1)| := by
            rw [abs_neg, abs_mul]
        _ ≤ (1 + |Real.log c_lo|) * (B_err / (k : ℝ)) + (B_err / (k : ℝ)) * B_sc := by
            refine add_le_add
              (hent_j.trans (mul_le_mul_of_nonneg_left herr_j (by positivity)))
              (mul_le_mul herr_j hsc_abs (abs_nonneg _)
                (le_trans (abs_nonneg _) herr_j))
        _ = ((1 + |Real.log c_lo|) * B_err + B_sc * B_err) / (k : ℝ) := by ring
    have hsum_le :
        (∑ j : Fin M,
          |(-((kv j : ℝ) / (k : ℝ)) * Real.log ((kv j : ℝ) / (k : ℝ)) +
                ((kv j : ℝ) / (k : ℝ)) * h_sc (m + 1 + j.1)) -
              (-p_opt (m + 1 + j.1) * Real.log (p_opt (m + 1 + j.1)) +
                p_opt (m + 1 + j.1) * h_sc (m + 1 + j.1))|) ≤
          (M : ℝ) * (((1 + |Real.log c_lo|) * B_err + B_sc * B_err) / (k : ℝ)) := by
      calc _ ≤ ∑ _j : Fin M, (((1 + |Real.log c_lo|) * B_err + B_sc * B_err) / (k : ℝ)) :=
              Finset.sum_le_sum fun j _ ↦ hcoord j
        _ = (M : ℝ) * (((1 + |Real.log c_lo|) * B_err + B_sc * B_err) / (k : ℝ)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc (k : ℝ) * |∑ j : Fin M, _|
        ≤ (k : ℝ) * ∑ j : Fin M, |_| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hkR_gt0.le
      _ ≤ (k : ℝ) * ((M : ℝ) * (((1 + |Real.log c_lo|) * B_err + B_sc * B_err) / (k : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum_le hkR_gt0.le
      _ = C_round := by dsimp [C_round]; field_simp [hkR_gt0.ne']
  linarith [hL_kv_ge, (abs_le.mp hround_diff).1]

private theorem roundedWindowProfile_unmarked_v13
    {n alpha m M k : ℕ} (hm : m ≤ 1) (hM : 7 ≤ M)
    (hn : 1 ≤ n) (halpha : 4 * (1 + M) ^ 2 ≤ alpha)
    {c_lo : ℝ} (hc_lo : 0 < c_lo)
    {p_opt : ℕ → ℝ}
    (hp_sum : ∑ i ∈ Finset.Icc (m + 1) (m + M), p_opt i = 1)
    (hp_mean : ∑ i ∈ Finset.Icc (m + 1) (m + M), (i : ℝ) * p_opt i =
      (alpha : ℝ) - (n : ℝ) / (k : ℝ))
    (hp_lo : ∀ i ∈ Finset.Icc (m + 1) (m + M), 2 * c_lo ≤ p_opt i)
    (hk_big : (((m + M + 4) * M + 1 : ℕ) : ℝ) / c_lo + 1 ≤ (k : ℝ)) :
    let W := Finset.Icc (m + 1) (m + M)
    let h_sc : ℕ → ℝ := fun i ↦
      Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) -
        Real.log 2 / 2 * (i : ℝ) ^ 2
    let u : Fin M → ℕ := fun j ↦ alpha - (m + 1 + j.1)
    let kv : Fin M → ℕ := fun j ↦ (roundedWindowProfile m M alpha k n p_opt (m + 1 + j.1)).toNat
    let B_err : ℝ := (((m + M + 4) * M + 1 : ℕ) : ℝ)
    let B_sc : ℝ := ((1 + M : ℕ) : ℝ) ^ 2 + 1
    let C_round : ℝ := (M : ℝ) * ((1 + |Real.log c_lo|) * B_err + B_sc * B_err)
    (∀ j : Fin M, 0 < kv j ∧ c_lo ≤ (kv j : ℝ) / (k : ℝ) ∧
      |(kv j : ℝ) / (k : ℝ) - p_opt (m + 1 + j.1)| ≤ B_err / (k : ℝ)) ∧
    selectedBlockCount kv = k ∧
    selectedVertexMass u kv = n ∧
    (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (k : ℝ) - (k : ℝ) * Real.log (k : ℝ) +
        (k : ℝ) * (profileDeficitAffineA alpha +
          profileDeficitAffineB alpha * fourSizeTarget n alpha (k : ℝ) +
          (-(∑ i ∈ W, p_opt i * Real.log (p_opt i)) + ∑ i ∈ W, p_opt i * h_sc i)) -
        C_round - (M : ℝ) * Real.log (Real.exp 1 * ((n : ℝ) + 1)) ≤
      Real.log (completeUnmarkedFirstMoment u kv) := by
  intro W h_sc u kv B_err B_sc C_round
  have hk_pos_R : (1 : ℝ) ≤ (k : ℝ) := by
    have : 0 ≤ B_err / c_lo := by dsimp [B_err]; positivity
    linarith
  have hk_pos : 1 ≤ k := by exact_mod_cast hk_pos_R
  have hkR_gt0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hk_pos_R
  obtain ⟨hsum_k_int, hsum_n_int, herr_int⟩ :=
    roundedWindowProfile_conservation_and_error hm (by omega : 4 ≤ M) hk_pos hp_sum hp_mean
  have hk_mul_c1 : B_err + c_lo ≤ c_lo * (k : ℝ) := by
    have hm_c := mul_le_mul_of_nonneg_left hk_big hc_lo.le
    rw [mul_add, mul_div_cancel₀ _ hc_lo.ne', mul_one] at hm_c
    linarith only [hm_c]
  have hk_mul_c : B_err ≤ c_lo * (k : ℝ) := by linarith only [hk_mul_c1, hc_lo]
  have hZ_pos : ∀ i ∈ W, 1 ≤ roundedWindowProfile m M alpha k n p_opt i := by
    intro i hi
    have herr_i := (abs_le.mp (herr_int i hi)).1
    have hp_i := hp_lo i hi
    have hkp_ge : 2 * B_err + c_lo ≤ (k : ℝ) * p_opt i := by
      have hm_k := mul_le_mul_of_nonneg_left hp_i hkR_gt0.le
      have heq2 : (k : ℝ) * (2 * c_lo) = 2 * (c_lo * (k : ℝ)) := by ring
      linarith only [hm_k, hk_mul_c1, hc_lo, heq2]
    have hB_ge1 : (1 : ℝ) ≤ B_err := by
      dsimp [B_err]; exact_mod_cast (show 1 ≤ (m + M + 4) * M + 1 by omega)
    have hR_gt0 : (0 : ℝ) < (roundedWindowProfile m M alpha k n p_opt i : ℝ) := by linarith
    have hI_gt0 : (0 : ℤ) < roundedWindowProfile m M alpha k n p_opt i := by exact_mod_cast hR_gt0
    omega
  have hkv_cast_int : ∀ j : Fin M,
      (kv j : ℤ) = roundedWindowProfile m M alpha k n p_opt (m + 1 + j.1) := by
    intro j
    have hjW : m + 1 + j.1 ∈ W := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have h1 := hZ_pos (m + 1 + j.1) hjW
    dsimp [kv]
    exact Int.toNat_of_nonneg (by omega)
  have hkv_props : ∀ j : Fin M,
      0 < kv j ∧ c_lo ≤ (kv j : ℝ) / (k : ℝ) ∧
        |(kv j : ℝ) / (k : ℝ) - p_opt (m + 1 + j.1)| ≤ B_err / (k : ℝ) := by
    intro j
    have hjW : m + 1 + j.1 ∈ W := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have _ := hZ_pos (m + 1 + j.1) hjW
    have hpos_j : 0 < kv j := by have hIj := hkv_cast_int j; omega
    have hkv_R : (kv j : ℝ) = (roundedWindowProfile m M alpha k n p_opt (m + 1 + j.1) : ℝ) := by
      exact_mod_cast hkv_cast_int j
    have hdiff_R : |(kv j : ℝ) / (k : ℝ) - p_opt (m + 1 + j.1)| ≤ B_err / (k : ℝ) := by
      have hrew : (kv j : ℝ) / (k : ℝ) - p_opt (m + 1 + j.1) =
          ((kv j : ℝ) - (k : ℝ) * p_opt (m + 1 + j.1)) / (k : ℝ) := by
        field_simp [hkR_gt0.ne']
      rw [hrew, abs_div, abs_of_pos hkR_gt0, hkv_R]
      exact div_le_div_of_nonneg_right (herr_int _ hjW) hkR_gt0.le
    have hdiv_c : B_err / (k : ℝ) ≤ c_lo := (div_le_iff₀ hkR_gt0).mpr hk_mul_c
    have hp_j := hp_lo _ hjW
    exact ⟨hpos_j, by linarith [(abs_le.mp hdiff_R).1], hdiff_R⟩
  have hbij_W : ∀ f : ℕ → ℤ, ∑ j : Fin M, f (m + 1 + j.1) = ∑ i ∈ W, f i := by
    intro f
    refine Finset.sum_bij (fun (j : Fin M) _ ↦ m + 1 + j.1) ?_ ?_ ?_ (fun _ _ ↦ rfl)
    · intro j _; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a _ b _ h; ext; omega
    · intro i hi
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
      exact ⟨⟨i - (m + 1), by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
  have hblock_eq : selectedBlockCount kv = k := by
    have hI : (selectedBlockCount kv : ℤ) = (k : ℤ) := by
      unfold selectedBlockCount
      rw [Nat.cast_sum]
      simp_rw [hkv_cast_int]
      rw [hbij_W]
      exact hsum_k_int
    exact_mod_cast hI
  have hmass_eq : selectedVertexMass u kv = n := by
    have ha_ge_self : 1 + M ≤ (1 + M) ^ 2 := Nat.le_self_pow (by norm_num) (1 + M)
    have hI : (selectedVertexMass u kv : ℤ) = (n : ℤ) := by
      unfold selectedVertexMass
      rw [Nat.cast_sum]
      have hterm : ∀ j : Fin M,
          ((u j * kv j : ℕ) : ℤ) =
            ((alpha : ℤ) - ((m + 1 + j.1 : ℕ) : ℤ)) *
              roundedWindowProfile m M alpha k n p_opt (m + 1 + j.1) := by
        intro j
        rw [Nat.cast_mul, hkv_cast_int j]
        congr 1
        dsimp [u]
        exact Int.ofNat_sub (by omega)
      simp_rw [hterm]
      rw [hbij_W (fun i ↦ ((alpha : ℤ) - (i : ℤ)) * roundedWindowProfile m M alpha k n p_opt i)]
      exact hsum_n_int
    exact_mod_cast hI
  exact ⟨hkv_props, hblock_eq, hmass_eq,
    log_completeUnmarkedFirstMoment_ge_of_integer_approx_v13 hm hM hn halpha hk_pos hc_lo
      hp_sum (fun i hi ↦ by linarith [hp_lo i hi]) hkv_props hblock_eq hmass_eq⟩

private theorem wProb_and_wMean_shift_S0M_v13
    {m M : ℕ} (hM : 1 ≤ M) (l : ℝ) :
    let W := Finset.Icc (m + 1) (m + M)
    let g_sc : ℕ → ℝ := fun i ↦ -Real.log 2 / 2 * (i : ℝ) ^ 2
    let l' : ℝ := l - (m : ℝ) * Real.log 2
    (∀ j : Fin M, wProb_v13 W g_sc l (m + 1 + j.1) = gibbsProbS0M M l' ((j.1 : ℤ) + 1)) ∧
      wMean_v13 W g_sc l = meanS0M M l' + (m : ℝ) := by
  intro W g_sc l'
  set S_pref : ℝ := Real.exp (l * (m : ℝ) - Real.log 2 / 2 * (m : ℝ) ^ 2)
  have hS_pos : 0 < S_pref := Real.exp_pos _
  have hZM_pos := partitionFn_S0M_pos hM l'
  have hbij_W : ∀ f : ℕ → ℝ, ∑ i ∈ W, f i = ∑ j : Fin M, f (m + 1 + j.1) := by
    intro f; symm
    refine Finset.sum_bij (fun (j : Fin M) _ ↦ m + 1 + j.1) ?_ ?_ ?_ (fun _ _ ↦ rfl)
    · intro j _; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a _ b _ h; ext; omega
    · intro i hi
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
      exact ⟨⟨i - (m + 1), by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
  have hbij_F : ∀ f : ℤ → ℝ, ∑ i ∈ F0M M, f i = ∑ j : Fin M, f ((j.1 : ℤ) + 1) := by
    intro f; symm
    refine Finset.sum_bij (fun (j : Fin M) _ ↦ (j.1 : ℤ) + 1) ?_ ?_ ?_ (fun _ _ ↦ rfl)
    · intro j _; rw [F0M, Finset.mem_Icc]; exact ⟨by omega, by omega⟩
    · intro a _ b _ hab; exact Fin.ext (by omega)
    · intro i hi; rw [F0M, Finset.mem_Icc] at hi
      exact ⟨⟨(i - 1).toNat, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
  have hwt_j : ∀ j : Fin M,
      Real.exp (l * ((m + 1 + j.1 : ℕ) : ℝ) + g_sc (m + 1 + j.1)) =
        S_pref * gaussWeight l' ((j.1 : ℤ) + 1) := by
    intro j
    dsimp [S_pref, g_sc, l']
    unfold gaussWeight
    rw [← Real.exp_add]
    congr 1
    push_cast; ring
  have hpart_eq : wPart_v13 W g_sc l = S_pref * partitionFn (S0M M) l' := by
    unfold wPart_v13
    rw [hbij_W, Finset.sum_congr rfl fun j _ ↦ hwt_j j, ← Finset.mul_sum,
      partitionFn_S0M_eq_sum, hbij_F]
  have hprob_eq : ∀ j : Fin M,
      wProb_v13 W g_sc l (m + 1 + j.1) = gibbsProbS0M M l' ((j.1 : ℤ) + 1) := by
    intro j
    have hjW : m + 1 + j.1 ∈ W := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hjF : ((j.1 : ℤ) + 1) ∈ F0M M := by rw [F0M, Finset.mem_Icc]; omega
    simp only [wProb_v13, hjW, ↓reduceIte, gibbsProbS0M, hjF]
    rw [hwt_j j, hpart_eq, mul_div_mul_left _ _ hS_pos.ne']
  refine ⟨hprob_eq, ?_⟩
  rw [← sum_mul_wProb_v13, hbij_W]
  have hterm_m : ∀ j : Fin M,
      ((m + 1 + j.1 : ℕ) : ℝ) * wProb_v13 W g_sc l (m + 1 + j.1) =
        (((j.1 : ℤ) + 1 : ℤ) : ℝ) * gibbsProbS0M M l' ((j.1 : ℤ) + 1) +
          (m : ℝ) * gibbsProbS0M M l' ((j.1 : ℤ) + 1) := by
    intro j
    rw [hprob_eq j]
    push_cast; ring
  rw [Finset.sum_congr rfl fun j _ ↦ hterm_m j, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← hbij_F (fun i ↦ (i : ℝ) * gibbsProbS0M M l' i),
    ← hbij_F (fun i ↦ gibbsProbS0M M l' i),
    sum_mul_gibbsProbS0M, sum_gibbsProbS0M hM l', mul_one]

private theorem eventually_corridor_pad_and_root_bounds_v13 (C_corr : ℝ) (hC : 0 < C_corr) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ n ∧ 2 ≤ Real.log (n : ℝ) ∧ 1 ≤ Real.log (Real.log (n : ℝ)) ∧
      Real.log (n : ℝ) + 20 ≤ logLogOrder n * phaseRootGapRadius n ∧
      (∀ s ∈ Set.Icc
          (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n),
        phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar →
          fourSizeTarget n (phaseNat n) s ∈ KcapInterval) ∧
      ∀ r ∈ Set.Ioo
          (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n),
        let k_co : ℕ := Nat.ceil r + 16
        let k_ch : ℕ := Nat.ceil r + Nat.ceil (Real.log (n : ℝ))
        (n : ℝ) / (6 * Real.log (n : ℝ)) ≤ r ∧
        1 ≤ k_co ∧ (k_co : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ∧
        (n : ℝ) / (6 * Real.log (n : ℝ)) ≤ (k_co : ℝ) ∧
        r + 16 ≤ (k_co : ℝ) ∧
        (k_co : ℝ) ∈ Set.Icc
          (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n) ∧
        1 ≤ k_ch ∧ (k_ch : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ∧
        (n : ℝ) / (6 * Real.log (n : ℝ)) ≤ (k_ch : ℝ) ∧
        r + Real.log (n : ℝ) ≤ (k_ch : ℝ) ∧
        (k_ch : ℝ) ∈ Set.Icc
          (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n) ∧
        |(fourSizeTarget n (phaseNat n) (k_co : ℝ)) - phaseTarget (phaseDelta n)| ≤
          2 * (C_corr + 1) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) ∧
        |(fourSizeTarget n (phaseNat n) (k_ch : ℝ)) - phaseTarget (phaseDelta n)| ≤
          2 * (C_corr + 1) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
  have hC1 : 0 ≤ C_corr + 1 := by linarith
  have hL4_small : ∀ᶠ n : ℕ in atTop,
      192 * (Real.log (n : ℝ)) ^ 4 ≤ (n : ℝ) := by
    have hdiv : Tendsto (fun x : ℝ ↦ (Real.log x) ^ 4 / x) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using (Real.isLittleO_pow_log_id_atTop (n := 4)).tendsto_div_nhds_zero
    have hm := (hdiv.comp tendsto_natCast_atTop_atTop).eventually
      (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 192))
    filter_upwards [eventually_gt_atTop 1, hm] with n hn1 hle
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have h1 := (div_le_iff₀ hn_pos).mp hle
    linarith
  have hs0_ge : ∀ᶠ n : ℕ in atTop, (5 / 2 : ℝ) * Real.log (n : ℝ) ≤ phaseRootS0 n := by
    have hlim := tendsto_phaseNat_add_mul_q_div_logOrder_two 0
    have h25q : (5 / 2 : ℝ) * q + 1 / 20 < 2 := by
      unfold q; linarith [Real.log_two_lt_d9]
    have hgt := (tendsto_order.1 hlim).1 ((5 / 2 : ℝ) * q + 1 / 20) h25q
    have hL_big : ∀ᶠ n : ℕ in atTop, 80 ≤ logOrder n :=
      tendsto_logOrder_atTop.eventually_ge_atTop 80
    filter_upwards [eventually_phaseDomain, hgt, hL_big] with n hdom hgt_n hL80
    have hL_pos : 0 < logOrder n := by linarith
    rw [Nat.add_zero, lt_div_iff₀ hL_pos] at hgt_n
    have h2q : 2 / q < 3 := by rw [div_lt_iff₀ q_pos]; unfold q; linarith [Real.log_two_gt_d9]
    have hph_ge : (5 / 2 : ℝ) * logOrder n + 4 ≤ (phaseNat n : ℝ) := by
      have h4q : 4 * q ≤ (1 / 20 : ℝ) * logOrder n := by
        have hq1 : q ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)
        linarith
      have hm : ((5 / 2 : ℝ) * logOrder n + 4) * q < (phaseNat n : ℝ) * q := by linarith
      exact (lt_of_mul_lt_mul_right hm q_pos.le).le
    rw [phaseRootS0, alphaZero_eq_phaseNat_add_delta hdom]
    unfold logOrder at hph_ge
    linarith [phaseDelta_nonneg n]
  have hllc80 : ∀ᶠ n : ℕ in atTop,
      ‖logLogOrder n‖ ≤ (1 / (80 * (C_corr + 1))) * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound (by positivity)
  have hDelta_small : ∀ᶠ n : ℕ in atTop,
      (C_corr + 1) * logLogOrder n * phaseRootGapRadius n ≤ phaseRootCenter n / 5 := by
    filter_upwards [hllc80, tendsto_logOrder_atTop.eventually_ge_atTop 4,
      tendsto_logLogOrder_atTop.eventually_ge_atTop 1,
      eventually_phaseRoot_domain_pos_and_target_corridor,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
      n hll hL4 hll1 hcd hph
    have hL_pos : 0 < logOrder n := by linarith
    have hc_pos : 0 < phaseRootCenter n :=
      div_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hcd.1.1)) hcd.2.1
    have ha_pos : (0 : ℝ) < (phaseNat n : ℝ) := lt_of_lt_of_le hL_pos hph.1
    rw [Real.norm_eq_abs, abs_of_pos (by linarith), Real.norm_eq_abs, abs_of_pos hL_pos] at hll
    have h1 : (C_corr + 1) * logLogOrder n ≤ logOrder n / 80 := by
      have hm := mul_le_mul_of_nonneg_left hll hC1
      have hs : (C_corr + 1) * (1 / (80 * (C_corr + 1)) * logOrder n) = logOrder n / 80 := by
        field_simp [(show (0 : ℝ) < C_corr + 1 by linarith).ne']
      linarith
    have hfrac : (C_corr + 1) * logLogOrder n / (phaseNat n : ℝ) ^ 2 ≤ 1 / 5 := by
      rw [div_le_iff₀ (sq_pos_of_pos ha_pos)]
      have ha4 : 4 ≤ (phaseNat n : ℝ) := le_trans hL4 hph.1
      have ha_sq : (phaseNat n : ℝ) ≤ (phaseNat n : ℝ) ^ 2 := by
        calc (phaseNat n : ℝ) = (phaseNat n : ℝ) * 1 := (mul_one _).symm
          _ ≤ (phaseNat n : ℝ) * (phaseNat n : ℝ) := mul_le_mul_of_nonneg_left (by linarith) ha_pos.le
          _ = (phaseNat n : ℝ) ^ 2 := (sq _).symm
      linarith [hph.1]
    have hrew : (C_corr + 1) * logLogOrder n * phaseRootGapRadius n =
        phaseRootCenter n * ((C_corr + 1) * logLogOrder n / (phaseNat n : ℝ) ^ 2) := by
      unfold phaseRootGapRadius; ring
    rw [hrew]
    exact (mul_le_mul_of_nonneg_left hfrac hc_pos.le).trans_eq (by ring)
  filter_upwards [eventually_ge_atTop 20,
    tendsto_logOrder_atTop.eventually_ge_atTop 20,
    tendsto_logLogOrder_atTop.eventually_ge_atTop 1,
    hL4_small, hs0_ge, hllc80, hDelta_small,
    eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
    n hn20 hL20 hll1 hL4n hs0_lb hllc_n hD5 hcd hph
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hL_ge20 : (20 : ℝ) ≤ Real.log (n : ℝ) := hL20
  have hL_pos : 0 < Real.log (n : ℝ) := by linarith
  have hs0_pos : 0 < phaseRootS0 n := hcd.2.1
  have hs0_le_a : phaseRootS0 n ≤ (phaseNat n : ℝ) := by
    rw [phaseRootS0, alphaZero_eq_phaseNat_add_delta hcd.1]
    have h2q : (1 : ℝ) < 2 / q := by rw [lt_div_iff₀ q_pos]; unfold q; linarith [Real.log_two_lt_d9]
    linarith [phaseDelta_lt_one n]
  have ha_le4L : (phaseNat n : ℝ) ≤ 4 * Real.log (n : ℝ) := hph.2
  have ha_pos : (0 : ℝ) < (phaseNat n : ℝ) := lt_of_lt_of_le hL_pos hph.1
  have hc_pos : 0 < phaseRootCenter n := div_pos hn_pos hs0_pos
  have htar_corridor : ∀ s ∈ Set.Icc
      (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n),
      |fourSizeTarget n (phaseNat n) s - phaseTarget (phaseDelta n)| ≤
        2 * (C_corr + 1) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
    intro s hs
    have hs_lo : phaseRootCenter n / 2 ≤ s := by linarith [hs.1, hD5, hc_pos]
    have hs_pos : 0 < s := by linarith [hs_lo, hc_pos]
    have hnc : (n : ℝ) = phaseRootCenter n * phaseRootS0 n := by
      unfold phaseRootCenter; exact (div_mul_cancel₀ _ hs0_pos.ne').symm
    have hdiff_s0 : (n : ℝ) / s - phaseRootS0 n = phaseRootS0 n * (phaseRootCenter n - s) / s := by
      rw [hnc]; field_simp [hs_pos.ne']
    have habs_cs : |phaseRootCenter n - s| ≤
        (C_corr + 1) * logLogOrder n * (phaseRootCenter n / (phaseNat n : ℝ) ^ 2) := by
      rw [abs_sub_comm, abs_le]
      have hgap : phaseRootGapRadius n = phaseRootCenter n / (phaseNat n : ℝ) ^ 2 := rfl
      rw [hgap] at hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hbound_s0 : |(n : ℝ) / s - phaseRootS0 n| ≤
        2 * (C_corr + 1) * logLogOrder n / logOrder n := by
      rw [hdiff_s0, abs_div, abs_mul, abs_of_pos hs0_pos, abs_of_pos hs_pos]
      calc phaseRootS0 n * |phaseRootCenter n - s| / s
          ≤ phaseRootS0 n * ((C_corr + 1) * logLogOrder n *
              (phaseRootCenter n / (phaseNat n : ℝ) ^ 2)) / (phaseRootCenter n / 2) :=
            div_le_div₀ (by positivity)
              (mul_le_mul_of_nonneg_left habs_cs hs0_pos.le) (half_pos hc_pos) hs_lo
        _ = 2 * (C_corr + 1) * logLogOrder n * (phaseRootS0 n / (phaseNat n : ℝ)) / (phaseNat n : ℝ) := by
            field_simp [hc_pos.ne', ha_pos.ne']
        _ ≤ 2 * (C_corr + 1) * logLogOrder n * 1 / (phaseNat n : ℝ) := by
            apply div_le_div_of_nonneg_right _ ha_pos.le
            exact mul_le_mul_of_nonneg_left ((div_le_one ha_pos).mpr hs0_le_a)
              (mul_nonneg (by positivity) (by linarith [hll1]))
        _ = 2 * (C_corr + 1) * logLogOrder n / (phaseNat n : ℝ) := by ring
        _ ≤ 2 * (C_corr + 1) * logLogOrder n / logOrder n :=
            div_le_div_of_nonneg_left (mul_nonneg (by positivity) (by linarith [hll1]))
              hL_pos hph.1
    have htarget_eq : fourSizeTarget n (phaseNat n) s - phaseTarget (phaseDelta n) =
        phaseRootS0 n - (n : ℝ) / s := by
      unfold fourSizeTarget phaseTarget phaseRootS0 q
      rw [alphaZero_eq_phaseNat_add_delta hcd.1]; ring
    rw [htarget_eq, abs_sub_comm]
    simpa only [logLogOrder, logOrder] using hbound_s0
  have hKcap_corridor : ∀ s ∈ Set.Icc
      (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n),
      phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar →
        fourSizeTarget n (phaseNat n) s ∈ KcapInterval := by
    intro s hs hd
    have htar_s := htar_corridor s hs
    have hrate_le : 2 * (C_corr + 1) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) ≤ 1 / 40 := by
      dsimp [logLogOrder, logOrder] at hllc_n hll1
      rw [abs_of_pos (by linarith only [hll1]), abs_of_pos hL_pos] at hllc_n
      rw [div_le_iff₀ hL_pos]
      have hm := mul_le_mul_of_nonneg_left hllc_n (show (0 : ℝ) ≤ 2 * (C_corr + 1) by positivity)
      have hs' : 2 * (C_corr + 1) * (1 / (80 * (C_corr + 1)) * Real.log (n : ℝ)) =
          1 / 40 * Real.log (n : ℝ) := by
        field_simp [(show (0 : ℝ) < C_corr + 1 by linarith).ne']; ring
      linarith
    have hb := abs_le.mp (htar_s.trans hrate_le)
    unfold phaseTarget at hb; unfold deltaStar at hd; unfold KcapInterval
    exact ⟨by linarith [hd.2, hb.1], by linarith [hd.1, hb.2]⟩
  have hgap_lb : (n : ℝ) / (64 * (Real.log (n : ℝ)) ^ 3) ≤ phaseRootGapRadius n := by
    unfold phaseRootGapRadius phaseRootCenter
    rw [div_div]
    have hden_le : phaseRootS0 n * (phaseNat n : ℝ) ^ 2 ≤ 64 * (Real.log (n : ℝ)) ^ 3 := by
      calc phaseRootS0 n * (phaseNat n : ℝ) ^ 2
          ≤ (4 * Real.log (n : ℝ)) * (4 * Real.log (n : ℝ)) ^ 2 :=
            mul_le_mul (hs0_le_a.trans ha_le4L)
              (pow_le_pow_left₀ ha_pos.le ha_le4L 2) (sq_nonneg _) (by positivity)
        _ = 64 * (Real.log (n : ℝ)) ^ 3 := by ring
    exact div_le_div_of_nonneg_left hn_pos.le (mul_pos hs0_pos (sq_pos_of_pos ha_pos)) hden_le
  have hpad_shift : Real.log (n : ℝ) + 20 ≤ logLogOrder n * phaseRootGapRadius n := by
    have h1 : Real.log (n : ℝ) + 20 ≤ 3 * Real.log (n : ℝ) := by linarith
    have h2 : 3 * Real.log (n : ℝ) ≤ (n : ℝ) / (64 * (Real.log (n : ℝ)) ^ 3) := by
      rw [le_div_iff₀ (by positivity)]
      calc 3 * Real.log (n : ℝ) * (64 * (Real.log (n : ℝ)) ^ 3)
          = 192 * (Real.log (n : ℝ)) ^ 4 := by ring
        _ ≤ (n : ℝ) := hL4n
    have h3 : phaseRootGapRadius n ≤ logLogOrder n * phaseRootGapRadius n :=
      le_mul_of_one_le_left (le_trans (by positivity) hgap_lb) hll1
    linarith
  have hc_hi : phaseRootCenter n ≤ (2 / 5 : ℝ) * (n : ℝ) / Real.log (n : ℝ) := by
    unfold phaseRootCenter
    have h1 := div_le_div_of_nonneg_left hn_pos.le (by positivity) hs0_lb
    exact h1.trans_eq (by ring)
  have hc_lo : (n : ℝ) / (4 * Real.log (n : ℝ)) ≤ phaseRootCenter n := by
    unfold phaseRootCenter
    exact div_le_div_of_nonneg_left hn_pos.le hs0_pos (hs0_le_a.trans ha_le4L)
  refine ⟨hn1, by linarith, hll1, hpad_shift, hKcap_corridor, fun r hr ↦ ?_⟩
  intro k_co k_ch
  have hrad_nn : 0 ≤ logLogOrder n * phaseRootGapRadius n := by linarith [hL_pos, hpad_shift]
  have hr_wide : r ∈ Set.Icc
      (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n) :=
    ⟨by linarith [hr.1, hrad_nn], by linarith [hr.2, hrad_nn]⟩
  have hr_lo : (n : ℝ) / (6 * Real.log (n : ℝ)) ≤ r := by
    have h1 : (4 / 5 : ℝ) * phaseRootCenter n ≤ r := by linarith [hr_wide.1, hD5]
    have h2 : (n : ℝ) / (6 * Real.log (n : ℝ)) ≤ (4 / 5 : ℝ) * ((n : ℝ) / (4 * Real.log (n : ℝ))) := by
      have : (0 : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) := by positivity
      linarith [show (n : ℝ) / (6 * Real.log (n : ℝ)) = (1 / 6) * ((n : ℝ) / Real.log (n : ℝ)) by ring,
        show (4 / 5 : ℝ) * ((n : ℝ) / (4 * Real.log (n : ℝ))) = (1 / 5) * ((n : ℝ) / Real.log (n : ℝ)) by ring]
    exact h2.trans ((mul_le_mul_of_nonneg_left hc_lo (by norm_num)).trans h1)
  have hk_co_ge : r + 16 ≤ (k_co : ℝ) := by
    dsimp [k_co]; push_cast; linarith [Nat.le_ceil r]
  have hk_co_le : (k_co : ℝ) ≤ r + 17 := by
    dsimp [k_co]; push_cast
    have hr_nn : 0 ≤ r := le_trans (by positivity) hr_lo
    linarith [Nat.ceil_lt_add_one hr_nn]
  have hk_ch_ge : r + Real.log (n : ℝ) ≤ (k_ch : ℝ) := by
    dsimp [k_ch]; push_cast; linarith [Nat.le_ceil r, Nat.le_ceil (Real.log (n : ℝ))]
  have hk_ch_le : (k_ch : ℝ) ≤ r + Real.log (n : ℝ) + 2 := by
    dsimp [k_ch]; push_cast
    have hr_nn : 0 ≤ r := le_trans (by positivity) hr_lo
    linarith [Nat.ceil_lt_add_one hr_nn, Nat.ceil_lt_add_one hL_pos.le]
  have hk_co_icc : (k_co : ℝ) ∈ Set.Icc
      (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n) := by
    refine ⟨by linarith [hr.1, hk_co_ge, hrad_nn], ?_⟩
    have : (17 : ℝ) ≤ logLogOrder n * phaseRootGapRadius n := by linarith [hpad_shift, hL_pos]
    linarith [hr.2, hk_co_le]
  have hk_ch_icc : (k_ch : ℝ) ∈ Set.Icc
      (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n) := by
    refine ⟨by linarith [hr.1, hk_ch_ge, hrad_nn, hL_pos], ?_⟩
    have : Real.log (n : ℝ) + 2 ≤ logLogOrder n * phaseRootGapRadius n := by linarith [hpad_shift]
    linarith [hr.2, hk_ch_le]
  have hub_corridor : ∀ s ∈ Set.Icc
      (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n),
      s ≤ (n : ℝ) / Real.log (n : ℝ) := by
    intro s hs
    calc s ≤ (6 / 5 : ℝ) * phaseRootCenter n := by linarith [hs.2, hD5]
      _ ≤ (6 / 5 : ℝ) * ((2 / 5 : ℝ) * (n : ℝ) / Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hc_hi (by norm_num)
      _ ≤ (n : ℝ) / Real.log (n : ℝ) := by
          have : (0 : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) := by positivity
          linarith [show (6 / 5 : ℝ) * ((2 / 5 : ℝ) * (n : ℝ) / Real.log (n : ℝ)) =
            (12 / 25) * ((n : ℝ) / Real.log (n : ℝ)) by ring]
  exact ⟨hr_lo,
    by dsimp [k_co]; omega,
    hub_corridor (k_co : ℝ) hk_co_icc,
    by linarith [hr_lo, hk_co_ge],
    hk_co_ge,
    hk_co_icc,
    by
      have hceil_pos : 1 ≤ Nat.ceil (Real.log (n : ℝ)) :=
        Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hL_pos).ne'
      dsimp [k_ch]; omega,
    hub_corridor (k_ch : ℝ) hk_ch_icc,
    by linarith [hr_lo, hk_ch_ge, hL_pos],
    hk_ch_ge,
    hk_ch_icc,
    htar_corridor (k_co : ℝ) hk_co_icc,
    htar_corridor (k_ch : ℝ) hk_ch_icc⟩

private theorem wProb_lip_in_tilt_v13
    {m M : ℕ} (hM : 1 ≤ M) (sc : ℕ → ℝ)
    {i : ℕ} (hi : i ∈ Finset.Icc (m + 1) (m + M)) (l₁ l₂ : ℝ) :
    |wProb_v13 (Finset.Icc (m + 1) (m + M)) sc l₁ i -
        wProb_v13 (Finset.Icc (m + 1) (m + M)) sc l₂ i| ≤
      2 * ((m + M : ℕ) : ℝ) * |l₁ - l₂| := by
  set W := Finset.Icc (m + 1) (m + M)
  have hW_ne : W.Nonempty := ⟨m + 1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have hd_p : ∀ x : ℝ,
      HasDerivAt (fun μ ↦ wProb_v13 W sc μ i)
        (((i : ℝ) - wMean_v13 W sc x) * wProb_v13 W sc x i) x := by
    intro x
    have hZ := wPart_v13_pos hW_ne sc x
    have hfn : (fun μ ↦ wProb_v13 W sc μ i) =
        fun μ ↦ Real.exp (μ * (i : ℝ) + sc i) / wPart_v13 W sc μ := by
      funext μ; simp [wProb_v13, hi]
    rw [hfn]
    have hd1 : HasDerivAt (fun μ : ℝ ↦ Real.exp (μ * (i : ℝ) + sc i))
        ((i : ℝ) * Real.exp (x * (i : ℝ) + sc i)) x := by
      have hl : HasDerivAt (fun μ : ℝ ↦ μ * (i : ℝ) + sc i) (i : ℝ) x := by
        simpa using ((hasDerivAt_id x).mul_const (i : ℝ)).add_const (sc i)
      exact (hl.exp).congr_deriv (by ring)
    have hd2 : HasDerivAt (wPart_v13 W sc)
        (∑ j ∈ W, (j : ℝ) * Real.exp (x * (j : ℝ) + sc j)) x := by
      classical
      unfold wPart_v13
      have hst : ∀ s : Finset ℕ,
          HasDerivAt (fun μ ↦ ∑ j ∈ s, Real.exp (μ * (j : ℝ) + sc j))
            (∑ j ∈ s, (j : ℝ) * Real.exp (x * (j : ℝ) + sc j)) x := by
        intro s
        induction s using Finset.induction_on with
        | empty => simpa using hasDerivAt_const x (0 : ℝ)
        | @insert a t ha ih =>
          have hf_eq : (fun μ ↦ ∑ j ∈ insert a t, Real.exp (μ * (j : ℝ) + sc j)) =
              fun μ ↦ Real.exp (μ * (a : ℝ) + sc a) +
                ∑ j ∈ t, Real.exp (μ * (j : ℝ) + sc j) := by
            funext μ; exact Finset.sum_insert ha
          rw [hf_eq, Finset.sum_insert ha]
          have hda : HasDerivAt (fun μ : ℝ ↦ Real.exp (μ * (a : ℝ) + sc a))
              ((a : ℝ) * Real.exp (x * (a : ℝ) + sc a)) x := by
            have hl : HasDerivAt (fun μ : ℝ ↦ μ * (a : ℝ) + sc a) (a : ℝ) x := by
              simpa using ((hasDerivAt_id x).mul_const (a : ℝ)).add_const (sc a)
            exact (hl.exp).congr_deriv (by ring)
          exact hda.add ih
      exact hst W
    refine (hd1.div hd2 hZ.ne').congr_deriv ?_
    simp only [wProb_v13, hi, ↓reduceIte, wMean_v13]
    field_simp [hZ.ne']
  have hnorm_d : ∀ x : ℝ,
      ‖((i : ℝ) - wMean_v13 W sc x) * wProb_v13 W sc x i‖ ≤ 2 * ((m + M : ℕ) : ℝ) := by
    intro x
    have hZ := wPart_v13_pos hW_ne sc x
    have hp_nn : 0 ≤ wProb_v13 W sc x i := by
      simp only [wProb_v13, hi, ↓reduceIte]; exact div_nonneg (Real.exp_pos _).le hZ.le
    have hp_le1 : wProb_v13 W sc x i ≤ 1 := by
      rw [← sum_wProb_v13 hW_ne sc x]
      exact Finset.single_le_sum (fun j hj ↦ by
        simp only [wProb_v13, hj, ↓reduceIte]; exact div_nonneg (Real.exp_pos _).le hZ.le) hi
    have hm_nn : 0 ≤ wMean_v13 W sc x :=
      div_nonneg (Finset.sum_nonneg fun j _ ↦ mul_nonneg (Nat.cast_nonneg j) (Real.exp_pos _).le) hZ.le
    have hm_hi : wMean_v13 W sc x ≤ ((m + M : ℕ) : ℝ) := by
      rw [← sum_mul_wProb_v13]
      calc ∑ j ∈ W, (j : ℝ) * wProb_v13 W sc x j
          ≤ ∑ j ∈ W, ((m + M : ℕ) : ℝ) * wProb_v13 W sc x j := by
            refine Finset.sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_right ?_ ?_
            · exact_mod_cast (Finset.mem_Icc.mp hj).2
            · simp only [wProb_v13, hj, ↓reduceIte]; exact div_nonneg (Real.exp_pos _).le hZ.le
        _ = ((m + M : ℕ) : ℝ) := by rw [← Finset.mul_sum, sum_wProb_v13 hW_ne, mul_one]
    have hi_hi : (i : ℝ) ≤ ((m + M : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hi).2
    have hi_nn : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp_nn]
    have habs_im : |(i : ℝ) - wMean_v13 W sc x| ≤ 2 * ((m + M : ℕ) : ℝ) := by
      rw [abs_le]; exact ⟨by linarith only [hi_nn, hm_hi, hi_hi], by linarith only [hm_nn, hi_hi, hm_hi]⟩
    exact (mul_le_mul habs_im hp_le1 hp_nn (by positivity)).trans_eq (mul_one _)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun μ ↦ wProb_v13 W sc μ i)
    (fun x _ ↦ (hd_p x).hasDerivWithinAt)
    (fun x _ ↦ hnorm_d x) convex_univ (Set.mem_univ l₂) (Set.mem_univ l₁)
  simpa only [Real.norm_eq_abs] using hmvt

private theorem build_selectedProfile_at_k_regimeU_v13
    {n m M k : ℕ} (hm : m ≤ 1) (hM : 7 ≤ M) (hn8 : 8 ≤ n)
    (ha_ge_4sq : 4 * (1 + M) ^ 2 ≤ phaseNat n)
    (ha_ge_L : Real.log (n : ℝ) ≤ (phaseNat n : ℝ))
    {C_corr c_star C_opt B_err_max C_round_max C_p : ℝ}
    (_hC_pos : 0 < C_corr) (hc_pos : 0 < c_star) (hCopt_pos : 0 < C_opt)
    (hBerr_max_def : B_err_max = (((1 + M + 4) * M + 1 : ℕ) : ℝ))
    (hCround_max_def : C_round_max =
      (M : ℝ) * ((1 + |Real.log c_star|) * B_err_max + (((1 + M : ℕ) : ℝ) ^ 2 + 1) * B_err_max))
    (hCp_def : C_p = 4 * ((1 + M : ℕ) : ℝ) * (C_corr + 1) / wMasterCstar M + C_opt + 6 * B_err_max + 1)
    (hk_th1 : 6 * (B_err_max / c_star + 1) * Real.log (n : ℝ) ≤ (n : ℝ))
    (hk_th2 : 6 * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ))
    (hL_ge2 : (2 : ℝ) ≤ Real.log (n : ℝ))
    (hll_ge1 : (1 : ℝ) ≤ Real.log (Real.log (n : ℝ)))
    (hk1 : 1 ≤ k)
    (hk_lb : (n : ℝ) / (6 * Real.log (n : ℝ)) ≤ (k : ℝ))
    (hTk_17 : fourSizeTarget n (phaseNat n) (k : ℝ) ∈ Set.Icc (9 / 4 : ℝ) (17 / 4))
    (htar_k : |fourSizeTarget n (phaseNat n) (k : ℝ) - phaseTarget (phaseDelta n)| ≤
      2 * (C_corr + 1) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
    {l_lim l_fin : ℝ}
    (hl_lim_eq : wMean_v13 (Finset.Icc (m + 1) (m + M))
      (fun i ↦ -Real.log 2 / 2 * (i : ℝ) ^ 2) l_lim = fourSizeTarget n (phaseNat n) (k : ℝ))
    (hp_sum : ∑ i ∈ Finset.Icc (m + 1) (m + M),
      (if i ∈ Finset.Icc (m + 1) (m + M) then
        Real.exp (l_fin * (i : ℝ) +
          (Real.log ((phaseNat n).descFactorial i : ℝ) -
            (i : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (i : ℝ) ^ 2)) /
          (∑ j ∈ Finset.Icc (m + 1) (m + M),
            Real.exp (l_fin * (j : ℝ) +
              (Real.log ((phaseNat n).descFactorial j : ℝ) -
                (j : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (j : ℝ) ^ 2)))
      else 0) = 1)
    (hp_mean : ∑ i ∈ Finset.Icc (m + 1) (m + M),
      (i : ℝ) * (if i ∈ Finset.Icc (m + 1) (m + M) then
        Real.exp (l_fin * (i : ℝ) +
          (Real.log ((phaseNat n).descFactorial i : ℝ) -
            (i : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (i : ℝ) ^ 2)) /
          (∑ j ∈ Finset.Icc (m + 1) (m + M),
            Real.exp (l_fin * (j : ℝ) +
              (Real.log ((phaseNat n).descFactorial j : ℝ) -
                (j : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (j : ℝ) ^ 2)))
      else 0) = fourSizeTarget n (phaseNat n) (k : ℝ))
    (hF_ent : (⨅ l : ℝ,
        (Real.log (∑ i ∈ Finset.Icc (m + 1) (m + M),
          Real.exp (l * (i : ℝ) +
            (Real.log ((phaseNat n).descFactorial i : ℝ) -
              (i : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (i : ℝ) ^ 2))) -
          l * fourSizeTarget n (phaseNat n) (k : ℝ))) =
      -(∑ i ∈ Finset.Icc (m + 1) (m + M),
          (if i ∈ Finset.Icc (m + 1) (m + M) then
            Real.exp (l_fin * (i : ℝ) +
              (Real.log ((phaseNat n).descFactorial i : ℝ) -
                (i : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (i : ℝ) ^ 2)) /
              (∑ j ∈ Finset.Icc (m + 1) (m + M),
                Real.exp (l_fin * (j : ℝ) +
                  (Real.log ((phaseNat n).descFactorial j : ℝ) -
                    (j : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (j : ℝ) ^ 2)))
          else 0) * Real.log (if i ∈ Finset.Icc (m + 1) (m + M) then
            Real.exp (l_fin * (i : ℝ) +
              (Real.log ((phaseNat n).descFactorial i : ℝ) -
                (i : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (i : ℝ) ^ 2)) /
              (∑ j ∈ Finset.Icc (m + 1) (m + M),
                Real.exp (l_fin * (j : ℝ) +
                  (Real.log ((phaseNat n).descFactorial j : ℝ) -
                    (j : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (j : ℝ) ^ 2)))
          else 0)) +
        ∑ i ∈ Finset.Icc (m + 1) (m + M),
          (if i ∈ Finset.Icc (m + 1) (m + M) then
            Real.exp (l_fin * (i : ℝ) +
              (Real.log ((phaseNat n).descFactorial i : ℝ) -
                (i : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (i : ℝ) ^ 2)) /
              (∑ j ∈ Finset.Icc (m + 1) (m + M),
                Real.exp (l_fin * (j : ℝ) +
                  (Real.log ((phaseNat n).descFactorial j : ℝ) -
                    (j : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (j : ℝ) ^ 2)))
          else 0) * (Real.log ((phaseNat n).descFactorial i : ℝ) -
            (i : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (i : ℝ) ^ 2))
    (hp_bds : ∀ i ∈ Finset.Icc (m + 1) (m + M),
      2 * c_star ≤ (if i ∈ Finset.Icc (m + 1) (m + M) then
        Real.exp (l_fin * (i : ℝ) +
          (Real.log ((phaseNat n).descFactorial i : ℝ) -
            (i : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (i : ℝ) ^ 2)) /
          (∑ j ∈ Finset.Icc (m + 1) (m + M),
            Real.exp (l_fin * (j : ℝ) +
              (Real.log ((phaseNat n).descFactorial j : ℝ) -
                (j : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (j : ℝ) ^ 2)))
      else 0) ∧
      |(if i ∈ Finset.Icc (m + 1) (m + M) then
          Real.exp (l_fin * (i : ℝ) +
            (Real.log ((phaseNat n).descFactorial i : ℝ) -
              (i : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (i : ℝ) ^ 2)) /
            (∑ j ∈ Finset.Icc (m + 1) (m + M),
              Real.exp (l_fin * (j : ℝ) +
                (Real.log ((phaseNat n).descFactorial j : ℝ) -
                  (j : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (j : ℝ) ^ 2)))
        else 0) -
        (if i ∈ Finset.Icc (m + 1) (m + M) then
          Real.exp (l_lim * (i : ℝ) + (-Real.log 2 / 2 * (i : ℝ) ^ 2)) /
            (∑ j ∈ Finset.Icc (m + 1) (m + M),
              Real.exp (l_lim * (j : ℝ) + (-Real.log 2 / 2 * (j : ℝ) ^ 2)))
        else 0)| ≤ C_opt / (phaseNat n : ℝ)) :
    let u : Fin M → ℕ := fun j ↦ phaseNat n - (m + 1 + j.1)
    let h_sc : ℕ → ℝ := fun i ↦
      Real.log ((phaseNat n).descFactorial i : ℝ) -
        (i : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (i : ℝ) ^ 2
    let F_win : ℝ → ℝ := fun T ↦ ⨅ l : ℝ,
      (Real.log (∑ i ∈ Finset.Icc (m + 1) (m + M), Real.exp (l * (i : ℝ) + h_sc i)) - l * T)
    let obj_win0 : ℝ :=
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (k : ℝ) - (k : ℝ) * Real.log (k : ℝ) +
        (k : ℝ) * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) (k : ℝ) +
          F_win (fourSizeTarget n (phaseNat n) (k : ℝ)) + 0)
    ∃ (kv : Fin M → ℕ) (kp : ColoringProfile (phaseNat n)),
      selectedBlockCount kv = k ∧
      selectedVertexMass u kv = n ∧
      (∀ j : Fin M, 0 < kv j ∧ c_star ≤ (kv j : ℝ) / (k : ℝ)) ∧
      (∀ idx : Fin (phaseNat n), kp idx = ∑ j : Fin M, if u j = idx.1 + 1 then kv j else 0) ∧
      ColoringProfile.partCount kp = k ∧
      ColoringProfile.vertexMass kp = n ∧
      (profileColoringExpectation n kp).toReal = completeUnmarkedFirstMoment u kv ∧
      (signedProfileExpectation n kp).toReal = completeSignedFirstMoment u kv ∧
      (∀ P : ProfilePartition n kp,
        P.1.parts.card = k ∧
        ∀ D ∈ P.1.parts, phaseNat n - (m + M) ≤ D.card ∧ D.card ≤ phaseNat n - (m + 1)) ∧
      (∀ G : LabeledGraph n,
        ((∃ P : ProfilePartition n kp, G ∈ partitionCocoloringEvent P.1) → cochromaticNumber G ≤ k) ∧
        ((∃ P : ProfilePartition n kp, G ∈ partitionColoringEvent P.1) → chromaticNumberNat G ≤ k)) ∧
      (∀ lam : ℝ, meanS0M M lam = phaseTarget (phaseDelta n + (m : ℝ)) →
        ∀ j : Fin M,
          |(kv j : ℝ) / (k : ℝ) - gibbsProbS0M M lam ((j.1 : ℤ) + 1)| ≤
            C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) ∧
      obj_win0 - C_round_max - (M : ℝ) * (1 + 2 * Real.log (n : ℝ)) ≤
        Real.log (completeUnmarkedFirstMoment u kv) := by
  intro u h_sc F_win obj_win0
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL_pos : 0 < Real.log (n : ℝ) := by linarith only [hL_ge2]
  have hwmc_pos : 0 < wMasterCstar M := by unfold wMasterCstar; positivity
  have hBerr_max_pos : 0 < B_err_max := by rw [hBerr_max_def]; positivity
  have hB_le_max : (((m + M + 4) * M + 1 : ℕ) : ℝ) ≤ B_err_max := by
    rw [hBerr_max_def]
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_right M (by omega)) 1
  set T_k : ℝ := fourSizeTarget n (phaseNat n) (k : ℝ)
  have hTk_icc : T_k ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) := ⟨hTk_17.1, by linarith only [hTk_17.2]⟩
  set W := Finset.Icc (m + 1) (m + M)
  let p_fin : ℕ → ℝ := fun i ↦
    if i ∈ W then Real.exp (l_fin * (i : ℝ) + h_sc i) /
      (∑ j ∈ W, Real.exp (l_fin * (j : ℝ) + h_sc j)) else 0
  let p_lim : ℕ → ℝ := fun i ↦
    if i ∈ W then Real.exp (l_lim * (i : ℝ) + (-Real.log 2 / 2 * (i : ℝ) ^ 2)) /
      (∑ j ∈ W, Real.exp (l_lim * (j : ℝ) + (-Real.log 2 / 2 * (j : ℝ) ^ 2))) else 0
  have hk_big : (((m + M + 4) * M + 1 : ℕ) : ℝ) / c_star + 1 ≤ (k : ℝ) := by
    have h1 : (((m + M + 4) * M + 1 : ℕ) : ℝ) / c_star + 1 ≤ B_err_max / c_star + 1 := by
      have hd := div_le_div_of_nonneg_right hB_le_max hc_pos.le
      linarith only [hd]
    have h2 : B_err_max / c_star + 1 ≤ (n : ℝ) / (6 * Real.log (n : ℝ)) :=
      (le_div_iff₀ (by positivity)).mpr (by linarith only [hk_th1])
    exact h1.trans (h2.trans hk_lb)
  obtain ⟨hkv_props, hblock_eq, hmass_eq, hlog_ge⟩ :=
    roundedWindowProfile_unmarked_v13 (n := n) (alpha := phaseNat n) (m := m) (M := M) (k := k)
      (p_opt := p_fin) hm hM (by omega) ha_ge_4sq hc_pos hp_sum hp_mean
      (fun i hi ↦ (hp_bds i hi).1) hk_big
  let kv : Fin M → ℕ := fun j ↦ (roundedWindowProfile m M (phaseNat n) k n p_fin (m + 1 + j.1)).toNat
  let kp : ColoringProfile (phaseNat n) := embedWindowProfile_v13 (phaseNat n) m M kv
  obtain ⟨_, hkp_part, hkp_mass, _, hkp_unm, hkp_sgn, hkp_P, hkp_G⟩ :=
    embedWindowProfile_properties_v13 (n := n) (alpha := phaseNat n) (m := m) (M := M)
      (by have := Nat.le_self_pow (by norm_num : 2 ≠ 0) (1 + M); omega) hmass_eq
  have hCround_le :
      (M : ℝ) * ((1 + |Real.log c_star|) * (((m + M + 4) * M + 1 : ℕ) : ℝ) +
          (((1 + M : ℕ) : ℝ) ^ 2 + 1) * (((m + M + 4) * M + 1 : ℕ) : ℝ)) ≤ C_round_max := by
    rw [hCround_max_def]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg M)
    exact add_le_add (mul_le_mul_of_nonneg_left hB_le_max (by positivity))
      (mul_le_mul_of_nonneg_left hB_le_max (by positivity))
  have hlog_en1 : Real.log (Real.exp 1 * ((n : ℝ) + 1)) ≤ 1 + 2 * Real.log (n : ℝ) := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn1_sq : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast (show n + 1 ≤ n ^ 2 by rw [sq]; calc n + 1 ≤ 2 * n := by omega
        _ ≤ n * n := Nat.mul_le_mul_right n (by omega))
    calc Real.log (Real.exp 1 * ((n : ℝ) + 1))
        ≤ Real.log (Real.exp 1 * (n : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hn1_sq (Real.exp_pos 1).le)
      _ = Real.log (Real.exp 1) + Real.log ((n : ℝ) ^ 2) :=
          Real.log_mul (Real.exp_pos 1).ne' (pow_pos hn_pos 2).ne'
      _ = 1 + 2 * Real.log (n : ℝ) := by rw [Real.log_exp, Real.log_pow]; norm_num
  have hobj0_eq :
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (k : ℝ) - (k : ℝ) * Real.log (k : ℝ) +
        (k : ℝ) * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) (k : ℝ) +
          (-(∑ i ∈ W, p_fin i * Real.log (p_fin i)) + ∑ i ∈ W, p_fin i * h_sc i)) =
        obj_win0 := by
    have hF_eq_ent : F_win T_k =
        -(∑ i ∈ W, p_fin i * Real.log (p_fin i)) + ∑ i ∈ W, p_fin i * h_sc i := hF_ent
    dsimp [obj_win0, T_k] at hF_eq_ent ⊢
    rw [hF_eq_ent]; ring
  have hlog_unm_ge :
      obj_win0 - C_round_max - (M : ℝ) * (1 + 2 * Real.log (n : ℝ)) ≤
        Real.log (completeUnmarkedFirstMoment u kv) := by
    have hm_log := mul_le_mul_of_nonneg_left hlog_en1 (Nat.cast_nonneg M)
    linarith only [hlog_ge, hobj0_eq, hCround_le, hm_log]
  have hratio_lam : ∀ lam : ℝ, meanS0M M lam = phaseTarget (phaseDelta n + (m : ℝ)) →
      ∀ j : Fin M,
        |(kv j : ℝ) / (k : ℝ) - gibbsProbS0M M lam ((j.1 : ℤ) + 1)| ≤
          C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
    intro lam hlam_mean j
    let g_sc : ℕ → ℝ := fun i ↦ -Real.log 2 / 2 * (i : ℝ) ^ 2
    set lam_W : ℝ := lam + (m : ℝ) * Real.log 2
    have hsh := wProb_and_wMean_shift_S0M_v13 (m := m) (M := M) (by omega) lam_W
    have hl'_eq : lam_W - (m : ℝ) * Real.log 2 = lam := by dsimp [lam_W]; ring
    have hp_sh : wProb_v13 W g_sc lam_W (m + 1 + j.1) = gibbsProbS0M M lam ((j.1 : ℤ) + 1) := by
      simpa only [hl'_eq] using hsh.1 j
    have hm_sh : wMean_v13 W g_sc lam_W = phaseTarget (phaseDelta n) := by
      have h1 : wMean_v13 W g_sc lam_W = meanS0M M lam + (m : ℝ) := by simpa only [hl'_eq] using hsh.2
      rw [h1, hlam_mean]; unfold phaseTarget; ring
    have hT0_icc : phaseTarget (phaseDelta n) ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) := by
      obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
      unfold phaseTarget
      exact ⟨by linarith [phaseDelta_lt_one n, h2lo], by linarith [phaseDelta_nonneg n, h2hi]⟩
    have hg_bds : ∀ i ∈ W, -(((1 + M : ℕ) : ℝ) ^ 2 + 1) ≤ g_sc i ∧ g_sc i ≤ 0 := by
      intro i hi
      dsimp [g_sc]
      have hsq_le : (i : ℝ) ^ 2 ≤ ((1 + M : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg i)
          (by exact_mod_cast (le_trans (Finset.mem_Icc.mp hi).2 (by omega : m + M ≤ 1 + M))) 2
      have hq_i : (Real.log 2 / 2) * (i : ℝ) ^ 2 ≤ 1 * ((1 + M : ℕ) : ℝ) ^ 2 :=
        mul_le_mul (by linarith [Real.log_two_lt_d9]) hsq_le (sq_nonneg _) zero_le_one
      have hq_nn : 0 ≤ (Real.log 2 / 2) * (i : ℝ) ^ 2 :=
        mul_nonneg (div_nonneg hq_pos.le zero_le_two) (sq_nonneg _)
      rw [show -Real.log 2 / 2 * (i : ℝ) ^ 2 = -((Real.log 2 / 2) * (i : ℝ) ^ 2) by ring]
      exact ⟨by linarith only [hq_i], by linarith only [hq_nn]⟩
    have hm_master := windowGibbs_master_v13 hm hM hg_bds
    have hStrict_g := hm_master.2.2.1
    have hBox_g := hm_master.2.2.2.1
    have hl_lim_icc : l_lim ∈ Set.Icc (-(wMasterLambda M)) (wMasterLambda M) :=
      ((hm_master.2.2.2.2 T_k hTk_icc).2 l_lim hl_lim_eq).1
    have hlamW_icc : lam_W ∈ Set.Icc (-(wMasterLambda M)) (wMasterLambda M) :=
      ((hm_master.2.2.2.2 _ hT0_icc).2 lam_W hm_sh).1
    clear hm_master
    have hW_ne : W.Nonempty := ⟨m + 1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
    have hl_dist : |l_lim - lam_W| ≤
        (2 * (C_corr + 1) / wMasterCstar M) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
      have hmvt_g : ∀ {a b : ℝ},
          a ∈ Set.Icc (-(wMasterLambda M)) (wMasterLambda M) →
          b ∈ Set.Icc (-(wMasterLambda M)) (wMasterLambda M) → a ≤ b →
          wMasterCstar M * (b - a) ≤ wMean_v13 W g_sc b - wMean_v13 W g_sc a := by
        intro a b ha hb hab
        exact derivative_lower_bound_mul_sub_le_sub hab
          (fun x _ ↦ (hasDerivAt_wMean_v13 hW_ne g_sc x).continuousAt.continuousWithinAt)
          (fun x _ ↦ (hasDerivAt_wMean_v13 hW_ne g_sc x).differentiableAt.differentiableWithinAt)
          (fun x hx ↦ by
            rw [(hasDerivAt_wMean_v13 hW_ne g_sc x).deriv]
            exact (hBox_g x ⟨ha.1.trans (Ioo_subset_Icc_self hx).1,
              (Ioo_subset_Icc_self hx).2.trans hb.2⟩).2)
      have hmul_c : wMasterCstar M * |l_lim - lam_W| ≤ |T_k - phaseTarget (phaseDelta n)| := by
        rw [← hl_lim_eq, ← hm_sh]
        rcases le_total l_lim lam_W with hle | hle
        · rw [abs_sub_comm l_lim lam_W, abs_of_nonneg (sub_nonneg.mpr hle),
            abs_sub_comm (wMean_v13 _ _ l_lim),
            abs_of_nonneg (sub_nonneg.mpr (hStrict_g.monotone hle))]
          exact hmvt_g hl_lim_icc hlamW_icc hle
        · rw [abs_of_nonneg (sub_nonneg.mpr hle),
            abs_of_nonneg (sub_nonneg.mpr (hStrict_g.monotone hle))]
          exact hmvt_g hlamW_icc hl_lim_icc hle
      exact ((le_div_iff₀' hwmc_pos).mpr (hmul_c.trans htar_k)).trans_eq (by ring)
    have hjW : m + 1 + j.1 ∈ W := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hp_lip_g :
        |wProb_v13 W g_sc l_lim (m + 1 + j.1) - wProb_v13 W g_sc lam_W (m + 1 + j.1)| ≤
          2 * ((1 + M : ℕ) : ℝ) * |l_lim - lam_W| :=
      (wProb_lip_in_tilt_v13 (by omega) g_sc hjW l_lim lam_W).trans
        (mul_le_mul_of_nonneg_right
          (by exact_mod_cast (show 2 * (m + M) ≤ 2 * (1 + M) by omega)) (abs_nonneg _))
    have herr1 : |(kv j : ℝ) / (k : ℝ) - p_fin (m + 1 + j.1)| ≤
        6 * B_err_max * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
      have hb1 := (hkv_props j).2.2
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
      have hinv_k : 1 / (k : ℝ) ≤ 6 / Real.log (n : ℝ) := by
        have hL_le_k : Real.log (n : ℝ) ≤ (k : ℝ) :=
          ((le_div_iff₀ (by positivity : (0 : ℝ) < 6 * Real.log (n : ℝ))).mpr
            (by
              have heq6 : Real.log (n : ℝ) * (6 * Real.log (n : ℝ)) = 6 * (Real.log (n : ℝ)) ^ 2 := by ring
              linarith only [hk_th2, heq6])).trans hk_lb
        rw [div_le_div_iff₀ hk_pos hL_pos]
        linarith only [hL_le_k]
      calc |(kv j : ℝ) / (k : ℝ) - p_fin (m + 1 + j.1)|
          ≤ B_err_max * (1 / (k : ℝ)) := by
            calc _ ≤ (((m + M + 4) * M + 1 : ℕ) : ℝ) / (k : ℝ) := hb1
              _ ≤ B_err_max / (k : ℝ) := div_le_div_of_nonneg_right hB_le_max hk_pos.le
              _ = B_err_max * (1 / (k : ℝ)) := by ring
        _ ≤ B_err_max * (6 / Real.log (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hinv_k hBerr_max_pos.le
        _ = (6 * B_err_max / Real.log (n : ℝ)) * 1 := by ring
        _ ≤ (6 * B_err_max / Real.log (n : ℝ)) * Real.log (Real.log (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hll_ge1 (by positivity)
        _ = 6 * B_err_max * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by ring
    have herr2 : |p_fin (m + 1 + j.1) - p_lim (m + 1 + j.1)| ≤
        C_opt * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
      have hb2 := (hp_bds _ hjW).2
      calc |p_fin (m + 1 + j.1) - p_lim (m + 1 + j.1)|
          ≤ C_opt / (phaseNat n : ℝ) := hb2
        _ ≤ C_opt / Real.log (n : ℝ) :=
            div_le_div_of_nonneg_left hCopt_pos.le hL_pos ha_ge_L
        _ = (C_opt / Real.log (n : ℝ)) * 1 := (mul_one _).symm
        _ ≤ (C_opt / Real.log (n : ℝ)) * Real.log (Real.log (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hll_ge1 (div_nonneg hCopt_pos.le hL_pos.le)
        _ = C_opt * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by ring
    have herr3 : |p_lim (m + 1 + j.1) - gibbsProbS0M M lam ((j.1 : ℤ) + 1)| ≤
        (4 * ((1 + M : ℕ) : ℝ) * (C_corr + 1) / wMasterCstar M) *
          Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
      rw [← hp_sh]
      have hplim_eq : p_lim (m + 1 + j.1) = wProb_v13 W g_sc l_lim (m + 1 + j.1) := rfl
      rw [hplim_eq]
      exact (hp_lip_g.trans (mul_le_mul_of_nonneg_left hl_dist (by positivity))).trans_eq (by ring)
    calc |(kv j : ℝ) / (k : ℝ) - gibbsProbS0M M lam ((j.1 : ℤ) + 1)|
        ≤ |(kv j : ℝ) / (k : ℝ) - p_fin (m + 1 + j.1)| +
            (|p_fin (m + 1 + j.1) - p_lim (m + 1 + j.1)| +
              |p_lim (m + 1 + j.1) - gibbsProbS0M M lam ((j.1 : ℤ) + 1)|) :=
          (abs_sub_le _ _ _).trans (add_le_add le_rfl (abs_sub_le _ _ _))
      _ ≤ C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
          have hsum3 := add_le_add herr1 (add_le_add herr2 herr3)
          refine hsum3.trans ?_
          have hid :
              6 * B_err_max * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) +
                (C_opt * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) +
                  4 * ((1 + M : ℕ) : ℝ) * (C_corr + 1) / wMasterCstar M *
                    Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) =
              (4 * ((1 + M : ℕ) : ℝ) * (C_corr + 1) / wMasterCstar M + C_opt + 6 * B_err_max) *
                (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) := by ring
          rw [hid, ← mul_div_assoc]
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith only [hCp_def]) (by linarith only [hll_ge1])) hL_pos.le
  exact ⟨kv, kp, hblock_eq, hmass_eq, fun j ↦ ⟨(hkv_props j).1, (hkv_props j).2.1⟩,
    fun _ ↦ rfl, hkp_part.trans hblock_eq, hkp_mass, hkp_unm, hkp_sgn,
    fun P ↦ ⟨by rw [hblock_eq] at hkp_P; exact (hkp_P P).1, (hkp_P P).2⟩,
    fun G ↦ ⟨by rw [hblock_eq] at hkp_G; exact (hkp_G G).1,
      by rw [hblock_eq] at hkp_G; exact (hkp_G G).2⟩,
    hratio_lam, hlog_unm_ge⟩

/-- **Proposition 5.3(i)–(ii) in `Regime U` (`main.tex` lines 817–866, eq. `(5.17)`):**
for every `M ≥ 7`, there exist deterministic `M`-dependent constants `C_corr > 0`, `c_star > 0`,
`c_Z > 0`, and `C_p > 0` such that eventually across all `m ∈ {0, 1}`:
1. the finite-window phase objectives `𝓛_{S_{m, M}}(n, ·) + (log 2) · = 0` and
   `𝓛_{S_{m, M}}(n, ·) = 0` have unique corridor roots `r_co, r_ch`;
2. whenever `δ_n + m ≤ 1 + δ_*`, `M_{S_{0, M}}(λ) = T_{δ_n + m}` has a unique tilt `λ`;
3. at `k_co := ⌈r_co⌉ + 16` and `k_ch := ⌈r_ch⌉ + ⌈log n⌉`, there exist integer profiles
   `k_co_vec, k_ch_vec : Fin M → ℕ` and embedded `ColoringProfile (phaseNat n)` witnesses
   `kp_co, kp_ch` satisfying exact class-count & vertex-mass conservation, strict linear coordinate
   positivity `≥ c_star`, `O_M((log log n) / log n)` Gibbs-ratio accuracy,
   `log E[Z_{k_co}^mk] ≥ c_Z (log n)²`, and `log E[X̄_{k_ch}] ≥ c_Z (log n)³`. -/
theorem eventually_selectedProfiles_prop53_regimeU
    {M : ℕ} (hM : 7 ≤ M) :
    ∃ C_corr c_star c_Z C_p : ℝ,
      0 < C_corr ∧ 0 < c_star ∧ 0 < c_Z ∧ 0 < C_p ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ {m : ℕ}, m ≤ 1 →
          let u : Fin M → ℕ := fun j ↦ phaseNat n - (m + 1 + j.1)
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
          (phaseDelta n + (m : ℝ) ≤ 1 + deltaStar →
            ∃! lam : ℝ, meanS0M M lam = phaseTarget (phaseDelta n + (m : ℝ))) ∧
          (∀ {r_co r_ch : ℝ},
            r_co ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) →
            obj_win (Real.log 2) r_co = 0 →
            r_ch ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) →
            obj_win 0 r_ch = 0 →
            let k_co : ℕ := Nat.ceil r_co + 16
            let k_ch : ℕ := Nat.ceil r_ch + Nat.ceil (Real.log (n : ℝ))
            1 ≤ k_co ∧ (k_co : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ∧
            1 ≤ k_ch ∧ (k_ch : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ∧
            ∃ (k_co_vec k_ch_vec : Fin M → ℕ) (kp_co kp_ch : ColoringProfile (phaseNat n)),
              selectedBlockCount k_co_vec = k_co ∧
              selectedVertexMass u k_co_vec = n ∧
              selectedBlockCount k_ch_vec = k_ch ∧
              selectedVertexMass u k_ch_vec = n ∧
              (∀ j : Fin M, 0 < k_co_vec j ∧ c_star ≤ (k_co_vec j : ℝ) / (k_co : ℝ)) ∧
              (∀ j : Fin M, 0 < k_ch_vec j ∧ c_star ≤ (k_ch_vec j : ℝ) / (k_ch : ℝ)) ∧
              (∀ idx : Fin (phaseNat n),
                kp_co idx = ∑ j : Fin M, if u j = idx.1 + 1 then k_co_vec j else 0) ∧
              (∀ idx : Fin (phaseNat n),
                kp_ch idx = ∑ j : Fin M, if u j = idx.1 + 1 then k_ch_vec j else 0) ∧
              ColoringProfile.partCount kp_co = k_co ∧
              ColoringProfile.vertexMass kp_co = n ∧
              (signedProfileExpectation n kp_co).toReal = completeSignedFirstMoment u k_co_vec ∧
              (∀ P : ProfilePartition n kp_co,
                P.1.parts.card = k_co ∧
                ∀ D ∈ P.1.parts, phaseNat n - (m + M) ≤ D.card ∧ D.card ≤ phaseNat n - (m + 1)) ∧
              (∀ G : LabeledGraph n,
                (∃ P : ProfilePartition n kp_co, G ∈ partitionCocoloringEvent P.1) →
                  cochromaticNumber G ≤ k_co) ∧
              ColoringProfile.partCount kp_ch = k_ch ∧
              ColoringProfile.vertexMass kp_ch = n ∧
              (profileColoringExpectation n kp_ch).toReal = completeUnmarkedFirstMoment u k_ch_vec ∧
              (∀ P : ProfilePartition n kp_ch,
                P.1.parts.card = k_ch ∧
                ∀ D ∈ P.1.parts, phaseNat n - (m + M) ≤ D.card ∧ D.card ≤ phaseNat n - (m + 1)) ∧
              (∀ G : LabeledGraph n,
                (∃ P : ProfilePartition n kp_ch, G ∈ partitionColoringEvent P.1) →
                  chromaticNumberNat G ≤ k_ch) ∧
              (∀ lam : ℝ, meanS0M M lam = phaseTarget (phaseDelta n + (m : ℝ)) →
                ∀ j : Fin M,
                  |(k_co_vec j : ℝ) / (k_co : ℝ) - gibbsProbS0M M lam ((j.1 : ℤ) + 1)| ≤
                    C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) ∧
                  |(k_ch_vec j : ℝ) / (k_ch : ℝ) - gibbsProbS0M M lam ((j.1 : ℤ) + 1)| ≤
                    C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) ∧
              c_Z * (Real.log (n : ℝ)) ^ 2 ≤ Real.log (completeSignedFirstMoment u k_co_vec) ∧
              c_Z * (Real.log (n : ℝ)) ^ 3 ≤ Real.log (completeUnmarkedFirstMoment u k_ch_vec)) := by
  obtain ⟨C_corr, _, hC_pos, _, hRoots_ev⟩ :=
    exists_pos_eventually_existsUnique_windowPhaseObjective_zero_logLogCorridor hM
  obtain ⟨Λ_M, c_star, C_opt, _, hc_pos, hCopt_pos, hLem32⟩ :=
    existsUnique_windowFiniteGibbsTilt_and_optimizer_bounds_lemma32_ii hM
  obtain ⟨K_slope, hK_pos, hSlope_ev⟩ :=
    (eventually_window_and_capped_phaseObjective_deriv_and_diff_lemma31 hM (C_corr + 1) (by positivity)).2
  have hwmc_pos : 0 < wMasterCstar M := by unfold wMasterCstar; positivity
  set B_err_max : ℝ := (((1 + M + 4) * M + 1 : ℕ) : ℝ) with hBerr_max_def
  have hBerr_max_pos : 0 < B_err_max := by rw [hBerr_max_def]; positivity
  clear_value B_err_max
  set C_round_max : ℝ :=
    (M : ℝ) * ((1 + |Real.log c_star|) * B_err_max + (((1 + M : ℕ) : ℝ) ^ 2 + 1) * B_err_max)
    with hCround_max_def
  clear_value C_round_max
  set c_Z : ℝ := 1 / (2 * Real.log 2) with hcZ_def
  have hcZ_pos : 0 < c_Z := by rw [hcZ_def]; have := Real.log_pos one_lt_two; positivity
  clear_value c_Z
  set C_p : ℝ := 4 * ((1 + M : ℕ) : ℝ) * (C_corr + 1) / wMasterCstar M + C_opt + 6 * B_err_max + 1 with hCp_def
  have hCp_pos : 0 < C_p := by rw [hCp_def]; positivity
  clear_value C_p
  refine ⟨C_corr, c_star, c_Z, C_p, hC_pos, hc_pos, hcZ_pos, hCp_pos, ?_⟩
  have halpha_ev : ∀ᶠ n : ℕ in atTop, 4 * (1 + M) ^ 2 + 4 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (((4 * (1 + M) ^ 2 + 4 : ℕ) : ℝ)),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  have hk_thresh_ev : ∀ᶠ n : ℕ in atTop,
      6 * (B_err_max / c_star + 1) * Real.log (n : ℝ) ≤ (n : ℝ) ∧
      6 * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) := by
    have hdiv2 : Tendsto (fun x : ℝ ↦ (Real.log x) ^ 2 / x) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero
    set K_t : ℝ := max (6 * (B_err_max / c_star + 1)) 6
    have hKt_pos : 0 < K_t := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hm := (hdiv2.comp tendsto_natCast_atTop_atTop).eventually
      (Iic_mem_nhds (one_div_pos.mpr hKt_pos))
    filter_upwards [eventually_ge_atTop 4,
      tendsto_logOrder_atTop.eventually_ge_atTop 1, hm] with n hn4 hL1 hle
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hL_ge1 : (1 : ℝ) ≤ Real.log (n : ℝ) := hL1
    have h1 := (div_le_iff₀ hn_pos).mp hle
    have hmul := mul_le_mul_of_nonneg_left h1 hKt_pos.le
    have hcanc : K_t * (1 / K_t * (n : ℝ)) = (n : ℝ) := by field_simp [hKt_pos.ne']
    rw [hcanc] at hmul
    have hL_le_L2 : Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
      calc Real.log (n : ℝ) = Real.log (n : ℝ) * 1 := (mul_one _).symm
        _ ≤ Real.log (n : ℝ) * Real.log (n : ℝ) :=
            mul_le_mul_of_nonneg_left hL_ge1 (by linarith only [hL_ge1])
        _ = (Real.log (n : ℝ)) ^ 2 := (sq _).symm
    refine ⟨(mul_le_mul (le_max_left _ _) hL_le_L2 (by linarith only [hL_ge1]) hKt_pos.le).trans hmul,
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)).trans hmul⟩
  have hslope_dom : ∀ᶠ n : ℕ in atTop,
      K_slope * Real.log (Real.log (n : ℝ)) ≤ (1 / Real.log 2) * Real.log (n : ℝ) := by
    have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hb := logLogOrder_isLittleO_logOrder.bound (div_pos (one_div_pos.mpr hq_pos) hK_pos)
    filter_upwards [hb, tendsto_logOrder_atTop.eventually_ge_atTop 2,
      tendsto_logLogOrder_atTop.eventually_ge_atTop 1] with n hbn hL2 hll1
    dsimp [logOrder, logLogOrder] at hbn hL2 hll1
    rw [abs_of_pos (by linarith only [hll1]), abs_of_pos (by linarith only [hL2])] at hbn
    have hm := mul_le_mul_of_nonneg_left hbn hK_pos.le
    have hc : K_slope * ((1 / Real.log 2 / K_slope) * Real.log (n : ℝ)) =
        (1 / Real.log 2) * Real.log (n : ℝ) := by field_simp [hK_pos.ne', hq_pos.ne']
    linarith only [hm, hc]
  have hround_abs_ev : ∀ᶠ n : ℕ in atTop,
      C_round_max + (M : ℝ) * (1 + 2 * Real.log (n : ℝ)) ≤
        (1 / (2 * Real.log 2)) * (Real.log (n : ℝ)) ^ 2 := by
    have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    set K_abs : ℝ := 2 * Real.log 2 * (|C_round_max| + 3 * (M : ℝ) + 1)
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (max 2 K_abs)] with n hLn
    dsimp [logOrder] at hLn
    have hL2 : 2 ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hLn
    have hLK : K_abs ≤ Real.log (n : ℝ) := (le_max_right _ _).trans hLn
    have h1 : (|C_round_max| + 3 * (M : ℝ) + 1) * Real.log (n : ℝ) ≤
        (1 / (2 * Real.log 2)) * (Real.log (n : ℝ)) ^ 2 := by
      have hm := mul_le_mul_of_nonneg_right hLK
        (by positivity : 0 ≤ (1 / (2 * Real.log 2)) * Real.log (n : ℝ))
      dsimp [K_abs] at hm
      have hc : 2 * Real.log 2 * (|C_round_max| + 3 * (M : ℝ) + 1) *
          (1 / (2 * Real.log 2) * Real.log (n : ℝ)) =
          (|C_round_max| + 3 * (M : ℝ) + 1) * Real.log (n : ℝ) := by field_simp [hq_pos.ne']
      rw [hc] at hm
      exact hm.trans_eq (by ring)
    have hC_le : C_round_max ≤ |C_round_max| * Real.log (n : ℝ) :=
      (le_abs_self _).trans ((mul_one _).symm.le.trans
        (mul_le_mul_of_nonneg_left (by linarith only [hL2]) (abs_nonneg _)))
    have hM_le : (M : ℝ) * (1 + 2 * Real.log (n : ℝ)) ≤ 3 * (M : ℝ) * Real.log (n : ℝ) := by
      calc (M : ℝ) * (1 + 2 * Real.log (n : ℝ))
          ≤ (M : ℝ) * (3 * Real.log (n : ℝ)) :=
            mul_le_mul_of_nonneg_left (by linarith only [hL2]) (Nat.cast_nonneg M)
        _ = 3 * (M : ℝ) * Real.log (n : ℝ) := by ring
    linarith only [h1, hC_le, hM_le, hL2]
  filter_upwards [eventually_ge_atTop 8, hRoots_ev, hSlope_ev,
    eventually_corridor_pad_and_root_bounds_v13 C_corr hC_pos,
    eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc (C_corr + 1) (by positivity),
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    halpha_ev, hk_thresh_ev, hslope_dom, hround_abs_ev] with
    n hn8 hRoots hSlope hPad hTarIcc hPh halpha_n ⟨hk_th1, hk_th2⟩ hsl_dom hround_dom
    m hm u h_sc F_win obj_win
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL_ge2 : (2 : ℝ) ≤ Real.log (n : ℝ) := hPad.2.1
  have hL_pos : 0 < Real.log (n : ℝ) := by linarith only [hL_ge2]
  have hll_ge1 : (1 : ℝ) ≤ Real.log (Real.log (n : ℝ)) := hPad.2.2.1
  have ha_ge_4sq : 4 * (1 + M) ^ 2 ≤ phaseNat n := by omega
  have ha_ge_L : Real.log (n : ℝ) ≤ (phaseNat n : ℝ) := hPh.1
  have hexu_co := (hRoots m hm (Real.log 2) ⟨hq_pos.le, le_rfl⟩).2.1
  have hexu_ch := (hRoots m hm 0 ⟨le_rfl, hq_pos.le⟩).2.1
  clear hRoots
  have hexu_tilt : phaseDelta n + (m : ℝ) ≤ 1 + deltaStar →
      ∃! lam : ℝ, meanS0M M lam = phaseTarget (phaseDelta n + (m : ℝ)) := by
    intro htd_hi
    obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
    have htd_nn : 0 ≤ phaseDelta n + (m : ℝ) :=
      add_nonneg (phaseDelta_nonneg n) (Nat.cast_nonneg m)
    have htar_icc : phaseTarget (phaseDelta n + (m : ℝ)) ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) := by
      unfold phaseTarget; unfold deltaStar at htd_hi
      exact ⟨by linarith only [htd_hi, h2lo], by linarith only [htd_nn, h2hi]⟩
    let g_sc0 : ℕ → ℝ := fun i ↦ -Real.log 2 / 2 * (i : ℝ) ^ 2
    have hg0_bds : ∀ i ∈ Finset.Icc (0 + 1) (0 + M),
        -(((1 + M : ℕ) : ℝ) ^ 2 + 1) ≤ g_sc0 i ∧ g_sc0 i ≤ 0 := by
      intro i hi
      dsimp [g_sc0]
      have hsq : (i : ℝ) ^ 2 ≤ ((1 + M : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg i)
          (by exact_mod_cast (le_trans (Finset.mem_Icc.mp hi).2 (by omega : 0 + M ≤ 1 + M))) 2
      have hq_i : (Real.log 2 / 2) * (i : ℝ) ^ 2 ≤ 1 * ((1 + M : ℕ) : ℝ) ^ 2 :=
        mul_le_mul (by linarith [Real.log_two_lt_d9]) hsq (sq_nonneg _) zero_le_one
      have hq_nn : 0 ≤ (Real.log 2 / 2) * (i : ℝ) ^ 2 :=
        mul_nonneg (div_nonneg hq_pos.le zero_le_two) (sq_nonneg _)
      rw [show -Real.log 2 / 2 * (i : ℝ) ^ 2 = -((Real.log 2 / 2) * (i : ℝ) ^ 2) by ring]
      exact ⟨by linarith only [hq_i], by linarith only [hq_nn]⟩
    have hm0 := windowGibbs_master_v13 (m := 0) (M := M) (Nat.zero_le 1) hM hg0_bds
    obtain ⟨hexu_w, _⟩ := hm0.2.2.2.2 _ htar_icc
    have hmean_eq : ∀ l : ℝ, wMean_v13 (Finset.Icc (0 + 1) (0 + M)) g_sc0 l = meanS0M M l := by
      intro l
      have hsh0 := (wProb_and_wMean_shift_S0M_v13 (m := 0) (M := M) (by omega) l).2
      simpa only [Nat.cast_zero, zero_mul, sub_zero, add_zero] using hsh0
    simpa only [hmean_eq] using hexu_w
  refine ⟨hexu_co, hexu_ch, hexu_tilt, ?_⟩
  intro r_co r_ch hr_co hobj_co hr_ch hobj_ch k_co k_ch
  have hpad_shift := hPad.2.2.2.1
  obtain ⟨_, hk_co1, hk_co_ub, hk_co_lb, hk_co_r, hk_co_icc, _, _, _, _, _, htar_co, _⟩ :=
    hPad.2.2.2.2.2 r_co hr_co
  obtain ⟨_, _, _, _, _, _, hk_ch1, hk_ch_ub, hk_ch_lb, hk_ch_r, hk_ch_icc, _, htar_ch⟩ :=
    hPad.2.2.2.2.2 r_ch hr_ch
  clear hPad
  have hTco_17 := hTarIcc (k_co : ℝ) hk_co_icc
  have hTch_17 := hTarIcc (k_ch : ℝ) hk_ch_icc
  clear hTarIcc
  obtain ⟨⟨l_lim_co, hl_lim_co, _⟩, ⟨l_fin_co, hl_fin_co, _⟩, hsp_co⟩ :=
    hLem32 ha_ge_4sq hm ⟨hTco_17.1, by linarith only [hTco_17.2]⟩
  obtain ⟨-, -, -, -, hp_sum_co, hp_mean_co, hF_ent_co, -, hp_bds_co⟩ := hsp_co hl_lim_co hl_fin_co
  clear hsp_co
  obtain ⟨⟨l_lim_ch, hl_lim_ch, _⟩, ⟨l_fin_ch, hl_fin_ch, _⟩, hsp_ch⟩ :=
    hLem32 ha_ge_4sq hm ⟨hTch_17.1, by linarith only [hTch_17.2]⟩
  obtain ⟨-, -, -, -, hp_sum_ch, hp_mean_ch, hF_ent_ch, -, hp_bds_ch⟩ := hsp_ch hl_lim_ch hl_fin_ch
  clear hsp_ch hLem32
  obtain ⟨k_co_vec, kp_co, hco_blk, hco_mass, hco_pos, hco_kp_def, hco_part, hco_vm,
    _, hco_sgn, hco_P, hco_G, hco_rat, hco_log_unm⟩ :=
    build_selectedProfile_at_k_regimeU_v13 hm hM hn8 ha_ge_4sq ha_ge_L
      hC_pos hc_pos hCopt_pos hBerr_max_def hCround_max_def hCp_def
      hk_th1 hk_th2 hL_ge2 hll_ge1 hk_co1 hk_co_lb hTco_17 htar_co
      hl_lim_co hp_sum_co hp_mean_co hF_ent_co
      (fun i hi ↦ ⟨(hp_bds_co i hi).1, (hp_bds_co i hi).2.2⟩)
  obtain ⟨k_ch_vec, kp_ch, hch_blk, hch_mass, hch_pos, hch_kp_def, hch_part, hch_vm,
    hch_unm, _, hch_P, hch_G, hch_rat, hch_log_unm⟩ :=
    build_selectedProfile_at_k_regimeU_v13 hm hM hn8 ha_ge_4sq ha_ge_L
      hC_pos hc_pos hCopt_pos hBerr_max_def hCround_max_def hCp_def
      hk_th1 hk_th2 hL_ge2 hll_ge1 hk_ch1 hk_ch_lb hTch_17 htar_ch
      hl_lim_ch hp_sum_ch hp_mean_ch hF_ent_ch
      (fun i hi ↦ ⟨(hp_bds_ch i hi).1, (hp_bds_ch i hi).2.2⟩)
  have hobj_inc : ∀ (tau : ℝ), tau ∈ Set.Icc (0 : ℝ) (Real.log 2) →
      ∀ {a b : ℝ},
        a ∈ Set.Icc (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
                    (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n) →
        b ∈ Set.Icc (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
                    (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n) →
        a ≤ b →
        ((1 / Real.log 2) * (Real.log (n : ℝ)) ^ 2) * (b - a) ≤ obj_win tau b - obj_win tau a := by
    intro tau htau a b ha hb hab
    have hsl_tau := hSlope.1 hm tau htau
    have hsub : Set.Icc a b ⊆ Set.Icc
        (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n) :=
      fun x hx ↦ ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
    exact derivative_lower_bound_mul_sub_le_sub hab
      (fun x hx ↦ (hsl_tau x (hsub hx)).1.continuousAt.continuousWithinAt)
      (fun x hx ↦ (hsl_tau x (hsub (Ioo_subset_Icc_self hx))).1.differentiableWithinAt)
      (fun x hx ↦ by
        have hd_abs : |deriv (obj_win tau) x - (2 / Real.log 2) * (Real.log (n : ℝ)) ^ 2| ≤
            K_slope * Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) :=
          (hsl_tau x (hsub (Ioo_subset_Icc_self hx))).2
        have hd_b := (abs_le.mp hd_abs).1
        have hm_sl := mul_le_mul_of_nonneg_left hsl_dom hL_pos.le
        have e1 : Real.log (n : ℝ) * (K_slope * Real.log (Real.log (n : ℝ))) =
            K_slope * Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) := by ring
        have e2 : Real.log (n : ℝ) * ((1 / Real.log 2) * Real.log (n : ℝ)) =
            (1 / Real.log 2) * (Real.log (n : ℝ)) ^ 2 := by ring
        have e3 : 2 / Real.log 2 * (Real.log (n : ℝ)) ^ 2 =
            2 * ((1 / Real.log 2) * (Real.log (n : ℝ)) ^ 2) := by ring
        linarith only [hd_b, hm_sl, e1, e2, e3])
  clear hSlope
  have hr_co_icc : r_co ∈ Set.Icc
      (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n) :=
    ⟨by linarith only [hr_co.1, hpad_shift, hL_pos], by linarith only [hr_co.2, hpad_shift, hL_pos]⟩
  have hr_ch_icc : r_ch ∈ Set.Icc
      (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n) :=
    ⟨by linarith only [hr_ch.1, hpad_shift, hL_pos], by linarith only [hr_ch.2, hpad_shift, hL_pos]⟩
  have hobj_co_k : (16 / Real.log 2) * (Real.log (n : ℝ)) ^ 2 ≤ obj_win (Real.log 2) (k_co : ℝ) := by
    have hinc := hobj_inc (Real.log 2) ⟨hq_pos.le, le_rfl⟩ hr_co_icc hk_co_icc (by linarith only [hk_co_r])
    rw [hobj_co, sub_zero] at hinc
    have h16 : (16 : ℝ) ≤ (k_co : ℝ) - r_co := by linarith only [hk_co_r]
    calc (16 / Real.log 2) * (Real.log (n : ℝ)) ^ 2
        = ((1 / Real.log 2) * (Real.log (n : ℝ)) ^ 2) * 16 := by ring
      _ ≤ ((1 / Real.log 2) * (Real.log (n : ℝ)) ^ 2) * ((k_co : ℝ) - r_co) :=
          mul_le_mul_of_nonneg_left h16 (by positivity)
      _ ≤ obj_win (Real.log 2) (k_co : ℝ) := hinc
  have hlog_signed_co :
      c_Z * (Real.log (n : ℝ)) ^ 2 ≤ Real.log (completeSignedFirstMoment u k_co_vec) := by
    have hrel_sgn :
        Real.log (completeSignedFirstMoment u k_co_vec) =
          (k_co : ℝ) * Real.log 2 + Real.log (completeUnmarkedFirstMoment u k_co_vec) := by
      have hpos_s : 0 < completeSignedFirstMoment u k_co_vec := completeSignedFirstMoment_pos u k_co_vec
      unfold completeUnmarkedFirstMoment
      have h2_pos : 0 < (2 : ℝ) ^ k_co := by positivity
      have hsum_eq : ∑ j : Fin M, k_co_vec j = k_co := hco_blk
      rw [hsum_eq, Real.log_mul (inv_pos.mpr h2_pos).ne' hpos_s.ne', Real.log_inv, Real.log_pow]
      ring
    have hobj_rel : obj_win (Real.log 2) (k_co : ℝ) =
        (k_co : ℝ) * Real.log 2 + obj_win 0 (k_co : ℝ) := by
      dsimp [obj_win]; ring
    rw [hrel_sgn, hcZ_def]
    have hgap16 : (1 / (2 * Real.log 2)) * (Real.log (n : ℝ)) ^ 2 ≤
        (16 / Real.log 2) * (Real.log (n : ℝ)) ^ 2 -
          (1 / (2 * Real.log 2)) * (Real.log (n : ℝ)) ^ 2 := by
      have hnn : 0 ≤ (Real.log (n : ℝ)) ^ 2 / Real.log 2 := by positivity
      have e1 : (1 / (2 * Real.log 2)) * (Real.log (n : ℝ)) ^ 2 =
          (1 / 2) * ((Real.log (n : ℝ)) ^ 2 / Real.log 2) := by ring
      have e2 : (16 / Real.log 2) * (Real.log (n : ℝ)) ^ 2 =
          16 * ((Real.log (n : ℝ)) ^ 2 / Real.log 2) := by ring
      linarith only [hnn, e1, e2]
    have hco_log_unm' :
        obj_win 0 (k_co : ℝ) - C_round_max - (M : ℝ) * (1 + 2 * Real.log (n : ℝ)) ≤
          Real.log (completeUnmarkedFirstMoment u k_co_vec) := hco_log_unm
    linarith only [hco_log_unm', hobj_co_k, hobj_rel, hround_dom, hgap16]
  have hobj_ch_k : (1 / Real.log 2) * (Real.log (n : ℝ)) ^ 3 ≤ obj_win 0 (k_ch : ℝ) := by
    have hinc := hobj_inc 0 ⟨le_rfl, hq_pos.le⟩ hr_ch_icc hk_ch_icc (by linarith only [hk_ch_r, hL_pos])
    rw [hobj_ch, sub_zero] at hinc
    have hL_diff : Real.log (n : ℝ) ≤ (k_ch : ℝ) - r_ch := by linarith only [hk_ch_r]
    calc (1 / Real.log 2) * (Real.log (n : ℝ)) ^ 3
        = ((1 / Real.log 2) * (Real.log (n : ℝ)) ^ 2) * Real.log (n : ℝ) := by ring
      _ ≤ ((1 / Real.log 2) * (Real.log (n : ℝ)) ^ 2) * ((k_ch : ℝ) - r_ch) :=
          mul_le_mul_of_nonneg_left hL_diff (by positivity)
      _ ≤ obj_win 0 (k_ch : ℝ) := hinc
  have hlog_unm_ch :
      c_Z * (Real.log (n : ℝ)) ^ 3 ≤ Real.log (completeUnmarkedFirstMoment u k_ch_vec) := by
    have hL2_le_L3 : (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ 3 := by
      calc (Real.log (n : ℝ)) ^ 2 = (Real.log (n : ℝ)) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (Real.log (n : ℝ)) ^ 2 * Real.log (n : ℝ) :=
            mul_le_mul_of_nonneg_left (by linarith only [hL_ge2]) (sq_nonneg _)
        _ = (Real.log (n : ℝ)) ^ 3 := by ring
    have hround_L3 :
        C_round_max + (M : ℝ) * (1 + 2 * Real.log (n : ℝ)) ≤
          (1 / (2 * Real.log 2)) * (Real.log (n : ℝ)) ^ 3 :=
      hround_dom.trans (mul_le_mul_of_nonneg_left hL2_le_L3 (by positivity))
    rw [hcZ_def]
    have hhalf_id :
        (1 / Real.log 2) * (Real.log (n : ℝ)) ^ 3 -
            (1 / (2 * Real.log 2)) * (Real.log (n : ℝ)) ^ 3 =
          (1 / (2 * Real.log 2)) * (Real.log (n : ℝ)) ^ 3 := by ring
    have hch_log_unm' :
        obj_win 0 (k_ch : ℝ) - C_round_max - (M : ℝ) * (1 + 2 * Real.log (n : ℝ)) ≤
          Real.log (completeUnmarkedFirstMoment u k_ch_vec) := hch_log_unm
    linarith only [hch_log_unm', hobj_ch_k, hround_L3, hhalf_id]
  exact ⟨hk_co1, hk_co_ub, hk_ch1, hk_ch_ub, k_co_vec, k_ch_vec, kp_co, kp_ch,
    hco_blk, hco_mass, hch_blk, hch_mass, hco_pos, hch_pos,
    hco_kp_def, hch_kp_def,
    hco_part, hco_vm, hco_sgn, hco_P, fun G ↦ (hco_G G).1,
    hch_part, hch_vm, hch_unm, hch_P, fun G ↦ (hch_G G).2,
    fun lam hlam j ↦ ⟨hco_rat lam hlam j, hch_rat lam hlam j⟩,
    hlog_signed_co, hlog_unm_ch⟩

private theorem reducedTarget_mem_Icc_and_Ioo_v13
    {theta T : ℝ} (htheta : theta ∈ Set.Icc (0 : ℝ) (1 / 20)) (hT : T ∈ KcapInterval) :
    (T - theta) / (1 - theta) ∈ Set.Icc (11 / 4 : ℝ) (9 / 2) ∧
      (T - theta) / (1 - theta) ∈ Set.Ioo (9 / 4 : ℝ) (9 / 2) := by
  have h1m_pos : 0 < 1 - theta := by linarith only [htheta.2]
  obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
  obtain ⟨hT_lo, hT_hi⟩ := hT
  have hicc : (T - theta) / (1 - theta) ∈ Set.Icc (11 / 4 : ℝ) (17 / 4) := by
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ h1m_pos]; linarith only [htheta.1, htheta.2, hT_lo, h2lo]
    · rw [div_le_iff₀ h1m_pos]; linarith only [htheta.1, htheta.2, hT_hi, h2hi]
  exact ⟨⟨hicc.1, by linarith only [hicc.2]⟩,
    ⟨by linarith only [hicc.1], by linarith only [hicc.2]⟩⟩

private def capClipTheta_v13 (M : ℕ) (p1Bar : ℝ) : ℝ :=
  let Λ_tail := wMasterLambda (M - 1)
  let B_sc := ((1 + M : ℕ) : ℝ) ^ 2 + 1
  let CL_tail := Λ_tail * (M : ℝ) + B_sc + Real.log (M : ℝ) + 2
  2 * (1 + |Real.log (p1Bar / 2)|) + 2 + 16 * Λ_tail + CL_tail + 5 * Λ_tail

private theorem Fcap_theta_diff_le_v13
    {alpha M k : ℕ} (hM : 8 ≤ M) (ha_ge_4sq_p : 4 * (1 + (M - 1)) ^ 2 ≤ alpha)
    (hk1 : 1 ≤ k)
    {p1Bar θ_n T_k : ℝ} (hp1 : p1Bar ∈ Set.Ioc (0 : ℝ) (1 / 40))
    (hθ_lo : p1Bar / 2 ≤ θ_n) (hθ_hi : θ_n ≤ p1Bar)
    (hθ_diff : |θ_n - p1Bar| ≤ 1 / (k : ℝ))
    (hTk_cap : T_k ∈ KcapInterval) :
    let h_sc : ℕ → ℝ := fun i ↦
      Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) -
        Real.log 2 / 2 * (i : ℝ) ^ 2
    let F_cap : ℝ → ℝ → ℝ := fun theta T ↦
      binEntropy theta - Real.log 2 / 2 * theta +
        (1 - theta) * (⨅ l : ℝ,
          (Real.log (∑ i ∈ Finset.Icc 2 M, Real.exp (l * (i : ℝ) + h_sc i)) -
            l * ((T - theta) / (1 - theta))))
    (k : ℝ) * |F_cap θ_n T_k - F_cap p1Bar T_k| ≤ capClipTheta_v13 M p1Bar := by
  intro h_sc F_cap
  have hMp7 : 7 ≤ M - 1 := by omega
  have h1_Mp : 1 + (M - 1) = M := by omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  set Λ_tail : ℝ := wMasterLambda (M - 1)
  have hΛt_pos : 0 < Λ_tail := by
    have : 0 < Real.log (8 * ((M - 1 : ℕ) : ℝ) ^ 2 + 1) := Real.log_pos (by
      have : (0 : ℝ) < ((M - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < M - 1 by omega)
      nlinarith)
    dsimp [Λ_tail]; unfold wMasterLambda wMasterBsc; positivity
  set B_sc : ℝ := ((1 + M : ℕ) : ℝ) ^ 2 + 1
  have hBsc_pos : 0 < B_sc := by dsimp [B_sc]; positivity
  set CL_tail : ℝ := Λ_tail * (M : ℝ) + B_sc + Real.log (M : ℝ) + 2
  have hClip_pos : 0 < capClipTheta_v13 M p1Bar := by
    have : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
    unfold capClipTheta_v13; positivity
  have hθ_120 : θ_n ∈ Set.Icc (0 : ℝ) (1 / 20) :=
    ⟨by linarith only [hp1.1, hθ_lo], by linarith only [hp1.2, hθ_hi]⟩
  have hp1_120 : p1Bar ∈ Set.Icc (0 : ℝ) (1 / 20) :=
    ⟨hp1.1.le, by linarith only [hp1.2]⟩
  have h1mθ_pos : 0 < 1 - θ_n := by linarith only [hθ_hi, hp1.2]
  have h1mθ_ge : 39 / 40 ≤ 1 - θ_n := by linarith only [hθ_hi, hp1.2]
  have hθ_icc : θ_n ∈ Set.Icc (p1Bar / 2) 1 := ⟨hθ_lo, by linarith only [hθ_hi, hp1.2]⟩
  have hp1_icc : p1Bar ∈ Set.Icc (p1Bar / 2) 1 := ⟨by linarith only [hp1.1], by linarith only [hp1.2]⟩
  have h1mθ_icc : 1 - θ_n ∈ Set.Icc (p1Bar / 2) 1 :=
    ⟨by linarith only [hp1.2, h1mθ_ge], by linarith only [hp1.1, hθ_lo]⟩
  have h1mp1_icc : 1 - p1Bar ∈ Set.Icc (p1Bar / 2) 1 :=
    ⟨by linarith only [hp1.2], by linarith only [hp1.1]⟩
  have hbin_diff : |binEntropy θ_n - binEntropy p1Bar| ≤
      2 * (1 + |Real.log (p1Bar / 2)|) * |θ_n - p1Bar| := by
    unfold binEntropy
    have hb1 := abs_mul_log_sub_le_of_mem_Icc_v13 (half_pos hp1.1) hθ_icc hp1_icc
    have hb2 := abs_mul_log_sub_le_of_mem_Icc_v13 (half_pos hp1.1) h1mθ_icc h1mp1_icc
    rw [show (1 - θ_n) - (1 - p1Bar) = -(θ_n - p1Bar) by ring, abs_neg] at hb2
    rw [show (-θ_n * Real.log θ_n - (1 - θ_n) * Real.log (1 - θ_n)) -
        (-p1Bar * Real.log p1Bar - (1 - p1Bar) * Real.log (1 - p1Bar)) =
      -(θ_n * Real.log θ_n - p1Bar * Real.log p1Bar) -
        ((1 - θ_n) * Real.log (1 - θ_n) - (1 - p1Bar) * Real.log (1 - p1Bar)) by ring]
    calc |-(θ_n * Real.log θ_n - p1Bar * Real.log p1Bar) -
            ((1 - θ_n) * Real.log (1 - θ_n) - (1 - p1Bar) * Real.log (1 - p1Bar))|
        ≤ |-(θ_n * Real.log θ_n - p1Bar * Real.log p1Bar)| +
            |(1 - θ_n) * Real.log (1 - θ_n) - (1 - p1Bar) * Real.log (1 - p1Bar)| := abs_sub _ _
      _ ≤ 2 * (1 + |Real.log (p1Bar / 2)|) * |θ_n - p1Bar| := by
          rw [abs_neg]; linarith only [hb1, hb2]
  set u_n : ℝ := (T_k - θ_n) / (1 - θ_n)
  set u_bar : ℝ := (T_k - p1Bar) / (1 - p1Bar)
  have hubar_icc : u_bar ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) := by
    have hc := (reducedTarget_mem_Icc_and_Ioo_v13 hp1_120 hTk_cap).1
    exact ⟨by linarith only [hc.1], hc.2⟩
  have hu_diff : |u_n - u_bar| ≤ 16 * |θ_n - p1Bar| := by
    have h1mp1_pos : 0 < 1 - p1Bar := by linarith only [hp1.2]
    have hid_u : u_n - u_bar = (T_k - 1) * (θ_n - p1Bar) / ((1 - θ_n) * (1 - p1Bar)) := by
      dsimp [u_n, u_bar]; field_simp [h1mθ_pos.ne', h1mp1_pos.ne']; ring
    obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
    have hTk1 : |T_k - 1| ≤ 4 := by
      obtain ⟨hlo, hhi⟩ := hTk_cap
      rw [abs_le]; exact ⟨by linarith only [hlo, h2lo], by linarith only [hhi, h2hi]⟩
    have hden_ge : 1 / 4 ≤ (1 - θ_n) * (1 - p1Bar) :=
      le_trans (by norm_num : (1 / 4 : ℝ) ≤ (39 / 40) * (39 / 40))
        (mul_le_mul h1mθ_ge (by linarith only [hp1.2]) (by norm_num) h1mθ_pos.le)
    rw [hid_u, abs_div, abs_mul, abs_of_pos (mul_pos h1mθ_pos h1mp1_pos)]
    calc |T_k - 1| * |θ_n - p1Bar| / ((1 - θ_n) * (1 - p1Bar))
        ≤ (4 * |θ_n - p1Bar|) / (1 / 4 : ℝ) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hTk1 (abs_nonneg _))
            (by norm_num) hden_ge
      _ = 16 * |θ_n - p1Bar| := by ring
  set W_tail := Finset.Icc (1 + 1) (1 + (M - 1))
  let F_t_fn : ℝ → ℝ := fun v ↦ ⨅ l : ℝ, (Real.log (wPart_v13 W_tail h_sc l) - l * v)
  have hsc_wt := h_sc_window_bounds_v13 (m' := 1) (M' := M - 1) le_rfl ha_ge_4sq_p
  have hm_wt := windowGibbs_master_v13 (m := 1) (M := M - 1) le_rfl hMp7 hsc_wt
  have hspec_wt := hm_wt.2.2.2.2
  clear hm_wt
  have hun_sub : u_n ∈ Set.Icc (11 / 4 : ℝ) (17 / 4) := by
    obtain ⟨_, h2hi⟩ := two_div_log_two_bounds
    have hc := (reducedTarget_mem_Icc_and_Ioo_v13 hθ_120 hTk_cap).1
    refine ⟨hc.1, ?_⟩
    dsimp [u_n]; rw [div_le_iff₀ h1mθ_pos]
    linarith only [hθ_120.1, hθ_120.2, hTk_cap.2, h2hi]
  have hubar_sub : u_bar ∈ Set.Icc (11 / 4 : ℝ) (17 / 4) := by
    obtain ⟨_, h2hi⟩ := two_div_log_two_bounds
    have hc := (reducedTarget_mem_Icc_and_Ioo_v13 hp1_120 hTk_cap).1
    refine ⟨hc.1, ?_⟩
    dsimp [u_bar]; rw [div_le_iff₀ (by linarith only [hp1_120.2])]
    linarith only [hp1_120.1, hp1_120.2, hTk_cap.2, h2hi]
  have hFt_diff : |F_t_fn u_n - F_t_fn u_bar| ≤ Λ_tail * |u_n - u_bar| := by
    have hd_on : ∀ v ∈ Set.Icc (11 / 4 : ℝ) (17 / 4),
        ∃ lv : ℝ, ‖-lv‖ ≤ Λ_tail ∧ HasDerivWithinAt F_t_fn (-lv) (Set.Icc (11 / 4) (17 / 4)) v := by
      intro v hv
      have hv_ioo : v ∈ Set.Ioo (9 / 4 : ℝ) (9 / 2) :=
        ⟨by linarith only [hv.1], by linarith only [hv.2]⟩
      obtain ⟨⟨lfv, hlfv, _⟩, hsp_v⟩ := hspec_wt v (Ioo_subset_Icc_self hv_ioo)
      have hlf_icc := (hsp_v lfv hlfv).1
      have hd_v := hasDerivAt_wDual_v13 (m := 1) (M := M - 1) le_rfl hMp7 hsc_wt hv_ioo hlfv
      exact ⟨lfv, by rw [Real.norm_eq_abs, abs_neg]; exact abs_le.mpr hlf_icc,
        hd_v.hasDerivWithinAt⟩
    let d_pick : ℝ → ℝ := fun v ↦
      if hv : v ∈ Set.Icc (11 / 4 : ℝ) (17 / 4) then -(hd_on v hv).choose else 0
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := F_t_fn) (f' := d_pick)
      (fun v hv ↦ by simp only [d_pick, dif_pos hv]; exact (hd_on v hv).choose_spec.2)
      (fun v hv ↦ by simp only [d_pick, dif_pos hv]; exact (hd_on v hv).choose_spec.1)
      (convex_Icc (11 / 4) (17 / 4)) hubar_sub hun_sub
    simpa only [Real.norm_eq_abs] using hmvt
  have hFt_ubar_abs : |F_t_fn u_bar| ≤ CL_tail + 5 * Λ_tail := by
    obtain ⟨⟨lf_b, hlf_b, _⟩, hsp_b⟩ := hspec_wt u_bar hubar_icc
    obtain ⟨hlf_b_icc, hFb_eq, -, -⟩ := hsp_b lf_b hlf_b
    clear hsp_b hspec_wt
    have hFb_eq' : F_t_fn u_bar = Real.log (wPart_v13 W_tail h_sc lf_b) - lf_b * u_bar := hFb_eq
    rw [hFb_eq']
    have hlf_abs : |lf_b| ≤ Λ_tail := abs_le.mpr hlf_b_icc
    have h2_in : 2 ∈ W_tail := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    have hcard_wt : W_tail.card = M - 1 := by dsimp [W_tail]; rw [Nat.card_Icc]; omega
    have hsc_2 : -(((1 + (M - 1) : ℕ) : ℝ) ^ 2 + 1) ≤ h_sc 2 := (hsc_wt 2 h2_in).1
    have hZ_lo : Real.exp (-Λ_tail * (M : ℝ) - B_sc) ≤ wPart_v13 W_tail h_sc lf_b := by
      calc Real.exp (-Λ_tail * (M : ℝ) - B_sc)
          ≤ Real.exp (lf_b * (2 : ℝ) + h_sc 2) := by
            apply Real.exp_le_exp.mpr
            have h2M : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 2 ≤ M by omega)
            have hp2 : |lf_b * (2 : ℝ)| ≤ Λ_tail * (M : ℝ) := by
              rw [abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)]
              exact mul_le_mul hlf_abs h2M zero_le_two hΛt_pos.le
            have hB_le : ((1 + (M - 1) : ℕ) : ℝ) ^ 2 + 1 ≤ B_sc := by
              dsimp [B_sc]
              have hsq : ((1 + (M - 1) : ℕ) : ℝ) ^ 2 ≤ ((1 + M : ℕ) : ℝ) ^ 2 :=
                pow_le_pow_left₀ (Nat.cast_nonneg _)
                  (by exact_mod_cast (show 1 + (M - 1) ≤ 1 + M by omega)) 2
              linarith only [hsq]
            have hp2_lo := (abs_le.mp hp2).1
            linarith only [hp2_lo, hsc_2, hB_le]
        _ ≤ wPart_v13 W_tail h_sc lf_b :=
            Finset.single_le_sum (f := fun i : ℕ ↦ Real.exp (lf_b * (i : ℝ) + h_sc i))
              (fun _ _ ↦ (Real.exp_pos _).le) h2_in
    have hZ_hi : wPart_v13 W_tail h_sc lf_b ≤ (M : ℝ) * Real.exp (Λ_tail * (M : ℝ)) := by
      calc wPart_v13 W_tail h_sc lf_b
          ≤ ∑ _i ∈ W_tail, Real.exp (Λ_tail * (M : ℝ)) := by
            refine Finset.sum_le_sum fun i hi ↦ Real.exp_le_exp.mpr ?_
            have hi_le : (i : ℝ) ≤ (M : ℝ) := by
              exact_mod_cast (le_trans (Finset.mem_Icc.mp hi).2 (by omega : 1 + (M - 1) ≤ M))
            have hp_i : lf_b * (i : ℝ) ≤ Λ_tail * (M : ℝ) :=
              (mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg i)).trans
                (mul_le_mul hlf_abs hi_le (Nat.cast_nonneg i) hΛt_pos.le)
            have hsc_i : h_sc i ≤ 0 := (hsc_wt i hi).2
            linarith only [hp_i, hsc_i]
        _ = ((M - 1 : ℕ) : ℝ) * Real.exp (Λ_tail * (M : ℝ)) := by
            rw [Finset.sum_const, hcard_wt, nsmul_eq_mul]
        _ ≤ (M : ℝ) * Real.exp (Λ_tail * (M : ℝ)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast (show M - 1 ≤ M by omega)) (Real.exp_pos _).le
    have hZ_pos := wPart_v13_pos ⟨2, h2_in⟩ h_sc lf_b
    have hlog_lo := Real.log_le_log (Real.exp_pos _) hZ_lo
    have hlog_hi := Real.log_le_log hZ_pos hZ_hi
    rw [Real.log_exp] at hlog_lo
    rw [Real.log_mul (by exact_mod_cast (show 0 < M by omega) : (0 : ℝ) < M).ne' (Real.exp_pos _).ne',
      Real.log_exp] at hlog_hi
    have hlog_abs : |Real.log (wPart_v13 W_tail h_sc lf_b)| ≤ CL_tail := by
      rw [abs_le]; dsimp [CL_tail]
      have hlogM_pos : 0 < Real.log (M : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < M by omega))
      exact ⟨by linarith only [hlog_lo, hBsc_pos, hlogM_pos],
        by linarith only [hlog_hi, hBsc_pos, hlogM_pos]⟩
    have hlfu : |lf_b * u_bar| ≤ 5 * Λ_tail := by
      have hub_pos : 0 < u_bar := by linarith only [hubar_icc.1]
      rw [abs_mul, abs_of_pos hub_pos]
      exact (mul_le_mul hlf_abs (show u_bar ≤ 5 by linarith only [hubar_icc.2])
        hub_pos.le hΛt_pos.le).trans_eq (mul_comm _ 5)
    exact (abs_sub _ _).trans (add_le_add hlog_abs hlfu)
  have hFcap_decomp :
      F_cap θ_n T_k - F_cap p1Bar T_k =
        (binEntropy θ_n - binEntropy p1Bar) - Real.log 2 / 2 * (θ_n - p1Bar) +
          (1 - θ_n) * (F_t_fn u_n - F_t_fn u_bar) - (θ_n - p1Bar) * F_t_fn u_bar := by
    dsimp [F_cap, F_t_fn, wPart_v13, W_tail, u_n, u_bar]
    rw [h1_Mp]; ring
  have htot_diff : |F_cap θ_n T_k - F_cap p1Bar T_k| ≤ capClipTheta_v13 M p1Bar * |θ_n - p1Bar| := by
    rw [hFcap_decomp]
    have hq2 : |Real.log 2 / 2 * (θ_n - p1Bar)| ≤ 2 * |θ_n - p1Bar| := by
      rw [abs_mul, abs_of_pos (div_pos hq_pos two_pos)]
      exact mul_le_mul_of_nonneg_right (by linarith [Real.log_two_lt_d9]) (abs_nonneg _)
    have ht1 : |(1 - θ_n) * (F_t_fn u_n - F_t_fn u_bar)| ≤ 16 * Λ_tail * |θ_n - p1Bar| := by
      rw [abs_mul, abs_of_pos h1mθ_pos]
      have h1m_le1 : 1 - θ_n ≤ 1 := by linarith only [hθ_120.1]
      calc (1 - θ_n) * |F_t_fn u_n - F_t_fn u_bar|
          ≤ 1 * (Λ_tail * (16 * |θ_n - p1Bar|)) :=
            mul_le_mul h1m_le1 (hFt_diff.trans (mul_le_mul_of_nonneg_left hu_diff hΛt_pos.le))
              (abs_nonneg _) zero_le_one
        _ = 16 * Λ_tail * |θ_n - p1Bar| := by ring
    have ht2 : |(θ_n - p1Bar) * F_t_fn u_bar| ≤ (CL_tail + 5 * Λ_tail) * |θ_n - p1Bar| := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hFt_ubar_abs (abs_nonneg _)
    have htri1 := abs_sub ((binEntropy θ_n - binEntropy p1Bar) - Real.log 2 / 2 * (θ_n - p1Bar) +
      (1 - θ_n) * (F_t_fn u_n - F_t_fn u_bar)) ((θ_n - p1Bar) * F_t_fn u_bar)
    have htri2 := abs_add_le ((binEntropy θ_n - binEntropy p1Bar) - Real.log 2 / 2 * (θ_n - p1Bar))
      ((1 - θ_n) * (F_t_fn u_n - F_t_fn u_bar))
    have htri3 := abs_sub (binEntropy θ_n - binEntropy p1Bar) (Real.log 2 / 2 * (θ_n - p1Bar))
    have hid_c :
        2 * (1 + |Real.log (p1Bar / 2)|) * |θ_n - p1Bar| + 2 * |θ_n - p1Bar| +
          16 * Λ_tail * |θ_n - p1Bar| + (CL_tail + 5 * Λ_tail) * |θ_n - p1Bar| =
        capClipTheta_v13 M p1Bar * |θ_n - p1Bar| := by
      dsimp [capClipTheta_v13, CL_tail, B_sc, Λ_tail]; ring
    linarith only [htri1, htri2, htri3, hbin_diff, hq2, ht1, ht2, hid_c]
  calc (k : ℝ) * |F_cap θ_n T_k - F_cap p1Bar T_k|
      ≤ (k : ℝ) * (capClipTheta_v13 M p1Bar * (1 / (k : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (htot_diff.trans (mul_le_mul_of_nonneg_left hθ_diff hClip_pos.le)) hk_pos.le
    _ = capClipTheta_v13 M p1Bar := by field_simp [hk_pos.ne']

private theorem cappedTail_ratio_approx_v13
    {n M k : ℕ} (hM : 8 ≤ M)
    {p1Bar C_corr B_err_tail C_opt_tail C_p θ_n l_lim : ℝ}
    (hp1 : p1Bar ∈ Set.Ioc (0 : ℝ) (1 / 40))
    (hBerr_tail_pos : 0 < B_err_tail) (hCopt_pos : 0 < C_opt_tail)
    (hCp_ge :
      6 * B_err_tail + C_opt_tail +
        (2 * (M : ℝ) / wMasterCstar (M - 1)) * (4 * (C_corr + 1) + 96) + 6 ≤ C_p)
    (hL_ge2 : (2 : ℝ) ≤ Real.log (n : ℝ))
    (hll_ge1 : (1 : ℝ) ≤ Real.log (Real.log (n : ℝ)))
    (ha_ge_L : Real.log (n : ℝ) ≤ (phaseNat n : ℝ))
    (hk_th2 : 6 * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ))
    (hd : phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar)
    (hk1 : 1 ≤ k)
    (hk_lb : (n : ℝ) / (6 * Real.log (n : ℝ)) ≤ (k : ℝ))
    (hTk_cap : fourSizeTarget n (phaseNat n) (k : ℝ) ∈ KcapInterval)
    (htar_k : |fourSizeTarget n (phaseNat n) (k : ℝ) - phaseTarget (phaseDelta n)| ≤
      2 * (C_corr + 1) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
    (hθ_lo : p1Bar / 2 ≤ θ_n) (hθ_hi : θ_n ≤ p1Bar)
    (hθ_diff : |θ_n - p1Bar| ≤ 1 / (k : ℝ))
    {p_t_fin p_t_lim : ℕ → ℝ} {kv : Fin M → ℕ}
    (hkv0 : ∀ j : Fin M, j.1 = 0 → (kv j : ℝ) / (k : ℝ) = θ_n)
    (hl_lim_eq : wMean_v13 (Finset.Icc (1 + 1) (1 + (M - 1)))
      (fun i ↦ -Real.log 2 / 2 * (i : ℝ) ^ 2) l_lim =
        (fourSizeTarget n (phaseNat n) (k : ℝ) - θ_n) / (1 - θ_n))
    (hp_lim_def : ∀ i ∈ Finset.Icc (1 + 1) (1 + (M - 1)),
      p_t_lim i = wProb_v13 (Finset.Icc (1 + 1) (1 + (M - 1)))
        (fun i ↦ -Real.log 2 / 2 * (i : ℝ) ^ 2) l_lim i)
    (hp_t_approx : ∀ i ∈ Finset.Icc (1 + 1) (1 + (M - 1)),
      |p_t_fin i - p_t_lim i| ≤ C_opt_tail / (phaseNat n : ℝ))
    (hkv_approx : ∀ j : Fin M, j.1 ≠ 0 →
      |(kv j : ℝ) / (k : ℝ) - (1 - θ_n) * p_t_fin (1 + j.1)| ≤ B_err_tail / (k : ℝ)) :
    ∀ lamTilde : ℝ,
      meanS0M (M - 1) lamTilde = (phaseTarget (phaseDelta n) - 1) / (1 - p1Bar) →
      ∀ j : Fin M,
        |(kv j : ℝ) / (k : ℝ) - cappedGibbsProbS0M M p1Bar lamTilde ((j.1 : ℤ) + 1)| ≤
          C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
  intro lamTilde hlamT j
  have hMp7 : 7 ≤ M - 1 := by omega
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL_pos : 0 < Real.log (n : ℝ) := by linarith only [hL_ge2]
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hwmc_tail_pos : 0 < wMasterCstar (M - 1) := by unfold wMasterCstar; positivity
  have hθ_120 : θ_n ∈ Set.Icc (0 : ℝ) (1 / 20) :=
    ⟨by linarith only [hp1.1, hθ_lo], by linarith only [hp1.2, hθ_hi]⟩
  have hp1_120 : p1Bar ∈ Set.Icc (0 : ℝ) (1 / 20) :=
    ⟨hp1.1.le, by linarith only [hp1.2]⟩
  have h1mθ_pos : 0 < 1 - θ_n := by linarith only [hθ_hi, hp1.2]
  have h1mθ_ge : 39 / 40 ≤ 1 - θ_n := by linarith only [hθ_hi, hp1.2]
  have hinv_k : 1 / (k : ℝ) ≤ 6 / Real.log (n : ℝ) := by
    have hL_le_k : Real.log (n : ℝ) ≤ (k : ℝ) :=
      ((le_div_iff₀ (by positivity : (0 : ℝ) < 6 * Real.log (n : ℝ))).mpr
        (by
          have heq6 : Real.log (n : ℝ) * (6 * Real.log (n : ℝ)) = 6 * (Real.log (n : ℝ)) ^ 2 := by ring
          linarith only [hk_th2, heq6])).trans hk_lb
    rw [div_le_div_iff₀ hk_pos hL_pos]; linarith only [hL_le_k]
  by_cases hj0 : j.1 = 0
  · have hcap0 : cappedGibbsProbS0M M p1Bar lamTilde ((j.1 : ℤ) + 1) = p1Bar := by
      rw [hj0]; simp [cappedGibbsProbS0M]
    rw [hkv0 j hj0, hcap0]
    calc |θ_n - p1Bar| ≤ 1 / (k : ℝ) := hθ_diff
      _ ≤ 6 / Real.log (n : ℝ) := hinv_k
      _ ≤ (6 * Real.log (Real.log (n : ℝ))) / Real.log (n : ℝ) := by
          rw [div_le_div_iff_of_pos_right hL_pos]; linarith only [hll_ge1]
      _ ≤ C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
          apply div_le_div_of_nonneg_right _ hL_pos.le
          have h6_le : 6 ≤ C_p := by
            have hnn3 : 0 ≤ (2 * (M : ℝ) / wMasterCstar (M - 1)) * (4 * (C_corr + 1) + 96) := by
              have hC1_nn : 0 ≤ C_corr + 1 := by
                have htar_nn := le_trans (abs_nonneg _) htar_k
                have hm := (div_nonneg_iff.mp htar_nn)
                rcases hm with ⟨hnum, _⟩ | ⟨_, hden⟩
                · have hnum' := nonneg_of_mul_nonneg_left hnum (by linarith only [hll_ge1])
                  linarith only [hnum']
                · exfalso; linarith only [hL_pos, hden]
              positivity
            linarith only [hCp_ge, hBerr_tail_pos, hCopt_pos, hnn3]
          exact mul_le_mul_of_nonneg_right h6_le (by linarith only [hll_ge1])
  · let j' : Fin (M - 1) := ⟨j.1 - 1, by omega⟩
    have hcap_j : cappedGibbsProbS0M M p1Bar lamTilde ((j.1 : ℤ) + 1) =
        (1 - p1Bar) * gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1) := by
      have hne1 : ((j.1 : ℤ) + 1) ≠ 1 := by omega
      have h2M : 2 ≤ ((j.1 : ℤ) + 1) ∧ ((j.1 : ℤ) + 1) ≤ (M : ℤ) := ⟨by omega, by omega⟩
      have hsub1 : ((j.1 : ℤ) + 1) - 1 = (j'.1 : ℤ) + 1 := by dsimp [j']; omega
      simp only [cappedGibbsProbS0M, hne1, h2M, and_self, ↓reduceIte, hsub1]
    rw [hcap_j]
    set W_tail := Finset.Icc (1 + 1) (1 + (M - 1))
    let g_sc : ℕ → ℝ := fun i ↦ -Real.log 2 / 2 * (i : ℝ) ^ 2
    set lam_W : ℝ := lamTilde + Real.log 2
    have hsh_lam := wProb_and_wMean_shift_S0M_v13 (m := 1) (M := M - 1) (by omega) lam_W
    have hl'_eq : lam_W - ((1 : ℕ) : ℝ) * Real.log 2 = lamTilde := by dsimp [lam_W]; ring
    have hp_sh : wProb_v13 W_tail g_sc lam_W (1 + 1 + j'.1) =
        gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1) := by
      simpa only [hl'_eq] using hsh_lam.1 j'
    set T_k : ℝ := fourSizeTarget n (phaseNat n) (k : ℝ)
    set u_n : ℝ := (T_k - θ_n) / (1 - θ_n)
    set u_star : ℝ := (phaseTarget (phaseDelta n) - p1Bar) / (1 - p1Bar)
    have hm_sh : wMean_v13 W_tail g_sc lam_W = u_star := by
      have h1 : wMean_v13 W_tail g_sc lam_W = meanS0M (M - 1) lamTilde + 1 := by
        have h2 := hsh_lam.2
        rw [hl'_eq] at h2
        simpa only [Nat.cast_one] using h2
      have h1mp1_pos : 0 < 1 - p1Bar := by linarith only [hp1.2]
      rw [h1, hlamT]; dsimp [u_star]; field_simp [h1mp1_pos.ne']; ring
    have hun_icc : u_n ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) := by
      have hc := (reducedTarget_mem_Icc_and_Ioo_v13 hθ_120 hTk_cap).1
      exact ⟨by linarith only [hc.1], hc.2⟩
    have hustar_icc : u_star ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) := by
      have hT0_cap : phaseTarget (phaseDelta n) ∈ KcapInterval := by
        unfold phaseTarget KcapInterval; unfold deltaStar at hd
        exact ⟨by linarith only [hd.2], by linarith only [hd.1]⟩
      have hc := (reducedTarget_mem_Icc_and_Ioo_v13 hp1_120 hT0_cap).1
      exact ⟨by linarith only [hc.1], hc.2⟩
    have hg_bds : ∀ i ∈ W_tail,
        -(((1 + (M - 1) : ℕ) : ℝ) ^ 2 + 1) ≤ g_sc i ∧ g_sc i ≤ 0 := by
      intro i hi
      dsimp [g_sc]
      have hsq : (i : ℝ) ^ 2 ≤ ((1 + (M - 1) : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg i) (by exact_mod_cast (Finset.mem_Icc.mp hi).2) 2
      have hq_i : (Real.log 2 / 2) * (i : ℝ) ^ 2 ≤ 1 * ((1 + (M - 1) : ℕ) : ℝ) ^ 2 :=
        mul_le_mul (by linarith [Real.log_two_lt_d9]) hsq (sq_nonneg _) zero_le_one
      have hq_nn : 0 ≤ (Real.log 2 / 2) * (i : ℝ) ^ 2 :=
        mul_nonneg (div_nonneg hq_pos.le zero_le_two) (sq_nonneg _)
      rw [show -Real.log 2 / 2 * (i : ℝ) ^ 2 = -((Real.log 2 / 2) * (i : ℝ) ^ 2) by ring]
      exact ⟨by linarith only [hq_i], by linarith only [hq_nn]⟩
    have hm_master := windowGibbs_master_v13 (m := 1) (M := M - 1) le_rfl hMp7 hg_bds
    have hStrict_g := hm_master.2.2.1
    have hBox_g := hm_master.2.2.2.1
    have hm_lim_t_eq : wMean_v13 W_tail g_sc l_lim = u_n := hl_lim_eq
    have hl_lim_m_icc : l_lim ∈ Set.Icc (-(wMasterLambda (M - 1))) (wMasterLambda (M - 1)) :=
      ((hm_master.2.2.2.2 u_n hun_icc).2 l_lim hm_lim_t_eq).1
    have hlamW_icc : lam_W ∈ Set.Icc (-(wMasterLambda (M - 1))) (wMasterLambda (M - 1)) :=
      ((hm_master.2.2.2.2 u_star hustar_icc).2 lam_W hm_sh).1
    clear hm_master
    have hu_star_diff : |u_n - u_star| ≤
        (4 * (C_corr + 1) + 96) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
      have h1mp1_pos : 0 < 1 - p1Bar := by linarith only [hp1.2]
      set u_bar : ℝ := (T_k - p1Bar) / (1 - p1Bar)
      have h1 : |u_n - u_bar| ≤ 96 * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
        have hid_u : u_n - u_bar = (T_k - 1) * (θ_n - p1Bar) / ((1 - θ_n) * (1 - p1Bar)) := by
          dsimp [u_n, u_bar]; field_simp [h1mθ_pos.ne', h1mp1_pos.ne']; ring
        obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
        have hTk1 : |T_k - 1| ≤ 4 := by
          obtain ⟨hlo, hhi⟩ := hTk_cap
          rw [abs_le]; exact ⟨by linarith only [hlo, h2lo], by linarith only [hhi, h2hi]⟩
        have hden_ge : 1 / 4 ≤ (1 - θ_n) * (1 - p1Bar) :=
          le_trans (by norm_num : (1 / 4 : ℝ) ≤ (39 / 40) * (39 / 40))
            (mul_le_mul h1mθ_ge (by linarith only [hp1.2]) (by norm_num) h1mθ_pos.le)
        rw [hid_u, abs_div, abs_mul, abs_of_pos (mul_pos h1mθ_pos h1mp1_pos)]
        calc |T_k - 1| * |θ_n - p1Bar| / ((1 - θ_n) * (1 - p1Bar))
            ≤ (4 * (1 / (k : ℝ))) / (1 / 4 : ℝ) :=
              div_le_div₀ (by positivity) (mul_le_mul hTk1 hθ_diff (abs_nonneg _) (by norm_num))
                (by norm_num) hden_ge
          _ = 16 * (1 / (k : ℝ)) := by ring
          _ ≤ 16 * (6 / Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left hinv_k (by norm_num)
          _ = (96 / Real.log (n : ℝ)) * 1 := by ring
          _ ≤ (96 / Real.log (n : ℝ)) * Real.log (Real.log (n : ℝ)) :=
              mul_le_mul_of_nonneg_left hll_ge1 (by positivity)
          _ = 96 * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by ring
      have h2 : |u_bar - u_star| ≤
          4 * (C_corr + 1) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
        have hsub_u : u_bar - u_star = (T_k - phaseTarget (phaseDelta n)) / (1 - p1Bar) := by
          dsimp [u_bar, u_star]; ring
        rw [hsub_u, abs_div, abs_of_pos h1mp1_pos]
        calc |T_k - phaseTarget (phaseDelta n)| / (1 - p1Bar)
            ≤ (2 * (C_corr + 1) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) / (1 / 2 : ℝ) :=
              div_le_div₀ (le_trans (abs_nonneg _) htar_k) htar_k (by norm_num) (by linarith only [hp1.2])
          _ = 4 * (C_corr + 1) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by ring
      exact (abs_sub_le u_n u_bar u_star).trans ((add_le_add h1 h2).trans_eq (by ring))
    have hWt_ne : W_tail.Nonempty := ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
    have hl_dist : |l_lim - lam_W| ≤
        ((4 * (C_corr + 1) + 96) / wMasterCstar (M - 1)) *
          Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
      have hmvt_g : ∀ {a b : ℝ},
          a ∈ Set.Icc (-(wMasterLambda (M - 1))) (wMasterLambda (M - 1)) →
          b ∈ Set.Icc (-(wMasterLambda (M - 1))) (wMasterLambda (M - 1)) → a ≤ b →
          wMasterCstar (M - 1) * (b - a) ≤ wMean_v13 W_tail g_sc b - wMean_v13 W_tail g_sc a := by
        intro a b ha hb hab
        exact derivative_lower_bound_mul_sub_le_sub hab
          (fun x _ ↦ (hasDerivAt_wMean_v13 hWt_ne g_sc x).continuousAt.continuousWithinAt)
          (fun x _ ↦ (hasDerivAt_wMean_v13 hWt_ne g_sc x).differentiableAt.differentiableWithinAt)
          (fun x hx ↦ by
            rw [(hasDerivAt_wMean_v13 hWt_ne g_sc x).deriv]
            exact (hBox_g x ⟨ha.1.trans (Ioo_subset_Icc_self hx).1,
              (Ioo_subset_Icc_self hx).2.trans hb.2⟩).2)
      have hmul_c : wMasterCstar (M - 1) * |l_lim - lam_W| ≤ |u_n - u_star| := by
        rw [← hm_lim_t_eq, ← hm_sh]
        rcases le_total l_lim lam_W with hle | hle
        · rw [abs_sub_comm l_lim lam_W, abs_of_nonneg (sub_nonneg.mpr hle),
            abs_sub_comm (wMean_v13 _ _ l_lim),
            abs_of_nonneg (sub_nonneg.mpr (hStrict_g.monotone hle))]
          exact hmvt_g hl_lim_m_icc hlamW_icc hle
        · rw [abs_of_nonneg (sub_nonneg.mpr hle),
            abs_of_nonneg (sub_nonneg.mpr (hStrict_g.monotone hle))]
          exact hmvt_g hlamW_icc hl_lim_m_icc hle
      exact ((le_div_iff₀' hwmc_tail_pos).mpr (hmul_c.trans hu_star_diff)).trans_eq (by ring)
    have hjWt : 1 + 1 + j'.1 ∈ W_tail := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hp_lip_g :
        |wProb_v13 W_tail g_sc l_lim (1 + 1 + j'.1) - wProb_v13 W_tail g_sc lam_W (1 + 1 + j'.1)| ≤
          2 * (M : ℝ) * |l_lim - lam_W| := by
      have hlip := wProb_lip_in_tilt_v13 (m := 1) (M := M - 1) (by omega) g_sc hjWt l_lim lam_W
      have h1M : ((1 + (M - 1) : ℕ) : ℝ) = (M : ℝ) := by exact_mod_cast (show 1 + (M - 1) = M by omega)
      rwa [h1M] at hlip
    have hi_eq1 : 1 + j.1 = 1 + 1 + j'.1 := by dsimp [j']; omega
    have herr1 : |(kv j : ℝ) / (k : ℝ) - (1 - θ_n) * p_t_fin (1 + 1 + j'.1)| ≤
        6 * B_err_tail * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
      have hb1 := hkv_approx j hj0
      rw [hi_eq1] at hb1
      calc |(kv j : ℝ) / (k : ℝ) - (1 - θ_n) * p_t_fin (1 + 1 + j'.1)|
          ≤ B_err_tail * (1 / (k : ℝ)) := by simpa [div_eq_mul_inv] using hb1
        _ ≤ B_err_tail * (6 / Real.log (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hinv_k hBerr_tail_pos.le
        _ = (6 * B_err_tail / Real.log (n : ℝ)) * 1 := by ring
        _ ≤ (6 * B_err_tail / Real.log (n : ℝ)) * Real.log (Real.log (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hll_ge1 (by positivity)
        _ = 6 * B_err_tail * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by ring
    have herr2 : |(1 - θ_n) * p_t_fin (1 + 1 + j'.1) - (1 - θ_n) * p_t_lim (1 + 1 + j'.1)| ≤
        C_opt_tail * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
      rw [← mul_sub, abs_mul, abs_of_pos h1mθ_pos]
      have h1m_le1 : 1 - θ_n ≤ 1 := by linarith only [hθ_120.1]
      calc (1 - θ_n) * |p_t_fin (1 + 1 + j'.1) - p_t_lim (1 + 1 + j'.1)|
          ≤ 1 * (C_opt_tail / (phaseNat n : ℝ)) :=
            mul_le_mul h1m_le1 (hp_t_approx _ hjWt) (abs_nonneg _) zero_le_one
        _ ≤ C_opt_tail / Real.log (n : ℝ) := by
            rw [one_mul]; exact div_le_div_of_nonneg_left hCopt_pos.le hL_pos ha_ge_L
        _ ≤ (C_opt_tail / Real.log (n : ℝ)) * Real.log (Real.log (n : ℝ)) :=
            le_mul_of_one_le_right (div_nonneg hCopt_pos.le hL_pos.le) hll_ge1
        _ = C_opt_tail * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by ring
    have herr3 :
        |(1 - θ_n) * p_t_lim (1 + 1 + j'.1) -
            (1 - θ_n) * gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1)| ≤
          (2 * (M : ℝ) / wMasterCstar (M - 1) * (4 * (C_corr + 1) + 96)) *
            Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
      rw [← mul_sub, abs_mul, abs_of_pos h1mθ_pos, ← hp_sh, hp_lim_def _ hjWt]
      have h1m_le1 : 1 - θ_n ≤ 1 := by linarith only [hθ_120.1]
      calc (1 - θ_n) * |wProb_v13 W_tail g_sc l_lim (1 + 1 + j'.1) -
              wProb_v13 W_tail g_sc lam_W (1 + 1 + j'.1)|
          ≤ 1 * (2 * (M : ℝ) * |l_lim - lam_W|) :=
            mul_le_mul h1m_le1 hp_lip_g (abs_nonneg _) zero_le_one
        _ ≤ 2 * (M : ℝ) * (((4 * (C_corr + 1) + 96) / wMasterCstar (M - 1)) *
              Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_left hl_dist (by positivity)
        _ = (2 * (M : ℝ) / wMasterCstar (M - 1) * (4 * (C_corr + 1) + 96)) *
              Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by ring
    have herr4 :
        |(1 - θ_n) * gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1) -
            (1 - p1Bar) * gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1)| ≤
          6 * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
      have hg_le1 : gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1) ≤ 1 := by
        rw [← hp_sh, ← sum_wProb_v13 hWt_ne g_sc lam_W]
        have hZ := wPart_v13_pos hWt_ne g_sc lam_W
        exact Finset.single_le_sum (fun i hi ↦ by
          simp only [wProb_v13, hi, ↓reduceIte]; exact div_nonneg (Real.exp_pos _).le hZ.le) hjWt
      have hg_nn : 0 ≤ gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1) := by
        rw [← hp_sh]; simp only [wProb_v13, hjWt, ↓reduceIte]
        exact div_nonneg (Real.exp_pos _).le (wPart_v13_pos hWt_ne g_sc lam_W).le
      rw [show (1 - θ_n) * gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1) -
          (1 - p1Bar) * gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1) =
        -(θ_n - p1Bar) * gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1) by ring,
        abs_mul, abs_neg, abs_of_nonneg hg_nn]
      calc |θ_n - p1Bar| * gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1)
          ≤ (1 / (k : ℝ)) * 1 := mul_le_mul hθ_diff hg_le1 hg_nn (by positivity)
        _ ≤ 6 / Real.log (n : ℝ) := by rw [mul_one]; exact hinv_k
        _ ≤ 6 * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
            rw [div_le_div_iff_of_pos_right hL_pos]; linarith only [hll_ge1]
    have htri_all :
        |(kv j : ℝ) / (k : ℝ) - (1 - p1Bar) * gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1)| ≤
          |(kv j : ℝ) / (k : ℝ) - (1 - θ_n) * p_t_fin (1 + 1 + j'.1)| +
          |(1 - θ_n) * p_t_fin (1 + 1 + j'.1) - (1 - θ_n) * p_t_lim (1 + 1 + j'.1)| +
          |(1 - θ_n) * p_t_lim (1 + 1 + j'.1) -
            (1 - θ_n) * gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1)| +
          |(1 - θ_n) * gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1) -
            (1 - p1Bar) * gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1)| := by
      have t1 := abs_sub_le ((kv j : ℝ) / (k : ℝ))
        ((1 - θ_n) * p_t_fin (1 + 1 + j'.1))
        ((1 - p1Bar) * gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1))
      have t2 := abs_sub_le ((1 - θ_n) * p_t_fin (1 + 1 + j'.1))
        ((1 - θ_n) * p_t_lim (1 + 1 + j'.1))
        ((1 - p1Bar) * gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1))
      have t3 := abs_sub_le ((1 - θ_n) * p_t_lim (1 + 1 + j'.1))
        ((1 - θ_n) * gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1))
        ((1 - p1Bar) * gibbsProbS0M (M - 1) lamTilde ((j'.1 : ℤ) + 1))
      linarith only [t1, t2, t3]
    refine htri_all.trans ((add_le_add (add_le_add (add_le_add herr1 herr2) herr3) herr4).trans ?_)
    have hid :
        6 * B_err_tail * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) +
          C_opt_tail * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) +
          (2 * (M : ℝ) / wMasterCstar (M - 1) * (4 * (C_corr + 1) + 96)) *
            Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) +
          6 * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) =
        (6 * B_err_tail + C_opt_tail +
          (2 * (M : ℝ) / wMasterCstar (M - 1)) * (4 * (C_corr + 1) + 96) + 6) *
          (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) := by ring
    rw [hid, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCp_ge (by linarith only [hll_ge1])) hL_pos.le

private theorem build_selectedProfile_at_k_regimeC_v13
    {n M k : ℕ} (hM : 8 ≤ M) (hn8 : 8 ≤ n)
    (ha_ge_4sq : 4 * (1 + M) ^ 2 ≤ phaseNat n)
    (ha_ge_4sq_p : 4 * (1 + (M - 1)) ^ 2 ≤ phaseNat n)
    (ha_ge_L : Real.log (n : ℝ) ≤ (phaseNat n : ℝ))
    (ha_le4L : (phaseNat n : ℝ) ≤ 4 * Real.log (n : ℝ))
    {p1Bar C_corr c_tail c_star C_opt_tail B_err_tail C_round_cap C_p : ℝ}
    (hp1 : p1Bar ∈ Set.Ioc (0 : ℝ) (1 / 40))
    (hct_pos : 0 < c_tail) (hc_pos : 0 < c_star)
    (hc_le_p1 : c_star ≤ p1Bar / 2) (hc_le_ct : c_star ≤ (39 / 40 : ℝ) * c_tail)
    (hCopt_pos : 0 < C_opt_tail)
    (hBerr_tail_def : B_err_tail = (((1 + (M - 1) + 4) * (M - 1) + 1 : ℕ) : ℝ))
    (hCround_cap_def : C_round_cap =
      (M : ℝ) * ((1 + |Real.log c_star|) * B_err_tail + (((1 + M : ℕ) : ℝ) ^ 2 + 1) * B_err_tail))
    (hCp_ge :
      6 * B_err_tail + C_opt_tail +
        (2 * (M : ℝ) / wMasterCstar (M - 1)) * (4 * (C_corr + 1) + 96) + 6 ≤ C_p)
    (hk_th1 : 12 * (B_err_tail / c_tail + 2 / p1Bar + 16) * Real.log (n : ℝ) ≤ (n : ℝ))
    (hk_th2 : 6 * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ))
    (hL_ge2 : (2 : ℝ) ≤ Real.log (n : ℝ))
    (hll_ge1 : (1 : ℝ) ≤ Real.log (Real.log (n : ℝ)))
    (hd : phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar)
    (hk1 : 1 ≤ k)
    (hk_lb : (n : ℝ) / (6 * Real.log (n : ℝ)) ≤ (k : ℝ))
    (hk_ub : (k : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ))
    (hTk_cap : fourSizeTarget n (phaseNat n) (k : ℝ) ∈ KcapInterval)
    (htar_k : |fourSizeTarget n (phaseNat n) (k : ℝ) - phaseTarget (phaseDelta n)| ≤
      2 * (C_corr + 1) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
    (hLem32_at_un :
      let W_tail := Finset.Icc (1 + 1) (1 + (M - 1))
      let h_sc : ℕ → ℝ := fun i ↦
        Real.log ((phaseNat n).descFactorial i : ℝ) -
          (i : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (i : ℝ) ^ 2
      ∀ u_n : ℝ, u_n ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) →
        ∃ l_lim l_fin : ℝ,
          wMean_v13 W_tail (fun i ↦ -Real.log 2 / 2 * (i : ℝ) ^ 2) l_lim = u_n ∧
          (∑ i ∈ W_tail, (if i ∈ W_tail then
            Real.exp (l_fin * (i : ℝ) + h_sc i) /
              (∑ j ∈ W_tail, Real.exp (l_fin * (j : ℝ) + h_sc j)) else 0) = 1) ∧
          (∑ i ∈ W_tail, (i : ℝ) * (if i ∈ W_tail then
            Real.exp (l_fin * (i : ℝ) + h_sc i) /
              (∑ j ∈ W_tail, Real.exp (l_fin * (j : ℝ) + h_sc j)) else 0) = u_n) ∧
          ((⨅ l : ℝ, (Real.log (∑ i ∈ W_tail, Real.exp (l * (i : ℝ) + h_sc i)) - l * u_n)) =
            -(∑ i ∈ W_tail, (if i ∈ W_tail then
                Real.exp (l_fin * (i : ℝ) + h_sc i) /
                  (∑ j ∈ W_tail, Real.exp (l_fin * (j : ℝ) + h_sc j)) else 0) *
                Real.log (if i ∈ W_tail then
                  Real.exp (l_fin * (i : ℝ) + h_sc i) /
                    (∑ j ∈ W_tail, Real.exp (l_fin * (j : ℝ) + h_sc j)) else 0)) +
              ∑ i ∈ W_tail, (if i ∈ W_tail then
                Real.exp (l_fin * (i : ℝ) + h_sc i) /
                  (∑ j ∈ W_tail, Real.exp (l_fin * (j : ℝ) + h_sc j)) else 0) * h_sc i) ∧
          (∀ i ∈ W_tail,
            2 * c_tail ≤ (if i ∈ W_tail then
              Real.exp (l_fin * (i : ℝ) + h_sc i) /
                (∑ j ∈ W_tail, Real.exp (l_fin * (j : ℝ) + h_sc j)) else 0) ∧
            |(if i ∈ W_tail then
                Real.exp (l_fin * (i : ℝ) + h_sc i) /
                  (∑ j ∈ W_tail, Real.exp (l_fin * (j : ℝ) + h_sc j)) else 0) -
              (if i ∈ W_tail then
                Real.exp (l_lim * (i : ℝ) + (-Real.log 2 / 2 * (i : ℝ) ^ 2)) /
                  (∑ j ∈ W_tail, Real.exp (l_lim * (j : ℝ) + (-Real.log 2 / 2 * (j : ℝ) ^ 2)))
              else 0)| ≤ C_opt_tail / (phaseNat n : ℝ))) :
    let u : Fin M → ℕ := fun j ↦ phaseNat n - (1 + j.1)
    let h_sc : ℕ → ℝ := fun i ↦
      Real.log ((phaseNat n).descFactorial i : ℝ) -
        (i : ℝ) * Real.log (phaseNat n : ℝ) - Real.log 2 / 2 * (i : ℝ) ^ 2
    let F_cap : ℝ → ℝ → ℝ := fun theta T ↦
      binEntropy theta - Real.log 2 / 2 * theta +
        (1 - theta) * (⨅ l : ℝ,
          (Real.log (∑ i ∈ Finset.Icc 2 M, Real.exp (l * (i : ℝ) + h_sc i)) -
            l * ((T - theta) / (1 - theta))))
    let obj_cap0 : ℝ :=
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (k : ℝ) - (k : ℝ) * Real.log (k : ℝ) +
        (k : ℝ) * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) (k : ℝ) +
          F_cap p1Bar (fourSizeTarget n (phaseNat n) (k : ℝ)) + 0)
    ∃ (kv : Fin M → ℕ) (kp : ColoringProfile (phaseNat n)),
      selectedBlockCount kv = k ∧
      selectedVertexMass u kv = n ∧
      (∀ j : Fin M, 0 < kv j ∧ c_star ≤ (kv j : ℝ) / (k : ℝ)) ∧
      (∀ idx : Fin (phaseNat n), kp idx = ∑ j : Fin M, if u j = idx.1 + 1 then kv j else 0) ∧
      ColoringProfile.partCount kp = k ∧
      ColoringProfile.vertexMass kp = n ∧
      (profileColoringExpectation n kp).toReal = completeUnmarkedFirstMoment u kv ∧
      (signedProfileExpectation n kp).toReal = completeSignedFirstMoment u kv ∧
      (∀ P : ProfilePartition n kp,
        P.1.parts.card = k ∧
        ∀ D ∈ P.1.parts, phaseNat n - M ≤ D.card ∧ D.card ≤ phaseNat n - 1) ∧
      (∀ G : LabeledGraph n,
        ((∃ P : ProfilePartition n kp, G ∈ partitionCocoloringEvent P.1) → cochromaticNumber G ≤ k) ∧
        ((∃ P : ProfilePartition n kp, G ∈ partitionColoringEvent P.1) → chromaticNumberNat G ≤ k)) ∧
      (∀ lamTilde : ℝ,
        meanS0M (M - 1) lamTilde = (phaseTarget (phaseDelta n) - 1) / (1 - p1Bar) →
        ∀ j : Fin M,
          |(kv j : ℝ) / (k : ℝ) - cappedGibbsProbS0M M p1Bar lamTilde ((j.1 : ℤ) + 1)| ≤
            C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) ∧
      obj_cap0 - C_round_cap - capClipTheta_v13 M p1Bar - (M : ℝ) * (1 + 2 * Real.log (n : ℝ)) ≤
        Real.log (completeUnmarkedFirstMoment u kv) := by
  intro u h_sc F_cap obj_cap0
  have hM7 : 7 ≤ M := by omega
  have hMp7 : 7 ≤ M - 1 := by omega
  have hL_pos : 0 < Real.log (n : ℝ) := by linarith only [hL_ge2]
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hBerr_tail_pos : 0 < B_err_tail := by rw [hBerr_tail_def]; positivity
  have hk_ge_th : 2 * (B_err_tail / c_tail + 2 / p1Bar + 16) ≤ (k : ℝ) := by
    have h1 : 2 * (B_err_tail / c_tail + 2 / p1Bar + 16) ≤ (n : ℝ) / (6 * Real.log (n : ℝ)) :=
      (le_div_iff₀ (by positivity)).mpr (by linarith only [hk_th1])
    exact h1.trans hk_lb
  set T_k : ℝ := fourSizeTarget n (phaseNat n) (k : ℝ)
  set k₁ : ℕ := Nat.floor (p1Bar * (k : ℝ))
  have hp1k_ge2 : 2 ≤ p1Bar * (k : ℝ) := by
    have h1 : 2 / p1Bar ≤ (k : ℝ) := by
      have hbt : 0 ≤ B_err_tail / c_tail := by positivity
      linarith only [hk_ge_th, hbt]
    exact (div_le_iff₀' hp1.1).mp h1
  have hk₁_le_R : (k₁ : ℝ) ≤ p1Bar * (k : ℝ) := Nat.floor_le (by positivity)
  have hk₁_gt_R : p1Bar * (k : ℝ) - 1 < (k₁ : ℝ) := by
    have hfl := Nat.lt_floor_add_one (p1Bar * (k : ℝ))
    linarith only [hfl]
  have hk₁_pos : 0 < k₁ := by
    have h1lt : (1 : ℝ) < (k₁ : ℝ) := by linarith only [hp1k_ge2, hk₁_gt_R]
    exact_mod_cast (lt_trans zero_lt_one h1lt)
  have hk₁_lt_k : k₁ < k := by
    have hlt_R : (k₁ : ℝ) < (k : ℝ) :=
      lt_of_le_of_lt hk₁_le_R ((mul_lt_iff_lt_one_left hk_pos).mpr (by linarith only [hp1.2]))
    exact_mod_cast hlt_R
  set θ_n : ℝ := (k₁ : ℝ) / (k : ℝ)
  have hθ_lo : p1Bar / 2 ≤ θ_n := by
    dsimp [θ_n]; rw [le_div_iff₀ hk_pos]; linarith only [hp1k_ge2, hk₁_gt_R]
  have hθ_hi : θ_n ≤ p1Bar := (div_le_iff₀ hk_pos).mpr hk₁_le_R
  have hθ_diff : |θ_n - p1Bar| ≤ 1 / (k : ℝ) := by
    dsimp [θ_n]; rw [abs_le]
    have h1 : -(1 : ℝ) ≤ (k₁ : ℝ) - p1Bar * (k : ℝ) := by linarith only [hk₁_gt_R]
    have h2 : (k₁ : ℝ) - p1Bar * (k : ℝ) ≤ 0 := by linarith only [hk₁_le_R]
    have hd1 := div_le_div_of_nonneg_right h1 hk_pos.le
    have hd2 := div_le_div_of_nonneg_right h2 hk_pos.le
    rw [sub_div, mul_div_cancel_right₀ _ hk_pos.ne'] at hd1 hd2
    rw [neg_div] at hd1
    rw [zero_div] at hd2
    have hinv_pos := one_div_pos.mpr hk_pos
    exact ⟨hd1, by linarith only [hd2, hinv_pos]⟩
  have hθ_120 : θ_n ∈ Set.Icc (0 : ℝ) (1 / 20) :=
    ⟨by linarith only [hp1.1, hθ_lo], by linarith only [hp1.2, hθ_hi]⟩
  have h1mθ_pos : 0 < 1 - θ_n := by linarith only [hθ_hi, hp1.2]
  have h1mθ_ge : 39 / 40 ≤ 1 - θ_n := by linarith only [hθ_hi, hp1.2]
  set k' : ℕ := k - k₁
  have hk'_R : (k' : ℝ) = (1 - θ_n) * (k : ℝ) := by
    dsimp [k', θ_n]; rw [Nat.cast_sub hk₁_lt_k.le]; field_simp [hk_pos.ne']
  have hk'_ge : (39 / 40 : ℝ) * (k : ℝ) ≤ (k' : ℝ) := by
    rw [hk'_R]; exact mul_le_mul_of_nonneg_right h1mθ_ge hk_pos.le
  have hk₁_mass_lt : (phaseNat n - 1) * k₁ < n := by
    have h1 : ((phaseNat n - 1 : ℕ) : ℝ) * (k₁ : ℝ) ≤ (n : ℝ) / 10 := by
      have ha1 : ((phaseNat n - 1 : ℕ) : ℝ) ≤ 4 * Real.log (n : ℝ) :=
        le_trans (by exact_mod_cast Nat.sub_le (phaseNat n) 1) ha_le4L
      have hk1_le : (k₁ : ℝ) ≤ (1 / 40 : ℝ) * ((n : ℝ) / Real.log (n : ℝ)) :=
        hk₁_le_R.trans (mul_le_mul hp1.2 hk_ub hk_pos.le (by norm_num))
      calc ((phaseNat n - 1 : ℕ) : ℝ) * (k₁ : ℝ)
          ≤ (4 * Real.log (n : ℝ)) * ((1 / 40 : ℝ) * ((n : ℝ) / Real.log (n : ℝ))) :=
            mul_le_mul ha1 hk1_le (Nat.cast_nonneg _) (by positivity)
        _ = (n : ℝ) / 10 := by field_simp [hL_pos.ne']; ring
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hlt_R : (((phaseNat n - 1) * k₁ : ℕ) : ℝ) < (n : ℝ) := by push_cast; linarith only [h1, hn_pos]
    exact_mod_cast hlt_R
  set n' : ℕ := n - (phaseNat n - 1) * k₁
  have hn'1 : 1 ≤ n' := by dsimp [n']; omega
  set u_n : ℝ := (T_k - θ_n) / (1 - θ_n)
  have ha_ge1 : 1 ≤ phaseNat n := by
    have h4 : 4 ≤ 4 * (1 + M) ^ 2 := by
      have : 1 ≤ (1 + M) ^ 2 := Nat.one_le_pow 2 (1 + M) (by omega)
      omega
    omega
  have htar_red_eq : fourSizeTarget n' (phaseNat n) (k' : ℝ) = u_n := by
    unfold fourSizeTarget
    dsimp [n', u_n, T_k]; unfold fourSizeTarget
    rw [Nat.cast_sub hk₁_mass_lt.le, Nat.cast_mul,
      Nat.cast_sub ha_ge1, Nat.cast_one, hk'_R]
    have hk₁_eq : (k₁ : ℝ) = θ_n * (k : ℝ) := by dsimp [θ_n]; exact (div_mul_cancel₀ _ hk_pos.ne').symm
    rw [hk₁_eq]
    field_simp [hk_pos.ne', h1mθ_pos.ne']; ring
  have hun_icc : u_n ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) := by
    have hc := (reducedTarget_mem_Icc_and_Ioo_v13 hθ_120 hTk_cap).1
    exact ⟨by linarith only [hc.1], hc.2⟩
  have h1_Mp : 1 + (M - 1) = M := by omega
  obtain ⟨l_lim, l_fin, hl_lim_eq, hp_t_sum, hp_t_mean, hFt_ent, hp_t_bds⟩ :=
    hLem32_at_un u_n hun_icc
  clear hLem32_at_un
  set W_tail := Finset.Icc (1 + 1) (1 + (M - 1))
  let p_t_fin : ℕ → ℝ := fun i ↦
    if i ∈ W_tail then Real.exp (l_fin * (i : ℝ) + h_sc i) /
      (∑ j ∈ W_tail, Real.exp (l_fin * (j : ℝ) + h_sc j)) else 0
  let p_t_lim : ℕ → ℝ := fun i ↦
    if i ∈ W_tail then Real.exp (l_lim * (i : ℝ) + (-Real.log 2 / 2 * (i : ℝ) ^ 2)) /
      (∑ j ∈ W_tail, Real.exp (l_lim * (j : ℝ) + (-Real.log 2 / 2 * (j : ℝ) ^ 2))) else 0
  have hk'_big : (((1 + (M - 1) + 4) * (M - 1) + 1 : ℕ) : ℝ) / c_tail + 1 ≤ (k' : ℝ) := by
    rw [← hBerr_tail_def]
    have h1 : B_err_tail / c_tail + 1 ≤ (39 / 40 : ℝ) * (k : ℝ) := by
      have hp1_pos : 0 < p1Bar := hp1.1
      have hp1_nn : 0 ≤ 2 / p1Bar := by positivity
      have hbt_nn : 0 ≤ B_err_tail / c_tail := by positivity
      linarith only [hk_ge_th, hp1_nn, hbt_nn]
    exact h1.trans hk'_ge
  have hp_t_mean' : ∑ i ∈ W_tail, (i : ℝ) * p_t_fin i = (phaseNat n : ℝ) - (n' : ℝ) / (k' : ℝ) := by
    change ∑ i ∈ W_tail, (i : ℝ) * p_t_fin i = u_n at hp_t_mean
    rw [hp_t_mean, ← htar_red_eq]; rfl
  obtain ⟨hkv_t_props, hblock_t, hmass_t, _⟩ :=
    roundedWindowProfile_unmarked_v13 (n := n') (alpha := phaseNat n) (m := 1) (M := M - 1) (k := k')
      (p_opt := p_t_fin) le_rfl hMp7 hn'1 ha_ge_4sq_p hct_pos hp_t_sum hp_t_mean'
      (fun i hi ↦ (hp_t_bds i hi).1) hk'_big
  let kv_tail : Fin (M - 1) → ℕ := fun j' ↦
    (roundedWindowProfile 1 (M - 1) (phaseNat n) k' n' p_t_fin (1 + 1 + j'.1)).toNat
  let kv : Fin M → ℕ := fun j ↦
    if _hj0 : j.1 = 0 then k₁ else kv_tail ⟨j.1 - 1, by omega⟩
  let p_full : ℕ → ℝ := fun i ↦
    if i = 1 then θ_n else if i ∈ W_tail then (1 - θ_n) * p_t_fin i else 0
  have hdisj_1t : Disjoint ({1} : Finset ℕ) W_tail := by
    rw [Finset.disjoint_singleton_left]; simp [W_tail, Finset.mem_Icc]
  have hun_1t : ({1} : Finset ℕ) ∪ W_tail = Finset.Icc 1 M := by
    ext i; simp only [Finset.mem_union, Finset.mem_singleton, W_tail, Finset.mem_Icc]; omega
  have hp_full_sum : ∑ i ∈ Finset.Icc (0 + 1) (0 + M), p_full i = 1 := by
    rw [Nat.zero_add, Nat.zero_add, ← hun_1t, Finset.sum_union hdisj_1t, Finset.sum_singleton]
    have ht_sum : ∑ i ∈ W_tail, p_full i = (1 - θ_n) * ∑ i ∈ W_tail, p_t_fin i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hne1 : i ≠ 1 := by have := (Finset.mem_Icc.mp hi).1; omega
      simp [p_full, hne1, hi]
    change ∑ i ∈ W_tail, p_t_fin i = 1 at hp_t_sum
    rw [ht_sum, hp_t_sum, mul_one]; simp [p_full]
  have hp_full_lo : ∀ i ∈ Finset.Icc (0 + 1) (0 + M), c_star ≤ p_full i := by
    intro i hi
    obtain ⟨_, hiM⟩ := Finset.mem_Icc.mp hi
    by_cases heq1 : i = 1
    · subst heq1; simp only [p_full, ↓reduceIte]; exact hc_le_p1.trans hθ_lo
    · have hi_wt : i ∈ W_tail := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      simp only [p_full, heq1, ↓reduceIte, hi_wt]
      have hp_i_lo : 2 * c_tail ≤ p_t_fin i := (hp_t_bds i hi_wt).1
      calc c_star ≤ (39 / 40 : ℝ) * c_tail := hc_le_ct
        _ ≤ (1 - θ_n) * (2 * c_tail) :=
            mul_le_mul h1mθ_ge (by linarith only [hct_pos]) hct_pos.le h1mθ_pos.le
        _ ≤ (1 - θ_n) * p_t_fin i := mul_le_mul_of_nonneg_left hp_i_lo h1mθ_pos.le
  have hkv_full_props : ∀ j : Fin M,
      0 < kv j ∧ c_star ≤ (kv j : ℝ) / (k : ℝ) ∧
        |(kv j : ℝ) / (k : ℝ) - p_full (0 + 1 + j.1)| ≤ B_err_tail / (k : ℝ) := by
    intro j
    by_cases hj0 : j.1 = 0
    · have hkv0 : kv j = k₁ := by simp [kv, hj0]
      have hi0 : 0 + 1 + j.1 = 1 := by omega
      rw [hkv0, hi0]
      simp only [p_full, ↓reduceIte, θ_n, sub_self, abs_zero]
      exact ⟨hk₁_pos, hc_le_p1.trans hθ_lo, by positivity⟩
    · let j' : Fin (M - 1) := ⟨j.1 - 1, by omega⟩
      have hkv_j : kv j = kv_tail j' := by simp [kv, hj0, j']
      have hi_eq : 0 + 1 + j.1 = 1 + 1 + j'.1 := by dsimp [j']; omega
      have hi_wt : 1 + 1 + j'.1 ∈ W_tail := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      rw [hkv_j, hi_eq]
      simp only [p_full, show 1 + 1 + j'.1 ≠ 1 by omega, ↓reduceIte, hi_wt]
      have hk'_pos_R : 0 < (k' : ℝ) := by rw [hk'_R]; positivity
      have hratio_id : (kv_tail j' : ℝ) / (k : ℝ) = (1 - θ_n) * ((kv_tail j' : ℝ) / (k' : ℝ)) := by
        rw [hk'_R]; field_simp [hk_pos.ne', h1mθ_pos.ne']
      refine ⟨(hkv_t_props j').1, ?_, ?_⟩
      · rw [hratio_id]
        exact hc_le_ct.trans (mul_le_mul h1mθ_ge (hkv_t_props j').2.1 hct_pos.le h1mθ_pos.le)
      · rw [hratio_id, ← mul_sub, abs_mul, abs_of_pos h1mθ_pos]
        calc (1 - θ_n) * |(kv_tail j' : ℝ) / (k' : ℝ) - p_t_fin (1 + 1 + j'.1)|
            ≤ (1 - θ_n) * (B_err_tail / (k' : ℝ)) := by
              rw [hBerr_tail_def]
              exact mul_le_mul_of_nonneg_left (hkv_t_props j').2.2 h1mθ_pos.le
          _ = B_err_tail / (k : ℝ) := by rw [hk'_R]; field_simp [hk_pos.ne', h1mθ_pos.ne']
  have hfin_split : ∀ f : Fin M → ℕ,
      ∑ j : Fin M, f j = f ⟨0, by omega⟩ + ∑ j' : Fin (M - 1), f ⟨j'.1 + 1, by omega⟩ := by
    intro f
    let e : Option (Fin (M - 1)) ≃ Fin M :=
      { toFun := fun o ↦ match o with | none => ⟨0, by omega⟩ | some j' => ⟨j'.1 + 1, by omega⟩
        invFun := fun j ↦ if _h0 : j.1 = 0 then none else some ⟨j.1 - 1, by omega⟩
        left_inv := fun o ↦ by cases o <;> simp
        right_inv := fun j ↦ by
          by_cases h0 : j.1 = 0
          · simp [h0]; ext; exact h0.symm
          · simp [h0]; ext; dsimp; omega }
    rw [← e.sum_comp, Fintype.sum_option]; rfl
  have hblock_full : selectedBlockCount kv = k := by
    unfold selectedBlockCount; rw [hfin_split]
    have h0 : kv ⟨0, by omega⟩ = k₁ := by simp [kv]
    have ht : ∑ j' : Fin (M - 1), kv ⟨j'.1 + 1, by omega⟩ = k' := by
      have hc : ∀ j' : Fin (M - 1), kv ⟨j'.1 + 1, by omega⟩ = kv_tail j' := fun j' ↦ by simp [kv]
      simp_rw [hc]; exact hblock_t
    rw [h0, ht]; dsimp [k']; omega
  have hmass_full : selectedVertexMass u kv = n := by
    unfold selectedVertexMass; rw [hfin_split]
    have h0 : u ⟨0, by omega⟩ * kv ⟨0, by omega⟩ = (phaseNat n - 1) * k₁ := by simp [u, kv]
    have ht : ∑ j' : Fin (M - 1), u ⟨j'.1 + 1, by omega⟩ * kv ⟨j'.1 + 1, by omega⟩ = n' := by
      have hc : ∀ j' : Fin (M - 1),
          u ⟨j'.1 + 1, by omega⟩ * kv ⟨j'.1 + 1, by omega⟩ =
            (phaseNat n - (1 + 1 + j'.1)) * kv_tail j' := fun j' ↦ by
        dsimp [u, kv]; congr 1; omega
      simp_rw [hc]; exact hmass_t
    rw [h0, ht]; dsimp [n']; omega
  have hu_eq0 : (fun j : Fin M ↦ phaseNat n - (0 + 1 + j.1)) = u := by
    funext j; dsimp [u]
  have hlog_unm_θ := log_completeUnmarkedFirstMoment_ge_of_integer_approx_v13
    (n := n) (alpha := phaseNat n) (m := 0) (M := M) (k := k)
    (p_opt := p_full) (kv := kv) (Nat.zero_le 1) hM7 (by omega) ha_ge_4sq hk1 hc_pos
    hp_full_sum hp_full_lo hkv_full_props hblock_full (by rwa [hu_eq0])
  have hent_full_eq :
      -(∑ i ∈ Finset.Icc (0 + 1) (0 + M), p_full i * Real.log (p_full i)) +
          ∑ i ∈ Finset.Icc (0 + 1) (0 + M), p_full i * h_sc i =
        F_cap θ_n T_k := by
    rw [Nat.zero_add, Nat.zero_add, ← hun_1t,
      Finset.sum_union hdisj_1t, Finset.sum_union hdisj_1t,
      Finset.sum_singleton, Finset.sum_singleton]
    have hh1 : h_sc 1 = -Real.log 2 / 2 := by
      dsimp [h_sc]
      rw [Nat.mul_one, Nat.cast_one]
      ring
    have hp1_f : p_full 1 = θ_n := by simp [p_full]
    have htail_ent :
        ∑ i ∈ W_tail, p_full i * Real.log (p_full i) =
          (1 - θ_n) * Real.log (1 - θ_n) + (1 - θ_n) * ∑ i ∈ W_tail, p_t_fin i * Real.log (p_t_fin i) := by
      have hpt : ∀ i ∈ W_tail,
          p_full i * Real.log (p_full i) =
            (1 - θ_n) * Real.log (1 - θ_n) * p_t_fin i +
              (1 - θ_n) * (p_t_fin i * Real.log (p_t_fin i)) := by
        intro i hi
        have hne1 : i ≠ 1 := by have := (Finset.mem_Icc.mp hi).1; omega
        have hpt_pos : 0 < p_t_fin i := lt_of_lt_of_le (by positivity) (hp_t_bds i hi).1
        simp only [p_full, hne1, ↓reduceIte, hi]
        rw [Real.log_mul h1mθ_pos.ne' hpt_pos.ne']; ring
      change ∑ i ∈ W_tail, p_t_fin i = 1 at hp_t_sum
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hp_t_sum, mul_one]
    have htail_sc :
        ∑ i ∈ W_tail, p_full i * h_sc i = (1 - θ_n) * ∑ i ∈ W_tail, p_t_fin i * h_sc i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hne1 : i ≠ 1 := by have := (Finset.mem_Icc.mp hi).1; omega
      simp only [p_full, hne1, ↓reduceIte, hi]; ring
    rw [hp1_f, hh1, htail_ent, htail_sc]
    have hW_eq : Finset.Icc 2 M = W_tail := by dsimp [W_tail]; rw [h1_Mp]
    have hFt_match :
        (⨅ l : ℝ, (Real.log (∑ i ∈ Finset.Icc 2 M, Real.exp (l * (i : ℝ) + h_sc i)) - l * u_n)) =
          -(∑ i ∈ W_tail, p_t_fin i * Real.log (p_t_fin i)) + ∑ i ∈ W_tail, p_t_fin i * h_sc i := by
      rw [hW_eq]; exact hFt_ent
    dsimp [F_cap, u_n]; unfold binEntropy; rw [hFt_match]; ring
  have hFcap_lip : (k : ℝ) * |F_cap θ_n T_k - F_cap p1Bar T_k| ≤ capClipTheta_v13 M p1Bar :=
    Fcap_theta_diff_le_v13 hM ha_ge_4sq_p hk1 hp1 hθ_lo hθ_hi hθ_diff hTk_cap
  have hlog_en1 : Real.log (Real.exp 1 * ((n : ℝ) + 1)) ≤ 1 + 2 * Real.log (n : ℝ) := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn1_sq : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast (show n + 1 ≤ n ^ 2 by rw [sq]; calc n + 1 ≤ 2 * n := by omega
        _ ≤ n * n := Nat.mul_le_mul_right n (by omega))
    calc Real.log (Real.exp 1 * ((n : ℝ) + 1))
        ≤ Real.log (Real.exp 1 * (n : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hn1_sq (Real.exp_pos 1).le)
      _ = Real.log (Real.exp 1) + Real.log ((n : ℝ) ^ 2) :=
          Real.log_mul (Real.exp_pos 1).ne' (pow_pos hn_pos 2).ne'
      _ = 1 + 2 * Real.log (n : ℝ) := by rw [Real.log_exp, Real.log_pow]; norm_num
  have hlog_unm_ge :
      obj_cap0 - C_round_cap - capClipTheta_v13 M p1Bar - (M : ℝ) * (1 + 2 * Real.log (n : ℝ)) ≤
        Real.log (completeUnmarkedFirstMoment u kv) := by
    have hm_log := mul_le_mul_of_nonneg_left hlog_en1 (Nat.cast_nonneg M)
    have hobj_θ :
        (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (k : ℝ) - (k : ℝ) * Real.log (k : ℝ) +
          (k : ℝ) * (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) (k : ℝ) +
            F_cap θ_n T_k) =
        obj_cap0 + (k : ℝ) * (F_cap θ_n T_k - F_cap p1Bar T_k) := by
      dsimp [obj_cap0, T_k]; ring
    dsimp only at hlog_unm_θ
    rw [hent_full_eq, hu_eq0, ← hCround_cap_def] at hlog_unm_θ
    have hlip_abs : |(k : ℝ) * (F_cap θ_n T_k - F_cap p1Bar T_k)| ≤ capClipTheta_v13 M p1Bar := by
      rwa [abs_mul, abs_of_pos hk_pos]
    have hlip_lo := (abs_le.mp hlip_abs).1
    linarith only [hlog_unm_θ, hobj_θ, hm_log, hlip_lo]
  let kp : ColoringProfile (phaseNat n) := embedWindowProfile_v13 (phaseNat n) 0 M kv
  have hmass_0 : selectedVertexMass (fun j : Fin M ↦ phaseNat n - (0 + 1 + j.1)) kv = n := by
    rwa [hu_eq0]
  obtain ⟨_, hkp_part, hkp_mass, _, hkp_unm, hkp_sgn, hkp_P, hkp_G⟩ :=
    embedWindowProfile_properties_v13 (n := n) (alpha := phaseNat n) (m := 0) (M := M)
      (by have := Nat.le_self_pow (by norm_num : 2 ≠ 0) (1 + M); omega) hmass_0
  rw [hu_eq0] at hkp_unm hkp_sgn
  have hratio_cap := cappedTail_ratio_approx_v13 hM hp1 hBerr_tail_pos hCopt_pos hCp_ge
    hL_ge2 hll_ge1 ha_ge_L hk_th2 hd hk1 hk_lb hTk_cap htar_k hθ_lo hθ_hi hθ_diff
    (p_t_fin := p_t_fin) (p_t_lim := p_t_lim) (kv := kv)
    (fun j hj0 ↦ by simp [kv, hj0, θ_n])
    hl_lim_eq
    (fun i hi ↦ rfl)
    (fun i hi ↦ (hp_t_bds i hi).2)
    (fun j hj0 ↦ by
      have hb := (hkv_full_props j).2.2
      have hi_wt : 1 + j.1 ∈ W_tail := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hne1 : 1 + j.1 ≠ 1 := by omega
      simpa only [Nat.zero_add, p_full, hne1, ↓reduceIte, hi_wt] using hb)
  exact ⟨kv, kp, hblock_full, hmass_full, fun j ↦ ⟨(hkv_full_props j).1, (hkv_full_props j).2.1⟩,
    fun idx ↦ by dsimp [kp, embedWindowProfile_v13, u],
    hkp_part.trans hblock_full, hkp_mass, hkp_unm, hkp_sgn,
    fun P ↦ ⟨by rw [hblock_full] at hkp_P; exact (hkp_P P).1,
      by simpa only [Nat.zero_add] using (hkp_P P).2⟩,
    fun G ↦ ⟨by rw [hblock_full] at hkp_G; exact (hkp_G G).1,
      by rw [hblock_full] at hkp_G; exact (hkp_G G).2⟩,
    hratio_cap, hlog_unm_ge⟩

/-- **Proposition 5.3(i)–(ii) in `Regime C` (`main.tex` lines 817–843, 868–890, eq. `(5.17)`):**
for every `M ≥ 8` and `p̄₁ ∈ (0, 1/40]`, there exist deterministic `(M, p̄₁)`-dependent constants
`C_corr > 0`, `c_star > 0`, `c_Z > 0`, and `C_p > 0` such that eventually whenever
`δ_n ∈ [0, δ_*]`:
1. `𝓛_{S_{0, M}}^{=p̄₁}(n, ·) + (log 2) · = 0` and `𝓛_{S_{0, M}}^{=p̄₁}(n, ·) = 0` have unique
   corridor roots `r_co, r_ch`;
2. `M_{S_{0, M - 1}}(λ̃) = (T_{δ_n} - 1) / (1 - p̄₁)` has a unique tilt `λ̃`;
3. at `k_co := ⌈r_co⌉ + 16` and `k_ch := ⌈r_ch⌉ + ⌈log n⌉`, there exist integer profiles
   `k_co_vec, k_ch_vec : Fin M → ℕ` and embedded `ColoringProfile (phaseNat n)` witnesses
   `kp_co, kp_ch` satisfying exact class-count & vertex-mass conservation, strict linear coordinate
   positivity `≥ c_star`, `O_{M, p̄₁}((log log n) / log n)` capped-Gibbs accuracy against
   `cappedGibbsProbS0M M p̄₁ λ̃`, `log E[Z_{k_co}^mk] ≥ c_Z (log n)²`, and
   `log E[X̄_{k_ch}] ≥ c_Z (log n)³`. -/
theorem eventually_selectedProfiles_prop53_regimeC
    {M : ℕ} (hM : 8 ≤ M)
    {p1Bar : ℝ} (hp1 : p1Bar ∈ Set.Ioc (0 : ℝ) (1 / 40)) :
    ∃ C_corr c_star c_Z C_p : ℝ,
      0 < C_corr ∧ 0 < c_star ∧ 0 < c_Z ∧ 0 < C_p ∧
      ∀ᶠ n : ℕ in atTop,
        phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar →
          let u : Fin M → ℕ := fun j ↦ phaseNat n - (1 + j.1)
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
          (∃! lamTilde : ℝ,
            meanS0M (M - 1) lamTilde = (phaseTarget (phaseDelta n) - 1) / (1 - p1Bar)) ∧
          (∀ {r_co r_ch : ℝ},
            r_co ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) →
            obj_cap (Real.log 2) r_co = 0 →
            r_ch ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) →
            obj_cap 0 r_ch = 0 →
            let k_co : ℕ := Nat.ceil r_co + 16
            let k_ch : ℕ := Nat.ceil r_ch + Nat.ceil (Real.log (n : ℝ))
            1 ≤ k_co ∧ (k_co : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ∧
            1 ≤ k_ch ∧ (k_ch : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ∧
            ∃ (k_co_vec k_ch_vec : Fin M → ℕ) (kp_co kp_ch : ColoringProfile (phaseNat n)),
              selectedBlockCount k_co_vec = k_co ∧
              selectedVertexMass u k_co_vec = n ∧
              selectedBlockCount k_ch_vec = k_ch ∧
              selectedVertexMass u k_ch_vec = n ∧
              (∀ j : Fin M, 0 < k_co_vec j ∧ c_star ≤ (k_co_vec j : ℝ) / (k_co : ℝ)) ∧
              (∀ j : Fin M, 0 < k_ch_vec j ∧ c_star ≤ (k_ch_vec j : ℝ) / (k_ch : ℝ)) ∧
              (∀ idx : Fin (phaseNat n),
                kp_co idx = ∑ j : Fin M, if u j = idx.1 + 1 then k_co_vec j else 0) ∧
              (∀ idx : Fin (phaseNat n),
                kp_ch idx = ∑ j : Fin M, if u j = idx.1 + 1 then k_ch_vec j else 0) ∧
              ColoringProfile.partCount kp_co = k_co ∧
              ColoringProfile.vertexMass kp_co = n ∧
              (signedProfileExpectation n kp_co).toReal = completeSignedFirstMoment u k_co_vec ∧
              (∀ P : ProfilePartition n kp_co,
                P.1.parts.card = k_co ∧
                ∀ D ∈ P.1.parts, phaseNat n - M ≤ D.card ∧ D.card ≤ phaseNat n - 1) ∧
              (∀ G : LabeledGraph n,
                (∃ P : ProfilePartition n kp_co, G ∈ partitionCocoloringEvent P.1) →
                  cochromaticNumber G ≤ k_co) ∧
              ColoringProfile.partCount kp_ch = k_ch ∧
              ColoringProfile.vertexMass kp_ch = n ∧
              (profileColoringExpectation n kp_ch).toReal = completeUnmarkedFirstMoment u k_ch_vec ∧
              (∀ P : ProfilePartition n kp_ch,
                P.1.parts.card = k_ch ∧
                ∀ D ∈ P.1.parts, phaseNat n - M ≤ D.card ∧ D.card ≤ phaseNat n - 1) ∧
              (∀ G : LabeledGraph n,
                (∃ P : ProfilePartition n kp_ch, G ∈ partitionColoringEvent P.1) →
                  chromaticNumberNat G ≤ k_ch) ∧
              (∀ lamTilde : ℝ,
                meanS0M (M - 1) lamTilde = (phaseTarget (phaseDelta n) - 1) / (1 - p1Bar) →
                ∀ j : Fin M,
                  |(k_co_vec j : ℝ) / (k_co : ℝ) -
                      cappedGibbsProbS0M M p1Bar lamTilde ((j.1 : ℤ) + 1)| ≤
                    C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) ∧
                  |(k_ch_vec j : ℝ) / (k_ch : ℝ) -
                      cappedGibbsProbS0M M p1Bar lamTilde ((j.1 : ℤ) + 1)| ≤
                    C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) ∧
              c_Z * (Real.log (n : ℝ)) ^ 2 ≤ Real.log (completeSignedFirstMoment u k_co_vec) ∧
              c_Z * (Real.log (n : ℝ)) ^ 3 ≤ Real.log (completeUnmarkedFirstMoment u k_ch_vec)) := by
  have hM7 : 7 ≤ M := by omega
  have hMp7 : 7 ≤ M - 1 := by omega
  obtain ⟨C_corr, _, hC_pos, _, hRoots_ev⟩ :=
    exists_pos_eventually_existsUnique_cappedWindowPhaseObjective_zero_logLogCorridor hM
  obtain ⟨_, c_tail, C_opt_tail, _, hct_pos, hCopt_pos, hLem32_tail⟩ :=
    existsUnique_windowFiniteGibbsTilt_and_optimizer_bounds_lemma32_ii hMp7
  obtain ⟨K_slope, hK_pos, hSlope_ev⟩ :=
    (eventually_window_and_capped_phaseObjective_deriv_and_diff_lemma31 hM7 (C_corr + 1) (by positivity)).2
  have hwmc_tail_pos : 0 < wMasterCstar (M - 1) := by unfold wMasterCstar; positivity
  set c_star : ℝ := min (p1Bar / 2) ((39 / 40 : ℝ) * c_tail) with hc_star_def
  have hc_pos : 0 < c_star := by rw [hc_star_def]; exact lt_min (half_pos hp1.1) (by positivity)
  have hc_le_p1 : c_star ≤ p1Bar / 2 := by rw [hc_star_def]; exact min_le_left _ _
  have hc_le_ct : c_star ≤ (39 / 40 : ℝ) * c_tail := by rw [hc_star_def]; exact min_le_right _ _
  clear_value c_star
  set B_err_tail : ℝ := (((1 + (M - 1) + 4) * (M - 1) + 1 : ℕ) : ℝ) with hBerr_tail_def
  have hBerr_tail_pos : 0 < B_err_tail := by rw [hBerr_tail_def]; positivity
  clear_value B_err_tail
  set C_round_cap : ℝ :=
    (M : ℝ) * ((1 + |Real.log c_star|) * B_err_tail + (((1 + M : ℕ) : ℝ) ^ 2 + 1) * B_err_tail)
    with hCround_cap_def
  clear_value C_round_cap
  set C_lip_theta : ℝ := capClipTheta_v13 M p1Bar with hClip_def
  clear_value C_lip_theta
  set c_Z : ℝ := 1 / (2 * Real.log 2) with hcZ_def
  have hcZ_pos : 0 < c_Z := by rw [hcZ_def]; have := Real.log_pos one_lt_two; positivity
  clear_value c_Z
  set C_p : ℝ :=
    6 * B_err_tail + C_opt_tail +
      (2 * (M : ℝ) / wMasterCstar (M - 1)) * (4 * (C_corr + 1) + 96) + 6 + 1 with hCp_def
  have hCp_pos : 0 < C_p := by rw [hCp_def]; positivity
  have hCp_ge :
      6 * B_err_tail + C_opt_tail +
        (2 * (M : ℝ) / wMasterCstar (M - 1)) * (4 * (C_corr + 1) + 96) + 6 ≤ C_p := by
    linarith only [hCp_def]
  clear_value C_p
  refine ⟨C_corr, c_star, c_Z, C_p, hC_pos, hc_pos, hcZ_pos, hCp_pos, ?_⟩
  have halpha_ev : ∀ᶠ n : ℕ in atTop, 4 * (1 + M) ^ 2 + 4 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (((4 * (1 + M) ^ 2 + 4 : ℕ) : ℝ)),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  have hk_thresh_ev : ∀ᶠ n : ℕ in atTop,
      12 * (B_err_tail / c_tail + 2 / p1Bar + 16) * Real.log (n : ℝ) ≤ (n : ℝ) ∧
      6 * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) := by
    have hdiv2 : Tendsto (fun x : ℝ ↦ (Real.log x) ^ 2 / x) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero
    set K_t : ℝ := max (12 * (B_err_tail / c_tail + 2 / p1Bar + 16)) 6
    have hKt_pos : 0 < K_t := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hm := (hdiv2.comp tendsto_natCast_atTop_atTop).eventually
      (Iic_mem_nhds (one_div_pos.mpr hKt_pos))
    filter_upwards [eventually_ge_atTop 4,
      tendsto_logOrder_atTop.eventually_ge_atTop 1, hm] with n hn4 hL1 hle
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have h1 := (div_le_iff₀ hn_pos).mp hle
    have hmul := mul_le_mul_of_nonneg_left h1 hKt_pos.le
    have hcanc : K_t * (1 / K_t * (n : ℝ)) = (n : ℝ) := by field_simp [hKt_pos.ne']
    rw [hcanc] at hmul
    have hL_ge1 : (1 : ℝ) ≤ Real.log (n : ℝ) := hL1
    have hL_le_L2 : Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
      calc Real.log (n : ℝ) = Real.log (n : ℝ) * 1 := (mul_one _).symm
        _ ≤ Real.log (n : ℝ) * Real.log (n : ℝ) :=
            mul_le_mul_of_nonneg_left hL_ge1 (by linarith only [hL_ge1])
        _ = (Real.log (n : ℝ)) ^ 2 := (sq _).symm
    refine ⟨(mul_le_mul (le_max_left _ _) hL_le_L2 (by linarith only [hL_ge1]) hKt_pos.le).trans hmul,
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)).trans hmul⟩
  have hslope_dom : ∀ᶠ n : ℕ in atTop,
      K_slope * Real.log (Real.log (n : ℝ)) ≤ (1 / Real.log 2) * Real.log (n : ℝ) := by
    have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hb := logLogOrder_isLittleO_logOrder.bound (div_pos (one_div_pos.mpr hq_pos) hK_pos)
    filter_upwards [hb, tendsto_logOrder_atTop.eventually_ge_atTop 2,
      tendsto_logLogOrder_atTop.eventually_ge_atTop 1] with n hbn hL2 hll1
    dsimp [logOrder, logLogOrder] at hbn hL2 hll1
    rw [abs_of_pos (by linarith only [hll1]), abs_of_pos (by linarith only [hL2])] at hbn
    have hm := mul_le_mul_of_nonneg_left hbn hK_pos.le
    have hc : K_slope * ((1 / Real.log 2 / K_slope) * Real.log (n : ℝ)) =
        (1 / Real.log 2) * Real.log (n : ℝ) := by field_simp [hK_pos.ne', hq_pos.ne']
    linarith only [hm, hc]
  have hround_abs_ev : ∀ᶠ n : ℕ in atTop,
      C_round_cap + C_lip_theta + (M : ℝ) * (1 + 2 * Real.log (n : ℝ)) ≤
        (1 / (2 * Real.log 2)) * (Real.log (n : ℝ)) ^ 2 := by
    have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    set K_abs : ℝ := 2 * Real.log 2 * (|C_round_cap| + |C_lip_theta| + 3 * (M : ℝ) + 1)
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (max 2 K_abs)] with n hLn
    dsimp [logOrder] at hLn
    have hL2 : 2 ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hLn
    have hLK : K_abs ≤ Real.log (n : ℝ) := (le_max_right _ _).trans hLn
    have h1 : (|C_round_cap| + |C_lip_theta| + 3 * (M : ℝ) + 1) * Real.log (n : ℝ) ≤
        (1 / (2 * Real.log 2)) * (Real.log (n : ℝ)) ^ 2 := by
      have hm := mul_le_mul_of_nonneg_right hLK
        (by positivity : 0 ≤ (1 / (2 * Real.log 2)) * Real.log (n : ℝ))
      dsimp [K_abs] at hm
      have hc : 2 * Real.log 2 * (|C_round_cap| + |C_lip_theta| + 3 * (M : ℝ) + 1) *
          (1 / (2 * Real.log 2) * Real.log (n : ℝ)) =
          (|C_round_cap| + |C_lip_theta| + 3 * (M : ℝ) + 1) * Real.log (n : ℝ) := by
        field_simp [hq_pos.ne']
      rw [hc] at hm
      exact hm.trans_eq (by ring)
    have hC1 : C_round_cap ≤ |C_round_cap| * Real.log (n : ℝ) :=
      (le_abs_self _).trans ((mul_one _).symm.le.trans
        (mul_le_mul_of_nonneg_left (by linarith only [hL2]) (abs_nonneg _)))
    have hC2 : C_lip_theta ≤ |C_lip_theta| * Real.log (n : ℝ) :=
      (le_abs_self _).trans ((mul_one _).symm.le.trans
        (mul_le_mul_of_nonneg_left (by linarith only [hL2]) (abs_nonneg _)))
    have hM_le : (M : ℝ) * (1 + 2 * Real.log (n : ℝ)) ≤ 3 * (M : ℝ) * Real.log (n : ℝ) := by
      calc (M : ℝ) * (1 + 2 * Real.log (n : ℝ))
          ≤ (M : ℝ) * (3 * Real.log (n : ℝ)) :=
            mul_le_mul_of_nonneg_left (by linarith only [hL2]) (Nat.cast_nonneg M)
        _ = 3 * (M : ℝ) * Real.log (n : ℝ) := by ring
    linarith only [h1, hC1, hC2, hM_le, hL2]
  filter_upwards [eventually_ge_atTop 8, hRoots_ev, hSlope_ev,
    eventually_corridor_pad_and_root_bounds_v13 C_corr hC_pos,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    halpha_ev, hk_thresh_ev, hslope_dom, hround_abs_ev] with
    n hn8 hRoots hSlope hPad hPh halpha_n ⟨hk_th1, hk_th2⟩ hsl_dom hround_dom
    hd u h_sc F_cap obj_cap
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL_ge2 : (2 : ℝ) ≤ Real.log (n : ℝ) := hPad.2.1
  have hL_pos : 0 < Real.log (n : ℝ) := by linarith only [hL_ge2]
  have hll_ge1 : (1 : ℝ) ≤ Real.log (Real.log (n : ℝ)) := hPad.2.2.1
  have ha_ge_4sq : 4 * (1 + M) ^ 2 ≤ phaseNat n := by omega
  have ha_ge_4sq_p : 4 * (1 + (M - 1)) ^ 2 ≤ phaseNat n := by
    have : 1 + (M - 1) = M := by omega
    rw [this]
    have h1 := Nat.pow_le_pow_left (show M ≤ 1 + M by omega) 2
    omega
  have ha_ge_L : Real.log (n : ℝ) ≤ (phaseNat n : ℝ) := hPh.1
  have ha_le4L : (phaseNat n : ℝ) ≤ 4 * Real.log (n : ℝ) := hPh.2
  have hp1_120 : p1Bar ∈ Set.Icc (0 : ℝ) (1 / 20) := ⟨hp1.1.le, by linarith only [hp1.2]⟩
  have hexu_co := (hRoots hd p1Bar hp1_120 (Real.log 2) ⟨hq_pos.le, le_rfl⟩).2.1
  have hexu_ch := (hRoots hd p1Bar hp1_120 0 ⟨le_rfl, hq_pos.le⟩).2.1
  clear hRoots
  have hexu_tilt :
      ∃! lamTilde : ℝ, meanS0M (M - 1) lamTilde = (phaseTarget (phaseDelta n) - 1) / (1 - p1Bar) := by
    have h1mp1_pos : 0 < 1 - p1Bar := by linarith only [hp1.2]
    obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
    have htar_icc : (phaseTarget (phaseDelta n) - 1) / (1 - p1Bar) ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) := by
      unfold phaseTarget; unfold deltaStar at hd
      refine ⟨?_, ?_⟩
      · rw [le_div_iff₀ h1mp1_pos]; linarith only [hp1.1, hp1.2, hd.1, hd.2, h2lo]
      · rw [div_le_iff₀ h1mp1_pos]; linarith only [hp1.1, hp1.2, hd.1, hd.2, h2hi]
    let g_sc0 : ℕ → ℝ := fun i ↦ -Real.log 2 / 2 * (i : ℝ) ^ 2
    have hg0_bds : ∀ i ∈ Finset.Icc (0 + 1) (0 + (M - 1)),
        -(((1 + (M - 1) : ℕ) : ℝ) ^ 2 + 1) ≤ g_sc0 i ∧ g_sc0 i ≤ 0 := by
      intro i hi
      dsimp [g_sc0]
      have hsq : (i : ℝ) ^ 2 ≤ ((1 + (M - 1) : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg i)
          (by exact_mod_cast (le_trans (Finset.mem_Icc.mp hi).2 (by omega : 0 + (M - 1) ≤ 1 + (M - 1)))) 2
      have hq_i : (Real.log 2 / 2) * (i : ℝ) ^ 2 ≤ 1 * ((1 + (M - 1) : ℕ) : ℝ) ^ 2 :=
        mul_le_mul (by linarith [Real.log_two_lt_d9]) hsq (sq_nonneg _) zero_le_one
      have hq_nn : 0 ≤ (Real.log 2 / 2) * (i : ℝ) ^ 2 :=
        mul_nonneg (div_nonneg hq_pos.le zero_le_two) (sq_nonneg _)
      rw [show -Real.log 2 / 2 * (i : ℝ) ^ 2 = -((Real.log 2 / 2) * (i : ℝ) ^ 2) by ring]
      exact ⟨by linarith only [hq_i], by linarith only [hq_nn]⟩
    have hm0 := windowGibbs_master_v13 (m := 0) (M := M - 1) (Nat.zero_le 1) hMp7 hg0_bds
    obtain ⟨hexu_w, _⟩ := hm0.2.2.2.2 _ htar_icc
    have hmean_eq : ∀ l : ℝ, wMean_v13 (Finset.Icc (0 + 1) (0 + (M - 1))) g_sc0 l = meanS0M (M - 1) l := by
      intro l
      have hsh0 := (wProb_and_wMean_shift_S0M_v13 (m := 0) (M := M - 1) (by omega) l).2
      simpa only [Nat.cast_zero, zero_mul, sub_zero, add_zero] using hsh0
    simpa only [hmean_eq] using hexu_w
  refine ⟨hexu_co, hexu_ch, hexu_tilt, ?_⟩
  intro r_co r_ch hr_co hobj_co hr_ch hobj_ch k_co k_ch
  have hpad_shift := hPad.2.2.2.1
  have hKcap_fn := hPad.2.2.2.2.1
  obtain ⟨_, hk_co1, hk_co_ub, hk_co_lb, hk_co_r, hk_co_icc, _, _, _, _, _, htar_co, _⟩ :=
    hPad.2.2.2.2.2 r_co hr_co
  obtain ⟨_, _, _, _, _, _, hk_ch1, hk_ch_ub, hk_ch_lb, hk_ch_r, hk_ch_icc, _, htar_ch⟩ :=
    hPad.2.2.2.2.2 r_ch hr_ch
  clear hPad
  have hTk_co_cap := hKcap_fn (k_co : ℝ) hk_co_icc hd
  have hTk_ch_cap := hKcap_fn (k_ch : ℝ) hk_ch_icc hd
  clear hKcap_fn
  have hLem32_un :
      let W_tail := Finset.Icc (1 + 1) (1 + (M - 1))
      ∀ u_n : ℝ, u_n ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) →
        ∃ l_lim l_fin : ℝ,
          wMean_v13 W_tail (fun i ↦ -Real.log 2 / 2 * (i : ℝ) ^ 2) l_lim = u_n ∧
          (∑ i ∈ W_tail, (if i ∈ W_tail then
            Real.exp (l_fin * (i : ℝ) + h_sc i) /
              (∑ j ∈ W_tail, Real.exp (l_fin * (j : ℝ) + h_sc j)) else 0) = 1) ∧
          (∑ i ∈ W_tail, (i : ℝ) * (if i ∈ W_tail then
            Real.exp (l_fin * (i : ℝ) + h_sc i) /
              (∑ j ∈ W_tail, Real.exp (l_fin * (j : ℝ) + h_sc j)) else 0) = u_n) ∧
          ((⨅ l : ℝ, (Real.log (∑ i ∈ W_tail, Real.exp (l * (i : ℝ) + h_sc i)) - l * u_n)) =
            -(∑ i ∈ W_tail, (if i ∈ W_tail then
                Real.exp (l_fin * (i : ℝ) + h_sc i) /
                  (∑ j ∈ W_tail, Real.exp (l_fin * (j : ℝ) + h_sc j)) else 0) *
                Real.log (if i ∈ W_tail then
                  Real.exp (l_fin * (i : ℝ) + h_sc i) /
                    (∑ j ∈ W_tail, Real.exp (l_fin * (j : ℝ) + h_sc j)) else 0)) +
              ∑ i ∈ W_tail, (if i ∈ W_tail then
                Real.exp (l_fin * (i : ℝ) + h_sc i) /
                  (∑ j ∈ W_tail, Real.exp (l_fin * (j : ℝ) + h_sc j)) else 0) * h_sc i) ∧
          (∀ i ∈ W_tail,
            2 * c_tail ≤ (if i ∈ W_tail then
              Real.exp (l_fin * (i : ℝ) + h_sc i) /
                (∑ j ∈ W_tail, Real.exp (l_fin * (j : ℝ) + h_sc j)) else 0) ∧
            |(if i ∈ W_tail then
                Real.exp (l_fin * (i : ℝ) + h_sc i) /
                  (∑ j ∈ W_tail, Real.exp (l_fin * (j : ℝ) + h_sc j)) else 0) -
              (if i ∈ W_tail then
                Real.exp (l_lim * (i : ℝ) + (-Real.log 2 / 2 * (i : ℝ) ^ 2)) /
                  (∑ j ∈ W_tail, Real.exp (l_lim * (j : ℝ) + (-Real.log 2 / 2 * (j : ℝ) ^ 2)))
              else 0)| ≤ C_opt_tail / (phaseNat n : ℝ)) := by
    intro W_tail u_n hu_n
    obtain ⟨⟨l_lim, hl_lim, _⟩, ⟨l_fin, hl_fin, _⟩, hsp⟩ :=
      hLem32_tail ha_ge_4sq_p (m := 1) le_rfl hu_n
    obtain ⟨-, -, -, -, hp_s, hp_m, hF_e, -, hp_b⟩ := hsp hl_lim hl_fin
    exact ⟨l_lim, l_fin, hl_lim, hp_s, hp_m, hF_e, fun i hi ↦ ⟨(hp_b i hi).1, (hp_b i hi).2.2⟩⟩
  clear hLem32_tail
  obtain ⟨k_co_vec, kp_co, hco_blk, hco_mass, hco_pos, hco_kp_def, hco_part, hco_vm,
    _, hco_sgn, hco_P, hco_G, hco_rat, hco_log_unm⟩ :=
    build_selectedProfile_at_k_regimeC_v13 hM hn8 ha_ge_4sq ha_ge_4sq_p ha_ge_L ha_le4L
      hp1 hct_pos hc_pos hc_le_p1 hc_le_ct hCopt_pos hBerr_tail_def hCround_cap_def hCp_ge
      hk_th1 hk_th2 hL_ge2 hll_ge1 hd hk_co1 hk_co_lb hk_co_ub hTk_co_cap htar_co hLem32_un
  obtain ⟨k_ch_vec, kp_ch, hch_blk, hch_mass, hch_pos, hch_kp_def, hch_part, hch_vm,
    hch_unm, _, hch_P, hch_G, hch_rat, hch_log_unm⟩ :=
    build_selectedProfile_at_k_regimeC_v13 hM hn8 ha_ge_4sq ha_ge_4sq_p ha_ge_L ha_le4L
      hp1 hct_pos hc_pos hc_le_p1 hc_le_ct hCopt_pos hBerr_tail_def hCround_cap_def hCp_ge
      hk_th1 hk_th2 hL_ge2 hll_ge1 hd hk_ch1 hk_ch_lb hk_ch_ub hTk_ch_cap htar_ch hLem32_un
  clear hLem32_un
  have hobj_inc : ∀ (tau : ℝ), tau ∈ Set.Icc (0 : ℝ) (Real.log 2) →
      ∀ {a b : ℝ},
        a ∈ Set.Icc (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
                    (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n) →
        b ∈ Set.Icc (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
                    (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n) →
        a ≤ b →
        ((1 / Real.log 2) * (Real.log (n : ℝ)) ^ 2) * (b - a) ≤ obj_cap tau b - obj_cap tau a := by
    intro tau htau a b ha hb hab
    have hsl_tau := hSlope.2 hM hd p1Bar hp1_120 tau htau
    have hsub : Set.Icc a b ⊆ Set.Icc
        (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n) :=
      fun x hx ↦ ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
    exact derivative_lower_bound_mul_sub_le_sub hab
      (fun x hx ↦ (hsl_tau x (hsub hx)).1.continuousAt.continuousWithinAt)
      (fun x hx ↦ (hsl_tau x (hsub (Ioo_subset_Icc_self hx))).1.differentiableWithinAt)
      (fun x hx ↦ by
        have hd_abs : |deriv (obj_cap tau) x - (2 / Real.log 2) * (Real.log (n : ℝ)) ^ 2| ≤
            K_slope * Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) :=
          (hsl_tau x (hsub (Ioo_subset_Icc_self hx))).2
        have hd_b := (abs_le.mp hd_abs).1
        have hm_sl := mul_le_mul_of_nonneg_left hsl_dom hL_pos.le
        have e1 : Real.log (n : ℝ) * (K_slope * Real.log (Real.log (n : ℝ))) =
            K_slope * Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) := by ring
        have e2 : Real.log (n : ℝ) * ((1 / Real.log 2) * Real.log (n : ℝ)) =
            (1 / Real.log 2) * (Real.log (n : ℝ)) ^ 2 := by ring
        have e3 : 2 / Real.log 2 * (Real.log (n : ℝ)) ^ 2 =
            2 * ((1 / Real.log 2) * (Real.log (n : ℝ)) ^ 2) := by ring
        linarith only [hd_b, hm_sl, e1, e2, e3])
  clear hSlope
  have hr_co_icc : r_co ∈ Set.Icc
      (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n) :=
    ⟨by linarith only [hr_co.1, hpad_shift, hL_pos], by linarith only [hr_co.2, hpad_shift, hL_pos]⟩
  have hr_ch_icc : r_ch ∈ Set.Icc
      (phaseRootCenter n - (C_corr + 1) * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + (C_corr + 1) * logLogOrder n * phaseRootGapRadius n) :=
    ⟨by linarith only [hr_ch.1, hpad_shift, hL_pos], by linarith only [hr_ch.2, hpad_shift, hL_pos]⟩
  have hobj_co_k : (16 / Real.log 2) * (Real.log (n : ℝ)) ^ 2 ≤ obj_cap (Real.log 2) (k_co : ℝ) := by
    have hinc := hobj_inc (Real.log 2) ⟨hq_pos.le, le_rfl⟩ hr_co_icc hk_co_icc (by linarith only [hk_co_r])
    rw [hobj_co, sub_zero] at hinc
    have h16 : (16 : ℝ) ≤ (k_co : ℝ) - r_co := by linarith only [hk_co_r]
    calc (16 / Real.log 2) * (Real.log (n : ℝ)) ^ 2
        = ((1 / Real.log 2) * (Real.log (n : ℝ)) ^ 2) * 16 := by ring
      _ ≤ ((1 / Real.log 2) * (Real.log (n : ℝ)) ^ 2) * ((k_co : ℝ) - r_co) :=
          mul_le_mul_of_nonneg_left h16 (by positivity)
      _ ≤ obj_cap (Real.log 2) (k_co : ℝ) := hinc
  have hlog_signed_co :
      c_Z * (Real.log (n : ℝ)) ^ 2 ≤ Real.log (completeSignedFirstMoment u k_co_vec) := by
    have hrel_sgn :
        Real.log (completeSignedFirstMoment u k_co_vec) =
          (k_co : ℝ) * Real.log 2 + Real.log (completeUnmarkedFirstMoment u k_co_vec) := by
      have hpos_s : 0 < completeSignedFirstMoment u k_co_vec := completeSignedFirstMoment_pos u k_co_vec
      unfold completeUnmarkedFirstMoment
      have h2_pos : 0 < (2 : ℝ) ^ k_co := by positivity
      have hsum_eq : ∑ j : Fin M, k_co_vec j = k_co := hco_blk
      rw [hsum_eq, Real.log_mul (inv_pos.mpr h2_pos).ne' hpos_s.ne', Real.log_inv, Real.log_pow]
      ring
    have hobj_rel : obj_cap (Real.log 2) (k_co : ℝ) =
        (k_co : ℝ) * Real.log 2 + obj_cap 0 (k_co : ℝ) := by
      dsimp [obj_cap]; ring
    rw [hrel_sgn, hcZ_def]
    have hgap16 : (1 / (2 * Real.log 2)) * (Real.log (n : ℝ)) ^ 2 ≤
        (16 / Real.log 2) * (Real.log (n : ℝ)) ^ 2 -
          (1 / (2 * Real.log 2)) * (Real.log (n : ℝ)) ^ 2 := by
      have hnn : 0 ≤ (Real.log (n : ℝ)) ^ 2 / Real.log 2 := by positivity
      have e1 : (1 / (2 * Real.log 2)) * (Real.log (n : ℝ)) ^ 2 =
          (1 / 2) * ((Real.log (n : ℝ)) ^ 2 / Real.log 2) := by ring
      have e2 : (16 / Real.log 2) * (Real.log (n : ℝ)) ^ 2 =
          16 * ((Real.log (n : ℝ)) ^ 2 / Real.log 2) := by ring
      linarith only [hnn, e1, e2]
    have hco_log_unm' :
        obj_cap 0 (k_co : ℝ) - C_round_cap - C_lip_theta - (M : ℝ) * (1 + 2 * Real.log (n : ℝ)) ≤
          Real.log (completeUnmarkedFirstMoment u k_co_vec) := by
      rw [hClip_def]; exact hco_log_unm
    linarith only [hco_log_unm', hobj_co_k, hobj_rel, hround_dom, hgap16]
  have hobj_ch_k : (1 / Real.log 2) * (Real.log (n : ℝ)) ^ 3 ≤ obj_cap 0 (k_ch : ℝ) := by
    have hinc := hobj_inc 0 ⟨le_rfl, hq_pos.le⟩ hr_ch_icc hk_ch_icc (by linarith only [hk_ch_r, hL_pos])
    rw [hobj_ch, sub_zero] at hinc
    have hL_diff : Real.log (n : ℝ) ≤ (k_ch : ℝ) - r_ch := by linarith only [hk_ch_r]
    calc (1 / Real.log 2) * (Real.log (n : ℝ)) ^ 3
        = ((1 / Real.log 2) * (Real.log (n : ℝ)) ^ 2) * Real.log (n : ℝ) := by ring
      _ ≤ ((1 / Real.log 2) * (Real.log (n : ℝ)) ^ 2) * ((k_ch : ℝ) - r_ch) :=
          mul_le_mul_of_nonneg_left hL_diff (by positivity)
      _ ≤ obj_cap 0 (k_ch : ℝ) := hinc
  have hlog_unm_ch :
      c_Z * (Real.log (n : ℝ)) ^ 3 ≤ Real.log (completeUnmarkedFirstMoment u k_ch_vec) := by
    have hL2_le_L3 : (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ 3 := by
      calc (Real.log (n : ℝ)) ^ 2 = (Real.log (n : ℝ)) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (Real.log (n : ℝ)) ^ 2 * Real.log (n : ℝ) :=
            mul_le_mul_of_nonneg_left (by linarith only [hL_ge2]) (sq_nonneg _)
        _ = (Real.log (n : ℝ)) ^ 3 := by ring
    have hround_L3 :
        C_round_cap + C_lip_theta + (M : ℝ) * (1 + 2 * Real.log (n : ℝ)) ≤
          (1 / (2 * Real.log 2)) * (Real.log (n : ℝ)) ^ 3 :=
      hround_dom.trans (mul_le_mul_of_nonneg_left hL2_le_L3 (by positivity))
    rw [hcZ_def]
    have hhalf_id :
        (1 / Real.log 2) * (Real.log (n : ℝ)) ^ 3 -
            (1 / (2 * Real.log 2)) * (Real.log (n : ℝ)) ^ 3 =
          (1 / (2 * Real.log 2)) * (Real.log (n : ℝ)) ^ 3 := by ring
    have hch_log_unm' :
        obj_cap 0 (k_ch : ℝ) - C_round_cap - C_lip_theta - (M : ℝ) * (1 + 2 * Real.log (n : ℝ)) ≤
          Real.log (completeUnmarkedFirstMoment u k_ch_vec) := by
      rw [hClip_def]; exact hch_log_unm
    linarith only [hch_log_unm', hobj_ch_k, hround_L3, hhalf_id]
  exact ⟨hk_co1, hk_co_ub, hk_ch1, hk_ch_ub, k_co_vec, k_ch_vec, kp_co, kp_ch,
    hco_blk, hco_mass, hch_blk, hch_mass, hco_pos, hch_pos,
    hco_kp_def, hch_kp_def,
    hco_part, hco_vm, hco_sgn, hco_P, fun G ↦ (hco_G G).1,
    hch_part, hch_vm, hch_unm, hch_P, fun G ↦ (hch_G G).2,
    fun lamT hlamT j ↦ ⟨hco_rat lamT hlamT j, hch_rat lamT hlamT j⟩,
    hlog_signed_co, hlog_unm_ch⟩

/-!
## 4. Unconditional Lemma 6.1(i)–(ii) & Scrambled/Middle subprofile sums for selected profiles
-/

private theorem eventually_scrambledRange_commonClass_sum_le_v13
    (M : ℕ) {deltaMinus : ℝ} (hd : 0 < deltaMinus) :
    let c₀ : ℝ := secondMomentExponent deltaMinus
    ∀ᶠ n : ℕ in atTop,
      ∀ {m : ℕ}, m ≤ 1 →
        deltaMinus ≤ phaseDelta n + (m : ℝ) →
        let u : Fin M → ℕ := fun j ↦ phaseNat n - (m + 1 + j.1)
        ∀ (k : Fin M → ℕ) (S : Finset (Fin M → ℕ)),
          (selectedBlockCount k : ℝ) ≤ (n : ℝ) →
          (∀ nu ∈ S, IsPartialSubprofile k nu ∧
            (selectedVertexMass u nu : ℝ) < (n : ℝ) / (Real.log (n : ℝ)) ^ 3) →
          (∑ nu ∈ S, partialDiagonalWeight n u k nu) ≤
              Real.exp ((n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) ∧
            (∑ nu ∈ S, unmarkedDiagonalWeight n u k nu) ≤
              Real.exp ((n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) := by
  intro c₀
  have hc₀_pos : 0 < c₀ := lt_min (half_pos hd) (by norm_num)
  have hc₀_le : c₀ ≤ 1 / 60 := min_le_right _ _
  have hc₀_le_d : 2 * c₀ ≤ deltaMinus := by
    have : c₀ ≤ deltaMinus / 2 := min_le_left _ _; linarith
  obtain ⟨_, c₂, _, hc₂_pos, hLem21⟩ := exists_uniform_phaseExpansion_and_adjacent_bounds
  -- `(log n)^4 = o(n^(c₀ / 2))` absorbs both `(log n)^(...)` in `mu` and `Real.log n` in the exponent!
  have ho_c : (fun x : ℝ ↦ (Real.log x) ^ ((4 : ℕ) : ℝ)) =o[atTop] (fun x : ℝ ↦ x ^ (c₀ / 2)) :=
    isLittleO_log_rpow_rpow_atTop ((4 : ℕ) : ℝ) (half_pos hc₀_pos)
  set eps_c : ℝ := min 1 (c₂ / 2)
  have heps_c : 0 < eps_c := lt_min zero_lt_one (half_pos hc₂_pos)
  have hb_c := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Asymptotics.isLittleO_iff.mp ho_c heps_c)
  have hsq_lo : ∀ᶠ n : ℕ in atTop,
      (3 / 2 : ℝ) * Real.log (n : ℝ) ≤ ((phaseNat n - (M + 2) : ℕ) : ℝ) * q := by
    have hlim := tendsto_phaseNat_add_mul_q_div_logOrder_two 0
    have hlo : ∀ᶠ n : ℕ in atTop,
        (7 / 4 : ℝ) < (((phaseNat n + 0 : ℕ) : ℝ) * q) / logOrder n :=
      (tendsto_order.1 hlim).1 (7 / 4) (by norm_num)
    have hL_big : ∀ᶠ n : ℕ in atTop, 4 * ((M + 2 : ℕ) : ℝ) * q ≤ logOrder n :=
      tendsto_logOrder_atTop.eventually_ge_atTop _
    have hPh_gt : ∀ᶠ n : ℕ in atTop, M + 2 ≤ phaseNat n := by
      filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (((M + 2 : ℕ) : ℝ)),
        eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hLM hPh
      exact_mod_cast le_trans hLM hPh.1
    filter_upwards [hlo, hL_big, hPh_gt, eventually_gt_atTop 1] with n hlon hLb hPhn hn1
    have hL_pos : 0 < logOrder n := Real.log_pos (by exact_mod_cast hn1)
    rw [Nat.add_zero, lt_div_iff₀ hL_pos] at hlon
    rw [Nat.cast_sub hPhn, sub_mul]; dsimp [logOrder] at hlon hLb
    linarith
  filter_upwards [eventually_ge_atTop 20,
    tendsto_logOrder_atTop.eventually_ge_atTop (max 4 ((M + 4 : ℕ) : ℝ)),
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    eventually_two_mul_phaseNat_le, hLem21, hb_c, hsq_lo] with
    n hn20 hLmax hPh h2ph h21 hbn hsq m hm hdm_le u k S hk_le_n hS
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hL4 : (4 : ℝ) ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hLmax
  have hL_pos : 0 < Real.log (n : ℝ) := by linarith
  have ha_ge_M4 : M + 4 ≤ phaseNat n := by
    have : ((M + 4 : ℕ) : ℝ) ≤ (phaseNat n : ℝ) := ((le_max_right _ _).trans hLmax).trans hPh.1
    exact_mod_cast this
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hL_pos _),
    abs_of_pos (Real.rpow_pos_of_pos hn_pos _), Real.rpow_natCast] at hbn
  -- Monotonicity of `mu n s` as `s` decreases in `[phaseNat n - (M + 1), phaseNat n - 1]`
  have hmu_anti : ∀ r : ℕ, r ≤ M →
      mu n (phaseNat n - (m + 1)) ≤ mu n (phaseNat n - (m + 1 + r)) := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
      have hr_le : r ≤ M := Nat.le_of_succ_le hr
      set t : ℕ := phaseNat n - (m + 1 + r)
      have ht_pos : 1 ≤ t := by dsimp [t]; omega
      have ht_le : t ≤ n := by dsimp [t]; omega
      have hstep := log_mu_pred_sub_log_mu ht_pos ht_le
      have ht_ge : phaseNat n - (M + 2) ≤ t - 1 := by dsimp [t]; omega
      have hqt_ge : (3 / 2 : ℝ) * Real.log (n : ℝ) ≤ ((t - 1 : ℕ) : ℝ) * q :=
        hsq.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast ht_ge) q_pos.le)
      have hlog_t_nn : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg (by exact_mod_cast ht_pos)
      have hlog_den : Real.log (((n - t : ℕ) + 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (show n - t + 1 ≤ n by omega))
      have hdiff_nn : 0 ≤ Real.log (mu n (t - 1)) - Real.log (mu n t) := by linarith
      have hle_step : mu n t ≤ mu n (t - 1) := by
        rw [← Real.exp_log (mu_pos ht_le), ← Real.exp_log (mu_pos (by omega : t - 1 ≤ n))]
        exact Real.exp_le_exp.mpr (by linarith)
      have hsub_eq : t - 1 = phaseNat n - (m + 1 + (r + 1)) := by dsimp [t]; omega
      rw [← hsub_eq]
      exact (ih hr_le).trans hle_step
  -- Lower bound `mu_a := 2 * n^(1 + 3 * c₀ / 2) ≤ mu n (phaseNat n - (m + 1))`
  set mu_a : ℝ := 2 * (n : ℝ) ^ (1 + 3 * c₀ / 2)
  have hmu_a_pos : 0 < mu_a := by dsimp [mu_a]; positivity
  have h2_le_c2 : 2 ≤ c₂ * (n : ℝ) ^ (c₀ / 2) * (Real.log (n : ℝ)) ^ (-4 : ℝ) := by
    have h1 : (Real.log (n : ℝ)) ^ 4 ≤ (c₂ / 2) * (n : ℝ) ^ (c₀ / 2) :=
      hbn.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hn_pos.le _))
    have hL4_pos : 0 < (Real.log (n : ℝ)) ^ 4 := pow_pos hL_pos 4
    have hrpow_inv : (Real.log (n : ℝ)) ^ (-4 : ℝ) = ((Real.log (n : ℝ)) ^ 4)⁻¹ := by
      rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hL_pos.le, Real.rpow_natCast]
    rw [hrpow_inv]
    have hm : 1 ≤ ((Real.log (n : ℝ)) ^ 4)⁻¹ * ((c₂ / 2) * (n : ℝ) ^ (c₀ / 2)) := by
      have hmul := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hL4_pos.le)
      rwa [inv_mul_cancel₀ hL4_pos.ne'] at hmul
    linarith [show ((Real.log (n : ℝ)) ^ 4)⁻¹ * (c₂ / 2 * (n : ℝ) ^ (c₀ / 2)) =
      (1 / 2) * (c₂ * (n : ℝ) ^ (c₀ / 2) * ((Real.log (n : ℝ)) ^ 4)⁻¹) by ring]
  have hmu_top_lb : mu_a ≤ mu n (phaseNat n - (m + 1)) := by
    have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hL_ge1 : (1 : ℝ) ≤ logOrder n := by dsimp [logOrder]; linarith
    obtain ⟨h2lo, _⟩ := two_div_log_two_bounds
    rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
    · simp only [Nat.cast_zero, add_zero, Nat.zero_add] at hdm_le ⊢
      have hcl5 := h21.2.2.2.2.1
      have hexp_n : 1 + 2 * c₀ ≤ 1 + phaseDelta n := by linarith [hc₀_le_d, hdm_le]
      have hexp_L : (-4 : ℝ) ≤ 2 / q - 3 / 2 - phaseDelta n := by
        unfold q; linarith [phaseDelta_lt_one n, h2lo]
      calc mu_a
          = 2 * (n : ℝ) ^ (1 + 3 * c₀ / 2) := rfl
        _ ≤ (c₂ * (n : ℝ) ^ (c₀ / 2) * (Real.log (n : ℝ)) ^ (-4 : ℝ)) *
              (n : ℝ) ^ (1 + 3 * c₀ / 2) :=
            mul_le_mul_of_nonneg_right h2_le_c2 (Real.rpow_nonneg hn_pos.le _)
        _ = c₂ * ((n : ℝ) ^ (c₀ / 2) * (n : ℝ) ^ (1 + 3 * c₀ / 2)) *
              (logOrder n) ^ (-4 : ℝ) := by dsimp [logOrder]; ring
        _ = c₂ * (n : ℝ) ^ (1 + 2 * c₀) * (logOrder n) ^ (-4 : ℝ) := by
            rw [← Real.rpow_add hn_pos]; congr 3; ring
        _ ≤ c₂ * (n : ℝ) ^ (1 + phaseDelta n) *
              (logOrder n) ^ (2 / q - 3 / 2 - phaseDelta n) := by
            refine mul_le_mul
              (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn_ge1 hexp_n) hc₂_pos.le)
              (Real.rpow_le_rpow_of_exponent_le hL_ge1 hexp_L)
              (Real.rpow_nonneg hL_pos.le _) (by positivity)
        _ ≤ mu n (phaseNat n - 1) := hcl5
    · have hcl6 := h21.2.2.2.2.2
      have hexp_n : 1 + 2 * c₀ ≤ 2 + phaseDelta n := by linarith [phaseDelta_nonneg n, hc₀_le]
      have hexp_L : (-4 : ℝ) ≤ 2 / q - 5 / 2 - phaseDelta n := by
        unfold q; linarith [phaseDelta_lt_one n, h2lo]
      calc mu_a
          ≤ (c₂ * (n : ℝ) ^ (c₀ / 2) * (Real.log (n : ℝ)) ^ (-4 : ℝ)) *
              (n : ℝ) ^ (1 + 3 * c₀ / 2) :=
            mul_le_mul_of_nonneg_right h2_le_c2 (Real.rpow_nonneg hn_pos.le _)
        _ = c₂ * (n : ℝ) ^ (1 + 2 * c₀) * (logOrder n) ^ (-4 : ℝ) := by
            dsimp [logOrder]
            rw [show c₂ * (n : ℝ) ^ (c₀ / 2) * (Real.log (n : ℝ)) ^ (-4 : ℝ) *
                (n : ℝ) ^ (1 + 3 * c₀ / 2) =
              c₂ * ((n : ℝ) ^ (c₀ / 2) * (n : ℝ) ^ (1 + 3 * c₀ / 2)) *
                (Real.log (n : ℝ)) ^ (-4 : ℝ) by ring,
              ← Real.rpow_add hn_pos]
            congr 3; ring
        _ ≤ c₂ * (n : ℝ) ^ (2 + phaseDelta n) *
              (logOrder n) ^ (2 / q - 5 / 2 - phaseDelta n) := by
            refine mul_le_mul
              (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn_ge1 hexp_n) hc₂_pos.le)
              (Real.rpow_le_rpow_of_exponent_le hL_ge1 hexp_L)
              (Real.rpow_nonneg hL_pos.le _) (by positivity)
        _ ≤ mu n (phaseNat n - 2) := hcl6
  have hmu_lb : ∀ j : Fin M, mu_a ≤ mu n (u j) := fun j ↦
    hmu_top_lb.trans (hmu_anti j.1 (by omega))
  -- Verify scrambled hypotheses for `S`
  have hS_scr : ∀ nu ∈ S,
      IsPartialSubprofile k nu ∧
      2 * selectedVertexMass u nu ≤ n ∧
      ∀ j : Fin M, Real.exp ((u j : ℝ) * (selectedVertexMass u nu : ℝ) / (n : ℝ)) ≤ 2 := by
    intro nu hnuS
    obtain ⟨hsub, hm_lt⟩ := hS nu hnuS
    have hL3_ge64 : (64 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := by
      calc (64 : ℝ) = 4 ^ 3 := by norm_num
        _ ≤ (Real.log (n : ℝ)) ^ 3 := pow_le_pow_left₀ (by norm_num) hL4 3
    have hm2 : 2 * selectedVertexMass u nu ≤ n := by
      have h1 : (selectedVertexMass u nu : ℝ) ≤ (n : ℝ) / 64 :=
        hm_lt.le.trans (div_le_div_of_nonneg_left hn_pos.le (by norm_num) hL3_ge64)
      have h2 : ((2 * selectedVertexMass u nu : ℕ) : ℝ) ≤ (n : ℝ) := by push_cast; linarith
      exact_mod_cast h2
    refine ⟨hsub, hm2, fun j ↦ ?_⟩
    have huj_le : (u j : ℝ) ≤ 4 * Real.log (n : ℝ) :=
      le_trans (by exact_mod_cast Nat.sub_le (phaseNat n) _) hPh.2
    have hprod_le : (u j : ℝ) * (selectedVertexMass u nu : ℝ) / (n : ℝ) ≤ Real.log 2 := by
      calc (u j : ℝ) * (selectedVertexMass u nu : ℝ) / (n : ℝ)
          ≤ (4 * Real.log (n : ℝ)) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) / (n : ℝ) := by
            apply div_le_div_of_nonneg_right _ hn_pos.le
            exact mul_le_mul huj_le hm_lt.le (Nat.cast_nonneg _) (by positivity)
        _ = 4 / (Real.log (n : ℝ)) ^ 2 := by field_simp [hn_pos.ne', hL_pos.ne']
        _ ≤ 4 / 16 := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
            (calc (16 : ℝ) = 4 ^ 2 := by norm_num
              _ ≤ (Real.log (n : ℝ)) ^ 2 := pow_le_pow_left₀ (by norm_num) hL4 2)
        _ ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    exact (Real.exp_le_exp.mpr hprod_le).trans_eq (Real.exp_log two_pos)
  obtain ⟨hW_le_F1, hF1_le_exp⟩ :=
    sum_scrambled_partial_and_unmarkedDiagonalWeight_le_exp hn1 hmu_a_pos hmu_lb S hS_scr
  -- Bound `2 * K^2 / mu_a ≤ n^(1 - c₀) / log n`
  have hexp_le :
      Real.exp (2 * (selectedBlockCount k : ℝ) ^ 2 / mu_a) ≤
        Real.exp ((n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hL_le_pow : Real.log (n : ℝ) ≤ (n : ℝ) ^ (c₀ / 2) := by
      have h1 : Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 4 := by
        have h3 : 1 ≤ (Real.log (n : ℝ)) ^ 3 := one_le_pow₀ (by linarith)
        calc Real.log (n : ℝ) = Real.log (n : ℝ) * 1 := (mul_one _).symm
          _ ≤ Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ 3 := mul_le_mul_of_nonneg_left h3 hL_pos.le
          _ = (Real.log (n : ℝ)) ^ 4 := (pow_succ' _ 3).symm
      exact h1.trans (hbn.trans
        ((mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hn_pos.le _)).trans_eq
          (one_mul _)))
    calc 2 * (selectedBlockCount k : ℝ) ^ 2 / mu_a
        ≤ 2 * (n : ℝ) ^ 2 / (2 * (n : ℝ) ^ (1 + 3 * c₀ / 2)) := by
          dsimp [mu_a]
          apply div_le_div_of_nonneg_right _ hmu_a_pos.le
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (Nat.cast_nonneg _) hk_le_n 2) zero_le_two
      _ = (n : ℝ) ^ (1 - c₀) / (n : ℝ) ^ (c₀ / 2) := by
          have hpow2 : (n : ℝ) ^ 2 = (n : ℝ) ^ ((2 : ℝ)) := (Real.rpow_two (n : ℝ)).symm
          have hsplit1 : (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ (1 - c₀) * (n : ℝ) ^ (1 + c₀) := by
            rw [← Real.rpow_add hn_pos]; congr 1; ring
          have hsplit2 : (n : ℝ) ^ (1 + 3 * c₀ / 2) = (n : ℝ) ^ (c₀ / 2) * (n : ℝ) ^ (1 + c₀) := by
            rw [← Real.rpow_add hn_pos]; congr 1; ring
          rw [hpow2, hsplit1, hsplit2]
          have hp_ne : (n : ℝ) ^ (1 + c₀) ≠ 0 := (Real.rpow_pos_of_pos hn_pos _).ne'
          have hc_ne : (n : ℝ) ^ (c₀ / 2) ≠ 0 := (Real.rpow_pos_of_pos hn_pos _).ne'
          field_simp [hp_ne, hc_ne]
      _ ≤ (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ) :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg hn_pos.le _) hL_pos hL_le_pow
  exact ⟨hW_le_F1.trans (hF1_le_exp.trans hexp_le), hF1_le_exp.trans hexp_le⟩

/-- **Unconditional Lemma 6.1(i)–(ii) & Scrambled/Middle common-class subprofile sums in `Regime U`
(`main.tex` lines 900–916, 1106–1121):**
for every `7 ≤ M`, `m ≤ 1`, `δ_- ∈ (x₀, 1 + δ_*]`, and overlap exponent `C_ov : ℝ`, there exist
deterministic constants `C_corr > 0`, `c_star > 0`, `c_Z > 0`, and `c_W > 0` such that eventually
whenever `δ_n + m ∈ [δ_-, 1 + δ_*]`, the selected integer profiles `k_co_vec, k_ch_vec` of
Proposition 5.3 satisfy **unconditionally**:
1. **Lemma 6.1(i):** `W(ν), F_1^ch(ν) ≤ exp(-c_W m_ν) ≤ exp(-c_W n / (log n)³)` for all `ν` with
   `m_ν ≥ n / (log n)³` and `n - m_ν > 2^{-(M+5)} n`;
2. **Lemma 6.1(ii):** both chains `W(ν) ≤ (2 n^{-3/2})^{∑(k_i - ν_i)} exp(-c_Z (log n)²) ≤ exp(-(n - m_ν)/2)`
   and `F_1^ch(ν) ≤ (n^{-3/2})^{∑(k_i - ν_i)} exp(-c_Z (log n)³) ≤ exp(-(n - m_ν)/2)` for
   `n - m_ν ≤ 2^{-(M+5)} n`;
3. **Proposition 7.3 Scrambled & Middle subprofile sums:**
   `∑_{m_ν < n / (log n)³} ≤ exp(n^{1 - c₀} / log n)` and
   `exp(C_ov (log n)⁵) * ∑_{m_ν ≥ n / (log n)³, n - m_ν ≥ n^{1 - c₀}} ≤ 1`
   (`c₀ = secondMomentExponent δ_-`). -/
theorem eventually_selectedProfiles_lemma61_and_commonClass_sums_regimeU
    {M m : ℕ} (hM : 7 ≤ M) (hm : m ≤ 1)
    {deltaMinus : ℝ} (hd : deltaMinus ∈ Set.Ioc criticalPhaseX0 (1 + deltaStar))
    (C_ov : ℝ) :
    ∃ C_corr c_star c_Z c_W : ℝ,
      0 < C_corr ∧ 0 < c_star ∧ 0 < c_Z ∧ 0 < c_W ∧
      ∀ᶠ n : ℕ in atTop,
        phaseDelta n + (m : ℝ) ∈ Set.Icc deltaMinus (1 + deltaStar) →
          let u : Fin M → ℕ := fun j ↦ phaseNat n - (m + 1 + j.1)
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
            1 ≤ k_co ∧ (k_co : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ∧
            1 ≤ k_ch ∧ (k_ch : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ∧
            ∃ (k_co_vec k_ch_vec : Fin M → ℕ) (kp_co kp_ch : ColoringProfile (phaseNat n)),
              selectedBlockCount k_co_vec = k_co ∧
              selectedVertexMass u k_co_vec = n ∧
              selectedBlockCount k_ch_vec = k_ch ∧
              selectedVertexMass u k_ch_vec = n ∧
              (∀ j : Fin M, 0 < k_co_vec j ∧ c_star ≤ (k_co_vec j : ℝ) / (k_co : ℝ)) ∧
              (∀ j : Fin M, 0 < k_ch_vec j ∧ c_star ≤ (k_ch_vec j : ℝ) / (k_ch : ℝ)) ∧
              (∀ idx : Fin (phaseNat n),
                kp_co idx = ∑ j : Fin M, if u j = idx.1 + 1 then k_co_vec j else 0) ∧
              (∀ idx : Fin (phaseNat n),
                kp_ch idx = ∑ j : Fin M, if u j = idx.1 + 1 then k_ch_vec j else 0) ∧
              ColoringProfile.partCount kp_co = k_co ∧
              ColoringProfile.vertexMass kp_co = n ∧
              (signedProfileExpectation n kp_co).toReal = completeSignedFirstMoment u k_co_vec ∧
              (∀ P : ProfilePartition n kp_co,
                P.1.parts.card = k_co ∧
                ∀ D ∈ P.1.parts, phaseNat n - (m + M) ≤ D.card ∧ D.card ≤ phaseNat n - (m + 1)) ∧
              (∀ G : LabeledGraph n,
                (∃ P : ProfilePartition n kp_co, G ∈ partitionCocoloringEvent P.1) →
                  cochromaticNumber G ≤ k_co) ∧
              ColoringProfile.partCount kp_ch = k_ch ∧
              ColoringProfile.vertexMass kp_ch = n ∧
              (profileColoringExpectation n kp_ch).toReal = completeUnmarkedFirstMoment u k_ch_vec ∧
              (∀ P : ProfilePartition n kp_ch,
                P.1.parts.card = k_ch ∧
                ∀ D ∈ P.1.parts, phaseNat n - (m + M) ≤ D.card ∧ D.card ≤ phaseNat n - (m + 1)) ∧
              (∀ G : LabeledGraph n,
                (∃ P : ProfilePartition n kp_ch, G ∈ partitionColoringEvent P.1) →
                  chromaticNumberNat G ≤ k_ch) ∧
              c_Z * (Real.log (n : ℝ)) ^ 2 ≤ Real.log (completeSignedFirstMoment u k_co_vec) ∧
              c_Z * (Real.log (n : ℝ)) ^ 3 ≤ Real.log (completeUnmarkedFirstMoment u k_ch_vec) ∧
              -- Unconditional Lemma 6.1(i)
              (∀ nu : Fin M → ℕ,
                IsPartialSubprofile k_co_vec nu →
                (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤ (selectedVertexMass u nu : ℝ) →
                ((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ) < ((n - selectedVertexMass u nu : ℕ) : ℝ) →
                partialDiagonalWeight n u k_co_vec nu ≤
                    Real.exp (-c_W * (selectedVertexMass u nu : ℝ)) ∧
                  Real.exp (-c_W * (selectedVertexMass u nu : ℝ)) ≤
                    Real.exp (-c_W * (n : ℝ) / (Real.log (n : ℝ)) ^ 3)) ∧
              (∀ nu : Fin M → ℕ,
                IsPartialSubprofile k_ch_vec nu →
                (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤ (selectedVertexMass u nu : ℝ) →
                ((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ) < ((n - selectedVertexMass u nu : ℕ) : ℝ) →
                unmarkedDiagonalWeight n u k_ch_vec nu ≤
                    Real.exp (-c_W * (selectedVertexMass u nu : ℝ)) ∧
                  Real.exp (-c_W * (selectedVertexMass u nu : ℝ)) ≤
                    Real.exp (-c_W * (n : ℝ) / (Real.log (n : ℝ)) ^ 3)) ∧
              -- Unconditional Lemma 6.1(ii)
              (∀ nu : Fin M → ℕ,
                IsPartialSubprofile k_co_vec nu →
                ((n - selectedVertexMass u nu : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ) →
                partialDiagonalWeight n u k_co_vec nu ≤
                    (2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ j, (k_co_vec j - nu j)) *
                      Real.exp (-c_Z * (Real.log (n : ℝ)) ^ 2) ∧
                  (2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ j, (k_co_vec j - nu j)) *
                      Real.exp (-c_Z * (Real.log (n : ℝ)) ^ 2) ≤
                    Real.exp (-(((n - selectedVertexMass u nu : ℕ) : ℝ) / 2))) ∧
              (∀ nu : Fin M → ℕ,
                IsPartialSubprofile k_ch_vec nu →
                ((n - selectedVertexMass u nu : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ) →
                unmarkedDiagonalWeight n u k_ch_vec nu ≤
                    ((n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ j, (k_ch_vec j - nu j)) *
                      Real.exp (-c_Z * (Real.log (n : ℝ)) ^ 3) ∧
                  ((n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ j, (k_ch_vec j - nu j)) *
                      Real.exp (-c_Z * (Real.log (n : ℝ)) ^ 3) ≤
                    Real.exp (-(((n - selectedVertexMass u nu : ℕ) : ℝ) / 2))) ∧
              -- Unconditional Scrambled & Middle subprofile sums
              (∀ S_scr : Finset (Fin M → ℕ),
                (∀ nu ∈ S_scr, IsPartialSubprofile k_co_vec nu ∧
                  (selectedVertexMass u nu : ℝ) < (n : ℝ) / (Real.log (n : ℝ)) ^ 3) →
                (∑ nu ∈ S_scr, partialDiagonalWeight n u k_co_vec nu) ≤
                  Real.exp ((n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ))) ∧
              (∀ S_scr : Finset (Fin M → ℕ),
                (∀ nu ∈ S_scr, IsPartialSubprofile k_ch_vec nu ∧
                  (selectedVertexMass u nu : ℝ) < (n : ℝ) / (Real.log (n : ℝ)) ^ 3) →
                (∑ nu ∈ S_scr, unmarkedDiagonalWeight n u k_ch_vec nu) ≤
                  Real.exp ((n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ))) ∧
              (∀ S_mid : Finset (Fin M → ℕ),
                (∀ nu ∈ S_mid, IsPartialSubprofile k_co_vec nu ∧
                  (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤ (selectedVertexMass u nu : ℝ) ∧
                  (n : ℝ) ^ (1 - c₀) ≤ ((n - selectedVertexMass u nu : ℕ) : ℝ)) →
                Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
                  (∑ nu ∈ S_mid, partialDiagonalWeight n u k_co_vec nu) ≤ 1) ∧
              (∀ S_mid : Finset (Fin M → ℕ),
                (∀ nu ∈ S_mid, IsPartialSubprofile k_ch_vec nu ∧
                  (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤ (selectedVertexMass u nu : ℝ) ∧
                  (n : ℝ) ^ (1 - c₀) ≤ ((n - selectedVertexMass u nu : ℕ) : ℝ)) →
                Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
                  (∑ nu ∈ S_mid, unmarkedDiagonalWeight n u k_ch_vec nu) ≤ 1)) := by
  obtain ⟨C_corr, c_star, c_Z, C_p, hCc_pos, hcs_pos, hcZ_pos, _, hProp53⟩ :=
    eventually_selectedProfiles_prop53_regimeU hM
  obtain ⟨c_W, hcW_pos, hLem61_i⟩ :=
    eventually_commonClass_subprofile_le_regimeU hM hm hd C_p
  obtain ⟨⟨hx0_pos, _⟩, _⟩ := criticalPhaseX0_bounds_and_sign
  have hd_pos : 0 < deltaMinus := lt_trans (lt_of_le_of_lt (by norm_num) hx0_pos) hd.1
  refine ⟨C_corr, c_star, c_Z, c_W, hCc_pos, hcs_pos, hcZ_pos, hcW_pos, ?_⟩
  have ha_ge : ∀ᶠ n : ℕ in atTop, M + 4 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (((M + 4 : ℕ) : ℝ)),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hL hPh
    exact_mod_cast le_trans hL hPh.1
  filter_upwards [eventually_ge_atTop 4,
    tendsto_logOrder_atTop.eventually_ge_atTop 1,
    ha_ge, hProp53, hLem61_i,
    eventually_partialDiagonalWeight_subprofile_le_exp_neg_half M,
    eventually_unmarkedDiagonalWeight_subprofile_le_exp_neg_half M,
    eventually_scrambledRange_commonClass_sum_le_v13 M hd_pos,
    eventually_middleRange_commonClass_sum_small_regimeU hM hm hd C_p C_ov zero_lt_one] with
    n hn4 hL1 ha_n h53 h61i h61ii_mk h61ii_ch hScr hMid htd
    u c₀ h_sc F_win obj_win
  obtain ⟨hexu_co, hexu_ch, hexu_lam, hsel⟩ := h53 hm
  obtain ⟨lam, hlam_eq, _⟩ := hexu_lam htd.2
  refine ⟨hexu_co, hexu_ch, ?_⟩
  intro r_co r_ch hr_co hobj_co hr_ch hobj_ch k_co k_ch
  obtain ⟨hk_co1, hk_co_ub, hk_ch1, hk_ch_ub, k_co_vec, k_ch_vec, kp_co, kp_ch,
    hco_blk, hco_mass, hch_blk, hch_mass, hco_pos, hch_pos, hco_kp_def, hch_kp_def,
    hco_part, hco_vm, hco_sgn, hco_P, hco_G,
    hch_part, hch_vm, hch_unm, hch_P, hch_G,
    hrat_both, hmom_co, hmom_ch⟩ := hsel hr_co hobj_co hr_ch hobj_ch
  have hL_ge1 : (1 : ℝ) ≤ Real.log (n : ℝ) := hL1
  have hco_exp : Real.exp (c_Z * (Real.log (n : ℝ)) ^ 2) ≤ completeSignedFirstMoment u k_co_vec := by
    rw [← Real.exp_log (completeSignedFirstMoment_pos u k_co_vec)]
    exact Real.exp_le_exp.mpr hmom_co
  have hch_exp : Real.exp (c_Z * (Real.log (n : ℝ)) ^ 3) ≤ completeUnmarkedFirstMoment u k_ch_vec := by
    have hpos_unm : 0 < completeUnmarkedFirstMoment u k_ch_vec := by
      unfold completeUnmarkedFirstMoment
      exact mul_pos (by positivity) (completeSignedFirstMoment_pos u k_ch_vec)
    rw [← Real.exp_log hpos_unm]
    exact Real.exp_le_exp.mpr hmom_ch
  have hco_ge1 : 1 ≤ completeSignedFirstMoment u k_co_vec :=
    (Real.one_le_exp (by positivity)).trans hco_exp
  have hch_ge1 : 1 ≤ completeUnmarkedFirstMoment u k_ch_vec :=
    (Real.one_le_exp (by positivity)).trans hch_exp
  have hu_bds : ∀ j : Fin M, 1 ≤ u j ∧ phaseNat n - (M + 1) ≤ u j ∧ u j ≤ phaseNat n := by
    intro j; dsimp [u]; exact ⟨by omega, by omega, Nat.sub_le _ _⟩
  have hco_le_n : (selectedBlockCount k_co_vec : ℝ) ≤ (n : ℝ) := by
    rw [hco_blk]; exact hk_co_ub.trans (div_le_self (Nat.cast_nonneg n) hL_ge1)
  have hch_le_n : (selectedBlockCount k_ch_vec : ℝ) ≤ (n : ℝ) := by
    rw [hch_blk]; exact hk_ch_ub.trans (div_le_self (Nat.cast_nonneg n) hL_ge1)
  have hrat_co : ∀ j : Fin M,
      |(k_co_vec j : ℝ) / (selectedBlockCount k_co_vec : ℝ) - gibbsProbS0M M lam ((j.1 : ℤ) + 1)| ≤
        C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := fun j ↦ by
    rw [hco_blk]; exact (hrat_both lam hlam_eq j).1
  have hrat_ch : ∀ j : Fin M,
      |(k_ch_vec j : ℝ) / (selectedBlockCount k_ch_vec : ℝ) - gibbsProbS0M M lam ((j.1 : ℤ) + 1)| ≤
        C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := fun j ↦ by
    rw [hch_blk]; exact (hrat_both lam hlam_eq j).2
  exact ⟨hk_co1, hk_co_ub, hk_ch1, hk_ch_ub, k_co_vec, k_ch_vec, kp_co, kp_ch,
    hco_blk, hco_mass, hch_blk, hch_mass, hco_pos, hch_pos, hco_kp_def, hch_kp_def,
    hco_part, hco_vm, hco_sgn, hco_P, hco_G,
    hch_part, hch_vm, hch_unm, hch_P, hch_G,
    hmom_co, hmom_ch,
    fun nu hsub hmlo hrem ↦
      (h61i htd lam hlam_eq k_co_vec nu hco_mass hrat_co hsub hmlo hrem).1 hco_ge1,
    fun nu hsub hmlo hrem ↦
      (h61i htd lam hlam_eq k_ch_vec nu hch_mass hrat_ch hsub hmlo hrem).2 hch_ge1,
    fun nu hsub hrem ↦ h61ii_mk u k_co_vec nu c_Z hcZ_pos.le hu_bds hco_mass hsub hrem hco_exp,
    fun nu hsub hrem ↦ h61ii_ch u k_ch_vec nu c_Z hcZ_pos.le hu_bds hch_mass hsub hrem hch_exp,
    fun S_scr hS ↦ (hScr hm htd.1 k_co_vec S_scr hco_le_n hS).1,
    fun S_scr hS ↦ (hScr hm htd.1 k_ch_vec S_scr hch_le_n hS).2,
    fun S_mid hS ↦
      ((hMid htd lam hlam_eq k_co_vec S_mid hco_mass hrat_co hS).1 hco_ge1).le,
    fun S_mid hS ↦
      ((hMid htd lam hlam_eq k_ch_vec S_mid hch_mass hrat_ch hS).2 hch_ge1).le⟩

/-- **Unconditional Lemma 6.1(i)–(ii) & Scrambled/Middle common-class subprofile sums in `Regime C`
(`main.tex` lines 900–916, 1106–1121):**
for every `8 ≤ M`, `p̄₁ ∈ (0, 1/40]`, `δ_- ∈ (0, δ_*]`, `γ > 0`, and overlap exponent `C_ov : ℝ`,
there exist deterministic constants `C_corr > 0`, `c_star > 0`, `c_Z > 0`, and `c_W > 0` such that
eventually whenever `δ_n ∈ [δ_-, δ_*]` and `g(p̄₁) + (log 2 / 2)(T_{δ_n} - 1) ≤ -γ`, the selected
capped integer profiles `k_co_vec, k_ch_vec` of Proposition 5.3 satisfy **unconditionally** all
clauses of Lemma 6.1(i)–(ii) and the Scrambled & Middle subprofile sum bounds! -/
theorem eventually_selectedProfiles_lemma61_and_commonClass_sums_regimeC
    {M : ℕ} (hM : 8 ≤ M)
    {p1Bar : ℝ} (hp1 : p1Bar ∈ Set.Ioc (0 : ℝ) (1 / 40))
    {deltaMinus : ℝ} (hd : deltaMinus ∈ Set.Ioc (0 : ℝ) deltaStar)
    {gamma : ℝ} (hgam : 0 < gamma)
    (C_ov : ℝ) :
    ∃ C_corr c_star c_Z c_W : ℝ,
      0 < C_corr ∧ 0 < c_star ∧ 0 < c_Z ∧ 0 < c_W ∧
      ∀ᶠ n : ℕ in atTop,
        phaseDelta n ∈ Set.Icc deltaMinus deltaStar →
        phiInfAux p1Bar + Real.log 2 / 2 * (phaseTarget (phaseDelta n) - 1) ≤ -gamma →
          let u : Fin M → ℕ := fun j ↦ phaseNat n - (1 + j.1)
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
            1 ≤ k_co ∧ (k_co : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ∧
            1 ≤ k_ch ∧ (k_ch : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ∧
            ∃ (k_co_vec k_ch_vec : Fin M → ℕ) (kp_co kp_ch : ColoringProfile (phaseNat n)),
              selectedBlockCount k_co_vec = k_co ∧
              selectedVertexMass u k_co_vec = n ∧
              selectedBlockCount k_ch_vec = k_ch ∧
              selectedVertexMass u k_ch_vec = n ∧
              (∀ j : Fin M, 0 < k_co_vec j ∧ c_star ≤ (k_co_vec j : ℝ) / (k_co : ℝ)) ∧
              (∀ j : Fin M, 0 < k_ch_vec j ∧ c_star ≤ (k_ch_vec j : ℝ) / (k_ch : ℝ)) ∧
              (∀ idx : Fin (phaseNat n),
                kp_co idx = ∑ j : Fin M, if u j = idx.1 + 1 then k_co_vec j else 0) ∧
              (∀ idx : Fin (phaseNat n),
                kp_ch idx = ∑ j : Fin M, if u j = idx.1 + 1 then k_ch_vec j else 0) ∧
              ColoringProfile.partCount kp_co = k_co ∧
              ColoringProfile.vertexMass kp_co = n ∧
              (signedProfileExpectation n kp_co).toReal = completeSignedFirstMoment u k_co_vec ∧
              (∀ P : ProfilePartition n kp_co,
                P.1.parts.card = k_co ∧
                ∀ D ∈ P.1.parts, phaseNat n - M ≤ D.card ∧ D.card ≤ phaseNat n - 1) ∧
              (∀ G : LabeledGraph n,
                (∃ P : ProfilePartition n kp_co, G ∈ partitionCocoloringEvent P.1) →
                  cochromaticNumber G ≤ k_co) ∧
              ColoringProfile.partCount kp_ch = k_ch ∧
              ColoringProfile.vertexMass kp_ch = n ∧
              (profileColoringExpectation n kp_ch).toReal = completeUnmarkedFirstMoment u k_ch_vec ∧
              (∀ P : ProfilePartition n kp_ch,
                P.1.parts.card = k_ch ∧
                ∀ D ∈ P.1.parts, phaseNat n - M ≤ D.card ∧ D.card ≤ phaseNat n - 1) ∧
              (∀ G : LabeledGraph n,
                (∃ P : ProfilePartition n kp_ch, G ∈ partitionColoringEvent P.1) →
                  chromaticNumberNat G ≤ k_ch) ∧
              c_Z * (Real.log (n : ℝ)) ^ 2 ≤ Real.log (completeSignedFirstMoment u k_co_vec) ∧
              c_Z * (Real.log (n : ℝ)) ^ 3 ≤ Real.log (completeUnmarkedFirstMoment u k_ch_vec) ∧
              (∀ nu : Fin M → ℕ,
                IsPartialSubprofile k_co_vec nu →
                (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤ (selectedVertexMass u nu : ℝ) →
                ((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ) < ((n - selectedVertexMass u nu : ℕ) : ℝ) →
                partialDiagonalWeight n u k_co_vec nu ≤
                    Real.exp (-c_W * (selectedVertexMass u nu : ℝ)) ∧
                  Real.exp (-c_W * (selectedVertexMass u nu : ℝ)) ≤
                    Real.exp (-c_W * (n : ℝ) / (Real.log (n : ℝ)) ^ 3)) ∧
              (∀ nu : Fin M → ℕ,
                IsPartialSubprofile k_ch_vec nu →
                (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤ (selectedVertexMass u nu : ℝ) →
                ((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ) < ((n - selectedVertexMass u nu : ℕ) : ℝ) →
                unmarkedDiagonalWeight n u k_ch_vec nu ≤
                    Real.exp (-c_W * (selectedVertexMass u nu : ℝ)) ∧
                  Real.exp (-c_W * (selectedVertexMass u nu : ℝ)) ≤
                    Real.exp (-c_W * (n : ℝ) / (Real.log (n : ℝ)) ^ 3)) ∧
              (∀ nu : Fin M → ℕ,
                IsPartialSubprofile k_co_vec nu →
                ((n - selectedVertexMass u nu : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ) →
                partialDiagonalWeight n u k_co_vec nu ≤
                    (2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ j, (k_co_vec j - nu j)) *
                      Real.exp (-c_Z * (Real.log (n : ℝ)) ^ 2) ∧
                  (2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ j, (k_co_vec j - nu j)) *
                      Real.exp (-c_Z * (Real.log (n : ℝ)) ^ 2) ≤
                    Real.exp (-(((n - selectedVertexMass u nu : ℕ) : ℝ) / 2))) ∧
              (∀ nu : Fin M → ℕ,
                IsPartialSubprofile k_ch_vec nu →
                ((n - selectedVertexMass u nu : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ) →
                unmarkedDiagonalWeight n u k_ch_vec nu ≤
                    ((n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ j, (k_ch_vec j - nu j)) *
                      Real.exp (-c_Z * (Real.log (n : ℝ)) ^ 3) ∧
                  ((n : ℝ) ^ (-(3 / 2 : ℝ))) ^ (∑ j, (k_ch_vec j - nu j)) *
                      Real.exp (-c_Z * (Real.log (n : ℝ)) ^ 3) ≤
                    Real.exp (-(((n - selectedVertexMass u nu : ℕ) : ℝ) / 2))) ∧
              (∀ S_scr : Finset (Fin M → ℕ),
                (∀ nu ∈ S_scr, IsPartialSubprofile k_co_vec nu ∧
                  (selectedVertexMass u nu : ℝ) < (n : ℝ) / (Real.log (n : ℝ)) ^ 3) →
                (∑ nu ∈ S_scr, partialDiagonalWeight n u k_co_vec nu) ≤
                  Real.exp ((n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ))) ∧
              (∀ S_scr : Finset (Fin M → ℕ),
                (∀ nu ∈ S_scr, IsPartialSubprofile k_ch_vec nu ∧
                  (selectedVertexMass u nu : ℝ) < (n : ℝ) / (Real.log (n : ℝ)) ^ 3) →
                (∑ nu ∈ S_scr, unmarkedDiagonalWeight n u k_ch_vec nu) ≤
                  Real.exp ((n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ))) ∧
              (∀ S_mid : Finset (Fin M → ℕ),
                (∀ nu ∈ S_mid, IsPartialSubprofile k_co_vec nu ∧
                  (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤ (selectedVertexMass u nu : ℝ) ∧
                  (n : ℝ) ^ (1 - c₀) ≤ ((n - selectedVertexMass u nu : ℕ) : ℝ)) →
                Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
                  (∑ nu ∈ S_mid, partialDiagonalWeight n u k_co_vec nu) ≤ 1) ∧
              (∀ S_mid : Finset (Fin M → ℕ),
                (∀ nu ∈ S_mid, IsPartialSubprofile k_ch_vec nu ∧
                  (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤ (selectedVertexMass u nu : ℝ) ∧
                  (n : ℝ) ^ (1 - c₀) ≤ ((n - selectedVertexMass u nu : ℕ) : ℝ)) →
                Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
                  (∑ nu ∈ S_mid, unmarkedDiagonalWeight n u k_ch_vec nu) ≤ 1)) := by
  obtain ⟨C_corr, c_star, c_Z, C_p, hCc_pos, hcs_pos, hcZ_pos, _, hProp53⟩ :=
    eventually_selectedProfiles_prop53_regimeC hM hp1
  obtain ⟨c_W, hcW_pos, hLem61_i⟩ :=
    eventually_commonClass_subprofile_le_regimeC hM hp1 hd hgam C_p
  refine ⟨C_corr, c_star, c_Z, c_W, hCc_pos, hcs_pos, hcZ_pos, hcW_pos, ?_⟩
  have ha_ge : ∀ᶠ n : ℕ in atTop, M + 4 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (((M + 4 : ℕ) : ℝ)),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hL hPh
    exact_mod_cast le_trans hL hPh.1
  filter_upwards [eventually_ge_atTop 4,
    tendsto_logOrder_atTop.eventually_ge_atTop 1,
    ha_ge, hProp53, hLem61_i,
    eventually_partialDiagonalWeight_subprofile_le_exp_neg_half M,
    eventually_unmarkedDiagonalWeight_subprofile_le_exp_neg_half M,
    eventually_scrambledRange_commonClass_sum_le_v13 M hd.1,
    eventually_middleRange_commonClass_sum_small_regimeC hM hp1 hd hgam C_p C_ov zero_lt_one] with
    n hn4 hL1 ha_n h53 h61i h61ii_mk h61ii_ch hScr hMid hdn hcap_gap
    u c₀ h_sc F_cap obj_cap
  have hd_icc : phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar := ⟨hd.1.le.trans hdn.1, hdn.2⟩
  obtain ⟨hexu_co, hexu_ch, ⟨lamT, hlamT_eq, _⟩, hsel⟩ := h53 hd_icc
  refine ⟨hexu_co, hexu_ch, ?_⟩
  intro r_co r_ch hr_co hobj_co hr_ch hobj_ch k_co k_ch
  obtain ⟨hk_co1, hk_co_ub, hk_ch1, hk_ch_ub, k_co_vec, k_ch_vec, kp_co, kp_ch,
    hco_blk, hco_mass, hch_blk, hch_mass, hco_pos, hch_pos, hco_kp_def, hch_kp_def,
    hco_part, hco_vm, hco_sgn, hco_P, hco_G,
    hch_part, hch_vm, hch_unm, hch_P, hch_G,
    hrat_both, hmom_co, hmom_ch⟩ := hsel hr_co hobj_co hr_ch hobj_ch
  have hL_ge1 : (1 : ℝ) ≤ Real.log (n : ℝ) := hL1
  have hco_exp : Real.exp (c_Z * (Real.log (n : ℝ)) ^ 2) ≤ completeSignedFirstMoment u k_co_vec := by
    rw [← Real.exp_log (completeSignedFirstMoment_pos u k_co_vec)]
    exact Real.exp_le_exp.mpr hmom_co
  have hch_exp : Real.exp (c_Z * (Real.log (n : ℝ)) ^ 3) ≤ completeUnmarkedFirstMoment u k_ch_vec := by
    have hpos_unm : 0 < completeUnmarkedFirstMoment u k_ch_vec := by
      unfold completeUnmarkedFirstMoment
      exact mul_pos (by positivity) (completeSignedFirstMoment_pos u k_ch_vec)
    rw [← Real.exp_log hpos_unm]
    exact Real.exp_le_exp.mpr hmom_ch
  have hco_ge1 : 1 ≤ completeSignedFirstMoment u k_co_vec :=
    (Real.one_le_exp (by positivity)).trans hco_exp
  have hch_ge1 : 1 ≤ completeUnmarkedFirstMoment u k_ch_vec :=
    (Real.one_le_exp (by positivity)).trans hch_exp
  have hu_bds : ∀ j : Fin M, 1 ≤ u j ∧ phaseNat n - (M + 1) ≤ u j ∧ u j ≤ phaseNat n := by
    intro j; dsimp [u]; exact ⟨by omega, by omega, Nat.sub_le _ _⟩
  have hco_le_n : (selectedBlockCount k_co_vec : ℝ) ≤ (n : ℝ) := by
    rw [hco_blk]; exact hk_co_ub.trans (div_le_self (Nat.cast_nonneg n) hL_ge1)
  have hch_le_n : (selectedBlockCount k_ch_vec : ℝ) ≤ (n : ℝ) := by
    rw [hch_blk]; exact hk_ch_ub.trans (div_le_self (Nat.cast_nonneg n) hL_ge1)
  have hu_eq0 : (fun j : Fin M ↦ phaseNat n - (0 + 1 + j.1)) = u := by
    funext j; rfl
  have hscr0 := hScr (m := 0) (by omega) (by simpa using hdn.1)
  rw [hu_eq0] at hscr0
  have hrat_co : ∀ j : Fin M,
      |(k_co_vec j : ℝ) / (selectedBlockCount k_co_vec : ℝ) -
          cappedGibbsProbS0M M p1Bar lamT ((j.1 : ℤ) + 1)| ≤
        C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := fun j ↦ by
    rw [hco_blk]; exact (hrat_both lamT hlamT_eq j).1
  have hrat_ch : ∀ j : Fin M,
      |(k_ch_vec j : ℝ) / (selectedBlockCount k_ch_vec : ℝ) -
          cappedGibbsProbS0M M p1Bar lamT ((j.1 : ℤ) + 1)| ≤
        C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := fun j ↦ by
    rw [hch_blk]; exact (hrat_both lamT hlamT_eq j).2
  exact ⟨hk_co1, hk_co_ub, hk_ch1, hk_ch_ub, k_co_vec, k_ch_vec, kp_co, kp_ch,
    hco_blk, hco_mass, hch_blk, hch_mass, hco_pos, hch_pos, hco_kp_def, hch_kp_def,
    hco_part, hco_vm, hco_sgn, hco_P, hco_G,
    hch_part, hch_vm, hch_unm, hch_P, hch_G,
    hmom_co, hmom_ch,
    fun nu hsub hmlo hrem ↦
      (h61i hdn hcap_gap lamT hlamT_eq k_co_vec nu hco_mass hrat_co hsub hmlo hrem).1 hco_ge1,
    fun nu hsub hmlo hrem ↦
      (h61i hdn hcap_gap lamT hlamT_eq k_ch_vec nu hch_mass hrat_ch hsub hmlo hrem).2 hch_ge1,
    fun nu hsub hrem ↦ h61ii_mk u k_co_vec nu c_Z hcZ_pos.le hu_bds hco_mass hsub hrem hco_exp,
    fun nu hsub hrem ↦ h61ii_ch u k_ch_vec nu c_Z hcZ_pos.le hu_bds hch_mass hsub hrem hch_exp,
    fun S_scr hS ↦ (hscr0 k_co_vec S_scr hco_le_n hS).1,
    fun S_scr hS ↦ (hscr0 k_ch_vec S_scr hch_le_n hS).2,
    fun S_mid hS ↦
      ((hMid hdn hcap_gap lamT hlamT_eq k_co_vec S_mid hco_mass hrat_co hS).1 hco_ge1).le,
    fun S_mid hS ↦
      ((hMid hdn hcap_gap lamT hlamT_eq k_ch_vec S_mid hch_mass hrat_ch hS).2 hch_ge1).le⟩

end

end Erdos625HP
