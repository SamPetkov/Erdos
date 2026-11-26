import Erdos625HP.FiveSizeRateBound
import Erdos625HP.ShiftedSevenSizeCertificate

/-!
# Capped realizability threshold `θ(δ)`, general-`M` common-class rate bounds, and full-sequence `1/4` assembly

This module kernel-checks the remaining analytic and assembly pillars of the
upgraded full-sequence `1/4` Main Theorem:

1. **Realizability cap `θ(δ)` on `[0, x₀]` (`Lemma 5.2(i)` & `eq:theta-def`):**
   * `existsUnique_capThresholdTheta_pos`, `capThresholdTheta`: unique continuous
     strictly increasing function `θ : [0, x₀] → [0, p_{1,∞}(x₀)]` with `θ(0) = 0`,
     `θ(x₀) = p_{1,∞}(x₀) < 1 / 40`, `θ(δ) < p_{1,∞}(δ)` on `[0, x₀)`, and
     `g(θ(δ)) + (log 2 / 2)(T_δ - 1) = 0` on `(0, x₀]`.
   * `phiInfAux_capThresholdTheta_add_target`: exact linear shift identity
     `g(θ(δ₁)) + (log 2 / 2)(T_{δ₂} - 1) = (log 2 / 2)(δ₁ - δ₂)` for all
     `δ₁ ∈ (0, x₀]` and `δ₂ ∈ ℝ`.

2. **Unconditional general-`M` unconstrained common-class rate bound (`Lemma 5.2(ii)`, unconstrained case):**
   * `existsUnique_s0mTilt`: unique tilt `λ_{S_{0,M}}(T)` on `S_{0,M} = {1, …, M}`
     for all `M ≥ 7` and `T ∈ [M₇(121/25), M₇(209/20)]` (covering all `T̃_{δ̃}`
     for `δ̃ ∈ [0, 207/200]`).
   * `gibbsProbS0M_one_lt_p1Inf`: `p^*_1 < p_{1,∞}(δ̃)` for all `M ≥ 7`.
   * `commonClass_rate_bound_S0M`: for all `M ≥ 7`, `δ_- ∈ (x₀, 207/200]`,
     `δ̃ ∈ [δ_-, 207/200]`, and `0 ≤ z ≤ p^*_{S_{0,M}, T̃_{δ̃}}` on `{1, …, M}`
     with `R = ∑_{i=1}^M z_i ∈ [0, 1]`,
     `R log R + (log 2 / 2)(∑ i z_i - T̃_{δ̃} R) ≤ -min(1/240, -φ_∞(δ_-)) R (1 - R)`.

3. **Unconditional general-`M` capped common-class rate bound (`Lemma 5.2(ii)`, capped case):**
   * `convexOn_mul_log_add_quad`: convexity of `x ↦ x log x + b x (1 - x)` on
     `[0, 1]` whenever `b ≤ 1 / 2`.
   * `capped_rate_bound_of_tail_rate` and `commonClass_capped_rate_bound_S0M`:
     endpoint convexity proof of `-2 c_cap(γ) R (1 - R)` across **all** `R ∈ [0, 1]`
     for all `M ≥ 8`, `δ ∈ [0, δ_*]`, and `p̄₁ ∈ (0, 1/40]` with
     `g(p̄₁) + (log 2 / 2)(T_δ - 1) ≤ -γ < 0`.

4. **First-coordinate-capped duals `𝓕_S^{=ϑ}(T)` and full-sequence `1/4` assembly (`Lemma 3.2(iv)` & `Section 9`):**
   * `tendstoUniformlyOn_cappedDualValue_S0M_Sge1`: uniform convergence
     `𝓕_{S_{0,M}}^{=ϑ}(T) → 𝓕_{S_{≥ 1}}^{=ϑ}(T)` on `[0, 1/20] × K_cap`.
   * `fullSequence_sharpGapConstant_of_finite_phase_cover`: assembles any finite
     cover of `[0, 1)` into **full-sequence** summable failure probabilities,
     convergence in probability along all `n : ℕ`, and (via
     `ae_tendsto_normalizedGap_of_summable_failures`) almost-sure convergence to
     `(log 2)³ / 4` (and `1 / 4` in `log₂ n`) under **every** coupling.
-/

namespace Erdos625HP

open Erdos625 FiveSizeEntropyGap FiveSizePhaseGainSharp FiveSizePhaseGainCertificate
open Filter MeasureTheory Set
open scoped BigOperators Topology

set_option autoImplicit false

noncomputable section

/-! ## 1. Capped realizability threshold `θ(δ)` on `[0, x₀]` (`Lemma 5.2(i)`) -/

private theorem phiInfAux_lt_neg_one_add {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    phiInfAux p < -1 + p := by
  have h1p_pos : 0 < 1 - p := by linarith [hp.2]
  have hlog : Real.log (1 - p) < -p := by
    have := Real.log_lt_sub_one_of_pos h1p_pos (by linarith [hp.1])
    linarith
  have hfac : 0 < (1 - p) / p := div_pos h1p_pos hp.1
  unfold phiInfAux
  rw [mul_div_right_comm]
  calc (1 - p) / p * Real.log (1 - p)
      < (1 - p) / p * (-p) := mul_lt_mul_of_pos_left hlog hfac
    _ = -1 + p := by field_simp [hp.1.ne']; ring

private theorem neg_one_add_half_lt_phiInfAux {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    -1 + p / 2 < phiInfAux p := by
  let f : ℝ → ℝ := fun x ↦ x ^ 2 / (2 * (1 - x)) + x + Real.log (1 - x)
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt f (x ^ 2 / (2 * (1 - x) ^ 2)) x := by
    intro x hx
    have h1x : 1 - x ≠ 0 := by linarith [hx.2]
    have h2x : 2 * (1 - x) ≠ 0 := by linarith [hx.2]
    have hd_num : HasDerivAt (fun t : ℝ ↦ t ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x)
    have hd_1mx : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) x :=
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).congr_deriv (by ring)
    have hd_den : HasDerivAt (fun t : ℝ ↦ 2 * (1 - t)) (-2) x :=
      (hd_1mx.const_mul 2).congr_deriv (by ring)
    exact (((hd_num.div hd_den h2x).add (hasDerivAt_id x)).add
      (hd_1mx.log h1x)).congr_deriv (by field_simp [h1x]; ring)
  have hcont : ContinuousOn f (Set.Icc 0 p) := by
    intro x hx
    have h1x : 1 - x ≠ 0 := by linarith [hx.2, hp.2]
    have h2x : 2 * (1 - x) ≠ 0 := by linarith [hx.2, hp.2]
    exact (((continuousAt_id.pow 2).div
      (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)) h2x).add
      continuousAt_id |>.add
      ((continuousAt_const.sub continuousAt_id).log h1x)).continuousWithinAt
  have hmono : StrictMonoOn f (Set.Icc 0 p) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 p) hcont
    intro x hx
    rw [interior_Icc] at hx
    have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx.1, lt_trans hx.2 hp.2⟩
    rw [(hderiv x hx01).deriv]
    exact div_pos (sq_pos_of_pos hx01.1) (mul_pos two_pos (sq_pos_of_pos (sub_pos.mpr hx01.2)))
  have hf_pos : 0 < f p := by
    have hf0 : f 0 = 0 := by simp [f]
    rw [← hf0]
    exact hmono ⟨le_rfl, hp.1.le⟩ ⟨hp.1.le, le_rfl⟩ hp.1
  have hlog_gt : -p - p ^ 2 / (2 * (1 - p)) < Real.log (1 - p) := by
    dsimp [f] at hf_pos; linarith
  have h1p_pos : 0 < 1 - p := by linarith [hp.2]
  have hfac : 0 < (1 - p) / p := div_pos h1p_pos hp.1
  unfold phiInfAux
  rw [mul_div_right_comm]
  calc -1 + p / 2
      = (1 - p) / p * (-p - p ^ 2 / (2 * (1 - p))) := by
          field_simp [hp.1.ne', h1p_pos.ne']; ring
    _ < (1 - p) / p * Real.log (1 - p) := mul_lt_mul_of_pos_left hlog_gt hfac

theorem continuousOn_phiInfAux : ContinuousOn phiInfAux (Set.Ioo (0 : ℝ) 1) := by
  intro p hp
  unfold phiInfAux
  exact (((continuousAt_const.sub continuousAt_id).mul
    ((continuousAt_const.sub continuousAt_id).log (sub_pos.mpr hp.2).ne')).div
    continuousAt_id hp.1.ne').continuousWithinAt

theorem half_log_two_mul_phaseTarget_sub_one (d : ℝ) :
    Real.log 2 / 2 * (phaseTarget d - 1) = 1 - Real.log 2 / 2 * d := by
  have hq : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  unfold phaseTarget
  field_simp [hq]
  ring

/-- For every `d ∈ (0, x₀]`, there is a unique `θ ∈ (0, 1)` solving
`g(θ) + (log 2 / 2)(T_d - 1) = 0`, and it satisfies `(log 2 / 2) d < θ < (log 2) d`. -/
theorem existsUnique_capThresholdTheta_pos {d : ℝ}
    (hd : d ∈ Set.Ioc (0 : ℝ) criticalPhaseX0) :
    ∃! theta : ℝ,
      theta ∈ Set.Ioo (0 : ℝ) 1 ∧
        phiInfAux theta + Real.log 2 / 2 * (phaseTarget d - 1) = 0 := by
  obtain ⟨hd_pos, hd_hi⟩ := hd
  have hx0_hi : criticalPhaseX0 < 291 / 10000 := criticalPhaseX0_bounds_and_sign.1.2
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq_hi : Real.log 2 < 7 / 10 := lt_trans Real.log_two_lt_d9 (by norm_num)
  set plo : ℝ := Real.log 2 / 2 * d
  set phi : ℝ := Real.log 2 * d
  have hplo_pos : 0 < plo := by dsimp [plo]; positivity
  have hlo_lt_hi : plo < phi := by dsimp [plo, phi]; nlinarith
  have hphi_lt : phi < 1 / 40 := by
    dsimp [phi]
    have hd_lt : d < 291 / 10000 := lt_of_le_of_lt hd_hi hx0_hi
    nlinarith
  have hplo_mem : plo ∈ Set.Ioo (0 : ℝ) 1 := ⟨hplo_pos, by linarith⟩
  have hphi_mem : phi ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_trans hplo_pos hlo_lt_hi, by linarith⟩
  have hsub : Set.Icc plo phi ⊆ Set.Ioo (0 : ℝ) 1 :=
    fun x hx ↦ ⟨lt_of_lt_of_le hplo_pos hx.1, lt_of_le_of_lt hx.2 hphi_mem.2⟩
  have hlo_val : phiInfAux plo < -1 + Real.log 2 / 2 * d :=
    phiInfAux_lt_neg_one_add hplo_mem
  have hhi_val : -1 + Real.log 2 / 2 * d < phiInfAux phi := by
    have := neg_one_add_half_lt_phiInfAux hphi_mem
    dsimp [phi] at this
    linarith
  obtain ⟨theta, htheta_icc, htheta_eq⟩ :=
    intermediate_value_Icc hlo_lt_hi.le (continuousOn_phiInfAux.mono hsub)
      ⟨hlo_val.le, hhi_val.le⟩
  refine ⟨theta, ⟨hsub htheta_icc, ?_⟩, ?_⟩
  · rw [half_log_two_mul_phaseTarget_sub_one, htheta_eq]; ring
  · rintro y ⟨hy_mem, hy_zero⟩
    have hy_eq : phiInfAux y = -1 + Real.log 2 / 2 * d := by
      rw [half_log_two_mul_phaseTarget_sub_one] at hy_zero; linarith
    rcases lt_trichotomy y theta with hlt | rfl | hgt
    · have := strictMonoOn_phiInfAux hy_mem (hsub htheta_icc) hlt
      linarith
    · rfl
    · have := strictMonoOn_phiInfAux (hsub htheta_icc) hy_mem hgt
      linarith

/-- The realizability cap `θ(δ)` of equation `(6.1)` and Lemma 5.2(i):
`θ(0) = 0`, and on `(0, x₀]` the unique root of `g(θ) + (log 2 / 2)(T_δ - 1) = 0`. -/
def capThresholdTheta (d : ℝ) : ℝ := by
  classical
  exact if hd : d ∈ Set.Ioc (0 : ℝ) criticalPhaseX0 then
    (existsUnique_capThresholdTheta_pos hd).choose
  else 0

theorem capThresholdTheta_zero : capThresholdTheta 0 = 0 := by
  unfold capThresholdTheta
  simp

theorem capThresholdTheta_pos_spec {d : ℝ} (hd : d ∈ Set.Ioc (0 : ℝ) criticalPhaseX0) :
    capThresholdTheta d ∈ Set.Ioo (Real.log 2 / 2 * d) (Real.log 2 * d) ∧
      capThresholdTheta d ∈ Set.Ioo (0 : ℝ) 1 ∧
      phiInfAux (capThresholdTheta d) + Real.log 2 / 2 * (phaseTarget d - 1) = 0 := by
  have hdef : capThresholdTheta d = (existsUnique_capThresholdTheta_pos hd).choose := by
    unfold capThresholdTheta
    simp [hd]
  obtain ⟨⟨hmem, hzero⟩, _⟩ := (existsUnique_capThresholdTheta_pos hd).choose_spec
  rw [← hdef] at hmem hzero
  have hval : phiInfAux (capThresholdTheta d) = -1 + Real.log 2 / 2 * d := by
    rw [half_log_two_mul_phaseTarget_sub_one] at hzero; linarith
  have hgt : Real.log 2 / 2 * d < capThresholdTheta d := by
    have := phiInfAux_lt_neg_one_add hmem
    linarith
  have hlt : capThresholdTheta d < Real.log 2 * d := by
    have := neg_one_add_half_lt_phiInfAux hmem
    linarith
  exact ⟨⟨hgt, hlt⟩, hmem, hzero⟩

/-- `θ(δ) < 1 / 40` for all `δ ∈ [0, x₀]` (`Lemma 5.2(i)`). -/
theorem capThresholdTheta_lt_one_div_40 {d : ℝ}
    (hd : d ∈ Set.Icc (0 : ℝ) criticalPhaseX0) :
    0 ≤ capThresholdTheta d ∧ capThresholdTheta d < 1 / 40 := by
  rcases eq_or_lt_of_le hd.1 with rfl | hpos
  · rw [capThresholdTheta_zero]; norm_num
  · obtain ⟨⟨hlo, hhi⟩, -, -⟩ := capThresholdTheta_pos_spec ⟨hpos, hd.2⟩
    have hx0_hi : criticalPhaseX0 < 291 / 10000 := criticalPhaseX0_bounds_and_sign.1.2
    have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hq_hi : Real.log 2 < 7 / 10 := lt_trans Real.log_two_lt_d9 (by norm_num)
    refine ⟨le_trans (by positivity) hlo.le, ?_⟩
    have hd_lt : d < 291 / 10000 := lt_of_le_of_lt hd.2 hx0_hi
    nlinarith

/-- At the critical phase `x₀`, `θ(x₀) = p_{1,∞}(x₀)` (`Lemma 5.2(i)`). -/
theorem capThresholdTheta_x0_eq_p1Inf :
    capThresholdTheta criticalPhaseX0 = p1Inf criticalPhaseX0 := by
  obtain ⟨⟨hx0_lo, _⟩, hx0_phi, -, -⟩ := criticalPhaseX0_bounds_and_sign
  have hx0_ioc : criticalPhaseX0 ∈ Set.Ioc (0 : ℝ) criticalPhaseX0 :=
    ⟨lt_trans (by norm_num) hx0_lo, le_rfl⟩
  obtain ⟨_, hmem_th, hzero_th⟩ := capThresholdTheta_pos_spec hx0_ioc
  have hp_mem : p1Inf criticalPhaseX0 ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [p1Inf_eq_p1AtTilt]; exact p1AtTilt_mem_Ioo _
  exact (existsUnique_capThresholdTheta_pos hx0_ioc).unique
    ⟨hmem_th, hzero_th⟩ ⟨hp_mem, hx0_phi⟩

/-- On `[0, x₀)`, `θ(δ) < p_{1,∞}(δ)` (`Lemma 5.2(i)`). -/
theorem capThresholdTheta_lt_p1Inf_of_lt_x0 {d : ℝ}
    (hd : d ∈ Set.Ico (0 : ℝ) criticalPhaseX0) :
    capThresholdTheta d < p1Inf d := by
  have hp_mem : p1Inf d ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [p1Inf_eq_p1AtTilt]; exact p1AtTilt_mem_Ioo _
  rcases eq_or_lt_of_le hd.1 with rfl | hpos
  · rw [capThresholdTheta_zero]; exact hp_mem.1
  · obtain ⟨-, hmem_th, hzero_th⟩ := capThresholdTheta_pos_spec ⟨hpos, hd.2.le⟩
    have hphi_pos : 0 < phiInf d := criticalPhaseX0_bounds_and_sign.2.2.1 d hd
    unfold phiInf at hphi_pos
    have hg_lt : phiInfAux (capThresholdTheta d) < phiInfAux (p1Inf d) := by linarith
    by_contra hge
    rcases eq_or_lt_of_le (not_lt.mp hge) with heq | hgt
    · rw [heq] at hg_lt; exact lt_irrefl _ hg_lt
    · have := strictMonoOn_phiInfAux hp_mem hmem_th hgt
      linarith

/-- **Exact linear shift identity (`Lemma 5.2(i)` & `eq:cap-gap`):**
`g(θ(δ₁)) + (log 2 / 2)(T_{δ₂} - 1) = (log 2 / 2)(δ₁ - δ₂)` for all `δ₁ ∈ (0, x₀]`
and `δ₂ ∈ ℝ`. -/
theorem phiInfAux_capThresholdTheta_add_target {d1 : ℝ}
    (hd1 : d1 ∈ Set.Ioc (0 : ℝ) criticalPhaseX0) (d2 : ℝ) :
    phiInfAux (capThresholdTheta d1) + Real.log 2 / 2 * (phaseTarget d2 - 1) =
      Real.log 2 / 2 * (d1 - d2) := by
  obtain ⟨-, -, hzero⟩ := capThresholdTheta_pos_spec hd1
  rw [half_log_two_mul_phaseTarget_sub_one] at hzero ⊢
  linarith

/-- `θ` is strictly increasing on `[0, x₀]` (`Lemma 5.2(i)`). -/
theorem strictMonoOn_capThresholdTheta :
    StrictMonoOn capThresholdTheta (Set.Icc (0 : ℝ) criticalPhaseX0) := by
  intro d1 hd1 d2 hd2 hlt
  have hd2_pos : 0 < d2 := lt_of_le_of_lt hd1.1 hlt
  obtain ⟨⟨h2_lo, _⟩, hmem2, hzero2⟩ := capThresholdTheta_pos_spec ⟨hd2_pos, hd2.2⟩
  rcases eq_or_lt_of_le hd1.1 with rfl | hd1_pos
  · rw [capThresholdTheta_zero]
    exact lt_trans (by positivity : 0 < Real.log 2 / 2 * d2) h2_lo
  · obtain ⟨-, hmem1, hzero1⟩ := capThresholdTheta_pos_spec ⟨hd1_pos, hd1.2⟩
    rw [half_log_two_mul_phaseTarget_sub_one] at hzero1 hzero2
    have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hg_lt : phiInfAux (capThresholdTheta d1) < phiInfAux (capThresholdTheta d2) := by
      nlinarith
    by_contra hge
    rcases eq_or_lt_of_le (not_lt.mp hge) with heq | hgt
    · rw [heq] at hg_lt; exact lt_irrefl _ hg_lt
    · have := strictMonoOn_phiInfAux hmem2 hmem1 hgt
      linarith

/-- `θ` is continuous on `[0, x₀]` (`Lemma 5.2(i)`). -/
theorem continuousOn_capThresholdTheta :
    ContinuousOn capThresholdTheta (Set.Icc (0 : ℝ) criticalPhaseX0) := by
  rw [Metric.continuousOn_iff]
  intro d0 hd0 eps heps
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  rcases eq_or_lt_of_le hd0.1 with rfl | hd0_pos
  · refine ⟨eps / Real.log 2, div_pos heps hq_pos, fun d hd hdist ↦ ?_⟩
    rw [Real.dist_eq, sub_zero] at hdist
    rw [capThresholdTheta_zero, Real.dist_eq, sub_zero]
    rcases eq_or_lt_of_le hd.1 with rfl | hd_pos
    · rw [capThresholdTheta_zero, abs_zero]; exact heps
    · obtain ⟨⟨hlo, hhi⟩, -, -⟩ := capThresholdTheta_pos_spec ⟨hd_pos, hd.2⟩
      rw [abs_of_pos hd_pos] at hdist
      rw [abs_of_pos (lt_trans (by positivity) hlo)]
      have hmul := (lt_div_iff₀ hq_pos).mp hdist
      linarith
  · obtain ⟨-, hmem0, hzero0⟩ := capThresholdTheta_pos_spec ⟨hd0_pos, hd0.2⟩
    rw [half_log_two_mul_phaseTarget_sub_one] at hzero0
    set t0 := capThresholdTheta d0
    set tlo := max (t0 / 2) (t0 - eps / 2)
    set thi := min ((1 + t0) / 2) (t0 + eps / 2)
    have htlo_mem : tlo ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_lt_of_le (half_pos hmem0.1) (le_max_left _ _),
        lt_of_le_of_lt (max_le (by linarith [hmem0.1]) (by linarith)) hmem0.2⟩
    have hthi_mem : thi ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_lt_of_le hmem0.1 (le_min (by linarith [hmem0.2]) (by linarith)),
        lt_of_le_of_lt (min_le_left _ _) (by linarith [hmem0.2])⟩
    have htlo_lt : tlo < t0 := max_lt (by linarith [hmem0.1]) (by linarith)
    have hthi_gt : t0 < thi := lt_min (by linarith [hmem0.2]) (by linarith)
    have hg_lo : phiInfAux tlo < phiInfAux t0 := strictMonoOn_phiInfAux htlo_mem hmem0 htlo_lt
    have hg_hi : phiInfAux t0 < phiInfAux thi := strictMonoOn_phiInfAux hmem0 hthi_mem hthi_gt
    set gap := min (phiInfAux t0 - phiInfAux tlo) (phiInfAux thi - phiInfAux t0)
    have hgap_pos : 0 < gap := lt_min (by linarith) (by linarith)
    refine ⟨min (d0 / 2) (gap / (Real.log 2 / 2)),
      lt_min (half_pos hd0_pos) (div_pos hgap_pos (half_pos hq_pos)),
      fun d hd hdist ↦ ?_⟩
    rw [Real.dist_eq] at hdist ⊢
    have hd_pos : 0 < d := by
      have := lt_of_lt_of_le hdist (min_le_left _ _)
      linarith [(abs_lt.mp this).1]
    obtain ⟨-, hmemd, hzerod⟩ := capThresholdTheta_pos_spec ⟨hd_pos, hd.2⟩
    rw [half_log_two_mul_phaseTarget_sub_one] at hzerod
    have hdiff_d : |d - d0| < gap / (Real.log 2 / 2) :=
      lt_of_lt_of_le hdist (min_le_right _ _)
    have hdiff_g : |phiInfAux (capThresholdTheta d) - phiInfAux t0| < gap := by
      have heq : phiInfAux (capThresholdTheta d) - phiInfAux t0 =
          Real.log 2 / 2 * (d - d0) := by dsimp [t0] at *; linarith
      rw [heq, abs_mul, abs_of_pos (half_pos hq_pos), mul_comm]
      exact (lt_div_iff₀ (half_pos hq_pos)).mp hdiff_d
    have hg_d_gt : phiInfAux tlo < phiInfAux (capThresholdTheta d) := by
      have h1 : gap ≤ phiInfAux t0 - phiInfAux tlo := min_le_left _ _
      linarith [(abs_lt.mp hdiff_g).1]
    have hg_d_lt : phiInfAux (capThresholdTheta d) < phiInfAux thi := by
      have h2 : gap ≤ phiInfAux thi - phiInfAux t0 := min_le_right _ _
      linarith [(abs_lt.mp hdiff_g).2]
    have ht_gt : tlo < capThresholdTheta d := by
      by_contra hle
      rcases eq_or_lt_of_le (not_lt.mp hle) with heq | hlt
      · rw [heq] at hg_d_gt; exact lt_irrefl _ hg_d_gt
      · linarith [strictMonoOn_phiInfAux hmemd htlo_mem hlt]
    have ht_lt : capThresholdTheta d < thi := by
      by_contra hge
      rcases eq_or_lt_of_le (not_lt.mp hge) with heq | hgt
      · rw [← heq] at hg_d_lt; exact lt_irrefl _ hg_d_lt
      · linarith [strictMonoOn_phiInfAux hthi_mem hmemd hgt]
    have hlo_eps : t0 - eps / 2 ≤ tlo := le_max_right _ _
    have hhi_eps : thi ≤ t0 + eps / 2 := min_le_right _ _
    rw [abs_lt]
    dsimp [t0] at *
    exact ⟨by linarith, by linarith⟩

/-! ## 2. General-`M` unconstrained common-class rate bound (`Lemma 5.2(ii)`, unconstrained) -/

/-- `S_{0,M} = {1, …, M}` as a `Finset ℤ`. -/
def F0M (M : ℕ) : Finset ℤ := Finset.Icc 1 (M : ℤ)

theorem coe_F0M (M : ℕ) : (F0M M : Set ℤ) = S0M M := by
  ext i
  simp [F0M, S0M]

theorem partitionFn_S0M_eq_sum (M : ℕ) (lambda : ℝ) :
    partitionFn (S0M M) lambda = ∑ i ∈ F0M M, gaussWeight lambda i := by
  rw [← coe_F0M, partitionFn_coe_finset]

theorem partitionFn_S0M_pos {M : ℕ} (hM : 1 ≤ M) (lambda : ℝ) :
    0 < partitionFn (S0M M) lambda := by
  rw [partitionFn_S0M_eq_sum]
  have h1 : (1 : ℤ) ∈ F0M M := by
    simp only [F0M, Finset.mem_Icc]; exact ⟨le_rfl, by exact_mod_cast hM⟩
  exact Finset.sum_pos' (fun i _ ↦ (gaussWeight_pos lambda i).le)
    ⟨1, h1, gaussWeight_pos lambda 1⟩

/-- Gibbs distribution `p_{S_{0,M}, λ}` at tilt `λ`. -/
def gibbsProbS0M (M : ℕ) (lambda : ℝ) (i : ℤ) : ℝ :=
  if i ∈ F0M M then gaussWeight lambda i / partitionFn (S0M M) lambda else 0

/-- Mean `M_{S_{0,M}}(λ) = ∑_{i=1}^M i · p_{S_{0,M}, λ}(i)`. -/
def meanS0M (M : ℕ) (lambda : ℝ) : ℝ :=
  (∑ i ∈ F0M M, (i : ℝ) * gaussWeight lambda i) / partitionFn (S0M M) lambda

theorem sum_gibbsProbS0M {M : ℕ} (hM : 1 ≤ M) (lambda : ℝ) :
    ∑ i ∈ F0M M, gibbsProbS0M M lambda i = 1 := by
  have hZ := partitionFn_S0M_pos hM lambda
  calc ∑ i ∈ F0M M, gibbsProbS0M M lambda i
      = ∑ i ∈ F0M M, (gaussWeight lambda i / partitionFn (S0M M) lambda) :=
        Finset.sum_congr rfl fun i hi ↦ by simp [gibbsProbS0M, hi]
    _ = (∑ i ∈ F0M M, gaussWeight lambda i) / partitionFn (S0M M) lambda :=
        (Finset.sum_div _ _ _).symm
    _ = 1 := by rw [← partitionFn_S0M_eq_sum, div_self hZ.ne']

theorem sum_mul_gibbsProbS0M (M : ℕ) (lambda : ℝ) :
    ∑ i ∈ F0M M, (i : ℝ) * gibbsProbS0M M lambda i = meanS0M M lambda := by
  unfold meanS0M
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  simp only [gibbsProbS0M, hi, ↓reduceIte, mul_div_assoc]

private theorem hasDerivAt_gaussWeight (i : ℤ) (lambda : ℝ) :
    HasDerivAt (fun l : ℝ ↦ gaussWeight l i) ((i : ℝ) * gaussWeight lambda i) lambda := by
  unfold gaussWeight
  have hlin : HasDerivAt (fun l : ℝ ↦ l * (i : ℝ) - Real.log 2 / 2 * (i : ℝ) ^ 2)
      (i : ℝ) lambda := by
    simpa using ((hasDerivAt_id lambda).mul_const (i : ℝ)).sub_const
      (Real.log 2 / 2 * (i : ℝ) ^ 2)
  exact (hlin.exp).congr_deriv (by ring)

private theorem hasDerivAt_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (f' : ι → ℝ) (x : ℝ) (hf : ∀ i ∈ s, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (fun y ↦ ∑ i ∈ s, f i y) (∑ i ∈ s, f' i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDerivAt_const x (0 : ℝ)
  | @insert a s ha ih =>
    have hsum : (fun y ↦ ∑ i ∈ insert a s, f i y) =
        fun y ↦ f a y + ∑ i ∈ s, f i y := by
      ext y; exact Finset.sum_insert ha
    rw [hsum, Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

theorem strictMono_meanS0M {M : ℕ} (hM : 2 ≤ M) : StrictMono (meanS0M M) := by
  have hM1 : 1 ≤ M := by omega
  have hderiv : ∀ l : ℝ, ∃ v : ℝ, 0 < v ∧ HasDerivAt (meanS0M M) v l := by
    intro l
    have hZ_pos := partitionFn_S0M_pos hM1 l
    have hd_num : HasDerivAt (fun x ↦ ∑ i ∈ F0M M, (i : ℝ) * gaussWeight x i)
        (∑ i ∈ F0M M, (i : ℝ) ^ 2 * gaussWeight l i) l := by
      have h := hasDerivAt_finset_sum (F0M M) (fun i x ↦ (i : ℝ) * gaussWeight x i)
        (fun i ↦ (i : ℝ) * ((i : ℝ) * gaussWeight l i)) l
        fun i _ ↦ (hasDerivAt_gaussWeight i l).const_mul (i : ℝ)
      exact h.congr_deriv (Finset.sum_congr rfl fun i _ ↦ by ring)
    have hd_den : HasDerivAt (partitionFn (S0M M))
        (∑ i ∈ F0M M, (i : ℝ) * gaussWeight l i) l := by
      have h := hasDerivAt_finset_sum (F0M M) (fun i x ↦ gaussWeight x i)
        (fun i ↦ (i : ℝ) * gaussWeight l i) l
        fun i _ ↦ hasDerivAt_gaussWeight i l
      rwa [funext (partitionFn_S0M_eq_sum M)]
    have hd_quot := hd_num.div hd_den hZ_pos.ne'
    refine ⟨_, ?_, hd_quot⟩
    set m := meanS0M M l
    have hN1 : ∑ i ∈ F0M M, (i : ℝ) * gaussWeight l i = m * partitionFn (S0M M) l := by
      dsimp [m]; unfold meanS0M; exact (div_mul_cancel₀ _ hZ_pos.ne').symm
    have hvar_id :
        (∑ i ∈ F0M M, (i : ℝ) ^ 2 * gaussWeight l i) * partitionFn (S0M M) l -
            (∑ i ∈ F0M M, (i : ℝ) * gaussWeight l i) *
              (∑ i ∈ F0M M, (i : ℝ) * gaussWeight l i) =
          partitionFn (S0M M) l *
            ∑ i ∈ F0M M, ((i : ℝ) - m) ^ 2 * gaussWeight l i := by
      have hexp :
          ∑ i ∈ F0M M, ((i : ℝ) - m) ^ 2 * gaussWeight l i =
            (∑ i ∈ F0M M, (i : ℝ) ^ 2 * gaussWeight l i) -
              2 * m * (∑ i ∈ F0M M, (i : ℝ) * gaussWeight l i) +
              m ^ 2 * partitionFn (S0M M) l := by
        rw [partitionFn_S0M_eq_sum, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [hexp, hN1]
      ring
    have hvar_pos : 0 < ∑ i ∈ F0M M, ((i : ℝ) - m) ^ 2 * gaussWeight l i := by
      have h12_sub : ({1, 2} : Finset ℤ) ⊆ F0M M := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [F0M, Finset.mem_Icc]
        rcases hx with rfl | rfl <;> exact ⟨by omega, by exact_mod_cast (by omega : _ ≤ M)⟩
      have hpair :
          ((1 : ℝ) - m) ^ 2 * gaussWeight l 1 + ((2 : ℝ) - m) ^ 2 * gaussWeight l 2 ≤
            ∑ i ∈ F0M M, ((i : ℝ) - m) ^ 2 * gaussWeight l i := by
        have hle := Finset.sum_le_sum_of_subset_of_nonneg h12_sub
          (fun i _ _ ↦ mul_nonneg (sq_nonneg ((i : ℝ) - m)) (gaussWeight_pos l i).le)
        rw [Finset.sum_pair (by decide : (1 : ℤ) ≠ 2)] at hle
        push_cast at hle
        exact hle
      have hw1 := gaussWeight_pos l 1
      have hw2 := gaussWeight_pos l 2
      have hsq : 0 < ((1 : ℝ) - m) ^ 2 ∨ 0 < ((2 : ℝ) - m) ^ 2 := by
        by_cases hm1 : m = 1
        · right; rw [hm1]; norm_num
        · left; exact sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hm1))
      rcases hsq with hpos1 | hpos2
      · exact lt_of_lt_of_le
          (add_pos_of_pos_of_nonneg (mul_pos hpos1 hw1) (mul_nonneg (sq_nonneg _) hw2.le))
          hpair
      · exact lt_of_lt_of_le
          (add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg _) hw1.le) (mul_pos hpos2 hw2))
          hpair
    rw [hvar_id]
    exact div_pos (mul_pos hZ_pos hvar_pos) (sq_pos_of_pos hZ_pos)
  apply strictMono_of_deriv_pos
  intro l
  obtain ⟨v, hv_pos, hv⟩ := hderiv l
  rwa [hv.deriv]

theorem continuous_meanS0M {M : ℕ} (hM : 1 ≤ M) : Continuous (meanS0M M) := by
  unfold meanS0M
  refine Continuous.div ?_ ?_ (fun l ↦ (partitionFn_S0M_pos hM l).ne')
  · exact continuous_finsetSum _ fun i _ ↦
      continuous_const.mul (continuous_iff_continuousAt.mpr fun l ↦
        (hasDerivAt_gaussWeight i l).continuousAt)
  · rw [funext (partitionFn_S0M_eq_sum M)]
    exact continuous_finsetSum _ fun i _ ↦
      continuous_iff_continuousAt.mpr fun l ↦ (hasDerivAt_gaussWeight i l).continuousAt

/-- Upper bound `U_{1,7}(y) = P₇(y) + (8/7) y⁸ 2⁻²⁸ ≥ Z_{S_{≥ 1}}(yTilt y)` for `y ≤ 16`. -/
def sge1Bound7Y (y : ℝ) : ℝ :=
  sevenPartY y + 8 / 7 * (y ^ 8 / 268435456)

/-- Upper bound `M_{∞,7}^{ub}(y) ≥ M_{S_{≥ 1}}(yTilt y)` for `y ≤ 16`. -/
def sge1MeanUb7Y (y : ℝ) : ℝ :=
  (sevenFirstY y + 64 / 7 * (y ^ 8 / 268435456)) / sevenPartY y

private theorem sevenMeanY_lt_eight {y : ℝ} (hy : 0 < y) : sevenMeanY y < 8 := by
  have hP := sevenPartY_pos hy
  unfold sevenMeanY
  rw [div_lt_iff₀ hP]
  unfold sevenFirstY sevenPartY
  nlinarith [pow_pos hy 2, pow_pos hy 3, pow_pos hy 4, pow_pos hy 5,
    pow_pos hy 6, pow_pos hy 7]

theorem sevenMeanY_le_meanS0M {M : ℕ} (hM : 7 ≤ M) {y : ℝ} (hy : 0 < y) :
    sevenMeanY y ≤ meanS0M M (yTilt y) := by
  have hM1 : 1 ≤ M := by omega
  have hdisj : Disjoint F07 (Finset.Icc 8 (M : ℤ)) := by
    rw [Finset.disjoint_left]
    intro i hi7 hi8
    simp only [F07, Finset.mem_insert, Finset.mem_singleton] at hi7
    simp only [Finset.mem_Icc] at hi8
    omega
  have hunion : F07 ∪ Finset.Icc 8 (M : ℤ) = F0M M := by
    ext i
    simp only [Finset.mem_union, F07, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_Icc, F0M]
    omega
  have hZ_split : partitionFn (S0M M) (yTilt y) =
      sevenPartY y + ∑ i ∈ Finset.Icc 8 (M : ℤ), gaussWeight (yTilt y) i := by
    rw [partitionFn_S0M_eq_sum, ← hunion, Finset.sum_union hdisj, sum_F07_yTilt y hy]
  have hQ7 : ∑ i ∈ F07, (i : ℝ) * gaussWeight (yTilt y) i = sevenFirstY y := by
    obtain ⟨-, -, h1, h2, h3, h4, h5, h6, h7⟩ := weights_yTilt y hy
    rw [sum_F07, h1, h2, h3, h4, h5, h6, h7]
    push_cast; unfold sevenFirstY; ring
  have hQ_split : ∑ i ∈ F0M M, (i : ℝ) * gaussWeight (yTilt y) i =
      sevenFirstY y + ∑ i ∈ Finset.Icc 8 (M : ℤ), (i : ℝ) * gaussWeight (yTilt y) i := by
    rw [← hunion, Finset.sum_union hdisj, hQ7]
  have htail : sevenMeanY y * ∑ i ∈ Finset.Icc 8 (M : ℤ), gaussWeight (yTilt y) i ≤
      ∑ i ∈ Finset.Icc 8 (M : ℤ), (i : ℝ) * gaussWeight (yTilt y) i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have hi8 : (8 : ℝ) ≤ (i : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hi).1
    exact mul_le_mul_of_nonneg_right
      (le_trans (sevenMeanY_lt_eight hy).le hi8) (gaussWeight_pos _ _).le
  have hP7 := sevenPartY_pos hy
  have hZM := partitionFn_S0M_pos hM1 (yTilt y)
  unfold meanS0M
  rw [le_div_iff₀ hZM, hZ_split, hQ_split]
  have h7eq : sevenMeanY y * sevenPartY y = sevenFirstY y :=
    div_mul_cancel₀ _ hP7.ne'
  linarith

private theorem sge1_partition_and_first_split {M : ℕ} (hM : 1 ≤ M) (lambda : ℝ) :
    let mu := lambda - 2 * q
    let S := Real.exp (2 * lambda - 2 * q)
    S * extendedGaussianPartition q mu =
      partitionFn (S0M M) lambda +
        ∑' k : ℕ, gaussWeight lambda ((M : ℤ) + 1 + (k : ℤ)) ∧
    S * (extendedGaussianFirstNumerator q mu + 2 * extendedGaussianPartition q mu) =
      (∑ i ∈ F0M M, (i : ℝ) * gaussWeight lambda i) +
        ∑' k : ℕ, (((M : ℤ) + 1 + (k : ℤ)) : ℝ) *
          gaussWeight lambda ((M : ℤ) + 1 + (k : ℤ)) := by
  intro mu S
  have hexc : S * extendedGaussianExceptionalAtom q mu = gaussWeight lambda 1 := by
    dsimp [S, mu]
    unfold extendedGaussianExceptionalAtom gaussWeight q
    rw [← Real.exp_add]; push_cast; congr 1; ring
  have hnat (d : ℕ) :
      S * extendedGaussianNaturalTerm q mu d = gaussWeight lambda ((d : ℤ) + 2) := by
    dsimp [S, mu]
    unfold extendedGaussianNaturalTerm gaussWeight q
    rw [← Real.exp_add]; push_cast; congr 1; ring
  have hs0 := summable_extendedGaussianNaturalTerm q_pos (lambda := mu)
  have hs1 := summable_extendedGaussianFirstMoment q_pos (lambda := mu)
  -- Split at `M - 1` so `1` and `{2, ..., M}` combine into `F0M M`
  set K : ℕ := M - 1
  have hKM : K + 1 = M := Nat.sub_add_cancel hM
  have hF0M_split : ∀ f : ℤ → ℝ,
      ∑ i ∈ F0M M, f i = f 1 + ∑ d ∈ Finset.range K, f ((d : ℤ) + 2) := by
    intro f
    have hbij : ∑ d ∈ Finset.range K, f ((d : ℤ) + 2) =
        ∑ i ∈ Finset.Icc 2 (M : ℤ), f i := by
      refine Finset.sum_bij (fun d _ ↦ (d : ℤ) + 2) ?_ ?_ ?_ (fun _ _ ↦ rfl)
      · intro d hd
        rw [Finset.mem_range] at hd
        rw [Finset.mem_Icc]
        exact ⟨by omega, by omega⟩
      · intro a _ b _ h; omega
      · intro i hi
        rw [Finset.mem_Icc] at hi
        refine ⟨(i - 2).toNat, ?_, ?_⟩
        · rw [Finset.mem_range]; omega
        · omega
    rw [hbij]
    have hdisj : Disjoint ({1} : Finset ℤ) (Finset.Icc 2 (M : ℤ)) := by
      simp [Finset.mem_Icc]
    have hun : ({1} : Finset ℤ) ∪ Finset.Icc 2 (M : ℤ) = F0M M := by
      ext i
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc, F0M]
      omega
    rw [← hun, Finset.sum_union hdisj, Finset.sum_singleton]
  constructor
  · unfold extendedGaussianPartition
    rw [← hs0.sum_add_tsum_nat_add K, mul_add, mul_add, hexc, Finset.mul_sum]
    have hsum_eq : ∑ d ∈ Finset.range K, S * extendedGaussianNaturalTerm q mu d =
        ∑ d ∈ Finset.range K, gaussWeight lambda ((d : ℤ) + 2) :=
      Finset.sum_congr rfl fun d _ ↦ hnat d
    have htail_eq : S * ∑' k : ℕ, extendedGaussianNaturalTerm q mu (k + K) =
        ∑' k : ℕ, gaussWeight lambda ((M : ℤ) + 1 + (k : ℤ)) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun k ↦ ?_
      rw [hnat (k + K)]
      congr 1; omega
    rw [hsum_eq, htail_eq, partitionFn_S0M_eq_sum, hF0M_split, add_assoc]
  · unfold extendedGaussianFirstNumerator extendedGaussianPartition
    rw [← hs1.sum_add_tsum_nat_add K, ← hs0.sum_add_tsum_nat_add K]
    have hcomb_fin :
        S * (-extendedGaussianExceptionalAtom q mu +
            ((∑ d ∈ Finset.range K, (d : ℝ) * extendedGaussianNaturalTerm q mu d) +
              ∑' k : ℕ, ((k + K : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu (k + K)) +
            2 * (extendedGaussianExceptionalAtom q mu +
              ((∑ d ∈ Finset.range K, extendedGaussianNaturalTerm q mu d) +
                ∑' k : ℕ, extendedGaussianNaturalTerm q mu (k + K)))) =
          S * extendedGaussianExceptionalAtom q mu +
            (∑ d ∈ Finset.range K, (((d : ℤ) + 2) : ℝ) *
              (S * extendedGaussianNaturalTerm q mu d)) +
            (S * ∑' k : ℕ, ((k + K : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu (k + K) +
              2 * (S * ∑' k : ℕ, extendedGaussianNaturalTerm q mu (k + K))) := by
      have hs_d : S * ∑ d ∈ Finset.range K, (d : ℝ) * extendedGaussianNaturalTerm q mu d =
          ∑ d ∈ Finset.range K, (d : ℝ) * (S * extendedGaussianNaturalTerm q mu d) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
      have hs_0 : S * ∑ d ∈ Finset.range K, extendedGaussianNaturalTerm q mu d =
          ∑ d ∈ Finset.range K, S * extendedGaussianNaturalTerm q mu d :=
        Finset.mul_sum _ _ _
      have hs_merge :
          (∑ d ∈ Finset.range K, (d : ℝ) * (S * extendedGaussianNaturalTerm q mu d)) +
            2 * (∑ d ∈ Finset.range K, S * extendedGaussianNaturalTerm q mu d) =
          ∑ d ∈ Finset.range K, (((d : ℤ) + 2) : ℝ) *
            (S * extendedGaussianNaturalTerm q mu d) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d _ ↦ ?_
        push_cast; ring
      linarith
    rw [hcomb_fin, hexc]
    have hfin_w :
        gaussWeight lambda 1 +
          ∑ d ∈ Finset.range K, (((d : ℤ) + 2) : ℝ) *
            (S * extendedGaussianNaturalTerm q mu d) =
        ∑ i ∈ F0M M, (i : ℝ) * gaussWeight lambda i := by
      rw [hF0M_split (fun i ↦ (i : ℝ) * gaussWeight lambda i)]
      simp only [Int.cast_one, one_mul]
      congr 1
      exact Finset.sum_congr rfl fun d _ ↦ by rw [hnat d]; push_cast; rfl
    have htail_w :
        S * ∑' k : ℕ, ((k + K : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu (k + K) +
          2 * (S * ∑' k : ℕ, extendedGaussianNaturalTerm q mu (k + K)) =
        ∑' k : ℕ, (((M : ℤ) + 1 + (k : ℤ)) : ℝ) *
          gaussWeight lambda ((M : ℤ) + 1 + (k : ℤ)) := by
      have ha := ((summable_nat_add_iff K).mpr hs1).mul_left S
      have hb := (((summable_nat_add_iff K).mpr hs0).mul_left S).mul_left 2
      rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← ha.tsum_add hb]
      refine tsum_congr fun k ↦ ?_
      have hn := hnat (k + K)
      have hidx : ((k + K : ℕ) : ℤ) + 2 = (M : ℤ) + 1 + (k : ℤ) := by omega
      have hcast : ((k + K : ℕ) : ℝ) + 2 = (((M : ℤ) + 1 + (k : ℤ)) : ℝ) := by
        exact_mod_cast hidx
      rw [← hidx, ← hn]
      linarith [congrArg (· * (S * extendedGaussianNaturalTerm q mu (k + K))) hcast]
    linarith

theorem meanS0M_lt_sge1Mean {M : ℕ} (hM : 1 ≤ M) (lambda : ℝ) :
    meanS0M M lambda < extendedGaussianMean q (lambda - 2 * q) + 2 := by
  obtain ⟨hZ_eq, hQ_eq⟩ := sge1_partition_and_first_split hM lambda
  set mu := lambda - 2 * q
  set S := Real.exp (2 * lambda - 2 * q)
  have hS_pos : 0 < S := Real.exp_pos _
  have hZinf_pos := extendedGaussianPartition_pos q_pos (lambda := mu)
  have hZM_pos := partitionFn_S0M_pos hM lambda
  have hm_le_M : meanS0M M lambda ≤ (M : ℝ) := by
    unfold meanS0M
    rw [div_le_iff₀ hZM_pos, partitionFn_S0M_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have hiM : (i : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hi).2
    exact mul_le_mul_of_nonneg_right hiM (gaussWeight_pos _ _).le
  have hM_sub : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub hM, Nat.cast_one]
  have hs_tail0 : Summable (fun k : ℕ ↦ gaussWeight lambda ((M : ℤ) + 1 + (k : ℤ))) := by
    refine (((summable_nat_add_iff (M - 1)).mpr
      (summable_extendedGaussianNaturalTerm q_pos (lambda := mu))).mul_left S).congr fun k ↦ ?_
    dsimp [S, mu]; unfold extendedGaussianNaturalTerm gaussWeight q
    rw [← Real.exp_add]; push_cast; rw [hM_sub]; congr 1; ring
  have hs_tail1 : Summable (fun k : ℕ ↦
      (((M : ℤ) + 1 + (k : ℤ)) : ℝ) * gaussWeight lambda ((M : ℤ) + 1 + (k : ℤ))) := by
    have h1 := ((summable_nat_add_iff (M - 1)).mpr
      (summable_extendedGaussianFirstMoment q_pos (lambda := mu))).mul_left S
    have h2 := hs_tail0.mul_left 2
    refine (h1.add h2).congr fun k ↦ ?_
    have hn : S * extendedGaussianNaturalTerm q mu (k + (M - 1)) =
        gaussWeight lambda ((M : ℤ) + 1 + (k : ℤ)) := by
      dsimp [S, mu]; unfold extendedGaussianNaturalTerm gaussWeight q
      rw [← Real.exp_add]; push_cast; rw [hM_sub]; congr 1; ring
    have hc : ((k + (M - 1) : ℕ) : ℝ) + 2 = (((M : ℤ) + 1 + (k : ℤ)) : ℝ) := by
      push_cast; rw [hM_sub]; ring
    calc S * (((k + (M - 1) : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu (k + (M - 1))) +
            2 * gaussWeight lambda ((M : ℤ) + 1 + (k : ℤ))
        = ((k + (M - 1) : ℕ) : ℝ) * (S * extendedGaussianNaturalTerm q mu (k + (M - 1))) +
            2 * gaussWeight lambda ((M : ℤ) + 1 + (k : ℤ)) := by ring
      _ = (((k + (M - 1) : ℕ) : ℝ) + 2) * gaussWeight lambda ((M : ℤ) + 1 + (k : ℤ)) := by
            rw [hn]; ring
      _ = (((M : ℤ) + 1 + (k : ℤ)) : ℝ) * gaussWeight lambda ((M : ℤ) + 1 + (k : ℤ)) := by
            rw [hc]
  have htail_strict :
      meanS0M M lambda * ∑' k : ℕ, gaussWeight lambda ((M : ℤ) + 1 + (k : ℤ)) <
        ∑' k : ℕ, (((M : ℤ) + 1 + (k : ℤ)) : ℝ) *
          gaussWeight lambda ((M : ℤ) + 1 + (k : ℤ)) := by
    rw [← hs_tail0.sum_add_tsum_nat_add 1, ← hs_tail1.sum_add_tsum_nat_add 1,
      Finset.sum_range_one, Finset.sum_range_one, mul_add]
    have h0_lt : meanS0M M lambda * gaussWeight lambda ((M : ℤ) + 1 + ((0 : ℕ) : ℤ)) <
        (((M : ℤ) + 1 + ((0 : ℕ) : ℤ)) : ℝ) * gaussWeight lambda ((M : ℤ) + 1 + ((0 : ℕ) : ℤ)) := by
      apply mul_lt_mul_of_pos_right _ (gaussWeight_pos _ _)
      push_cast; linarith
    have hrest_le :
        meanS0M M lambda * ∑' k : ℕ, gaussWeight lambda ((M : ℤ) + 1 + ((k + 1 : ℕ) : ℤ)) ≤
          ∑' k : ℕ, (((M : ℤ) + 1 + ((k + 1 : ℕ) : ℤ)) : ℝ) *
            gaussWeight lambda ((M : ℤ) + 1 + ((k + 1 : ℕ) : ℤ)) := by
      rw [← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun k ↦ ?_)
        (((summable_nat_add_iff 1).mpr hs_tail0).mul_left _)
        ((summable_nat_add_iff 1).mpr hs_tail1)
      apply mul_le_mul_of_nonneg_right _ (gaussWeight_pos _ _).le
      push_cast; linarith
    linarith
  have hmean_eq : extendedGaussianMean q mu + 2 =
      (S * (extendedGaussianFirstNumerator q mu + 2 * extendedGaussianPartition q mu)) /
        (S * extendedGaussianPartition q mu) := by
    unfold extendedGaussianMean
    field_simp [hS_pos.ne', hZinf_pos.ne']
  rw [hmean_eq, lt_div_iff₀ (mul_pos hS_pos hZinf_pos), hZ_eq, hQ_eq]
  have hMeq : meanS0M M lambda * partitionFn (S0M M) lambda =
      ∑ i ∈ F0M M, (i : ℝ) * gaussWeight lambda i :=
    div_mul_cancel₀ _ hZM_pos.ne'
  linarith

private theorem sge1_bounds7_at_yTilt {y : ℝ} (hy : 0 < y) (hy16 : y ≤ 16) :
    let mu := yTilt y - 2 * q
    let S := y ^ 2 / 2
    sevenPartY y ≤ S * extendedGaussianPartition q mu ∧
      S * extendedGaussianPartition q mu ≤ sge1Bound7Y y ∧
      extendedGaussianMean q mu + 2 ≤ sge1MeanUb7Y y := by
  intro mu S
  have hS_eq : S = Real.exp (2 * yTilt y - 2 * q) := by
    dsimp [S]; unfold yTilt q
    have h1 : 2 * (Real.log 2 / 2 + Real.log y) - 2 * Real.log 2 =
        2 * Real.log y - Real.log 2 := by ring
    rw [h1, Real.exp_sub, show (2 : ℝ) * Real.log y = ((2 : ℕ) : ℝ) * Real.log y by norm_num,
      Real.exp_nat_mul, Real.exp_log hy, Real.exp_log two_pos]
  have hSpos : 0 < S := by dsimp [S]; positivity
  obtain ⟨hZ7, hQ7⟩ := sge1_partition_and_first_split (M := 7) (by norm_num) (yTilt y)
  rw [← hS_eq] at hZ7 hQ7
  have hP7_eq : partitionFn (S0M 7) (yTilt y) = sevenPartY y := by
    have hF : F0M 7 = F07 := by decide
    rw [partitionFn_S0M_eq_sum, hF, sum_F07_yTilt y hy]
  have hF7_eq : ∑ i ∈ F0M 7, (i : ℝ) * gaussWeight (yTilt y) i = sevenFirstY y := by
    have hF : F0M 7 = F07 := by decide
    obtain ⟨-, -, w1, w2, w3, w4, w5, w6, w7⟩ := weights_yTilt y hy
    rw [hF, sum_F07, w1, w2, w3, w4, w5, w6, w7]
    push_cast; unfold sevenFirstY; ring
  have hw8 : gaussWeight (yTilt y) 8 = y ^ 8 / 268435456 := by
    rw [gaussWeight_yTilt y hy 8 8 28 (by norm_num) (by norm_num)]; norm_num
  have hy_step : ∀ k : ℕ,
      gaussWeight (yTilt y) ((7 : ℤ) + 1 + ((k + 1 : ℕ) : ℤ)) ≤
        1 / 16 * gaussWeight (yTilt y) ((7 : ℤ) + 1 + (k : ℤ)) ∧
      (((7 : ℤ) + 1 + ((k + 1 : ℕ) : ℤ)) : ℝ) *
          gaussWeight (yTilt y) ((7 : ℤ) + 1 + ((k + 1 : ℕ) : ℤ)) ≤
        1 / 8 * ((((7 : ℤ) + 1 + (k : ℤ)) : ℝ) *
          gaussWeight (yTilt y) ((7 : ℤ) + 1 + (k : ℤ))) := by
    intro k
    set j : ℤ := 8 + (k : ℤ)
    have hj_eq1 : (7 : ℤ) + 1 + (k : ℤ) = j := by omega
    have hj_eq2 : (7 : ℤ) + 1 + ((k + 1 : ℕ) : ℤ) = j + 1 := by omega
    have hj_r1 : (((7 : ℤ) + 1 + (k : ℤ)) : ℝ) = (j : ℝ) := by dsimp [j]; push_cast; ring
    have hj_r2 : (((7 : ℤ) + 1 + ((k + 1 : ℕ) : ℤ)) : ℝ) = ((j + 1 : ℤ) : ℝ) := by
      dsimp [j]; push_cast; ring
    rw [hj_r1, hj_r2, hj_eq1, hj_eq2]
    have hratio : gaussWeight (yTilt y) (j + 1) =
        Real.exp (yTilt y - q / 2 * (2 * (j : ℝ) + 1)) * gaussWeight (yTilt y) j := by
      unfold gaussWeight q; rw [← Real.exp_add]; push_cast; congr 1; ring
    have hj8 : (8 : ℝ) ≤ (j : ℝ) := by dsimp [j]; exact_mod_cast (by omega : (8 : ℤ) ≤ 8 + k)
    have hexp_le : yTilt y - q / 2 * (2 * (j : ℝ) + 1) ≤ -(4 * q) := by
      have hyt := yTilt_le_nine_q_half hy hy16
      nlinarith [mul_le_mul_of_nonneg_left hj8 q_pos.le]
    have hexp4q : Real.exp (-(4 * q)) = 1 / 16 := by
      rw [Real.exp_neg, show (4 : ℝ) * q = ((4 : ℕ) : ℝ) * Real.log 2 by unfold q; norm_num,
        Real.exp_nat_mul, Real.exp_log two_pos]
      norm_num
    have h16 : Real.exp (yTilt y - q / 2 * (2 * (j : ℝ) + 1)) ≤ 1 / 16 := by
      rw [← hexp4q]; exact Real.exp_le_exp.mpr hexp_le
    rw [hratio]
    constructor
    · exact mul_le_mul_of_nonneg_right h16 (gaussWeight_pos _ _).le
    · have hrat : ((j + 1 : ℤ) : ℝ) * (1 / 16) ≤ 1 / 8 * (j : ℝ) := by
        push_cast; linarith
      have hj1_nn : (0 : ℝ) ≤ ((j + 1 : ℤ) : ℝ) := by push_cast; linarith
      calc ((j + 1 : ℤ) : ℝ) *
              (Real.exp (yTilt y - q / 2 * (2 * (j : ℝ) + 1)) * gaussWeight (yTilt y) j)
          ≤ ((j + 1 : ℤ) : ℝ) * (1 / 16 * gaussWeight (yTilt y) j) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right h16 (gaussWeight_pos _ _).le) hj1_nn
        _ = (((j + 1 : ℤ) : ℝ) * (1 / 16)) * gaussWeight (yTilt y) j := by ring
        _ ≤ (1 / 8 * (j : ℝ)) * gaussWeight (yTilt y) j :=
            mul_le_mul_of_nonneg_right hrat (gaussWeight_pos _ _).le
        _ = 1 / 8 * ((j : ℝ) * gaussWeight (yTilt y) j) := by ring
  have hgeom0 : ∀ k : ℕ,
      gaussWeight (yTilt y) ((7 : ℤ) + 1 + (k : ℤ)) ≤
        (1 / 8 : ℝ) ^ k * gaussWeight (yTilt y) 8 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hw_pos := gaussWeight_pos (yTilt y) ((7 : ℤ) + 1 + (k : ℤ))
      calc gaussWeight (yTilt y) ((7 : ℤ) + 1 + ((k + 1 : ℕ) : ℤ))
          ≤ 1 / 16 * gaussWeight (yTilt y) ((7 : ℤ) + 1 + (k : ℤ)) := (hy_step k).1
        _ ≤ 1 / 8 * gaussWeight (yTilt y) ((7 : ℤ) + 1 + (k : ℤ)) :=
            mul_le_mul_of_nonneg_right (by norm_num) hw_pos.le
        _ ≤ 1 / 8 * ((1 / 8 : ℝ) ^ k * gaussWeight (yTilt y) 8) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 8 : ℝ) ^ (k + 1) * gaussWeight (yTilt y) 8 := by ring
  have hgeom1 : ∀ k : ℕ,
      (((7 : ℤ) + 1 + (k : ℤ)) : ℝ) * gaussWeight (yTilt y) ((7 : ℤ) + 1 + (k : ℤ)) ≤
        (1 / 8 : ℝ) ^ k * (8 * gaussWeight (yTilt y) 8) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      calc (((7 : ℤ) + 1 + ((k + 1 : ℕ) : ℤ)) : ℝ) *
              gaussWeight (yTilt y) ((7 : ℤ) + 1 + ((k + 1 : ℕ) : ℤ))
          ≤ 1 / 8 * ((((7 : ℤ) + 1 + (k : ℤ)) : ℝ) *
              gaussWeight (yTilt y) ((7 : ℤ) + 1 + (k : ℤ))) := (hy_step k).2
        _ ≤ 1 / 8 * ((1 / 8 : ℝ) ^ k * (8 * gaussWeight (yTilt y) 8)) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 8 : ℝ) ^ (k + 1) * (8 * gaussWeight (yTilt y) 8) := by ring
  have hs_w : Summable (fun k : ℕ ↦ gaussWeight (yTilt y) ((7 : ℤ) + 1 + (k : ℤ))) :=
    (summable_gaussWeight (yTilt y)).comp_injective fun a b (h : (7 : ℤ) + 1 + a = 7 + 1 + b) ↦ by omega
  have hs_g0 : Summable (fun k : ℕ ↦ (1 / 8 : ℝ) ^ k * gaussWeight (yTilt y) 8) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have hs_g1 : Summable (fun k : ℕ ↦ (1 / 8 : ℝ) ^ k * (8 * gaussWeight (yTilt y) 8)) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have hs_w1 : Summable (fun k : ℕ ↦
      (((7 : ℤ) + 1 + (k : ℤ)) : ℝ) * gaussWeight (yTilt y) ((7 : ℤ) + 1 + (k : ℤ))) :=
    Summable.of_nonneg_of_le
      (fun k ↦ mul_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ 7 + 1 + k)) (gaussWeight_pos _ _).le)
      hgeom1 hs_g1
  have htail0 : ∑' k : ℕ, gaussWeight (yTilt y) ((7 : ℤ) + 1 + (k : ℤ)) ≤
      8 / 7 * (y ^ 8 / 268435456) := by
    calc ∑' k : ℕ, gaussWeight (yTilt y) ((7 : ℤ) + 1 + (k : ℤ))
        ≤ ∑' k : ℕ, (1 / 8 : ℝ) ^ k * gaussWeight (yTilt y) 8 :=
          Summable.tsum_le_tsum hgeom0 hs_w hs_g0
      _ = 8 / 7 * (y ^ 8 / 268435456) := by
          rw [tsum_mul_right,
            tsum_geometric_of_lt_one (r := (1 / 8 : ℝ)) (by norm_num) (by norm_num), hw8]
          ring
  have htail1 : ∑' k : ℕ,
      (((7 : ℤ) + 1 + (k : ℤ)) : ℝ) * gaussWeight (yTilt y) ((7 : ℤ) + 1 + (k : ℤ)) ≤
        64 / 7 * (y ^ 8 / 268435456) := by
    calc ∑' k : ℕ, (((7 : ℤ) + 1 + (k : ℤ)) : ℝ) * gaussWeight (yTilt y) ((7 : ℤ) + 1 + (k : ℤ))
        ≤ ∑' k : ℕ, (1 / 8 : ℝ) ^ k * (8 * gaussWeight (yTilt y) 8) :=
          Summable.tsum_le_tsum hgeom1 hs_w1 hs_g1
      _ = 64 / 7 * (y ^ 8 / 268435456) := by
          rw [tsum_mul_right,
            tsum_geometric_of_lt_one (r := (1 / 8 : ℝ)) (by norm_num) (by norm_num), hw8]
          ring
  have hP7_le : sevenPartY y ≤ S * extendedGaussianPartition q mu := by
    rw [hZ7, hP7_eq]
    exact le_add_of_nonneg_right (tsum_nonneg fun _ ↦ (gaussWeight_pos _ _).le)
  have hP7_hi : S * extendedGaussianPartition q mu ≤ sge1Bound7Y y := by
    rw [hZ7, hP7_eq]; unfold sge1Bound7Y; linarith
  have hZinf_pos := extendedGaussianPartition_pos q_pos (lambda := mu)
  have hP7_pos := sevenPartY_pos hy
  refine ⟨hP7_le, hP7_hi, ?_⟩
  have hmean_eq : extendedGaussianMean q mu + 2 =
      (S * (extendedGaussianFirstNumerator q mu + 2 * extendedGaussianPartition q mu)) /
        (S * extendedGaussianPartition q mu) := by
    unfold extendedGaussianMean; field_simp [hSpos.ne', hZinf_pos.ne']
  rw [hmean_eq, div_le_iff₀ (mul_pos hSpos hZinf_pos), hQ7, hF7_eq]
  unfold sge1MeanUb7Y
  have hnum_pos : 0 ≤ sevenFirstY y + 64 / 7 * (y ^ 8 / 268435456) := by
    unfold sevenFirstY; positivity
  calc sevenFirstY y + ∑' k : ℕ,
          (((7 : ℤ) + 1 + (k : ℤ)) : ℝ) * gaussWeight (yTilt y) ((7 : ℤ) + 1 + (k : ℤ))
      ≤ sevenFirstY y + 64 / 7 * (y ^ 8 / 268435456) := by linarith
    _ = ((sevenFirstY y + 64 / 7 * (y ^ 8 / 268435456)) / sevenPartY y) * sevenPartY y := by
        rw [div_mul_cancel₀ _ hP7_pos.ne']
    _ ≤ ((sevenFirstY y + 64 / 7 * (y ^ 8 / 268435456)) / sevenPartY y) *
          (S * extendedGaussianPartition q mu) :=
        mul_le_mul_of_nonneg_left hP7_le (div_nonneg hnum_pos hP7_pos.le)

/-- **Existence and uniqueness of `λ_{S_{0,M}}(T)` (`Lemma 3.2(i)`):**
for every `M ≥ 7` and `T ∈ [M₇(121/25), M₇(209/20)]` (covering all `T̃_{δ̃}`
for `δ̃ ∈ [0, 207/200]`), there is a unique `λ ∈ ℝ` with `meanS0M M λ = T`. -/
theorem existsUnique_s0mTilt {M : ℕ} (hM : 7 ≤ M) {T : ℝ}
    (hT : T ∈ Set.Icc (sevenMeanY (121 / 25)) (sevenMeanY (209 / 20))) :
    ∃! lambda : ℝ, meanS0M M lambda = T := by
  have hM1 : 1 ≤ M := by omega
  have hM2 : 2 ≤ M := by omega
  have hlo_ub : sge1MeanUb7Y (119 / 25) < sevenMeanY (121 / 25) := by
    unfold sge1MeanUb7Y sevenMeanY sevenFirstY sevenPartY; norm_num
  have hlo_m : meanS0M M (yTilt (119 / 25)) < T := by
    have h1 := meanS0M_lt_sge1Mean hM1 (yTilt (119 / 25))
    have h2 := (sge1_bounds7_at_yTilt (y := 119 / 25) (by norm_num) (by norm_num)).2.2
    linarith [hT.1]
  have hhi_m : T ≤ meanS0M M (yTilt (209 / 20)) :=
    le_trans hT.2 (sevenMeanY_le_meanS0M hM (by norm_num))
  have hlt_tilt : yTilt (119 / 25) ≤ yTilt (209 / 20) := by
    unfold yTilt
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 119 / 25)
      (by norm_num : (119 / 25 : ℝ) ≤ 209 / 20)]
  obtain ⟨lambda, _, hlam⟩ := intermediate_value_Icc hlt_tilt
    (continuous_meanS0M hM1).continuousOn ⟨hlo_m.le, hhi_m⟩
  refine ⟨lambda, hlam, fun l hl ↦ ?_⟩
  exact (strictMono_meanS0M hM2).injective (hl.trans hlam.symm)

/-- **`p^*_1 < p_{1,∞}(δ̃)` (`eq:p1M-lt-pinf` in Appendix B.2):**
for all `M ≥ 7`, `δ̃ ≤ 207 / 200`, and `λ` with `meanS0M M λ = phaseTarget δ̃`,
`gibbsProbS0M M λ 1 < p1Inf δ̃`. -/
theorem gibbsProbS0M_one_lt_p1Inf {M : ℕ} (hM : 7 ≤ M) {td lambda : ℝ}
    (htd : td ≤ 207 / 200) (hmean : meanS0M M lambda = phaseTarget td) :
    gibbsProbS0M M lambda 1 < p1Inf td := by
  have hM1 : 1 ≤ M := by omega
  obtain ⟨h2lo, _⟩ := two_div_log_two_bounds
  set T := phaseTarget td
  have hT_gt2 : -1 < T - 2 := by dsimp [T]; unfold phaseTarget; linarith
  set linf := sge1Tilt T
  have hmean_inf : extendedGaussianMean q (linf - 2 * q) + 2 = T := by
    dsimp [linf]; unfold sge1Tilt
    rw [add_sub_cancel_right, extendedGaussianMean_extendedGaussianTilt q_pos hT_gt2]
    ring
  have hlinf_lt : linf < lambda := by
    have hlt_m : extendedGaussianMean q (linf - 2 * q) <
        extendedGaussianMean q (lambda - 2 * q) := by
      have := meanS0M_lt_sge1Mean hM1 lambda
      linarith
    have := (strictMono_extendedGaussianMean q q_pos).lt_iff_lt.mp hlt_m
    linarith
  -- Compare `p_i := gibbsProbS0M M lambda i` with `pinf_i := gaussWeight linf i / partitionFn Sge1 linf`
  set Zinf := partitionFn Sge1 linf
  set ZM := partitionFn (S0M M) lambda
  have hZinf_pos : 0 < Zinf := by
    dsimp [Zinf]
    rw [partitionFn_Sge1_eq_shift_extendedGaussian]
    exact mul_pos (Real.exp_pos _) (extendedGaussianPartition_pos q_pos)
  have hZM_pos := partitionFn_S0M_pos hM1 lambda
  set pinf : ℤ → ℝ := fun i ↦ gaussWeight linf i / Zinf
  have hp1_inf_eq : p1Inf td = pinf 1 := rfl
  -- Identity `∑_{i ∈ F0M M} (M + 1 - i) * pinf i ≥ (M + 1) - T = ∑_{i ∈ F0M M} (M + 1 - i) * p_i`
  obtain ⟨hZ_sp, hQ_sp⟩ := sge1_partition_and_first_split hM1 linf
  set S_inf := Real.exp (2 * linf - 2 * q)
  have hS_inf_pos : 0 < S_inf := Real.exp_pos _
  have hZinf_rel : S_inf * extendedGaussianPartition q (linf - 2 * q) = Zinf := by
    dsimp [Zinf, S_inf]; exact (partitionFn_Sge1_eq_shift_extendedGaussian linf).symm
  rw [hZinf_rel] at hZ_sp
  have hQinf_rel : S_inf * (extendedGaussianFirstNumerator q (linf - 2 * q) +
      2 * extendedGaussianPartition q (linf - 2 * q)) = T * Zinf := by
    have hm := hmean_inf
    unfold extendedGaussianMean at hm
    have hZp := extendedGaussianPartition_pos q_pos (lambda := linf - 2 * q)
    have h1 : extendedGaussianFirstNumerator q (linf - 2 * q) +
        2 * extendedGaussianPartition q (linf - 2 * q) =
        T * extendedGaussianPartition q (linf - 2 * q) := by
      field_simp [hZp.ne'] at hm ⊢; linarith
    rw [h1, ← mul_assoc, mul_comm S_inf T, mul_assoc, hZinf_rel]
  rw [hQinf_rel] at hQ_sp
  have hsum_pinf_ge :
      (M + 1 : ℝ) - T ≤ ∑ i ∈ F0M M, ((M + 1 : ℝ) - (i : ℝ)) * pinf i := by
    -- Multiply by `Zinf > 0`: equivalent to `(M + 1) * tail_Z ≤ tail_Q`!
    rw [← mul_le_mul_iff_left₀ hZinf_pos, Finset.sum_mul]
    have hfin_cancel :
        ∑ i ∈ F0M M, ((M + 1 : ℝ) - (i : ℝ)) * pinf i * Zinf =
          (M + 1 : ℝ) * partitionFn (S0M M) linf -
            ∑ i ∈ F0M M, (i : ℝ) * gaussWeight linf i := by
      calc ∑ i ∈ F0M M, ((M + 1 : ℝ) - (i : ℝ)) * pinf i * Zinf
          = ∑ i ∈ F0M M, ((M + 1 : ℝ) * gaussWeight linf i - (i : ℝ) * gaussWeight linf i) := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              dsimp [pinf]
              rw [mul_assoc, div_mul_cancel₀ _ hZinf_pos.ne']
              ring
        _ = (M + 1 : ℝ) * partitionFn (S0M M) linf -
              ∑ i ∈ F0M M, (i : ℝ) * gaussWeight linf i := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum, partitionFn_S0M_eq_sum]
    rw [hfin_cancel]
    have hs0 : Summable (fun k : ℕ ↦ gaussWeight linf ((M : ℤ) + 1 + (k : ℤ))) :=
      (summable_gaussWeight linf).comp_injective fun a b (h : (M : ℤ) + 1 + a = M + 1 + b) ↦ by omega
    have hM_sub : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub hM1, Nat.cast_one]
    have hs1 : Summable (fun k : ℕ ↦
        (((M : ℤ) + 1 + (k : ℤ)) : ℝ) * gaussWeight linf ((M : ℤ) + 1 + (k : ℤ))) := by
      have hsub := ((summable_nat_add_iff (M - 1)).mpr
        (summable_extendedGaussianFirstMoment q_pos (lambda := linf - 2 * q))).mul_left S_inf
      have hadd := hs0.mul_left 2
      refine (hsub.add hadd).congr fun k ↦ ?_
      have hn : S_inf * extendedGaussianNaturalTerm q (linf - 2 * q) (k + (M - 1)) =
          gaussWeight linf ((M : ℤ) + 1 + (k : ℤ)) := by
        dsimp [S_inf]; unfold extendedGaussianNaturalTerm gaussWeight q
        rw [← Real.exp_add]; push_cast; rw [hM_sub]; congr 1; ring
      have hc : ((k + (M - 1) : ℕ) : ℝ) + 2 = (((M : ℤ) + 1 + (k : ℤ)) : ℝ) := by
        push_cast; rw [hM_sub]; ring
      rw [← mul_assoc, mul_comm S_inf, mul_assoc, hn, ← add_mul, hc]
    have htail_le :
        (M + 1 : ℝ) * ∑' k : ℕ, gaussWeight linf ((M : ℤ) + 1 + (k : ℤ)) ≤
          ∑' k : ℕ, (((M : ℤ) + 1 + (k : ℤ)) : ℝ) *
            gaussWeight linf ((M : ℤ) + 1 + (k : ℤ)) := by
      rw [← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun k ↦ ?_) (hs0.mul_left _) hs1
      apply mul_le_mul_of_nonneg_right _ (gaussWeight_pos _ _).le
      push_cast; linarith
    have hmZ := congrArg ((M + 1 : ℝ) * ·) hZ_sp
    rw [mul_add] at hmZ
    linarith
  have hsum_p_eq :
      ∑ i ∈ F0M M, ((M + 1 : ℝ) - (i : ℝ)) * gibbsProbS0M M lambda i = (M + 1 : ℝ) - T := by
    have h1 := sum_gibbsProbS0M hM1 lambda
    have h2 := sum_mul_gibbsProbS0M M lambda
    rw [hmean] at h2
    calc ∑ i ∈ F0M M, ((M + 1 : ℝ) - (i : ℝ)) * gibbsProbS0M M lambda i
        = (M + 1 : ℝ) * (∑ i ∈ F0M M, gibbsProbS0M M lambda i) -
            ∑ i ∈ F0M M, (i : ℝ) * gibbsProbS0M M lambda i := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun _ _ ↦ by ring
      _ = (M + 1 : ℝ) - T := by rw [h1, h2]; ring
  rw [hp1_inf_eq]
  by_contra hge
  have hp1_ge : pinf 1 ≤ gibbsProbS0M M lambda 1 := not_lt.mp hge
  have h1_mem : (1 : ℤ) ∈ F0M M := by simp [F0M]; omega
  have h2_mem : (2 : ℤ) ∈ F0M M := by simp [F0M]; omega
  -- Ratio identity: `gibbsProbS0M M lambda i / pinf i = (gibbsProbS0M M lambda 1 / pinf 1) * exp ((lambda - linf) * (i - 1))`
  have hdom : ∀ i ∈ F0M M, pinf i ≤ gibbsProbS0M M lambda i := by
    intro i hi
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hi).1
    have hexp_ge : 1 ≤ Real.exp ((lambda - linf) * ((i : ℝ) - 1)) :=
      Real.one_le_exp (mul_nonneg (by linarith) (by linarith))
    have hrel : gibbsProbS0M M lambda i * pinf 1 =
        (gibbsProbS0M M lambda 1 * pinf i) * Real.exp ((lambda - linf) * ((i : ℝ) - 1)) := by
      simp only [gibbsProbS0M, hi, h1_mem, ↓reduceIte, pinf]
      unfold gaussWeight
      field_simp [hZM_pos.ne', hZinf_pos.ne']
      rw [mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1; push_cast; ring
    have hp1_pos : 0 < pinf 1 := div_pos (gaussWeight_pos _ _) hZinf_pos
    have hpi_pos : 0 < pinf i := div_pos (gaussWeight_pos _ _) hZinf_pos
    have hm1 : pinf 1 * pinf i ≤ gibbsProbS0M M lambda 1 * pinf i :=
      mul_le_mul_of_nonneg_right hp1_ge hpi_pos.le
    have hm2 : gibbsProbS0M M lambda 1 * pinf i ≤
        (gibbsProbS0M M lambda 1 * pinf i) * Real.exp ((lambda - linf) * ((i : ℝ) - 1)) :=
      le_mul_of_one_le_right (mul_nonneg (le_trans hp1_pos.le hp1_ge) hpi_pos.le) hexp_ge
    exact le_of_mul_le_mul_right (by linarith [hrel]) hp1_pos
  have hstrict2 : pinf 2 < gibbsProbS0M M lambda 2 := by
    have hexp_gt : 1 < Real.exp ((lambda - linf) * ((2 : ℝ) - 1)) :=
      Real.one_lt_exp_iff.mpr (by linarith)
    have hrel : gibbsProbS0M M lambda 2 * pinf 1 =
        (gibbsProbS0M M lambda 1 * pinf 2) * Real.exp ((lambda - linf) * ((2 : ℝ) - 1)) := by
      simp only [gibbsProbS0M, h2_mem, h1_mem, ↓reduceIte, pinf]
      unfold gaussWeight
      field_simp [hZM_pos.ne', hZinf_pos.ne']
      rw [mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1; push_cast; ring
    have hp1_pos : 0 < pinf 1 := div_pos (gaussWeight_pos _ _) hZinf_pos
    have hp2_pos : 0 < pinf 2 := div_pos (gaussWeight_pos _ _) hZinf_pos
    have hm1 : pinf 1 * pinf 2 ≤ gibbsProbS0M M lambda 1 * pinf 2 :=
      mul_le_mul_of_nonneg_right hp1_ge hp2_pos.le
    have hm2 : gibbsProbS0M M lambda 1 * pinf 2 <
        (gibbsProbS0M M lambda 1 * pinf 2) * Real.exp ((lambda - linf) * ((2 : ℝ) - 1)) :=
      lt_mul_of_one_lt_right (mul_pos (lt_of_lt_of_le hp1_pos hp1_ge) hp2_pos) hexp_gt
    exact lt_of_mul_lt_mul_right (by linarith [hrel]) hp1_pos.le
  have hsum_lt :
      ∑ i ∈ F0M M, ((M + 1 : ℝ) - (i : ℝ)) * pinf i <
        ∑ i ∈ F0M M, ((M + 1 : ℝ) - (i : ℝ)) * gibbsProbS0M M lambda i := by
    refine Finset.sum_lt_sum (fun i hi ↦ ?_) ⟨2, h2_mem, ?_⟩
    · have hiM : (i : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hi).2
      exact mul_le_mul_of_nonneg_left (hdom i hi) (by linarith)
    · have hM7 : (7 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      exact mul_lt_mul_of_pos_left hstrict2 (by push_cast; linarith)
  linarith

/-! ### Six-cell rational certificates for `Table B.1` (`Appendix B.2`) -/

private theorem log_eighth_ge : -(3 * 0.6931471808 : ℝ) ≤ Real.log (1 / 8) := by
  rw [one_div, Real.log_inv, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  push_cast
  linarith [Real.log_two_lt_d9]

private theorem log_le_of_inv_artanh {m m_ub c u lc L U : ℝ}
    (hm_pos : 0 < m) (hm_le : m ≤ m_ub) (hc : 0 < c) (hlc : lc ≤ Real.log c)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hinv : c * ((1 + u) / (1 - u)) ≤ 1 / m_ub)
    (hL : L ≤ ∑ j ∈ Finset.range 3, 2 * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1))
    (hU : -(lc + L) ≤ U) :
    Real.log m ≤ U := by
  have h1 := log_ge_of_artanh hc hlc hu0 hu1 hinv 3 hL
  rw [one_div, Real.log_inv] at h1
  have h2 := Real.log_le_log hm_pos hm_le
  linarith

private def r4UbY (yb : ℝ) : ℝ :=
  1 - (yb + yb ^ 2 / 2 + yb ^ 3 / 8) / sge1Bound7Y yb

private def s2UbY (ylo : ℝ) : ℝ :=
  (ylo + ylo ^ 2 / 2) / sevenPartY ylo

private theorem cell_rate_bounds_of_params
    {ya yb ylo m1 c1 u1 lc1 L1 U1 m2 c2 u2 lc2 L2 U2 s2_hi : ℝ}
    (hc1 : 0 < c1) (hlc1 : lc1 ≤ Real.log c1)
    (hc2 : 0 < c2) (hlc2 : lc2 ≤ Real.log c2)
    (hylo_eq : ylo = ya - 2 / 25)
    (hya_pos : 0 < ya) (hyb_pos : 0 < yb) (hylo_pos : 0 < ylo) (hyb16 : yb ≤ 16)
    (hm_gap : sge1MeanUb7Y ylo < sevenMeanY ya)
    (hm1_pos : 0 < r4UbY yb * yb * (1 + 1 / sevenPartY ylo))
    (hm1_le : r4UbY yb * yb * (1 + 1 / sevenPartY ylo) ≤ m1)
    (hu1_0 : 0 ≤ u1) (hu1_1 : u1 < 1)
    (hinv1 : c1 * ((1 + u1) / (1 - u1)) ≤ 1 / m1)
    (hL1 : L1 ≤ ∑ j ∈ Finset.range 3, 2 * (1 / (2 * (j : ℝ) + 1)) * u1 ^ (2 * j + 1))
    (hU1 : -(lc1 + L1) ≤ U1)
    (hM7_gt1 : 1 < sevenMeanY ya)
    (htot1 : U1 + 0.6931471803 * (1 - sevenMeanY ya) < -1 / 30)
    (hs2_pos : 0 < s2UbY ylo) (hs2_le : s2UbY ylo ≤ s2_hi) (hs2_lt1 : s2_hi < 1)
    (hm2_le : 1 - s2UbY ylo ≤ m2)
    (hu2_0 : 0 ≤ u2) (hu2_1 : u2 < 1)
    (hinv2 : c2 * ((1 + u2) / (1 - u2)) ≤ 1 / m2)
    (hL2 : L2 ≤ ∑ j ∈ Finset.range 3, 2 * (1 / (2 * (j : ℝ) + 1)) * u2 ^ (2 * j + 1))
    (hU2 : -(lc2 + L2) ≤ U2) (hU2_neg : U2 < 0)
    (hM7b_gt : 0 < sevenMeanY yb - 2 + 2 / (2 + ylo))
    (htot2 : (1 - s2_hi) / s2_hi * U2 +
      (0.6931471808 / 2) * (sevenMeanY yb - 2 + 2 / (2 + ylo)) < -1 / 5) :
    ylo = ya - 2 / 25 ∧ 0 < ya ∧ 0 < yb ∧ yb ≤ 16 ∧
      sge1MeanUb7Y ylo < sevenMeanY ya ∧
      Real.log (r4UbY yb) + Real.log yb + Real.log (1 + 1 / sevenPartY ylo) +
        Real.log 2 * (1 - sevenMeanY ya) < -1 / 30 ∧
      phiInfAux (s2UbY ylo) +
        Real.log 2 / 2 * (sevenMeanY yb - 2 + 2 / (2 + ylo)) < -1 / 5 := by
  have hlog1 := log_le_of_inv_artanh hm1_pos hm1_le hc1 hlc1 hu1_0 hu1_1 hinv1 hL1 hU1
  have hr4_pos : 0 < r4UbY yb := by
    by_contra hnp
    have hle0 : r4UbY yb * yb * (1 + 1 / sevenPartY ylo) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hnp) hyb_pos.le)
        (by have := sevenPartY_pos hylo_pos; positivity)
    linarith
  have h1p_pos : 0 < 1 + 1 / sevenPartY ylo := by
    have := sevenPartY_pos hylo_pos; positivity
  rw [Real.log_mul (mul_pos hr4_pos hyb_pos).ne' h1p_pos.ne',
    Real.log_mul hr4_pos.ne' hyb_pos.ne'] at hlog1
  have hq_lo := Real.log_two_gt_d9
  have hq_hi := Real.log_two_lt_d9
  have hq_term1 : Real.log 2 * (1 - sevenMeanY ya) ≤ 0.6931471803 * (1 - sevenMeanY ya) :=
    mul_le_mul_of_nonpos_right hq_lo.le (by linarith)
  have h1m_s2_pos : 0 < 1 - s2UbY ylo := by linarith
  have hlog2 := log_le_of_inv_artanh h1m_s2_pos hm2_le hc2 hlc2 hu2_0 hu2_1 hinv2 hL2 hU2
  have hratio_ge : (1 - s2_hi) / s2_hi ≤ (1 - s2UbY ylo) / s2UbY ylo := by
    rw [div_le_div_iff₀ (lt_of_lt_of_le hs2_pos hs2_le) hs2_pos]
    nlinarith
  have hg_le : phiInfAux (s2UbY ylo) ≤ (1 - s2_hi) / s2_hi * U2 := by
    unfold phiInfAux
    rw [mul_div_right_comm]
    calc (1 - s2UbY ylo) / s2UbY ylo * Real.log (1 - s2UbY ylo)
        ≤ (1 - s2UbY ylo) / s2UbY ylo * U2 :=
          mul_le_mul_of_nonneg_left hlog2 (div_nonneg h1m_s2_pos.le hs2_pos.le)
      _ ≤ (1 - s2_hi) / s2_hi * U2 :=
          mul_le_mul_of_nonpos_right hratio_ge hU2_neg.le
  have hq_term2 : Real.log 2 / 2 * (sevenMeanY yb - 2 + 2 / (2 + ylo)) ≤
      (0.6931471808 / 2) * (sevenMeanY yb - 2 + 2 / (2 + ylo)) :=
    mul_le_mul_of_nonneg_right (by linarith) hM7b_gt.le
  exact ⟨hylo_eq, hya_pos, hyb_pos, hyb16, hm_gap, by linarith, by linarith⟩

private theorem six_cells_rate_certificate {T : ℝ}
    (hT : T ∈ Set.Icc (sevenMeanY (121 / 25)) (sevenMeanY (209 / 20))) :
    ∃ ya yb ylo : ℝ,
      sevenMeanY ya ≤ T ∧ T ≤ sevenMeanY yb ∧
      ylo = ya - 2 / 25 ∧ 119 / 25 ≤ ylo ∧ 0 < ya ∧ 0 < yb ∧ yb ≤ 16 ∧
      sge1MeanUb7Y ylo < sevenMeanY ya ∧
      Real.log (r4UbY yb) + Real.log yb + Real.log (1 + 1 / sevenPartY ylo) +
        Real.log 2 * (1 - sevenMeanY ya) < -1 / 30 ∧
      phiInfAux (s2UbY ylo) +
        Real.log 2 / 2 * (sevenMeanY yb - 2 + 2 / (2 + ylo)) < -1 / 5 := by
  by_cases h1 : T ≤ sevenMeanY (11 / 2)
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := cell_rate_bounds_of_params
      (ya := 121 / 25) (yb := 11 / 2) (ylo := 119 / 25)
      (m1 := 4609 / 2500) (c1 := 1 / 2) (u1 := 391 / 9609)
      (lc1 := -0.6931471808) (L1 := 4071 / 50000) (U1 := 61173 / 100000)
      (m2 := 3007 / 5000) (c2 := 1) (u2 := 1993 / 8007)
      (lc2 := 0) (L2 := 50847 / 100000) (U2 := -50847 / 100000) (s2_hi := 3987 / 10000)
      (by norm_num) log_half_ge (by norm_num) log_one_ge
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold sge1MeanUb7Y sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold r4UbY sge1Bound7Y sevenPartY; norm_num)
      (by unfold r4UbY sge1Bound7Y sevenPartY; norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold s2UbY sevenPartY; norm_num)
      (by unfold s2UbY sevenPartY; norm_num) (by norm_num)
      (by unfold s2UbY sevenPartY; norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num) (by norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    exact ⟨121 / 25, 11 / 2, 119 / 25, hT.1, h1, e1, le_rfl, e2, e3, e4, e5, e6, e7⟩
  by_cases h2 : T ≤ sevenMeanY (129 / 20)
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := cell_rate_bounds_of_params
      (ya := 11 / 2) (yb := 129 / 20) (ylo := 271 / 50)
      (m1 := 26179 / 10000) (c1 := 1 / 4) (u1 := 13821 / 66179)
      (lc1 := -(2 * 0.6931471808)) (L1 := 42391 / 100000) (U1 := 96239 / 100000)
      (m2 := 6587 / 10000) (c2 := 1) (u2 := 3413 / 16587)
      (lc2 := 0) (L2 := 10437 / 25000) (U2 := -10437 / 25000) (s2_hi := 1707 / 5000)
      (by norm_num) log_quarter_ge (by norm_num) log_one_ge
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold sge1MeanUb7Y sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold r4UbY sge1Bound7Y sevenPartY; norm_num)
      (by unfold r4UbY sge1Bound7Y sevenPartY; norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold s2UbY sevenPartY; norm_num)
      (by unfold s2UbY sevenPartY; norm_num) (by norm_num)
      (by unfold s2UbY sevenPartY; norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num) (by norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    exact ⟨11 / 2, 129 / 20, 271 / 50, (not_le.mp h1).le, h2, e1, by norm_num,
      e2, e3, e4, e5, e6, e7⟩
  by_cases h3 : T ≤ sevenMeanY (153 / 20)
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := cell_rate_bounds_of_params
      (ya := 129 / 20) (yb := 153 / 20) (ylo := 637 / 100)
      (m1 := 37159 / 10000) (c1 := 1 / 4) (u1 := 2841 / 77159)
      (lc1 := -(2 * 0.6931471808)) (L1 := 7367 / 100000) (U1 := 131263 / 100000)
      (m2 := 7257 / 10000) (c2 := 1) (u2 := 2743 / 17257)
      (lc2 := 0) (L2 := 32061 / 100000) (U2 := -32061 / 100000) (s2_hi := 343 / 1250)
      (by norm_num) log_quarter_ge (by norm_num) log_one_ge
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold sge1MeanUb7Y sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold r4UbY sge1Bound7Y sevenPartY; norm_num)
      (by unfold r4UbY sge1Bound7Y sevenPartY; norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold s2UbY sevenPartY; norm_num)
      (by unfold s2UbY sevenPartY; norm_num) (by norm_num)
      (by unfold s2UbY sevenPartY; norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num) (by norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    exact ⟨129 / 20, 153 / 20, 637 / 100, (not_le.mp h2).le, h3, e1, by norm_num,
      e2, e3, e4, e5, e6, e7⟩
  by_cases h4 : T ≤ sevenMeanY (177 / 20)
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := cell_rate_bounds_of_params
      (ya := 153 / 20) (yb := 177 / 20) (ylo := 757 / 100)
      (m1 := 4911 / 1000) (c1 := 1 / 8) (u1 := 3089 / 12911)
      (lc1 := -(3 * 0.6931471808)) (L1 := 9759 / 20000) (U1 := 3183 / 2000)
      (m2 := 79 / 100) (c2 := 1) (u2 := 21 / 179)
      (lc2 := 0) (L2 := 5893 / 25000) (U2 := -5893 / 25000) (s2_hi := 2101 / 10000)
      (by norm_num) log_eighth_ge (by norm_num) log_one_ge
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold sge1MeanUb7Y sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold r4UbY sge1Bound7Y sevenPartY; norm_num)
      (by unfold r4UbY sge1Bound7Y sevenPartY; norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold s2UbY sevenPartY; norm_num)
      (by unfold s2UbY sevenPartY; norm_num) (by norm_num)
      (by unfold s2UbY sevenPartY; norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num) (by norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    exact ⟨153 / 20, 177 / 20, 757 / 100, (not_le.mp h3).le, h4, e1, by norm_num,
      e2, e3, e4, e5, e6, e7⟩
  by_cases h5 : T ≤ sevenMeanY (193 / 20)
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := cell_rate_bounds_of_params
      (ya := 177 / 20) (yb := 193 / 20) (ylo := 877 / 100)
      (m1 := 28727 / 5000) (c1 := 1 / 8) (u1 := 11273 / 68727)
      (lc1 := -(3 * 0.6931471808)) (L1 := 2069 / 6250) (U1 := 174841 / 100000)
      (m2 := 4187 / 5000) (c2 := 1) (u2 := 813 / 9187)
      (lc2 := 0) (L2 := 3549 / 20000) (U2 := -3549 / 20000) (s2_hi := 1627 / 10000)
      (by norm_num) log_eighth_ge (by norm_num) log_one_ge
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold sge1MeanUb7Y sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold r4UbY sge1Bound7Y sevenPartY; norm_num)
      (by unfold r4UbY sge1Bound7Y sevenPartY; norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold s2UbY sevenPartY; norm_num)
      (by unfold s2UbY sevenPartY; norm_num) (by norm_num)
      (by unfold s2UbY sevenPartY; norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num) (by norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    exact ⟨177 / 20, 193 / 20, 877 / 100, (not_le.mp h4).le, h5, e1, by norm_num,
      e2, e3, e4, e5, e6, e7⟩
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := cell_rate_bounds_of_params
      (ya := 193 / 20) (yb := 209 / 20) (ylo := 957 / 100)
      (m1 := 16521 / 2500) (c1 := 1 / 8) (u1 := 3479 / 36521)
      (lc1 := -(3 * 0.6931471808)) (L1 := 19109 / 100000) (U1 := 47209 / 25000)
      (m2 := 8621 / 10000) (c2 := 1) (u2 := 1379 / 18621)
      (lc2 := 0) (L2 := 7419 / 50000) (U2 := -7419 / 50000) (s2_hi := 69 / 500)
      (by norm_num) log_eighth_ge (by norm_num) log_one_ge
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold sge1MeanUb7Y sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold r4UbY sge1Bound7Y sevenPartY; norm_num)
      (by unfold r4UbY sge1Bound7Y sevenPartY; norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold s2UbY sevenPartY; norm_num)
      (by unfold s2UbY sevenPartY; norm_num) (by norm_num)
      (by unfold s2UbY sevenPartY; norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num) (by norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    exact ⟨193 / 20, 209 / 20, 957 / 100, (not_le.mp h5).le, hT.2, e1, by norm_num,
      e2, e3, e4, e5, e6, e7⟩

private theorem phaseTarget_mem_sevenMeanY_range {td : ℝ}
    (htd : td ∈ Set.Icc (0 : ℝ) (207 / 200)) :
    phaseTarget td ∈ Set.Icc (sevenMeanY (121 / 25)) (sevenMeanY (209 / 20)) := by
  have hq0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hqlo := Real.log_two_gt_d9
  have hqhi := Real.log_two_lt_d9
  have h2lo : (288539008 / 100000000 : ℝ) < 2 / Real.log 2 := by
    rw [lt_div_iff₀ hq0]; linarith
  have h2hi : 2 / Real.log 2 < (288539009 / 100000000 : ℝ) := by
    rw [div_lt_iff₀ hq0]; linarith
  have hM_lo : sevenMeanY (121 / 25) < 1 + 288539008 / 100000000 - 207 / 200 := by
    unfold sevenMeanY sevenFirstY sevenPartY; norm_num
  have hM_hi : 1 + 288539009 / 100000000 < sevenMeanY (209 / 20) := by
    unfold sevenMeanY sevenFirstY sevenPartY; norm_num
  unfold phaseTarget
  exact ⟨by linarith [htd.2], by linarith [htd.1]⟩

private theorem small_R_rate_bound_S0M {M : ℕ} (hM1 : 1 ≤ M)
    {lambda T ya yb ylo : ℝ}
    (hTa : sevenMeanY ya ≤ T)
    (hylo_pos : 0 < ylo)
    (hlam_le_yb : lambda ≤ yTilt yb)
    (hZM_ge_P7 : sevenPartY ylo ≤ partitionFn (S0M M) lambda)
    (hcell1 : Real.log (r4UbY yb) + Real.log yb + Real.log (1 + 1 / sevenPartY ylo) +
        Real.log 2 * (1 - sevenMeanY ya) < -1 / 30)
    (z' : ℤ → ℝ)
    (hz' : ∀ i ∈ F0M M, 0 ≤ z' i ∧ z' i ≤ gibbsProbS0M M lambda i) :
    let R' := ∑ i ∈ F0M M, z' i
    0 < R' → R' ≤ r4UbY yb →
    R' * Real.log R' +
        Real.log 2 / 2 * ((∑ i ∈ F0M M, (i : ℝ) * z' i) - T * R') ≤
      -(1 / 60) * R' := by
  intro R' hR'_pos hR'_le
  set ZM := partitionFn (S0M M) lambda
  have hZM_pos := partitionFn_S0M_pos hM1 lambda
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hZ_shift : partitionFn (S0M M) (lambda + Real.log 2) ≤
      Real.exp (lambda + Real.log 2 / 2) * (1 + ZM) := by
    rw [partitionFn_S0M_eq_sum]
    have hterm_sh : ∀ i ∈ F0M M,
        gaussWeight (lambda + Real.log 2) i =
          Real.exp (lambda + Real.log 2 / 2) * gaussWeight lambda (i - 1) := by
      intro i _
      unfold gaussWeight; rw [← Real.exp_add]; push_cast; congr 1; ring
    rw [Finset.sum_congr rfl hterm_sh, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have hbij : ∑ i ∈ F0M M, gaussWeight lambda (i - 1) =
        gaussWeight lambda 0 + ∑ j ∈ Finset.Icc 1 ((M : ℤ) - 1), gaussWeight lambda j := by
      have hsh : ∑ i ∈ F0M M, gaussWeight lambda (i - 1) =
          ∑ j ∈ Finset.Icc 0 ((M : ℤ) - 1), gaussWeight lambda j := by
        refine Finset.sum_bij (fun i _ ↦ i - 1) ?_ ?_ ?_ (fun _ _ ↦ rfl)
        · intro i hi; rw [F0M, Finset.mem_Icc] at hi; rw [Finset.mem_Icc]; omega
        · intro a _ b _ h; omega
        · intro j hj; rw [Finset.mem_Icc] at hj
          refine ⟨j + 1, ?_, by omega⟩
          rw [F0M, Finset.mem_Icc]; omega
      rw [hsh]
      have hdis : Disjoint ({0} : Finset ℤ) (Finset.Icc 1 ((M : ℤ) - 1)) := by
        simp [Finset.mem_Icc]
      have hun : ({0} : Finset ℤ) ∪ Finset.Icc 1 ((M : ℤ) - 1) =
          Finset.Icc 0 ((M : ℤ) - 1) := by
        ext j; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]; omega
      rw [← hun, Finset.sum_union hdis, Finset.sum_singleton]
    rw [hbij]
    have hw0 : gaussWeight lambda 0 = 1 := by unfold gaussWeight; simp
    have hsubM : Finset.Icc 1 ((M : ℤ) - 1) ⊆ F0M M := by
      intro j hj; rw [Finset.mem_Icc] at hj; rw [F0M, Finset.mem_Icc]; omega
    have hsum_le : ∑ j ∈ Finset.Icc 1 ((M : ℤ) - 1), gaussWeight lambda j ≤ ZM := by
      dsimp [ZM]; rw [partitionFn_S0M_eq_sum]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubM fun _ _ _ ↦ (gaussWeight_pos _ _).le
    linarith
  set S_iz := ∑ i ∈ F0M M, (i : ℝ) * z' i
  have hjensen : Real.exp (Real.log 2 / R' * S_iz) ≤
      partitionFn (S0M M) (lambda + Real.log 2) / (R' * ZM) := by
    have hsum1 : 1 ≤ ∑ i ∈ F0M M,
        (z' i / R') * Real.exp (Real.log 2 * (i : ℝ) - Real.log 2 / R' * S_iz) := by
      calc (1 : ℝ)
          = ∑ i ∈ F0M M, (z' i / R') *
              (1 + (Real.log 2 * (i : ℝ) - Real.log 2 / R' * S_iz)) := by
            have h1 : ∑ i ∈ F0M M, z' i / R' = 1 := by
              rw [← Finset.sum_div]; exact div_self hR'_pos.ne'
            have h2 : ∑ i ∈ F0M M, (z' i / R') * (Real.log 2 * (i : ℝ)) =
                Real.log 2 / R' * S_iz := by
              dsimp [S_iz]; rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun _ _ ↦ by ring
            have h3 : ∑ i ∈ F0M M, (z' i / R') * (Real.log 2 / R' * S_iz) =
                Real.log 2 / R' * S_iz := by
              rw [← Finset.sum_mul, h1, one_mul]
            have hexpnd :
                ∑ i ∈ F0M M, (z' i / R') *
                    (1 + (Real.log 2 * (i : ℝ) - Real.log 2 / R' * S_iz)) =
                  (∑ i ∈ F0M M, z' i / R') +
                    (∑ i ∈ F0M M, (z' i / R') * (Real.log 2 * (i : ℝ))) -
                    ∑ i ∈ F0M M, (z' i / R') * (Real.log 2 / R' * S_iz) := by
              rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun _ _ ↦ by ring
            rw [hexpnd, h1, h2, h3]; ring
        _ ≤ ∑ i ∈ F0M M,
              (z' i / R') * Real.exp (Real.log 2 * (i : ℝ) - Real.log 2 / R' * S_iz) := by
            refine Finset.sum_le_sum fun i hi ↦ ?_
            refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (hz' i hi).1 hR'_pos.le)
            linarith [Real.add_one_le_exp (Real.log 2 * (i : ℝ) - Real.log 2 / R' * S_iz)]
    have hmul_exp : Real.exp (Real.log 2 / R' * S_iz) ≤
        (1 / R') * ∑ i ∈ F0M M, z' i * Real.exp (Real.log 2 * (i : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_left hsum1 (Real.exp_pos (Real.log 2 / R' * S_iz)).le
      rw [mul_one] at hm
      refine le_trans hm (le_of_eq ?_)
      calc Real.exp (Real.log 2 / R' * S_iz) *
              ∑ i ∈ F0M M, (z' i / R') *
                Real.exp (Real.log 2 * (i : ℝ) - Real.log 2 / R' * S_iz)
          = ∑ i ∈ F0M M, Real.exp (Real.log 2 / R' * S_iz) *
              ((z' i / R') *
                Real.exp (Real.log 2 * (i : ℝ) - Real.log 2 / R' * S_iz)) :=
            Finset.mul_sum _ _ _
        _ = ∑ i ∈ F0M M, (1 / R') * (z' i * Real.exp (Real.log 2 * (i : ℝ))) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [Real.exp_sub]
            field_simp [(Real.exp_pos _).ne', hR'_pos.ne']
        _ = (1 / R') * ∑ i ∈ F0M M, z' i * Real.exp (Real.log 2 * (i : ℝ)) :=
            (Finset.mul_sum _ _ _).symm
    have hdom_z : ∑ i ∈ F0M M, z' i * Real.exp (Real.log 2 * (i : ℝ)) ≤
        partitionFn (S0M M) (lambda + Real.log 2) / ZM := by
      rw [partitionFn_S0M_eq_sum, Finset.sum_div]
      refine Finset.sum_le_sum fun i hi ↦ ?_
      have hpi := (hz' i hi).2
      simp only [gibbsProbS0M, hi, ↓reduceIte] at hpi
      have hw_eq : gaussWeight lambda i * Real.exp (Real.log 2 * (i : ℝ)) =
          gaussWeight (lambda + Real.log 2) i := by
        unfold gaussWeight; rw [← Real.exp_add]; congr 1; ring
      calc z' i * Real.exp (Real.log 2 * (i : ℝ))
          ≤ (gaussWeight lambda i / ZM) * Real.exp (Real.log 2 * (i : ℝ)) :=
            mul_le_mul_of_nonneg_right hpi (Real.exp_pos _).le
        _ = gaussWeight (lambda + Real.log 2) i / ZM := by
            rw [div_mul_eq_mul_div, hw_eq]
    calc Real.exp (Real.log 2 / R' * S_iz)
        ≤ (1 / R') * (partitionFn (S0M M) (lambda + Real.log 2) / ZM) :=
          le_trans hmul_exp (mul_le_mul_of_nonneg_left hdom_z (by positivity))
      _ = partitionFn (S0M M) (lambda + Real.log 2) / (R' * ZM) := by ring
  have hlog_step := Real.log_le_log (Real.exp_pos _) hjensen
  rw [Real.log_exp] at hlog_step
  have hZsh_pos := partitionFn_S0M_pos hM1 (lambda + Real.log 2)
  have hlog_ratio :
      Real.log (partitionFn (S0M M) (lambda + Real.log 2) / (R' * ZM)) ≤
        -Real.log R' + Real.log 2 + Real.log yb + Real.log (1 + 1 / sevenPartY ylo) := by
    have h1 : partitionFn (S0M M) (lambda + Real.log 2) / (R' * ZM) ≤
        Real.exp (lambda + Real.log 2 / 2) * (1 + 1 / ZM) / R' := by
      rw [div_le_div_iff₀ (mul_pos hR'_pos hZM_pos) hR'_pos]
      have hmul : (1 + 1 / ZM) * ZM = 1 + ZM := by
        rw [add_mul, one_mul, div_mul_cancel₀ _ hZM_pos.ne', add_comm]
      calc partitionFn (S0M M) (lambda + Real.log 2) * R'
          ≤ (Real.exp (lambda + Real.log 2 / 2) * (1 + ZM)) * R' :=
            mul_le_mul_of_nonneg_right hZ_shift hR'_pos.le
        _ = Real.exp (lambda + Real.log 2 / 2) * (1 + 1 / ZM) * (R' * ZM) := by
            rw [← hmul]; ring
    have hpos_rhs : 0 < Real.exp (lambda + Real.log 2 / 2) * (1 + 1 / ZM) :=
      mul_pos (Real.exp_pos _) (by positivity)
    have h2 := Real.log_le_log (div_pos hZsh_pos (mul_pos hR'_pos hZM_pos)) h1
    rw [Real.log_div hpos_rhs.ne' hR'_pos.ne',
      Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp] at h2
    have hlam_ub : lambda + Real.log 2 / 2 ≤ Real.log 2 + Real.log yb := by
      have := hlam_le_yb; unfold yTilt at this; linarith
    have h1ZM_le : 1 + 1 / ZM ≤ 1 + 1 / sevenPartY ylo := by
      have hP7 := sevenPartY_pos hylo_pos
      linarith [one_div_le_one_div_of_le hP7 hZM_ge_P7]
    have hlog_1ZM : Real.log (1 + 1 / ZM) ≤ Real.log (1 + 1 / sevenPartY ylo) :=
      Real.log_le_log (by positivity) h1ZM_le
    linarith
  have hlog_R' : Real.log R' ≤ Real.log (r4UbY yb) := Real.log_le_log hR'_pos hR'_le
  have hqT : Real.log 2 * sevenMeanY ya ≤ Real.log 2 * T :=
    mul_le_mul_of_nonneg_left hTa hq_pos.le
  have hm_half := mul_le_mul_of_nonneg_left (le_trans hlog_step hlog_ratio)
    (half_pos hR'_pos).le
  have hcancel_R : R' / 2 * (Real.log 2 / R' * S_iz) = Real.log 2 / 2 * S_iz := by
    field_simp [hR'_pos.ne']
  rw [hcancel_R] at hm_half
  have hm_R := mul_le_mul_of_nonneg_left hlog_R' (half_pos hR'_pos).le
  have hm_T := mul_le_mul_of_nonneg_left hqT (half_pos hR'_pos).le
  have hcell_mul := mul_lt_mul_of_pos_left hcell1 (half_pos hR'_pos)
  linarith

private theorem mlr_corner_bounds_S0M {M : ℕ} (hM : 7 ≤ M)
    {lambda yb ylo : ℝ}
    (hylo_pos : 0 < ylo) (hyb_pos : 0 < yb) (hyb16 : yb ≤ 16)
    (hlam_gt_y0 : yTilt (119 / 25) < lambda)
    (hlam_gt_ylo : yTilt ylo < lambda)
    (hlam_le_yb : lambda ≤ yTilt yb) :
    let p := gibbsProbS0M M lambda
    let R3 := 1 - p 1 - p 2
    let R4 := 1 - p 1 - p 2 - p 3
    R4 = (∑ i ∈ Finset.Icc 4 (M : ℤ), p i) ∧
      1 / 4 < R4 ∧
      1 - R3 ≤ s2UbY ylo ∧
      R4 ≤ r4UbY yb := by
  intro p R3 R4
  have hM1 : 1 ≤ M := by omega
  set ZM := partitionFn (S0M M) lambda
  have hZM_pos := partitionFn_S0M_pos hM1 lambda
  have h1m : (1 : ℤ) ∈ F0M M := by simp [F0M]; omega
  have h2m : (2 : ℤ) ∈ F0M M := by simp [F0M]; omega
  have h3m : (3 : ℤ) ∈ F0M M := by simp [F0M]; omega
  have hsplit3 : F0M M = ({1, 2, 3} : Finset ℤ) ∪ Finset.Icc 4 (M : ℤ) := by
    ext i
    simp only [F0M, Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hdisj3 : Disjoint ({1, 2, 3} : Finset ℤ) (Finset.Icc 4 (M : ℤ)) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi4
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi1
    simp only [Finset.mem_Icc] at hi4; omega
  have hR4_sum : R4 = ∑ i ∈ Finset.Icc 4 (M : ℤ), p i := by
    have h1 := sum_gibbsProbS0M hM1 lambda
    change ∑ i ∈ F0M M, p i = 1 at h1
    rw [hsplit3, Finset.sum_union hdisj3] at h1
    have hp123 : ∑ i ∈ ({1, 2, 3} : Finset ℤ), p i = p 1 + p 2 + p 3 := by
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      ring
    rw [hp123] at h1
    dsimp [R4]; linarith
  have hmlr_low : ∀ {y : ℝ}, 0 < y → yTilt y ≤ lambda →
      (p 1 + p 2 ≤ s2UbY y) ∧
        (p 1 + p 2 + p 3 ≤ (y + y ^ 2 / 2 + y ^ 3 / 8) / sevenPartY y) := by
    intro y hy hyl
    have hP7 := sevenPartY_pos hy
    obtain ⟨-, -, wy1, wy2, wy3, wy4, wy5, wy6, wy7⟩ := weights_yTilt y hy
    have hsub7 : F07 ⊆ F0M M := by
      intro i hi
      simp only [F07, Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [F0M, Finset.mem_Icc]; omega
    have hZ7_le : ∑ i ∈ F07, gaussWeight lambda i ≤ ZM := by
      dsimp [ZM]; rw [partitionFn_S0M_eq_sum]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub7 fun _ _ _ ↦ (gaussWeight_pos _ _).le
    set d := lambda - yTilt y
    have hd_nn : 0 ≤ d := by dsimp [d]; linarith
    have hw_shift (i : ℤ) :
        gaussWeight lambda i =
          Real.exp (d * (i : ℝ)) * gaussWeight (yTilt y) i := by
      dsimp [d]; unfold gaussWeight; rw [← Real.exp_add]; congr 1; ring
    have e12 : Real.exp (d * (1 : ℤ)) ≤ Real.exp (2 * d) :=
      Real.exp_le_exp.mpr (by push_cast; linarith)
    have e22 : Real.exp (d * (2 : ℤ)) ≤ Real.exp (2 * d) :=
      Real.exp_le_exp.mpr (by push_cast; linarith)
    have e23 : Real.exp (2 * d) ≤ Real.exp (d * (3 : ℤ)) :=
      Real.exp_le_exp.mpr (by push_cast; linarith)
    have e34 : Real.exp (d * (3 : ℤ)) ≤ Real.exp (d * (4 : ℤ)) :=
      Real.exp_le_exp.mpr (by push_cast; linarith)
    have e45 : Real.exp (d * (4 : ℤ)) ≤ Real.exp (d * (5 : ℤ)) :=
      Real.exp_le_exp.mpr (by push_cast; linarith)
    have e56 : Real.exp (d * (5 : ℤ)) ≤ Real.exp (d * (6 : ℤ)) :=
      Real.exp_le_exp.mpr (by push_cast; linarith)
    have e67 : Real.exp (d * (6 : ℤ)) ≤ Real.exp (d * (7 : ℤ)) :=
      Real.exp_le_exp.mpr (by push_cast; linarith)
    have hZ7_expand : ∑ i ∈ F07, gaussWeight lambda i =
        gaussWeight lambda 1 + gaussWeight lambda 2 + gaussWeight lambda 3 +
          gaussWeight lambda 4 + gaussWeight lambda 5 + gaussWeight lambda 6 +
          gaussWeight lambda 7 := sum_F07 _
    constructor
    · unfold s2UbY
      have hp12 : p 1 + p 2 = (gaussWeight lambda 1 + gaussWeight lambda 2) / ZM := by
        simp only [p, gibbsProbS0M, h1m, h2m, ↓reduceIte]; ring
      rw [hp12, div_le_div_iff₀ hZM_pos hP7]
      set A_l := gaussWeight lambda 1 + gaussWeight lambda 2
      set B_l := gaussWeight lambda 3 + gaussWeight lambda 4 + gaussWeight lambda 5 +
        gaussWeight lambda 6 + gaussWeight lambda 7
      set A_y := y + y ^ 2 / 2
      set B_y := y ^ 3 / 8 + y ^ 4 / 64 + y ^ 5 / 1024 + y ^ 6 / 32768 + y ^ 7 / 2097152
      have hAl_ub : A_l ≤ Real.exp (2 * d) * A_y := by
        dsimp [A_l, A_y]; rw [hw_shift 1, hw_shift 2, wy1, wy2, mul_add]
        exact add_le_add
          (mul_le_mul_of_nonneg_right e12 hy.le)
          (mul_le_mul_of_nonneg_right e22 (by positivity))
      have hBl_lb : Real.exp (2 * d) * B_y ≤ B_l := by
        dsimp [B_l, B_y]
        rw [hw_shift 3, hw_shift 4, hw_shift 5, hw_shift 6, hw_shift 7,
          wy3, wy4, wy5, wy6, wy7, mul_add, mul_add, mul_add, mul_add]
        exact add_le_add
          (add_le_add
            (add_le_add
              (add_le_add
                (mul_le_mul_of_nonneg_right e23 (by positivity))
                (mul_le_mul_of_nonneg_right (le_trans e23 e34) (by positivity)))
              (mul_le_mul_of_nonneg_right (le_trans e23 (le_trans e34 e45)) (by positivity)))
            (mul_le_mul_of_nonneg_right
              (le_trans e23 (le_trans e34 (le_trans e45 e56))) (by positivity)))
          (mul_le_mul_of_nonneg_right
            (le_trans e23 (le_trans e34 (le_trans e45 (le_trans e56 e67)))) (by positivity))
      have hcross : A_l * B_y ≤ A_y * B_l := by
        calc A_l * B_y ≤ (Real.exp (2 * d) * A_y) * B_y :=
              mul_le_mul_of_nonneg_right hAl_ub (by dsimp [B_y]; positivity)
          _ = A_y * (Real.exp (2 * d) * B_y) := by ring
          _ ≤ A_y * B_l := mul_le_mul_of_nonneg_left hBl_lb (by dsimp [A_y]; positivity)
      have hP7_eq : sevenPartY y = A_y + B_y := by unfold sevenPartY; dsimp [A_y, B_y]; ring
      have hAB_eq : A_l + B_l = ∑ i ∈ F07, gaussWeight lambda i := by
        rw [hZ7_expand]; dsimp [A_l, B_l]; ring
      have hAB_le : A_l + B_l ≤ ZM := hAB_eq.trans_le hZ7_le
      rw [hP7_eq]
      calc A_l * (A_y + B_y)
          = A_l * A_y + A_l * B_y := mul_add _ _ _
        _ ≤ A_l * A_y + A_y * B_l := add_le_add le_rfl hcross
        _ = A_y * (A_l + B_l) := by ring
        _ ≤ A_y * ZM := mul_le_mul_of_nonneg_left hAB_le (by dsimp [A_y]; positivity)
    · have hp123 : p 1 + p 2 + p 3 =
          (gaussWeight lambda 1 + gaussWeight lambda 2 + gaussWeight lambda 3) / ZM := by
        simp only [p, gibbsProbS0M, h1m, h2m, h3m, ↓reduceIte]; ring
      rw [hp123, div_le_div_iff₀ hZM_pos hP7]
      set A_l := gaussWeight lambda 1 + gaussWeight lambda 2 + gaussWeight lambda 3
      set B_l := gaussWeight lambda 4 + gaussWeight lambda 5 + gaussWeight lambda 6 +
        gaussWeight lambda 7
      set A_y := y + y ^ 2 / 2 + y ^ 3 / 8
      set B_y := y ^ 4 / 64 + y ^ 5 / 1024 + y ^ 6 / 32768 + y ^ 7 / 2097152
      have e13 : Real.exp (d * (1 : ℤ)) ≤ Real.exp (3 * d) :=
        Real.exp_le_exp.mpr (by push_cast; linarith)
      have e23' : Real.exp (d * (2 : ℤ)) ≤ Real.exp (3 * d) :=
        Real.exp_le_exp.mpr (by push_cast; linarith)
      have e33 : Real.exp (d * (3 : ℤ)) ≤ Real.exp (3 * d) :=
        Real.exp_le_exp.mpr (by push_cast; linarith)
      have e34' : Real.exp (3 * d) ≤ Real.exp (d * (4 : ℤ)) :=
        Real.exp_le_exp.mpr (by push_cast; linarith)
      have hAl_ub : A_l ≤ Real.exp (3 * d) * A_y := by
        dsimp [A_l, A_y]; rw [hw_shift 1, hw_shift 2, hw_shift 3, wy1, wy2, wy3, mul_add, mul_add]
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_right e13 hy.le)
            (mul_le_mul_of_nonneg_right e23' (by positivity)))
          (mul_le_mul_of_nonneg_right e33 (by positivity))
      have hBl_lb : Real.exp (3 * d) * B_y ≤ B_l := by
        dsimp [B_l, B_y]
        rw [hw_shift 4, hw_shift 5, hw_shift 6, hw_shift 7, wy4, wy5, wy6, wy7,
          mul_add, mul_add, mul_add]
        exact add_le_add
          (add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_right e34' (by positivity))
              (mul_le_mul_of_nonneg_right (le_trans e34' e45) (by positivity)))
            (mul_le_mul_of_nonneg_right (le_trans e34' (le_trans e45 e56)) (by positivity)))
          (mul_le_mul_of_nonneg_right
            (le_trans e34' (le_trans e45 (le_trans e56 e67))) (by positivity))
      have hcross : A_l * B_y ≤ A_y * B_l := by
        calc A_l * B_y ≤ (Real.exp (3 * d) * A_y) * B_y :=
              mul_le_mul_of_nonneg_right hAl_ub (by dsimp [B_y]; positivity)
          _ = A_y * (Real.exp (3 * d) * B_y) := by ring
          _ ≤ A_y * B_l := mul_le_mul_of_nonneg_left hBl_lb (by dsimp [A_y]; positivity)
      have hP7_eq : sevenPartY y = A_y + B_y := by unfold sevenPartY; dsimp [A_y, B_y]; ring
      have hAB_eq : A_l + B_l = ∑ i ∈ F07, gaussWeight lambda i := by
        rw [hZ7_expand]; dsimp [A_l, B_l]; ring
      have hAB_le : A_l + B_l ≤ ZM := hAB_eq.trans_le hZ7_le
      rw [hP7_eq]
      calc A_l * (A_y + B_y)
          = A_l * A_y + A_l * B_y := mul_add _ _ _
        _ ≤ A_l * A_y + A_y * B_l := add_le_add le_rfl hcross
        _ = A_y * (A_l + B_l) := by ring
        _ ≤ A_y * ZM := mul_le_mul_of_nonneg_left hAB_le (by dsimp [A_y]; positivity)
  have hR4_gt_quarter : 1 / 4 < R4 := by
    have h123 := (hmlr_low (by norm_num : (0 : ℝ) < 119 / 25) hlam_gt_y0.le).2
    have hrat : ((119 / 25 : ℝ) + (119 / 25) ^ 2 / 2 + (119 / 25) ^ 3 / 8) /
        sevenPartY (119 / 25) < 3 / 4 := by
      unfold sevenPartY; norm_num
    dsimp [R4]; linarith
  have h1mR3_le : 1 - R3 ≤ s2UbY ylo := by
    have h12 := (hmlr_low hylo_pos hlam_gt_ylo.le).1
    dsimp [R3]; linarith
  have hR4_le_ub : R4 ≤ r4UbY yb := by
    obtain ⟨-, -, wyb1, wyb2, wyb3, -, -, -, -⟩ := weights_yTilt yb hyb_pos
    set d := yTilt yb - lambda
    have hd_nn : 0 ≤ d := by dsimp [d]; linarith
    have hw_sh (i : ℤ) :
        gaussWeight lambda i =
          Real.exp (-d * (i : ℝ)) * gaussWeight (yTilt yb) i := by
      dsimp [d]; unfold gaussWeight; rw [← Real.exp_add]; congr 1; ring
    set A_l := gaussWeight lambda 1 + gaussWeight lambda 2 + gaussWeight lambda 3
    set B_l := ∑ i ∈ Finset.Icc 4 (M : ℤ), gaussWeight lambda i
    set A_b := yb + yb ^ 2 / 2 + yb ^ 3 / 8
    set B_b := ∑ i ∈ Finset.Icc 4 (M : ℤ), gaussWeight (yTilt yb) i
    have hAl_lb : Real.exp (-3 * d) * A_b ≤ A_l := by
      dsimp [A_l, A_b]; rw [hw_sh 1, hw_sh 2, hw_sh 3, wyb1, wyb2, wyb3, mul_add, mul_add]
      have f1 : Real.exp (-3 * d) ≤ Real.exp (-d * (1 : ℤ)) :=
        Real.exp_le_exp.mpr (by push_cast; linarith)
      have f2 : Real.exp (-3 * d) ≤ Real.exp (-d * (2 : ℤ)) :=
        Real.exp_le_exp.mpr (by push_cast; linarith)
      have f3 : Real.exp (-3 * d) ≤ Real.exp (-d * (3 : ℤ)) :=
        Real.exp_le_exp.mpr (by push_cast; linarith)
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_right f1 hyb_pos.le)
          (mul_le_mul_of_nonneg_right f2 (by positivity)))
        (mul_le_mul_of_nonneg_right f3 (by positivity))
    have hBl_ub : B_l ≤ Real.exp (-3 * d) * B_b := by
      dsimp [B_l, B_b]; rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi ↦ ?_
      rw [hw_sh i]
      have hi4 : (4 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hi).1
      have hdmul := mul_le_mul_of_nonneg_left hi4 hd_nn
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (by linarith)) (gaussWeight_pos _ _).le
    have hcross : B_l * A_b ≤ A_l * B_b := by
      calc B_l * A_b ≤ (Real.exp (-3 * d) * B_b) * A_b :=
            mul_le_mul_of_nonneg_right hBl_ub (by dsimp [A_b]; positivity)
        _ = (Real.exp (-3 * d) * A_b) * B_b := by ring
        _ ≤ A_l * B_b :=
            mul_le_mul_of_nonneg_right hAl_lb
              (Finset.sum_nonneg fun _ _ ↦ (gaussWeight_pos _ _).le)
    have hZM_split : partitionFn (S0M M) lambda = A_l + B_l := by
      rw [partitionFn_S0M_eq_sum, hsplit3, Finset.sum_union hdisj3]
      have h123 : ∑ i ∈ ({1, 2, 3} : Finset ℤ), gaussWeight lambda i = A_l := by
        rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
        dsimp [A_l]; ring
      rw [h123]
    have hZM_b_split : partitionFn (S0M M) (yTilt yb) = A_b + B_b := by
      rw [partitionFn_S0M_eq_sum, hsplit3, Finset.sum_union hdisj3]
      have h123 : ∑ i ∈ ({1, 2, 3} : Finset ℤ), gaussWeight (yTilt yb) i = A_b := by
        rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
          wyb1, wyb2, wyb3]
        dsimp [A_b]; ring
      rw [h123]
    have hZM_b_ub : partitionFn (S0M M) (yTilt yb) ≤ sge1Bound7Y yb := by
      obtain ⟨hZ_eq, _⟩ := sge1_partition_and_first_split hM1 (yTilt yb)
      have hS_yb : Real.exp (2 * yTilt yb - 2 * q) = yb ^ 2 / 2 := by
        unfold yTilt q
        have h1 : 2 * (Real.log 2 / 2 + Real.log yb) - 2 * Real.log 2 =
            2 * Real.log yb - Real.log 2 := by ring
        rw [h1, Real.exp_sub, show (2 : ℝ) * Real.log yb = ((2 : ℕ) : ℝ) * Real.log yb by norm_num,
          Real.exp_nat_mul, Real.exp_log hyb_pos, Real.exp_log two_pos]
      rw [hS_yb] at hZ_eq
      have htail_nn : 0 ≤ ∑' k : ℕ, gaussWeight (yTilt yb) ((M : ℤ) + 1 + (k : ℤ)) :=
        tsum_nonneg fun _ ↦ (gaussWeight_pos _ _).le
      have hub := (sge1_bounds7_at_yTilt hyb_pos hyb16).2.1
      linarith
    have hR4_eq : R4 = B_l / partitionFn (S0M M) lambda := by
      rw [hR4_sum]
      calc ∑ i ∈ Finset.Icc 4 (M : ℤ), p i
          = ∑ i ∈ Finset.Icc 4 (M : ℤ), (gaussWeight lambda i / partitionFn (S0M M) lambda) := by
              refine Finset.sum_congr rfl fun i hi ↦ ?_
              have hiM : i ∈ F0M M := by
                rw [Finset.mem_Icc] at hi; rw [F0M, Finset.mem_Icc]; omega
              simp [p, gibbsProbS0M, hiM]
        _ = B_l / partitionFn (S0M M) lambda := (Finset.sum_div _ _ _).symm
    have hZM_b_pos := partitionFn_S0M_pos hM1 (yTilt yb)
    have hstep1 : B_l / partitionFn (S0M M) lambda ≤ B_b / partitionFn (S0M M) (yTilt yb) := by
      rw [div_le_div_iff₀ hZM_pos hZM_b_pos, hZM_split, hZM_b_split]
      linarith [hcross]
    have hstep2 : B_b / partitionFn (S0M M) (yTilt yb) =
        1 - A_b / partitionFn (S0M M) (yTilt yb) := by
      field_simp [hZM_b_pos.ne']; linarith [hZM_b_split]
    have hstep3 : A_b / sge1Bound7Y yb ≤ A_b / partitionFn (S0M M) (yTilt yb) :=
      div_le_div_of_nonneg_left (by dsimp [A_b]; positivity) hZM_b_pos hZM_b_ub
    rw [hR4_eq]; unfold r4UbY
    linarith
  exact ⟨hR4_sum, hR4_gt_quarter, h1mR3_le, hR4_le_ub⟩

private theorem chord_affine_mul_log {a b x A B : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b)
    (hfa : a * Real.log a + A * a + B ≤ 0)
    (hfb : b * Real.log b + A * b + B ≤ 0) :
    x * Real.log x + A * x + B ≤ 0 := by
  have hba : 0 < b - a := by linarith
  set w1 := (b - x) / (b - a)
  set w2 := (x - a) / (b - a)
  have hw1 : 0 ≤ w1 := div_nonneg (by linarith) hba.le
  have hw2 : 0 ≤ w2 := div_nonneg (by linarith) hba.le
  have hwsum : w1 + w2 = 1 := by
    dsimp [w1, w2]
    rw [← add_div, show (b - x) + (x - a) = b - a by ring, div_self hba.ne']
  have hcomb : w1 * a + w2 * b = x := by
    dsimp [w1, w2]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      show (b - x) * a + (x - a) * b = x * (b - a) by ring,
      mul_div_cancel_right₀ x hba.ne']
  have hconv := (Real.convexOn_mul_log).2
    (show a ∈ Set.Ici (0 : ℝ) from ha)
    (show b ∈ Set.Ici (0 : ℝ) from le_trans ha hab.le) hw1 hw2 hwsum
  simp only [smul_eq_mul] at hconv
  rw [hcomb] at hconv
  have hlin_eq : A * x + B = w1 * (A * a + B) + w2 * (A * b + B) := by
    rw [← hcomb]; linear_combination B * hwsum.symm
  have m1 := mul_le_mul_of_nonneg_left hfa hw1
  have m2 := mul_le_mul_of_nonneg_left hfb hw2
  linarith

private theorem greedy_moment_upper_S0M {M : ℕ} (hM : 7 ≤ M)
    {lambda T : ℝ} (hmean : meanS0M M lambda = T)
    {z : ℤ → ℝ}
    (hz : ∀ i ∈ F0M M, 0 ≤ z i ∧ z i ≤ gibbsProbS0M M lambda i) :
    let p := gibbsProbS0M M lambda
    let R := ∑ i ∈ F0M M, z i
    let R3 := 1 - p 1 - p 2
    (∑ i ∈ F0M M, (i : ℝ) * z i) - T * R ≤
      (T - 3) * (1 - R) + min (1 - R) (1 - R3) + min (1 - R) (p 1) := by
  intro p R R3
  have hM1 : 1 ≤ M := by omega
  have h1m : (1 : ℤ) ∈ F0M M := by simp [F0M]; omega
  have h2m : (2 : ℤ) ∈ F0M M := by simp [F0M]; omega
  have h3m : (3 : ℤ) ∈ F0M M := by simp [F0M]; omega
  have hsplit3 : F0M M = ({1, 2, 3} : Finset ℤ) ∪ Finset.Icc 4 (M : ℤ) := by
    ext i
    simp only [F0M, Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hdisj3 : Disjoint ({1, 2, 3} : Finset ℤ) (Finset.Icc 4 (M : ℤ)) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi4
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi1
    simp only [Finset.mem_Icc] at hi4; omega
  let yv : ℤ → ℝ := fun i ↦ p i - z i
  have hyv_nn : ∀ i ∈ F0M M, 0 ≤ yv i ∧ yv i ≤ p i := fun i hi ↦
    ⟨sub_nonneg.mpr (hz i hi).2, sub_le_self _ (hz i hi).1⟩
  have hyv_sum : ∑ i ∈ F0M M, yv i = 1 - R := by
    dsimp [yv]; rw [Finset.sum_sub_distrib, sum_gibbsProbS0M hM1 lambda]
  have hid_mom : (∑ i ∈ F0M M, (i : ℝ) * z i) - T * R =
      ∑ i ∈ F0M M, (T - (i : ℝ)) * yv i := by
    have htot_mom : ∑ i ∈ F0M M, (i : ℝ) * p i = T := by
      dsimp [p]; rw [sum_mul_gibbsProbS0M, hmean]
    have h1 : ∑ i ∈ F0M M, (T - (i : ℝ)) * yv i =
        T * (∑ i ∈ F0M M, yv i) - ∑ i ∈ F0M M, (i : ℝ) * p i +
          ∑ i ∈ F0M M, (i : ℝ) * z i := by
      dsimp [yv]
      have hs : ∑ i ∈ F0M M, (T - (i : ℝ)) * (p i - z i) =
          ∑ i ∈ F0M M, (T * (p i - z i) - (i : ℝ) * p i + (i : ℝ) * z i) :=
        Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [hs, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [h1, hyv_sum, htot_mom]; ring
  rw [hid_mom, hsplit3, Finset.sum_union hdisj3]
  have h123 : ∑ i ∈ ({1, 2, 3} : Finset ℤ), (T - (i : ℝ)) * yv i =
      (T - 4) * (yv 1 + yv 2 + yv 3) + 3 * yv 1 + 2 * yv 2 + yv 3 := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    push_cast; ring
  have h4M : ∑ i ∈ Finset.Icc 4 (M : ℤ), (T - (i : ℝ)) * yv i ≤
      (T - 4) * ∑ i ∈ Finset.Icc 4 (M : ℤ), yv i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have hi4 : (4 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hi).1
    have hiM : i ∈ F0M M := by
      rw [Finset.mem_Icc] at hi; rw [F0M, Finset.mem_Icc]; omega
    exact mul_le_mul_of_nonneg_right (by linarith) (hyv_nn i hiM).1
  have hsum_split : yv 1 + yv 2 + yv 3 + ∑ i ∈ Finset.Icc 4 (M : ℤ), yv i = 1 - R := by
    rw [← hyv_sum, hsplit3, Finset.sum_union hdisj3]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  have hy4_nn : 0 ≤ ∑ i ∈ Finset.Icc 4 (M : ℤ), yv i :=
    Finset.sum_nonneg fun i hi ↦ (hyv_nn i (by
      rw [Finset.mem_Icc] at hi; rw [F0M, Finset.mem_Icc]; omega)).1
  have hy123_le : yv 1 + yv 2 + yv 3 ≤ 1 - R := by linarith
  have hy12_le : yv 1 + yv 2 ≤ min (1 - R) (1 - R3) := by
    refine le_min ?_ ?_
    · linarith [(hyv_nn 3 h3m).1]
    · dsimp [R3]; linarith [(hyv_nn 1 h1m).2, (hyv_nn 2 h2m).2]
  have hy1_le : yv 1 ≤ min (1 - R) (p 1) := by
    refine le_min ?_ (hyv_nn 1 h1m).2
    linarith [(hyv_nn 2 h2m).1, (hyv_nn 3 h3m).1]
  rw [h123]
  have hcomb4 : (T - 4) * (yv 1 + yv 2 + yv 3) +
      (T - 4) * ∑ i ∈ Finset.Icc 4 (M : ℤ), yv i = (T - 4) * (1 - R) := by
    rw [← mul_add, hsum_split]
  have halg : (T - 4) * (1 - R) + 3 * yv 1 + 2 * yv 2 + yv 3 =
      (T - 3) * (1 - R) + (yv 1 + yv 2 + yv 3 - (1 - R)) +
        (yv 1 + yv 2) + yv 1 := by ring
  linarith [h4M, hcomb4, halg, hy123_le, hy12_le, hy1_le]

private theorem corner_R3_and_piece1_S0M {M : ℕ} (hM : 7 ≤ M)
    {deltaMinus td lambda yb ylo : ℝ}
    (hd_gt : criticalPhaseX0 < deltaMinus)
    (htd_lo : deltaMinus ≤ td) (htd_hi : td ≤ 207 / 200)
    (hmean : meanS0M M lambda = phaseTarget td)
    (hTb : phaseTarget td ≤ sevenMeanY yb)
    (hylo_pos : 0 < ylo)
    (hlam_gt_ylo : yTilt ylo < lambda)
    (h1mR3_le : 1 - (1 - gibbsProbS0M M lambda 1 - gibbsProbS0M M lambda 2) ≤ s2UbY ylo)
    (hR4_gt_quarter :
      1 / 4 < 1 - gibbsProbS0M M lambda 1 - gibbsProbS0M M lambda 2 - gibbsProbS0M M lambda 3)
    (hcell2 : phiInfAux (s2UbY ylo) +
        Real.log 2 / 2 * (sevenMeanY yb - 2 + 2 / (2 + ylo)) < -1 / 5) :
    let p := gibbsProbS0M M lambda
    let T := phaseTarget td
    let c2 := min (1 / 240) (-phiInf deltaMinus)
    let R3 := 1 - p 1 - p 2
    (∀ x : ℝ, 1 - p 1 ≤ x → x < 1 →
      x * Real.log x + Real.log 2 / 2 * ((T - 1) * (1 - x)) + c2 * (1 - x) ≤ 0) ∧
    (R3 * Real.log R3 + Real.log 2 / 2 * ((T - 2) * (1 - R3) + p 1) + c2 * (1 - R3) ≤ 0) := by
  intro p T c2 R3
  have hM1 : 1 ≤ M := by omega
  have hZM_pos := partitionFn_S0M_pos hM1 lambda
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨⟨hx0_pos, _⟩, -, -, -⟩ := criticalPhaseX0_bounds_and_sign
  have h0_le_x0 : (0 : ℝ) ≤ criticalPhaseX0 :=
    le_trans (by norm_num : (0 : ℝ) ≤ 290 / 10000) hx0_pos.le
  have htd_icc : td ∈ Set.Icc (0 : ℝ) (207 / 200) :=
    ⟨le_trans (le_trans h0_le_x0 hd_gt.le) htd_lo, htd_hi⟩
  have h1m : (1 : ℤ) ∈ F0M M := by simp [F0M]; omega
  have h2m : (2 : ℤ) ∈ F0M M := by simp [F0M]; omega
  have h3m : (3 : ℤ) ∈ F0M M := by simp [F0M]; omega
  have hp1_pos : 0 < p 1 := by
    simp only [p, gibbsProbS0M, h1m, ↓reduceIte]; exact div_pos (gaussWeight_pos _ _) hZM_pos
  have hp2_pos : 0 < p 2 := by
    simp only [p, gibbsProbS0M, h2m, ↓reduceIte]; exact div_pos (gaussWeight_pos _ _) hZM_pos
  have hp3_pos : 0 < p 3 := by
    simp only [p, gibbsProbS0M, h3m, ↓reduceIte]; exact div_pos (gaussWeight_pos _ _) hZM_pos
  change 1 - R3 ≤ s2UbY ylo at h1mR3_le
  change 1 / 4 < 1 - p 1 - p 2 - p 3 at hR4_gt_quarter
  have hp1_lt_inf : p 1 < p1Inf td := gibbsProbS0M_one_lt_p1Inf hM htd_hi hmean
  have hp1_lt1 : p 1 < 1 := by linarith [hR4_gt_quarter, hp2_pos, hp3_pos]
  have hphi_td_le : phiInf td ≤ phiInf deltaMinus := by
    rcases eq_or_lt_of_le htd_lo with rfl | hlt
    · exact le_rfl
    · exact (strictAntiOn_phiInf ⟨le_trans h0_le_x0 hd_gt.le, le_trans htd_lo htd_hi⟩
        htd_icc hlt).le
  constructor
  · intro x hx_lo hx_hi
    have h1mx_pos : 0 < 1 - x := by linarith
    have h1mx_mem : 1 - x ∈ Set.Ioo (0 : ℝ) 1 := ⟨h1mx_pos, by linarith⟩
    have hp1_mem : p 1 ∈ Set.Ioo (0 : ℝ) 1 := ⟨hp1_pos, hp1_lt1⟩
    have hpinf_mem : p1Inf td ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [p1Inf_eq_p1AtTilt]; exact p1AtTilt_mem_Ioo _
    have hg_le : phiInfAux (1 - x) ≤ phiInfAux (p 1) := by
      rcases eq_or_lt_of_le (by linarith : 1 - x ≤ p 1) with heq | hlt
      · rw [heq]
      · exact (strictMonoOn_phiInfAux h1mx_mem hp1_mem hlt).le
    have hg_lt : phiInfAux (p 1) < phiInfAux (p1Inf td) :=
      strictMonoOn_phiInfAux hp1_mem hpinf_mem hp1_lt_inf
    have hsum_le : phiInfAux (1 - x) + Real.log 2 / 2 * (T - 1) + c2 ≤ 0 := by
      have hphi_def : phiInf td = phiInfAux (p1Inf td) + Real.log 2 / 2 * (T - 1) := rfl
      have hc2_le : c2 ≤ -phiInf deltaMinus := min_le_right _ _
      linarith
    have hmul := mul_nonpos_of_nonpos_of_nonneg hsum_le h1mx_pos.le
    have hid : (phiInfAux (1 - x) + Real.log 2 / 2 * (T - 1) + c2) * (1 - x) =
        x * Real.log x + Real.log 2 / 2 * ((T - 1) * (1 - x)) + c2 * (1 - x) := by
      unfold phiInfAux
      rw [show 1 - (1 - x) = x by ring, add_mul, add_mul,
        div_mul_cancel₀ _ h1mx_pos.ne']
      ring
    rwa [hid] at hmul
  · have h1mR3_pos : 0 < 1 - R3 := by dsimp [R3]; linarith
    have hs2_lt1 : s2UbY ylo < 1 := by
      have hP7 := sevenPartY_pos hylo_pos
      unfold s2UbY
      rw [div_lt_one hP7]
      unfold sevenPartY
      have hpos_tail : 0 < ylo ^ 3 / 8 + ylo ^ 4 / 64 + ylo ^ 5 / 1024 +
          ylo ^ 6 / 32768 + ylo ^ 7 / 2097152 := by positivity
      linarith
    have h1mR3_mem : 1 - R3 ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨h1mR3_pos, lt_of_le_of_lt h1mR3_le hs2_lt1⟩
    have hs2_mem : s2UbY ylo ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_lt_of_le h1mR3_pos h1mR3_le, hs2_lt1⟩
    have hg_R3 : phiInfAux (1 - R3) ≤ phiInfAux (s2UbY ylo) := by
      rcases eq_or_lt_of_le h1mR3_le with heq | hlt
      · rw [heq]
      · exact (strictMonoOn_phiInfAux h1mR3_mem hs2_mem hlt).le
    have hratio_p1 : p 1 / (1 - R3) < 2 / (2 + ylo) := by
      have h1mR3_eq : 1 - R3 = p 1 + p 2 := by dsimp [R3]; ring
      rw [h1mR3_eq]
      have hp_div : p 1 / (p 1 + p 2) =
          gaussWeight lambda 1 / (gaussWeight lambda 1 + gaussWeight lambda 2) := by
        simp only [p, gibbsProbS0M, h1m, h2m, ↓reduceIte]
        field_simp [hZM_pos.ne']
      rw [hp_div]
      have hw2_eq : gaussWeight lambda 2 =
          Real.exp (lambda - 3 * q / 2) * gaussWeight lambda 1 := by
        unfold gaussWeight q; rw [← Real.exp_add]; push_cast; congr 1; ring
      have hexp_ylo : Real.exp (yTilt ylo - 3 * q / 2) = ylo / 2 := by
        unfold yTilt q
        have h1 : Real.log 2 / 2 + Real.log ylo - 3 * Real.log 2 / 2 =
            Real.log ylo - Real.log 2 := by ring
        rw [h1, Real.exp_sub, Real.exp_log hylo_pos, Real.exp_log two_pos]
      have hexp_gt : ylo / 2 < Real.exp (lambda - 3 * q / 2) := by
        rw [← hexp_ylo]; exact Real.exp_lt_exp.mpr (by linarith)
      have hw1_pos := gaussWeight_pos lambda 1
      have hden_pos : 0 < gaussWeight lambda 1 + gaussWeight lambda 2 :=
        add_pos hw1_pos (gaussWeight_pos lambda 2)
      rw [div_lt_div_iff₀ hden_pos (by linarith), hw2_eq]
      have hm := mul_lt_mul_of_pos_right hexp_gt hw1_pos
      linarith
    have hq_lin : Real.log 2 / 2 * (T - 2 + p 1 / (1 - R3)) ≤
        Real.log 2 / 2 * (sevenMeanY yb - 2 + 2 / (2 + ylo)) :=
      mul_le_mul_of_nonneg_left (by dsimp [T]; linarith) (half_pos hq_pos).le
    have hc2_le : c2 ≤ 1 / 240 := min_le_left _ _
    have hdiv_neg : phiInfAux (1 - R3) +
        Real.log 2 / 2 * (T - 2 + p 1 / (1 - R3)) + c2 ≤ 0 := by linarith
    have hmul := mul_nonpos_of_nonpos_of_nonneg hdiv_neg h1mR3_pos.le
    have hid : (phiInfAux (1 - R3) + Real.log 2 / 2 * (T - 2 + p 1 / (1 - R3)) + c2) *
        (1 - R3) =
        R3 * Real.log R3 + Real.log 2 / 2 * ((T - 2) * (1 - R3) + p 1) + c2 * (1 - R3) := by
      unfold phiInfAux
      have h1 : (Real.log 2 / 2 * (T - 2 + p 1 / (1 - R3))) * (1 - R3) =
          Real.log 2 / 2 * ((T - 2) * (1 - R3) + p 1) := by
        rw [mul_assoc, add_mul, div_mul_cancel₀ _ h1mR3_pos.ne']
      rw [show 1 - (1 - R3) = R3 by ring, add_mul, add_mul,
        div_mul_cancel₀ _ h1mR3_pos.ne', h1]
    rwa [hid] at hmul

/-- **Unconditional unconstrained common-class rate bound (`Lemma 5.2(ii)`, unconstrained case):**
for every `M ≥ 7`, `δ_- ∈ (x₀, 207/200]`, `δ̃ ∈ [δ_-, 207/200]`, tilt `λ` with
`meanS0M M λ = phaseTarget δ̃`, and vector `z : ℤ → ℝ` with `0 ≤ z_i ≤ p^*_i` on
`{1, …, M}` and `R := ∑_{i=1}^M z_i`,
`R log R + (log 2 / 2)(∑_{i=1}^M i z_i - phaseTarget δ̃ · R)`
`≤ -min(1 / 240, -φ_∞(δ_-)) R (1 - R)`. -/
theorem commonClass_rate_bound_S0M {M : ℕ} (hM : 7 ≤ M)
    {deltaMinus td lambda : ℝ}
    (hd_gt : criticalPhaseX0 < deltaMinus)
    (htd_lo : deltaMinus ≤ td) (htd_hi : td ≤ 207 / 200)
    (hmean : meanS0M M lambda = phaseTarget td)
    {z : ℤ → ℝ}
    (hz : ∀ i ∈ F0M M, 0 ≤ z i ∧ z i ≤ gibbsProbS0M M lambda i) :
    let R := ∑ i ∈ F0M M, z i
    R * Real.log R +
        Real.log 2 / 2 * ((∑ i ∈ F0M M, (i : ℝ) * z i) - phaseTarget td * R) ≤
      -min (1 / 240) (-phiInf deltaMinus) * R * (1 - R) := by
  intro R
  have hM1 : 1 ≤ M := by omega
  have hM2 : 2 ≤ M := by omega
  obtain ⟨⟨hx0_pos, _⟩, -, -, hx0_neg⟩ := criticalPhaseX0_bounds_and_sign
  have hdm_ioc : deltaMinus ∈ Set.Ioc criticalPhaseX0 (207 / 200) :=
    ⟨hd_gt, le_trans htd_lo htd_hi⟩
  have hphi_dm_neg : phiInf deltaMinus < 0 := hx0_neg deltaMinus hdm_ioc
  set c2 : ℝ := min (1 / 240) (-phiInf deltaMinus)
  have hc2_pos : 0 < c2 := lt_min (by norm_num) (by linarith only [hphi_dm_neg])
  set p : ℤ → ℝ := gibbsProbS0M M lambda
  set T : ℝ := phaseTarget td
  have hR_nn : 0 ≤ R := Finset.sum_nonneg fun i hi ↦ (hz i hi).1
  have hR_le1 : R ≤ 1 := by
    calc R = ∑ i ∈ F0M M, z i := rfl
      _ ≤ ∑ i ∈ F0M M, p i := Finset.sum_le_sum fun i hi ↦ (hz i hi).2
      _ = 1 := sum_gibbsProbS0M hM1 lambda
  rcases eq_or_lt_of_le hR_nn with hR0 | hR_pos
  · have hz0 : ∀ i ∈ F0M M, z i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i hi ↦ (hz i hi).1)).mp hR0.symm
    have hiz0 : ∑ i ∈ F0M M, (i : ℝ) * z i = 0 :=
      Finset.sum_eq_zero fun i hi ↦ by rw [hz0 i hi, mul_zero]
    rw [← hR0, hiz0]; norm_num
  rcases eq_or_lt_of_le hR_le1 with hR1 | hR_lt1
  · have hdiff0 : ∑ i ∈ F0M M, (p i - z i) = 0 := by
      rw [Finset.sum_sub_distrib, sum_gibbsProbS0M hM1 lambda]
      exact sub_eq_zero.mpr hR1.symm
    have hpz : ∀ i ∈ F0M M, p i - z i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i hi ↦ sub_nonneg.mpr (hz i hi).2)).mp hdiff0
    have hiz_T : ∑ i ∈ F0M M, (i : ℝ) * z i = T := by
      calc ∑ i ∈ F0M M, (i : ℝ) * z i
          = ∑ i ∈ F0M M, (i : ℝ) * p i :=
            Finset.sum_congr rfl fun i hi ↦ by rw [← sub_eq_zero.mp (hpz i hi)]
        _ = T := by rw [sum_mul_gibbsProbS0M, hmean]
    rw [hR1, hiz_T]; norm_num
  have h0_le_x0 : (0 : ℝ) ≤ criticalPhaseX0 :=
    le_trans (by norm_num : (0 : ℝ) ≤ 290 / 10000) hx0_pos.le
  have htd_icc : td ∈ Set.Icc (0 : ℝ) (207 / 200) :=
    ⟨le_trans (le_trans h0_le_x0 hd_gt.le) htd_lo, htd_hi⟩
  obtain ⟨ya, yb, ylo, hTa, hTb, hylo_eq, hylo_ge, hya_pos, hyb_pos, hyb16,
    hm_gap, hcell1, hcell2⟩ :=
    six_cells_rate_certificate (phaseTarget_mem_sevenMeanY_range htd_icc)
  have hylo_pos : 0 < ylo := lt_of_lt_of_le (by norm_num) hylo_ge
  have hya_le_yb : ya ≤ yb := by
    by_contra hgt
    have hlt_yb : yb < ya := not_le.mp hgt
    have ht_lt : yTilt yb < yTilt ya := by
      unfold yTilt; linarith only [Real.log_lt_log hyb_pos hlt_yb]
    have hm_lt := strictMono_meanS0M (M := 7) (by norm_num) ht_lt
    have hm7_eq : ∀ {y : ℝ}, 0 < y → meanS0M 7 (yTilt y) = sevenMeanY y := by
      intro y hy
      have hF : F0M 7 = F07 := by decide
      obtain ⟨-, -, w1, w2, w3, w4, w5, w6, w7⟩ := weights_yTilt y hy
      unfold meanS0M sevenMeanY
      rw [partitionFn_S0M_eq_sum, hF, sum_F07_yTilt y hy, sum_F07,
        w1, w2, w3, w4, w5, w6, w7]
      push_cast; unfold sevenFirstY; ring
    rw [hm7_eq hyb_pos, hm7_eq hya_pos] at hm_lt
    linarith only [hm_lt, hTa, hTb]
  have hylo_le16 : ylo ≤ 16 := by linarith only [hylo_eq, hya_le_yb, hyb16]
  have hlam_gt_ylo : yTilt ylo < lambda := by
    apply (strictMono_meanS0M hM2).lt_iff_lt.mp
    rw [hmean]
    have h1 := meanS0M_lt_sge1Mean hM1 (yTilt ylo)
    have h2 := (sge1_bounds7_at_yTilt hylo_pos hylo_le16).2.2
    linarith only [h1, h2, hm_gap, hTa]
  have hlam_le_yb : lambda ≤ yTilt yb := by
    apply (strictMono_meanS0M hM2).le_iff_le.mp
    rw [hmean]
    exact le_trans hTb (sevenMeanY_le_meanS0M hM hyb_pos)
  have hy0_le_ylo : yTilt (119 / 25) ≤ yTilt ylo := by
    unfold yTilt
    linarith only [Real.log_le_log (by norm_num : (0 : ℝ) < 119 / 25) hylo_ge]
  have hlam_gt_y0 : yTilt (119 / 25) < lambda := lt_of_le_of_lt hy0_le_ylo hlam_gt_ylo
  set ZM := partitionFn (S0M M) lambda
  have hZM_pos := partitionFn_S0M_pos hM1 lambda
  have hZM_ge_P7 : sevenPartY ylo ≤ ZM := by
    dsimp [ZM]
    rw [← sum_F07_yTilt ylo hylo_pos, partitionFn_S0M_eq_sum]
    have hsub : F07 ⊆ F0M M := by
      intro i hi
      simp only [F07, Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [F0M, Finset.mem_Icc]; omega
    calc ∑ i ∈ F07, gaussWeight (yTilt ylo) i
        ≤ ∑ i ∈ F07, gaussWeight lambda i := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          unfold gaussWeight
          apply Real.exp_le_exp.mpr
          have hi_nn : (0 : ℝ) ≤ (i : ℝ) := by
            simp only [F07, Finset.mem_insert, Finset.mem_singleton] at hi
            rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
          have hmul := mul_le_mul_of_nonneg_right hlam_gt_ylo.le hi_nn
          linarith only [hmul]
      _ ≤ ∑ i ∈ F0M M, gaussWeight lambda i :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ ↦ (gaussWeight_pos _ _).le
  have hsmall_R := small_R_rate_bound_S0M hM1 hTa hylo_pos hlam_le_yb hZM_ge_P7 hcell1
  have h1m : (1 : ℤ) ∈ F0M M := by simp [F0M]; omega
  have h2m : (2 : ℤ) ∈ F0M M := by simp [F0M]; omega
  have h3m : (3 : ℤ) ∈ F0M M := by simp [F0M]; omega
  set R3 := 1 - p 1 - p 2
  set R4 := 1 - p 1 - p 2 - p 3
  have hsplit3 : F0M M = ({1, 2, 3} : Finset ℤ) ∪ Finset.Icc 4 (M : ℤ) := by
    ext i
    simp only [F0M, Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hdisj3 : Disjoint ({1, 2, 3} : Finset ℤ) (Finset.Icc 4 (M : ℤ)) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi4
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi1
    simp only [Finset.mem_Icc] at hi4; omega
  obtain ⟨hR4_sum, hR4_gt_quarter, h1mR3_le, hR4_le_ub⟩ :=
    mlr_corner_bounds_S0M hM hylo_pos hyb_pos hyb16 hlam_gt_y0 hlam_gt_ylo hlam_le_yb
  change R4 = ∑ i ∈ Finset.Icc 4 (M : ℤ), p i at hR4_sum
  change 1 / 4 < R4 at hR4_gt_quarter
  change 1 - R3 ≤ s2UbY ylo at h1mR3_le
  change R4 ≤ r4UbY yb at hR4_le_ub
  rcases le_or_gt R R4 with hR_le_R4 | hR_gt_R4
  · have hbound := hsmall_R z hz hR_pos (le_trans hR_le_R4 hR4_le_ub)
    change R * Real.log R +
        Real.log 2 / 2 * ((∑ i ∈ F0M M, (i : ℝ) * z i) - T * R) ≤ -(1 / 60) * R at hbound
    have h1 : -(1 / 60 : ℝ) * R ≤ -(1 / 60) * R * (1 - R) := by
      have hpos1 : 0 ≤ (1 / 60 : ℝ) * (R * R) := by positivity
      have hid1 : -(1 / 60 : ℝ) * R * (1 - R) - (-(1 / 60) * R) =
          (1 / 60) * (R * R) := by ring
      linarith only [hpos1, hid1]
    have hc2_le : c2 ≤ 1 / 60 := le_trans (min_le_left _ _) (by norm_num)
    have h2 : -(1 / 60 : ℝ) * R * (1 - R) ≤ -c2 * R * (1 - R) := by
      have hpos2 : 0 ≤ (1 / 60 - c2) * (R * (1 - R)) :=
        mul_nonneg (sub_nonneg.mpr hc2_le)
          (mul_nonneg hR_pos.le (sub_nonneg.mpr hR_lt1.le))
      have hid2 : -c2 * R * (1 - R) - (-(1 / 60) * R * (1 - R)) =
          (1 / 60 - c2) * (R * (1 - R)) := by ring
      linarith only [hpos2, hid2]
    linarith only [hbound, h1, h2]
  · have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hp1_pos : 0 < p 1 := by
      simp only [p, gibbsProbS0M, h1m, ↓reduceIte]; exact div_pos (gaussWeight_pos _ _) hZM_pos
    have hp2_pos : 0 < p 2 := by
      simp only [p, gibbsProbS0M, h2m, ↓reduceIte]; exact div_pos (gaussWeight_pos _ _) hZM_pos
    have hp3_pos : 0 < p 3 := by
      simp only [p, gibbsProbS0M, h3m, ↓reduceIte]; exact div_pos (gaussWeight_pos _ _) hZM_pos
    let z4 : ℤ → ℝ := fun i ↦ if 4 ≤ i ∧ i ≤ (M : ℤ) then p i else 0
    have hz4_adm : ∀ i ∈ F0M M, 0 ≤ z4 i ∧ z4 i ≤ p i := by
      intro i hi
      have hp_nn : 0 ≤ p i := by
        simp only [p, gibbsProbS0M, hi, ↓reduceIte]
        exact div_nonneg (gaussWeight_pos _ _).le hZM_pos.le
      dsimp [z4]
      split_ifs <;> exact ⟨by positivity, by linarith only [hp_nn]⟩
    have hz4_sum : ∑ i ∈ F0M M, z4 i = R4 := by
      rw [hsplit3, Finset.sum_union hdisj3, hR4_sum]
      have h0 : ∑ i ∈ ({1, 2, 3} : Finset ℤ), z4 i = 0 := by
        refine Finset.sum_eq_zero fun i hi ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        dsimp [z4]; rw [if_neg (by omega)]
      have h4 : ∑ i ∈ Finset.Icc 4 (M : ℤ), z4 i = ∑ i ∈ Finset.Icc 4 (M : ℤ), p i := by
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [Finset.mem_Icc] at hi; dsimp [z4]; rw [if_pos hi]
      rw [h0, h4, zero_add]
    have hz4_mom : (∑ i ∈ F0M M, (i : ℝ) * z4 i) - T * R4 =
        (T - 3) * (1 - R4) + (1 - R3) + p 1 := by
      have htot_mom : ∑ i ∈ F0M M, (i : ℝ) * p i = T := by
        dsimp [p]; rw [sum_mul_gibbsProbS0M, hmean]
      rw [hsplit3, Finset.sum_union hdisj3] at htot_mom ⊢
      have hm_z4_123 : ∑ i ∈ ({1, 2, 3} : Finset ℤ), (i : ℝ) * z4 i = 0 := by
        refine Finset.sum_eq_zero fun i hi ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        dsimp [z4]; rw [if_neg (by omega), mul_zero]
      have hm_z4_4M : ∑ i ∈ Finset.Icc 4 (M : ℤ), (i : ℝ) * z4 i =
          ∑ i ∈ Finset.Icc 4 (M : ℤ), (i : ℝ) * p i := by
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [Finset.mem_Icc] at hi; dsimp [z4]; rw [if_pos hi]
      have hm_p_123 : ∑ i ∈ ({1, 2, 3} : Finset ℤ), (i : ℝ) * p i =
          1 * p 1 + 2 * p 2 + 3 * p 3 := by
        rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
        push_cast; ring
      rw [hm_z4_123, hm_z4_4M, zero_add]
      rw [hm_p_123] at htot_mom
      have hr : (T - 3) * (1 - R4) + (1 - R3) + p 1 =
          -(1 * p 1 + 2 * p 2 + 3 * p 3) + T - T * R4 := by
        dsimp [R4, R3]; ring
      linarith only [htot_mom, hr]
    have hF_R4 :
        R4 * Real.log R4 +
            Real.log 2 / 2 * ((T - 3) * (1 - R4) + (1 - R3) + p 1) +
            c2 * (1 - R4) ≤ 0 := by
      have hb4 := hsmall_R z4 hz4_adm
        (by rw [hz4_sum]; linarith only [hR4_gt_quarter])
        (by rw [hz4_sum]; exact hR4_le_ub)
      change (∑ i ∈ F0M M, z4 i) * Real.log (∑ i ∈ F0M M, z4 i) +
          Real.log 2 / 2 * ((∑ i ∈ F0M M, (i : ℝ) * z4 i) - T * (∑ i ∈ F0M M, z4 i)) ≤
        -(1 / 60) * (∑ i ∈ F0M M, z4 i) at hb4
      rw [hz4_sum, hz4_mom] at hb4
      have hc2_le : c2 ≤ 1 / 240 := min_le_left _ _
      have h1mR4_nn : 0 ≤ 1 - R4 := by
        have hr4 : 1 - R4 = p 1 + p 2 + p 3 := by dsimp [R4]; ring
        linarith only [hr4, hp1_pos, hp2_pos, hp3_pos]
      have hc2_term : c2 * (1 - R4) ≤ 1 / 240 :=
        le_trans (mul_le_mul_of_nonneg_right hc2_le h1mR4_nn)
          (by linarith only [hR4_gt_quarter])
      linarith only [hb4, hc2_term, hR4_gt_quarter]
    have hmom_greedy :
        (∑ i ∈ F0M M, (i : ℝ) * z i) - T * R ≤
          (T - 3) * (1 - R) + min (1 - R) (1 - R3) + min (1 - R) (p 1) :=
      greedy_moment_upper_S0M hM hmean hz
    have hR4_lt_R3 : R4 < R3 := by
      have hr : R3 - R4 = p 3 := by dsimp [R4, R3]; ring
      linarith only [hr, hp3_pos]
    have hR3_lt_1mp1 : R3 < 1 - p 1 := by
      have hr : 1 - p 1 - R3 = p 2 := by dsimp [R3]; ring
      linarith only [hr, hp2_pos]
    obtain ⟨hpiece1, hF_R3⟩ := corner_R3_and_piece1_S0M hM hd_gt htd_lo htd_hi hmean
      hTb hylo_pos hlam_gt_ylo h1mR3_le hR4_gt_quarter hcell2
    change ∀ x : ℝ, 1 - p 1 ≤ x → x < 1 →
      x * Real.log x + Real.log 2 / 2 * ((T - 1) * (1 - x)) + c2 * (1 - x) ≤ 0 at hpiece1
    change R3 * Real.log R3 + Real.log 2 / 2 * ((T - 2) * (1 - R3) + p 1) +
      c2 * (1 - R3) ≤ 0 at hF_R3
    have h1mR_bound :
        R * Real.log R +
            Real.log 2 / 2 * ((∑ i ∈ F0M M, (i : ℝ) * z i) - T * R) ≤
          -c2 * (1 - R) := by
      have hm_step := mul_le_mul_of_nonneg_left hmom_greedy (half_pos hq_pos).le
      rcases le_or_gt (1 - p 1) R with hB1 | hB23
      · have hmin1 : min (1 - R) (1 - R3) = 1 - R :=
          min_eq_left (by linarith only [hB1, hR3_lt_1mp1])
        have hmin2 : min (1 - R) (p 1) = 1 - R := min_eq_left (by linarith only [hB1])
        rw [hmin1, hmin2] at hm_step
        have hp1_x := hpiece1 R hB1 hR_lt1
        have halg_b1 : Real.log 2 / 2 * ((T - 3) * (1 - R) + (1 - R) + (1 - R)) =
            Real.log 2 / 2 * ((T - 1) * (1 - R)) := by ring
        linarith only [hm_step, hp1_x, halg_b1]
      · rcases le_or_gt R3 R with hB2 | hB3
        · have hmin1 : min (1 - R) (1 - R3) = 1 - R := min_eq_left (by linarith only [hB2])
          have hmin2 : min (1 - R) (p 1) = p 1 := min_eq_right (by linarith only [hB23])
          rw [hmin1, hmin2] at hm_step
          have hF_1mp1 := hpiece1 (1 - p 1) le_rfl (by linarith only [hp1_pos])
          have heq1 : (1 - p 1) * Real.log (1 - p 1) +
              (-Real.log 2 / 2 * (T - 2) - c2) * (1 - p 1) +
              (Real.log 2 / 2 * ((T - 2) + p 1) + c2) =
            (1 - p 1) * Real.log (1 - p 1) +
              Real.log 2 / 2 * ((T - 1) * (1 - (1 - p 1))) +
              c2 * (1 - (1 - p 1)) := by ring
          have heq0 : R3 * Real.log R3 +
              (-Real.log 2 / 2 * (T - 2) - c2) * R3 +
              (Real.log 2 / 2 * ((T - 2) + p 1) + c2) =
            R3 * Real.log R3 + Real.log 2 / 2 * ((T - 2) * (1 - R3) + p 1) +
              c2 * (1 - R3) := by ring
          have hch := chord_affine_mul_log
            (a := R3) (b := 1 - p 1) (x := R)
            (A := -Real.log 2 / 2 * (T - 2) - c2)
            (B := Real.log 2 / 2 * ((T - 2) + p 1) + c2)
            (by linarith only [hR4_gt_quarter, hR4_lt_R3]) hR3_lt_1mp1 hB2 hB23.le
            (by linarith only [hF_R3, heq0]) (by linarith only [hF_1mp1, heq1])
          have halg_b2 : (-Real.log 2 / 2 * (T - 2) - c2) * R +
              (Real.log 2 / 2 * ((T - 2) + p 1) + c2) =
            Real.log 2 / 2 * ((T - 3) * (1 - R) + (1 - R) + p 1) + c2 * (1 - R) := by ring
          linarith only [hm_step, hch, halg_b2]
        · have hmin1 : min (1 - R) (1 - R3) = 1 - R3 := min_eq_right (by linarith only [hB3])
          have hmin2 : min (1 - R) (p 1) = p 1 := min_eq_right (by linarith only [hB23])
          rw [hmin1, hmin2] at hm_step
          have heq0 : R4 * Real.log R4 +
              (-Real.log 2 / 2 * (T - 3) - c2) * R4 +
              (Real.log 2 / 2 * ((T - 3) + (1 - R3) + p 1) + c2) =
            R4 * Real.log R4 +
              Real.log 2 / 2 * ((T - 3) * (1 - R4) + (1 - R3) + p 1) +
              c2 * (1 - R4) := by ring
          have heq1 : R3 * Real.log R3 +
              (-Real.log 2 / 2 * (T - 3) - c2) * R3 +
              (Real.log 2 / 2 * ((T - 3) + (1 - R3) + p 1) + c2) =
            R3 * Real.log R3 +
              Real.log 2 / 2 * ((T - 2) * (1 - R3) + p 1) +
              c2 * (1 - R3) := by ring
          have hch := chord_affine_mul_log
            (a := R4) (b := R3) (x := R)
            (A := -Real.log 2 / 2 * (T - 3) - c2)
            (B := Real.log 2 / 2 * ((T - 3) + (1 - R3) + p 1) + c2)
            (by linarith only [hR4_gt_quarter]) hR4_lt_R3 hR_gt_R4.le hB3.le
            (by linarith only [hF_R4, heq0]) (by linarith only [hF_R3, heq1])
          have halg_b3 : (-Real.log 2 / 2 * (T - 3) - c2) * R +
              (Real.log 2 / 2 * ((T - 3) + (1 - R3) + p 1) + c2) =
            Real.log 2 / 2 * ((T - 3) * (1 - R) + (1 - R3) + p 1) + c2 * (1 - R) := by ring
          linarith only [hm_step, hch, halg_b3]
    have hR1_sub : -c2 * (1 - R) ≤ -c2 * R * (1 - R) := by
      have hpos3 : 0 ≤ c2 * ((1 - R) * (1 - R)) :=
        mul_nonneg hc2_pos.le (mul_self_nonneg (1 - R))
      have hid3 : -c2 * R * (1 - R) - (-c2 * (1 - R)) =
          c2 * ((1 - R) * (1 - R)) := by ring
      linarith only [hpos3, hid3]
    linarith only [h1mR_bound, hR1_sub]

/-! ## 3. General-`M` capped common-class rate bound (`Lemma 5.2(ii)`, capped case) -/

/-- **Key convexity lemma (`Appendix B.2, capped case`):**
for every `b ≤ 1 / 2`, `x ↦ x log x + b x (1 - x)` is convex on `[0, 1]`. -/
theorem convexOn_mul_log_add_quad {b : ℝ} (hb : b ≤ 1 / 2) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun x ↦ x * Real.log x + b * x * (1 - x)) := by
  let f : ℝ → ℝ := fun x ↦ x * Real.log x + b * x * (1 - x)
  let df : ℝ → ℝ := fun x ↦ Real.log x + 1 + b * (1 - 2 * x)
  have hdf : ∀ x ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt f (df x) x := by
    intro x hx
    have hd1 : HasDerivAt (fun t : ℝ ↦ t * Real.log t) (Real.log x + 1) x := by
      have h := (hasDerivAt_id' x).mul ((hasDerivAt_id' x).log hx.1.ne')
      exact h.congr_deriv (by field_simp [hx.1.ne'])
    have hd2 : HasDerivAt (fun t : ℝ ↦ b * t * (1 - t)) (b * (1 - 2 * x)) x := by
      have h := ((hasDerivAt_id' x).const_mul b).mul
        ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id' x))
      exact h.congr_deriv (by simp only [Pi.sub_apply]; ring)
    exact hd1.add hd2
  have hddf : ∀ x ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt df (x⁻¹ - 2 * b) x := by
    intro x hx
    have h1 := ((hasDerivAt_id' x).log hx.1.ne').add_const 1
    have h2 : HasDerivAt (fun t : ℝ ↦ b * (1 - 2 * t)) (-2 * b) x := by
      have h := ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id' x).const_mul 2)).const_mul b
      exact h.congr_deriv (by ring)
    exact (h1.add h2).congr_deriv (by ring)
  have hmono_df : MonotoneOn df (Set.Ioc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 1)
    · intro x hx; exact (hddf x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      exact (hddf x ⟨hx.1, hx.2.le⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(hddf x ⟨hx.1, hx.2.le⟩).deriv]
      have hx_inv : 1 ≤ x⁻¹ := by
        rw [le_inv_comm₀ zero_lt_one hx.1]; simpa using hx.2.le
      linarith
  -- Subgradient inequality on `(0, 1]`: `f m + df m * (t - m) ≤ f t` for all `m, t ∈ (0, 1]`
  have hsubgrad : ∀ {m t : ℝ}, m ∈ Set.Ioc (0 : ℝ) 1 → t ∈ Set.Ioc (0 : ℝ) 1 →
      f m + df m * (t - m) ≤ f t := by
    intro m t hm ht
    let g : ℝ → ℝ := fun u ↦ f u - f m - df m * (u - m)
    have hdg : ∀ u ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt g (df u - df m) u := by
      intro u hu
      have hlin : HasDerivAt (fun v ↦ df m * (v - m)) (df m) u := by
        simpa using ((hasDerivAt_id' u).sub_const m).const_mul (df m)
      exact ((hdf u hu).sub_const (f m)).sub hlin
    rcases le_total m t with hmt | htm
    · have hmono_g : MonotoneOn g (Set.Icc m t) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc m t)
        · intro u hu
          exact (hdg u ⟨lt_of_lt_of_le hm.1 hu.1, le_trans hu.2 ht.2⟩).continuousAt.continuousWithinAt
        · intro u hu
          rw [interior_Icc] at hu
          exact (hdg u ⟨lt_trans hm.1 hu.1, le_trans hu.2.le ht.2⟩).differentiableAt.differentiableWithinAt
        · intro u hu
          rw [interior_Icc] at hu
          have hu_ioc : u ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_trans hm.1 hu.1, le_trans hu.2.le ht.2⟩
          rw [(hdg u hu_ioc).deriv]
          linarith [hmono_df hm hu_ioc hu.1.le]
      have h0 : g m ≤ g t := hmono_g ⟨le_rfl, hmt⟩ ⟨hmt, le_rfl⟩ hmt
      dsimp [g] at h0; linarith
    · have hmono_ng : MonotoneOn (-g) (Set.Icc t m) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc t m)
        · intro u hu
          exact (hdg u ⟨lt_of_lt_of_le ht.1 hu.1, le_trans hu.2 hm.2⟩).neg.continuousAt.continuousWithinAt
        · intro u hu
          rw [interior_Icc] at hu
          exact (hdg u ⟨lt_trans ht.1 hu.1, le_trans hu.2.le hm.2⟩).neg.differentiableAt.differentiableWithinAt
        · intro u hu
          rw [interior_Icc] at hu
          have hu_ioc : u ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_trans ht.1 hu.1, le_trans hu.2.le hm.2⟩
          rw [((hdg u hu_ioc).neg).deriv]
          linarith [hmono_df hu_ioc hm hu.2.le]
      have h0 : (-g) t ≤ (-g) m := hmono_ng ⟨le_rfl, htm⟩ ⟨htm, le_rfl⟩ htm
      simp only [Pi.neg_apply, g] at h0; linarith
  -- Extend from `(0, 1]` to `[0, 1]` directly at `0`:
  have hzero_case : ∀ {y w : ℝ}, y ∈ Set.Ioc (0 : ℝ) 1 → 0 ≤ w → w ≤ 1 →
      f (w * y) ≤ w * f y := by
    intro y w hy hw0 hw1
    rcases eq_or_lt_of_le hw0 with rfl | hw_pos
    · dsimp [f]; norm_num
    · have hwy_pos : 0 < w * y := mul_pos hw_pos hy.1
      have hdiff : f (w * y) - w * f y =
          w * y * (Real.log w + b * y * (1 - w)) := by
        dsimp [f]
        rw [Real.log_mul hw_pos.ne' hy.1.ne']
        ring
      have hlog_w : Real.log w ≤ -(1 - w) := by
        have := Real.log_le_sub_one_of_pos hw_pos; linarith
      have hby : b * y * (1 - w) ≤ 1 - w := by
        by_cases hb0 : b ≤ 0
        · have : b * y * (1 - w) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hb0 hy.1.le) (by linarith)
          linarith
        · have hb_pos := not_le.mp hb0
          have h1 : b * y ≤ 1 / 2 := by nlinarith [hy.2]
          nlinarith
      linarith [mul_nonpos_of_nonneg_of_nonpos hwy_pos.le (by linarith : Real.log w + b * y * (1 - w) ≤ 0)]
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy w1 w2 hw1 hw2 hwsum
  simp only [smul_eq_mul]
  change f (w1 * x + w2 * y) ≤ w1 * f x + w2 * f y
  rcases eq_or_lt_of_le hx.1 with rfl | hx_pos
  · rcases eq_or_lt_of_le hy.1 with rfl | hy_pos
    · simp only [mul_zero, add_zero, f]; norm_num
    · have hz := hzero_case ⟨hy_pos, hy.2⟩ hw2 (by linarith)
      have hf0 : f 0 = 0 := by dsimp [f]; norm_num
      rw [mul_zero, zero_add, hf0, mul_zero, zero_add]
      exact hz
  · rcases eq_or_lt_of_le hy.1 with rfl | hy_pos
    · have hz := hzero_case ⟨hx_pos, hx.2⟩ hw1 (by linarith)
      have hf0 : f 0 = 0 := by dsimp [f]; norm_num
      rw [mul_zero, add_zero, hf0, mul_zero, add_zero]
      exact hz
    · set m := w1 * x + w2 * y
      have hm_pos : 0 < m := by
        rcases eq_or_lt_of_le hw1 with rfl | hw1_pos
        · have hw2_pos : 0 < w2 := by linarith
          dsimp [m]; positivity
        · have hwx : 0 < w1 * x := mul_pos hw1_pos hx_pos
          have hwy : 0 ≤ w2 * y := mul_nonneg hw2 hy_pos.le
          dsimp [m]; linarith
      have hm_le1 : m ≤ 1 := by
        have h1 : w1 * x ≤ w1 * 1 := mul_le_mul_of_nonneg_left hx.2 hw1
        have h2 : w2 * y ≤ w2 * 1 := mul_le_mul_of_nonneg_left hy.2 hw2
        dsimp [m]; linarith
      have hsx := mul_le_mul_of_nonneg_left (hsubgrad ⟨hm_pos, hm_le1⟩ ⟨hx_pos, hx.2⟩) hw1
      have hsy := mul_le_mul_of_nonneg_left (hsubgrad ⟨hm_pos, hm_le1⟩ ⟨hy_pos, hy.2⟩) hw2
      have hcomb_m : w1 * (f m + df m * (x - m)) + w2 * (f m + df m * (y - m)) = f m := by
        dsimp [m]
        linear_combination (f m - df m * (w1 * x + w2 * y)) * hwsum
      linarith

/-- **Abstract capped scalar rate lemma (`Lemma 5.2(ii)`, capped reduction):**
whenever the `S \ {1}` tail vector satisfies `-c2_tail · R̃(1 - R̃)` and the first
coordinate `p̄₁ ∈ (0, 1)` satisfies `g(p̄₁) + (log 2 / 2)(T - 1) ≤ -γ < 0` with
`(log 2 / 2)(T - 1) ≥ 1 / 2`, endpoint convexity of `Ψ(r₁)` on `[0, 1]` yields
`-c2_cap · R(1 - R)` across **all** `r₁ ∈ [0, 1]`. -/
theorem capped_rate_bound_of_tail_rate
    {p1Bar T c2_tail gamma c2_cap r1 Rtilde Jtilde : ℝ}
    (hp1_pos : 0 < p1Bar) (hp1_lt1 : p1Bar < 1)
    (hT_half : 1 / 2 ≤ Real.log 2 / 2 * (T - 1))
    (hcap_gap : phiInfAux p1Bar + Real.log 2 / 2 * (T - 1) ≤ -gamma)
    (hc2_nn : 0 ≤ c2_cap)
    (hc2_le_tail : c2_cap ≤ (1 - p1Bar) * c2_tail)
    (hc2_le_gam : c2_cap ≤ gamma)
    (hc2_le_half : c2_cap ≤ 1 / 2)
    (hr1 : r1 ∈ Set.Icc (0 : ℝ) 1)
    (hRt : Rtilde ∈ Set.Icc (0 : ℝ) 1)
    (htail : Rtilde * Real.log Rtilde + Real.log 2 / 2 * Jtilde ≤
      -c2_tail * Rtilde * (1 - Rtilde)) :
    let R := p1Bar * r1 + (1 - p1Bar) * Rtilde
    let J := p1Bar * (T - 1) * (Rtilde - r1) + (1 - p1Bar) * Jtilde
    R * Real.log R + Real.log 2 / 2 * J ≤ -c2_cap * R * (1 - R) := by
  intro R J
  let f : ℝ → ℝ := fun x ↦ x * Real.log x + c2_cap * x * (1 - x)
  have hf_conv := convexOn_mul_log_add_quad hc2_le_half
  set R0 : ℝ := (1 - p1Bar) * Rtilde
  set R1 : ℝ := p1Bar + (1 - p1Bar) * Rtilde
  have h1mp1_pos : 0 < 1 - p1Bar := by linarith
  have hR0_mem : R0 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg h1mp1_pos.le hRt.1, by nlinarith [hRt.2, hp1_pos]⟩
  have hR1_mem : R1 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨add_nonneg hp1_pos.le (mul_nonneg h1mp1_pos.le hRt.1),
      by dsimp [R1]; nlinarith [hRt.2, hp1_lt1]⟩
  have hR_comb : (1 - r1) * R0 + r1 * R1 = R := by
    dsimp [R, R0, R1]; ring
  have hf_R_le : f R ≤ (1 - r1) * f R0 + r1 * f R1 := by
    have hc := hf_conv.2 hR0_mem hR1_mem
      (sub_nonneg.mpr hr1.2) hr1.1 (by ring)
    simp only [smul_eq_mul] at hc
    rwa [hR_comb] at hc
  set J0 : ℝ := p1Bar * (T - 1) * Rtilde + (1 - p1Bar) * Jtilde
  set J1 : ℝ := p1Bar * (T - 1) * (Rtilde - 1) + (1 - p1Bar) * Jtilde
  have hJ_comb : J = (1 - r1) * J0 + r1 * J1 := by
    dsimp [J, J0, J1]; ring
  have hend0 : f R0 + Real.log 2 / 2 * J0 ≤ 0 := by
    rcases eq_or_lt_of_le hRt.1 with hRt0 | hRt_pos
    · rw [← hRt0] at htail
      simp only [zero_mul, zero_add, mul_zero] at htail
      have hJ0 : Real.log 2 / 2 * J0 ≤ 0 := by
        dsimp [J0]; rw [← hRt0]; simp only [mul_zero, zero_add]
        have : Real.log 2 / 2 * ((1 - p1Bar) * Jtilde) =
            (1 - p1Bar) * (Real.log 2 / 2 * Jtilde) := by ring
        rw [this]
        exact mul_nonpos_of_nonneg_of_nonpos h1mp1_pos.le htail
      have hf0 : f R0 = 0 := by dsimp [f, R0]; rw [← hRt0]; norm_num
      linarith
    · have hR0_log : R0 * Real.log R0 =
          (1 - p1Bar) * Rtilde * Real.log (1 - p1Bar) +
            (1 - p1Bar) * (Rtilde * Real.log Rtilde) := by
        dsimp [R0]; rw [Real.log_mul h1mp1_pos.ne' hRt_pos.ne']; ring
      have hcap_mul : (1 - p1Bar) * Real.log (1 - p1Bar) +
          Real.log 2 / 2 * p1Bar * (T - 1) ≤ -gamma * p1Bar := by
        have hm := mul_le_mul_of_nonneg_right hcap_gap hp1_pos.le
        unfold phiInfAux at hm
        have hc : (1 - p1Bar) * Real.log (1 - p1Bar) / p1Bar * p1Bar =
            (1 - p1Bar) * Real.log (1 - p1Bar) := div_mul_cancel₀ _ hp1_pos.ne'
        linarith
      have hlhs0 : R0 * Real.log R0 + Real.log 2 / 2 * J0 ≤
          -gamma * p1Bar * Rtilde - (1 - p1Bar) * c2_tail * Rtilde * (1 - Rtilde) := by
        rw [hR0_log]; dsimp [J0]
        have hm1 := mul_le_mul_of_nonneg_left hcap_mul hRt_pos.le
        have hm2 := mul_le_mul_of_nonneg_left htail h1mp1_pos.le
        nlinarith
      have hrhs0 : c2_cap * R0 * (1 - R0) ≤
          gamma * p1Bar * Rtilde + (1 - p1Bar) * c2_tail * Rtilde * (1 - Rtilde) := by
        have h1mR0 : 1 - R0 = (1 - Rtilde) + p1Bar * Rtilde := by dsimp [R0]; ring
        have hR0_le : R0 ≤ Rtilde := by dsimp [R0]; nlinarith [hp1_pos, hRt_pos]
        have hp1Rt_nn : 0 ≤ p1Bar * Rtilde := by positivity
        have h1mRt_nn : 0 ≤ 1 - Rtilde := sub_nonneg.mpr hRt.2
        have hA : c2_cap * R0 * (1 - Rtilde) ≤
            (1 - p1Bar) * c2_tail * Rtilde * (1 - Rtilde) := by
          calc c2_cap * R0 * (1 - Rtilde)
              ≤ ((1 - p1Bar) * c2_tail) * Rtilde * (1 - Rtilde) := by
                apply mul_le_mul_of_nonneg_right _ h1mRt_nn
                exact mul_le_mul hc2_le_tail hR0_le hR0_mem.1
                  (le_trans hc2_nn hc2_le_tail)
            _ = (1 - p1Bar) * c2_tail * Rtilde * (1 - Rtilde) := by ring
        have hB : c2_cap * R0 * (p1Bar * Rtilde) ≤ gamma * p1Bar * Rtilde := by
          calc c2_cap * R0 * (p1Bar * Rtilde)
              ≤ gamma * 1 * (p1Bar * Rtilde) := by
                apply mul_le_mul_of_nonneg_right _ hp1Rt_nn
                exact mul_le_mul hc2_le_gam hR0_mem.2 hR0_mem.1
                  (le_trans hc2_nn hc2_le_gam)
            _ = gamma * p1Bar * Rtilde := by ring
        rw [h1mR0]
        linarith
      dsimp [f]
      linarith
  have hend1 : f R1 + Real.log 2 / 2 * J1 ≤ 0 := by
    have hmul_log_R1 : R1 * Real.log R1 ≤ (1 - p1Bar) * (Rtilde * Real.log Rtilde) := by
      have hc := (Real.convexOn_mul_log).2
        (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
        (show Rtilde ∈ Set.Ici (0 : ℝ) from hRt.1)
        hp1_pos.le h1mp1_pos.le (by ring)
      simp only [smul_eq_mul, mul_one, Real.log_one, mul_zero, zero_add] at hc
      exact hc
    have hlhs1 : R1 * Real.log R1 + Real.log 2 / 2 * J1 ≤
        -(Real.log 2 / 2 * (T - 1)) * p1Bar * (1 - Rtilde) -
          (1 - p1Bar) * c2_tail * Rtilde * (1 - Rtilde) := by
      dsimp [J1]
      have hm := mul_le_mul_of_nonneg_left htail h1mp1_pos.le
      nlinarith
    have h1mR1 : 1 - R1 = (1 - p1Bar) * (1 - Rtilde) := by dsimp [R1]; ring
    have h1mR1_le : 1 - R1 ≤ 1 - Rtilde := by
      rw [h1mR1]; nlinarith [hp1_pos, sub_nonneg.mpr hRt.2]
    have h1mRt_nn : 0 ≤ 1 - Rtilde := sub_nonneg.mpr hRt.2
    have hC : c2_cap * p1Bar * (1 - R1) ≤
        (Real.log 2 / 2 * (T - 1)) * p1Bar * (1 - Rtilde) := by
      have hct : c2_cap ≤ Real.log 2 / 2 * (T - 1) := le_trans hc2_le_half hT_half
      calc c2_cap * p1Bar * (1 - R1)
          ≤ c2_cap * p1Bar * (1 - Rtilde) :=
            mul_le_mul_of_nonneg_left h1mR1_le (mul_nonneg hc2_nn hp1_pos.le)
        _ ≤ (Real.log 2 / 2 * (T - 1)) * p1Bar * (1 - Rtilde) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hct hp1_pos.le) h1mRt_nn
    have hD : c2_cap * ((1 - p1Bar) * Rtilde) * (1 - R1) ≤
        (1 - p1Bar) * c2_tail * Rtilde * (1 - Rtilde) := by
      rw [h1mR1]
      calc c2_cap * ((1 - p1Bar) * Rtilde) * ((1 - p1Bar) * (1 - Rtilde))
          = (c2_cap * (1 - p1Bar)) * ((1 - p1Bar) * Rtilde * (1 - Rtilde)) := by ring
        _ ≤ ((1 - p1Bar) * c2_tail) * (Rtilde * (1 - Rtilde)) := by
            have hc1 : c2_cap * (1 - p1Bar) ≤ (1 - p1Bar) * c2_tail := by
              nlinarith [hc2_le_tail, hp1_pos, hp1_lt1, hc2_nn]
            have hc2' : (1 - p1Bar) * Rtilde * (1 - Rtilde) ≤ Rtilde * (1 - Rtilde) := by
              nlinarith [hp1_pos, hRt.1, h1mRt_nn]
            exact mul_le_mul hc1 hc2'
              (mul_nonneg (mul_nonneg h1mp1_pos.le hRt.1) h1mRt_nn)
              (le_trans hc2_nn hc2_le_tail)
        _ = (1 - p1Bar) * c2_tail * Rtilde * (1 - Rtilde) := by ring
    dsimp [f, R1] at hC hD ⊢
    linarith
  have hcomb_all : f R + Real.log 2 / 2 * J ≤
      (1 - r1) * (f R0 + Real.log 2 / 2 * J0) + r1 * (f R1 + Real.log 2 / 2 * J1) := by
    rw [hJ_comb]; linarith
  have hrhs_np : (1 - r1) * (f R0 + Real.log 2 / 2 * J0) +
      r1 * (f R1 + Real.log 2 / 2 * J1) ≤ 0 :=
    add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hr1.2) hend0)
      (mul_nonpos_of_nonneg_of_nonpos hr1.1 hend1)
  dsimp [f] at hcomb_all
  linarith

/-- Capped Gibbs vector `p^{cap}_{M, λ̃, p̄₁}` on `S_{0,M} = {1, …, M}` (`M ≥ 8`):
places mass `p̄₁` at `1` and `(1 - p̄₁) · gibbsProbS0M (M - 1) λ̃ (i - 1)` on `{2, …, M}`. -/
def cappedGibbsProbS0M (M : ℕ) (p1Bar lambdaTilde : ℝ) (i : ℤ) : ℝ :=
  if i = 1 then p1Bar
  else if 2 ≤ i ∧ i ≤ (M : ℤ) then (1 - p1Bar) * gibbsProbS0M (M - 1) lambdaTilde (i - 1)
  else 0

/-- **Unconditional capped common-class rate bound (`Lemma 5.2(ii)`, capped case):**
for all `M ≥ 8`, `δ ∈ [0, δ_*]`, `p̄₁ ∈ (0, 1/40]`, `γ > 0` with
`g(p̄₁) + (log 2 / 2)(T_δ - 1) ≤ -γ`, reduced tilt `λ̃` solving
`meanS0M (M - 1) λ̃ = (phaseTarget δ - 1) / (1 - p̄₁)`, and `0 ≤ z ≤ p^{cap}` on
`{1, …, M}` with `R = ∑_{i=1}^M z_i`,
`R log R + (log 2 / 2)(∑_{i=1}^M i z_i - phaseTarget δ · R)`
`≤ -min((39/40) · min(1/240, -φ_∞(1/2)), min(γ, 1/2)) R (1 - R)`. -/
theorem commonClass_capped_rate_bound_S0M {M : ℕ} (hM : 8 ≤ M)
    {delta p1Bar gamma lambdaTilde : ℝ}
    (hd : delta ∈ Set.Icc (0 : ℝ) deltaStar)
    (hp1 : p1Bar ∈ Set.Ioc (0 : ℝ) (1 / 40))
    (hgam : 0 < gamma)
    (hcap_gap : phiInfAux p1Bar + Real.log 2 / 2 * (phaseTarget delta - 1) ≤ -gamma)
    (hmean_red : meanS0M (M - 1) lambdaTilde = (phaseTarget delta - 1) / (1 - p1Bar))
    {z : ℤ → ℝ}
    (hz : ∀ i ∈ F0M M, 0 ≤ z i ∧ z i ≤ cappedGibbsProbS0M M p1Bar lambdaTilde i) :
    let R := ∑ i ∈ F0M M, z i
    let c2_half := min (1 / 240) (-phiInf (1 / 2))
    let c2_cap := min (39 / 40 * c2_half) (min gamma (1 / 2))
    R * Real.log R +
        Real.log 2 / 2 * ((∑ i ∈ F0M M, (i : ℝ) * z i) - phaseTarget delta * R) ≤
      -c2_cap * R * (1 - R) := by
  intro R c2_half c2_cap
  -- Effective unconstrained phase `td_eff ∈ [1/2, 207/200]` solving
  -- `phaseTarget td_eff = (phaseTarget delta - 1) / (1 - p1Bar)`!
  set td_eff : ℝ := 1 + 2 / Real.log 2 - (phaseTarget delta - 1) / (1 - p1Bar)
  have h1mp1_pos : 0 < 1 - p1Bar := by linarith [hp1.2]
  have htarget_eff : phaseTarget td_eff = (phaseTarget delta - 1) / (1 - p1Bar) := by
    dsimp [td_eff]; unfold phaseTarget; ring
  obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
  have htd_eff_lo : (1 / 2 : ℝ) ≤ td_eff := by
    dsimp [td_eff]; unfold phaseTarget; unfold deltaStar at hd
    rw [le_sub_iff_add_le, add_comm (1 / 2 : ℝ), ← le_sub_iff_add_le, div_le_iff₀ h1mp1_pos]
    nlinarith [hp1.1, hp1.2, hd.1, hd.2]
  have htd_eff_hi : td_eff ≤ 207 / 200 := by
    dsimp [td_eff]; unfold phaseTarget; unfold deltaStar at hd
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ h1mp1_pos]
    nlinarith [hp1.1, hp1.2, hd.1, hd.2]
  have hx0_lt_half : criticalPhaseX0 < 1 / 2 :=
    lt_trans criticalPhaseX0_bounds_and_sign.1.2 (by norm_num)
  have hphi_half_neg : phiInf (1 / 2) < 0 :=
    criticalPhaseX0_bounds_and_sign.2.2.2 (1 / 2) ⟨hx0_lt_half, by norm_num⟩
  have hc2_half_pos : 0 < c2_half := lt_min (by norm_num) (by linarith)
  have hc2_cap_pos : 0 < c2_cap :=
    lt_min (by positivity) (lt_min hgam (by norm_num))
  -- Define `r1 := z 1 / p1Bar` and `ztilde j := z (j + 1) / (1 - p1Bar)` on `F0M (M - 1)`
  have h1_memM : (1 : ℤ) ∈ F0M M := by simp [F0M]; omega
  set r1 : ℝ := z 1 / p1Bar
  have hr1_mem : r1 ∈ Set.Icc (0 : ℝ) 1 := by
    have hz1 := hz 1 h1_memM
    simp only [cappedGibbsProbS0M, ↓reduceIte] at hz1
    exact ⟨div_nonneg hz1.1 hp1.1.le, (div_le_one hp1.1).mpr hz1.2⟩
  let ztilde : ℤ → ℝ := fun j ↦ z (j + 1) / (1 - p1Bar)
  have hM7 : 7 ≤ M - 1 := by omega
  have hM_z : ((M - 1 : ℕ) : ℤ) + 1 = (M : ℤ) := by omega
  have hzt_adm : ∀ j ∈ F0M (M - 1),
      0 ≤ ztilde j ∧ ztilde j ≤ gibbsProbS0M (M - 1) lambdaTilde j := by
    intro j hj
    have hj_bounds := Finset.mem_Icc.mp hj
    have hj1_mem : j + 1 ∈ F0M M := by
      rw [F0M, Finset.mem_Icc]; exact ⟨by omega, by omega⟩
    have hzj := hz (j + 1) hj1_mem
    have hj1_ne1 : j + 1 ≠ 1 := by omega
    have hj1_2M : 2 ≤ j + 1 ∧ j + 1 ≤ (M : ℤ) := ⟨by omega, by omega⟩
    simp only [cappedGibbsProbS0M, hj1_ne1, hj1_2M, and_self, ↓reduceIte,
      add_sub_cancel_right] at hzj
    dsimp [ztilde]
    refine ⟨div_nonneg hzj.1 h1mp1_pos.le, (div_le_iff₀ h1mp1_pos).mpr ?_⟩
    linarith
  set Rtilde : ℝ := ∑ j ∈ F0M (M - 1), ztilde j
  have hRt_mem : Rtilde ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨Finset.sum_nonneg fun j hj ↦ (hzt_adm j hj).1, ?_⟩
    calc Rtilde ≤ ∑ j ∈ F0M (M - 1), gibbsProbS0M (M - 1) lambdaTilde j :=
          Finset.sum_le_sum fun j hj ↦ (hzt_adm j hj).2
      _ = 1 := sum_gibbsProbS0M (by omega) lambdaTilde
  -- Apply unconstrained `commonClass_rate_bound_S0M` on `S_{0, M - 1}`!
  have htail_bound := commonClass_rate_bound_S0M hM7 hx0_lt_half htd_eff_lo htd_eff_hi
    (hmean_red.trans htarget_eff.symm) hzt_adm
  rw [htarget_eff] at htail_bound
  -- Split `F0M M` into `{1}` and `{2, ..., M}` (shifted `F0M (M - 1)`)
  have hsplit_sum : ∀ g : ℤ → ℝ,
      ∑ i ∈ F0M M, g i = g 1 + ∑ j ∈ F0M (M - 1), g (j + 1) := by
    intro g
    have hdisj : Disjoint ({1} : Finset ℤ) (Finset.Icc 2 (M : ℤ)) := by
      simp [Finset.mem_Icc]
    have hun : ({1} : Finset ℤ) ∪ Finset.Icc 2 (M : ℤ) = F0M M := by
      ext i; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc, F0M]; omega
    rw [← hun, Finset.sum_union hdisj, Finset.sum_singleton]
    congr 1
    refine (Finset.sum_bij (fun j _ ↦ j + 1) ?_ ?_ ?_ (fun _ _ ↦ rfl)).symm
    · intro j hj; rw [F0M, Finset.mem_Icc] at hj; rw [Finset.mem_Icc]
      exact ⟨by omega, by omega⟩
    · intro a _ b _ h; omega
    · intro i hi; rw [Finset.mem_Icc] at hi
      refine ⟨i - 1, ?_, by omega⟩
      rw [F0M, Finset.mem_Icc]
      exact ⟨by omega, by omega⟩
  have hR_eq : R = p1Bar * r1 + (1 - p1Bar) * Rtilde := by
    dsimp [R, r1, Rtilde, ztilde]
    rw [hsplit_sum, mul_div_cancel₀ _ hp1.1.ne', Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ (mul_div_cancel₀ _ h1mp1_pos.ne').symm
  set Jtilde : ℝ :=
    (∑ j ∈ F0M (M - 1), (j : ℝ) * ztilde j) -
      ((phaseTarget delta - 1) / (1 - p1Bar)) * Rtilde
  have hmom_eq :
      (∑ i ∈ F0M M, (i : ℝ) * z i) - phaseTarget delta * R =
        p1Bar * (phaseTarget delta - 1) * (Rtilde - r1) + (1 - p1Bar) * Jtilde := by
    rw [hsplit_sum (fun i ↦ (i : ℝ) * z i), hR_eq]
    have hz1_eq : (1 : ℝ) * z 1 = p1Bar * r1 := by
      dsimp [r1]; rw [one_mul, mul_div_cancel₀ _ hp1.1.ne']
    have hsh_mom : ∑ j ∈ F0M (M - 1), ((j + 1 : ℤ) : ℝ) * z (j + 1) =
        (1 - p1Bar) * (∑ j ∈ F0M (M - 1), (j : ℝ) * ztilde j) + (1 - p1Bar) * Rtilde := by
      dsimp [Rtilde, ztilde]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hdiv : (1 - p1Bar) * (z (j + 1) / (1 - p1Bar)) = z (j + 1) :=
        mul_div_cancel₀ _ h1mp1_pos.ne'
      push_cast
      calc ((j : ℝ) + 1) * z (j + 1)
          = (j : ℝ) * ((1 - p1Bar) * (z (j + 1) / (1 - p1Bar))) +
              (1 - p1Bar) * (z (j + 1) / (1 - p1Bar)) := by rw [hdiv]; ring
        _ = (1 - p1Bar) * ((j : ℝ) * (z (j + 1) / (1 - p1Bar))) +
              (1 - p1Bar) * (z (j + 1) / (1 - p1Bar)) := by ring
    simp only [Int.cast_one]
    rw [hz1_eq, hsh_mom]
    dsimp [Jtilde]
    have hcanc : (1 - p1Bar) * (((phaseTarget delta - 1) / (1 - p1Bar)) * Rtilde) =
        (phaseTarget delta - 1) * Rtilde := by
      field_simp [h1mp1_pos.ne']
    linarith
  have hT_half : 1 / 2 ≤ Real.log 2 / 2 * (phaseTarget delta - 1) := by
    rw [half_log_two_mul_phaseTarget_sub_one]
    have hq_hi : Real.log 2 < 7 / 10 := lt_trans Real.log_two_lt_d9 (by norm_num)
    unfold deltaStar at hd
    nlinarith [hd.1, hd.2, Real.log_pos one_lt_two]
  have hc2_le_tail : c2_cap ≤ (1 - p1Bar) * c2_half := by
    have h1 : c2_cap ≤ 39 / 40 * c2_half := min_le_left _ _
    have h2 : 39 / 40 ≤ 1 - p1Bar := by linarith [hp1.2]
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 hc2_half_pos.le)
  have hc2_le_gam : c2_cap ≤ gamma :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hc2_le_half : c2_cap ≤ 1 / 2 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  rw [hmom_eq, hR_eq]
  exact capped_rate_bound_of_tail_rate hp1.1 (by linarith [hp1.2]) hT_half hcap_gap
    hc2_cap_pos.le hc2_le_tail hc2_le_gam hc2_le_half hr1_mem hRt_mem htail_bound

/-! ## 4. First-coordinate-capped duals `𝓕_S^{=ϑ}(T)` & full-sequence `1/4` assembly -/

/-- Binary entropy `H_bin(ϑ) = -ϑ log ϑ - (1 - ϑ) log (1 - ϑ)` (`eq:capped-F`). -/
def binEntropy (theta : ℝ) : ℝ :=
  -theta * Real.log theta - (1 - theta) * Real.log (1 - theta)

/-- First-coordinate-capped dual value `𝓕_S^{=ϑ}(T)` from equation `(3.6)` (`eq:capped-F`). -/
def cappedDualValue (S : Set ℤ) (theta T : ℝ) : ℝ :=
  binEntropy theta - Real.log 2 / 2 * theta +
    (1 - theta) * dualValue (S \ {1}) ((T - theta) / (1 - theta))

/-- Compact capped target interval `K_cap = [1 + 2 / log 2 - 1/10, 1 + 2 / log 2 + 1/20]`
from equation `(3.5)` (`eq:t3-9`). -/
def KcapInterval : Set ℝ :=
  Set.Icc (1 + 2 / Real.log 2 - 1 / 10) (1 + 2 / Real.log 2 + 1 / 20)

theorem cappedDualValue_zero (S : Set ℤ) (T : ℝ) :
    cappedDualValue S 0 T = dualValue (S \ {1}) T := by
  unfold cappedDualValue binEntropy
  simp

private theorem shiftSupportOne_Sge1_eq_diff :
    shiftSupportOne Sge1 = Sge1 \ {1} := by
  ext j
  simp only [shiftSupportOne, Sge1, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]
  omega

private theorem shiftSupportOne_S0M_pred_eq_diff {M : ℕ} (hM : 2 ≤ M) :
    shiftSupportOne (S0M (M - 1)) = S0M M \ {1} := by
  ext j
  simp only [shiftSupportOne, S0M, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]
  have : ((M - 1 : ℕ) : ℤ) + 1 = (M : ℤ) := by omega
  omega

/-- **Uniform capped support-limit convergence (`Lemma 3.2(iv)`):**
as `M → ∞`, `𝓕_{S_{0,M}}^{=ϑ}(T) → 𝓕_{S_{≥ 1}}^{=ϑ}(T)` uniformly over all
`ϑ ∈ [0, 1/20]` and `T ∈ K_cap`. -/
theorem tendstoUniformlyOn_cappedDualValue_S0M_Sge1 :
    ∀ eps : ℝ, 0 < eps → ∃ M₁ : ℕ, 8 ≤ M₁ ∧
      ∀ M ≥ M₁, ∀ theta ∈ Set.Icc (0 : ℝ) (1 / 20), ∀ T ∈ KcapInterval,
        0 ≤ cappedDualValue Sge1 theta T - cappedDualValue (S0M M) theta T ∧
          cappedDualValue Sge1 theta T - cappedDualValue (S0M M) theta T < eps := by
  intro eps heps
  obtain ⟨M₀, hM₀7, hconv⟩ := tendstoUniformlyOn_dualValue_S0M_Sge1 eps heps
  refine ⟨M₀ + 1, by omega, fun M hM theta hth T hT ↦ ?_⟩
  have hM2 : 2 ≤ M := by omega
  have hM_pred : M₀ ≤ M - 1 := by omega
  have h1mth_pos : 0 < 1 - theta := by linarith [hth.2]
  set Tred : ℝ := (T - 1) / (1 - theta)
  -- Verify `Tred ∈ [11/4, 4]` for `T ∈ KcapInterval` and `theta ∈ [0, 1/20]`
  obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
  obtain ⟨hT_lo, hT_hi⟩ := hT
  have hTred_icc : Tred ∈ Set.Icc (11 / 4 : ℝ) 4 := by
    dsimp [Tred]
    constructor
    · rw [le_div_iff₀ h1mth_pos]; nlinarith [hth.1, hth.2, hT_lo, h2lo]
    · rw [div_le_iff₀ h1mth_pos]; nlinarith [hth.1, hth.2, hT_hi, h2hi]
  have hTred_25 : Tred ∈ Set.Ioo (2 : ℝ) 5 :=
    ⟨lt_of_lt_of_le (by norm_num) hTred_icc.1, lt_of_le_of_lt hTred_icc.2 (by norm_num)⟩
  have hm4 := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hTred_25)
  have hS4_sub_M : S4 ⊆ S0M (M - 1) := by
    intro i hi
    simp only [S4, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    simp only [S0M, Set.mem_setOf_eq]
    have : (7 : ℤ) ≤ ((M - 1 : ℕ) : ℤ) := by exact_mod_cast (le_trans hM₀7 hM_pred)
    omega
  have harg_eq : (T - theta) / (1 - theta) = Tred + 1 := by
    dsimp [Tred]; field_simp [h1mth_pos.ne']; ring
  have hsh1 := dualValue_shiftSupportOne (S := Sge1) ⟨1, by simp [Sge1]⟩
    (bddBelow_dual S4_subset_Sge1 hm4)
  have hshM := dualValue_shiftSupportOne (S := S0M (M - 1))
    ⟨1, by simp [S0M]; omega⟩ (bddBelow_dual hS4_sub_M hm4)
  rw [shiftSupportOne_Sge1_eq_diff, ← harg_eq] at hsh1
  rw [shiftSupportOne_S0M_pred_eq_diff hM2, ← harg_eq] at hshM
  have hdiff_eq :
      cappedDualValue Sge1 theta T - cappedDualValue (S0M M) theta T =
        (1 - theta) * (dualValue Sge1 Tred - dualValue (S0M (M - 1)) Tred) := by
    unfold cappedDualValue
    rw [hsh1, hshM]
    ring
  obtain ⟨h0, hlt⟩ := hconv (M - 1) hM_pred Tred hTred_icc
  rw [hdiff_eq]
  refine ⟨mul_nonneg h1mth_pos.le h0, ?_⟩
  have h1mth_le1 : 1 - theta ≤ 1 := by linarith [hth.1]
  calc (1 - theta) * (dualValue Sge1 Tred - dualValue (S0M (M - 1)) Tred)
      ≤ 1 * (dualValue Sge1 Tred - dualValue (S0M (M - 1)) Tred) :=
        mul_le_mul_of_nonneg_right h1mth_le1 h0
    _ < eps := by rwa [one_mul]

/-- **Full-sequence finite-phase-cover assembly of the `1/4` Main Theorem (`Section 9`):**
given any `eta > 0` and any finite phase cover `I : Fin K → Set ℝ` of `[0, 1)`
such that on each piece `{n | phaseDelta n ∈ I r}` four threshold sequences
locate the gap within `eta` of `sharpGapConstant` with summable failure tails,
the two-sided failure probability around `sharpGapConstant` is **summable over
all `n : ℕ`** and the two-sided gap probability tends to `1` along **all `n : ℕ`**. -/
theorem fullSequence_sharpGapConstant_of_finite_phase_cover
    {K : ℕ} (I : Fin K → Set ℝ)
    (hcov : ∀ d ∈ Set.Ico (0 : ℝ) 1, ∃ r : Fin K, d ∈ I r)
    (kZetaMinus kCo kChiMinus kCh : Fin K → ℕ → ℕ)
    (a b : Fin K → ℕ → ℝ)
    {eta : ℝ}
    (hLoc : ∀ r : Fin K, ∀ᶠ n : ℕ in atTop, phaseDelta n ∈ I r →
      (sharpGapConstant - eta) * ((n : ℝ) / (Real.log n) ^ 3) ≤
        (kChiMinus r n : ℝ) - (kCo r n : ℝ) - a r n ∧
      (kCh r n : ℝ) + b r n - (kZetaMinus r n : ℝ) ≤
        (sharpGapConstant + eta) * ((n : ℝ) / (Real.log n) ^ 3))
    (hSumChiLow : ∀ r : Fin K,
      Summable (fun n : ℕ ↦ by
        classical
        exact if phaseDelta n ∈ I r then
          (randomGraphMeasure n).real {G | kChiMinus r n < chromaticNumberNat G}ᶜ
        else 0))
    (hSumZetaUp : ∀ r : Fin K,
      Summable (fun n : ℕ ↦ by
        classical
        exact if phaseDelta n ∈ I r then
          (randomGraphMeasure n).real {G | (cochromaticNumber G : ℝ) ≤ (kCo r n : ℝ) + a r n}ᶜ
        else 0))
    (hSumZetaLow : ∀ r : Fin K,
      Summable (fun n : ℕ ↦ by
        classical
        exact if phaseDelta n ∈ I r then
          (randomGraphMeasure n).real {G | kZetaMinus r n < cochromaticNumber G}ᶜ
        else 0))
    (hSumChiUp : ∀ r : Fin K,
      Summable (fun n : ℕ ↦ by
        classical
        exact if phaseDelta n ∈ I r then
          (randomGraphMeasure n).real {G | (chromaticNumberNat G : ℝ) ≤ (kCh r n : ℝ) + b r n}ᶜ
        else 0)) :
    Summable (fun n : ℕ ↦ (randomGraphMeasure n).real
        (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n)ᶜ) ∧
      Tendsto (fun n : ℕ ↦ randomGraphMeasure n
        (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n))
        atTop (nhds 1) := by
  classical
  let pieceFail (r : Fin K) (n : ℕ) : ℝ :=
    if phaseDelta n ∈ I r then
      (randomGraphMeasure n).real {G | kChiMinus r n < chromaticNumberNat G}ᶜ +
      (randomGraphMeasure n).real {G | (cochromaticNumber G : ℝ) ≤ (kCo r n : ℝ) + a r n}ᶜ +
      (randomGraphMeasure n).real {G | kZetaMinus r n < cochromaticNumber G}ᶜ +
      (randomGraphMeasure n).real {G | (chromaticNumberNat G : ℝ) ≤ (kCh r n : ℝ) + b r n}ᶜ
    else 0
  have hsum_piece : ∀ r : Fin K, Summable (pieceFail r) := by
    intro r
    refine ((((hSumChiLow r).add (hSumZetaUp r)).add (hSumZetaLow r)).add (hSumChiUp r)).congr
      fun n ↦ ?_
    dsimp [pieceFail]
    by_cases hm : phaseDelta n ∈ I r <;> simp [hm]
  have hsum_total : Summable (fun n : ℕ ↦ ∑ r : Fin K, pieceFail r n) :=
    summable_sum fun r _ ↦ hsum_piece r
  have hall_loc : ∀ᶠ n : ℕ in atTop, ∀ r : Fin K, phaseDelta n ∈ I r →
      (sharpGapConstant - eta) * ((n : ℝ) / (Real.log n) ^ 3) ≤
        (kChiMinus r n : ℝ) - (kCo r n : ℝ) - a r n ∧
      (kCh r n : ℝ) + b r n - (kZetaMinus r n : ℝ) ≤
        (sharpGapConstant + eta) * ((n : ℝ) / (Real.log n) ^ 3) :=
    eventually_all.mpr hLoc
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hall_loc.and (eventually_ge_atTop 2))
  -- Eventual comparison: for `n ≥ N₀`, target failure probability `≤ ∑ r, pieceFail r n`
  have hev_le : ∀ n ≥ N₀,
      (randomGraphMeasure n).real
          (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n)ᶜ ≤
        ∑ r : Fin K, pieceFail r n := by
    intro n hn
    obtain ⟨hLn_all, hn2⟩ := hN₀ n hn
    obtain ⟨r, hr_mem⟩ := hcov (phaseDelta n) (phaseDelta_mem_Ico n)
    obtain ⟨hL_lo, hL_hi⟩ := hLn_all r hr_mem
    have hsub_compl :
        (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n)ᶜ ⊆
          ({G | kChiMinus r n < chromaticNumberNat G}ᶜ ∪
            {G | (cochromaticNumber G : ℝ) ≤ (kCo r n : ℝ) + a r n}ᶜ) ∪
          ({G | kZetaMinus r n < cochromaticNumber G}ᶜ ∪
            {G | (chromaticNumberNat G : ℝ) ≤ (kCh r n : ℝ) + b r n}ᶜ) := by
      intro G hGnot
      by_contra hAll
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_not] at hAll
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hAll
      apply hGnot
      have h1R : (kChiMinus r n : ℝ) < (chromaticNumberNat G : ℝ) := by exact_mod_cast h1
      have h3R : (kZetaMinus r n : ℝ) < (cochromaticNumber G : ℝ) := by exact_mod_cast h3
      unfold twoSidedGapEvent
      rw [Set.mem_setOf_eq]
      exact ⟨by linarith, by linarith⟩
    have hr_le :
        (randomGraphMeasure n).real
            (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n)ᶜ ≤
          pieceFail r n := by
      dsimp [pieceFail]
      rw [if_pos hr_mem]
      calc (randomGraphMeasure n).real _
          ≤ (randomGraphMeasure n).real _ := measureReal_mono hsub_compl
        _ ≤ (randomGraphMeasure n).real (_ ∪ _) + (randomGraphMeasure n).real (_ ∪ _) :=
            measureReal_union_le _ _
        _ ≤ ((randomGraphMeasure n).real _ + (randomGraphMeasure n).real _) +
              ((randomGraphMeasure n).real _ + (randomGraphMeasure n).real _) :=
            add_le_add (measureReal_union_le _ _) (measureReal_union_le _ _)
        _ = _ := by rw [← add_assoc]
    have hpiece_nn : ∀ s : Fin K, 0 ≤ pieceFail s n := by
      intro s; dsimp [pieceFail]
      split_ifs
      · exact add_nonneg
          (add_nonneg (add_nonneg measureReal_nonneg measureReal_nonneg) measureReal_nonneg)
          measureReal_nonneg
      · exact le_rfl
    exact le_trans hr_le
      (Finset.single_le_sum (fun s _ ↦ hpiece_nn s) (Finset.mem_univ r))
  have hSummableTarget :
      Summable (fun n : ℕ ↦ (randomGraphMeasure n).real
        (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n)ᶜ) := by
    let targetFail : ℕ → ℝ := fun n ↦ (randomGraphMeasure n).real
      (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n)ᶜ
    have hshift : Summable (fun k : ℕ ↦ targetFail (k + N₀)) :=
      Summable.of_nonneg_of_le (fun _ ↦ measureReal_nonneg)
        (fun k ↦ hev_le (k + N₀) (Nat.le_add_left N₀ k))
        (hsum_total.comp_injective (add_left_injective N₀))
    exact (summable_nat_add_iff N₀).mp hshift
  refine ⟨hSummableTarget, ?_⟩
  have hComplZero := hSummableTarget.tendsto_atTop_zero
  have hRealOne : Tendsto (fun n : ℕ ↦ (randomGraphMeasure n).real
      (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n))
      atTop (nhds 1) := by
    have hsub : Tendsto (fun n : ℕ ↦ (1 : ℝ) - (randomGraphMeasure n).real
        (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n)ᶜ)
        atTop (nhds 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hComplZero
    refine hsub.congr fun n ↦ ?_
    rw [probReal_compl_eq_one_sub (Set.toFinite _).measurableSet]
    ring
  have hOfReal : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((randomGraphMeasure n).real
      (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n)))
      atTop (nhds 1) := by
    simpa only [Function.comp_def, ENNReal.ofReal_one] using ENNReal.tendsto_ofReal hRealOne
  refine hOfReal.congr fun n ↦ ?_
  rw [Measure.real]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

end

end Erdos625HP

