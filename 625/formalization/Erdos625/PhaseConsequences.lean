import Erdos625.PhaseAsymptotic
import Erdos625.IndependentSets
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Consequences of the full phase asymptotic

This module derives the manuscript consequences (2.3), (2.4), and (2.9)
from the endpoint-uniform expansion in `PhaseAsymptotic`.  The class sizes
are the actual natural-number floor phase `phaseNat n` and its natural
successor/predecessor operations; no real surrogate is substituted for them.
-/

namespace Erdos625

open Filter Asymptotics Set
open scoped ENNReal Topology

noncomputable section

/-! ## Vanishing of the phase-expansion error -/

theorem tendsto_sq_logLogOrder_div_logOrder_zero :
    Tendsto (fun n : ℕ ↦ logLogOrder n ^ 2 / logOrder n) atTop (𝓝 0) := by
  have h : (fun n : ℕ ↦ logLogOrder n ^ 2) =o[atTop] logOrder := by
    simpa only [logLogOrder, Function.comp_def, id_eq] using
      (Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto tendsto_logOrder_atTop
  exact h.tendsto_div_nhds_zero

theorem phaseExpansionResidual_tendsto_zero :
    Tendsto phaseExpansionResidual atTop (𝓝 0) :=
  phaseExpansionResidual_isBigO.trans_tendsto
    tendsto_sq_logLogOrder_div_logOrder_zero

private theorem tendsto_logLogOrder_div_logOrder_zero :
    Tendsto (fun n : ℕ ↦ logLogOrder n / logOrder n) atTop (𝓝 0) :=
  logLogOrder_isLittleO_logOrder.tendsto_div_nhds_zero

private theorem tendsto_inv_logOrder_zero :
    Tendsto (fun n : ℕ ↦ (logOrder n)⁻¹) atTop (𝓝 0) :=
  tendsto_logOrder_atTop.inv_tendsto_atTop

/-- The phase first moment has logarithmic exponent `phaseDelta`, uniformly
on the full integer-floor sequence. -/
theorem log_mu_phaseNat_div_logOrder_sub_phaseDelta_tendsto_zero :
    Tendsto (fun n : ℕ ↦
      Real.log (mu n (phaseNat n)) / logOrder n - phaseDelta n)
      atTop (𝓝 0) := by
  have hDeltaLog : Tendsto (fun n : ℕ ↦
      phaseDelta n * (logLogOrder n / logOrder n)) atTop (𝓝 0) := by
    apply bdd_le_mul_tendsto_zero
    · exact Filter.Eventually.of_forall phaseDelta_nonneg
    · exact Filter.Eventually.of_forall fun n ↦ (phaseDelta_lt_one n).le
    · exact tendsto_logLogOrder_div_logOrder_zero
  have hLinearLog : Tendsto (fun n : ℕ ↦
      (2 / q - 1 / 2 : ℝ) * (logLogOrder n / logOrder n)) atTop (𝓝 0) :=
    by
      simpa using tendsto_logLogOrder_div_logOrder_zero.const_mul
        (2 / q - 1 / 2 : ℝ)
  obtain ⟨M, hM⟩ := exists_phaseK_abs_bound
  have hK : Tendsto (fun n : ℕ ↦ phaseK (phaseDelta n) / logOrder n)
      atTop (𝓝 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero (b := -M) (B := M)
    · exact Filter.Eventually.of_forall fun n ↦
        (neg_le_of_abs_le (hM _ ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩))
    · exact Filter.Eventually.of_forall fun n ↦
        (le_of_abs_le (hM _ ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩))
    · exact tendsto_logOrder_atTop
  have hResidualDiv : Tendsto (fun n : ℕ ↦
      phaseExpansionResidual n / logOrder n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, zero_mul] using
      phaseExpansionResidual_tendsto_zero.mul tendsto_inv_logOrder_zero
  have hSum := ((hDeltaLog.neg.add hLinearLog).add hK).add hResidualDiv
  simp only [neg_zero, add_zero] at hSum
  refine hSum.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hN : 0 < logOrder n := Real.log_pos (by exact_mod_cast hn)
  simp only [phaseExpansionResidual, phaseExpansionMain]
  field_simp [hN.ne']
  ring

/-! ## Exact logarithmic form of the adjacent-size ratio -/

theorem log_mu_succ_sub_log_mu {n s : ℕ} (hsv : s + 1 ≤ n) :
    Real.log (mu n (s + 1)) - Real.log (mu n s) =
      Real.log ((n - s : ℕ) : ℝ) - Real.log ((s + 1 : ℕ) : ℝ) -
        (s : ℝ) * q := by
  have hsle : s ≤ n := by omega
  have hnsub : (((n - s : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (show n - s ≠ 0 by omega)
  have hsadd : (((s + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hquot : (((n - s : ℕ) : ℝ) / ((s + 1 : ℕ) : ℝ)) ≠ 0 :=
    div_ne_zero hnsub hsadd
  have hpow : (2 : ℝ) ^ s ≠ 0 := by positivity
  calc
    Real.log (mu n (s + 1)) - Real.log (mu n s) =
        Real.log (mu n (s + 1) / mu n s) := by
          rw [Real.log_div (mu_ne_zero hsv) (mu_ne_zero hsle)]
    _ = Real.log
        ((((n - s : ℕ) : ℝ) / ((s + 1 : ℕ) : ℝ)) / (2 : ℝ) ^ s) := by
          rw [mu_succ_div_identity hsle]
    _ = Real.log ((n - s : ℕ) : ℝ) -
          Real.log ((s + 1 : ℕ) : ℝ) - Real.log ((2 : ℝ) ^ s) := by
          rw [Real.log_div hquot hpow, Real.log_div hnsub hsadd]
    _ = Real.log ((n - s : ℕ) : ℝ) -
          Real.log ((s + 1 : ℕ) : ℝ) - (s : ℝ) * q := by
          rw [Real.log_pow]
          rfl

private theorem phaseNat_add_isLittleO_natCast (k : ℕ) :
    (fun n : ℕ ↦ ((phaseNat n + k : ℕ) : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  have hPhase := phaseNat_isTheta_logOrder.1.trans_isLittleO
    logOrder_isLittleO_natCast
  have hConst : (fun _n : ℕ ↦ (k : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
    simpa only [Function.comp_def, id_eq] using
      (isLittleO_const_id_atTop (k : ℝ)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
  exact (hPhase.add hConst).congr_left fun n ↦ by push_cast; rfl

private theorem tendsto_log_natSub_phaseNat_add_div_logOrder_one (k : ℕ)
    (hRange : ∀ᶠ n : ℕ in atTop, phaseNat n + k ≤ n) :
    Tendsto (fun n : ℕ ↦
      Real.log (((n - (phaseNat n + k) : ℕ) : ℝ)) / logOrder n)
      atTop (𝓝 1) := by
  have hSmall := phaseNat_add_isLittleO_natCast k
  have hDiff : (fun n : ℕ ↦
      (((n - (phaseNat n + k) : ℕ) : ℝ)) - (n : ℝ)) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ)) := by
    refine hSmall.neg_left.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hRange] with n hn
    rw [Nat.cast_sub hn]
    push_cast
    ring
  have hEq : (fun n : ℕ ↦ (((n - (phaseNat n + k) : ℕ) : ℝ))) ~[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := hDiff.isEquivalent
  have hLogEq := hEq.log (tendsto_natCast_atTop_atTop (R := ℝ))
  have hDenom : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≠ 0 := by
    simpa only [logOrder] using tendsto_logOrder_atTop.eventually_ne_atTop 0
  have hRatio := (isEquivalent_iff_tendsto_one hDenom).mp hLogEq
  convert hRatio using 1
  ext n
  rfl

private theorem tendsto_log_scaledLogOrder_div_logOrder_zero :
    Tendsto (fun n : ℕ ↦
      Real.log ((2 / q) * logOrder n) / logOrder n) atTop (𝓝 0) := by
  have hScalePos : 0 < (2 / q : ℝ) := div_pos (by norm_num) q_pos
  have hConst : Tendsto (fun n : ℕ ↦
      Real.log (2 / q) * (logOrder n)⁻¹) atTop (𝓝 0) :=
    by
      simpa using tendsto_inv_logOrder_zero.const_mul (Real.log (2 / q))
  have hSum := hConst.add tendsto_logLogOrder_div_logOrder_zero
  simp only [add_zero] at hSum
  refine hSum.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hN : logOrder n ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  rw [Real.log_mul hScalePos.ne' hN]
  simp only [logLogOrder]
  field_simp [hN]

private theorem tendsto_log_phaseNat_add_div_logOrder_zero (k : ℕ) :
    Tendsto (fun n : ℕ ↦
      Real.log (((phaseNat n + k : ℕ) : ℝ)) / logOrder n)
      atTop (𝓝 0) := by
  have hScaleTop : Tendsto (fun n : ℕ ↦ (2 / q) * logOrder n) atTop atTop :=
    tendsto_logOrder_atTop.const_mul_atTop (div_pos (by norm_num) q_pos)
  have hConst : (fun _n : ℕ ↦ (k : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (2 / q) * logOrder n) := by
    simpa only [Function.comp_def, id_eq] using
      (isLittleO_const_id_atTop (k : ℝ)).comp_tendsto hScaleTop
  have hEq : (fun n : ℕ ↦ ((phaseNat n + k : ℕ) : ℝ)) ~[atTop]
      (fun n : ℕ ↦ (2 / q) * logOrder n) := by
    apply (phaseNat_isEquivalent_scaled_logOrder.add_isLittleO hConst).congr_left
    exact Filter.Eventually.of_forall fun n ↦ by push_cast; rfl
  have hLogEq := hEq.log hScaleTop
  have hInvBigO : (fun n : ℕ ↦ (logOrder n)⁻¹) =O[atTop]
      (fun n : ℕ ↦ (logOrder n)⁻¹) := isBigO_refl _ _
  have hDivBigO := hLogEq.isBigO.mul hInvBigO
  have hDivBigO' : (fun n : ℕ ↦
      Real.log (((phaseNat n + k : ℕ) : ℝ)) / logOrder n) =O[atTop]
        (fun n : ℕ ↦ Real.log ((2 / q) * logOrder n) / logOrder n) := by
    exact hDivBigO.congr_left (fun n ↦ by simp [div_eq_mul_inv]) |>.congr_right
      (fun n ↦ by simp [div_eq_mul_inv])
  exact hDivBigO'.trans_tendsto tendsto_log_scaledLogOrder_div_logOrder_zero

private theorem tendsto_phaseNat_add_mul_q_div_logOrder_two (k : ℕ) :
    Tendsto (fun n : ℕ ↦
      (((phaseNat n + k : ℕ) : ℝ) * q) / logOrder n)
      atTop (𝓝 2) := by
  have hScaleTop : Tendsto (fun n : ℕ ↦ (2 / q) * logOrder n) atTop atTop :=
    tendsto_logOrder_atTop.const_mul_atTop (div_pos (by norm_num) q_pos)
  have hDenom : ∀ᶠ n : ℕ in atTop, (2 / q) * logOrder n ≠ 0 :=
    hScaleTop.eventually_ne_atTop 0
  have hRatio := (isEquivalent_iff_tendsto_one hDenom).mp
    phaseNat_isEquivalent_scaled_logOrder
  have hBase : Tendsto (fun n : ℕ ↦
      ((phaseNat n : ℝ) * q) / logOrder n) atTop (𝓝 2) := by
    have h := hRatio.const_mul (2 : ℝ)
    simp only [mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hN : logOrder n ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
    simp only [Pi.div_apply]
    field_simp [hN, q_ne_zero]
  have hConst : Tendsto (fun n : ℕ ↦
      ((k : ℝ) * q) * (logOrder n)⁻¹) atTop (𝓝 0) :=
    by
      simpa using tendsto_inv_logOrder_zero.const_mul ((k : ℝ) * q)
  have h := hBase.add hConst
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hN : logOrder n ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  push_cast
  field_simp [hN]

private theorem tendsto_log_mu_succ_increment_div_logOrder_neg_one (k : ℕ)
    (hRange : ∀ᶠ n : ℕ in atTop, phaseNat n + k + 1 ≤ n) :
    Tendsto (fun n : ℕ ↦
      (Real.log (mu n (phaseNat n + k + 1)) -
        Real.log (mu n (phaseNat n + k))) / logOrder n)
      atTop (𝓝 (-1)) := by
  have hRange' : ∀ᶠ n : ℕ in atTop, phaseNat n + k ≤ n :=
    hRange.mono fun _n hn ↦ by omega
  have hNumerator :=
    tendsto_log_natSub_phaseNat_add_div_logOrder_one k hRange'
  have hClassSize := tendsto_log_phaseNat_add_div_logOrder_zero (k + 1)
  have hPower := tendsto_phaseNat_add_mul_q_div_logOrder_two k
  have h := (hNumerator.sub hClassSize).sub hPower
  norm_num at h
  refine h.congr' ?_
  filter_upwards [hRange, eventually_gt_atTop (1 : ℕ)] with n hn hnOne
  have hN : logOrder n ≠ 0 := (Real.log_pos (by exact_mod_cast hnOne)).ne'
  rw [log_mu_succ_sub_log_mu hn]
  simp only [Nat.add_assoc]
  field_simp [hN]
  push_cast
  ring

/-! ## The two-step upper-tail moment: manuscript equation (2.3) -/

/-- Exact full-sequence form of
`log μ_{α+2} / log n = phaseDelta - 2 + o(1)`.

Here `α = phaseNat n` is the natural-number floor from the manuscript; the
two successors are genuine natural successors. -/
theorem log_mu_phaseNat_add_two_div_logOrder_sub_phaseDelta_add_two_tendsto_zero :
    Tendsto (fun n : ℕ ↦
      Real.log (mu n (phaseNat n + 2)) / logOrder n -
        (phaseDelta n - 2)) atTop (𝓝 0) := by
  have hRangeOne : ∀ᶠ n : ℕ in atTop, phaseNat n + 0 + 1 ≤ n :=
    eventually_phaseNat_add_two_le.mono fun _n hn ↦ by omega
  have hRangeTwo : ∀ᶠ n : ℕ in atTop, phaseNat n + 1 + 1 ≤ n := by
    simpa only [Nat.add_assoc, Nat.zero_add] using eventually_phaseNat_add_two_le
  have hFirst :=
    tendsto_log_mu_succ_increment_div_logOrder_neg_one 0 hRangeOne
  have hSecond :=
    tendsto_log_mu_succ_increment_div_logOrder_neg_one 1 hRangeTwo
  have h :=
    (log_mu_phaseNat_div_logOrder_sub_phaseDelta_tendsto_zero.add
      (hFirst.add_const 1)).add (hSecond.add_const 1)
  norm_num at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hN : logOrder n ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  field_simp [hN]
  ring

/-- Manuscript (2.3), with its full-sequence quantifier: the first moment at
the actual floor phase plus two tends to zero. -/
theorem mu_phaseNat_add_two_tendsto_zero :
    Tendsto (fun n : ℕ ↦ mu n (phaseNat n + 2)) atTop (𝓝 0) := by
  have hErrorLt : ∀ᶠ n : ℕ in atTop,
      Real.log (mu n (phaseNat n + 2)) / logOrder n -
        (phaseDelta n - 2) < (1 / 2 : ℝ) :=
    log_mu_phaseNat_add_two_div_logOrder_sub_phaseDelta_add_two_tendsto_zero.eventually
      (Iio_mem_nhds (by norm_num))
  have hUpper : ∀ᶠ n : ℕ in atTop,
      mu n (phaseNat n + 2) ≤ Real.exp ((-1 / 2 : ℝ) * logOrder n) := by
    filter_upwards [hErrorLt, eventually_phaseNat_add_two_le,
      eventually_gt_atTop (1 : ℕ)] with n hError hRange hn
    have hN : 0 < logOrder n := Real.log_pos (by exact_mod_cast hn)
    have hRatio :
        Real.log (mu n (phaseNat n + 2)) / logOrder n < (-1 / 2 : ℝ) := by
      have hDelta := phaseDelta_lt_one n
      linarith
    have hLog : Real.log (mu n (phaseNat n + 2)) <
        (-1 / 2 : ℝ) * logOrder n := (div_lt_iff₀ hN).mp hRatio
    calc
      mu n (phaseNat n + 2) =
          Real.exp (Real.log (mu n (phaseNat n + 2))) :=
        (Real.exp_log (mu_pos hRange)).symm
      _ ≤ Real.exp ((-1 / 2 : ℝ) * logOrder n) :=
        Real.exp_le_exp.mpr hLog.le
  have hEnvelope : Tendsto (fun n : ℕ ↦
      Real.exp ((-1 / 2 : ℝ) * logOrder n)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_logOrder_atTop.const_mul_atTop_of_neg (by norm_num))
  exact squeeze_zero' (Filter.Eventually.of_forall fun n ↦ mu_nonneg n _)
    hUpper hEnvelope

/-! ## The two-step lower-tail moment: manuscript equation (2.4) -/

theorem log_mu_pred_sub_log_mu {n s : ℕ} (hs : 0 < s) (hsv : s ≤ n) :
    Real.log (mu n (s - 1)) - Real.log (mu n s) =
      Real.log (s : ℝ) - Real.log (((n - s : ℕ) + 1 : ℕ) : ℝ) +
        ((s - 1 : ℕ) : ℝ) * q := by
  have hPred : s - 1 ≤ n := by omega
  have hsCast : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hDenom : ((((n - s : ℕ) + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hFraction : (s : ℝ) / (((n - s : ℕ) + 1 : ℕ) : ℝ) ≠ 0 :=
    div_ne_zero hsCast hDenom
  have hPower : (2 : ℝ) ^ (s - 1) ≠ 0 := by positivity
  calc
    Real.log (mu n (s - 1)) - Real.log (mu n s) =
        Real.log (mu n (s - 1) / mu n s) := by
          rw [Real.log_div (mu_ne_zero hPred) (mu_ne_zero hsv)]
    _ = Real.log (((s : ℝ) / (((n - s : ℕ) + 1 : ℕ) : ℝ)) *
          (2 : ℝ) ^ (s - 1)) := by
      rw [mu_pred_div_identity hs hsv]
    _ = Real.log (s : ℝ) - Real.log (((n - s : ℕ) + 1 : ℕ) : ℝ) +
          Real.log ((2 : ℝ) ^ (s - 1)) := by
      rw [Real.log_mul hFraction hPower, Real.log_div hsCast hDenom]
    _ = Real.log (s : ℝ) - Real.log (((n - s : ℕ) + 1 : ℕ) : ℝ) +
          ((s - 1 : ℕ) : ℝ) * q := by
      rw [Real.log_pow]
      rfl

private theorem eventually_logLogOrder_le_logOrder :
    ∀ᶠ n : ℕ in atTop, logLogOrder n ≤ logOrder n := by
  have hBound :=
    logLogOrder_isLittleO_logOrder.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hOrderNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop (0 : ℝ))
  filter_upwards [hBound, hOrderNonneg] with n hnBound hnNonneg
  calc
    logLogOrder n ≤ |logLogOrder n| := le_abs_self _
    _ = ‖logLogOrder n‖ := (Real.norm_eq_abs _).symm
    _ ≤ (1 / 2 : ℝ) * ‖logOrder n‖ := hnBound
    _ ≤ logOrder n := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnNonneg]
      linarith

private theorem exists_eventually_log_mu_phaseNat_lower :
    ∃ B : ℝ, ∀ᶠ n : ℕ in atTop,
      (2 / q - 1 / 2 : ℝ) * logLogOrder n - B ≤
        Real.log (mu n (phaseNat n)) := by
  obtain ⟨M, hM⟩ := exists_phaseK_abs_bound
  refine ⟨M + 1, ?_⟩
  have hResidualLower : ∀ᶠ n : ℕ in atTop, -1 < phaseExpansionResidual n :=
    phaseExpansionResidual_tendsto_zero.eventually
      (Ioi_mem_nhds (by norm_num))
  filter_upwards [hResidualLower, eventually_logLogOrder_le_logOrder] with
    n hResidual hLogLog
  have hDeltaTerm : 0 ≤
      phaseDelta n * (logOrder n - logLogOrder n) :=
    mul_nonneg (phaseDelta_nonneg n) (sub_nonneg.mpr hLogLog)
  have hKLower : -M ≤ phaseK (phaseDelta n) :=
    neg_le_of_abs_le
      (hM _ ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩)
  simp only [phaseExpansionResidual, phaseExpansionMain] at hResidual
  linarith

private theorem phaseNat_mul_q_identity {n : ℕ} (hn : PhaseDomain n) :
    (phaseNat n : ℝ) * q =
      2 * logOrder n - 2 * logLogOrder n + 2 * phaseC + phaseB n * q := by
  rw [phaseNat_cast_eq_two_phaseS_div_q_add_phaseB hn]
  simp only [phaseS]
  field_simp [q_ne_zero]

/-- Manuscript (2.4), including an explicit full-sequence quantifier and an
absolute positive constant.  The exponent is a real power, so the displayed
right-hand side is literally `c n² (log n)^(2/q-5/2)`. -/
theorem exists_pos_eventually_mu_phaseNat_sub_two_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ 2 *
          (logOrder n) ^ (2 / q - 5 / 2 : ℝ) ≤
        mu n (phaseNat n - 2) := by
  obtain ⟨B, hBaseMoment⟩ := exists_eventually_log_mu_phaseNat_lower
  let D : ℝ := 4 * phaseC - 4 * q - B
  refine ⟨Real.exp D, Real.exp_pos D, ?_⟩
  have hOrderLarge : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hBaseMoment, eventually_phaseDomain,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    eventually_two_mul_phaseNat_le, hOrderLarge] with
    n hBase hnDomain hPhaseBounds hTwo hOrderLarge
  let a : ℕ := phaseNat n
  have hOrderPos : 0 < logOrder n := lt_of_lt_of_le (by norm_num) hOrderLarge
  have hnPos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by
      have := hnDomain.1
      omega)
  have haTwo : 2 ≤ a := by
    have hCast : (2 : ℝ) ≤ (a : ℝ) := hOrderLarge.trans hPhaseBounds.1
    exact_mod_cast hCast
  have haPos : 0 < a := by omega
  have haLe : a ≤ n := by
    change 2 * a ≤ n at hTwo
    omega
  have haPredPos : 0 < a - 1 := by omega
  have haPredLe : a - 1 ≤ n := by omega
  have haSubTwoLe : a - 2 ≤ n := by omega
  have hPredOne := log_mu_pred_sub_log_mu haPos haLe
  have hPredTwo := log_mu_pred_sub_log_mu haPredPos haPredLe
  have hLogA : logLogOrder n ≤ Real.log (a : ℝ) := by
    simpa only [logLogOrder] using
      Real.log_le_log hOrderPos hPhaseBounds.1
  have hCastPred : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hHalfLePred : logOrder n / 2 ≤ ((a - 1 : ℕ) : ℝ) := by
    rw [hCastPred]
    linarith [hPhaseBounds.1]
  have hLogHalf :
      Real.log (logOrder n / 2) = logLogOrder n - q := by
    rw [Real.log_div hOrderPos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    rfl
  have hLogPred :
      logLogOrder n - q ≤ Real.log ((a - 1 : ℕ) : ℝ) := by
    rw [← hLogHalf]
    exact Real.log_le_log (div_pos hOrderPos (by norm_num)) hHalfLePred
  have hDenomOneNat : n - a + 1 ≤ n := by omega
  have hDenomOne :
      Real.log (((n - a : ℕ) + 1 : ℕ) : ℝ) ≤ logOrder n := by
    simpa only [logOrder] using Real.log_le_log (by positivity)
      (by exact_mod_cast hDenomOneNat)
  have hDenomTwoNat : n - (a - 1) + 1 ≤ n := by omega
  have hDenomTwo :
      Real.log (((n - (a - 1) : ℕ) + 1 : ℕ) : ℝ) ≤ logOrder n := by
    simpa only [logOrder] using Real.log_le_log (by positivity)
      (by exact_mod_cast hDenomTwoNat)
  have hCastSubTwo : ((a - 2 : ℕ) : ℝ) = (a : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hPhaseQ := phaseNat_mul_q_identity hnDomain
  have hBq : 0 ≤ phaseB n * q :=
    mul_nonneg (phaseB_pos n).le q_pos.le
  have hPowerLower :
      4 * logOrder n - 4 * logLogOrder n + 4 * phaseC - 3 * q ≤
        ((a - 1 : ℕ) : ℝ) * q + ((a - 2 : ℕ) : ℝ) * q := by
    rw [hCastPred, hCastSubTwo]
    linarith
  have hSubSub : (a - 1 : ℕ) - 1 = a - 2 := by omega
  simp only [hSubSub] at hPredTwo
  have hLogLower :
      2 * logOrder n + (2 / q - 5 / 2 : ℝ) * logLogOrder n + D ≤
        Real.log (mu n (a - 2)) := by
    dsimp only [D]
    linarith
  have hExpTwo : Real.exp (2 * logOrder n) = (n : ℝ) ^ 2 := by
    rw [show 2 * logOrder n = (2 : ℕ) * logOrder n by norm_num,
      Real.exp_nat_mul]
    simp only [logOrder, Real.exp_log hnPos]
  calc
    Real.exp D * (n : ℝ) ^ 2 *
          (logOrder n) ^ (2 / q - 5 / 2 : ℝ) =
        Real.exp
          (2 * logOrder n + (2 / q - 5 / 2 : ℝ) * logLogOrder n + D) := by
      rw [Real.rpow_def_of_pos hOrderPos, ← hExpTwo]
      rw [show 2 * logOrder n + (2 / q - 5 / 2 : ℝ) * logLogOrder n + D =
          D + 2 * logOrder n + Real.log (logOrder n) *
            (2 / q - 5 / 2 : ℝ) by
            simp only [logLogOrder]
            ring,
        Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (Real.log (mu n (a - 2))) := Real.exp_le_exp.mpr hLogLower
    _ = mu n (a - 2) := Real.exp_log (mu_pos haSubTwoLe)

/-! ## The first-moment probability consequence: manuscript equation (2.9) -/

/-- The sharp shifted Markov bound and (2.3) give, on the full sequence,
`P(α(Gₙ) > phaseNat n + 1) → 0`. -/
theorem randomGraphMeasure_independenceNumberExceeds_phaseNat_add_one_tendsto_zero :
    Tendsto (fun n : ℕ ↦ randomGraphMeasure n
      (independenceNumberExceedsEvent n (phaseNat n + 1)))
      atTop (𝓝 0) := by
  have hMoment : Tendsto (fun n : ℕ ↦
      ENNReal.ofReal (mu n (phaseNat n + 2))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal mu_phaseNat_add_two_tendsto_zero
  have hUpper : ∀ᶠ n : ℕ in atTop,
      randomGraphMeasure n
          (independenceNumberExceedsEvent n (phaseNat n + 1)) ≤
        ENNReal.ofReal (mu n (phaseNat n + 2)) := by
    apply Filter.Eventually.of_forall
    intro n
    simpa only [Nat.add_assoc, one_add_one_eq_two] using
      randomGraphMeasure_independenceNumberExceeds_le_mu_succ
        n (phaseNat n + 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hMoment
    (Filter.Eventually.of_forall fun _n ↦ bot_le) hUpper

end

end Erdos625
