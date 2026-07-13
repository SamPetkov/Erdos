import Erdos625.Phase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Exact setup for the phase expansion

This module isolates the exact constants and elementary domain bookkeeping
used in (2.5)--(2.7) of the manuscript.  It deliberately does not assert the
`O(w² / N)` remainder in Lemma 2.1; that estimate requires a separate,
quantitative Taylor-and-Stirling argument.
-/

namespace Erdos625

open Filter Asymptotics

/-- The constant `C = 1 + log q - q` used in the phase expansion. -/
noncomputable def phaseC : ℝ := 1 + Real.log q - q

/-- The centered logarithmic scale `S = N - w + C`. -/
noncomputable def phaseS (n : ℕ) : ℝ :=
  logOrder n - logLogOrder n + phaseC

/-- The endpoint-uniform offset `b = 1 - delta`. -/
noncomputable def phaseB (n : ℕ) : ℝ := 1 - phaseDelta n

/-- The bounded constant term `K(delta)` displayed in (2.7). -/
noncomputable def phaseK (delta : ℝ) : ℝ :=
  delta * phaseC + q / 2 * delta * (1 - delta) - 2 * phaseC / q -
    (1 - delta) - (1 / 2 : ℝ) * Real.log (2 * Real.pi) - q / 2 +
    (1 / 2 : ℝ) * Real.log q

theorem phaseB_pos (n : ℕ) : 0 < phaseB n := by
  exact sub_pos.mpr (phaseDelta_lt_one n)

theorem phaseB_le_one (n : ℕ) : phaseB n ≤ 1 := by
  exact sub_le_self 1 (phaseDelta_nonneg n)

theorem phaseB_mem_Ioc (n : ℕ) : phaseB n ∈ Set.Ioc (0 : ℝ) 1 :=
  ⟨phaseB_pos n, phaseB_le_one n⟩

private theorem log_logBaseTwo_nat {n : ℕ} (hn : 1 < n) :
    Real.log (logBaseTwo (n : ℝ)) = logLogOrder n - Real.log q := by
  have hnReal : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog : logOrder n ≠ 0 := ne_of_gt (Real.log_pos hnReal)
  have hlog' : Real.log (n : ℝ) ≠ 0 := by
    simpa only [logOrder] using hlog
  simpa only [logBaseTwo, logOrder, logLogOrder] using
    (Real.log_div hlog' q_ne_zero)

private theorem log_exp_one_div_two :
    Real.log (Real.exp 1 / 2) = 1 - q := by
  rw [Real.log_div (Real.exp_ne_zero 1) (by norm_num : (2 : ℝ) ≠ 0)]
  simp [q]

/-- Exact, non-asymptotic normal form for `alpha_0` on its logarithmic domain. -/
theorem alphaZero_eq_two_phaseS_div_q_add_one {n : ℕ} (hn : 1 < n) :
    alphaZero n = 2 * phaseS n / q + 1 := by
  rw [alphaZero]
  change
    2 * (logOrder n / q) -
          2 * (Real.log (logBaseTwo (n : ℝ)) / q) +
        2 * (Real.log (Real.exp 1 / 2) / q) + 1 =
      2 * phaseS n / q + 1
  rw [log_logBaseTwo_nat hn, log_exp_one_div_two]
  simp only [phaseS, phaseC]
  ring

/-- The manuscript identity `alpha = 2S/q + b`, with `alpha` represented by
the integer floor and then cast to `ℝ`.  Only `1 < n` is needed here. -/
theorem phaseInt_cast_eq_two_phaseS_div_q_add_phaseB {n : ℕ} (hn : 1 < n) :
    (phaseInt n : ℝ) = 2 * phaseS n / q + phaseB n := by
  have hzero := alphaZero_eq_two_phaseS_div_q_add_one hn
  have hfloor := alphaZero_eq_phaseInt_add_delta n
  simp only [phaseB]
  linarith

/-- Natural-number version of `alpha = 2S/q + b`.  `PhaseDomain` is exactly
the extra condition needed to identify `phaseNat` with the integer floor. -/
theorem phaseNat_cast_eq_two_phaseS_div_q_add_phaseB {n : ℕ}
    (hn : PhaseDomain n) :
    (phaseNat n : ℝ) = 2 * phaseS n / q + phaseB n := by
  rw [phaseNat_cast_real hn]
  exact phaseInt_cast_eq_two_phaseS_div_q_add_phaseB hn.1

theorem continuous_phaseK : Continuous phaseK := by
  unfold phaseK
  fun_prop

theorem phaseK_bddAbove_Icc : BddAbove (phaseK '' Set.Icc (0 : ℝ) 1) :=
  isCompact_Icc.bddAbove_image continuous_phaseK.continuousOn

theorem phaseK_bddBelow_Icc : BddBelow (phaseK '' Set.Icc (0 : ℝ) 1) :=
  isCompact_Icc.bddBelow_image continuous_phaseK.continuousOn

/-- A single absolute bound for `K` on the full closed phase interval. -/
theorem exists_phaseK_abs_bound :
    ∃ M : ℝ, ∀ delta ∈ Set.Icc (0 : ℝ) 1, |phaseK delta| ≤ M := by
  have hbounded : BddAbove ((fun delta : ℝ ↦ |phaseK delta|) '' Set.Icc 0 1) :=
    isCompact_Icc.bddAbove_image continuous_phaseK.abs.continuousOn
  obtain ⟨M, hM⟩ := bddAbove_def.mp hbounded
  refine ⟨M, ?_⟩
  intro delta hdelta
  exact hM _ (Set.mem_image_of_mem (fun x : ℝ ↦ |phaseK x|) hdelta)

theorem tendsto_logOrder_atTop : Tendsto logOrder atTop atTop := by
  change Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop
  simpa only [Function.comp_def] using
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem tendsto_logLogOrder_atTop : Tendsto logLogOrder atTop atTop := by
  change Tendsto (fun n : ℕ ↦ Real.log (logOrder n)) atTop atTop
  simpa only [Function.comp_def] using
    Real.tendsto_log_atTop.comp tendsto_logOrder_atTop

theorem logOrder_isLittleO_natCast :
    (fun n : ℕ ↦ logOrder n) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
  simpa only [logOrder, Function.comp_def, id_eq] using
    Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))

theorem logLogOrder_isLittleO_logOrder :
    (fun n : ℕ ↦ logLogOrder n) =o[atTop] (fun n : ℕ ↦ logOrder n) := by
  simpa only [logLogOrder, Function.comp_def, id_eq] using
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_logOrder_atTop

theorem logLogOrder_isLittleO_natCast :
    (fun n : ℕ ↦ logLogOrder n) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) :=
  logLogOrder_isLittleO_logOrder.trans logOrder_isLittleO_natCast

theorem phaseS_isLittleO_natCast :
    (fun n : ℕ ↦ phaseS n) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
  have hC : (fun _n : ℕ ↦ phaseC) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
    simpa only [Function.comp_def, id_eq] using
      (isLittleO_const_id_atTop phaseC).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [phaseS] using
    (logOrder_isLittleO_natCast.sub logLogOrder_isLittleO_natCast).add hC

theorem alphaZero_isLittleO_natCast :
    (fun n : ℕ ↦ alphaZero n) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
  have hOne : (fun _n : ℕ ↦ (1 : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
    simpa only [Function.comp_def, id_eq] using
      (isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hNormal :
      (fun n : ℕ ↦ (2 / q) * phaseS n + 1) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ)) :=
    (phaseS_isLittleO_natCast.const_mul_left (2 / q)).add hOne
  have hEventually :
      (fun n : ℕ ↦ alphaZero n) =ᶠ[atTop]
        (fun n : ℕ ↦ (2 / q) * phaseS n + 1) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    rw [alphaZero_eq_two_phaseS_div_q_add_one hn]
    ring
  exact hEventually.trans_isLittleO hNormal

theorem tendsto_phaseS_atTop : Tendsto phaseS atTop atTop := by
  have hBound := logLogOrder_isLittleO_logOrder.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hOrderNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop (0 : ℝ))
  have hLower :
      (fun n : ℕ ↦ logOrder n / 2 + phaseC) ≤ᶠ[atTop] phaseS := by
    filter_upwards [hBound, hOrderNonneg] with n hnBound hnNonneg
    have hwLe : logLogOrder n ≤ logOrder n / 2 := by
      calc
        logLogOrder n ≤ |logLogOrder n| := le_abs_self _
        _ = ‖logLogOrder n‖ := (Real.norm_eq_abs _).symm
        _ ≤ (1 / 2 : ℝ) * ‖logOrder n‖ := hnBound
        _ = logOrder n / 2 := by rw [Real.norm_eq_abs, abs_of_nonneg hnNonneg]; ring
    simp only [phaseS]
    linarith
  have hHalf : Tendsto (fun n : ℕ ↦ logOrder n / 2) atTop atTop := by
    convert tendsto_logOrder_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 1
    ext n
    ring
  have hLowerTop : Tendsto (fun n : ℕ ↦ logOrder n / 2 + phaseC) atTop atTop :=
    tendsto_atTop_add_const_right atTop phaseC hHalf
  exact tendsto_atTop_mono' atTop hLower hLowerTop

theorem tendsto_alphaZero_atTop : Tendsto alphaZero atTop atTop := by
  have hScaled : Tendsto (fun n : ℕ ↦ (2 / q) * phaseS n) atTop atTop :=
    tendsto_phaseS_atTop.const_mul_atTop (div_pos (by norm_num) q_pos)
  have hNormal : Tendsto (fun n : ℕ ↦ (2 / q) * phaseS n + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hScaled
  apply hNormal.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  rw [alphaZero_eq_two_phaseS_div_q_add_one hn]
  ring

/-- A convenient exact safe domain for all finite phase indices used later. -/
def PhaseRangeDomain (n : ℕ) : Prop :=
  1 < n ∧ 2 ≤ alphaZero n ∧ alphaZero n < (n : ℝ) - 1

theorem PhaseRangeDomain.phaseDomain {n : ℕ} (hn : PhaseRangeDomain n) :
    PhaseDomain n := by
  exact ⟨hn.1, le_trans (by norm_num : (0 : ℝ) ≤ 2) hn.2.1⟩

theorem PhaseRangeDomain.two_le_phaseInt {n : ℕ} (hn : PhaseRangeDomain n) :
    (2 : ℤ) ≤ phaseInt n := by
  rw [phaseInt, Int.le_floor]
  exact hn.2.1

theorem PhaseRangeDomain.two_le_phaseNat {n : ℕ} (hn : PhaseRangeDomain n) :
    2 ≤ phaseNat n := by
  have hcast : (2 : ℤ) ≤ (phaseNat n : ℤ) := by
    rw [phaseNat_cast_int hn.phaseDomain]
    exact hn.two_le_phaseInt
  exact_mod_cast hcast

theorem PhaseRangeDomain.phaseInt_lt_n_sub_one {n : ℕ}
    (hn : PhaseRangeDomain n) :
    phaseInt n < (n : ℤ) - 1 := by
  rw [phaseInt, Int.floor_lt]
  exact_mod_cast hn.2.2

theorem PhaseRangeDomain.phaseNat_add_two_le {n : ℕ}
    (hn : PhaseRangeDomain n) :
    phaseNat n + 2 ≤ n := by
  have hlt := hn.phaseInt_lt_n_sub_one
  have hInt : phaseInt n + 2 ≤ (n : ℤ) := by
    omega
  have hcast : (phaseNat n : ℤ) + 2 ≤ (n : ℤ) := by
    rw [phaseNat_cast_int hn.phaseDomain]
    exact hInt
  exact_mod_cast hcast

theorem eventually_phaseRangeDomain : ∀ᶠ n : ℕ in atTop, PhaseRangeDomain n := by
  have hOne : ∀ᶠ n : ℕ in atTop, 1 < n := eventually_gt_atTop 1
  have hTwo : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ alphaZero n :=
    tendsto_alphaZero_atTop.eventually (eventually_ge_atTop (2 : ℝ))
  have hSmall := alphaZero_isLittleO_natCast.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hFour : ∀ᶠ n : ℕ in atTop, 4 ≤ n := eventually_ge_atTop 4
  filter_upwards [hOne, hTwo, hSmall, hFour] with n hnOne hnTwo hnSmall hnFour
  refine ⟨hnOne, hnTwo, ?_⟩
  have hAlphaLeAbs : alphaZero n ≤ ‖alphaZero n‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  have hnNorm : ‖(n : ℝ)‖ = (n : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
  rw [hnNorm] at hnSmall
  have hnReal : (4 : ℝ) ≤ n := by exact_mod_cast hnFour
  linarith

theorem eventually_phaseDomain : ∀ᶠ n : ℕ in atTop, PhaseDomain n :=
  eventually_phaseRangeDomain.mono fun _n hn ↦ hn.phaseDomain

theorem eventually_two_le_phaseNat : ∀ᶠ n : ℕ in atTop, 2 ≤ phaseNat n :=
  eventually_phaseRangeDomain.mono fun _n hn ↦ hn.two_le_phaseNat

theorem eventually_phaseNat_add_two_le :
    ∀ᶠ n : ℕ in atTop, phaseNat n + 2 ≤ n :=
  eventually_phaseRangeDomain.mono fun _n hn ↦ hn.phaseNat_add_two_le

end Erdos625
