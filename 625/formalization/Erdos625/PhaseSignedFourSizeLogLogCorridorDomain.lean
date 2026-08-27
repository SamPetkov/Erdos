import Erdos625.PhaseSignedFourSizeReferenceCenterScale
import Erdos625.PhaseSignedFourSizeGapCorridorDomain
import Mathlib.Tactic

/-!
# The logarithmic-logarithmic signed-root corridor domain

The signed objective at the reference center has normalized size
`O(logLogOrder)`, so the actual root search must use a corridor whose radius
is a fixed multiple of `logLogOrder * phaseRootGapRadius`.  This module proves
only the geometric/admissibility part of that enlargement.  Derivative
control and root existence remain separate obligations.
-/

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

private theorem eventually_mul_logLogOrder_le_phaseNat_div_sixteen
    (C : Real) (hC : 0 ≤ C) :
    ∀ᶠ n : Nat in atTop,
      C * logLogOrder n ≤ (phaseNat n : Real) / 16 := by
  have hOneC : 0 < 1 + C := by linarith
  have hEps : (0 : Real) < 1 / (16 * (1 + C)) := by positivity
  have hLittle := logLogOrder_isLittleO_logOrder.bound hEps
  have hLogPos : ∀ᶠ n : Nat in atTop, 0 < logOrder n :=
    tendsto_logOrder_atTop.eventually_gt_atTop 0
  have hLogLogNonneg : ∀ᶠ n : Nat in atTop, 0 ≤ logLogOrder n :=
    (tendsto_logLogOrder_atTop.eventually_gt_atTop 0).mono fun _ hn ↦ hn.le
  filter_upwards [hLittle, hLogPos, hLogLogNonneg,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
      n hsmall hlog hloglog hphase
  rw [Real.norm_eq_abs, abs_of_nonneg hloglog,
    Real.norm_eq_abs, abs_of_pos hlog] at hsmall
  have hCLe : C ≤ 1 + C := by linarith
  have hmul : C * logLogOrder n ≤ (1 + C) * logLogOrder n :=
    mul_le_mul_of_nonneg_right hCLe hloglog
  have hscaled :
      (1 + C) * logLogOrder n ≤ logOrder n / 16 := by
    calc
      (1 + C) * logLogOrder n ≤
          (1 + C) * ((1 / (16 * (1 + C))) * logOrder n) :=
        mul_le_mul_of_nonneg_left hsmall hOneC.le
      _ = logOrder n / 16 := by field_simp
  exact hmul.trans (hscaled.trans (by linarith [hphase.1]))

/-- For every fixed nonnegative coefficient, the
`logLogOrder * phaseRootGapRadius` corridor is eventually positive and remains
inside the literal open four-size support `(2, 5)`. -/
theorem eventually_phaseRootLogLogCorridor_fourSize_domain
    (C : Real) (hC : 0 ≤ C) :
    ∀ᶠ n : Nat in atTop,
      ∀ s ∈ Icc
          (phaseRootCenter n -
            C * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            C * logLogOrder n * phaseRootGapRadius n),
        0 < s ∧
          fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : Real) 5 := by
  have hqLower : (2 / 3 : Real) < q := by
    exact (by norm_num : (2 / 3 : Real) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hqUpper : q < (4 / 5 : Real) := by
    exact Real.log_two_lt_d9.trans (by norm_num)
  have hTwoDivQLower : (5 / 2 : Real) < 2 / q := by
    rw [lt_div_iff₀ q_pos]
    nlinarith
  have hTwoDivQUpper : 2 / q < (3 : Real) := by
    rw [div_lt_iff₀ q_pos]
    nlinarith
  have hScale := eventually_mul_logLogOrder_le_phaseNat_div_sixteen C hC
  have hLogLogNonneg : ∀ᶠ n : Nat in atTop, 0 ≤ logLogOrder n :=
    (tendsto_logLogOrder_atTop.eventually_gt_atTop 0).mono fun _ hn ↦ hn.le
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_five_lt_phaseNat, hScale, hLogLogNonneg] with
      n hcenter hphase hscale hloglog
  obtain ⟨hdom, hs0Pos, _⟩ := hcenter
  set a : Real := (phaseNat n : Real) with ha
  set s0 : Real := phaseRootS0 n with hs0
  set c : Real := phaseRootCenter n with hc
  set gap : Real := phaseRootGapRadius n with hgap
  set wide : Real := C * logLogOrder n * gap with hwide
  have haSix : (6 : Real) ≤ a := by
    rw [ha]
    exact_mod_cast hphase
  have haPos : 0 < a := by linarith
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
  have hnPos : (0 : Real) < n := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hdom.1)
  have hcEq : c = (n : Real) / s0 := by
    rw [hc, hs0]
    rfl
  have hcPos : 0 < c := by
    rw [hcEq]
    exact div_pos hnPos hs0Pos
  have hnEq : (n : Real) = c * s0 := by
    rw [hcEq]
    field_simp [hs0Pos.ne']
  have hgapEq : gap = c / a ^ 2 := by
    rw [hgap, hc, ha]
    rfl
  have hwideEq : wide = c * (C * logLogOrder n / a ^ 2) := by
    rw [hwide, hgapEq]
    ring
  have hs0Eq : s0 = a + phaseDelta n - 1 - 2 / q := by
    rw [hs0, phaseRootS0, alphaZero_eq_phaseNat_add_delta hdom, ha]
  have hs0Upper : s0 < a - 5 / 2 := by
    rw [hs0Eq]
    linarith [phaseDelta_lt_one n]
  have hs0Lower : a - 4 < s0 := by
    rw [hs0Eq]
    linarith [phaseDelta_nonneg n]
  have hscale' : C * logLogOrder n ≤ a / 16 := by
    simpa [ha] using hscale
  have hratioNonneg : 0 ≤ C * logLogOrder n / a ^ 2 :=
    div_nonneg (mul_nonneg hC hloglog) haSqPos.le
  have hratioLtOne : C * logLogOrder n / a ^ 2 < 1 := by
    rw [div_lt_iff₀ haSqPos]
    nlinarith [hscale', sq_pos_of_pos haPos]
  have hwideNonneg : 0 ≤ wide := by
    rw [hwideEq]
    exact mul_nonneg hcPos.le hratioNonneg
  have hwideLtCenter : wide < c := by
    rw [hwideEq]
    nlinarith [hcPos]
  have hLowerCorrection :
      (a - 2) * (C * logLogOrder n) / a ^ 2 < (1 / 2 : Real) := by
    rw [div_lt_iff₀ haSqPos]
    have hmul := mul_le_mul_of_nonneg_left hscale' (by linarith : 0 ≤ a - 2)
    nlinarith [sq_pos_of_pos haPos]
  have hUpperCorrection :
      (a - 5) * (C * logLogOrder n) / a ^ 2 < (1 : Real) := by
    rw [div_lt_iff₀ haSqPos]
    have hmul := mul_le_mul_of_nonneg_left hscale' (by linarith : 0 ≤ a - 5)
    nlinarith [sq_pos_of_pos haPos]
  have hs0BelowLowerEndpointSlope :
      s0 < (a - 2) * (1 - C * logLogOrder n / a ^ 2) := by
    rw [show (a - 2) * (1 - C * logLogOrder n / a ^ 2) =
      a - 2 - (a - 2) * (C * logLogOrder n) / a ^ 2 by ring]
    linarith
  have hs0AboveUpperEndpointSlope :
      (a - 5) * (1 + C * logLogOrder n / a ^ 2) < s0 := by
    rw [show (a - 5) * (1 + C * logLogOrder n / a ^ 2) =
      a - 5 + (a - 5) * (C * logLogOrder n) / a ^ 2 by ring]
    linarith
  intro s hs
  rw [mem_Icc] at hs
  have hsPos : 0 < s := by
    linarith [hs.1, hwideLtCenter]
  refine ⟨hsPos, ?_⟩
  rw [fourSizeTarget, mem_Ioo]
  change 2 < a - (n : Real) / s ∧ a - (n : Real) / s < 5
  have hLowerBase : (n : Real) < (a - 2) * (c - wide) := by
    have hmul := mul_lt_mul_of_pos_left hs0BelowLowerEndpointSlope hcPos
    rw [hnEq, hwideEq]
    calc
      c * s0 < c * ((a - 2) *
          (1 - C * logLogOrder n / a ^ 2)) := hmul
      _ = (a - 2) *
          (c - c * (C * logLogOrder n / a ^ 2)) := by ring
  have hLowerNumerator : (n : Real) < (a - 2) * s := by
    exact hLowerBase.trans_le
      (mul_le_mul_of_nonneg_left hs.1 (by linarith))
  have hLowerQuotient : (n : Real) / s < a - 2 := by
    rw [div_lt_iff₀ hsPos]
    simpa [mul_comm] using hLowerNumerator
  have hUpperBase : (a - 5) * (c + wide) < (n : Real) := by
    have hmul := mul_lt_mul_of_pos_left hs0AboveUpperEndpointSlope hcPos
    rw [hnEq, hwideEq]
    calc
      (a - 5) * (c + c * (C * logLogOrder n / a ^ 2)) =
          c * ((a - 5) *
            (1 + C * logLogOrder n / a ^ 2)) := by ring
      _ < c * s0 := hmul
  have hUpperNumerator : (a - 5) * s < (n : Real) := by
    exact (mul_le_mul_of_nonneg_left hs.2 (by linarith)).trans_lt hUpperBase
  have hUpperQuotient : a - 5 < (n : Real) / s := by
    rw [lt_div_iff₀ hsPos]
    exact hUpperNumerator
  constructor <;> linarith

end

#print axioms eventually_phaseRootLogLogCorridor_fourSize_domain

end Erdos625
