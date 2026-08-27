import Erdos625.PhaseSignedFourSizeGapCorridorDomain
import Mathlib.Tactic

/-!
# Compact target corridor for the signed four-size phase objective

This strengthens the native gap-corridor domain theorem to a fixed compact
subinterval of `(2, 5)`.  That fixed compact set is the input required by the
existing uniform finite-four tilt and optimizer convergence APIs.  No
derivative estimate, center-value estimate, or root-existence claim is made.
-/

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

/-- Eventually the deficit target attached to every point of the native
phase-root gap corridor lies in the fixed compact interval `[9/4, 17/4]`.
This interval is strictly contained in the four-size support `(2, 5)`. -/
theorem eventually_phaseRootGapCorridor_fourSize_target_mem_Icc :
    ∀ᶠ n : Nat in atTop,
      ∀ s ∈ Icc
          (phaseRootCenter n - phaseRootGapRadius n)
          (phaseRootCenter n + phaseRootGapRadius n),
        fourSizeTarget n (phaseNat n) s ∈
          Icc (9 / 4 : Real) (17 / 4 : Real) := by
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_five_lt_phaseNat,
    eventually_phaseRootGapCorridor_fourSize_domain] with
      n hcenter hphase hcorridor
  obtain ⟨hdom, hs0Pos, _⟩ := hcenter
  set a : Real := (phaseNat n : Real) with ha
  set s0 : Real := phaseRootS0 n with hs0
  set c : Real := phaseRootCenter n with hc
  set gap : Real := phaseRootGapRadius n with hgap
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
  have hs0Eq : s0 = a + phaseDelta n - 1 - 2 / q := by
    rw [hs0, phaseRootS0, alphaZero_eq_phaseNat_add_delta hdom, ha]
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
  have hs0Upper : s0 < a - 5 / 2 := by
    rw [hs0Eq]
    linarith [phaseDelta_lt_one n]
  have hs0Lower : a - 4 < s0 := by
    rw [hs0Eq]
    linarith [phaseDelta_nonneg n]
  have hLowerCorrection :
      (a - 9 / 4) / a ^ 2 < (1 / 4 : Real) := by
    rw [div_lt_iff₀ haSqPos]
    nlinarith [sq_nonneg (a - 2)]
  have hUpperCorrection :
      (a - 17 / 4) / a ^ 2 < (1 / 4 : Real) := by
    rw [div_lt_iff₀ haSqPos]
    nlinarith [sq_nonneg (a - 2)]
  have hs0BelowLowerEndpointSlope :
      s0 < (a - 9 / 4) * (1 - 1 / a ^ 2) := by
    rw [show (a - 9 / 4) * (1 - 1 / a ^ 2) =
      a - 9 / 4 - (a - 9 / 4) / a ^ 2 by ring]
    linarith
  have hs0AboveUpperEndpointSlope :
      (a - 17 / 4) * (1 + 1 / a ^ 2) < s0 := by
    rw [show (a - 17 / 4) * (1 + 1 / a ^ 2) =
      a - 17 / 4 + (a - 17 / 4) / a ^ 2 by ring]
    linarith
  intro s hs
  have hsDomain := hcorridor s hs
  rw [mem_Icc] at hs
  have hsPos : 0 < s := hsDomain.1
  rw [fourSizeTarget, mem_Icc]
  change 9 / 4 ≤ a - (n : Real) / s ∧
    a - (n : Real) / s ≤ 17 / 4
  have hLowerBase :
      (n : Real) < (a - 9 / 4) * (c - gap) := by
    have hmul := mul_lt_mul_of_pos_left hs0BelowLowerEndpointSlope hcPos
    rw [hnEq, hgapEq]
    calc
      c * s0 < c * ((a - 9 / 4) * (1 - 1 / a ^ 2)) := hmul
      _ = (a - 9 / 4) * (c - c / a ^ 2) := by ring
  have hLowerNumerator : (n : Real) < (a - 9 / 4) * s := by
    exact hLowerBase.trans_le
      (mul_le_mul_of_nonneg_left hs.1 (by linarith))
  have hLowerQuotient : (n : Real) / s < a - 9 / 4 := by
    rw [div_lt_iff₀ hsPos]
    simpa [mul_comm] using hLowerNumerator
  have hUpperBase :
      (a - 17 / 4) * (c + gap) < (n : Real) := by
    have hmul := mul_lt_mul_of_pos_left hs0AboveUpperEndpointSlope hcPos
    rw [hnEq, hgapEq]
    calc
      (a - 17 / 4) * (c + c / a ^ 2) =
          c * ((a - 17 / 4) * (1 + 1 / a ^ 2)) := by ring
      _ < c * s0 := hmul
  have hUpperNumerator : (a - 17 / 4) * s < (n : Real) := by
    exact (mul_le_mul_of_nonneg_left hs.2 (by linarith)).trans_lt hUpperBase
  have hUpperQuotient : a - 17 / 4 < (n : Real) / s := by
    rw [lt_div_iff₀ hsPos]
    exact hUpperNumerator
  constructor <;> linarith

end

end Erdos625
