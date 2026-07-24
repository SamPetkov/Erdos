import Erdos625.PhaseRootPartGeometry
import Erdos625.PhaseEstimates
import Mathlib.Tactic

namespace Erdos625

open Filter Asymptotics

noncomputable section

set_option autoImplicit false

/-- The natural manuscript-scale radius around the reference phase center. -/
noncomputable def phaseRootGapRadius (n : ℕ) : ℝ :=
  phaseRootCenter n / (phaseNat n : ℝ) ^ 2

/--
The inverse quadratic slope scale at the reference center has exactly the
manuscript order `n / (logOrder n)^3`.
-/
theorem phaseRootCenter_div_phaseNat_sq_isTheta_gapScale :
    (fun n : ℕ ↦
      phaseRootCenter n / (phaseNat n : ℝ) ^ 2) =Θ[atTop]
        (fun n : ℕ ↦ (n : ℝ) / (logOrder n) ^ 3) := by
  have hS0 : phaseRootS0 =Θ[atTop] logOrder :=
    (IsEquivalent.isTheta phaseRootS0_isEquivalent_scaled_logOrder).of_const_mul_right
      (div_ne_zero (by norm_num) q_ne_zero)
  have hPhase : (fun n : ℕ ↦ (phaseNat n : ℝ)) =Θ[atTop] logOrder :=
    phaseNat_isTheta_logOrder
  have hCenter : (fun n : ℕ ↦ (n : ℝ) / phaseRootS0 n) =Θ[atTop]
      (fun n : ℕ ↦ (n : ℝ) / logOrder n) :=
    (isTheta_refl (fun n : ℕ ↦ (n : ℝ)) atTop).div hS0
  have hSq : (fun n : ℕ ↦ (phaseNat n : ℝ) ^ 2) =Θ[atTop]
      (fun n : ℕ ↦ (logOrder n) ^ 2) := hPhase.pow 2
  have hDiv := hCenter.div hSq
  have hEq : (fun n : ℕ ↦ ((n : ℝ) / logOrder n) / (logOrder n) ^ 2) =
      (fun n : ℕ ↦ (n : ℝ) / (logOrder n) ^ 3) := by
    funext n; ring
  rw [hEq] at hDiv
  simpa only [phaseRootCenter] using hDiv

/-- The named phase-root corridor radius has order `n / (logOrder n)^3`. -/
theorem phaseRootGapRadius_isTheta_gapScale :
    phaseRootGapRadius =Θ[atTop]
      (fun n : ℕ ↦ (n : ℝ) / (logOrder n) ^ 3) := by
  change (fun n : ℕ ↦ phaseRootCenter n / (phaseNat n : ℝ) ^ 2) =Θ[atTop]
    (fun n : ℕ ↦ (n : ℝ) / (logOrder n) ^ 3)
  exact phaseRootCenter_div_phaseNat_sq_isTheta_gapScale

end

end Erdos625
