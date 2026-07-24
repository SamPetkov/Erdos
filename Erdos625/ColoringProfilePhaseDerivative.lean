import Erdos625.ColoringProfilePhaseObjective
import Erdos625.ColoringProfileDualOptimalValue

/-!
# Derivative of the selected phase/profile objective

The phase entropy contribution is constant in the real part count, so the
derivative is inherited directly from the selected finite dual optimum.
-/

namespace Erdos625

noncomputable section

/-- The selected phase/profile objective has the finite-envelope derivative
with respect to the real part count throughout its interior mean domain. -/
theorem hasDerivAt_profilePhaseObjective_parts
    (n : ℕ) {parts : ℝ} (hparts : 0 < parts)
    (htarget : (n : ℝ) / parts ∈
      Set.Ioo 1 (((phaseNat n + 1 : ℕ) : ℝ))) :
    HasDerivAt (fun k ↦ profilePhaseObjective n k)
      (Real.log (profileDualPartition (phaseNat n + 1)
          (profileDualTilt (phaseNat n + 1) ((n : ℝ) / parts))) -
        Real.log parts) parts := by
  have hbReal : (1 : ℝ) < ((phaseNat n + 1 : ℕ) : ℝ) :=
    lt_trans htarget.1 htarget.2
  have hb : 2 ≤ phaseNat n + 1 := by
    exact_mod_cast hbReal
  have hConst : HasDerivAt
      (fun _ : ℝ ↦ ((phaseNat n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1))
      0 parts :=
    hasDerivAt_const parts _
  change HasDerivAt
    (fun k ↦ ((phaseNat n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) +
      profileDualOptimalValue (phaseNat n + 1) (n : ℝ) k)
    (Real.log (profileDualPartition (phaseNat n + 1)
        (profileDualTilt (phaseNat n + 1) ((n : ℝ) / parts))) -
      Real.log parts) parts
  apply ((hConst.add
    (hasDerivAt_profileDualOptimalValue_parts hb hparts htarget)).congr_of_eventuallyEq
      (f₁ := fun k ↦ ((phaseNat n + 1 : ℕ) : ℝ) *
        Real.log ((n : ℝ) + 1) +
        profileDualOptimalValue (phaseNat n + 1) (n : ℝ) k)
      (Filter.Eventually.of_forall fun _ ↦ rfl)).congr_deriv
  simp

/-- The derivative form of `hasDerivAt_profilePhaseObjective_parts`. -/
theorem deriv_profilePhaseObjective_parts
    (n : ℕ) {parts : ℝ} (hparts : 0 < parts)
    (htarget : (n : ℝ) / parts ∈
      Set.Ioo 1 (((phaseNat n + 1 : ℕ) : ℝ))) :
    deriv (fun k ↦ profilePhaseObjective n k) parts =
      Real.log (profileDualPartition (phaseNat n + 1)
          (profileDualTilt (phaseNat n + 1) ((n : ℝ) / parts))) -
        Real.log parts :=
  (hasDerivAt_profilePhaseObjective_parts n hparts htarget).deriv

end

end Erdos625
