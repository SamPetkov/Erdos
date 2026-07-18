import Erdos625.ColoringProfileDualOptimalValue
import Erdos625.Phase

/-!
# The selected phase/profile objective

This small adapter packages the phase entropy term together with the attained
finite profile optimum.  It identifies that package with the selected dual
core which occurs in the logarithmic first-moment reduction.  No asymptotic
estimate, root statement, or chromatic tail conclusion is supplied here.
-/

namespace Erdos625

noncomputable section

/-- The phase entropy term plus the attained finite profile optimum at a real
part count. -/
def profilePhaseObjective (n : ℕ) (parts : ℝ) : ℝ :=
  ((phaseNat n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) +
    profileDualOptimalValue (phaseNat n + 1) (n : ℝ) parts

/-- At nonzero part count, the phase/profile objective is exactly the
phase-and-dual core evaluated at its selected tilt. -/
theorem profilePhaseObjective_eq_selected_core
    (n : ℕ) {parts : ℝ} (hparts : parts ≠ 0) :
    profilePhaseObjective n parts =
      ((phaseNat n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) +
        profileDualUpper (phaseNat n + 1) (n : ℝ) parts
          (profileDualTilt (phaseNat n + 1) ((n : ℝ) / parts)) := by
  unfold profilePhaseObjective
  rw [profileDualOptimalValue_eq_profileDualUpper (phaseNat n + 1) hparts]

#print axioms profilePhaseObjective_eq_selected_core

end

end Erdos625
