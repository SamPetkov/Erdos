import Erdos625.ColoringProfilePhaseRootCenter
import Erdos625.ColoringProfileDeficitTilt
import Mathlib.Tactic

namespace Erdos625

open Set

noncomputable section

set_option autoImplicit false

/-- The deficit-target corridor gives the corresponding size-coordinate
corridor and forces the phase support endpoint to be at least two. -/
theorem phaseDeficitTarget_domain_coordinates
    {n : ℕ} {k : ℝ}
    (hT : profileDeficitTarget (phaseNat n) (n : ℝ) k ∈
      Ioo (-1 : ℝ) ((phaseNat n : ℝ) - 1)) :
    (n : ℝ) / k ∈
        Ioo (1 : ℝ) ((((phaseNat n) + 1 : ℕ) : ℝ)) ∧
      2 ≤ phaseNat n + 1 := by
  rw [Set.mem_Ioo] at hT
  unfold profileDeficitTarget at hT
  obtain ⟨h1, h2⟩ := hT
  have hpos : (0 : ℝ) < (phaseNat n : ℝ) := by linarith
  have hpn : 0 < phaseNat n := by exact_mod_cast hpos
  refine ⟨?_, ?_⟩
  · rw [Set.mem_Ioo]
    push_cast
    constructor <;> linarith
  · omega

end

end Erdos625
