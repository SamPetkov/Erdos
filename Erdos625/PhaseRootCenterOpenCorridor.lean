import Erdos625.ColoringProfilePhaseRootCenter
import Erdos625.PhaseEstimates
import Mathlib.Tactic

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

/--
Eventually the exact deficit target at the reference center lies in the open
finite-support domain needed by the derivative formula.
-/
theorem eventually_phaseRootCenter_deficitTarget_mem_open :
    ∀ᶠ n : ℕ in atTop,
      profileDeficitTarget (phaseNat n) (n : ℝ) (phaseRootCenter n) ∈
        Ioo (-1 : ℝ) ((phaseNat n : ℝ) - 1) := by
  have hqLower : (1 / 2 : ℝ) < q :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hqUpper : q < 2 := Real.log_two_lt_d9.trans (by norm_num)
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_five_lt_phaseNat] with n hcorr hfive
  obtain ⟨-, -, hmem⟩ := hcorr
  rw [Set.mem_Icc] at hmem
  obtain ⟨hlo, hhi⟩ := hmem
  have h1 : (1 : ℝ) < 2 / q := by rw [lt_div_iff₀ q_pos]; linarith
  have h2 : 2 / q < 4 := by rw [div_lt_iff₀ q_pos]; linarith
  have hsixR : (6 : ℝ) ≤ (phaseNat n : ℝ) := by
    have hsix : (6 : ℕ) ≤ phaseNat n := hfive
    exact_mod_cast hsix
  rw [profileDeficitTarget, Set.mem_Ioo]
  refine ⟨by linarith, by linarith⟩

end

end Erdos625
