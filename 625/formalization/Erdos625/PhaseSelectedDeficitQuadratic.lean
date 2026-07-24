import Erdos625.PhaseRootSelectedDeficitBound
import Erdos625.PhaseEstimates
import Mathlib.Tactic

namespace Erdos625

open Filter

noncomputable section

set_option autoImplicit false

/--
The selected deficit contribution is eventually negligible compared with the
positive quadratic phase scale, in the explicit form needed by later
assemblies.
-/
theorem eventually_abs_phaseRootSelectedDeficitTerm_le_quadratic :
    ∀ᶠ n : ℕ in atTop,
      |phaseRootSelectedDeficitTerm n| ≤
        q / 16 * (phaseNat n : ℝ) ^ 2 := by
  obtain ⟨C, hC⟩ := (phaseRootSelectedDeficitTerm_isBigO_one).bound
  have hPhaseTop : Tendsto (fun n : ℕ ↦ (phaseNat n : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ tendsto_logOrder_atTop
    filter_upwards [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder]
      with n hn
    exact hn.1
  have hQuadTop :
      Tendsto (fun n : ℕ ↦ q / 16 * (phaseNat n : ℝ) ^ 2) atTop atTop := by
    apply Tendsto.const_mul_atTop (div_pos q_pos (by norm_num))
    exact (tendsto_pow_atTop (by norm_num)).comp hPhaseTop
  filter_upwards [hC, hQuadTop.eventually_ge_atTop C] with n hn hge
  simp only [Real.norm_eq_abs, norm_one, mul_one] at hn
  exact hn.trans hge

end

end Erdos625
