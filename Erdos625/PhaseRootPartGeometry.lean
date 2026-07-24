import Erdos625.ColoringProfilePhaseRootCenter
import Erdos625.PhaseAsymptotic
import Mathlib.Tactic

namespace Erdos625

open Filter Asymptotics

noncomputable section

set_option autoImplicit false

theorem phaseRootS0_isEquivalent_scaled_logOrder :
    phaseRootS0 ~[atTop] (fun n : ℕ ↦ (2 / q) * logOrder n) := by
  have hScaleNe : (2 / q : ℝ) ≠ 0 :=
    div_ne_zero (by norm_num) q_ne_zero
  have hScaled :
      (fun n : ℕ ↦ (2 / q) * phaseS n) ~[atTop]
        (fun n : ℕ ↦ (2 / q) * logOrder n) :=
    (IsEquivalent.refl : (fun _n : ℕ ↦ (2 / q : ℝ)) ~[atTop]
      (fun _n : ℕ ↦ (2 / q : ℝ))).mul phaseS_isEquivalent_logOrder
  have hConstant :
      (fun _n : ℕ ↦ (-2 / q : ℝ)) =o[atTop]
        (fun n : ℕ ↦ (2 / q) * logOrder n) := by
    have h :
        (fun _n : ℕ ↦ (-2 / q : ℝ)) =o[atTop]
          (fun n : ℕ ↦ logOrder n) := by
      simpa only [Function.comp_def, id_eq] using
        (isLittleO_const_id_atTop (-2 / q : ℝ)).comp_tendsto
          tendsto_logOrder_atTop
    exact h.const_mul_right hScaleNe
  have hSum := hScaled.add_isLittleO hConstant
  apply hSum.congr'
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    change (2 / q * phaseS n + (-2 / q) - 2 / q * logOrder n) =
      phaseRootS0 n - 2 / q * logOrder n
    rw [phaseRootS0, alphaZero_eq_two_phaseS_div_q_add_one hn]
    ring
  · exact EventuallyEq.rfl

end

end Erdos625
