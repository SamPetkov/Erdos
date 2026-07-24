import Erdos625.PhaseRootScalarBound
import Erdos625.PhaseRootDisplacementScale
import Mathlib.Tactic

namespace Erdos625

open Filter Asymptotics

noncomputable section

set_option autoImplicit false

/-- The scalar correction, after division by the quadratic slope scale, is
negligible relative to the manuscript gap scale. -/
theorem phaseRootScalarTerm_div_phaseNat_sq_isLittleO_gapScale :
    (fun n : ℕ ↦ phaseRootScalarTerm n / (phaseNat n : ℝ) ^ 2) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) / (logOrder n) ^ 3) := by
  have h1 : phaseRootScalarTerm =O[atTop] logLogOrder :=
    phaseRootScalarTerm_isBigO_logLogOrder
  have hPhaseSq : (fun n : ℕ ↦ (phaseNat n : ℝ) ^ 2) =Θ[atTop]
      (fun n : ℕ ↦ (logOrder n) ^ 2) := phaseNat_isTheta_logOrder.pow 2
  have hFG : (fun n : ℕ ↦ phaseRootScalarTerm n * ((phaseNat n : ℝ) ^ 2)⁻¹)
      =O[atTop] (fun n : ℕ ↦ logLogOrder n * ((logOrder n) ^ 2)⁻¹) :=
    h1.mul hPhaseSq.inv.isBigO
  have hlogsq : (fun n : ℕ ↦ logOrder n * logOrder n) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
    have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [logOrder, Function.comp_def, pow_two] using h
  have htrans : (fun n : ℕ ↦ logLogOrder n * logOrder n) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) :=
    (logLogOrder_isLittleO_logOrder.mul_isBigO
      (isBigO_refl (fun n : ℕ ↦ logOrder n) atTop)).trans hlogsq
  have hmul := htrans.mul_isBigO
    (isBigO_refl (fun n : ℕ ↦ ((logOrder n) ^ 3)⁻¹) atTop)
  have hG : (fun n : ℕ ↦ logLogOrder n * ((logOrder n) ^ 2)⁻¹) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) * ((logOrder n) ^ 3)⁻¹) := by
    refine hmul.congr' ?_ EventuallyEq.rfl
    filter_upwards [tendsto_logOrder_atTop.eventually_gt_atTop (0 : ℝ)] with n hlog
    have hne : logOrder n ≠ 0 := ne_of_gt hlog
    field_simp
  have hfinal :
      (fun n : ℕ ↦ phaseRootScalarTerm n * ((phaseNat n : ℝ) ^ 2)⁻¹) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ) * ((logOrder n) ^ 3)⁻¹) :=
    hFG.trans_isLittleO hG
  simpa only [div_eq_mul_inv] using hfinal

end

end Erdos625
