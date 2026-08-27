import Erdos625.PhaseSignedFourSizeLogLogCorridorDerivativeLower
import Erdos625.PhaseSignedFourSizeRootCorridor
import Mathlib.Tactic

/-!
# Actual signed four-size root in a logarithmic corridor

This module combines the normalized reference-center bound, the enlarged
corridor domain, and the uniform positive derivative.  It chooses one fixed
corridor width and obtains the actual unique signed finite-four root.  It does
not compare this root with the unrestricted root or perform integer rounding.
-/

namespace Erdos625

open Filter Set Asymptotics

noncomputable section

set_option autoImplicit false

/-- There is a fixed positive logarithmic-corridor coefficient which
eventually contains the unique actual signed finite-four phase root. -/
theorem exists_pos_eventually_existsUnique_phaseSignedFourSizeRoot_logLogCorridor :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ n : Nat in atTop,
        ∃! r : Real,
          r ∈ Ioo
              (phaseRootCenter n -
                C * logLogOrder n * phaseRootGapRadius n)
              (phaseRootCenter n +
                C * logLogOrder n * phaseRootGapRadius n) ∧
            IsPhaseSignedFourSizeRoot n r := by
  obtain ⟨B, hBpos, hB⟩ :=
    phaseSignedFourSizeObjective_referenceCenter_div_isBigO_logLogOrder.exists_pos
  let C : Real := 16 * B / q
  have hCpos : 0 < C := by
    dsimp [C]
    exact div_pos (mul_pos (by norm_num) hBpos) q_pos
  refine ⟨C, hCpos, ?_⟩
  have hdomain :=
    eventually_phaseRootLogLogCorridor_fourSize_domain C hCpos.le
  have hderiv :=
    eventually_signedFourSizeObjectiveDerivative_logLogCorridor_lower C hCpos.le
  have hLogLogPos : ∀ᶠ n : Nat in atTop, 0 < logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_gt_atTop 0
  filter_upwards
    [hB.bound, hdomain, hderiv,
      eventually_phaseRoot_domain_pos_and_target_corridor,
      eventually_five_lt_phaseNat, hLogLogPos] with
      n hcenterBound hdomainN hderivN hcenterDomain hphase hLogLog
  have hcenterPos : 0 < phaseRootCenter n := by
    exact div_pos
      (by exact_mod_cast (lt_trans Nat.zero_lt_one hcenterDomain.1.1))
      hcenterDomain.2.1
  have hphasePos : 0 < (phaseNat n : Real) := by
    have hphaseNatPos : 0 < phaseNat n := by omega
    exact_mod_cast hphaseNatPos
  have hgapPos : 0 < phaseRootGapRadius n := by
    rw [phaseRootGapRadius]
    exact div_pos hcenterPos (sq_pos_of_pos hphasePos)
  let Delta : Real := C * logLogOrder n * phaseRootGapRadius n
  let E : Real := B * logLogOrder n * phaseRootCenter n
  let D : Real := q / 8 * (phaseNat n : Real) ^ 2
  have hDelta : 0 < Delta := by
    dsimp [Delta]
    positivity
  have hD : 0 < D := by
    dsimp [D]
    exact mul_pos (div_pos q_pos (by norm_num)) (sq_pos_of_pos hphasePos)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hLogLog] at hcenterBound
  have hcenterAbs :
      |phaseSignedFourSizeObjective n (phaseRootCenter n)| ≤ E := by
    dsimp [E]
    calc
      |phaseSignedFourSizeObjective n (phaseRootCenter n)| =
          |phaseSignedFourSizeObjective n (phaseRootCenter n) /
            phaseRootCenter n| * phaseRootCenter n := by
        rw [abs_div, abs_of_pos hcenterPos,
          div_mul_cancel₀ _ hcenterPos.ne']
      _ ≤ (B * logLogOrder n) * phaseRootCenter n :=
        mul_le_mul_of_nonneg_right hcenterBound hcenterPos.le
  have hEpos : 0 < E := by
    dsimp [E]
    positivity
  have hproduct : D * Delta = 2 * E := by
    dsimp [D, Delta, E, C]
    rw [phaseRootGapRadius]
    field_simp [q_ne_zero, hphasePos.ne']
    ; ring
  have hmargin : E < D * Delta := by
    rw [hproduct]
    linarith
  exact existsUnique_phaseSignedFourSizeRoot_of_center_and_deriv_lower
    n (phaseRootCenter n) Delta E D hDelta hD hmargin hcenterAbs
      (by simpa [Delta] using hdomainN)
      (by
        intro s hs
        exact hderivN s (Ioo_subset_Icc_self (by simpa [Delta] using hs)))

end

#print axioms exists_pos_eventually_existsUnique_phaseSignedFourSizeRoot_logLogCorridor

end Erdos625
