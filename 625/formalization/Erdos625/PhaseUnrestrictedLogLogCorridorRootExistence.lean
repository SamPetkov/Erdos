import Erdos625.PhaseRootObjectiveCenterBound
import Erdos625.PhaseUnrestrictedLogLogCorridorDerivativeLower
import Erdos625.PhaseSignedFourSizeLogLogCorridorDomain
import Erdos625.ProfileCorridorTools
import Mathlib.Tactic

/-!
# Unrestricted phase root in a logarithmic-logarithmic corridor

This module combines the unrestricted objective's normalized center bound,
the enlarged-corridor domain, and the uniform positive derivative. It proves
existence and uniqueness of the unrestricted zero only. Root displacement,
comparison with the signed finite-four root, and integer selection remain
separate obligations.
-/

namespace Erdos625

open Filter Set Asymptotics

noncomputable section

set_option autoImplicit false

/-- Local bridge from corridor control and a positive derivative to a unique
zero of the raw unrestricted phase objective. -/
private theorem existsUnique_unrestrictedPhaseObjective_zero_of_center_and_deriv_lower
    (n : Nat) (s0 Delta E D : Real)
    (hDelta : 0 < Delta) (hD : 0 < D)
    (hmargin : E < D * Delta)
    (hphase : 5 < phaseNat n)
    (hcenter : |unrestrictedPhaseObjective n s0| ≤ E)
    (hfeasible : ∀ s ∈ Icc (s0 - Delta) (s0 + Delta),
      0 < s ∧
        fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : Real) 5)
    (hderivLower : ∀ s ∈ Ioo (s0 - Delta) (s0 + Delta),
      D ≤ deriv (unrestrictedPhaseObjective n) s) :
    ∃! r : Real,
      r ∈ Ioo (s0 - Delta) (s0 + Delta) ∧
        unrestrictedPhaseObjective n r = 0 := by
  have hb : 2 ≤ phaseNat n + 1 := by omega
  have hsix : (6 : Real) ≤ (phaseNat n : Real) := by
    have h : (6 : Nat) ≤ phaseNat n := hphase
    exact_mod_cast h
  have hkey : ∀ s ∈ Icc (s0 - Delta) (s0 + Delta),
      HasDerivAt (unrestrictedPhaseObjective n)
        (Real.log (profileDualPartition (phaseNat n + 1)
            (profileDualTilt (phaseNat n + 1) ((n : Real) / s))) -
          Real.log s) s := by
    intro s hs
    obtain ⟨hspos, htar⟩ := hfeasible s hs
    rw [fourSizeTarget, mem_Ioo] at htar
    have hcast : (((phaseNat n + 1 : Nat)) : Real) = (phaseNat n : Real) + 1 := by
      push_cast
      ring
    have htarget : (n : Real) / s ∈
        Set.Ioo (1 : Real) (((phaseNat n + 1 : Nat)) : Real) := by
      rw [Set.mem_Ioo, hcast]
      exact ⟨by linarith [htar.2], by linarith [htar.1]⟩
    exact hasDerivAt_profileDualOptimalValue_parts hb hspos htarget
  let psi : Real → Real := fun s => -unrestrictedPhaseObjective n s
  have hcont : ContinuousOn psi (Icc (s0 - Delta) (s0 + Delta)) := by
    intro s hs
    exact ((hkey s hs).continuousAt.neg).continuousWithinAt
  have hdiff : DifferentiableOn Real psi (Ioo (s0 - Delta) (s0 + Delta)) := by
    intro s hs
    exact
      ((hkey s (Ioo_subset_Icc_self hs)).neg.differentiableAt).differentiableWithinAt
  have hupper : ∀ s ∈ Ioo (s0 - Delta) (s0 + Delta), deriv psi s ≤ -D := by
    intro s hs
    have hd := hkey s (Ioo_subset_Icc_self hs)
    have hlow := hderivLower s hs
    rw [hd.deriv] at hlow
    have hdn : HasDerivAt psi
        (-(Real.log (profileDualPartition (phaseNat n + 1)
            (profileDualTilt (phaseNat n + 1) ((n : Real) / s))) -
          Real.log s)) s := hd.neg
    rw [hdn.deriv]
    linarith
  have hcenterPsi : |psi s0| ≤ E := by
    simpa [psi] using hcenter
  obtain ⟨r, hr, hunique⟩ :=
    existsUnique_root_mem_corridor_of_center_bound_deriv_upper
      hDelta hD hmargin hcenterPsi hcont hdiff hupper
  refine ⟨r, ⟨hr.1, ?_⟩, ?_⟩
  · have h := hr.2
    simp only [psi, neg_eq_zero] at h
    exact h
  · intro y hy
    refine hunique y ⟨hy.1, ?_⟩
    simp only [psi, neg_eq_zero]
    exact hy.2

/-- There is a fixed positive logarithmic-logarithmic corridor coefficient
which eventually contains the unique zero of the unrestricted phase
objective. -/
theorem exists_pos_eventually_existsUnique_unrestrictedPhaseObjective_zero_logLogCorridor :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ n : Nat in atTop,
        ∃! r : Real,
          r ∈ Ioo
              (phaseRootCenter n -
                C * logLogOrder n * phaseRootGapRadius n)
              (phaseRootCenter n +
                C * logLogOrder n * phaseRootGapRadius n) ∧
            unrestrictedPhaseObjective n r = 0 := by
  obtain ⟨B, hBpos, hB⟩ :=
    unrestrictedPhaseObjective_center_div_isBigO_logLogOrder.exists_pos
  let C : Real := 16 * B / q
  have hCpos : 0 < C := by
    dsimp [C]
    exact div_pos (mul_pos (by norm_num) hBpos) q_pos
  refine ⟨C, hCpos, ?_⟩
  have hdomain :=
    eventually_phaseRootLogLogCorridor_fourSize_domain C hCpos.le
  have hderiv :=
    eventually_unrestrictedPhaseObjective_deriv_logLogCorridor_lower C hCpos.le
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
      |unrestrictedPhaseObjective n (phaseRootCenter n)| ≤ E := by
    dsimp [E]
    calc
      |unrestrictedPhaseObjective n (phaseRootCenter n)| =
          |unrestrictedPhaseObjective n (phaseRootCenter n) /
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
    ring
  have hmargin : E < D * Delta := by
    rw [hproduct]
    linarith
  exact existsUnique_unrestrictedPhaseObjective_zero_of_center_and_deriv_lower
    n (phaseRootCenter n) Delta E D hDelta hD hmargin hphase hcenterAbs
      (by simpa [Delta] using hdomainN)
      (by
        intro s hs
        exact hderivN s (Ioo_subset_Icc_self (by simpa [Delta] using hs)))

end

end Erdos625
