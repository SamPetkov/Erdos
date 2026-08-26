import Erdos625.UnrestrictedDerivativeCorridor
import Erdos625.ProfileCorridorTools
import Mathlib.Tactic

/-!
# Finite unrestricted phase-root corridor

This module supplies the missing finite adapter between the concrete
unrestricted derivative corridor and the later asymptotic root construction.
It exposes the exact `HasDerivAt` statement on the compact manuscript target
corridor, then applies the existing generic symmetric-corridor IVT theorem to
obtain a unique unrestricted root from a center-value bound and a positive
derivative lower bound.

The theorem does not supply the center-value estimate, the corridor radius,
the derivative estimate, or any asymptotic root localization.  In particular,
it does not assume or prove an equivalent of the desired concrete root
asymptotic, the signed root, the chromatic lower tail, partial diagonals,
skeletons, second moments, or the final Erdős statement.
-/

namespace Erdos625

open Set
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Exact derivative of the unrestricted phase objective at every positive
part count whose deficit target lies in the fixed manuscript corridor.  This
retains the full `HasDerivAt` data needed for continuity and IVT arguments. -/
theorem hasDerivAt_unrestrictedPhaseObjective_of_target_mem_admissibilityCorridor
    (n : ℕ) {parts : ℝ}
    (hPhase : 6 ≤ phaseNat n)
    (hparts : 0 < parts)
    (hTarget : profileDeficitTarget (phaseNat n) (n : ℝ) parts ∈
      signedFourAdmissibilityTargetCorridor) :
    HasDerivAt (unrestrictedPhaseObjective n)
      (Real.log
          (profileDualPartition (phaseNat n + 1)
            (profileDualTilt (phaseNat n + 1) ((n : ℝ) / parts))) -
        Real.log parts)
      parts := by
  have hDeficitInterior :
      profileDeficitTarget (phaseNat n) (n : ℝ) parts ∈
        Ioo (-1 : ℝ) ((phaseNat n : ℝ) - 1) := by
    have hBounds := hTarget
    simp only [signedFourAdmissibilityTargetCorridor, mem_Icc] at hBounds
    constructor
    · linarith [hBounds.1]
    · have hPhaseReal : (6 : ℝ) ≤ (phaseNat n : ℝ) := by
        exact_mod_cast hPhase
      linarith [hBounds.2]
  have hSizeInterior :
      (n : ℝ) / parts ∈
        Ioo (1 : ℝ) (((phaseNat n + 1 : ℕ) : ℝ)) := by
    have h :=
      (deficitTarget_mem_Ioo_iff_sizeTarget_mem_Ioo
        (phaseNat n)
        (profileDeficitTarget (phaseNat n) (n : ℝ) parts)).mp
        hDeficitInterior
    convert h using 1 <;> ring
  have hb : 2 ≤ phaseNat n + 1 := by omega
  change HasDerivAt
    (fun k ↦ profileDualOptimalValue (phaseNat n + 1) (n : ℝ) k)
    _ parts
  exact hasDerivAt_profileDualOptimalValue_parts hb hparts hSizeInterior

/-- A concrete center error smaller than the integrated positive derivative
margin gives a unique unrestricted root in the open symmetric corridor.
Admissibility of the complete closed corridor is preserved in the returned
root data. -/
theorem existsUnique_unrestrictedPhaseRoot_of_center_and_deriv_lower
    (n : ℕ) (s0 Delta E D : ℝ)
    (hPhase : 6 ≤ phaseNat n)
    (hDelta : 0 < Delta) (hD : 0 < D)
    (hmargin : E < D * Delta)
    (hcenter : |unrestrictedPhaseObjective n s0| ≤ E)
    (hfeasible : ∀ s ∈ Icc (s0 - Delta) (s0 + Delta),
      0 < s ∧
        profileDeficitTarget (phaseNat n) (n : ℝ) s ∈
          signedFourAdmissibilityTargetCorridor)
    (hderivLower : ∀ s ∈ Ioo (s0 - Delta) (s0 + Delta),
      D ≤ deriv (unrestrictedPhaseObjective n) s) :
    ∃! r : ℝ,
      r ∈ Ioo (s0 - Delta) (s0 + Delta) ∧
        0 < r ∧
        profileDeficitTarget (phaseNat n) (n : ℝ) r ∈
          signedFourAdmissibilityTargetCorridor ∧
        unrestrictedPhaseObjective n r = 0 := by
  let psi : ℝ → ℝ := fun s ↦ -unrestrictedPhaseObjective n s
  have hcont : ContinuousOn psi (Icc (s0 - Delta) (s0 + Delta)) := by
    intro s hs
    have hsData := hfeasible s hs
    exact
      (hasDerivAt_unrestrictedPhaseObjective_of_target_mem_admissibilityCorridor
        n hPhase hsData.1 hsData.2).continuousAt.neg.continuousWithinAt
  have hdiff : DifferentiableOn ℝ psi (Ioo (s0 - Delta) (s0 + Delta)) := by
    intro s hs
    have hsIcc : s ∈ Icc (s0 - Delta) (s0 + Delta) :=
      Ioo_subset_Icc_self hs
    have hsData := hfeasible s hsIcc
    exact
      (hasDerivAt_unrestrictedPhaseObjective_of_target_mem_admissibilityCorridor
        n hPhase hsData.1 hsData.2).neg.differentiableAt.differentiableWithinAt
  have hupper : ∀ s ∈ Ioo (s0 - Delta) (s0 + Delta),
      deriv psi s ≤ -D := by
    intro s hs
    have hsIcc : s ∈ Icc (s0 - Delta) (s0 + Delta) :=
      Ioo_subset_Icc_self hs
    have hsData := hfeasible s hsIcc
    have hderiv :=
      (hasDerivAt_unrestrictedPhaseObjective_of_target_mem_admissibilityCorridor
        n hPhase hsData.1 hsData.2).neg
    change deriv (-unrestrictedPhaseObjective n) s ≤ -D
    rw [hderiv.deriv]
    exact neg_le_neg (hderivLower s hs)
  have hcenterPsi : |psi s0| ≤ E := by
    simpa [psi] using hcenter
  obtain ⟨r, hr, hunique⟩ :=
    existsUnique_root_mem_corridor_of_center_bound_deriv_upper
      hDelta hD hmargin hcenterPsi hcont hdiff hupper
  refine ⟨r, ⟨hr.1, ?_⟩, ?_⟩
  · have hrIcc : r ∈ Icc (s0 - Delta) (s0 + Delta) :=
      Ioo_subset_Icc_self hr.1
    have hrData := hfeasible r hrIcc
    exact ⟨hrData.1, hrData.2, by simpa [psi] using hr.2⟩
  · intro y hy
    apply hunique y
    exact ⟨hy.1, by simpa [psi] using hy.2.2.2⟩

#print axioms hasDerivAt_unrestrictedPhaseObjective_of_target_mem_admissibilityCorridor
#print axioms existsUnique_unrestrictedPhaseRoot_of_center_and_deriv_lower

end

end Erdos625
