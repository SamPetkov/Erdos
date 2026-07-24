import Erdos625.SignedFourSizeObjective
import Erdos625.ProfileCorridorTools
import Mathlib.Tactic

namespace Erdos625

open Set
open scoped Topology

noncomputable section

/-- A signed four-size root follows from a concrete center-value error,
admissibility of the full corridor, and a positive derivative lower bound.
The quantitative center and derivative estimates are hypotheses, not supplied
by this finite bridge. -/
theorem existsUnique_phaseSignedFourSizeRoot_of_center_and_deriv_lower
    (n : Nat) (s0 Delta E D : Real)
    (hDelta : 0 < Delta) (hD : 0 < D)
    (hmargin : E < D * Delta)
    (hcenter : |phaseSignedFourSizeObjective n s0| ≤ E)
    (hfeasible : ∀ s ∈ Icc (s0 - Delta) (s0 + Delta),
      0 < s ∧
        fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : Real) 5)
    (hderivLower : ∀ s ∈ Ioo (s0 - Delta) (s0 + Delta),
      D ≤ signedFourSizeObjectiveDerivative n (phaseNat n) s) :
    ∃! r : Real,
      r ∈ Ioo (s0 - Delta) (s0 + Delta) ∧
        IsPhaseSignedFourSizeRoot n r := by
  let psi : Real → Real := fun s => -phaseSignedFourSizeObjective n s
  have hcont : ContinuousOn psi (Icc (s0 - Delta) (s0 + Delta)) := by
    intro s hs
    exact (continuousAt_phaseSignedFourSizeObjective n
      (hfeasible s hs).1 (hfeasible s hs).2).neg.continuousWithinAt
  have hdiff : DifferentiableOn Real psi (Ioo (s0 - Delta) (s0 + Delta)) := by
    intro s hs
    have hsIcc : s ∈ Icc (s0 - Delta) (s0 + Delta) :=
      Ioo_subset_Icc_self hs
    exact (hasDerivAt_phaseSignedFourSizeObjective n
      (hfeasible s hsIcc).1 (hfeasible s hsIcc).2).neg.differentiableAt.differentiableWithinAt
  have hupper : ∀ s ∈ Ioo (s0 - Delta) (s0 + Delta), deriv psi s ≤ -D := by
    intro s hs
    have hsIcc : s ∈ Icc (s0 - Delta) (s0 + Delta) :=
      Ioo_subset_Icc_self hs
    have hderiv := (hasDerivAt_phaseSignedFourSizeObjective n
      (hfeasible s hsIcc).1 (hfeasible s hsIcc).2).neg
    change deriv (-phaseSignedFourSizeObjective n) s ≤ -D
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
    have hradmissible := hfeasible r hrIcc
    exact ⟨hradmissible.1, hradmissible.2, by
      simpa [psi, phaseSignedFourSizeObjective] using hr.2⟩
  · intro y hy
    apply hunique y
    exact ⟨hy.1, by simpa [psi, IsPhaseSignedFourSizeRoot,
      IsSignedFourSizeRoot, phaseSignedFourSizeObjective] using hy.2.2.2⟩

end

end Erdos625
