import Erdos625.ProfileCorridorTools
import Erdos625.RootSeparationRounding
import Erdos625.SignedFourSizeObjective
import Mathlib.Tactic

/-!
# Finite objective bounds at the rounded root midpoint

This module proves the deterministic calculus seam needed before the
asymptotic E625-10 objective assembly.  If a function vanishes at the left
root and its derivative is trapped on the root corridor, then its value at

`ceil ((rCo + rPlus) / 2)`

is trapped by the corresponding derivative bounds times one half of the root
gap, with exactly one additional unit in the upper bound for the ceiling.

The final theorem specializes the generic statement to
`phaseSignedFourSizeObjective`.  It assumes root, feasibility, and derivative
corridor data, but no first-moment estimate and no root-gap asymptotic.

No chromatic lower tail, partial diagonal, skeleton, second moment, or final
Erdős statement is used.
-/

namespace Erdos625

open Set
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- A pointwise derivative upper bound integrates to the corresponding finite
increment upper bound. -/
theorem sub_le_derivative_upper_bound_mul_sub
    {f : ℝ → ℝ} {a b s : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : DifferentiableOn ℝ f (Ioo a b))
    (hupper : ∀ x ∈ Ioo a b, deriv f x ≤ s) :
    f b - f a ≤ s * (b - a) := by
  have hconv : Convex ℝ (Icc a b) := convex_Icc a b
  have hint : interior (Icc a b) = Ioo a b := interior_Icc
  refine Convex.image_sub_le_mul_sub_of_deriv_le hconv hcont ?_ ?_
    a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab) hab
  · rw [hint]
    exact hdiff
  · intro x hx
    rw [hint] at hx
    exact hupper x hx

/-- Exact displacement bounds for the manuscript ceiling midpoint. -/
theorem rootCochromaticIndex_cast_sub_root_bounds
    (rCo rPlus : ℝ) :
    (rPlus - rCo) / 2 ≤
        ((rootCochromaticIndex rCo rPlus : ℤ) : ℝ) - rCo ∧
    ((rootCochromaticIndex rCo rPlus : ℤ) : ℝ) - rCo ≤
        (rPlus - rCo) / 2 + 1 := by
  unfold rootCochromaticIndex
  norm_num
  constructor
  · linarith [Int.le_ceil ((rCo + rPlus) / 2)]
  · linarith [Int.ceil_lt_add_one ((rCo + rPlus) / 2)]

/-- A root gap of at least two places the ceiling midpoint inside the full
closed root corridor. -/
theorem rootCochromaticIndex_cast_mem_Icc
    (rCo rPlus : ℝ) (hGap : 2 ≤ rPlus - rCo) :
    ((rootCochromaticIndex rCo rPlus : ℤ) : ℝ) ∈ Icc rCo rPlus := by
  have hBounds := rootCochromaticIndex_cast_sub_root_bounds rCo rPlus
  constructor
  · linarith [hBounds.1]
  · linarith [hBounds.2]

/-- Finite objective envelope at the rounded root midpoint.  The only ceiling
loss is the explicit `+ 1` in the upper displacement. -/
theorem value_at_rootCochromaticIndex_bounds
    {F : ℝ → ℝ} {rCo rPlus slopeLower slopeUpper : ℝ}
    (hGap : 2 ≤ rPlus - rCo)
    (hSlopeLower : 0 ≤ slopeLower)
    (hSlopeUpper : 0 ≤ slopeUpper)
    (hCont : ContinuousOn F (Icc rCo rPlus))
    (hDiff : DifferentiableOn ℝ F (Ioo rCo rPlus))
    (hDerivLower : ∀ x ∈ Ioo rCo rPlus,
      slopeLower ≤ deriv F x)
    (hDerivUpper : ∀ x ∈ Ioo rCo rPlus,
      deriv F x ≤ slopeUpper)
    (hRoot : F rCo = 0) :
    slopeLower * ((rPlus - rCo) / 2) ≤
        F (((rootCochromaticIndex rCo rPlus : ℤ) : ℝ)) ∧
    F (((rootCochromaticIndex rCo rPlus : ℤ) : ℝ)) ≤
        slopeUpper * ((rPlus - rCo) / 2 + 1) := by
  let midpoint : ℝ :=
    ((rootCochromaticIndex rCo rPlus : ℤ) : ℝ)
  have hMid := rootCochromaticIndex_cast_mem_Icc rCo rPlus hGap
  have hMidLe : rCo ≤ midpoint := hMid.1
  have hClosedSubset : Icc rCo midpoint ⊆ Icc rCo rPlus := by
    intro x hx
    exact ⟨hx.1, hx.2.trans hMid.2⟩
  have hOpenSubset : Ioo rCo midpoint ⊆ Ioo rCo rPlus := by
    intro x hx
    exact ⟨hx.1, hx.2.trans_le hMid.2⟩
  have hContMid : ContinuousOn F (Icc rCo midpoint) :=
    hCont.mono hClosedSubset
  have hDiffMid : DifferentiableOn ℝ F (Ioo rCo midpoint) :=
    hDiff.mono hOpenSubset
  have hLowerIncrement :
      slopeLower * (midpoint - rCo) ≤ F midpoint - F rCo :=
    derivative_lower_bound_mul_sub_le_sub hMidLe hContMid hDiffMid
      (fun x hx ↦ hDerivLower x (hOpenSubset hx))
  have hUpperIncrement :
      F midpoint - F rCo ≤ slopeUpper * (midpoint - rCo) :=
    sub_le_derivative_upper_bound_mul_sub hMidLe hContMid hDiffMid
      (fun x hx ↦ hDerivUpper x (hOpenSubset hx))
  have hDisplacement :=
    rootCochromaticIndex_cast_sub_root_bounds rCo rPlus
  constructor
  · calc
      slopeLower * ((rPlus - rCo) / 2) ≤
          slopeLower * (midpoint - rCo) :=
        mul_le_mul_of_nonneg_left hDisplacement.1 hSlopeLower
      _ ≤ F midpoint - F rCo := hLowerIncrement
      _ = F midpoint := by rw [hRoot, sub_zero]
  · calc
      F midpoint = F midpoint - F rCo := by rw [hRoot, sub_zero]
      _ ≤ slopeUpper * (midpoint - rCo) := hUpperIncrement
      _ ≤ slopeUpper * ((rPlus - rCo) / 2 + 1) :=
        mul_le_mul_of_nonneg_left hDisplacement.2 hSlopeUpper

/-- Manuscript-facing specialization to the signed finite four-size objective.
The feasibility hypothesis is exactly what supplies continuity and
differentiability throughout the root corridor. -/
theorem phaseSignedFourSizeObjective_at_rootCochromaticIndex_bounds
    (n : ℕ) (rCo rPlus slopeLower slopeUpper : ℝ)
    (hGap : 2 ≤ rPlus - rCo)
    (hSlopeLower : 0 ≤ slopeLower)
    (hSlopeUpper : 0 ≤ slopeUpper)
    (hFeasible : ∀ s ∈ Icc rCo rPlus,
      0 < s ∧ fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : ℝ) 5)
    (hDerivLower : ∀ s ∈ Ioo rCo rPlus,
      slopeLower ≤ signedFourSizeObjectiveDerivative n (phaseNat n) s)
    (hDerivUpper : ∀ s ∈ Ioo rCo rPlus,
      signedFourSizeObjectiveDerivative n (phaseNat n) s ≤ slopeUpper)
    (hRoot : phaseSignedFourSizeObjective n rCo = 0) :
    slopeLower * ((rPlus - rCo) / 2) ≤
        phaseSignedFourSizeObjective n
          (((rootCochromaticIndex rCo rPlus : ℤ) : ℝ)) ∧
    phaseSignedFourSizeObjective n
          (((rootCochromaticIndex rCo rPlus : ℤ) : ℝ)) ≤
        slopeUpper * ((rPlus - rCo) / 2 + 1) := by
  have hCont : ContinuousOn (phaseSignedFourSizeObjective n)
      (Icc rCo rPlus) := by
    intro s hs
    exact (continuousAt_phaseSignedFourSizeObjective n
      (hFeasible s hs).1 (hFeasible s hs).2).continuousWithinAt
  have hDiff : DifferentiableOn ℝ (phaseSignedFourSizeObjective n)
      (Ioo rCo rPlus) := by
    intro s hs
    have hsClosed : s ∈ Icc rCo rPlus := Ioo_subset_Icc_self hs
    exact (hasDerivAt_phaseSignedFourSizeObjective n
      (hFeasible s hsClosed).1
      (hFeasible s hsClosed).2).differentiableAt.differentiableWithinAt
  have hLower : ∀ s ∈ Ioo rCo rPlus,
      slopeLower ≤ deriv (phaseSignedFourSizeObjective n) s := by
    intro s hs
    have hsClosed : s ∈ Icc rCo rPlus := Ioo_subset_Icc_self hs
    have hDeriv := hasDerivAt_phaseSignedFourSizeObjective n
      (hFeasible s hsClosed).1 (hFeasible s hsClosed).2
    rw [hDeriv.deriv]
    exact hDerivLower s hs
  have hUpper : ∀ s ∈ Ioo rCo rPlus,
      deriv (phaseSignedFourSizeObjective n) s ≤ slopeUpper := by
    intro s hs
    have hsClosed : s ∈ Icc rCo rPlus := Ioo_subset_Icc_self hs
    have hDeriv := hasDerivAt_phaseSignedFourSizeObjective n
      (hFeasible s hsClosed).1 (hFeasible s hsClosed).2
    rw [hDeriv.deriv]
    exact hDerivUpper s hs
  exact value_at_rootCochromaticIndex_bounds hGap hSlopeLower hSlopeUpper
    hCont hDiff hLower hUpper hRoot

#print axioms sub_le_derivative_upper_bound_mul_sub
#print axioms rootCochromaticIndex_cast_sub_root_bounds
#print axioms rootCochromaticIndex_cast_mem_Icc
#print axioms value_at_rootCochromaticIndex_bounds
#print axioms phaseSignedFourSizeObjective_at_rootCochromaticIndex_bounds

end

end Erdos625
