import Erdos625.InverseConvergenceTools
import Erdos625.MeanInversionTools

/-!
# The selected tilt of the extended Gaussian profile

This module turns unique inversion of the limiting deficit mean into a total
selector.  On the genuine parameter range `0 < a` and `-1 < target`, the
selector is the unique tilt having the prescribed mean; outside that range it
is defined to be zero.

The second part records the compact quantitative input needed for inverse
convergence.  In particular, it proves continuity and a positive compact
lower bound for the limiting variance, then integrates that derivative bound
to obtain a uniform lower separation for the limiting mean.  Thus no inverse
modulus is inferred from strict monotonicity alone.
-/

namespace Erdos625

open Set
open scoped Topology

noncomputable section

/-! ## A total limiting selector -/

/-- The selected limiting tilt.  It is the unique inverse of the extended
Gaussian mean when `0 < a` and `-1 < target`, and is zero otherwise. -/
noncomputable def extendedGaussianTilt (a target : ℝ) : ℝ :=
  if h : 0 < a ∧ -1 < target then
    Classical.choose (existsUnique_extendedGaussianMean_eq h.1 h.2)
  else
    0

/-- On the interior target range, the total selector realizes the prescribed
limiting mean. -/
theorem extendedGaussianMean_extendedGaussianTilt
    {a target : ℝ} (ha : 0 < a) (htarget : -1 < target) :
    extendedGaussianMean a (extendedGaussianTilt a target) = target := by
  rw [extendedGaussianTilt, dif_pos ⟨ha, htarget⟩]
  exact (Classical.choose_spec
    (existsUnique_extendedGaussianMean_eq ha htarget)).1

/-- On the interior target range, any tilt realizing the target is the total
selected limiting tilt. -/
theorem eq_extendedGaussianTilt_of_extendedGaussianMean_eq
    {a target lambda : ℝ} (ha : 0 < a) (htarget : -1 < target)
    (hmean : extendedGaussianMean a lambda = target) :
    lambda = extendedGaussianTilt a target := by
  exact (strictMono_extendedGaussianMean a ha).injective
    (hmean.trans
      (extendedGaussianMean_extendedGaussianTilt ha htarget).symm)

/-- The selected limiting tilt is the unique solution of the limiting mean
equation on the interior target range. -/
theorem existsUnique_extendedGaussianTilt
    {a target : ℝ} (ha : 0 < a) (htarget : -1 < target) :
    ∃! lambda : ℝ,
      extendedGaussianMean a lambda = target := by
  refine ⟨extendedGaussianTilt a target,
    extendedGaussianMean_extendedGaussianTilt ha htarget, ?_⟩
  intro lambda hmean
  exact eq_extendedGaussianTilt_of_extendedGaussianMean_eq
    ha htarget hmean

/-! ## Compact trapping of the limiting selector -/

/-- Every compact target interval strictly above `-1` has one ordered tilt
bracket that traps all selected limiting tilts. -/
theorem exists_ordered_extendedGaussianTilt_bracket
    {a A B : ℝ} (ha : 0 < a) (hA : -1 < A) (hAB : A ≤ B) :
    ∃ L R : ℝ, L < R ∧
      extendedGaussianMean a L < A ∧
      B < extendedGaussianMean a R ∧
      ∀ target ∈ Icc A B,
        extendedGaussianTilt a target ∈ Ioo L R := by
  obtain ⟨L, R, hLR, hleft, hright⟩ :=
    exists_ordered_extendedGaussianMean_bracket ha hA hAB
  refine ⟨L, R, hLR, hleft, hright, ?_⟩
  intro target htarget
  have htargetInterior : -1 < target := hA.trans_le htarget.1
  have hroot :=
    extendedGaussianMean_extendedGaussianTilt ha htargetInterior
  constructor
  · apply (strictMono_extendedGaussianMean a ha).lt_iff_lt.mp
    rw [hroot]
    exact hleft.trans_le htarget.1
  · apply (strictMono_extendedGaussianMean a ha).lt_iff_lt.mp
    rw [hroot]
    exact htarget.2.trans_lt hright

/-- Symmetric compact trapping, convenient for uniform convergence on a
closed parameter interval. -/
theorem exists_abs_extendedGaussianTilt_le_on_compact
    {a A B : ℝ} (ha : 0 < a) (hA : -1 < A) (hAB : A ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ target ∈ Icc A B,
        |extendedGaussianTilt a target| ≤ M := by
  obtain ⟨L, R, _hLR, _hleft, _hright, htrap⟩ :=
    exists_ordered_extendedGaussianTilt_bracket ha hA hAB
  refine ⟨max |L| |R|,
    (abs_nonneg L).trans (le_max_left |L| |R|), ?_⟩
  intro target htarget
  exact abs_le_max_abs_abs
    (htrap target htarget).1.le (htrap target htarget).2.le

/-! ## Compact variance and lower separation -/

/-- The limiting second numerator is continuous on every symmetric compact
tilt interval.  The proof exposes the summable endpoint majorant for its
natural-deficit series. -/
theorem continuousOn_extendedGaussianSecondNumerator_Icc
    (a M : ℝ) (ha : 0 < a) :
    ContinuousOn (extendedGaussianSecondNumerator a) (Icc (-M) M) := by
  have hseries :
      ContinuousOn
        (fun lambda : ℝ ↦
          ∑' d : ℕ,
            ((d : ℝ) ^ 2) *
              extendedGaussianNaturalTerm a lambda d)
        (Icc (-M) M) := by
    apply continuousOn_tsum
      (u := fun d : ℕ ↦
        ((d : ℝ) ^ 2) * extendedGaussianNaturalTerm a M d)
    · intro d
      unfold extendedGaussianNaturalTerm
      fun_prop
    · exact summable_extendedGaussianSecondMoment
        (a := a) (lambda := M) ha
    · intro d lambda hlambda
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg (d : ℝ))
          (extendedGaussianNaturalTerm_pos a lambda d).le)]
      exact mul_le_mul_of_nonneg_left
        (by
          rw [extendedGaussianNaturalTerm,
            extendedGaussianNaturalTerm]
          exact Real.exp_le_exp.mpr
            (sub_le_sub_right
              (mul_le_mul_of_nonneg_right hlambda.2
                (Nat.cast_nonneg d)) _))
        (sq_nonneg (d : ℝ))
  have hexceptional :
      Continuous (extendedGaussianExceptionalAtom a) := by
    unfold extendedGaussianExceptionalAtom
    fun_prop
  change ContinuousOn
    (fun lambda : ℝ ↦
      extendedGaussianExceptionalAtom a lambda +
        ∑' d : ℕ,
          ((d : ℝ) ^ 2) *
            extendedGaussianNaturalTerm a lambda d)
    (Icc (-M) M)
  exact hexceptional.continuousOn.add hseries

/-- The limiting raw variance is continuous on every symmetric compact tilt
interval. -/
theorem continuousOn_extendedGaussianRawVariance_Icc
    (a M : ℝ) (ha : 0 < a) :
    ContinuousOn (extendedGaussianRawVariance a) (Icc (-M) M) := by
  have hpartition : Continuous (extendedGaussianPartition a) := by
    rw [continuous_iff_continuousAt]
    exact fun lambda ↦
      (hasDerivAt_extendedGaussianPartition a lambda ha).continuousAt
  have hsecond := continuousOn_extendedGaussianSecondNumerator_Icc a M ha
  change ContinuousOn
    (fun lambda : ℝ ↦
      extendedGaussianSecondNumerator a lambda /
          extendedGaussianPartition a lambda -
        (extendedGaussianMean a lambda) ^ 2)
    (Icc (-M) M)
  exact
    (hsecond.div hpartition.continuousOn
      (fun lambda _ ↦ extendedGaussianPartition_ne_zero ha)).sub
      ((continuous_extendedGaussianMean a ha).continuousOn.pow 2)

/-- Strict pointwise variance positivity becomes a uniform positive lower
bound on a nonempty symmetric compact interval. -/
theorem exists_pos_extendedGaussianRawVariance_lower_bound_on_Icc
    (a M : ℝ) (ha : 0 < a) (hM : 0 ≤ M) :
    ∃ c : ℝ, 0 < c ∧
      ∀ lambda ∈ Icc (-M) M,
        c ≤ extendedGaussianRawVariance a lambda := by
  exact exists_pos_lower_bound_on_Icc
    (show -M ≤ M by linarith)
    (continuousOn_extendedGaussianRawVariance_Icc a M ha)
    (fun lambda _ ↦ extendedGaussianRawVariance_pos a lambda ha)

/-- A positive lower variance bound on `[-M,M]` gives a quantitative lower
separation for the limiting mean throughout that interval. -/
theorem extendedGaussianMean_lower_separation_on_Icc
    (a M c : ℝ) (ha : 0 < a) (_hc : 0 < c)
    (hlower : ∀ lambda ∈ Icc (-M) M,
      c ≤ extendedGaussianRawVariance a lambda) :
    ∀ u ∈ Icc (-M) M, ∀ v ∈ Icc (-M) M,
      c * |u - v| ≤
        |extendedGaussianMean a u - extendedGaussianMean a v| := by
  have hordered : ∀ {u v : ℝ},
      u ∈ Icc (-M) M → v ∈ Icc (-M) M → u ≤ v →
      c * (v - u) ≤
        extendedGaussianMean a v - extendedGaussianMean a u := by
    intro u v hu hv huv
    have hconv : Convex ℝ (Icc u v) := convex_Icc u v
    have hinterior : interior (Icc u v) = Ioo u v := interior_Icc
    refine Convex.mul_sub_le_image_sub_of_le_deriv hconv
      (continuous_extendedGaussianMean a ha).continuousOn ?_ ?_
      u (left_mem_Icc.mpr huv) v (right_mem_Icc.mpr huv) huv
    · rw [hinterior]
      exact (differentiable_extendedGaussianMean a ha).differentiableOn
    · intro lambda hlambda
      rw [hinterior] at hlambda
      rw [(hasDerivAt_extendedGaussianMean a lambda ha).deriv]
      apply hlower lambda
      exact ⟨hu.1.trans hlambda.1.le,
        hlambda.2.le.trans hv.2⟩
  intro u hu v hv
  by_cases huv : u ≤ v
  · have hmono :
        extendedGaussianMean a u ≤ extendedGaussianMean a v :=
      (strictMono_extendedGaussianMean a ha).monotone huv
    calc
      c * |u - v| = c * (v - u) := by
        rw [abs_of_nonpos (sub_nonpos.mpr huv)]
        ring
      _ ≤ extendedGaussianMean a v - extendedGaussianMean a u :=
        hordered hu hv huv
      _ = |extendedGaussianMean a u -
          extendedGaussianMean a v| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
        ring
  · have hvu : v ≤ u := le_of_not_ge huv
    have hmono :
        extendedGaussianMean a v ≤ extendedGaussianMean a u :=
      (strictMono_extendedGaussianMean a ha).monotone hvu
    calc
      c * |u - v| = c * (u - v) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
      _ ≤ extendedGaussianMean a u - extendedGaussianMean a v :=
        hordered hv hu hvu
      _ = |extendedGaussianMean a u -
          extendedGaussianMean a v| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hmono)]

end

end Erdos625
