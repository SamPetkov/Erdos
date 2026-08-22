import Erdos625.ExtendedGaussianGibbsOptimizer
import Erdos625.SignedUnrestrictedObjectiveGapIdentity
import Erdos625.SignedFourMidpointObjectiveCorridor
import Mathlib.Tactic

/-!
# A deterministic error bound for the finite unrestricted entropy

The exact signed-versus-unrestricted objective ledger isolates the finite
unrestricted entropy error

`log Z_alpha(lambda_alpha(T)) - lambda_alpha(T) T - H_infinity(T)`.

This module decomposes its absolute value into the three quantities controlled
by the existing compact-uniform infrastructure:

1. the finite partition error at the moving finite tilt;
2. transport of the limiting log-partition between the finite and limiting
   selected tilts;
3. the selected-tilt error multiplied by the bounded target.

The first logarithmic error is reduced to the raw partition error using the
fact that both partition functions are at least one.  No convergence theorem,
root statement, first moment, chromatic tail, partial diagonal, second moment,
or final Erdős statement is asserted here.
-/

namespace Erdos625

open Set
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- On the half-line `[1,infinity)`, the real logarithm is one-Lipschitz. -/
theorem abs_log_sub_log_le_abs_sub_of_one_le
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| := by
  have hOrdered : ∀ {a b : ℝ}, 1 ≤ a → a ≤ b →
      |Real.log a - Real.log b| ≤ |a - b| := by
    intro a b ha hab
    have haPos : 0 < a := zero_lt_one.trans_le ha
    have hbPos : 0 < b := haPos.trans_le hab
    have hCont : ContinuousOn Real.log (Icc a b) := by
      intro z hz
      exact (Real.continuousAt_log
        (ne_of_gt (haPos.trans_le hz.1))).continuousWithinAt
    have hDiff : DifferentiableOn ℝ Real.log (Ioo a b) := by
      intro z hz
      have hzPos : 0 < z := haPos.trans_le hz.1.le
      exact (Real.hasDerivAt_log hzPos.ne').differentiableAt.differentiableWithinAt
    have hUpper : ∀ z ∈ Ioo a b, deriv Real.log z ≤ 1 := by
      intro z hz
      have hzOne : 1 ≤ z := ha.trans hz.1.le
      have hzPos : 0 < z := zero_lt_one.trans_le hzOne
      rw [(Real.hasDerivAt_log hzPos.ne').deriv, inv_eq_one_div]
      exact (div_le_iff₀ hzPos).2 (by simpa using hzOne)
    have hIncrement :=
      sub_le_derivative_upper_bound_mul_sub hab hCont hDiff hUpper
    have hLog : Real.log a ≤ Real.log b :=
      Real.strictMonoOn_log.monotoneOn haPos hbPos hab
    rw [abs_of_nonpos (sub_nonpos.mpr hLog),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    simpa using hIncrement
  rcases le_total x y with hxy | hyx
  · exact hOrdered hx hxy
  · rw [abs_sub_comm (Real.log x) (Real.log y), abs_sub_comm x y]
    exact hOrdered hy hyx

/-- The logarithmic finite-partition error is no larger than the raw
partition error at every positive finite support. -/
theorem abs_log_profileDeficitPartition_sub_log_extendedGaussianPartition_le
    (alpha : ℕ) (halpha : 0 < alpha) (tilt : ℝ) :
    |Real.log (profileDeficitPartition alpha tilt) -
        Real.log (extendedGaussianPartition q tilt)| ≤
      |profileDeficitPartition alpha tilt -
        extendedGaussianPartition q tilt| := by
  exact abs_log_sub_log_le_abs_sub_of_one_le
    (one_le_profileDeficitPartition alpha halpha tilt)
    (one_le_extendedGaussianPartition q_pos)

/-- Exact three-term deterministic bound for the finite unrestricted entropy
error at an interior target.  Each term on the right has a distinct analytic
source and can be controlled uniformly without hiding the main estimate in a
single hypothesis. -/
theorem abs_finiteUnrestrictedEntropyError_le
    (alpha : ℕ) {target : ℝ}
    (halpha : 0 < alpha)
    (htarget : target ∈ Ioo (2 : ℝ) 5) :
    |finiteUnrestrictedEntropyError alpha target| ≤
      |profileDeficitPartition alpha
          (profileDeficitTilt alpha target) -
        extendedGaussianPartition q
          (profileDeficitTilt alpha target)| +
      |Real.log
          (extendedGaussianPartition q
            (profileDeficitTilt alpha target)) -
        Real.log
          (extendedGaussianPartition q
            (extendedGaussianTilt q target))| +
      |target| *
        |profileDeficitTilt alpha target -
          extendedGaussianTilt q target| := by
  have hLimitEntropy :=
    extendedGaussianEntropyValue_eq_log_partition_sub_tilt_mul htarget
  have hIdentity :
      finiteUnrestrictedEntropyError alpha target =
        (Real.log
            (profileDeficitPartition alpha
              (profileDeficitTilt alpha target)) -
          Real.log
            (extendedGaussianPartition q
              (profileDeficitTilt alpha target))) +
        (Real.log
            (extendedGaussianPartition q
              (profileDeficitTilt alpha target)) -
          Real.log
            (extendedGaussianPartition q
              (extendedGaussianTilt q target))) +
        (extendedGaussianTilt q target -
          profileDeficitTilt alpha target) * target := by
    unfold finiteUnrestrictedEntropyError finiteUnrestrictedDeficitEntropy
    rw [hLimitEntropy]
    ring
  rw [hIdentity]
  have hFirst :=
    abs_log_profileDeficitPartition_sub_log_extendedGaussianPartition_le
      alpha halpha (profileDeficitTilt alpha target)
  have hTriangle :
      |(Real.log
            (profileDeficitPartition alpha
              (profileDeficitTilt alpha target)) -
          Real.log
            (extendedGaussianPartition q
              (profileDeficitTilt alpha target))) +
        (Real.log
            (extendedGaussianPartition q
              (profileDeficitTilt alpha target)) -
          Real.log
            (extendedGaussianPartition q
              (extendedGaussianTilt q target))) +
        (extendedGaussianTilt q target -
          profileDeficitTilt alpha target) * target| ≤
      |Real.log
          (profileDeficitPartition alpha
            (profileDeficitTilt alpha target)) -
        Real.log
          (extendedGaussianPartition q
            (profileDeficitTilt alpha target))| +
      |Real.log
          (extendedGaussianPartition q
            (profileDeficitTilt alpha target)) -
        Real.log
          (extendedGaussianPartition q
            (extendedGaussianTilt q target))| +
      |(extendedGaussianTilt q target -
          profileDeficitTilt alpha target) * target| := by
    calc
      _ ≤
          |(Real.log
                (profileDeficitPartition alpha
                  (profileDeficitTilt alpha target)) -
              Real.log
                (extendedGaussianPartition q
                  (profileDeficitTilt alpha target))) +
            (Real.log
                (extendedGaussianPartition q
                  (profileDeficitTilt alpha target)) -
              Real.log
                (extendedGaussianPartition q
                  (extendedGaussianTilt q target)))| +
          |(extendedGaussianTilt q target -
              profileDeficitTilt alpha target) * target| :=
        abs_add_le _ _
      _ ≤
          (|Real.log
              (profileDeficitPartition alpha
                (profileDeficitTilt alpha target)) -
            Real.log
              (extendedGaussianPartition q
                (profileDeficitTilt alpha target))| +
            |Real.log
              (extendedGaussianPartition q
                (profileDeficitTilt alpha target)) -
            Real.log
              (extendedGaussianPartition q
                (extendedGaussianTilt q target))|) +
          |(extendedGaussianTilt q target -
              profileDeficitTilt alpha target) * target| :=
        add_le_add_right (abs_add_le _ _) _
      _ = _ := by ring
  calc
    _ ≤
        |Real.log
            (profileDeficitPartition alpha
              (profileDeficitTilt alpha target)) -
          Real.log
            (extendedGaussianPartition q
              (profileDeficitTilt alpha target))| +
        |Real.log
            (extendedGaussianPartition q
              (profileDeficitTilt alpha target)) -
          Real.log
            (extendedGaussianPartition q
              (extendedGaussianTilt q target))| +
        |(extendedGaussianTilt q target -
            profileDeficitTilt alpha target) * target| :=
      hTriangle
    _ ≤
        |profileDeficitPartition alpha
            (profileDeficitTilt alpha target) -
          extendedGaussianPartition q
            (profileDeficitTilt alpha target)| +
        |Real.log
            (extendedGaussianPartition q
              (profileDeficitTilt alpha target)) -
          Real.log
            (extendedGaussianPartition q
              (extendedGaussianTilt q target))| +
        |(extendedGaussianTilt q target -
            profileDeficitTilt alpha target) * target| := by
      gcongr
    _ =
        |profileDeficitPartition alpha
            (profileDeficitTilt alpha target) -
          extendedGaussianPartition q
            (profileDeficitTilt alpha target)| +
        |Real.log
            (extendedGaussianPartition q
              (profileDeficitTilt alpha target)) -
          Real.log
            (extendedGaussianPartition q
              (extendedGaussianTilt q target))| +
        |target| *
          |profileDeficitTilt alpha target -
            extendedGaussianTilt q target| := by
      rw [abs_mul, abs_sub_comm]
      ring

#print axioms abs_log_sub_log_le_abs_sub_of_one_le
#print axioms abs_log_profileDeficitPartition_sub_log_extendedGaussianPartition_le
#print axioms abs_finiteUnrestrictedEntropyError_le

end

end Erdos625