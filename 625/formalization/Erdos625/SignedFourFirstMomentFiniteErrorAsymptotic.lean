import Erdos625.MidpointRoundedSignedFourSizeObjectiveBridge
import Erdos625.ColoringProfileDualLogReduction
import Mathlib.Tactic

/-!
# Normalized finite signed four-size first-moment error

This module turns the explicit finite first-moment bridge

`|log M - signedFourSizeObjective| ≤ 4 * factorialLogErrorBound n + 50 / 7`

into a reusable little-o and normalized-limit statement.  It keeps the
remaining growth input explicit: the part-count scale must dominate
`logOrder`.  This is substantially weaker than the manuscript midpoint
asymptotic `K ~ (q / 2) n / log n` and does not assume any first-moment
conclusion.

No phase-root selector, chromatic lower tail, partial-diagonal estimate,
second moment, or final Erdős statement is used.
-/

namespace Erdos625

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

set_option autoImplicit false

/-- The exact signed first-moment logarithmic error for a sequence of finite
four-size profiles. -/
noncomputable def midpointPartialSignedFirstMomentLogError
    (alpha K : ℕ → ℕ) (n : ℕ) : ℝ :=
  Real.log
      (partialSignedFirstMoment n
        (fun i : Fin 4 ↦ alpha n - fourDeficit i)
        (midpointMultiplicity n (alpha n) (K n))) -
    signedFourSizeObjective n (alpha n) (K n : ℝ)

/-- The explicit deterministic finite-error majorant supplied by the
four-coordinate Stirling and tangent-rounding bridges. -/
noncomputable def signedFourFiniteFirstMomentErrorBound (n : ℕ) : ℝ :=
  4 * factorialLogErrorBound n + 50 / 7

/-- The explicit finite-error majorant is nonnegative. -/
theorem signedFourFiniteFirstMomentErrorBound_nonneg (n : ℕ) :
    0 ≤ signedFourFiniteFirstMomentErrorBound n := by
  unfold signedFourFiniteFirstMomentErrorBound
  have hFactorial := factorialLogErrorBound_nonneg n
  positivity

/-- Eventual admissibility gives the exact deterministic error estimate along
any sequence of finite midpoint profiles. -/
theorem eventually_abs_midpointPartialSignedFirstMomentLogError_le
    (alpha K : ℕ → ℕ)
    (hAdmissible : ∀ᶠ n : ℕ in atTop,
      MidpointRoundingAdmissible n (alpha n) (K n)) :
    ∀ᶠ n : ℕ in atTop,
      |midpointPartialSignedFirstMomentLogError alpha K n| ≤
        signedFourFiniteFirstMomentErrorBound n := by
  filter_upwards [hAdmissible] with n hn
  simpa [midpointPartialSignedFirstMomentLogError,
    signedFourFiniteFirstMomentErrorBound] using
      abs_log_midpointPartialSignedFirstMoment_sub_signedFourSizeObjective_le
        n (alpha n) (K n) hn

/-- The exact logarithmic first-moment error is big-O of its explicit finite
majorant. -/
theorem midpointPartialSignedFirstMomentLogError_isBigO
    (alpha K : ℕ → ℕ)
    (hAdmissible : ∀ᶠ n : ℕ in atTop,
      MidpointRoundingAdmissible n (alpha n) (K n)) :
    midpointPartialSignedFirstMomentLogError alpha K =O[atTop]
      signedFourFiniteFirstMomentErrorBound := by
  apply IsBigO.of_bound 1
  filter_upwards
    [eventually_abs_midpointPartialSignedFirstMomentLogError_le
      alpha K hAdmissible] with n hn
  have hErrorNonneg := signedFourFiniteFirstMomentErrorBound_nonneg n
  simpa [Real.norm_eq_abs, abs_of_nonneg hErrorNonneg] using hn

/-- If the part-count scale dominates `logOrder`, then the complete explicit
finite first-moment error is little-o of the part count. -/
theorem signedFourFiniteFirstMomentErrorBound_isLittleO_of_logOrder
    (K : ℕ → ℕ)
    (hK : logOrder =o[atTop] (fun n : ℕ ↦ (K n : ℝ))) :
    signedFourFiniteFirstMomentErrorBound =o[atTop]
      (fun n : ℕ ↦ (K n : ℝ)) := by
  have hLogNe : ∀ᶠ n : ℕ in atTop, logOrder n ≠ 0 :=
    tendsto_logOrder_atTop.eventually_ne_atTop 0
  have hFactorialEq :
      (fun n : ℕ ↦ factorialLogErrorBound n) ~[atTop] logOrder :=
    (isEquivalent_iff_tendsto_one hLogNe).2
      factorialLogErrorBound_div_logOrder_tendsto_one
  have hFactorialLittle :
      (fun n : ℕ ↦ factorialLogErrorBound n) =o[atTop]
        (fun n : ℕ ↦ (K n : ℝ)) :=
    hFactorialEq.isBigO.trans_isLittleO hK
  have hFour :
      (fun n : ℕ ↦ (4 : ℝ) * factorialLogErrorBound n) =o[atTop]
        (fun n : ℕ ↦ (K n : ℝ)) :=
    hFactorialLittle.const_mul_left 4
  have hConstLog :
      (fun _n : ℕ ↦ (50 / 7 : ℝ)) =o[atTop] logOrder := by
    simpa only [Function.comp_def, id_eq] using
      (isLittleO_const_id_atTop (50 / 7 : ℝ)).comp_tendsto
        tendsto_logOrder_atTop
  have hConstK :
      (fun _n : ℕ ↦ (50 / 7 : ℝ)) =o[atTop]
        (fun n : ℕ ↦ (K n : ℝ)) :=
    hConstLog.trans hK
  have hSum := hFour.add hConstK
  exact hSum.congr_left fun n ↦ by
    simp [signedFourFiniteFirstMomentErrorBound]

/-- The exact finite first-moment logarithmic error is little-o of the part
count whenever the part count dominates `logOrder`. -/
theorem midpointPartialSignedFirstMomentLogError_isLittleO_of_logOrder
    (alpha K : ℕ → ℕ)
    (hAdmissible : ∀ᶠ n : ℕ in atTop,
      MidpointRoundingAdmissible n (alpha n) (K n))
    (hK : logOrder =o[atTop] (fun n : ℕ ↦ (K n : ℝ))) :
    midpointPartialSignedFirstMomentLogError alpha K =o[atTop]
      (fun n : ℕ ↦ (K n : ℝ)) :=
  (midpointPartialSignedFirstMomentLogError_isBigO
    alpha K hAdmissible).trans_isLittleO
      (signedFourFiniteFirstMomentErrorBound_isLittleO_of_logOrder K hK)

/-- Normalized finite first-moment estimate: after division by the number of parts, the
exact factorial first moment and the signed finite four-size objective differ
by a quantity tending to zero. -/
theorem tendsto_midpointPartialSignedFirstMomentLogError_div_parts_zero
    (alpha K : ℕ → ℕ)
    (hAdmissible : ∀ᶠ n : ℕ in atTop,
      MidpointRoundingAdmissible n (alpha n) (K n))
    (hK : logOrder =o[atTop] (fun n : ℕ ↦ (K n : ℝ))) :
    Tendsto
      (fun n : ℕ ↦
        midpointPartialSignedFirstMomentLogError alpha K n / (K n : ℝ))
      atTop (𝓝 0) := by
  exact
    (midpointPartialSignedFirstMomentLogError_isLittleO_of_logOrder
      alpha K hAdmissible hK).tendsto_div_nhds_zero

#print axioms signedFourFiniteFirstMomentErrorBound_nonneg
#print axioms eventually_abs_midpointPartialSignedFirstMomentLogError_le
#print axioms midpointPartialSignedFirstMomentLogError_isBigO
#print axioms signedFourFiniteFirstMomentErrorBound_isLittleO_of_logOrder
#print axioms midpointPartialSignedFirstMomentLogError_isLittleO_of_logOrder
#print axioms tendsto_midpointPartialSignedFirstMomentLogError_div_parts_zero

end

end Erdos625
