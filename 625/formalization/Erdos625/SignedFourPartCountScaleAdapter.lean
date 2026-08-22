import Erdos625.SignedFourFirstMomentFiniteErrorAsymptotic
import Mathlib.Tactic

/-!
# Part-count scale adapter for the signed four-size first moment

This module discharges the deterministic growth input used by the normalized
finite E625-10 error theorem.  The manuscript part-count scale is

`n / log n`.

The module first proves that `log n = o(n / log n)`.  It then transports this
through any part-count sequence which dominates that natural scale in the
big-O sense.  This condition is weaker than the concrete manuscript
asymptotic

`K_n ~ (q / 2) * n / log n`.

No phase-root selector, root separation, entropy margin, chromatic lower tail,
partial-diagonal estimate, second moment, or final Erdős statement is used.
-/

namespace Erdos625

open Filter Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- The natural real part-count scale occurring in the manuscript.  It is kept
total at small `n`; only its `atTop` behavior is used. -/
noncomputable def signedFourNaturalPartScale (n : ℕ) : ℝ :=
  (n : ℝ) / logOrder n

/-- The square of the logarithmic order is negligible relative to the vertex
count. -/
theorem logOrder_sq_isLittleO_natCast :
    (fun n : ℕ ↦ logOrder n ^ 2) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  simpa only [logOrder, Function.comp_def, id_eq] using
    (Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))

/-- `log n` is negligible relative to the manuscript part-count scale
`n / log n`. -/
theorem logOrder_isLittleO_signedFourNaturalPartScale :
    logOrder =o[atTop] signedFourNaturalPartScale := by
  have hInv :
      (fun n : ℕ ↦ (logOrder n)⁻¹) =O[atTop]
        (fun n : ℕ ↦ (logOrder n)⁻¹) :=
    isBigO_refl _ _
  have hMul := logOrder_sq_isLittleO_natCast.mul_isBigO hInv
  exact
    (hMul.congr_left fun n ↦ by
      by_cases hlog : logOrder n = 0
      · simp [hlog]
      · field_simp [hlog]).congr_right fun n ↦ by
        simp [signedFourNaturalPartScale, div_eq_mul_inv]

/-- Any part-count sequence which is at least of the natural manuscript scale
up to a constant factor dominates `logOrder`. -/
theorem logOrder_isLittleO_parts_of_naturalScale_isBigO
    (K : ℕ → ℕ)
    (hScaleToParts : signedFourNaturalPartScale =O[atTop]
      (fun n : ℕ ↦ (K n : ℝ))) :
    logOrder =o[atTop] (fun n : ℕ ↦ (K n : ℝ)) :=
  logOrder_isLittleO_signedFourNaturalPartScale.trans_isBigO hScaleToParts

/-- The complete explicit finite first-moment error is negligible for every
part-count sequence which dominates `n / log n`. -/
theorem signedFourFiniteFirstMomentErrorBound_isLittleO_of_naturalScale
    (K : ℕ → ℕ)
    (hScaleToParts : signedFourNaturalPartScale =O[atTop]
      (fun n : ℕ ↦ (K n : ℝ))) :
    signedFourFiniteFirstMomentErrorBound =o[atTop]
      (fun n : ℕ ↦ (K n : ℝ)) :=
  signedFourFiniteFirstMomentErrorBound_isLittleO_of_logOrder K
    (logOrder_isLittleO_parts_of_naturalScale_isBigO K hScaleToParts)

/-- The exact logarithmic finite first-moment error is negligible relative to
any admissible part-count sequence of manuscript scale. -/
theorem midpointPartialSignedFirstMomentLogError_isLittleO_of_naturalScale
    (alpha K : ℕ → ℕ)
    (hAdmissible : ∀ᶠ n : ℕ in atTop,
      MidpointRoundingAdmissible n (alpha n) (K n))
    (hScaleToParts : signedFourNaturalPartScale =O[atTop]
      (fun n : ℕ ↦ (K n : ℝ))) :
    midpointPartialSignedFirstMomentLogError alpha K =o[atTop]
      (fun n : ℕ ↦ (K n : ℝ)) :=
  midpointPartialSignedFirstMomentLogError_isLittleO_of_logOrder
    alpha K hAdmissible
      (logOrder_isLittleO_parts_of_naturalScale_isBigO K hScaleToParts)

/-- Manuscript-scale specialization of the normalized finite E625-10 seam. -/
theorem tendsto_midpointPartialSignedFirstMomentLogError_div_parts_zero_of_naturalScale
    (alpha K : ℕ → ℕ)
    (hAdmissible : ∀ᶠ n : ℕ in atTop,
      MidpointRoundingAdmissible n (alpha n) (K n))
    (hScaleToParts : signedFourNaturalPartScale =O[atTop]
      (fun n : ℕ ↦ (K n : ℝ))) :
    Tendsto
      (fun n : ℕ ↦
        midpointPartialSignedFirstMomentLogError alpha K n / (K n : ℝ))
      atTop (𝓝 0) :=
  (midpointPartialSignedFirstMomentLogError_isLittleO_of_naturalScale
    alpha K hAdmissible hScaleToParts).tendsto_div_nhds_zero

#print axioms logOrder_sq_isLittleO_natCast
#print axioms logOrder_isLittleO_signedFourNaturalPartScale
#print axioms logOrder_isLittleO_parts_of_naturalScale_isBigO
#print axioms signedFourFiniteFirstMomentErrorBound_isLittleO_of_naturalScale
#print axioms midpointPartialSignedFirstMomentLogError_isLittleO_of_naturalScale
#print axioms tendsto_midpointPartialSignedFirstMomentLogError_div_parts_zero_of_naturalScale

end

end Erdos625
