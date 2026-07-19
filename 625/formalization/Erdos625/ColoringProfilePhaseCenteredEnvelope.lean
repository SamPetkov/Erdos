import Erdos625.ColoringProfileCubicPhaseTail
import Erdos625.ColoringProfileDeficitTilt

set_option warningAsError true

/-!
# Exact centered form and a finite cubic phase envelope

This module exposes the selected profile phase in the manuscript's deficit
coordinates without replacing the natural floor phase or the selected finite
Gibbs tilt.  It also replaces the negative-limit premise of the cubic-tail
adapter by a one-sided eventual estimate, which is the strictly smaller
remaining analytic obligation needed by that adapter.
-/

namespace Erdos625

open Filter
open scoped Topology

noncomputable section

/-- The selected phase objective, in exact finite deficit coordinates.  The
support is the literal `phaseNat n + 1`, the target is the exact quotient
`n / parts`, and no asymptotic or rounding replacement occurs. -/
theorem profilePhaseObjective_eq_deficitCentered
    (n : ℕ) {parts : ℝ} (hparts : parts ≠ 0) :
    profilePhaseObjective n parts =
      ((phaseNat n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) +
        ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + parts -
          parts * Real.log parts +
          parts *
            (profileDeficitAffineA (phaseNat n) +
              profileDeficitAffineB (phaseNat n) *
                profileDeficitTarget (phaseNat n) (n : ℝ) parts +
              Real.log
                (profileDeficitPartition (phaseNat n)
                  (profileDeficitTilt (phaseNat n)
                    (profileDeficitTarget (phaseNat n) (n : ℝ) parts))) -
              profileDeficitTilt (phaseNat n)
                  (profileDeficitTarget (phaseNat n) (n : ℝ) parts) *
                profileDeficitTarget (phaseNat n) (n : ℝ) parts)) := by
  rw [profilePhaseObjective_eq_selected_core n hparts]
  have htarget :
      (n : ℝ) / parts =
        (phaseNat n : ℝ) -
          profileDeficitTarget (phaseNat n) (n : ℝ) parts := by
    simp [profileDeficitTarget]
  rw [htarget, ← profileDeficitAffineB_sub_profileDeficitTilt]
  rw [profileDualUpper_eq_deficitCentered (phaseNat n) hparts]

/-- A fixed negative cubic envelope is enough for the complete logarithmic
phase envelope to tend to `-∞`.  This removes the need to identify an exact
cubic-scale limit: only the displayed one-sided finite estimate remains. -/
theorem phaseEnvelope_atBot_of_eventually_le_neg_cubic
    (parts : ℕ → ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hphase : ∀ᶠ n : ℕ in atTop,
      profilePhaseObjective n (parts n : ℝ) ≤
        -epsilon * (logOrder n) ^ 3) :
    Tendsto
      (fun n : ℕ ↦
        profilePhaseObjective n (parts n : ℝ) + factorialLogErrorBound n)
      atTop atBot := by
  have hcorrection : ∀ᶠ n : ℕ in atTop,
      factorialLogErrorBound n ≤
        (epsilon / 2) * (logOrder n) ^ 3 := by
    have hratio : ∀ᶠ n : ℕ in atTop,
        factorialLogErrorBound n / (logOrder n) ^ 3 < epsilon / 2 :=
      factorialLogErrorBound_div_logOrder_cubed_tendsto_zero.eventually
        (Iio_mem_nhds (by linarith : (0 : ℝ) < epsilon / 2))
    have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < (logOrder n) ^ 3 :=
      ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp
        tendsto_logOrder_atTop).eventually (eventually_gt_atTop 0)
    filter_upwards [hratio, hscalePos] with n hn hpos
    calc
      factorialLogErrorBound n =
          (factorialLogErrorBound n / (logOrder n) ^ 3) *
            (logOrder n) ^ 3 := (div_mul_cancel₀ _ hpos.ne').symm
      _ ≤ (epsilon / 2) * (logOrder n) ^ 3 :=
        mul_le_mul_of_nonneg_right hn.le hpos.le
  apply tendsto_atBot_mono' atTop (by
    filter_upwards [hphase, hcorrection] with n hn hc
    calc
      profilePhaseObjective n (parts n : ℝ) + factorialLogErrorBound n ≤
          (-epsilon) * (logOrder n) ^ 3 +
            (epsilon / 2) * (logOrder n) ^ 3 := add_le_add hn hc
      _ = (-(epsilon / 2)) * (logOrder n) ^ 3 := by ring)
  exact (((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp
    tendsto_logOrder_atTop).const_mul_atTop_of_neg (by linarith))

/-- Consequently, the same explicit one-sided cubic estimate implies the
concrete chromatic at-most tail.  The natural-number threshold sequence and
all casts are left unchanged. -/
theorem randomGraphMeasure_chromaticNumberAtMost_tendsto_zero_of_eventually_le_neg_cubic
    (parts : ℕ → ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hpartsPos : ∀ᶠ n in atTop, 0 < parts n)
    (hpartsLe : ∀ᶠ n in atTop, parts n ≤ n)
    (hphase : ∀ᶠ n : ℕ in atTop,
      profilePhaseObjective n (parts n : ℝ) ≤
        -epsilon * (logOrder n) ^ 3) :
    Tendsto
      (fun n : ℕ ↦ randomGraphMeasure n
        {G : LabeledGraph n | chromaticNumberNat G ≤ parts n})
      atTop (𝓝 0) := by
  apply chromaticAtMost_tendsto_zero_of_phaseEnvelope_atBot
    parts hpartsPos hpartsLe
  exact phaseEnvelope_atBot_of_eventually_le_neg_cubic
    parts epsilon hepsilon hphase

#print axioms profilePhaseObjective_eq_deficitCentered
#print axioms phaseEnvelope_atBot_of_eventually_le_neg_cubic
#print axioms randomGraphMeasure_chromaticNumberAtMost_tendsto_zero_of_eventually_le_neg_cubic

end

end Erdos625

