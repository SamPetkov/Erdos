import Erdos625.ColoringProfileDeficitConvergence
import Erdos625.ColoringProfileDeficitPartitionBounds
import Erdos625.ExtendedGaussianProfile
import Erdos625.ProfileAsymptoticTools

/-!
# Pointwise convergence of finite deficit weights

This module embeds each fixed natural deficit into the growing finite support
and proves convergence of its exact centered weight to the corresponding
extended tilted-Gaussian term.  Outside the finite support the embedded term
is totalized by zero; this choice is irrelevant at `Filter.atTop` for every
fixed deficit.

The exceptional deficit `-1` atom is treated separately.  These are pointwise
statements only: no interchange of a limit with the growing-support sum is
performed here.
-/

namespace Erdos625

open Filter
open scoped Topology

noncomputable section

/-- The finite centered weight at a fixed natural deficit.  When `d < alpha`,
the reverse support coordinate has deficit exactly `d`; outside the support
the value is totalized by zero. -/
def profileDeficitNaturalTerm
    (alpha : ℕ) (lambda : ℝ) (d : ℕ) : ℝ :=
  if h : d < alpha then
    profileDeficitUnnormalized alpha lambda
      (Fin.rev (⟨d, h⟩ : Fin alpha).succ)
  else 0

/-- The finite centered weight at the exceptional deficit `-1`. -/
def profileDeficitExceptionalTerm (alpha : ℕ) (lambda : ℝ) : ℝ :=
  profileDeficitUnnormalized alpha lambda (Fin.last alpha)

/-- Exact descending-factorial expression for an interior reversed support
coordinate. -/
theorem profileDeficitResidualScore_rev_succ_eq
    (alpha : ℕ) (d : Fin alpha) :
    profileDeficitResidualScore alpha (Fin.rev d.succ) =
      Real.log (alpha.descFactorial d.1 : ℝ) -
        (d.1 : ℝ) * Real.log (alpha : ℝ) -
          q / 2 * (d.1 : ℝ) ^ 2 := by
  have hsize : (Fin.rev d.succ).1 + 1 ≤ alpha := by
    rw [Fin.val_rev, Fin.val_succ]
    omega
  have hsub : alpha - ((Fin.rev d.succ).1 + 1) = d.1 := by
    rw [Fin.val_rev, Fin.val_succ]
    omega
  rw [profileDeficitResidualScore_eq_descFactorial alpha
    (Fin.rev d.succ) hsize, hsub]

/-- On its support, the totalized natural-deficit term has the exact finite
factorial-correction formula. -/
theorem profileDeficitNaturalTerm_eq_of_lt
    (alpha : ℕ) (lambda : ℝ) (d : ℕ) (h : d < alpha) :
    profileDeficitNaturalTerm alpha lambda d =
      Real.exp
        ((Real.log (alpha.descFactorial d : ℝ) -
            (d : ℝ) * Real.log (alpha : ℝ)) +
          (lambda * (d : ℝ) - q / 2 * (d : ℝ) ^ 2)) := by
  rw [profileDeficitNaturalTerm, dif_pos h,
    profileDeficitUnnormalized,
    profileDeficitResidualScore_rev_succ_eq,
    profileDeficit_rev_succ]
  congr 1
  ring

/-- For fixed tilt and fixed natural deficit, the exact finite centered weight
converges to the corresponding extended tilted-Gaussian term. -/
theorem tendsto_profileDeficitNaturalTerm
    (lambda : ℝ) (d : ℕ) :
    Tendsto
      (fun alpha : ℕ ↦ profileDeficitNaturalTerm alpha lambda d)
      atTop
      (𝓝 (extendedGaussianNaturalTerm (Real.log 2) lambda d)) := by
  have hcorr := tendsto_log_descFactorial_sub_mul_log d
  have hexponent :
      Tendsto
        (fun alpha : ℕ ↦
          (Real.log (alpha.descFactorial d : ℝ) -
              (d : ℝ) * Real.log (alpha : ℝ)) +
            (lambda * (d : ℝ) - q / 2 * (d : ℝ) ^ 2))
        atTop
        (𝓝
          (0 + (lambda * (d : ℝ) - q / 2 * (d : ℝ) ^ 2))) :=
    hcorr.add tendsto_const_nhds
  have heq :
      (fun alpha : ℕ ↦ profileDeficitNaturalTerm alpha lambda d) =ᶠ[atTop]
        (fun alpha : ℕ ↦
          Real.exp
            ((Real.log (alpha.descFactorial d : ℝ) -
                (d : ℝ) * Real.log (alpha : ℝ)) +
              (lambda * (d : ℝ) - q / 2 * (d : ℝ) ^ 2))) := by
    filter_upwards [eventually_gt_atTop d] with alpha halpha
    exact profileDeficitNaturalTerm_eq_of_lt alpha lambda d halpha
  simpa [extendedGaussianNaturalTerm, q] using
    (hexponent.rexp.congr' heq.symm)

/-- Exact finite formula for the exceptional deficit `-1` atom. -/
theorem profileDeficitExceptionalTerm_eq
    (alpha : ℕ) (halpha : 0 < alpha) (lambda : ℝ) :
    profileDeficitExceptionalTerm alpha lambda =
      Real.exp
        (Real.log ((alpha : ℝ) / ((alpha : ℝ) + 1)) +
          (-lambda - q / 2)) := by
  rw [profileDeficitExceptionalTerm, profileDeficitUnnormalized,
    profileDeficitResidualScore_last alpha halpha,
    profileDeficit_last]
  congr 1
  ring

/-- The finite exceptional deficit `-1` atom converges to the exceptional atom
of the extended tilted-Gaussian profile. -/
theorem tendsto_profileDeficitExceptionalTerm (lambda : ℝ) :
    Tendsto
      (fun alpha : ℕ ↦ profileDeficitExceptionalTerm alpha lambda)
      atTop
      (𝓝 (extendedGaussianExceptionalAtom (Real.log 2) lambda)) := by
  have hexponent :
      Tendsto
        (fun alpha : ℕ ↦
          Real.log ((alpha : ℝ) / ((alpha : ℝ) + 1)) +
            (-lambda - q / 2))
        atTop
        (𝓝 (0 + (-lambda - q / 2))) :=
    tendsto_log_nat_div_nat_add_one.add tendsto_const_nhds
  have heq :
      (fun alpha : ℕ ↦ profileDeficitExceptionalTerm alpha lambda) =ᶠ[atTop]
        (fun alpha : ℕ ↦
          Real.exp
            (Real.log ((alpha : ℝ) / ((alpha : ℝ) + 1)) +
              (-lambda - q / 2))) := by
    filter_upwards [eventually_gt_atTop 0] with alpha halpha
    exact profileDeficitExceptionalTerm_eq alpha halpha lambda
  simpa [extendedGaussianExceptionalAtom, q] using
    (hexponent.rexp.congr' heq.symm)

/-- Fixed-coordinate convergence persists after multiplication by the first
moment coordinate. -/
theorem tendsto_profileDeficitNaturalFirstMomentTerm
    (lambda : ℝ) (d : ℕ) :
    Tendsto
      (fun alpha : ℕ ↦
        (d : ℝ) * profileDeficitNaturalTerm alpha lambda d)
      atTop
      (𝓝
        ((d : ℝ) *
          extendedGaussianNaturalTerm (Real.log 2) lambda d)) :=
  tendsto_const_nhds.mul (tendsto_profileDeficitNaturalTerm lambda d)

/-- Fixed-coordinate convergence persists after multiplication by the raw
second-moment coordinate. -/
theorem tendsto_profileDeficitNaturalSecondMomentTerm
    (lambda : ℝ) (d : ℕ) :
    Tendsto
      (fun alpha : ℕ ↦
        (d : ℝ) ^ 2 * profileDeficitNaturalTerm alpha lambda d)
      atTop
      (𝓝
        ((d : ℝ) ^ 2 *
          extendedGaussianNaturalTerm (Real.log 2) lambda d)) :=
  tendsto_const_nhds.mul (tendsto_profileDeficitNaturalTerm lambda d)

end

end Erdos625
