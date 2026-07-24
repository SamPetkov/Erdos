import Erdos625.Section10QuarterDensityEvent
import Mathlib.Tactic

/-!
# Section X: full-sequence cutoff-event limit

This module connects the literal finite cutoff-family failure bound to the
already proved deterministic union-bound decay.  It proves only that the
fixed cutoff-size simultaneous event has probability tending to one.  It does
not lift quarter density to larger subsets and does not supply the subsequent
greedy deletion chain.
-/

namespace Erdos625

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

/-- The elementary quadratic comparison needed to absorb the `choose u 2`
exponent into the established union-bound decay. -/
theorem quarterDensity_choose_two_div_sixteen_lower_bound
    (u : ℕ) (hu : 2 ≤ u) :
    ((1 : ℝ) / 64) * (u : ℝ) ^ 2 ≤ ((u.choose 2 : ℕ) : ℝ) / 16 := by
  rw [Nat.cast_choose_two]
  have huReal : (2 : ℝ) ≤ (u : ℝ) := by
    exact_mod_cast hu
  norm_num
  nlinarith

/-- The quarter-density cutoff diverges along the full sequence. -/
theorem quarterDensityCutoff_tendsto_atTop :
    Tendsto quarterDensityCutoff atTop atTop := by
  change Tendsto
    ((fun x : ℝ => ⌈x⌉₊) ∘ (fun x : ℝ => x ^ (1 / 4 : ℝ)) ∘ Nat.cast)
    atTop atTop
  exact tendsto_nat_ceil_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop)

/-- Eventually, the literal binomial lower-tail exponent is at least the
quadratic exponent with constant `1/64`. -/
theorem quarterDensity_eventually_exponent_bound :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-((quarterDensityCutoff n).choose 2 : ℕ) / 16 : ℝ) ≤
        Real.exp (-((1 : ℝ) / 64) * (quarterDensityCutoff n : ℝ) ^ 2) := by
  filter_upwards [quarterDensityCutoff_tendsto_atTop.eventually_ge_atTop 2] with n hn
  apply Real.exp_le_exp.mpr
  calc
    -((quarterDensityCutoff n).choose 2 : ℕ) / 16 =
        -(((quarterDensityCutoff n).choose 2 : ℕ) : ℝ) / 16 := by ring
    _ = -((((quarterDensityCutoff n).choose 2 : ℕ) : ℝ) / 16) := by ring
    _ ≤ -((1 : ℝ) / 64 * (quarterDensityCutoff n : ℝ) ^ 2) :=
      neg_le_neg (quarterDensity_choose_two_div_sixteen_lower_bound
        (quarterDensityCutoff n) hn)
    _ = -((1 : ℝ) / 64) * (quarterDensityCutoff n : ℝ) ^ 2 := by ring

/-- The failure probability of the literal finite cutoff-family event tends
to zero along the full sequence. -/
theorem cutoffComplementQuarterDensityEvent_failure_real_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (randomGraphMeasure n).real (cutoffComplementQuarterDensityEvent n)ᶜ)
      atTop (nhds 0) := by
  have hDecay := quarterDensity_unionBound_tendsto_zero ((1 : ℝ) / 64)
    (by norm_num : (0 : ℝ) < 1 / 64)
  have hUpper : ∀ᶠ n : ℕ in atTop,
      (randomGraphMeasure n).real (cutoffComplementQuarterDensityEvent n)ᶜ ≤
        (Nat.choose n (quarterDensityCutoff n) : ℝ) *
          Real.exp (-((1 : ℝ) / 64) * (quarterDensityCutoff n : ℝ) ^ 2) := by
    filter_upwards [quarterDensity_eventually_exponent_bound] with n hn
    calc
      (randomGraphMeasure n).real (cutoffComplementQuarterDensityEvent n)ᶜ ≤
          (Nat.choose n (quarterDensityCutoff n) : ℝ) *
            Real.exp (-((quarterDensityCutoff n).choose 2 : ℕ) / 16 : ℝ) :=
        cutoffComplementQuarterDensityEvent_failure_le n
      _ ≤ (Nat.choose n (quarterDensityCutoff n) : ℝ) *
          Real.exp (-((1 : ℝ) / 64) * (quarterDensityCutoff n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hDecay
    (Filter.Eventually.of_forall fun _ ↦ measureReal_nonneg)
    hUpper

/-- The literal finite simultaneous cutoff event has probability tending to
one.  This is still only the cutoff-size event, not a statement for all
larger vertex subsets. -/
theorem cutoffComplementQuarterDensityEvent_probability_tendsto_one :
    Tendsto
      (fun n : ℕ ↦ randomGraphMeasure n (cutoffComplementQuarterDensityEvent n))
      atTop (nhds 1) := by
  have hSuccessIdentity : ∀ n : ℕ,
      (randomGraphMeasure n).real (cutoffComplementQuarterDensityEvent n) =
        1 - (randomGraphMeasure n).real
          (cutoffComplementQuarterDensityEvent n)ᶜ := by
    intro n
    have hCompl := measureReal_compl
      (μ := randomGraphMeasure n)
      (measurableSet_cutoffComplementQuarterDensityEvent n)
    rw [probReal_univ] at hCompl
    linarith
  have hSuccessReal : Tendsto
      (fun n : ℕ ↦
        (randomGraphMeasure n).real (cutoffComplementQuarterDensityEvent n))
      atTop (nhds (1 : ℝ)) := by
    have hOne : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hSub := hOne.sub cutoffComplementQuarterDensityEvent_failure_real_tendsto_zero
    convert hSub using 1
    · funext n
      exact hSuccessIdentity n
    · norm_num
  exact
    (ENNReal.tendsto_toReal_iff
      (fun n ↦ measure_ne_top (randomGraphMeasure n)
        (cutoffComplementQuarterDensityEvent n))
      ENNReal.one_ne_top).mp (by
        simpa only [Measure.real, ENNReal.toReal_one] using hSuccessReal)

#print axioms quarterDensity_choose_two_div_sixteen_lower_bound
#print axioms quarterDensityCutoff_tendsto_atTop
#print axioms quarterDensity_eventually_exponent_bound
#print axioms cutoffComplementQuarterDensityEvent_failure_real_tendsto_zero
#print axioms cutoffComplementQuarterDensityEvent_probability_tendsto_one

end

end Erdos625
