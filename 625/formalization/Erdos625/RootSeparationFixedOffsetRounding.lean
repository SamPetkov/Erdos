import Erdos625.RootSeparationRoundingNatAdapter
import Erdos625.RootSeparationRoundingBudget
import Mathlib.Tactic

namespace Erdos625

open Filter Asymptotics
open scoped Topology

noncomputable section
set_option autoImplicit false

/-- The manuscript's cocoloring witness is sixteen integer units above the signed root. -/
def rootCochromaticFixedOffsetIndex (rCo : ℝ) : ℤ :=
  ⌈rCo⌉ + 16

/-- Fixed-offset rounding preserves the full real-root coefficient; the exact
loss budget is `N + 19`. -/
theorem root_fixedOffset_rounding_gap
    (rPlus rCo N c base rho : ℝ)
    (hGap : c * base ≤ rPlus - rCo)
    (hRounding : N + 19 ≤ rho * base) :
    (c - rho) * base ≤
      ((rootChromaticIndex rPlus N : ℤ) : ℝ) -
        ((rootCochromaticFixedOffsetIndex rCo : ℤ) : ℝ) := by
  unfold rootChromaticIndex rootCochromaticFixedOffsetIndex
  norm_num [sub_mul] at *
  linarith [Int.lt_floor_add_one rPlus, Int.ceil_lt_add_one N, Int.ceil_lt_add_one rCo]

/-- Natural-number transport of the fixed-offset rounding bound. -/
theorem root_fixedOffset_rounding_gap_toNat
    (rPlus rCo N c base rho : ℝ)
    (hGap : c * base ≤ rPlus - rCo)
    (hRounding : N + 19 ≤ rho * base)
    (hChromaticNonneg : 0 ≤ rootChromaticIndex rPlus N)
    (hCochromaticNonneg : 0 ≤ rootCochromaticFixedOffsetIndex rCo) :
    (c - rho) * base ≤
      (((rootChromaticIndex rPlus N).toNat : ℕ) : ℝ) -
        (((rootCochromaticFixedOffsetIndex rCo).toNat : ℕ) : ℝ) := by
  have h := root_fixedOffset_rounding_gap rPlus rCo N c base rho hGap hRounding
  rw [← Int.toNat_of_nonneg hChromaticNonneg,
    ← Int.toNat_of_nonneg hCochromaticNonneg] at h
  exact h

/-- A negligible budget that pays for the fixed offset and all integer rounding. -/
def fixedOffsetRoundingBudget (n : ℕ) : ℝ :=
  (Real.log (n : ℝ) + 20) * (Real.log (n : ℝ)) ^ 3 / (n : ℝ)

theorem fixedOffset_rounding_budget_spec :
    Tendsto fixedOffsetRoundingBudget atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        Real.log (n : ℝ) + 19 ≤
          fixedOffsetRoundingBudget n *
            ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) := by
  constructor
  · unfold fixedOffsetRoundingBudget
    suffices h : Tendsto (fun y : ℝ => (y + 20) * y ^ 3 / Real.exp y) atTop (nhds 0) by
      have h' := (h.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
      apply h'.congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      simp [Real.exp_log (Nat.cast_pos.mpr hn)]
    ring_nf
    norm_num [← Real.exp_neg]
    simpa using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).mul tendsto_const_nhds |>.add
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (Nat.one_lt_cast.mpr hn))
    rw [fixedOffsetRoundingBudget]
    field_simp
    norm_num

#print axioms root_fixedOffset_rounding_gap
#print axioms root_fixedOffset_rounding_gap_toNat
#print axioms fixedOffset_rounding_budget_spec

end
end Erdos625
