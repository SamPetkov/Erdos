import Erdos625.Section10QuarterChainParameters
import Erdos625.Section10SimultaneousGreedyColoring
import Mathlib.Algebra.Order.Floor.Div

/-!
# Section X: numerical bound for the quarter-chain greedy colouring

This module isolates the floor/ceiling arithmetic in the deterministic
colouring bound.  It does not assert a graph event or a probability estimate.
The final additive `+ 1` is the honest loss from ceiling division.
-/

namespace Erdos625

open Filter
open scoped Topology

noncomputable section

/-- The defining coverage property of ceiling division. -/
theorem le_ceilDivNat_mul (a b : ℕ) (hb : 1 ≤ b) :
    a ≤ ceilDivNat a b * b := by
  have hpos : 0 < b := Nat.zero_lt_of_lt hb
  change a ≤ (a ⌈/⌉ b) * b
  have hcover : a ≤ b * (a ⌈/⌉ b) :=
    (ceilDiv_le_iff_le_mul hpos).1 le_rfl
  simpa [Nat.mul_comm] using hcover

/-- Ceiling division is at most ordinary natural-number division plus one. -/
theorem ceilDivNat_le_div_add_one (a b : ℕ) (hb : 1 ≤ b) :
    ceilDivNat a b ≤ a / b + 1 := by
  unfold ceilDivNat
  calc
    (a + b - 1) / b ≤ (a + b) / b :=
      Nat.div_le_div_right (Nat.sub_le (a + b) 1)
    _ = a / b + 1 := by
      rw [Nat.add_div_right]
      omega

/-- Real-valued form of the elementary ceiling-division estimate. -/
theorem ceilDivNat_cast_le_div_add_one (a b : ℕ) (hb : 1 ≤ b) :
    (ceilDivNat a b : ℝ) ≤ (a : ℝ) / (b : ℝ) + 1 := by
  calc
    (ceilDivNat a b : ℝ) ≤ (a / b + 1 : ℕ) := by
      exact_mod_cast ceilDivNat_le_div_add_one a b hb
    _ = (a / b : ℕ) + 1 := by norm_num
    _ ≤ (a : ℝ) / (b : ℝ) + 1 := by
      gcongr
      exact Nat.cast_div_le

/-- Eventually the concrete greedy-colouring count has the manuscript-scale
upper bound.  The starting cutoff is retained exactly and the only extra loss
is the explicit `+ 1` from ceiling division. -/
theorem quarterChain_greedy_count_real_upper_bound_eventually :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      (ceilDivNat m (quarterChainSteps n) + quarterChainStart n : ℝ) ≤
        14 * Real.log 4 * (m : ℝ) / Real.log n +
          (quarterChainStart n : ℝ) + 1 := by
  filter_upwards
      [one_le_quarterChainSteps_eventually,
        quarterChainSteps_real_lower_bound_eventually,
        Filter.eventually_gt_atTop 1] with n hsteps hstepsLower hn m
  have hlogPos : 0 < Real.log (n : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hn)
  have hlogFourPos : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hdenPos : 0 < (14 * Real.log 4 : ℝ) := by positivity
  have hstepPos : 0 < (quarterChainSteps n : ℝ) := by
    exact_mod_cast hsteps
  have hquotient :
      (m : ℝ) / (quarterChainSteps n : ℝ) ≤
        14 * Real.log 4 * (m : ℝ) / Real.log n := by
    have hbasePos :
        0 < Real.log (n : ℝ) / (14 * Real.log 4) := by positivity
    have hinv :
        ((quarterChainSteps n : ℝ))⁻¹ ≤
          (14 * Real.log 4) / Real.log n := by
      calc
        ((quarterChainSteps n : ℝ))⁻¹ =
            1 / (quarterChainSteps n : ℝ) := by rw [one_div]
        _ ≤ 1 / (Real.log (n : ℝ) / (14 * Real.log 4)) :=
          one_div_le_one_div_of_le hbasePos hstepsLower
        _ = (14 * Real.log 4) / Real.log n := by
          field_simp
    calc
      (m : ℝ) / (quarterChainSteps n : ℝ) =
          (m : ℝ) * ((quarterChainSteps n : ℝ))⁻¹ := by
            rw [div_eq_mul_inv]
      _ ≤ (m : ℝ) * ((14 * Real.log 4) / Real.log n) :=
        mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg m)
      _ = 14 * Real.log 4 * (m : ℝ) / Real.log n := by ring
  calc
    (ceilDivNat m (quarterChainSteps n) + quarterChainStart n : ℝ) =
        (ceilDivNat m (quarterChainSteps n) : ℝ) +
          (quarterChainStart n : ℝ) := by norm_num
    _ ≤ ((m : ℝ) / (quarterChainSteps n : ℝ) + 1) +
          (quarterChainStart n : ℝ) := by
      gcongr
      exact ceilDivNat_cast_le_div_add_one m (quarterChainSteps n) hsteps
    _ ≤ (14 * Real.log 4 * (m : ℝ) / Real.log n + 1) +
          (quarterChainStart n : ℝ) := by gcongr
    _ = 14 * Real.log 4 * (m : ℝ) / Real.log n +
          (quarterChainStart n : ℝ) + 1 := by ring

/-- The exact piecewise natural-number cost produced by greedy deletion:
small sets are coloured singly, while large sets use logarithmic independent
blocks and then colour the final cutoff vertices singly. -/
def quarterChainGreedyColorCost (n u : ℕ) : ℕ :=
  if u < quarterChainStart n then u
  else ceilDivNat u (quarterChainSteps n) + quarterChainStart n

/-- Eventually the logarithm is bounded by the real cube root. -/
theorem log_le_realCubeRoot_eventually :
    ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 3 : ℝ))
        atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop
      (r := (1 / 3 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  have hnat :
      Tendsto
        (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ (1 / 3 : ℝ))
        atTop (nhds 0) :=
    hreal.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [hnat.eventually_lt_const zero_lt_one,
        Filter.eventually_gt_atTop 0] with n hn hnPos
  have hrootPos : 0 < (n : ℝ) ^ (1 / 3 : ℝ) := by positivity
  exact ((div_lt_one hrootPos).mp hn).le

/-- Uniform manuscript-scale numerical bound for the exact piecewise greedy
cost.  The small branch introduces no ceiling loss.  In the large branch the
one-unit ceiling-division loss and the one-unit cube-root ceiling loss are
absorbed explicitly into `2 * u / log n`. -/
theorem quarterChainGreedyColorCost_eventually_le_linear_log_plus_cubeRoot :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ u : ℕ, u ≤ n →
        (quarterChainGreedyColorCost n u : ℝ) ≤
          C * (u : ℝ) / Real.log (n : ℝ) +
            (n : ℝ) ^ (1 / 3 : ℝ) := by
  refine ⟨14 * Real.log 4 + 2, by positivity, ?_⟩
  filter_upwards
      [quarterChain_greedy_count_real_upper_bound_eventually,
        log_le_realCubeRoot_eventually,
        Filter.eventually_gt_atTop 1] with n hcount hlogCube hn u _hu
  have hlogPos : 0 < Real.log (n : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hn)
  by_cases hsmall : u < quarterChainStart n
  · rw [quarterChainGreedyColorCost, if_pos hsmall]
    have huCube : (u : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
      contrapose! hsmall
      exact Nat.ceil_le.mpr hsmall.le
    have hlinear :
        0 ≤ (14 * Real.log 4 + 2) * (u : ℝ) / Real.log (n : ℝ) := by
      positivity
    linarith
  · rw [quarterChainGreedyColorCost, if_neg hsmall]
    have hstart :
        (quarterChainStart n : ℝ) <
          (n : ℝ) ^ (1 / 3 : ℝ) + 1 := by
      exact Nat.ceil_lt_add_one (by positivity)
    have hrootLeStart :
        (n : ℝ) ^ (1 / 3 : ℝ) ≤ (quarterChainStart n : ℝ) :=
      Nat.le_ceil _
    have hstartLeU : quarterChainStart n ≤ u := le_of_not_gt hsmall
    have hrootLeU : (n : ℝ) ^ (1 / 3 : ℝ) ≤ (u : ℝ) := by
      exact hrootLeStart.trans (by exact_mod_cast hstartLeU)
    have hlogLeU : Real.log (n : ℝ) ≤ (u : ℝ) :=
      hlogCube.trans hrootLeU
    have habsorb :
        (2 : ℝ) ≤ 2 * (u : ℝ) / Real.log (n : ℝ) := by
      rw [le_div_iff₀ hlogPos]
      linarith
    calc
      ((ceilDivNat u (quarterChainSteps n) + quarterChainStart n : ℕ) : ℝ) ≤
          14 * Real.log 4 * (u : ℝ) / Real.log n +
            (quarterChainStart n : ℝ) + 1 :=
        by simpa only [Nat.cast_add] using hcount u
      _ ≤ 14 * Real.log 4 * (u : ℝ) / Real.log n +
            ((n : ℝ) ^ (1 / 3 : ℝ) + 1) + 1 := by
        linarith
      _ = 14 * Real.log 4 * (u : ℝ) / Real.log n +
            (n : ℝ) ^ (1 / 3 : ℝ) + 2 := by ring
      _ ≤ 14 * Real.log 4 * (u : ℝ) / Real.log n +
            (n : ℝ) ^ (1 / 3 : ℝ) +
              (2 * (u : ℝ) / Real.log n) := by
        gcongr
      _ = (14 * Real.log 4 + 2) * (u : ℝ) / Real.log n +
            (n : ℝ) ^ (1 / 3 : ℝ) := by ring

#print axioms le_ceilDivNat_mul
#print axioms ceilDivNat_le_div_add_one
#print axioms ceilDivNat_cast_le_div_add_one
#print axioms quarterChain_greedy_count_real_upper_bound_eventually
#print axioms log_le_realCubeRoot_eventually
#print axioms quarterChainGreedyColorCost_eventually_le_linear_log_plus_cubeRoot

end

end Erdos625
