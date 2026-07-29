import Erdos625.PhaseEstimates
import Erdos625.Section8CanonicalThreeQuarterRho
import Mathlib.Tactic

/-!
# Section VIII: coarse phase corridor for the three-quarter deficit charge

The sharp local estimate in the manuscript is stronger than the second moment
needs.  The phase satisfies

`phaseNat n ~ (2 / log 2) * log n`,

and `2 / log 2 > 5/2`.  Thus it is eventually enough to use the coarse corridor

`(5/2) log n <= phaseNat n`.

Every four-endpoint overlap size is at least `alpha-5`.  Combined with the
three-quarter integer budget and the elementary lower bound `log 2 > 2/3`, this
gives

`(5/4) log n - 19/6 <= log 2 * floor((3m-1)/4)`.

Hence the denominator in the local charge already gains a factor of order
`n^(5/4)`, so the local base has the much coarser but still sufficient scale
`O(log n / n^(1/4))`.  This module proves the corridor and the finite logarithmic
budget; it deliberately leaves the final exponential conversion separate.
-/

namespace Erdos625

open Filter Asymptotics Set
open scoped Topology BigOperators

noncomputable section

set_option autoImplicit false

/-- A coarse lower phase corridor.  The constant `5/2` is chosen below the
limit `2/log 2` and is more than sufficient for the deficit product. -/
theorem eventually_five_halves_logOrder_le_phaseNat :
    ∀ᶠ n : Nat in atTop,
      (5 / 2 : Real) * logOrder n ≤ (phaseNat n : Real) := by
  have hDenom : ∀ᶠ n : Nat in atTop,
      (2 / q) * logOrder n ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : Nat)] with n hn
    have hlog : 0 < logOrder n := Real.log_pos (by exact_mod_cast hn)
    exact mul_ne_zero (div_ne_zero (by norm_num) q_ne_zero) hlog.ne'
  have hRatioOne : Tendsto
      ((fun n : Nat => (phaseNat n : Real)) /
        (fun n : Nat => (2 / q) * logOrder n)) atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one hDenom).mp
      phaseNat_isEquivalent_scaled_logOrder
  have hRatio : Tendsto
      (fun n : Nat => (phaseNat n : Real) / logOrder n)
      atTop (nhds (2 / q)) := by
    have hScaled := hRatioOne.const_mul (2 / q)
    convert hScaled using 1
    · funext n
      by_cases hlog : logOrder n = 0
      · simp [hlog]
      · change (phaseNat n : Real) / logOrder n =
            (2 / q) * ((phaseNat n : Real) / ((2 / q) * logOrder n))
        field_simp [q_ne_zero]
    · simp
  have hqUpper : q < (4 / 5 : Real) := by
    exact Real.log_two_lt_d9.trans (by norm_num)
  have hqLower : (1 / 2 : Real) < q := by
    exact (by norm_num : (1 / 2 : Real) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hLimitLower : (5 / 2 : Real) < 2 / q := by
    rw [lt_div_iff₀ q_pos]
    nlinarith
  have hLimitUpper : 2 / q < (4 : Real) := by
    rw [div_lt_iff₀ q_pos]
    nlinarith
  have hEventuallyRatio : ∀ᶠ n : Nat in atTop,
      (phaseNat n : Real) / logOrder n ∈ Set.Icc (5 / 2 : Real) 4 :=
    hRatio.eventually (Icc_mem_nhds hLimitLower hLimitUpper)
  have hLogPos : ∀ᶠ n : Nat in atTop, 0 < logOrder n := by
    filter_upwards [eventually_gt_atTop (1 : Nat)] with n hn
    exact Real.log_pos (by exact_mod_cast hn)
  filter_upwards [hEventuallyRatio, hLogPos] with n hnRatio hnLog
  exact (le_div_iff₀ hnLog).mp hnRatio.1

/-- The phase eventually exceeds the finite threshold needed to cast all
truncated natural-number subtractions as ordinary real subtractions. -/
theorem eventually_eight_lt_phaseNat :
    ∀ᶠ n : Nat in atTop, 8 < phaseNat n := by
  have hLog : ∀ᶠ n : Nat in atTop, (8 : Real) < logOrder n :=
    tendsto_logOrder_atTop.eventually (eventually_gt_atTop 8)
  filter_upwards
    [hLog, eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder]
      with n hnLog hnPhase
  exact_mod_cast (hnLog.trans_le hnPhase.1)

/-- Every four-endpoint overlap size is at least the smallest endpoint size
`alpha-5`. -/
theorem alpha_sub_five_le_fourEndpointOverlapSize
    (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    alpha - 5 ≤ fourEndpointOverlapSize alpha hAlpha i j := by
  fin_cases i <;> fin_cases j <;>
    simp [fourEndpointOverlapSize, fourEndpointSize,
      fourEndpointCoordinate, fourDeficitCoordinate, fourDeficit] <;> omega

/-- Division-free floor estimate for the three-quarter exponent. -/
theorem three_mul_alpha_sub_nineteen_le_four_mul_threeQuarterBudget
    (alpha m : Nat) (hm : alpha - 5 ≤ m) :
    3 * alpha - 19 ≤ 4 * ((3 * m - 1) / 4) := by
  omega

/-- Four-endpoint specialization of the preceding floor estimate. -/
theorem three_mul_alpha_sub_nineteen_le_four_mul_endpointBudget
    (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    3 * alpha - 19 ≤
      4 * ((3 * fourEndpointOverlapSize alpha hAlpha i j - 1) / 4) := by
  exact three_mul_alpha_sub_nineteen_le_four_mul_threeQuarterBudget
    alpha (fourEndpointOverlapSize alpha hAlpha i j)
      (alpha_sub_five_le_fourEndpointOverlapSize alpha hAlpha i j)

/-- Coarse real logarithmic budget.  It uses only `log 2 > 2/3`, the
five-halves phase corridor, and the finite endpoint floor estimate. -/
theorem five_fourths_log_sub_le_q_mul_endpointBudget
    (n alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    (hphase : (5 / 2 : Real) * logOrder n ≤ (alpha : Real))
    (i j : Fin 4) :
    (5 / 4 : Real) * logOrder n - 19 / 6 ≤
      q * (((3 * fourEndpointOverlapSize alpha hAlpha i j - 1) / 4 : Nat) : Real) := by
  let budget : Nat :=
    (3 * fourEndpointOverlapSize alpha hAlpha i j - 1) / 4
  have hnat : 3 * alpha - 19 ≤ 4 * budget := by
    exact three_mul_alpha_sub_nineteen_le_four_mul_endpointBudget
      alpha hAlpha i j
  have h19 : 19 ≤ 3 * alpha := by omega
  have hcast : 3 * (alpha : Real) - 19 ≤ 4 * (budget : Real) := by
    have hcastNat := congrArg (fun x : Nat => (x : Real)) hnat
    rw [Nat.cast_sub h19] at hcastNat
    norm_num at hcastNat ⊢
    exact hcastNat
  have hq : (2 / 3 : Real) ≤ q := by
    exact ((by norm_num : (2 / 3 : Real) < 0.6931471803).trans
      Real.log_two_gt_d9).le
  have hbudgetNonneg : 0 ≤ (budget : Real) := by positivity
  have hqmul : (2 / 3 : Real) * (budget : Real) ≤ q * (budget : Real) :=
    mul_le_mul_of_nonneg_right hq hbudgetNonneg
  dsimp only [budget]
  nlinarith

/-- Eventual form simultaneously valid for all sixteen endpoint types.  The
finite proof argument `hAlpha` is explicit so no theorem statement depends on a
hidden tactic-generated proof. -/
theorem eventually_five_fourths_log_sub_le_q_mul_endpointBudget :
    ∀ᶠ n : Nat in atTop,
      ∀ (hAlpha : 5 < phaseNat n) (i j : Fin 4),
        (5 / 4 : Real) * logOrder n - 19 / 6 ≤
          q * (((3 * fourEndpointOverlapSize (phaseNat n)
            hAlpha i j - 1) / 4 : Nat) : Real) := by
  filter_upwards
    [eventually_five_halves_logOrder_le_phaseNat,
      eventually_eight_lt_phaseNat]
      with n hphase hHigh
  intro hAlpha i j
  exact five_fourths_log_sub_le_q_mul_endpointBudget
    n (phaseNat n) hAlpha hHigh hphase i j

#print axioms eventually_five_halves_logOrder_le_phaseNat
#print axioms alpha_sub_five_le_fourEndpointOverlapSize
#print axioms three_mul_alpha_sub_nineteen_le_four_mul_endpointBudget
#print axioms five_fourths_log_sub_le_q_mul_endpointBudget

end

end Erdos625
