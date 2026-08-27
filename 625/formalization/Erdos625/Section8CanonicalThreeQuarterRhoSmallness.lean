import Erdos625.Section8CanonicalThreeQuarterRho
import Erdos625.Section8CoarsePhaseCorridor
import Mathlib.Tactic

namespace Erdos625

open Filter
open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

private theorem eventually_endpointThreeQuarter_decay_margin :
    ∀ᶠ n : Nat in atTop,
      64 * Real.exp (19 / 6 : Real) * logOrder n /
          (n : Real) ^ (1 / 4 : Real) ≤ 1 := by
  have hreal :
      Tendsto (fun x : Real => Real.log x / x ^ (1 / 4 : Real))
        atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop
      (r := (1 / 4 : Real)) (by norm_num)).tendsto_div_nhds_zero
  have hnat :
      Tendsto (fun n : Nat => logOrder n / (n : Real) ^ (1 / 4 : Real))
        atTop (nhds 0) := by
    simpa only [Function.comp_apply, Function.comp_def, logOrder] using
      hreal.comp tendsto_natCast_atTop_atTop
  have hscaled :
      Tendsto (fun n : Nat =>
        (64 * Real.exp (19 / 6 : Real)) *
          (logOrder n / (n : Real) ^ (1 / 4 : Real))) atTop (nhds 0) := by
    simpa using hnat.const_mul (64 * Real.exp (19 / 6 : Real))
  filter_upwards [hscaled.eventually_lt_const zero_lt_one] with n hn
  calc
    64 * Real.exp (19 / 6 : Real) * logOrder n /
          (n : Real) ^ (1 / 4 : Real) =
        (64 * Real.exp (19 / 6 : Real)) *
          (logOrder n / (n : Real) ^ (1 / 4 : Real)) := by ring
    _ ≤ 1 := hn.le

/-- The explicit sum of all sixteen endpoint-type three-quarter bases is
eventually small enough for the canonical finite Section VIII reduction. -/
theorem eventually_fourEndpointThreeQuarterRho_le_one :
    ∀ᶠ n : Nat in atTop,
      ∀ hAlpha : 5 < phaseNat n,
        fourEndpointThreeQuarterRho n (phaseNat n) hAlpha ≤ (1 : ENNReal) := by
  filter_upwards
    [eventually_five_fourths_log_sub_le_q_mul_endpointBudget,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      eventually_endpointThreeQuarter_decay_margin,
      eventually_gt_atTop (1 : Nat)] with n hbudget hphase hdecay hn
  intro hAlpha
  have hnPos : (0 : Real) < n := by positivity
  have hterm : ∀ i j : Fin 4,
      (threeQuarterCellBase n
        (fourEndpointOverlapSize (phaseNat n) hAlpha i j)).toReal ≤
          4 * Real.exp (19 / 6 : Real) * logOrder n /
            (n : Real) ^ (1 / 4 : Real) := by
    intro i j
    let m := fourEndpointOverlapSize (phaseNat n) hAlpha i j
    let b : Nat := (3 * m - 1) / 4
    have hb := hbudget hAlpha i j
    change (5 / 4 : Real) * logOrder n - 19 / 6 ≤ q * (b : Real) at hb
    have hexp := (Real.exp_le_exp.mpr hb)
    have hpow :
        (n : Real) ^ (5 / 4 : Real) / Real.exp (19 / 6 : Real) ≤
          (2 : Real) ^ b := by
      rw [Real.exp_sub] at hexp
      rw [show Real.exp ((5 / 4 : Real) * logOrder n) =
          (n : Real) ^ (5 / 4 : Real) by
        rw [Real.rpow_def_of_pos hnPos, logOrder]
        (congr 1; ring)]
        at hexp
      rw [show Real.exp (q * (b : Real)) = (2 : Real) ^ b by
        rw [show q * (b : Real) = (b : Real) * q by ring,
          Real.exp_nat_mul, q, Real.exp_log (by norm_num : (0 : Real) < 2)]] at hexp
      exact hexp
    have hm : (m : Real) ≤ 4 * logOrder n := by
      exact (Nat.cast_le.mpr (fourEndpointOverlapSize_le_alpha
        (phaseNat n) hAlpha i j)).trans hphase.2
    have hdenPos : (0 : Real) < (2 : Real) ^ b := by positivity
    have hbase :
        (n : Real) * (m : Real) / (2 : Real) ^ b ≤
          Real.exp (19 / 6 : Real) * (m : Real) /
            (n : Real) ^ (1 / 4 : Real) := by
      have hnRpowPos : 0 < (n : Real) ^ (1 / 4 : Real) := by positivity
      rw [div_le_div_iff₀ hdenPos hnRpowPos]
      calc
        (n : Real) * (m : Real) * (n : Real) ^ (1 / 4 : Real) =
            ((n : Real) ^ (5 / 4 : Real) / Real.exp (19 / 6 : Real)) *
              (m : Real) * Real.exp (19 / 6 : Real) := by
          rw [show (5 / 4 : Real) = 1 + 1 / 4 by ring,
            Real.rpow_add hnPos, Real.rpow_one]
          field_simp [Real.exp_ne_zero]
        _ ≤ (2 : Real) ^ b * (m : Real) * Real.exp (19 / 6 : Real) := by
          gcongr
        _ = Real.exp (19 / 6 : Real) * (m : Real) * (2 : Real) ^ b := by ring
    rw [threeQuarterCellBase, ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat]
    exact hbase.trans (by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hm (Real.exp_pos (19 / 6 : Real)).le])
  have hcellTop : ∀ i j : Fin 4,
      threeQuarterCellBase n
          (fourEndpointOverlapSize (phaseNat n) hAlpha i j) ≠ ⊤ := by
    intro i j
    rw [threeQuarterCellBase]
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top n)
        (ENNReal.natCast_ne_top
          (fourEndpointOverlapSize (phaseNat n) hAlpha i j))
    · exact pow_ne_zero _ (by norm_num : (2 : ENNReal) ≠ 0)
  have hrhoTop : fourEndpointThreeQuarterRho n (phaseNat n) hAlpha ≠ ⊤ := by
    rw [fourEndpointThreeQuarterRho]
    apply ENNReal.sum_ne_top.mpr
    intro i hi
    apply ENNReal.sum_ne_top.mpr
    intro j hj
    exact hcellTop i j
  apply (ENNReal.toReal_le_toReal hrhoTop (by simp)).mp
  rw [ENNReal.toReal_one]
  rw [fourEndpointThreeQuarterRho, ENNReal.toReal_sum]
  · have hinner : ∀ i : Fin 4,
        (∑ j : Fin 4, threeQuarterCellBase n
          (fourEndpointOverlapSize (phaseNat n) hAlpha i j)).toReal =
        ∑ j : Fin 4, (threeQuarterCellBase n
          (fourEndpointOverlapSize (phaseNat n) hAlpha i j)).toReal := by
      intro i
      apply ENNReal.toReal_sum
      intro j hj
      exact hcellTop i j
    simp_rw [hinner]
    calc
      (∑ i : Fin 4, ∑ j : Fin 4,
          (threeQuarterCellBase n
            (fourEndpointOverlapSize (phaseNat n) hAlpha i j)).toReal) ≤
          ∑ i : Fin 4, ∑ _j : Fin 4,
            (4 * Real.exp (19 / 6 : Real) * logOrder n /
              (n : Real) ^ (1 / 4 : Real)) := by
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = 64 * Real.exp (19 / 6 : Real) * logOrder n /
            (n : Real) ^ (1 / 4 : Real) := by
        norm_num
        ring
      _ ≤ 1 := hdecay
  · intro i hi
    apply ENNReal.sum_ne_top.mpr
    intro j hj
    exact hcellTop i j

#print axioms eventually_fourEndpointThreeQuarterRho_le_one

end

end Erdos625
