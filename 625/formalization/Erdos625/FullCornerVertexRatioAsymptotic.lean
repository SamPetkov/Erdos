import Erdos625.PartialDiagonalCentralLogEnvelope
import Erdos625.PhaseEstimates
import Mathlib.Tactic

/-!
# Full-corner vertex-ratio exponent

This module isolates the canonical `n / 32` vertex-ratio power from manuscript
Section VII equation (7.26).  It deliberately contains no independent-set
first-moment asymptotic, midpoint multiplicity, activity sum, or aggregate
partial-diagonal estimate.
-/

namespace Erdos625

open Filter
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- For each canonical deficit coordinate, the logarithm of the full-corner
vertex-ratio power has normalized exponent `-10`. -/
theorem midpointFullCornerVertexRatio_logExponent_tendsto_neg_ten
    (i : Fin 4) :
    Tendsto
      (fun n : Nat =>
        ((midpointPartialDiagonalSize (phaseNat n) i : Real) *
            Real.log
              (((n / 32 + midpointPartialDiagonalSize (phaseNat n) i : Nat) : Real) /
                (n : Real))) /
          logOrder n)
      atTop
      (nhds (-10 : Real)) := by
  have hq : q ≠ 0 := q_ne_zero
  have hDenom : ∀ᶠ n : Nat in atTop, (2 / q) * logOrder n ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : Nat)] with n hn
    have hlog : 0 < logOrder n := Real.log_pos (by exact_mod_cast hn)
    exact mul_ne_zero (div_ne_zero (by norm_num) hq) hlog.ne'
  have hRatioOne : Tendsto
      ((fun n : Nat => (phaseNat n : Real)) /
        (fun n : Nat => (2 / q) * logOrder n)) atTop (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hDenom).mp
      phaseNat_isEquivalent_scaled_logOrder
  have hP : Tendsto (fun n : Nat => (phaseNat n : Real) / logOrder n) atTop
      (nhds (2 / q)) := by
    have hScaled := hRatioOne.const_mul (2 / q)
    convert hScaled using 1
    · funext n
      by_cases hlog : logOrder n = 0
      · simp [hlog]
      · change (phaseNat n : Real) / logOrder n =
            (2 / q) * ((phaseNat n : Real) / ((2 / q) * logOrder n))
        field_simp
    · simp
  have hPo : Tendsto (fun n : Nat => (phaseNat n : Real) / (n : Real)) atTop
      (nhds 0) :=
    (phaseNat_isTheta_logOrder.1.trans_isLittleO
      logOrder_isLittleO_natCast).tendsto_div_nhds_zero
  simp only [midpointPartialDiagonalSize]
  set d : Nat := fourDeficit i with hd
  have hdle : d ≤ 5 := by
    have hi : i.1 < 4 := i.2
    simp only [hd, fourDeficit]
    omega
  have hA : Tendsto
      (fun n : Nat => ((phaseNat n - d : Nat) : Real) / logOrder n) atTop
      (nhds (2 / q)) := by
    have hzero : Tendsto (fun n : Nat => (d : Real) / logOrder n) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_logOrder_atTop
    have hsub := hP.sub hzero
    rw [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_five_lt_phaseNat] with n hn
    have hdn : d ≤ phaseNat n := by omega
    rw [Nat.cast_sub hdn, sub_div]
  have hfloor : Tendsto (fun n : Nat => ((n / 32 : Nat) : Real) / (n : Real))
      atTop (nhds (1 / 32)) := by
    have hlow : Tendsto (fun n : Nat => (1 / 32 : Real) - 1 / (n : Real)) atTop
        (nhds (1 / 32)) := by
      simpa using
        (tendsto_const_nhds (x := (1 / 32 : Real)) (f := atTop (α := Nat))).sub
          tendsto_one_div_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow
      (tendsto_const_nhds (x := (1 / 32 : Real))) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (0 : Real) < n := by exact_mod_cast hn
      have h2 : n ≤ 32 * (n / 32) + 31 := by omega
      have hr2 : (n : Real) ≤ 32 * ((n / 32 : Nat) : Real) + 31 := by
        exact_mod_cast h2
      have hrw : (1 / 32 : Real) - 1 / (n : Real) =
          ((n : Real) - 32) / (32 * (n : Real)) := by
        field_simp
      rw [hrw, div_le_div_iff₀ (by positivity) hnR]
      nlinarith
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (0 : Real) < n := by exact_mod_cast hn
      have h1 : 32 * (n / 32) ≤ n := by omega
      have hr1 : 32 * ((n / 32 : Nat) : Real) ≤ (n : Real) := by exact_mod_cast h1
      rw [div_le_div_iff₀ hnR (by norm_num)]
      linarith
  have hsmall : Tendsto
      (fun n : Nat => ((phaseNat n - d : Nat) : Real) / (n : Real)) atTop
      (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hPo ?_ ?_
    · filter_upwards with n
      positivity
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (0 : Real) < n := by exact_mod_cast hn
      have hle : ((phaseNat n - d : Nat) : Real) ≤ (phaseNat n : Real) := by
        exact_mod_cast Nat.sub_le (phaseNat n) d
      gcongr
  have hB : Tendsto
      (fun n : Nat =>
        ((n / 32 + (phaseNat n - d) : Nat) : Real) / (n : Real)) atTop
      (nhds (1 / 32)) := by
    have hsum := hfloor.add hsmall
    rw [add_zero] at hsum
    refine hsum.congr ?_
    intro n
    push_cast
    rw [add_div]
  have hlog32 : Real.log (1 / 32 : Real) = -5 * q := by
    rw [one_div, Real.log_inv]
    have h32 : (32 : Real) = 2 ^ (5 : Nat) := by norm_num
    rw [h32, Real.log_pow]
    simp [q]
  have hC : Tendsto
      (fun n : Nat =>
        Real.log (((n / 32 + (phaseNat n - d) : Nat) : Real) / (n : Real)))
      atTop (nhds (-5 * q)) := by
    have hcomp :=
      (Real.continuousAt_log (by norm_num : (1 / 32 : Real) ≠ 0)).tendsto.comp hB
    rw [hlog32] at hcomp
    exact hcomp
  have hmul := hA.mul hC
  have hval : (2 / q) * (-5 * q) = -10 := by
    field_simp
    norm_num
  rw [hval] at hmul
  refine hmul.congr ?_
  intro n
  rw [div_mul_eq_mul_div]

end

end Erdos625
