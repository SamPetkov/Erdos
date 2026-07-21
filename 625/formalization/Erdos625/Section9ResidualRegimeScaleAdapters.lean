import Erdos625.Section9ResidualAsymptoticArithmetic
import Erdos625.Section9CanonicalDemandSmallResidualBound
import Mathlib.Tactic

/-!
# Section IX: residual-regime scale adapters

This module converts the exact finite small-residual power bound into the
manuscript exponential scale and transports it to one attained canonical
demand.  It does not estimate the skeleton/incidence sum or prove Lemma 9.1.
-/

namespace Erdos625

open scoped ENNReal

set_option autoImplicit false

/-- The literal natural exponent `U*m/2` from the small-residual branch is
bounded by the manuscript-scale exponential whenever `U = O(L)` and
`m ≤ n/L^6`. -/
theorem smallResidual_two_pow_le_exp_scale
    (n L C : ℝ) (U m : ℕ)
    (hn : 0 ≤ n)
    (hL : 0 < L)
    (hC : 0 ≤ C)
    (hU : (U : ℝ) ≤ C * L)
    (hm : (m : ℝ) ≤ n / L ^ 6) :
    ((2 : ℝ≥0∞) ^ (U * m / 2)) ≤
      ENNReal.ofReal
        (Real.exp ((C * Real.log 2 / 2) * (n / L ^ 5))) := by
  convert @ennreal_two_pow_nat_le_of_log_bound _ _ _ using 1
  have hlog :
      Real.log 2 * (U * m / 2 : ℝ) ≤
        (C * Real.log 2 / 2) * (n / L ^ 5) := by
    convert smallResidualExponent_bound n L (U : ℝ) m C
      (by exact hn) (by exact hL) (by positivity) (by positivity)
      (by exact hC) (by exact hU) (by exact hm) using 1 <;> norm_num
  exact le_trans
    (mul_le_mul_of_nonneg_left
      (Nat.cast_div_le .. |> le_trans <| by norm_num)
      (Real.log_nonneg one_le_two))
    hlog

/-- The exact raw attachment term for one attained canonical demand inherits
`exp(O(n/L^5))` in the small-residual regime.  The bare canonical reward and
labelled-witness incidence remain explicit for the later skeleton sum. -/
theorem canonicalDemandRawAttachmentTerm_le_smallResidualExpScale
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (htotal : (∑ a, row a) = ∑ b, col b)
    (hrowCap : ∀ a, row a ≤ U) (hcolCap : ∀ b, col b ≤ U)
    (demand : canonicalDemandImage row col U)
    (n L C : ℝ)
    (hn : 0 ≤ n)
    (hL : 0 < L)
    (hC : 0 ≤ C)
    (hU : (U : ℝ) ≤ C * L)
    (hm : (canonicalDemandResidualTotal row col U demand : ℝ) ≤
      n / L ^ 6) :
    canonicalDemandRawAttachmentTerm row col U htotal demand ≤
      (canonicalDemandLocalReward demand : ENNReal) *
        (labelledWitnessIncidence demand.1 row col *
          ENNReal.ofReal
            (Real.exp ((C * Real.log 2 / 2) * (n / L ^ 5)))) := by
  have hsmall := canonicalDemandRawAttachmentTerm_le_smallResidualBound
    row col U htotal hrowCap hcolCap demand
  have hpow := smallResidual_two_pow_le_exp_scale n L C U
    (canonicalDemandResidualTotal row col U demand)
    hn hL hC hU hm
  exact hsmall.trans (mul_le_mul_right (mul_le_mul_right hpow _) _)

#print axioms smallResidual_two_pow_le_exp_scale
#print axioms canonicalDemandRawAttachmentTerm_le_smallResidualExpScale

end Erdos625
