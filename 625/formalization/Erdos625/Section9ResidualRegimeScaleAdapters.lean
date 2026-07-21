import Erdos625.Section9ResidualAsymptoticArithmetic
import Erdos625.Section9CanonicalDemandSmallResidualBound
import Mathlib.Tactic

/-!
# Section IX: residual-regime scale adapters

This module converts the exact finite small-residual power bound into the
manuscript exponential scale and transports it to one attained canonical
demand.  It also supplies the elementary eventual logarithmic inequalities
needed to instantiate the accepted large-residual arithmetic envelope.

It does not estimate the skeleton/incidence sum or prove Lemma 9.1.
-/

namespace Erdos625

open Filter
open scoped ENNReal Topology

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
  have hcast :
      ((U * m / 2 : ℕ) : ℝ) ≤ (U : ℝ) * (m : ℝ) / 2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Nat.cast_div_le (m := U * m) (n := 2) :
        (((U * m) / 2 : ℕ) : ℝ) ≤ ((U * m : ℕ) : ℝ) / (2 : ℝ))
  have hround :
      Real.log 2 * ((U * m / 2 : ℕ) : ℝ) ≤
        Real.log 2 * ((U : ℝ) * (m : ℝ) / 2) :=
    mul_le_mul_of_nonneg_left hcast (Real.log_nonneg one_le_two)
  have hscale := smallResidualExponent_bound n L (U : ℝ) (m : ℝ) C
    hn hL (Nat.cast_nonneg U) (Nat.cast_nonneg m) hC hU hm
  exact ennreal_two_pow_nat_le_of_log_bound (U * m / 2)
    ((C * Real.log 2 / 2) * (n / L ^ 5)) (hround.trans hscale)

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

/-- Eventually `log n` is positive, `(log n)^2 ≤ n`, and
`(log n)^28 ≤ n^3`. -/
theorem eventually_log_growth_bounds :
    ∀ᶠ n : ℕ in atTop,
      0 < Real.log (n : ℝ) ∧
      Real.log (n : ℝ) ^ 2 ≤ (n : ℝ) ∧
      Real.log (n : ℝ) ^ 28 ≤ (n : ℝ) ^ 3 := by
  have h_pos : ∀ᶠ n : ℕ in atTop, 0 < Real.log n := by
    exact eventually_atTop.mpr
      ⟨2, fun n hn => Real.log_pos (Nat.one_lt_cast.mpr hn)⟩
  have h_sq : ∀ᶠ n : ℕ in atTop, (Real.log n) ^ 2 ≤ n := by
    have h_lim : Tendsto (fun n : ℕ => (Real.log n) ^ 2 / (n : ℝ)) atTop (nhds 0) :=
      Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop
    filter_upwards [h_lim.eventually (gt_mem_nhds zero_lt_one),
      eventually_gt_atTop 0] with n hn hn0
    rw [div_lt_one (by positivity)] at hn
    linarith
  have h_28 : ∀ᶠ n : ℕ in atTop, (Real.log n) ^ 28 ≤ n := by
    have h_lim : Tendsto (fun n : ℕ => (Real.log n) ^ 28 / (n : ℝ)) atTop (nhds 0) :=
      Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop
    filter_upwards [h_lim.eventually (gt_mem_nhds zero_lt_one),
      eventually_gt_atTop 0] with n hn hn0
    rw [div_lt_one (by positivity)] at hn
    linarith
  filter_upwards [h_pos, h_sq, h_28, eventually_ge_atTop 1] with n hpos hsq h28 hn
  exact ⟨hpos, hsq, h28.trans (by
    exact_mod_cast Nat.le_self_pow (by norm_num) n)⟩

/-- The accepted finite large-residual arithmetic envelope specializes
uniformly to `O((log n)^8)` once `L = log n`. -/
theorem eventually_largeResidualEnvelope_logScale
    (kappaLambda kappaQ C_U : ℝ)
    (hkappaLambda0 : 0 ≤ kappaLambda)
    (hkappaQ0 : 0 ≤ kappaQ)
    (hCU0 : 0 ≤ C_U) :
    ∀ᶠ n : ℕ in atTop,
      ∀ U m A H : ℝ,
        0 ≤ U →
        0 < m →
        0 ≤ A →
        0 ≤ H →
        (n : ℝ) / Real.log (n : ℝ) ^ 6 ≤ m →
        U ≤ C_U * Real.log (n : ℝ) →
        A ≤ (n : ℝ) →
        H * U ≤ 2 * (n : ℝ) →
        kappaLambda * U ^ 4 / m +
              2 * A * (kappaQ * U ^ 3 / m) ^ 4 +
              6 * H * (kappaQ * U ^ 3 / m) ≤
          (kappaLambda * C_U ^ 4 +
              2 * kappaQ ^ 4 * C_U ^ 12 +
              12 * kappaQ * C_U ^ 2) *
            Real.log (n : ℝ) ^ 8 := by
  filter_upwards [eventually_log_growth_bounds, eventually_gt_atTop 0] with n hlog hn
  intro U m A H hU0 hm0 hA0 hH0 hmass hU hA hH
  exact largeResidualEnvelope_bound
    (n := (n : ℝ)) (L := Real.log (n : ℝ))
    (U := U) (m := m) (A := A) (H := H)
    (kappaLambda := kappaLambda) (kappaQ := kappaQ) (C_U := C_U)
    (by exact_mod_cast hn) hlog.1 hU0 hm0 hA0 hH0
    hkappaLambda0 hkappaQ0 hCU0 hmass hU hA hH hlog.2.1 hlog.2.2

#print axioms smallResidual_two_pow_le_exp_scale
#print axioms canonicalDemandRawAttachmentTerm_le_smallResidualExpScale
#print axioms eventually_log_growth_bounds
#print axioms eventually_largeResidualEnvelope_logScale

end Erdos625
