import Erdos625.Section9CanonicalDemandProductEstimate
import Mathlib.Tactic

/-!
# Section IX: large-residual exponent envelope

This module gives the coarse deterministic envelope used in the
large-residual branch.  It controls both geometric denominators when the
normalized residual scale is at most one third and substitutes those bounds
into `residualProductExponentMajorant`.

It does not choose the manuscript parameters or prove that the resulting
envelope is asymptotically negligible.
-/

namespace Erdos625

open scoped ENNReal

noncomputable section

/-- The two geometric denominators in the residual product exponent have
uniform coarse bounds throughout the one-third corridor. -/
theorem residual_geometric_denominators_le
    (tau : ENNReal) (htau : tau ≤ (1 / 3 : ENNReal)) :
    tau ^ 4 * (1 - tau ^ 2)⁻¹ ≤ 2 * tau ^ 4 ∧
      let beta := tau * (1 - tau)⁻¹
      beta * (1 - beta)⁻¹ ≤ 3 * tau := by
  rcases eq_or_ne tau 0 <;> simp_all +decide [mul_comm]
  constructor
  · gcongr
    rw [← ENNReal.inv_le_inv, inv_inv]
    refine' le_trans _
      (tsub_le_tsub_left
        (pow_le_pow_left'
          (show tau ≤ 1 / 3 by
            rw [ENNReal.le_div_iff_mul_le] <;> norm_num
            aesop)
          2)
        _) <;>
      norm_num
    rw [← ENNReal.toReal_le_toReal] <;> norm_num
    rw [ENNReal.toReal_sub_of_le] <;> norm_num
    rw [← ENNReal.toReal_le_toReal] <;> norm_num
  · rcases eq_or_ne (1 - tau) 0 <;> simp_all +decide [mul_assoc]
    · rw [tsub_eq_zero_iff_le] at *
      exact absurd htau
        (not_le_of_gt
          (lt_of_lt_of_le (by norm_num) (mul_le_mul_right' ‹1 ≤ tau› _)))
    · gcongr
      rw [← ENNReal.toReal_le_toReal] <;> norm_num
      · rw [← mul_inv, ENNReal.toReal_sub_of_le] <;> norm_num
        · rw [ENNReal.toReal_sub_of_le] <;> norm_num
          · rcases eq_or_ne tau ⊤ with rfl | htau' <;>
              simp_all +decide [ENNReal.toReal_mul]
            rw [← mul_inv, inv_le_comm₀] <;> norm_num
            · rw [ENNReal.toReal_sub_of_le] <;> norm_num
              · rw [← ENNReal.toReal_le_toReal] at * <;> norm_num at *
                · nlinarith
                    [inv_mul_cancel₀
                      (show (1 - tau.toReal) ≠ 0 from
                        sub_ne_zero_of_ne <| by linarith),
                      show 0 ≤ tau.toReal from ENNReal.toReal_nonneg]
                · aesop
              · exact le_trans
                  (le_mul_of_one_le_right (zero_le _) (by norm_num)) htau
            · refine' mul_pos _ _ <;> norm_num
              · rw [← div_eq_mul_inv, div_lt_one]
                · rw [ENNReal.toReal_sub_of_le] <;> norm_num
                  · rw [← ENNReal.toReal_le_toReal] at * <;> norm_num at *
                    · linarith
                    · aesop
                  · exact le_trans
                      (le_mul_of_one_le_right (by positivity) (by norm_num)) htau
                · exact ENNReal.toReal_pos (by aesop) (by aesop)
              · rw [← ENNReal.toReal_le_toReal] at * <;> norm_num at *
                · linarith
                · exact ENNReal.mul_ne_top htau' (by norm_num)
          · rw [← ENNReal.toReal_le_toReal] <;> norm_num
            · rw [← div_eq_mul_inv, div_le_iff₀] <;> norm_num
              · rw [ENNReal.toReal_sub_of_le] <;> norm_num
                · rw [← ENNReal.toReal_le_toReal] at * <;> norm_num at *
                  · linarith
                  · aesop
                · exact le_trans
                    (le_mul_of_one_le_right (zero_le _) (by norm_num)) htau
              · exact ENNReal.toReal_pos (by aesop) (by aesop)
            · rw [ENNReal.mul_eq_top]
              aesop
        · exact le_trans
            (le_mul_of_one_le_right (zero_le _) (by norm_num)) htau
      · simp_all +decide [ENNReal.mul_eq_top]
        rw [tsub_eq_zero_iff_le] at *
        rw [← ENNReal.toReal_le_toReal] <;> norm_num
        · rw [← div_eq_mul_inv, div_lt_one]
          · rw [ENNReal.toReal_sub_of_le] <;> norm_num
            · rw [← ENNReal.toReal_le_toReal] at * <;> norm_num at *
              · linarith
              · aesop
              · aesop
            · exact le_trans
                (le_mul_of_one_le_right (by positivity) (by norm_num)) htau
          · exact ENNReal.toReal_pos
              (ne_of_gt <| tsub_pos_of_lt <| lt_of_not_ge ‹_›)
              (ne_of_lt <| lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top)
        · simp_all +decide [ENNReal.mul_eq_top]
          exact
            ⟨ne_of_gt (tsub_pos_of_lt ‹_›),
              ne_of_lt (lt_of_lt_of_le ‹_› (by norm_num))⟩

/-- Coarse explicit envelope for the large-residual product exponent. -/
theorem residualProductExponentMajorant_le_largeResidualEnvelope
    (kappaLambda kappaQ : ENNReal) (cardA matchingCard U m : ℕ)
    (htau : let tau : ENNReal :=
        kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)
      tau ≤ (1 / 3 : ENNReal)) :
    let tau : ENNReal :=
      kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)
    residualProductExponentMajorant kappaLambda kappaQ
        cardA matchingCard U m ≤
      kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal) +
        2 * (cardA : ENNReal) * tau ^ 4 +
        (((6 * matchingCard : ℕ) : ENNReal) * tau) := by
  convert add_le_add_three le_rfl
      (mul_le_mul_left'
        (residual_geometric_denominators_le _ htau).1 _)
      (mul_le_mul_left'
        (residual_geometric_denominators_le _ htau).2 _) using 1
  grobner

#print axioms residual_geometric_denominators_le
#print axioms residualProductExponentMajorant_le_largeResidualEnvelope

end

end Erdos625
