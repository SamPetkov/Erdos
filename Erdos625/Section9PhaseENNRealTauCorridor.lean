import Erdos625.PhaseEstimates
import Erdos625.Section9AttachmentAsymptotics
import Mathlib.Tactic

/-!
# Section IX: phase-controlled `ENNReal` tau corridor

This is only the numerical bridge needed to supply the strict tau hypothesis
of the accepted actual-attachment large-residual envelope.
-/

namespace Erdos625

open Filter
open scoped ENNReal Topology

noncomputable section

/-- Any finite `ENNReal` coefficient, a cap bounded by the concrete phase,
and the manuscript large-residual cutoff eventually give the strict
`ENNReal` tau corridor used by the attachment envelope. -/
theorem eventually_phaseControlled_ennreal_tau_lt_one_third
    (kappaQ : ENNReal) (hkappaQ : kappaQ ≠ ∞) :
    ∀ᶠ n : Nat in atTop,
      ∀ (U m : Nat),
        U ≤ phaseNat n →
        0 < m →
        (n : Real) / Real.log (n : Real) ^ 6 ≤ (m : Real) →
        kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal) <
          (1 / 3 : ENNReal) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ᶠ n in atTop, ∀ U m : ℕ, U ≤ phaseNat n → 0 < m → (n : ℝ) /Real.log n ^ 6 ≤ m → (kappaQ.toReal * U ^ 3 : ℝ) / m < 1 / 3 := by
    have h_logOrder : ∀ᶠ n in atTop, ∀ U : ℕ, U ≤ phaseNat n → U ≤ 4 * Real.log n := by
      filter_upwards [ eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder ] with n hn U hU using le_trans ( Nat.cast_le.mpr hU ) hn.2
    convert eventually_tau_lt_one_third ( kappaQ.toReal ) ( ENNReal.toReal_nonneg ) using 1;
    constructor <;> intro h;
    · convert eventually_tau_lt_one_third ( kappaQ.toReal ) ( ENNReal.toReal_nonneg ) using 1;
    · use 0;
      filter_upwards [ h_logOrder, h, Filter.eventually_gt_atTop 1 ] with n hn hn' hn'' U m hU hm hn'''; specialize hn' U m hm hn'''; simp_all +decide [ mul_div_assoc ] ;
      exact hn' ( by have := hn U hU; rw [ mul_div, le_div_iff₀ ( Real.log_pos one_lt_two ) ] ; nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, Real.log_pos one_lt_two, Real.log_le_log ( by positivity ) ( show ( n : ℝ ) ≥ 2 by norm_cast ) ] );
  filter_upwards [ hC ] with n hn U m hU hm hmn;
  convert ENNReal.ofReal_lt_ofReal_iff ( show ( 0 : ℝ ) < 1 / 3 by norm_num ) |>.2 ( hn U m hU hm hmn ) using 1;
  · rw [ ENNReal.ofReal_div_of_pos ( by positivity ), ENNReal.ofReal_mul ( by positivity ), ENNReal.ofReal_pow ( by positivity ) ] ; aesop;
  · rw [ ENNReal.ofReal_div_of_pos ] <;> norm_num

#print axioms eventually_phaseControlled_ennreal_tau_lt_one_third

end

end Erdos625
