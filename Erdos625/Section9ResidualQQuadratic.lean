import Erdos625.Section9CappedFixedFExpansion
import Erdos625.Section9FiniteAnalyticEndpoint
import Mathlib.Tactic

/-!
# Section IX: universal residual-q quadratic bound

This module transports the accepted finite real endpoint estimate to the
literal `ENNReal` residual kernel. It is a pointwise analytic bridge only: it
does not identify a conditioned residual event, prove an attachment estimate,
or assemble Lemma 9.1.
-/

universe u v

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- One finite positive `ENNReal` constant bounds the literal Section IX
`residualQ` quadratically in the literal configuration-cell parameter,
simultaneously for all finite row/column type families. -/
theorem existsAbsoluteResidualQQuadraticBound :
    ∃ κ : ℝ≥0∞, 0 < κ ∧ κ ≠ ∞ ∧
      ∀ {A : Type u} {B : Type v} [Fintype A] [Fintype B]
          [DecidableEq A] [DecidableEq B]
          (M : Finset (A × B)) (U R m : ℕ)
          (row : A → ℕ) (col : B → ℕ),
        0 < m →
        (∑ a, row a) = m →
        R = U / 2 →
        (∀ a b, (a, b) ∉ M →
          (configurationCellTheta row col m a b).toReal ≤
            Real.exp 1 * (U : ℝ) ^ 2 / (m : ℝ)) →
        2 ^ U ≤ m ^ 3 →
        ∀ a b,
          residualQ M R row col a b ≤
            κ * configurationCellTheta row col m a b ^ 2 := by
  obtain ⟨ C, hC₀, hC ⟩ := existsAbsoluteFiniteEndpointConstant;
  use ENNReal.ofReal C;
  refine' ⟨ ENNReal.ofReal_pos.mpr hC₀, ENNReal.ofReal_ne_top, _ ⟩;
  intro A B _ _ _ _ M U R m row col hm hsum hR hbound hpow a b; by_cases hab : ( a, b ) ∈ M <;> simp +decide [ hab, residualQ ] ;
  have h_residLambda : residualLambda M R row col a b = ENNReal.ofReal (endpointLambda R (configurationCellTheta row col m a b).toReal) := by
    unfold residualLambda; simp +decide [ *, endpointLambda ] ;
    rw [ ENNReal.ofReal_sum_of_nonneg ];
    · refine' Finset.sum_congr rfl fun x hx => _;
      rw [ ENNReal.ofReal_div_of_pos ( by positivity ), ENNReal.ofReal_mul ( by
        unfold endpointIncrement; simp +decide [ endpointRewardNat ] ;
        split_ifs <;> norm_num at *;
        · exact pow_le_pow_right₀ ( by norm_num ) ( Nat.sub_le_sub_right ( Nat.choose_le_choose _ ( Nat.pred_le _ ) ) _ );
        · omega;
        · exact one_le_pow₀ ( by norm_num ) ), ENNReal.ofReal_pow ( by
        exact ENNReal.toReal_nonneg ) ];
      rw [ show endpointIncrement x = ( residualRewardIncrement x : ℝ ) from ?_ ];
      · rw [ ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, ENNReal.ofReal_toReal ];
        unfold configurationCellTheta; simp +decide [ eulerENNReal ] ;
        simp +decide [ ENNReal.div_eq_top, hm.ne' ];
        exact ENNReal.mul_ne_top ( ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) ( by norm_num ) ) ( by norm_num );
      · unfold endpointIncrement residualRewardIncrement; simp +decide [ residualReward ] ;
        rcases x with ( _ | _ | _ | _ | x ) <;> simp +arith +decide [ endpointRewardNat ] at hx ⊢;
        · norm_num;
        · rw [ Nat.cast_sub ] <;> norm_num;
          apply pow_le_pow_right₀ (by norm_num)
          have hchoose : Nat.choose (x + 3) 2 ≤ Nat.choose (x + 4) 2 := by
            exact Nat.choose_le_succ (x + 3) 2
          omega
    · intro i hi; exact div_nonneg ( mul_nonneg ( sub_nonneg.mpr <| Nat.cast_le.mpr <| by
        rcases i with ( _ | _ | _ | i ) <;> simp +arith +decide [ endpointRewardNat, Nat.choose ] at hi ⊢;
        split_ifs;
        · apply pow_le_pow_right₀ (by norm_num)
          omega
        · exact Nat.one_le_pow _ _ ( by decide ) ) <| pow_nonneg ( ENNReal.toReal_nonneg ) _ ) <| Nat.cast_nonneg _;
  have h_residQ : configurationCellTheta row col m a b ^ 2 / 2 + ENNReal.ofReal (endpointLambda R (configurationCellTheta row col m a b).toReal) ≤ ENNReal.ofReal (endpointQ R (configurationCellTheta row col m a b).toReal) := by
    rw [ endpointQ ];
    rw [ ENNReal.ofReal_add ];
    · gcongr;
      rw [ ENNReal.le_ofReal_iff_toReal_le ] <;> norm_num;
      · simp +decide [ configurationCellTheta ];
        simp +decide [ ENNReal.div_eq_top, ENNReal.mul_eq_top ];
        exact fun _ _ _ => hm.ne';
      · positivity;
    · positivity;
    · refine' Finset.sum_nonneg fun x hx => div_nonneg ( mul_nonneg _ _ ) _ <;> norm_num;
      exact sub_nonneg_of_le ( mod_cast Nat.le_of_lt_succ ( by
        unfold endpointRewardNat; rcases x with ( _ | _ | _ | x ) <;> simp +arith +decide [ Nat.choose ] at hx ⊢;
        split_ifs <;> [ exact pow_le_pow_right₀ ( by norm_num ) ( by linarith ) ; exact Nat.one_le_pow _ _ ( by norm_num ) ] ) );
  by_cases h : configurationCellTheta row col m a b = ⊤ <;> simp_all +decide;
  refine le_trans h_residQ ?_;
  calc
    _ ≤ ENNReal.ofReal (C * (configurationCellTheta row col m a b).toReal ^ 2) :=
      ENNReal.ofReal_le_ofReal
        (hC U m (U / 2) (configurationCellTheta row col m a b).toReal hm rfl
          ENNReal.toReal_nonneg (hbound a b hab) hpow).2
    _ = ENNReal.ofReal C * configurationCellTheta row col m a b ^ 2 := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_toReal h]

#print axioms existsAbsoluteResidualQQuadraticBound

end

end Erdos625
