import Erdos625.ConfigurationModelProbability

/-!
# Capped fixed-F prescribed-demand expansion

This is the finite configuration-model obligation extracted from manuscript
(9.10)--(9.12).  It retains the cap/no-return event, the actual local reward
`g`, its threshold increments, and the literal uniform matching law.  The fixed
edge set `F` need not be even: evenness enters only when this estimate is later
summed over the residual cycle-space family.

This module proves only the fixed-`F` expansion.  It does not perform that
even-family summation, prove the polymer/cycle bounds, or assemble Lemma 9.1.
-/

namespace Erdos625

open scoped BigOperators ENNReal

/-- The local topological reward from manuscript (6.5):
`g(0)=g(1)=g(2)=1` and `g(x)=2^(choose(x,2)-1)` for `x >= 3`. -/
def residualReward (x : ℕ) : ℕ :=
  if x ≤ 2 then 1 else 2 ^ (Nat.choose x 2 - 1)

/-- The nonnegative threshold increment `Delta_x = g(x)-g(x-1)`. -/
def residualRewardIncrement (x : ℕ) : ℕ :=
  residualReward x - residualReward (x - 1)

/-- The residual event retained before the nonnegative threshold expansion:
every cell is capped by `R`, and a cell exposed in the high skeleton `M`
receives no residual pair. -/
def ResidualCapNoReturnEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ) :
    Set (ConfigurationMatching row col) :=
  {matching |
    (∀ a b, configurationCellCount matching a b ≤ R) ∧
      ∀ e ∈ M, configurationCellCount matching e.1 e.2 = 0}

/-- The manuscript quantity
`lambda_ab = sum_{x=3}^R Delta_x theta_ab^x / x!`, set to zero on the
already-exposed high skeleton. -/
noncomputable def residualLambda
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (a : A) (b : B) : ℝ≥0∞ :=
  if (a, b) ∈ M then 0 else
    ∑ x ∈ Finset.Icc 3 R,
      (residualRewardIncrement x : ℝ≥0∞) *
          configurationCellTheta row col (Finset.univ.sum row) a b ^ x /
        (x.factorial : ℝ≥0∞)

/-- The fixed-selected-edge weight
`q_ab = theta_ab^2/2 + lambda_ab`, again zero on the high skeleton. -/
noncomputable def residualQ
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (a : A) (b : B) : ℝ≥0∞ :=
  if (a, b) ∈ M then 0 else
    configurationCellTheta row col (Finset.univ.sum row) a b ^ 2 / 2 +
      residualLambda M R row col a b

/-- The capped local factor for one fixed cycle-space edge set `F`.
Edges of `F ∩ M` are already exposed and carry weight one.  Every edge of
`F \ M` imposes the base residual threshold two. -/
noncomputable def residualFixedFWeight
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M F : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (matching : ConfigurationMatching row col) : ℝ≥0∞ := by
  classical
  exact
    if matching ∈ ResidualCapNoReturnEvent M R row col then
      (∏ a : A, ∏ b : B,
        (residualReward (configurationCellCount matching a b) : ℝ≥0∞)) *
      (∏ e ∈ F,
        if e ∈ M then 1 else
          if 2 ≤ configurationCellCount matching e.1 e.2 then 1 else 0)
    else 0

/-- Uniform expectation of the capped fixed-`F` factor, written as the exact
finite PMF sum so that no measurability or integrability abstraction is added. -/
noncomputable def residualFixedFExpectation
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M F : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col) : ℝ≥0∞ :=
  ∑ matching : ConfigurationMatching row col,
    uniformConfigurationMatching row col htotal matching *
      residualFixedFWeight M F R row col matching

/-- The reward is the sum of its threshold increments. -/
private theorem residualReward_threshold_sum (n : ℕ) :
    (residualReward n : ℝ≥0∞) =
      1 + ∑ x ∈ Finset.Icc 3 n, (residualRewardIncrement x : ℝ≥0∞) := by
  induction' n with n ih;
  · norm_cast;
  · rcases n with ( _ | _ | _ | n ) <;> simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
    · norm_cast;
    · convert congr_arg ( · + ( residualRewardIncrement ( n + 3 + 1 ) : ℝ≥0∞ ) ) ih using 1;
      · unfold residualReward residualRewardIncrement;
        unfold residualReward; simp +arith +decide [ Nat.choose_succ_succ ] ;
        rw [ add_tsub_cancel_of_le ( pow_le_pow_right₀ ( by norm_num ) ( by linarith ) ) ];
      · ring

/-- A finite weighted threshold expansion, with the joint prescribed-cell
bound applied once to every demand occurring in the expansion. -/
private theorem weighted_prescribedDemand_product_bound
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (S : A → B → Finset ℕ) (w : A → B → ℕ → ℝ≥0∞)
    (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hm : 0 < Finset.univ.sum row) :
    (∑ matching : ConfigurationMatching row col,
      uniformConfigurationMatching row col htotal matching *
        (∏ a : A, ∏ b : B,
          ∑ x ∈ S a b,
            if x ≤ configurationCellCount matching a b then w a b x else 0)) ≤
      ∏ a : A, ∏ b : B,
        ∑ x ∈ S a b,
          w a b x *
            configurationCellTheta row col (Finset.univ.sum row) a b ^ x /
              (x.factorial : ℝ≥0∞) := by
  revert S w;
  -- Apply the jointPrescribedCellBound_cellwise theorem to each demand in the expansion.
  have h_jointPrescribedCellBound_cellwise : ∀ (demand : A → B → ℕ) (w : A → B → ℕ → ℝ≥0∞),
    (∑ matching : ConfigurationMatching row col,
      (uniformConfigurationMatching row col htotal) matching *
        (∏ a : A, ∏ b : B, if demand a b ≤ configurationCellCount matching a b then (w a b (demand a b)) else 0)) ≤
    (∏ a : A, ∏ b : B, (w a b (demand a b) * configurationCellTheta row col (Finset.univ.sum row) a b ^ demand a b / ((demand a b).factorial : ℝ≥0∞))) := by
      intro demand w
      have hjointPrescribedCellBound_cellwise : (∑ matching : ConfigurationMatching row col,
        (uniformConfigurationMatching row col htotal) matching *
          (∏ a : A, ∏ b : B, if demand a b ≤ configurationCellCount matching a b then 1 else 0)) ≤
        (∏ a : A, ∏ b : B, (configurationCellTheta row col (Finset.univ.sum row) a b ^ (demand a b) / ((demand a b).factorial : ℝ≥0∞))) := by
          convert jointPrescribedCellBound_cellwise demand row col htotal hm using 1;
          unfold prescribedCellEvent; simp +decide [ Finset.prod_ite ] ;
          congr! 1;
          by_cases h : ∀ a b, demand a b ≤ configurationCellCount ‹_› a b <;> simp_all +decide [ Finset.prod_eq_zero_iff ];
          simp +decide [ Finset.card_eq_zero.mpr, h ];
      convert mul_le_mul_left hjointPrescribedCellBound_cellwise ( ∏ a : A, ∏ b : B, w a b ( demand a b ) ) using 1;
      · simp +decide [ Finset.sum_mul _ _ _ ];
        simp +decide only [mul_assoc, ← Finset.prod_mul_distrib];
        exact Finset.sum_congr rfl fun _ _ => by congr; ext; congr; ext; split_ifs <;> ring;
      · simp +decide only [mul_div_assoc, mul_comm, ← Finset.prod_mul_distrib];
  intro S w;
  simp only [ Finset.prod_univ_sum ];
  simp only [ Finset.mul_sum _ _ _ ];
  rw [ Finset.sum_comm ];
  refine' Finset.sum_le_sum fun demand hdemand => _;
  exact h_jointPrescribedCellBound_cellwise demand w

/-- Faithful fixed-`F` form of the capped prescribed-demand expansion behind
(9.10)--(9.12).  The cap/no-return indicator is dropped only after expanding
the nonnegative threshold alternatives, and the same joint configuration-model
bound is applied to all demanded cells at once. -/
theorem capped_fixedF_prescribedDemand_expansion
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M F : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hm : 0 < Finset.univ.sum row) :
    residualFixedFExpectation M F R row col htotal ≤
      ∏ a : A, ∏ b : B,
        if (a, b) ∈ M then 1
        else if (a, b) ∈ F then residualQ M R row col a b
        else 1 + residualLambda M R row col a b := by
  refine' le_trans ( Finset.sum_le_sum _ ) _;
  use fun matching => uniformConfigurationMatching row col htotal matching * ( ∏ a : A, ∏ b : B, ∑ x ∈ if ( a, b ) ∈ M then { 0 } else if ( a, b ) ∈ F then { 2 } ∪ Finset.Icc 3 R else { 0 } ∪ Finset.Icc 3 R, if x ≤ configurationCellCount matching a b then ( if ( a, b ) ∈ M then 1 else if ( a, b ) ∈ F then if x = 2 then 1 else residualRewardIncrement x else if x = 0 then 1 else residualRewardIncrement x ) else 0 );
  · intro matching;
    by_cases h : matching ∈ ResidualCapNoReturnEvent M R row col <;> simp +decide;
    · unfold residualFixedFWeight;
      rw [ if_pos h ];
      let badCells := Finset.filter
        ( fun x => configurationCellCount matching x.1 x.2 < 2 )
        ( Finset.filter ( fun x => x ∉ M ) F );
      by_cases hbad : badCells.Nonempty;
      · rcases hbad with ⟨ e, he ⟩;
        have he' := he;
        simp only [ badCells, Finset.mem_filter ] at he';
        rcases he' with ⟨ ⟨ heF, heM ⟩, heLow ⟩;
        have hzero :
            (∏ e ∈ F,
              if e ∈ M then (1 : ℝ≥0∞)
              else if 2 ≤ configurationCellCount matching e.1 e.2 then 1 else 0) = 0 :=
          Finset.prod_eq_zero heF ( by simp [ heM, Nat.not_le.mpr heLow ] );
        simp [ hzero ];
      · have hNoBad (a : A) (b : B)
            (habF : (a, b) ∈ F) (habM : (a, b) ∉ M) :
            2 ≤ configurationCellCount matching a b := by
          by_contra hlt;
          apply hbad;
          refine' ⟨ (a, b), _ ⟩;
          simp only [ badCells, Finset.mem_filter ];
          exact ⟨ ⟨ habF, habM ⟩, Nat.lt_of_not_ge hlt ⟩;
        apply mul_le_mul_right;
        have hF :
            (∏ e ∈ F,
              if e ∈ M then (1 : ℝ≥0∞)
              else if 2 ≤ configurationCellCount matching e.1 e.2 then 1 else 0) =
            ∏ a : A, ∏ b : B,
              if (a, b) ∈ F then
                (if (a, b) ∈ M then 1
                  else if 2 ≤ configurationCellCount matching a b then 1 else 0)
              else 1 := by
          rw [ ← Fintype.prod_ite_mem ];
          exact Fintype.prod_prod_type'
            ( fun a : A => fun b : B =>
              if (a, b) ∈ F then
                (if (a, b) ∈ M then (1 : ℝ≥0∞)
                  else if 2 ≤ configurationCellCount matching a b then 1 else 0)
              else 1 );
        rw [ hF ];
        simp only [ ← Finset.prod_mul_distrib ];
        refine' Finset.prod_le_prod' fun a _ => Finset.prod_le_prod' fun b _ => _;
        by_cases habM : (a, b) ∈ M;
        · have hzero := h.2 (a, b) habM;
          simp [ habM, hzero, residualReward ];
        · have hcap : configurationCellCount matching a b ≤ R := h.1 a b;
          have hfilter :
              (Finset.Icc 3 R).filter
                  (fun x => x ≤ configurationCellCount matching a b) =
                Finset.Icc 3 (configurationCellCount matching a b) := by
            ext x;
            simp only [ Finset.mem_filter, Finset.mem_Icc ];
            constructor;
            · rintro ⟨ ⟨ hx3, hxR ⟩, hxCount ⟩;
              exact ⟨ hx3, hxCount ⟩;
            · rintro ⟨ hx3, hxCount ⟩;
              exact ⟨ ⟨ hx3, hxCount.trans hcap ⟩, hxCount ⟩;
          have hthreshold :
              (∑ x ∈ Finset.Icc 3 R,
                if x ≤ configurationCellCount matching a b then
                  (residualRewardIncrement x : ℝ≥0∞)
                else 0) =
                ∑ x ∈ Finset.Icc 3 (configurationCellCount matching a b),
                  (residualRewardIncrement x : ℝ≥0∞) := by
            calc
              (∑ x ∈ Finset.Icc 3 R,
                if x ≤ configurationCellCount matching a b then
                  (residualRewardIncrement x : ℝ≥0∞)
                else 0) =
                  ∑ x ∈ (Finset.Icc 3 R).filter
                      (fun x => x ≤ configurationCellCount matching a b),
                    (residualRewardIncrement x : ℝ≥0∞) := by
                      rw [ Finset.sum_filter ];
              _ = ∑ x ∈ Finset.Icc 3 (configurationCellCount matching a b),
                    (residualRewardIncrement x : ℝ≥0∞) := by
                      rw [ hfilter ];
          by_cases habF : (a, b) ∈ F;
          · have htwo := hNoBad a b habF habM;
            simp only [ if_neg habM, if_pos habF, if_pos htwo, mul_one ];
            rw [ residualReward_threshold_sum ];
            rw [ Finset.sum_insert (by simp [ Finset.mem_Icc ]) ];
            simp only [ if_pos htwo ];
            have hsumInner :
                (∑ x ∈ Finset.Icc 3 R,
                  if x ≤ configurationCellCount matching a b then
                    (if x = 2 then 1
                      else (residualRewardIncrement x : ℝ≥0∞))
                  else 0) =
                  ∑ x ∈ Finset.Icc 3 R,
                    if x ≤ configurationCellCount matching a b then
                      (residualRewardIncrement x : ℝ≥0∞)
                    else 0 := by
              apply Finset.sum_congr rfl;
              intro x hx;
              have hxne : x ≠ 2 := by
                have hx3 := (Finset.mem_Icc.mp hx).1;
                omega;
              simp only [ hxne, if_false ];
            rw [ hsumInner, hthreshold ];
            simp only [ if_true ];
            exact le_rfl;
          · simp only [ if_neg habM, if_neg habF, mul_one ];
            rw [ residualReward_threshold_sum ];
            rw [ Finset.sum_insert (by simp [ Finset.mem_Icc ]) ];
            simp only [ if_pos (Nat.zero_le _) ];
            have hsumInner :
                (∑ x ∈ Finset.Icc 3 R,
                  if x ≤ configurationCellCount matching a b then
                    (if x = 0 then 1
                      else (residualRewardIncrement x : ℝ≥0∞))
                  else 0) =
                  ∑ x ∈ Finset.Icc 3 R,
                    if x ≤ configurationCellCount matching a b then
                      (residualRewardIncrement x : ℝ≥0∞)
                    else 0 := by
              apply Finset.sum_congr rfl;
              intro x hx;
              have hxne : x ≠ 0 := by
                have hx3 := (Finset.mem_Icc.mp hx).1;
                omega;
              simp only [ hxne, if_false ];
            rw [ hsumInner, hthreshold ];
            simp only [ if_true ];
            exact le_rfl;
    · unfold residualFixedFWeight; simp +decide [ h ] ;
  · convert weighted_prescribedDemand_product_bound ( fun a b => if ( a, b ) ∈ M then { 0 } else if ( a, b ) ∈ F then { 2 } ∪ Finset.Icc 3 R else { 0 } ∪ Finset.Icc 3 R ) ( fun a b x => if ( a, b ) ∈ M then 1 else if ( a, b ) ∈ F then if x = 2 then 1 else residualRewardIncrement x else if x = 0 then 1 else residualRewardIncrement x ) row col htotal hm using 1;
    · rfl;
    · apply Fintype.sum_congr;
      intro matching;
      congr 1;
      norm_cast;
    · refine' Finset.prod_congr rfl fun a ha => Finset.prod_congr rfl fun b hb => _ ; split_ifs <;> simp +decide [ *, residualQ, residualLambda ] ;
      · exact congr_arg _ ( Finset.sum_congr rfl fun x hx => by aesop );
      · exact Finset.sum_congr rfl fun x hx => by rw [ if_neg ( by linarith [ Finset.mem_Icc.mp hx ] ) ] ;

#print axioms capped_fixedF_prescribedDemand_expansion

end Erdos625
