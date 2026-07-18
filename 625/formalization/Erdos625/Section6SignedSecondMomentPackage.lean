import Erdos625.ProfileOverlapTables
import Erdos625.Section6PairSignCompatibility
import Mathlib.Tactic

/-!
# Section 6 signed second-moment table package

This module packages the already proved finite overlap-table fibration,
probability law, compatible-sign count, and signed local reward into the exact
finite table sum occurring on the right hand side of (6.6). It deliberately
does not identify this table sum with the graph-level second moment; that
remaining bridge requires the exact joint mass of two fixed signed witnesses.

The previously suggested `OrderedSignedProfileBridge` import is intentionally
absent: none of the declarations below uses that unfinished quotient bridge.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- The probability mass of one bounded fixed-margin overlap table. -/
def boundedOverlapTableProbability
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} (row : Fin n → A) (columnMargin : B → ℕ)
    (table : BoundedFixedMarginTable n row columnMargin) : ℚ :=
  (Fintype.card (table.event row columnMargin) : ℚ) /
    Fintype.card (FixedFiberLabeling (V := Fin n) columnMargin)

/-- The Lemma 6.1 local factor attached to a bounded overlap table. -/
def boundedOverlapTableLocalFactor
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} {row : Fin n → A} {columnMargin : B → ℕ}
    (table : BoundedFixedMarginTable n row columnMargin) : ℚ :=
  signedOverlapReward table.tableNat

/-- The concrete finite right hand side of the normalized second-moment
identity (6.6), indexed by the bounded fixed-margin table fibration. -/
def signedSecondMomentTableSum
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} (row : Fin n → A) (columnMargin : B → ℕ) : ℚ :=
  ∑ table : BoundedFixedMarginTable n row columnMargin,
    boundedOverlapTableProbability row columnMargin table *
      boundedOverlapTableLocalFactor table

/-- Formula (6.2) for the probability term in the packaged finite sum. -/
theorem boundedOverlapTableProbability_eq_factorialLaw
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} (row : Fin n → A) (columnMargin : B → ℕ)
    (table : BoundedFixedMarginTable n row columnMargin) :
    boundedOverlapTableProbability row columnMargin table =
      ((∏ a, (labelingFiberCount row a).factorial) *
          ∏ b, (columnMargin b).factorial : ℕ) /
        (((n.factorial *
          ∏ a, ∏ b, (table.tableNat a b).factorial : ℕ) : ℚ)) := by
  exact boundedFixedMarginTable_probability_eq row columnMargin table

/-- Formula (6.4): the table local factor is the product of the cell rewards
`g` and the binary cycle-space factor. -/
theorem boundedOverlapTableLocalFactor_eq_product_cycleRank
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} {row : Fin n → A} {columnMargin : B → ℕ}
    (table : BoundedFixedMarginTable n row columnMargin) :
    boundedOverlapTableLocalFactor table =
      ((∏ a, ∏ b, localSignRewardNat (table.tableNat a b)) *
        2 ^ cycleRank (signedOverlapSupportGraph table.tableNat) : ℕ) := by
  rfl

/-- The finite overlap-table probabilities sum to one whenever the prescribed
column-labeling sample space is nonempty. -/
theorem sum_boundedOverlapTableProbability_eq_one
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} (row : Fin n → A) (columnMargin : B → ℕ)
    (hne : Fintype.card (FixedFiberLabeling (V := Fin n) columnMargin) ≠ 0) :
    (∑ table : BoundedFixedMarginTable n row columnMargin,
      boundedOverlapTableProbability row columnMargin table) = 1 := by
  unfold boundedOverlapTableProbability
  rw [← Finset.sum_div]
  rw [← Nat.cast_sum]
  rw [← card_fixedFiberLabeling_eq_sum_card_fixedMarginOverlapEvent]
  exact div_self (Nat.cast_ne_zero.mpr hne)

/-- Fully expanded finite form of the packaged right hand side of (6.6). -/
theorem signedSecondMomentTableSum_eq_factorial_reward_sum
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} (row : Fin n → A) (columnMargin : B → ℕ) :
    signedSecondMomentTableSum row columnMargin =
      ∑ table : BoundedFixedMarginTable n row columnMargin,
        (((∏ a, (labelingFiberCount row a).factorial) *
              ∏ b, (columnMargin b).factorial : ℕ) /
            (((n.factorial *
              ∏ a, ∏ b, (table.tableNat a b).factorial : ℕ) : ℚ))) *
          (signedOverlapReward table.tableNat : ℚ) := by
  unfold signedSecondMomentTableSum boundedOverlapTableLocalFactor
  apply Finset.sum_congr rfl
  intro table _
  rw [boundedOverlapTableProbability_eq_factorialLaw]

#print axioms boundedOverlapTableProbability_eq_factorialLaw
#print axioms boundedOverlapTableLocalFactor_eq_product_cycleRank
#print axioms sum_boundedOverlapTableProbability_eq_one
#print axioms signedSecondMomentTableSum_eq_factorial_reward_sum

end

end Erdos625
