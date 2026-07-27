import Erdos625.Section8MatchingDemandCellFibre
import Mathlib.Tactic

/-!
# Section VIII: pointwise attained partial-cell aggregate weight

The preceding matching-demand equivalence removes the completion ambiguity:
for a matching-supported demand table, the global physical skeleton fibre is
exactly a product of independent one-cell partial matching fibres.

This module computes the cardinality of that product and applies it to the exact
profile high-skeleton weight.  The final theorem is pointwise in one attained
canonical demand and introduces no endpoint completion, probability estimate,
or asymptotic bound.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Product of the unique local cell-factorial denominators. -/
def matchingDemandCellFactorialProduct
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → Nat) : Nat :=
  ∏ e : ↥(positiveDemandSupport demand),
    (demand e.1.1 e.1.2).factorial

/-- Product of the two local descending-factorial stub selections in every
positive demand cell. -/
def matchingDemandCellSelectionProduct
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → Nat) (row : A → Nat) (col : B → Nat) : Nat :=
  ∏ e : ↥(positiveDemandSupport demand),
    (row e.1.1).descFactorial (demand e.1.1 e.1.2) *
      (col e.1.2).descFactorial (demand e.1.1 e.1.2)

/-- Exact cross-multiplied cardinality of the product of positive-cell partial
matching fibres. -/
theorem card_matchingDemandCellDecoration_mul_factorials
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → Nat) (row : A → Nat) (col : B → Nat) :
    Fintype.card (MatchingDemandCellDecoration demand row col) *
        matchingDemandCellFactorialProduct demand =
      matchingDemandCellSelectionProduct demand row col := by
  classical
  rw [Fintype.card_pi]
  unfold matchingDemandCellFactorialProduct
    matchingDemandCellSelectionProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _he
  exact card_singleCellStubMatching_mul_factorial
    (row e.1.1) (col e.1.2) (demand e.1.1 e.1.2)

/-- The product of local factorials is positive. -/
theorem matchingDemandCellFactorialProduct_ne_zero
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → Nat) :
    matchingDemandCellFactorialProduct demand ≠ 0 := by
  unfold matchingDemandCellFactorialProduct
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _

/-- Division form of the exact local-cell product cardinality in `ENNReal`. -/
theorem ennreal_card_matchingDemandCellDecoration_eq_quotient
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → Nat) (row : A → Nat) (col : B → Nat) :
    (Fintype.card (MatchingDemandCellDecoration demand row col) : ENNReal) =
      (matchingDemandCellSelectionProduct demand row col : ENNReal) /
        (matchingDemandCellFactorialProduct demand : ENNReal) := by
  apply (ENNReal.eq_div_iff
    (Nat.cast_ne_zero.mpr
      (matchingDemandCellFactorialProduct_ne_zero demand))
    (ENNReal.natCast_ne_top _)).2
  simpa only [Nat.cast_mul, mul_comm] using
    congrArg (fun x : Nat => (x : ENNReal))
      (card_matchingDemandCellDecoration_mul_factorials demand row col)

/-- The exact aggregate obtained by summing any weight constant on the local
cell-decoration fibre. -/
def matchingDemandCellAggregateWeight
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → Nat) (row : A → Nat) (col : B → Nat)
    (atomWeight : ENNReal) : ENNReal :=
  ((matchingDemandCellSelectionProduct demand row col : Nat) : ENNReal) /
      ((matchingDemandCellFactorialProduct demand : Nat) : ENNReal) *
    atomWeight

/-- Summing a common atom over all independent positive-cell partial matchings
is exactly the aggregate quotient weight. -/
theorem sum_matchingDemandCellDecoration_const_eq_aggregateWeight
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → Nat) (row : A → Nat) (col : B → Nat)
    (atomWeight : ENNReal) :
    (∑ _ : MatchingDemandCellDecoration demand row col, atomWeight) =
      matchingDemandCellAggregateWeight demand row col atomWeight := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [ennreal_card_matchingDemandCellDecoration_eq_quotient]
  rfl

/-- Pointwise completion-free identity for one attained profile high skeleton.
The exact physical fibre is replaced by the equivalent product of local
positive-cell partial matching fibres, and its common atom is the existing
`profileHighSkeletonWitnessWeight`. -/
theorem profileHighSkeletonWeight_eq_matchingDemandCellAggregateWeight
    {b : Nat} (k : ColoringProfile b) (U : Nat)
    (demand : ProfileCanonicalHighSkeleton k U)
    (hmatching : IsBipartiteMatching (positiveDemandSupport demand.1)) :
    profileHighSkeletonWeight k U demand =
      matchingDemandCellAggregateWeight demand.1
        (profileBlockMargin k) (profileBlockMargin k)
        (profileHighSkeletonWitnessWeight k U demand) := by
  calc
    profileHighSkeletonWeight k U demand =
        ∑ _ : {S : UnlabelledTypedSkeleton (profileBlockMargin k)
          (profileBlockMargin k) // S.typeTable = demand.1},
            profileHighSkeletonWitnessWeight k U demand :=
      profileHighSkeletonWeight_eq_sum_unlabelledSkeletonFibre k U demand
    _ = ∑ _ : MatchingDemandCellDecoration demand.1
          (profileBlockMargin k) (profileBlockMargin k),
            profileHighSkeletonWitnessWeight k U demand := by
      simpa using
        (matchingDemandCellDecorationEquivPhysicalFibre demand.1
          (profileBlockMargin k) (profileBlockMargin k) hmatching).symm.sum_comp
            (fun _ => profileHighSkeletonWitnessWeight k U demand)
    _ = matchingDemandCellAggregateWeight demand.1
          (profileBlockMargin k) (profileBlockMargin k)
          (profileHighSkeletonWitnessWeight k U demand) :=
      sum_matchingDemandCellDecoration_const_eq_aggregateWeight
        demand.1 (profileBlockMargin k) (profileBlockMargin k)
          (profileHighSkeletonWitnessWeight k U demand)

/-- Structural specialization: every attained canonical profile high demand
with the usual degree cap satisfies the pointwise aggregate identity. -/
theorem profileHighSkeletonWeight_eq_matchingDemandCellAggregateWeight_of_cap
    {b : Nat} (k : ColoringProfile b) (U : Nat)
    (hcap : ∀ a : ProfileBlockIndex k, profileBlockMargin k a ≤ U)
    (demand : ProfileCanonicalHighSkeleton k U) :
    profileHighSkeletonWeight k U demand =
      matchingDemandCellAggregateWeight demand.1
        (profileBlockMargin k) (profileBlockMargin k)
        (profileHighSkeletonWitnessWeight k U demand) := by
  apply profileHighSkeletonWeight_eq_matchingDemandCellAggregateWeight
  exact profileHighSkeleton_positiveSupport_isBipartiteMatching k U hcap demand

#print axioms card_matchingDemandCellDecoration_mul_factorials
#print axioms ennreal_card_matchingDemandCellDecoration_eq_quotient
#print axioms sum_matchingDemandCellDecoration_const_eq_aggregateWeight
#print axioms profileHighSkeletonWeight_eq_matchingDemandCellAggregateWeight
#print axioms profileHighSkeletonWeight_eq_matchingDemandCellAggregateWeight_of_cap

end

end Erdos625
