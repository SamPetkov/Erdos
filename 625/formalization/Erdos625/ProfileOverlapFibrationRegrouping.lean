import Erdos625.ProfileOverlapCanonicalTable
import Mathlib.Tactic

/-!
# Weighted regrouping over bounded overlap-table fibers

For a fixed row labeling, `fixedFiberLabelingOverlapTableEquiv` identifies
every column labeling of the prescribed margin with its unique bounded
overlap table and a point of the corresponding literal overlap-event fiber.
This module turns that equivalence into the exact weighted finite-sum
identity needed to regroup a second-moment sum by overlap table.

The main theorem is deliberately valued in an arbitrary additive commutative
monoid.  Thus it is purely a finite fibration statement: no probability,
independence, or random-graph assumption is used.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- Regroup any weight of the realized bounded overlap table over the
fixed-margin column-labeling sample space.  The coefficient of each table is
the cardinality of its literal fixed-margin overlap-event fiber. -/
theorem sum_weight_boundedTableOfFixedFiberLabeling_eq_sum_card_nsmul
    {A B R : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [AddCommMonoid R]
    {n : ℕ} (row : Fin n → A) (columnMargin : B → ℕ)
    (weight : BoundedFixedMarginTable n row columnMargin → R) :
    (∑ column : FixedFiberLabeling (V := Fin n) columnMargin,
      weight (boundedTableOfFixedFiberLabeling row columnMargin column)) =
      ∑ table : BoundedFixedMarginTable n row columnMargin,
        Fintype.card (table.event row columnMargin) • weight table := by
  calc
    (∑ column : FixedFiberLabeling (V := Fin n) columnMargin,
        weight (boundedTableOfFixedFiberLabeling row columnMargin column)) =
        ∑ point : Σ table : BoundedFixedMarginTable n row columnMargin,
          table.event row columnMargin, weight point.1 := by
      apply Fintype.sum_equiv
        (fixedFiberLabelingOverlapTableEquiv row columnMargin)
      intro column
      rfl
    _ = ∑ table : BoundedFixedMarginTable n row columnMargin,
        ∑ _point : table.event row columnMargin, weight table := by
      exact Fintype.sum_sigma _
    _ = ∑ table : BoundedFixedMarginTable n row columnMargin,
        Fintype.card (table.event row columnMargin) • weight table := by
      apply Finset.sum_congr rfl
      intro table _
      simp [Finset.sum_const]

/-- Rational form of weighted table regrouping.  This is the form used when
the fiber cardinality is divided by the size of the fixed-margin sample space
to form the overlap-table probability law. -/
theorem sum_weight_boundedTableOfFixedFiberLabeling_eq_sum_card_mul
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} (row : Fin n → A) (columnMargin : B → ℕ)
    (weight : BoundedFixedMarginTable n row columnMargin → ℚ) :
    (∑ column : FixedFiberLabeling (V := Fin n) columnMargin,
      weight (boundedTableOfFixedFiberLabeling row columnMargin column)) =
      ∑ table : BoundedFixedMarginTable n row columnMargin,
        (Fintype.card (table.event row columnMargin) : ℚ) * weight table := by
  simpa only [nsmul_eq_mul] using
    (sum_weight_boundedTableOfFixedFiberLabeling_eq_sum_card_nsmul
      row columnMargin weight)

/-- Canonical-profile form of the weighted fibration.  A fixed ordered row
partition supplies the row labeling; the equivalence
`profileOverlapTableEquivBounded` then reindexes the literal bounded fibers
by the row-independent canonical profile tables. -/
theorem sum_weight_profileOverlapTableOfOrderedPair_eq_sum_card_nsmul
    {b n : ℕ} {R : Type*} {k : ColoringProfile b} [AddCommMonoid R]
    (row : OrderedProfilePartition n k) (weight : ProfileOverlapTable n k → R) :
    (∑ column : OrderedProfilePartition n k,
      weight (profileOverlapTableOfOrderedPair row column)) =
      ∑ table : ProfileOverlapTable n k,
        Fintype.card ((profileOverlapTableEquivBounded row table).event row.1
          (profileBlockMargin k)) • weight table := by
  calc
    (∑ column : OrderedProfilePartition n k,
        weight (profileOverlapTableOfOrderedPair row column)) =
        ∑ table : BoundedFixedMarginTable n row.1 (profileBlockMargin k),
          Fintype.card (table.event row.1 (profileBlockMargin k)) •
            weight (boundedToProfileOverlapTable row table) := by
      simpa only [profileOverlapTableOfOrderedPair] using
        (sum_weight_boundedTableOfFixedFiberLabeling_eq_sum_card_nsmul
          row.1 (profileBlockMargin k)
          (fun table => weight (boundedToProfileOverlapTable row table)))
    _ = ∑ table : ProfileOverlapTable n k,
        Fintype.card ((profileOverlapTableEquivBounded row table).event row.1
          (profileBlockMargin k)) • weight table := by
      calc
        (∑ table : BoundedFixedMarginTable n row.1 (profileBlockMargin k),
          Fintype.card (table.event row.1 (profileBlockMargin k)) •
            weight (boundedToProfileOverlapTable row table)) =
            ∑ table : ProfileOverlapTable n k,
              Fintype.card ((profileOverlapTableEquivBounded row table).event row.1
                (profileBlockMargin k)) •
                  weight (boundedToProfileOverlapTable row
                    (profileOverlapTableEquivBounded row table)) :=
          (Equiv.sum_comp (profileOverlapTableEquivBounded row)
            (fun table : BoundedFixedMarginTable n row.1 (profileBlockMargin k) =>
              Fintype.card (table.event row.1 (profileBlockMargin k)) •
                weight (boundedToProfileOverlapTable row table))).symm
        _ = ∑ table : ProfileOverlapTable n k,
          Fintype.card ((profileOverlapTableEquivBounded row table).event row.1
            (profileBlockMargin k)) • weight table := by
          apply Finset.sum_congr rfl
          intro table _
          have htransport :
              boundedToProfileOverlapTable row
                (profileOverlapTableEquivBounded row table) = table := by
            apply ProfileOverlapTable.ext
            rfl
          rw [htransport]

#print axioms sum_weight_boundedTableOfFixedFiberLabeling_eq_sum_card_nsmul
#print axioms sum_weight_boundedTableOfFixedFiberLabeling_eq_sum_card_mul
#print axioms sum_weight_profileOverlapTableOfOrderedPair_eq_sum_card_nsmul

end

end Erdos625
