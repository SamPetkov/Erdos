import Erdos625.OrderedOverlapLaw
import Mathlib.Tactic

/-!
# Bounded fixed-margin overlap tables

This module gives the finite fibration needed when a row labeling is fixed
and the column labeling ranges uniformly over a prescribed fiber profile.  A
table is stored with entries in `Fin (n + 1)`, rather than as an unbounded
natural-valued function.  Thus the indexing family is visibly finite before
any probability calculation is performed.

The fibration is literal: every fixed-margin column labeling determines one
and only one bounded overlap table, and its fiber is precisely the existing
`FixedMarginOverlapEvent`.  No exchangeability or row-independence assertion
is used.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- A finite overlap table on a vertex set of size `n`, with every entry
stored in the a priori box `0, ..., n`. -/
structure BoundedFixedMarginTable
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (n : ℕ) (row : Fin n → A) (columnMargin : B → ℕ) where
  entries : A → B → Fin (n + 1)
  rowMargin : ∀ a, ∑ b, (entries a b).1 = labelingFiberCount row a
  columnMargin : ∀ b, ∑ a, (entries a b).1 = columnMargin b

namespace BoundedFixedMarginTable

/-- The natural-valued table represented by a bounded overlap table. -/
def tableNat
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} {row : Fin n → A} {columnMargin : B → ℕ}
    (table : BoundedFixedMarginTable n row columnMargin) : A → B → ℕ :=
  fun a b => (table.entries a b).1

@[simp] theorem tableNat_apply
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} {row : Fin n → A} {columnMargin : B → ℕ}
    (table : BoundedFixedMarginTable n row columnMargin) (a : A) (b : B) :
    table.tableNat a b = (table.entries a b).1 :=
  rfl

@[ext] theorem ext
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} {row : Fin n → A} {columnMargin : B → ℕ}
    {table table' : BoundedFixedMarginTable n row columnMargin}
    (h : table.entries = table'.entries) :
    table = table' := by
  cases table
  cases table'
  cases h
  rfl

end BoundedFixedMarginTable

noncomputable instance instFintypeBoundedFixedMarginTable
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (n : ℕ) (row : Fin n → A) (columnMargin : B → ℕ) :
    Fintype (BoundedFixedMarginTable n row columnMargin) :=
  Fintype.ofInjective
    (fun table : BoundedFixedMarginTable n row columnMargin => table.entries)
    (by
      intro table table' h
      exact BoundedFixedMarginTable.ext h)

/-- Every actual overlap-cell count is bounded by the number of vertices. -/
theorem orderedOverlapCount_le_vertexCount
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} (row : Fin n → A) (column : Fin n → B) (a : A) (b : B) :
    orderedOverlapCount row column a b ≤ n := by
  unfold orderedOverlapCount
  calc
    (Finset.univ.filter fun v : Fin n => row v = a ∧ column v = b).card ≤
        Finset.univ.card :=
      Finset.card_filter_le _ _
    _ = n := by simp

/-- The bounded table attained by a fixed-margin column labeling against a
fixed row labeling. -/
def boundedTableOfFixedFiberLabeling
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} (row : Fin n → A) (columnMargin : B → ℕ)
    (column : FixedFiberLabeling (V := Fin n) columnMargin) :
    BoundedFixedMarginTable n row columnMargin where
  entries := fun a b =>
    ⟨orderedOverlapCount row column.1 a b,
      Nat.lt_succ_iff.mpr (orderedOverlapCount_le_vertexCount row column.1 a b)⟩
  rowMargin := by
    intro a
    simpa only using sum_orderedOverlapCount_row row column.1 a
  columnMargin := by
    intro b
    calc
      ∑ a, orderedOverlapCount row column.1 a b =
          labelingFiberCount column.1 b :=
        sum_orderedOverlapCount_column row column.1 b
      _ = columnMargin b := column.2 b

/-- The overlap event attached to a bounded fixed-margin table. -/
abbrev BoundedFixedMarginTable.event
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} (row : Fin n → A) (columnMargin : B → ℕ)
    (table : BoundedFixedMarginTable n row columnMargin) :=
  FixedMarginOverlapEvent row table.tableNat columnMargin

/-- For a fixed bounded table, its literal overlap-event fiber is the fiber
of the deterministic map sending a column labeling to its overlap table. -/
def fixedFiberLabelingTableFiberEquiv
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} (row : Fin n → A) (columnMargin : B → ℕ)
    (table : BoundedFixedMarginTable n row columnMargin) :
    {column : FixedFiberLabeling (V := Fin n) columnMargin //
      boundedTableOfFixedFiberLabeling row columnMargin column = table} ≃
      table.event row columnMargin where
  toFun column :=
    ⟨column.1, fun a b => by
      have hentry := congrArg
        (fun t : BoundedFixedMarginTable n row columnMargin => t.tableNat a b)
        column.2
      simpa [boundedTableOfFixedFiberLabeling,
        BoundedFixedMarginTable.tableNat] using hentry⟩
  invFun event :=
    ⟨event.1, by
      apply BoundedFixedMarginTable.ext
      funext a b
      apply Fin.ext
      exact event.2 a b⟩
  left_inv := by
    intro column
    apply Subtype.ext
    rfl
  right_inv := by
    intro event
    apply Subtype.ext
    rfl

/-- A fixed-margin column labeling is exactly a bounded overlap table together
with a point in its literal overlap-event fiber. -/
def fixedFiberLabelingOverlapTableEquiv
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} (row : Fin n → A) (columnMargin : B → ℕ) :
    FixedFiberLabeling (V := Fin n) columnMargin ≃
      Σ table : BoundedFixedMarginTable n row columnMargin,
        table.event row columnMargin :=
  (Equiv.sigmaFiberEquiv
    (boundedTableOfFixedFiberLabeling row columnMargin)).symm.trans
    (Equiv.sigmaCongrRight
      (fun table => fixedFiberLabelingTableFiberEquiv row columnMargin table))

/-- The overlap-event fibers exhaust the fixed-margin sample space, with a
unique table for every column labeling. -/
theorem fixedMarginOverlapEvent_exhaustion
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} (row : Fin n → A) (columnMargin : B → ℕ)
    (column : FixedFiberLabeling (V := Fin n) columnMargin) :
    ∃! table : BoundedFixedMarginTable n row columnMargin,
      ∀ a b,
        orderedOverlapCount row column.1 a b = table.tableNat a b := by
  refine ⟨boundedTableOfFixedFiberLabeling row columnMargin column, ?_, ?_⟩
  · intro a b
    rfl
  · intro table htable
    apply BoundedFixedMarginTable.ext
    funext a b
    apply Fin.ext
    have h :
        ((boundedTableOfFixedFiberLabeling row columnMargin column).entries a b).1 =
          (table.entries a b).1 := by
      calc
        ((boundedTableOfFixedFiberLabeling row columnMargin column).entries a b).1 =
            orderedOverlapCount row column.1 a b := rfl
        _ = table.tableNat a b := htable a b
        _ = (table.entries a b).1 := rfl
    exact h.symm

/-- Distinct bounded tables have disjoint fixed-margin overlap fibers. -/
theorem fixedMarginOverlapEvent_disjoint
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} (row : Fin n → A) (columnMargin : B → ℕ)
    {table table' : BoundedFixedMarginTable n row columnMargin}
    (hne : table ≠ table') :
    ¬ ∃ column : FixedFiberLabeling (V := Fin n) columnMargin,
      (∀ a b, orderedOverlapCount row column.1 a b = table.tableNat a b) ∧
      (∀ a b, orderedOverlapCount row column.1 a b = table'.tableNat a b) := by
  rintro ⟨column, htable, htable'⟩
  apply hne
  apply BoundedFixedMarginTable.ext
  funext a b
  apply Fin.ext
  calc
    (table.entries a b).1 = table.tableNat a b := rfl
    _ = orderedOverlapCount row column.1 a b := (htable a b).symm
    _ = table'.tableNat a b := htable' a b
    _ = (table'.entries a b).1 := rfl

/-- Exact cardinality disintegration of the fixed-margin sample space over
the bounded overlap-table fibers. -/
theorem card_fixedFiberLabeling_eq_sum_card_fixedMarginOverlapEvent
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} (row : Fin n → A) (columnMargin : B → ℕ) :
    Fintype.card (FixedFiberLabeling (V := Fin n) columnMargin) =
      ∑ table : BoundedFixedMarginTable n row columnMargin,
        Fintype.card (table.event row columnMargin) := by
  calc
    Fintype.card (FixedFiberLabeling (V := Fin n) columnMargin) =
        Fintype.card
          (Σ table : BoundedFixedMarginTable n row columnMargin,
            table.event row columnMargin) :=
      Fintype.card_congr (fixedFiberLabelingOverlapTableEquiv row columnMargin)
    _ = ∑ table : BoundedFixedMarginTable n row columnMargin,
        Fintype.card (table.event row columnMargin) :=
      Fintype.card_sigma

/-- The exact fixed-margin overlap-table law for a bounded table.  This is
the profile-table law (6.2) transported to the finite fibration above. -/
theorem boundedFixedMarginTable_probability_eq
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} (row : Fin n → A) (columnMargin : B → ℕ)
    (table : BoundedFixedMarginTable n row columnMargin) :
    (Fintype.card (table.event row columnMargin) : ℚ) /
          Fintype.card (FixedFiberLabeling (V := Fin n) columnMargin) =
      ((∏ a, (labelingFiberCount row a).factorial) *
          ∏ b, (columnMargin b).factorial : ℕ) /
        (((n.factorial *
          ∏ a, ∏ b, (table.tableNat a b).factorial : ℕ) : ℚ)) := by
  simpa using
    (fixedMarginOverlapEvent_probability_eq row table.tableNat columnMargin
      table.rowMargin table.columnMargin)

#print axioms fixedFiberLabelingOverlapTableEquiv
#print axioms fixedMarginOverlapEvent_exhaustion
#print axioms card_fixedFiberLabeling_eq_sum_card_fixedMarginOverlapEvent
#print axioms boundedFixedMarginTable_probability_eq

end

end Erdos625
