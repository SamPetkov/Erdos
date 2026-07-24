import Erdos625.OrderedSignedProfileBridge
import Erdos625.ProfileOverlapTables
import Mathlib.Tactic

/-!
# Canonical fixed-margin profile overlap tables

The overlap-table law is independent of the particular row partition once
both ordered partitions have profile `k`: every row and every column margin
is the prescribed block-slot size. This file packages that row-independent
indexing type and transports it exactly to the literal bounded table type
used by `ProfileOverlapTables` after a row labeling is fixed.

No probability assertion is made here. The purpose is to separate the
canonical finite table index from the row-dependent event fibers.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- A canonical overlap table for two ordered profile partitions of profile
`k`. Its two margins are both the profile-block margin, so the type does not
depend on a chosen row partition. -/
structure ProfileOverlapTable {b : ℕ} (n : ℕ) (k : ColoringProfile b) where
  entries : ProfileBlockIndex k → ProfileBlockIndex k → Fin (n + 1)
  rowMargin : ∀ a, ∑ b, (entries a b).1 = profileBlockMargin k a
  columnMargin : ∀ b, ∑ a, (entries a b).1 = profileBlockMargin k b

namespace ProfileOverlapTable

/-- The natural-valued matrix carried by a canonical bounded table. -/
def tableNat {b n : ℕ} {k : ColoringProfile b}
    (table : ProfileOverlapTable n k) :
    ProfileBlockIndex k → ProfileBlockIndex k → ℕ :=
  fun a b => (table.entries a b).1

@[simp] theorem tableNat_apply {b n : ℕ} {k : ColoringProfile b}
    (table : ProfileOverlapTable n k) (a b : ProfileBlockIndex k) :
    table.tableNat a b = (table.entries a b).1 :=
  rfl

@[ext] theorem ext {b n : ℕ} {k : ColoringProfile b}
    {table table' : ProfileOverlapTable n k}
    (h : table.entries = table'.entries) : table = table' := by
  cases table
  cases table'
  cases h
  rfl

/-- Row margins of the natural matrix are the canonical block margins. -/
theorem tableNat_rowMargin {b n : ℕ} {k : ColoringProfile b}
    (table : ProfileOverlapTable n k) (a : ProfileBlockIndex k) :
    ∑ b, table.tableNat a b = profileBlockMargin k a :=
  table.rowMargin a

/-- Column margins of the natural matrix are the canonical block margins. -/
theorem tableNat_columnMargin {b n : ℕ} {k : ColoringProfile b}
    (table : ProfileOverlapTable n k) (b : ProfileBlockIndex k) :
    ∑ a, table.tableNat a b = profileBlockMargin k b :=
  table.columnMargin b

end ProfileOverlapTable

noncomputable instance instFintypeProfileOverlapTable {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) : Fintype (ProfileOverlapTable n k) :=
  Fintype.ofInjective
    (fun table : ProfileOverlapTable n k => table.entries)
    (by
      intro table table' h
      exact ProfileOverlapTable.ext h)

/-- The canonical block-slot type has one point for every part represented
by the profile. -/
theorem card_profileBlockIndex {b : ℕ} (k : ColoringProfile b) :
    Fintype.card (ProfileBlockIndex k) = ColoringProfile.partCount k := by
  change Fintype.card (ShapeBlockIndex (ColoringProfile.sizes k)) =
    (ColoringProfile.sizes k).card
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [show
      (Finset.univ : Finset (ColoringProfile.sizes k).toFinset) =
        (ColoringProfile.sizes k).toFinset.attach by
    ext s
    simp]
  simpa only using
    (Finset.sum_attach (ColoringProfile.sizes k).toFinset
      (fun s => (ColoringProfile.sizes k).count s)).trans
      (Multiset.toFinset_sum_count_eq _)

/-- Transport a canonical table to the row-dependent bounded table type for
a fixed ordered row partition. -/
def profileOverlapTableToBounded {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    ProfileOverlapTable n k → BoundedFixedMarginTable n row₀.1
      (profileBlockMargin k)
  | table =>
      { entries := table.entries
        rowMargin := by
          intro a
          calc
            ∑ b, (table.entries a b).1 = profileBlockMargin k a :=
              table.rowMargin a
            _ = labelingFiberCount row₀.1 a := (row₀.2 a).symm
        columnMargin := table.columnMargin }

/-- Transport a row-dependent bounded table back to the canonical table
type. -/
def boundedToProfileOverlapTable {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    BoundedFixedMarginTable n row₀.1 (profileBlockMargin k) →
      ProfileOverlapTable n k
  | table =>
      { entries := table.entries
        rowMargin := by
          intro a
          calc
            ∑ b, (table.entries a b).1 = labelingFiberCount row₀.1 a :=
              table.rowMargin a
            _ = profileBlockMargin k a := row₀.2 a
        columnMargin := table.columnMargin }

/-- Exact equivalence between the row-independent canonical table index and
the bounded fixed-margin table index based at any chosen ordered row
partition. -/
def profileOverlapTableEquivBounded {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    ProfileOverlapTable n k ≃
      BoundedFixedMarginTable n row₀.1 (profileBlockMargin k) where
  toFun := profileOverlapTableToBounded row₀
  invFun := boundedToProfileOverlapTable row₀
  left_inv := by
    intro table
    apply ProfileOverlapTable.ext
    rfl
  right_inv := by
    intro table
    apply BoundedFixedMarginTable.ext
    rfl

/-- Transport preserves every natural table entry. -/
@[simp] theorem profileOverlapTableToBounded_tableNat {b n : ℕ}
    {k : ColoringProfile b} (row₀ : OrderedProfilePartition n k)
    (table : ProfileOverlapTable n k) (a b : ProfileBlockIndex k) :
    (profileOverlapTableToBounded row₀ table).tableNat a b =
      table.tableNat a b :=
  rfl

/-- The inverse transport preserves every natural table entry. -/
@[simp] theorem boundedToProfileOverlapTable_tableNat {b n : ℕ}
    {k : ColoringProfile b} (row₀ : OrderedProfilePartition n k)
    (table : BoundedFixedMarginTable n row₀.1 (profileBlockMargin k))
    (a b : ProfileBlockIndex k) :
    (boundedToProfileOverlapTable row₀ table).tableNat a b =
      table.tableNat a b :=
  rfl

/-- The two finite table index types have exactly the same cardinality. -/
theorem card_profileOverlapTable_eq_card_bounded {b n : ℕ}
    {k : ColoringProfile b} (row₀ : OrderedProfilePartition n k) :
    Fintype.card (ProfileOverlapTable n k) =
      Fintype.card (BoundedFixedMarginTable n row₀.1 (profileBlockMargin k)) :=
  Fintype.card_congr (profileOverlapTableEquivBounded row₀)

/-- The canonical overlap table realized by two ordered profile partitions. -/
def profileOverlapTableOfOrderedPair {b n : ℕ} {k : ColoringProfile b}
    (row column : OrderedProfilePartition n k) : ProfileOverlapTable n k :=
  boundedToProfileOverlapTable row
    (boundedTableOfFixedFiberLabeling row.1 (profileBlockMargin k) column)

/-- The realized canonical table records the literal overlap-cell counts. -/
@[simp] theorem profileOverlapTableOfOrderedPair_tableNat {b n : ℕ}
    {k : ColoringProfile b} (row column : OrderedProfilePartition n k)
    (a b : ProfileBlockIndex k) :
    (profileOverlapTableOfOrderedPair row column).tableNat a b =
      orderedOverlapCount row.1 column.1 a b :=
  rfl

/-- Any existing ordered profile partition realizes at least one canonical
overlap table (take the same partition on both sides). -/
def profileOverlapTableOfOrderedDiagonal {b n : ℕ} {k : ColoringProfile b}
    (row : OrderedProfilePartition n k) : ProfileOverlapTable n k :=
  profileOverlapTableOfOrderedPair row row

/-- Feasibility of the ordered profile partition type implies nonemptiness of
the canonical overlap-table type. -/
theorem profileOverlapTable_nonempty_of_orderedProfilePartition
    {b n : ℕ} {k : ColoringProfile b}
    (row : OrderedProfilePartition n k) : Nonempty (ProfileOverlapTable n k) :=
  ⟨profileOverlapTableOfOrderedDiagonal row⟩

/-- A canonical table is realizable against a fixed row exactly when its
transported bounded-table event is nonempty. -/
theorem profileOverlapTable_realizable_iff {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (table : ProfileOverlapTable n k) :
    Nonempty
        (FixedMarginOverlapEvent row₀.1 table.tableNat (profileBlockMargin k)) ↔
      Nonempty
        ((profileOverlapTableEquivBounded row₀ table).event row₀.1
          (profileBlockMargin k)) := by
  constructor <;> intro h
  · rcases h with ⟨column, hcolumn⟩
    exact ⟨column, hcolumn⟩
  · rcases h with ⟨column, hcolumn⟩
    exact ⟨column, hcolumn⟩

#print axioms card_profileBlockIndex
#print axioms profileOverlapTableEquivBounded
#print axioms profileOverlapTableOfOrderedPair_tableNat
#print axioms profileOverlapTable_realizable_iff

end

end Erdos625
