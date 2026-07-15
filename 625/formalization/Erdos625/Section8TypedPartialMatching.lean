import Erdos625.ConfigurationModelPrescribedCells
import Mathlib.Tactic

/-!
# Section VIII: literal typed partial matchings for one finite demand matrix

This module gives a structural presentation of a finite partial
matching between the typed row-stub space `Sigma i, Fin (k i)` and the typed
column-stub space `Sigma j, Fin (ell j)`.  Its source and target embeddings
are injective, its cellwise pairing preserves the two types, and the number of
matched atoms in cell `(i,j)` is exactly `L i j`.

The candidate is entirely finite.  In particular it makes no assertion about a
random configuration matching, a canonical skeleton event, a probability, or
an asymptotic estimate.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- A literal cellwise presentation of a typed partial matching.  The row and
column allocations select disjoint stubs inside each type, while `pairing`
matches the selected row stubs in cell `(i,j)` bijectively to selected column
stubs in the same cell.  The global embeddings below turn these fields into a
partial matching between `Sigma i, Fin (k i)` and `Sigma j, Fin (ell j)`.

This deliberately carries no order on the edges of a cell: adding such an
order would multiply the finite count by `prod_{i,j} (L i j)!`. -/
structure TypedPartialMatching
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (L : I -> J -> Nat) (k : I -> Nat) (ell : J -> Nat) where
  rowAllocation : forall i, StubAllocation (k i) (L i)
  columnAllocation : forall j, StubAllocation (ell j) (fun i => L i j)
  pairing : forall i j,
    ((rowAllocation i).1 j : Finset (Fin (k i))) ≃
      ((columnAllocation j).1 i : Finset (Fin (ell j)))

/-- The selected row atoms of a typed partial matching. -/
abbrev TypedPartialMatchingSource
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {L : I -> J -> Nat} {k : I -> Nat} {ell : J -> Nat}
    (matching : TypedPartialMatching L k ell) :=
  Sigma fun i => Sigma fun j =>
    ((matching.rowAllocation i).1 j : Finset (Fin (k i)))

/-- The selected column atoms of a typed partial matching.  The outer index
is the column type and the inner index is the row type. -/
abbrev TypedPartialMatchingTarget
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {L : I -> J -> Nat} {k : I -> Nat} {ell : J -> Nat}
    (matching : TypedPartialMatching L k ell) :=
  Sigma fun j => Sigma fun i =>
    ((matching.columnAllocation j).1 i : Finset (Fin (ell j)))

/-- Inject the selected row atoms into the full typed row-stub space. -/
def typedPartialMatchingSourceEmbedding
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {L : I -> J -> Nat} {k : I -> Nat} {ell : J -> Nat}
    (matching : TypedPartialMatching L k ell) :
    TypedPartialMatchingSource matching ↪ RowStub k where
  toFun atom := ⟨atom.1, atom.2.2.1⟩
  inj' := by
    rintro ⟨i, j, stub⟩ ⟨i', j', stub'⟩ h
    have hi : i = i' := (Sigma.mk.inj_iff.mp h).1
    subst i'
    have hstub : (stub : Fin (k i)) = stub' :=
      eq_of_heq (Sigma.mk.inj_iff.mp h).2
    by_cases hj : j = j'
    · subst j'
      exact Sigma.ext rfl <| heq_of_eq <|
        Sigma.ext rfl <| heq_of_eq <| Subtype.ext hstub
    · have hdisjoint := (matching.rowAllocation i).2.2 j j' hj
      have hmem : (stub : Fin (k i)) ∈ (matching.rowAllocation i).1 j' := by
        rw [hstub]
        exact stub'.2
      exact False.elim <|
        (Finset.disjoint_left.mp hdisjoint) stub.2 hmem

/-- Inject the selected column atoms into the full typed column-stub space. -/
def typedPartialMatchingTargetEmbedding
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {L : I -> J -> Nat} {k : I -> Nat} {ell : J -> Nat}
    (matching : TypedPartialMatching L k ell) :
    TypedPartialMatchingTarget matching ↪ ColumnStub ell where
  toFun atom := ⟨atom.1, atom.2.2.1⟩
  inj' := by
    rintro ⟨j, i, stub⟩ ⟨j', i', stub'⟩ h
    have hj : j = j' := (Sigma.mk.inj_iff.mp h).1
    subst j'
    have hstub : (stub : Fin (ell j)) = stub' :=
      eq_of_heq (Sigma.mk.inj_iff.mp h).2
    by_cases hi : i = i'
    · subst i'
      exact Sigma.ext rfl <| heq_of_eq <|
        Sigma.ext rfl <| heq_of_eq <| Subtype.ext hstub
    · have hdisjoint := (matching.columnAllocation j).2.2 i i' hi
      have hmem : (stub : Fin (ell j)) ∈ (matching.columnAllocation j).1 i' := by
        rw [hstub]
        exact stub'.2
      exact False.elim <|
        (Finset.disjoint_left.mp hdisjoint) stub.2 hmem

/-- The cellwise bijections assemble to the literal matching between the
selected global row and column stubs. -/
def typedPartialMatchingPairing
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {L : I -> J -> Nat} {k : I -> Nat} {ell : J -> Nat}
    (matching : TypedPartialMatching L k ell) :
    TypedPartialMatchingSource matching ≃ TypedPartialMatchingTarget matching where
  toFun atom :=
    ⟨atom.2.1, atom.1,
      matching.pairing atom.1 atom.2.1 atom.2.2⟩
  invFun atom :=
    ⟨atom.2.1, atom.1,
      (matching.pairing atom.2.1 atom.1).symm atom.2.2⟩
  left_inv atom := by
    obtain ⟨i, j, stub⟩ := atom
    simp
  right_inv atom := by
    obtain ⟨j, i, stub⟩ := atom
    simp

/-- The literal matching preserves the row and column type of every cell. -/
theorem typedPartialMatchingPairing_cell
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {L : I -> J -> Nat} {k : I -> Nat} {ell : J -> Nat}
    (matching : TypedPartialMatching L k ell)
    (atom : TypedPartialMatchingSource matching) :
    (typedPartialMatchingPairing matching atom).1 = atom.2.1 ∧
      (typedPartialMatchingPairing matching atom).2.1 = atom.1 := by
  simp [typedPartialMatchingPairing]

/-- Each row-side cell of the literal matching has exactly its prescribed
demand. -/
theorem card_typedPartialMatching_rowCell
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {L : I -> J -> Nat} {k : I -> Nat} {ell : J -> Nat}
    (matching : TypedPartialMatching L k ell) (i : I) (j : J) :
    Fintype.card ((matching.rowAllocation i).1 j : Finset (Fin (k i))) =
      L i j := by
  simpa using (matching.rowAllocation i).2.1 j

/-- Each column-side cell of the literal matching has exactly its prescribed
demand. -/
theorem card_typedPartialMatching_columnCell
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {L : I -> J -> Nat} {k : I -> Nat} {ell : J -> Nat}
    (matching : TypedPartialMatching L k ell) (i : I) (j : J) :
    Fintype.card ((matching.columnAllocation j).1 i : Finset (Fin (ell j))) =
      L i j := by
  simpa using (matching.columnAllocation j).2.1 i

/-- The cellwise partial-matching presentation contains exactly the existing
`PrescribedDemandWitness` data; this equivalence is structural and carries no
probabilistic content. -/
def typedPartialMatchingEquivPrescribedDemandWitness
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (L : I -> J -> Nat) (k : I -> Nat) (ell : J -> Nat) :
    TypedPartialMatching L k ell ≃ PrescribedDemandWitness L k ell where
  toFun matching :=
    ⟨matching.rowAllocation, matching.columnAllocation, matching.pairing⟩
  invFun witness :=
    { rowAllocation := witness.1
      columnAllocation := witness.2.1
      pairing := witness.2.2 }
  left_inv matching := by
    cases matching
    rfl
  right_inv witness := by
    rcases witness with ⟨rowAllocation, columnAllocation, pairing⟩
    rfl

noncomputable instance instFintypeTypedPartialMatching
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (L : I -> J -> Nat) (k : I -> Nat) (ell : J -> Nat) :
    Fintype (TypedPartialMatching L k ell) :=
  Fintype.ofEquiv (PrescribedDemandWitness L k ell)
    (typedPartialMatchingEquivPrescribedDemandWitness L k ell).symm

/-- The exact cross-multiplied finite count for literal typed partial
matchings.  It is transported from the already proved prescribed-demand
count, so it remains total even when some cell demand is infeasible. -/
theorem card_typedPartialMatching_mul_factorials
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (L : I -> J -> Nat) (k : I -> Nat) (ell : J -> Nat) :
    Fintype.card (TypedPartialMatching L k ell) *
        Finset.univ.prod
          (fun i => Finset.univ.prod (fun j => (L i j).factorial)) =
      (Finset.univ.prod
          (fun i => (k i).descFactorial (Finset.univ.sum (L i)))) *
      (Finset.univ.prod
          (fun j =>
            (ell j).descFactorial (Finset.univ.sum (fun i => L i j)))) := by
  rw [Fintype.card_congr
    (typedPartialMatchingEquivPrescribedDemandWitness L k ell)]
  exact card_prescribedDemandWitness_mul_factorials L k ell

#print axioms typedPartialMatchingSourceEmbedding
#print axioms typedPartialMatchingTargetEmbedding
#print axioms typedPartialMatchingPairing
#print axioms typedPartialMatchingEquivPrescribedDemandWitness
#print axioms card_typedPartialMatching_mul_factorials

end

end Erdos625
