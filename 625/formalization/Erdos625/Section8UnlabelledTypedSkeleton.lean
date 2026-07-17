import Erdos625.Section8TypedPartialMatching
import Mathlib.Tactic

/-!
# Section VIII: unlabelled typed skeletons

This module forgets the cellwise presentation of a `TypedPartialMatching` and
retains only its physical row--column stub edges.  An unlabelled skeleton is a
finite bipartite edge set in which no row stub and no column stub occurs twice.
Its `typeTable` counts physical edges by their row and column types.

The construction below is finite and deterministic.  It contains no
probability or asymptotic assertion.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- A physical finite partial matching between typed row and column stubs. -/
structure UnlabelledTypedSkeleton
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (k : I -> Nat) (ell : J -> Nat) where
  edges : Finset (RowStub k × ColumnStub ell)
  leftUnique :
    ∀ e₁ ∈ edges, ∀ e₂ ∈ edges, e₁.1 = e₂.1 -> e₁ = e₂
  rightUnique :
    ∀ e₁ ∈ edges, ∀ e₂ ∈ edges, e₁.2 = e₂.2 -> e₁ = e₂

@[ext]
theorem UnlabelledTypedSkeleton.ext
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    {S T : UnlabelledTypedSkeleton k ell}
    (hEdges : S.edges = T.edges) :
    S = T := by
  cases S
  cases T
  simp_all

noncomputable instance instFintypeUnlabelledTypedSkeleton
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (k : I -> Nat) (ell : J -> Nat) :
    Fintype (UnlabelledTypedSkeleton k ell) := by
  letI : Finite (UnlabelledTypedSkeleton k ell) :=
    Finite.of_injective
      (fun S : UnlabelledTypedSkeleton k ell => S.edges)
      (fun _ _ h => UnlabelledTypedSkeleton.ext h)
  exact Fintype.ofFinite _

/-- The number of physical skeleton edges in each row-type/column-type cell. -/
def UnlabelledTypedSkeleton.typeTable
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (i : I) (j : J) : Nat :=
  (S.edges.filter (fun e => e.1.1 = i ∧ e.2.1 = j)).card

/-- The physical edges in one fixed type cell, with the type indices removed
from their endpoints. -/
def UnlabelledTypedSkeleton.cellEdges
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (i : I) (j : J) :
    Finset (Fin (k i) × Fin (ell j)) :=
  Finset.univ.filter
    (fun p => ((⟨i, p.1⟩, ⟨j, p.2⟩) :
      RowStub k × ColumnStub ell) ∈ S.edges)

/-- Row stubs used by one type cell. -/
def UnlabelledTypedSkeleton.rowCell
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (i : I) (j : J) :
    Finset (Fin (k i)) :=
  (S.cellEdges i j).image Prod.fst

/-- Column stubs used by one type cell. -/
def UnlabelledTypedSkeleton.columnCell
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (i : I) (j : J) :
    Finset (Fin (ell j)) :=
  (S.cellEdges i j).image Prod.snd

private theorem cellEdges_card_eq_typeTable
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (i : I) (j : J) :
    (S.cellEdges i j).card = S.typeTable i j := by
  unfold UnlabelledTypedSkeleton.cellEdges
    UnlabelledTypedSkeleton.typeTable
  refine Finset.card_bij
    (fun p _ =>
      ((⟨i, p.1⟩, ⟨j, p.2⟩) :
        RowStub k × ColumnStub ell)) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.2, rfl, rfl⟩
  · intro p₁ hp₁ p₂ hp₂ hEq
    exact Prod.ext
      (eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst hEq)).2)
      (eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.snd hEq)).2)
  · intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨hEdge, hI, hJ⟩ := he
    obtain ⟨⟨i', r⟩, ⟨j', c⟩⟩ := e
    simp only at hI hJ
    subst i'
    subst j'
    exact ⟨(r, c), by simp [hEdge], rfl⟩

private theorem rowCell_card
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (i : I) (j : J) :
    (S.rowCell i j).card = S.typeTable i j := by
  rw [UnlabelledTypedSkeleton.rowCell,
    Finset.card_image_of_injOn]
  · exact cellEdges_card_eq_typeTable S i j
  · intro p₁ hp₁ p₂ hp₂ hFirst
    have hEdge₁ :
        ((⟨i, p₁.1⟩, ⟨j, p₁.2⟩) :
          RowStub k × ColumnStub ell) ∈ S.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using hp₁
    have hEdge₂ :
        ((⟨i, p₂.1⟩, ⟨j, p₂.2⟩) :
          RowStub k × ColumnStub ell) ∈ S.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using hp₂
    have hGlobal := S.leftUnique _ hEdge₁ _ hEdge₂ (by
      exact Sigma.ext rfl (heq_of_eq hFirst))
    exact Prod.ext hFirst
      (eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.snd hGlobal)).2)

private theorem columnCell_card
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (i : I) (j : J) :
    (S.columnCell i j).card = S.typeTable i j := by
  rw [UnlabelledTypedSkeleton.columnCell,
    Finset.card_image_of_injOn]
  · exact cellEdges_card_eq_typeTable S i j
  · intro p₁ hp₁ p₂ hp₂ hSecond
    have hEdge₁ :
        ((⟨i, p₁.1⟩, ⟨j, p₁.2⟩) :
          RowStub k × ColumnStub ell) ∈ S.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using hp₁
    have hEdge₂ :
        ((⟨i, p₂.1⟩, ⟨j, p₂.2⟩) :
          RowStub k × ColumnStub ell) ∈ S.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using hp₂
    have hGlobal := S.rightUnique _ hEdge₁ _ hEdge₂ (by
      exact Sigma.ext rfl (heq_of_eq hSecond))
    exact Prod.ext
      (eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst hGlobal)).2)
      hSecond

private theorem rowCell_disjoint
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (i : I)
    (j₁ j₂ : J) (hNe : j₁ ≠ j₂) :
    Disjoint (S.rowCell i j₁) (S.rowCell i j₂) := by
  rw [Finset.disjoint_left]
  intro r hr₁ hr₂
  rw [UnlabelledTypedSkeleton.rowCell, Finset.mem_image] at hr₁ hr₂
  obtain ⟨p₁, hp₁, hFirst₁⟩ := hr₁
  obtain ⟨p₂, hp₂, hFirst₂⟩ := hr₂
  have hEdge₁ :
      ((⟨i, p₁.1⟩, ⟨j₁, p₁.2⟩) :
        RowStub k × ColumnStub ell) ∈ S.edges := by
    simpa [UnlabelledTypedSkeleton.cellEdges] using hp₁
  have hEdge₂ :
      ((⟨i, p₂.1⟩, ⟨j₂, p₂.2⟩) :
        RowStub k × ColumnStub ell) ∈ S.edges := by
    simpa [UnlabelledTypedSkeleton.cellEdges] using hp₂
  have hLeft : (⟨i, p₁.1⟩ : RowStub k) = ⟨i, p₂.1⟩ := by
    exact Sigma.ext rfl (heq_of_eq (hFirst₁.trans hFirst₂.symm))
  have hEdges := S.leftUnique _ hEdge₁ _ hEdge₂ hLeft
  exact hNe (congrArg (fun e => e.2.1) hEdges)

private theorem columnCell_disjoint
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (j : J)
    (i₁ i₂ : I) (hNe : i₁ ≠ i₂) :
    Disjoint (S.columnCell i₁ j) (S.columnCell i₂ j) := by
  rw [Finset.disjoint_left]
  intro c hc₁ hc₂
  rw [UnlabelledTypedSkeleton.columnCell, Finset.mem_image] at hc₁ hc₂
  obtain ⟨p₁, hp₁, hSecond₁⟩ := hc₁
  obtain ⟨p₂, hp₂, hSecond₂⟩ := hc₂
  have hEdge₁ :
      ((⟨i₁, p₁.1⟩, ⟨j, p₁.2⟩) :
        RowStub k × ColumnStub ell) ∈ S.edges := by
    simpa [UnlabelledTypedSkeleton.cellEdges] using hp₁
  have hEdge₂ :
      ((⟨i₂, p₂.1⟩, ⟨j, p₂.2⟩) :
        RowStub k × ColumnStub ell) ∈ S.edges := by
    simpa [UnlabelledTypedSkeleton.cellEdges] using hp₂
  have hRight : (⟨j, p₁.2⟩ : ColumnStub ell) = ⟨j, p₂.2⟩ := by
    exact Sigma.ext rfl (heq_of_eq (hSecond₁.trans hSecond₂.symm))
  have hEdges := S.rightUnique _ hEdge₁ _ hEdge₂ hRight
  exact hNe (congrArg (fun e => e.1.1) hEdges)

private def skeletonRowAllocation
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {L : I -> J -> Nat} {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (hTable : S.typeTable = L)
    (i : I) :
    StubAllocation (k i) (L i) :=
  ⟨S.rowCell i, by
    constructor
    · intro j
      rw [rowCell_card]
      exact congrFun (congrFun hTable i) j
    · intro j₁ j₂ hNe
      exact rowCell_disjoint S i j₁ j₂ hNe⟩

private def skeletonColumnAllocation
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {L : I -> J -> Nat} {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (hTable : S.typeTable = L)
    (j : J) :
    StubAllocation (ell j) (fun i => L i j) :=
  ⟨fun i => S.columnCell i j, by
    constructor
    · intro i
      rw [columnCell_card]
      exact congrFun (congrFun hTable i) j
    · intro i₁ i₂ hNe
      exact columnCell_disjoint S j i₁ i₂ hNe⟩

private noncomputable def skeletonCellEdgeOfRow
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (i : I) (j : J)
    (r : ↑(S.rowCell i j)) :
    Fin (k i) × Fin (ell j) :=
  Classical.choose (Finset.mem_image.mp r.2)

private theorem skeletonCellEdgeOfRow_mem
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (i : I) (j : J)
    (r : ↑(S.rowCell i j)) :
    skeletonCellEdgeOfRow S i j r ∈ S.cellEdges i j :=
  (Classical.choose_spec (Finset.mem_image.mp r.2)).1

private theorem skeletonCellEdgeOfRow_fst
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (i : I) (j : J)
    (r : ↑(S.rowCell i j)) :
    (skeletonCellEdgeOfRow S i j r).1 = r.1 :=
  (Classical.choose_spec (Finset.mem_image.mp r.2)).2

private noncomputable def skeletonCellPairing
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (i : I) (j : J) :
    ↑(S.rowCell i j) ≃ ↑(S.columnCell i j) := by
  let toColumn :
      ↑(S.rowCell i j) -> ↑(S.columnCell i j) :=
    fun r =>
      ⟨(skeletonCellEdgeOfRow S i j r).2,
        Finset.mem_image.mpr
          ⟨skeletonCellEdgeOfRow S i j r,
            skeletonCellEdgeOfRow_mem S i j r, rfl⟩⟩
  refine Equiv.ofBijective toColumn ⟨?_, ?_⟩
  · intro r₁ r₂ hColumn
    have hEdge₁ :
        ((⟨i, (skeletonCellEdgeOfRow S i j r₁).1⟩,
            ⟨j, (skeletonCellEdgeOfRow S i j r₁).2⟩) :
          RowStub k × ColumnStub ell) ∈ S.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using
        skeletonCellEdgeOfRow_mem S i j r₁
    have hEdge₂ :
        ((⟨i, (skeletonCellEdgeOfRow S i j r₂).1⟩,
            ⟨j, (skeletonCellEdgeOfRow S i j r₂).2⟩) :
          RowStub k × ColumnStub ell) ∈ S.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using
        skeletonCellEdgeOfRow_mem S i j r₂
    have hSecond :
        (skeletonCellEdgeOfRow S i j r₁).2 =
          (skeletonCellEdgeOfRow S i j r₂).2 :=
      congrArg Subtype.val hColumn
    have hGlobal := S.rightUnique _ hEdge₁ _ hEdge₂ (by
      exact Sigma.ext rfl (heq_of_eq hSecond))
    apply Subtype.ext
    rw [← skeletonCellEdgeOfRow_fst S i j r₁,
      ← skeletonCellEdgeOfRow_fst S i j r₂]
    exact eq_of_heq
      (Sigma.mk.inj_iff.mp (congrArg Prod.fst hGlobal)).2
  · intro c
    have hc := c.2
    change c.1 ∈ (S.cellEdges i j).image Prod.snd at hc
    rw [Finset.mem_image] at hc
    obtain ⟨p, hp, hSecond⟩ := hc
    let r : ↑(S.rowCell i j) :=
      ⟨p.1, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    refine ⟨r, ?_⟩
    apply Subtype.ext
    have hChosen :
        ((⟨i, (skeletonCellEdgeOfRow S i j r).1⟩,
            ⟨j, (skeletonCellEdgeOfRow S i j r).2⟩) :
          RowStub k × ColumnStub ell) ∈ S.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using
        skeletonCellEdgeOfRow_mem S i j r
    have hGiven :
        ((⟨i, p.1⟩, ⟨j, p.2⟩) :
          RowStub k × ColumnStub ell) ∈ S.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using hp
    have hFirst :
        (skeletonCellEdgeOfRow S i j r).1 = p.1 := by
      simpa [r] using skeletonCellEdgeOfRow_fst S i j r
    have hGlobal := S.leftUnique _ hChosen _ hGiven (by
      exact Sigma.ext rfl (heq_of_eq hFirst))
    exact (eq_of_heq
      (Sigma.mk.inj_iff.mp (congrArg Prod.snd hGlobal)).2).trans hSecond

@[simp]
private theorem skeletonCellPairing_apply
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (i : I) (j : J)
    (r : ↑(S.rowCell i j)) :
    ((skeletonCellPairing S i j r : ↑(S.columnCell i j)) :
      Fin (ell j)) =
      (skeletonCellEdgeOfRow S i j r).2 := by
  rfl

/-- The graph edge associated with every selected row atom of a typed partial
matching.  Injectivity follows already from injectivity on row stubs. -/
def typedPartialMatchingEdgeEmbedding
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {L : I -> J -> Nat} {k : I -> Nat} {ell : J -> Nat}
    (matching : TypedPartialMatching L k ell) :
    TypedPartialMatchingSource matching ↪
      (RowStub k × ColumnStub ell) where
  toFun atom :=
    (typedPartialMatchingSourceEmbedding matching atom,
      typedPartialMatchingTargetEmbedding matching
        (typedPartialMatchingPairing matching atom))
  inj' := by
    intro atom₁ atom₂ h
    apply (typedPartialMatchingSourceEmbedding matching).injective
    exact congrArg Prod.fst h

/-- Forget the cellwise presentation of a typed partial matching and retain
only its physical edge set. -/
def typedPartialMatchingUnlabelledSkeleton
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {L : I -> J -> Nat} {k : I -> Nat} {ell : J -> Nat}
    (matching : TypedPartialMatching L k ell) :
    UnlabelledTypedSkeleton k ell where
  edges := Finset.univ.map (typedPartialMatchingEdgeEmbedding matching)
  leftUnique := by
    intro e₁ he₁ e₂ he₂ hLeft
    rw [Finset.mem_map] at he₁ he₂
    obtain ⟨atom₁, _, rfl⟩ := he₁
    obtain ⟨atom₂, _, rfl⟩ := he₂
    have hAtom :
        atom₁ = atom₂ :=
      (typedPartialMatchingSourceEmbedding matching).injective hLeft
    subst atom₂
    rfl
  rightUnique := by
    intro e₁ he₁ e₂ he₂ hRight
    rw [Finset.mem_map] at he₁ he₂
    obtain ⟨atom₁, _, rfl⟩ := he₁
    obtain ⟨atom₂, _, rfl⟩ := he₂
    have hPaired :
        typedPartialMatchingPairing matching atom₁ =
          typedPartialMatchingPairing matching atom₂ :=
      (typedPartialMatchingTargetEmbedding matching).injective hRight
    have hAtom :
        atom₁ = atom₂ :=
      (typedPartialMatchingPairing matching).injective hPaired
    subst atom₂
    rfl

private theorem card_source_cell_filter
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {L : I -> J -> Nat} {k : I -> Nat} {ell : J -> Nat}
    (matching : TypedPartialMatching L k ell) (i : I) (j : J) :
    (Finset.univ.filter
        (fun atom : TypedPartialMatchingSource matching =>
          atom.1 = i ∧ atom.2.1 = j)).card =
      ((matching.rowAllocation i).1 j).card := by
  symm
  refine Finset.card_bij
    (fun stub hStub =>
      (⟨i, j, ⟨stub, hStub⟩⟩ :
        TypedPartialMatchingSource matching)) ?_ ?_ ?_
  · intro stub hStub
    simp
  · intro stub₁ hStub₁ stub₂ hStub₂ hEq
    have hUnderlying :
        (⟨stub₁, hStub₁⟩ :
          ((matching.rowAllocation i).1 j : Finset (Fin (k i)))) =
        ⟨stub₂, hStub₂⟩ := by
      exact eq_of_heq (Sigma.mk.inj_iff.mp
        (eq_of_heq (Sigma.mk.inj_iff.mp hEq).2)).2
    exact congrArg Subtype.val hUnderlying
  · intro atom hAtom
    rw [Finset.mem_filter] at hAtom
    obtain ⟨_, hI, hJ⟩ := hAtom
    obtain ⟨i', j', stub⟩ := atom
    simp only at hI hJ
    subst i'
    subst j'
    exact ⟨stub.1, stub.2, rfl⟩

/-- Forgetting cell labels does not change the prescribed type table. -/
theorem typedPartialMatchingUnlabelledSkeleton_typeTable
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {L : I -> J -> Nat} {k : I -> Nat} {ell : J -> Nat}
    (matching : TypedPartialMatching L k ell) :
    (typedPartialMatchingUnlabelledSkeleton matching).typeTable = L := by
  funext i j
  unfold UnlabelledTypedSkeleton.typeTable
  change
    ((Finset.univ.map (typedPartialMatchingEdgeEmbedding matching)).filter
      (fun e => e.1.1 = i ∧ e.2.1 = j)).card = L i j
  rw [Finset.filter_map, Finset.card_map]
  change
    (Finset.univ.filter
      (fun atom : TypedPartialMatchingSource matching =>
        atom.1 = i ∧ atom.2.1 = j)).card = L i j
  rw [card_source_cell_filter matching i j]
  simpa using (matching.rowAllocation i).2.1 j

/-- The forward map from cellwise typed partial matchings to physical
unlabelled skeletons with the prescribed type table. -/
def typedPartialMatchingToUnlabelledSkeletonFibre
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (L : I -> J -> Nat) (k : I -> Nat) (ell : J -> Nat) :
    TypedPartialMatching L k ell ->
      {S : UnlabelledTypedSkeleton k ell // S.typeTable = L} :=
  fun matching =>
    ⟨typedPartialMatchingUnlabelledSkeleton matching,
      typedPartialMatchingUnlabelledSkeleton_typeTable matching⟩

/-- Reconstruct the cellwise presentation from a physical skeleton.  The
within-cell equivalence is the unique pairing encoded by the physical edges;
the use of classical choice only selects that already unique endpoint. -/
noncomputable def unlabelledSkeletonFibreToTypedPartialMatching
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (L : I -> J -> Nat) (k : I -> Nat) (ell : J -> Nat) :
    {S : UnlabelledTypedSkeleton k ell // S.typeTable = L} ->
      TypedPartialMatching L k ell :=
  fun S =>
    { rowAllocation := skeletonRowAllocation S.1 S.2
      columnAllocation := skeletonColumnAllocation S.1 S.2
      pairing := fun i j => skeletonCellPairing S.1 i j }

private theorem reconstructed_edgeEmbedding_apply
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (L : I -> J -> Nat) (k : I -> Nat) (ell : J -> Nat)
    (S : {S : UnlabelledTypedSkeleton k ell // S.typeTable = L})
    (i : I) (j : J) (r : ↑(S.1.rowCell i j)) :
    typedPartialMatchingEdgeEmbedding
        (unlabelledSkeletonFibreToTypedPartialMatching L k ell S)
        ⟨i, j, r⟩ =
      ((⟨i, r.1⟩,
          ⟨j, (skeletonCellEdgeOfRow S.1 i j r).2⟩) :
        RowStub k × ColumnStub ell) := by
  apply Prod.ext
  · rfl
  · apply Sigma.ext rfl
    exact heq_of_eq (skeletonCellPairing_apply S.1 i j r)

private theorem unlabelledSkeleton_roundTrip_edges
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (L : I -> J -> Nat) (k : I -> Nat) (ell : J -> Nat)
    (S : {S : UnlabelledTypedSkeleton k ell // S.typeTable = L}) :
    (typedPartialMatchingUnlabelledSkeleton
      (unlabelledSkeletonFibreToTypedPartialMatching L k ell S)).edges =
      S.1.edges := by
  ext e
  constructor
  · intro he
    rw [typedPartialMatchingUnlabelledSkeleton, Finset.mem_map] at he
    obtain ⟨atom, _, rfl⟩ := he
    obtain ⟨i, j, r⟩ := atom
    change ↑(S.1.rowCell i j) at r
    have hCell :=
      skeletonCellEdgeOfRow_mem S.1 i j r
    have hEdge :
        ((⟨i, (skeletonCellEdgeOfRow S.1 i j r).1⟩,
            ⟨j, (skeletonCellEdgeOfRow S.1 i j r).2⟩) :
          RowStub k × ColumnStub ell) ∈ S.1.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using hCell
    have hFirst :
        (skeletonCellEdgeOfRow S.1 i j r).1 = r.1 :=
      skeletonCellEdgeOfRow_fst S.1 i j r
    rw [reconstructed_edgeEmbedding_apply L k ell S i j r]
    simpa [hFirst] using hEdge
  · intro he
    obtain ⟨⟨i, r⟩, ⟨j, c⟩⟩ := e
    let p : Fin (k i) × Fin (ell j) := (r, c)
    have hp : p ∈ S.1.cellEdges i j := by
      simp [p, UnlabelledTypedSkeleton.cellEdges, he]
    let r' : ↑(S.1.rowCell i j) :=
      ⟨r, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    let atom :
        TypedPartialMatchingSource
          (unlabelledSkeletonFibreToTypedPartialMatching L k ell S) :=
      ⟨i, j, r'⟩
    rw [typedPartialMatchingUnlabelledSkeleton, Finset.mem_map]
    refine ⟨atom, Finset.mem_univ _, ?_⟩
    have hChosen :
        ((⟨i, (skeletonCellEdgeOfRow S.1 i j r').1⟩,
            ⟨j, (skeletonCellEdgeOfRow S.1 i j r').2⟩) :
          RowStub k × ColumnStub ell) ∈ S.1.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using
        skeletonCellEdgeOfRow_mem S.1 i j r'
    have hGiven :
        ((⟨i, p.1⟩, ⟨j, p.2⟩) :
          RowStub k × ColumnStub ell) ∈ S.1.edges := by
      simpa [p] using he
    have hFirst :
        (skeletonCellEdgeOfRow S.1 i j r').1 = p.1 := by
      simpa [r', p] using skeletonCellEdgeOfRow_fst S.1 i j r'
    have hEdges := S.1.leftUnique _ hChosen _ hGiven (by
      exact Sigma.ext rfl (heq_of_eq hFirst))
    have hSecond :
        (skeletonCellEdgeOfRow S.1 i j r').2 = p.2 :=
      eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.snd hEdges)).2
    change
      typedPartialMatchingEdgeEmbedding
          (unlabelledSkeletonFibreToTypedPartialMatching L k ell S)
          ⟨i, j, r'⟩ =
        ((⟨i, r⟩, ⟨j, c⟩) :
          RowStub k × ColumnStub ell)
    rw [reconstructed_edgeEmbedding_apply L k ell S i j r']
    apply Prod.ext
    · exact Sigma.ext rfl (heq_of_eq rfl)
    · exact Sigma.ext rfl (heq_of_eq (by simpa [p] using hSecond))

private theorem typedPartialMatching_roundTrip_rowCell
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {L : I -> J -> Nat} {k : I -> Nat} {ell : J -> Nat}
    (matching : TypedPartialMatching L k ell) (i : I) (j : J) :
    (typedPartialMatchingUnlabelledSkeleton matching).rowCell i j =
      (matching.rowAllocation i).1 j := by
  ext r
  simp [UnlabelledTypedSkeleton.rowCell,
    UnlabelledTypedSkeleton.cellEdges,
    typedPartialMatchingUnlabelledSkeleton,
    typedPartialMatchingEdgeEmbedding,
    typedPartialMatchingSourceEmbedding,
    typedPartialMatchingTargetEmbedding,
    typedPartialMatchingPairing]

private theorem typedPartialMatching_roundTrip_columnCell
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {L : I -> J -> Nat} {k : I -> Nat} {ell : J -> Nat}
    (matching : TypedPartialMatching L k ell) (i : I) (j : J) :
    (typedPartialMatchingUnlabelledSkeleton matching).columnCell i j =
      (matching.columnAllocation j).1 i := by
  ext c
  constructor
  · intro hc
    rw [UnlabelledTypedSkeleton.columnCell, Finset.mem_image] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    rw [UnlabelledTypedSkeleton.cellEdges, Finset.mem_filter] at hp
    obtain ⟨_, hp⟩ := hp
    rw [typedPartialMatchingUnlabelledSkeleton, Finset.mem_map] at hp
    obtain ⟨atom, _, hAtom⟩ := hp
    have hRow := congrArg Prod.fst hAtom
    have hColumn := congrArg Prod.snd hAtom
    obtain ⟨i', j', r⟩ := atom
    simp [typedPartialMatchingEdgeEmbedding,
      typedPartialMatchingSourceEmbedding,
      typedPartialMatchingTargetEmbedding,
      typedPartialMatchingPairing] at hRow hColumn
    obtain ⟨hI, _⟩ := hRow
    obtain ⟨hJ, hC⟩ := hColumn
    subst i'
    subst j'
    rw [← eq_of_heq hC]
    exact (matching.pairing i j r).2
  · intro hc
    let c' :
        ((matching.columnAllocation j).1 i :
          Finset (Fin (ell j))) := ⟨c, hc⟩
    let r' := (matching.pairing i j).symm c'
    let p : Fin (k i) × Fin (ell j) := (r'.1, c)
    rw [UnlabelledTypedSkeleton.columnCell, Finset.mem_image]
    refine ⟨p, ?_, rfl⟩
    rw [UnlabelledTypedSkeleton.cellEdges, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [typedPartialMatchingUnlabelledSkeleton, Finset.mem_map]
    refine ⟨(⟨i, j, r'⟩ :
      TypedPartialMatchingSource matching), Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · exact Sigma.ext rfl (heq_of_eq rfl)
    · change
        (typedPartialMatchingEdgeEmbedding matching
          (⟨i, j, r'⟩ : TypedPartialMatchingSource matching)).2 =
          (⟨j, c⟩ : ColumnStub ell)
      change
        (⟨j, ((matching.pairing i j) r' : Fin (ell j))⟩ :
          ColumnStub ell) =
          ⟨j, c⟩
      exact Sigma.ext rfl (heq_of_eq (by
        change ((matching.pairing i j) r' : Fin (ell j)) = c
        simp [r', c']))

private theorem typedPartialMatchingUnlabelledSkeleton_injective
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {L : I -> J -> Nat} {k : I -> Nat} {ell : J -> Nat} :
    Function.Injective
      (typedPartialMatchingUnlabelledSkeleton :
        TypedPartialMatching L k ell ->
          UnlabelledTypedSkeleton k ell) := by
  intro matching₁ matching₂ hSkeleton
  have hRows :
      matching₁.rowAllocation = matching₂.rowAllocation := by
    funext i
    apply Subtype.ext
    funext j
    rw [← typedPartialMatching_roundTrip_rowCell matching₁ i j,
      hSkeleton,
      typedPartialMatching_roundTrip_rowCell matching₂ i j]
  have hColumns :
      matching₁.columnAllocation = matching₂.columnAllocation := by
    funext j
    apply Subtype.ext
    funext i
    rw [← typedPartialMatching_roundTrip_columnCell matching₁ i j,
      hSkeleton,
      typedPartialMatching_roundTrip_columnCell matching₂ i j]
  obtain ⟨rowAllocation₁, columnAllocation₁, pairing₁⟩ := matching₁
  obtain ⟨rowAllocation₂, columnAllocation₂, pairing₂⟩ := matching₂
  simp only at hRows hColumns
  subst rowAllocation₂
  subst columnAllocation₂
  have hPairing : pairing₁ = pairing₂ := by
    funext i j
    apply Equiv.ext
    intro r
    let matching₁ : TypedPartialMatching L k ell :=
      { rowAllocation := rowAllocation₁
        columnAllocation := columnAllocation₁
        pairing := pairing₁ }
    let matching₂ : TypedPartialMatching L k ell :=
      { rowAllocation := rowAllocation₁
        columnAllocation := columnAllocation₁
        pairing := pairing₂ }
    let atom₁ : TypedPartialMatchingSource matching₁ := ⟨i, j, r⟩
    let atom₂ : TypedPartialMatchingSource matching₂ := ⟨i, j, r⟩
    let edge₁ := typedPartialMatchingEdgeEmbedding matching₁ atom₁
    let edge₂ := typedPartialMatchingEdgeEmbedding matching₂ atom₂
    have hEdge₁ :
        edge₁ ∈
          (typedPartialMatchingUnlabelledSkeleton matching₁).edges := by
      simp [edge₁, atom₁, typedPartialMatchingUnlabelledSkeleton]
    have hEdge₂ :
        edge₂ ∈
          (typedPartialMatchingUnlabelledSkeleton matching₂).edges := by
      simp [edge₂, atom₂, typedPartialMatchingUnlabelledSkeleton]
    have hSkeleton' :
        typedPartialMatchingUnlabelledSkeleton matching₁ =
          typedPartialMatchingUnlabelledSkeleton matching₂ := by
      simpa [matching₁, matching₂] using hSkeleton
    have hEdge₁' :
        edge₁ ∈
          (typedPartialMatchingUnlabelledSkeleton matching₂).edges := by
      rw [← hSkeleton']
      exact hEdge₁
    have hLeft : edge₁.1 = edge₂.1 := by
      rfl
    have hEdges :=
      (typedPartialMatchingUnlabelledSkeleton matching₂).leftUnique
        edge₁ hEdge₁' edge₂ hEdge₂ hLeft
    apply Subtype.ext
    exact eq_of_heq
      (Sigma.mk.inj_iff.mp (congrArg Prod.snd hEdges)).2
  subst pairing₂
  rfl

/-- Cellwise typed partial matchings are exactly physical unlabelled skeletons
whose type table is the prescribed matrix.  No ordering is introduced inside
a cell on either side of this equivalence. -/
noncomputable def typedPartialMatchingEquivUnlabelledSkeletonFibre
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (L : I -> J -> Nat) (k : I -> Nat) (ell : J -> Nat) :
    TypedPartialMatching L k ell ≃
      {S : UnlabelledTypedSkeleton k ell // S.typeTable = L} :=
  Equiv.ofBijective
    (typedPartialMatchingToUnlabelledSkeletonFibre L k ell)
    ⟨by
      intro matching₁ matching₂ h
      apply typedPartialMatchingUnlabelledSkeleton_injective
      exact congrArg Subtype.val h,
    by
      intro S
      refine ⟨unlabelledSkeletonFibreToTypedPartialMatching L k ell S, ?_⟩
      apply Subtype.ext
      apply UnlabelledTypedSkeleton.ext
      exact unlabelledSkeleton_roundTrip_edges L k ell S⟩

/-- Exact finite cardinality of the physical unlabelled-skeleton fibre.  The
single cell-factorial product is inherited directly from the literal
typed-partial-matching count; there is no additional quotient or factorial
division. -/
theorem card_unlabelledTypedSkeleton_typeTable_mul_factorials
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (L : I -> J -> Nat) (k : I -> Nat) (ell : J -> Nat) :
    Fintype.card
          {S : UnlabelledTypedSkeleton k ell // S.typeTable = L} *
        Finset.univ.prod
          (fun i => Finset.univ.prod (fun j => (L i j).factorial)) =
      (Finset.univ.prod
          (fun i => (k i).descFactorial (Finset.univ.sum (L i)))) *
      (Finset.univ.prod
          (fun j =>
            (ell j).descFactorial
              (Finset.univ.sum (fun i => L i j)))) := by
  rw [← Fintype.card_congr
    (typedPartialMatchingEquivUnlabelledSkeletonFibre L k ell)]
  exact card_typedPartialMatching_mul_factorials L k ell

#print axioms UnlabelledTypedSkeleton.ext
#print axioms typedPartialMatchingUnlabelledSkeleton
#print axioms typedPartialMatchingUnlabelledSkeleton_typeTable
#print axioms unlabelledSkeletonFibreToTypedPartialMatching
#print axioms typedPartialMatchingEquivUnlabelledSkeletonFibre
#print axioms card_unlabelledTypedSkeleton_typeTable_mul_factorials

end

end Erdos625
