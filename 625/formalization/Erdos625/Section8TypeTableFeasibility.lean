import Erdos625.Section8UnlabelledTypedSkeleton
import Mathlib.Tactic

/-!
# Section VIII: feasibility margins for unlabelled typed skeleton tables

This module proves the literal capacity inequalities for the already-defined
physical skeleton `typeTable`; it does not assume a matching presentation or
replace the concrete skeleton definitions with a weaker surrogate.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

private theorem cellEdges_card_eq_typeTable_aux
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

private theorem rowCell_card_aux
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (i : I) (j : J) :
    (S.rowCell i j).card = S.typeTable i j := by
  rw [UnlabelledTypedSkeleton.rowCell,
    Finset.card_image_of_injOn]
  · exact cellEdges_card_eq_typeTable_aux S i j
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

private theorem columnCell_card_aux
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (i : I) (j : J) :
    (S.columnCell i j).card = S.typeTable i j := by
  rw [UnlabelledTypedSkeleton.columnCell,
    Finset.card_image_of_injOn]
  · exact cellEdges_card_eq_typeTable_aux S i j
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

private theorem rowCell_disjoint_aux
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (i : I)
    (j1 j2 : J) (hNe : j1 ≠ j2) :
    Disjoint (S.rowCell i j1) (S.rowCell i j2) := by
  rw [Finset.disjoint_left]
  intro r hr1 hr2
  rw [UnlabelledTypedSkeleton.rowCell, Finset.mem_image] at hr1 hr2
  rcases hr1 with ⟨p1, hp1, hFirst1⟩
  rcases hr2 with ⟨p2, hp2, hFirst2⟩
  have hEdge1 :
      ((Sigma.mk i p1.1, Sigma.mk j1 p1.2) :
        Prod (RowStub k) (ColumnStub ell)) ∈ S.edges := by
    simpa [UnlabelledTypedSkeleton.cellEdges] using hp1
  have hEdge2 :
      ((Sigma.mk i p2.1, Sigma.mk j2 p2.2) :
        Prod (RowStub k) (ColumnStub ell)) ∈ S.edges := by
    simpa [UnlabelledTypedSkeleton.cellEdges] using hp2
  have hLeft : (Sigma.mk i p1.1 : RowStub k) = Sigma.mk i p2.1 := by
    exact Sigma.ext rfl (heq_of_eq (hFirst1.trans hFirst2.symm))
  have hEdges := S.leftUnique _ hEdge1 _ hEdge2 hLeft
  exact hNe (congrArg (fun e => e.2.1) hEdges)

private theorem columnCell_disjoint_aux
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (j : J)
    (i1 i2 : I) (hNe : i1 ≠ i2) :
    Disjoint (S.columnCell i1 j) (S.columnCell i2 j) := by
  rw [Finset.disjoint_left]
  intro c hc1 hc2
  rw [UnlabelledTypedSkeleton.columnCell, Finset.mem_image] at hc1 hc2
  rcases hc1 with ⟨p1, hp1, hSecond1⟩
  rcases hc2 with ⟨p2, hp2, hSecond2⟩
  have hEdge1 :
      ((Sigma.mk i1 p1.1, Sigma.mk j p1.2) :
        Prod (RowStub k) (ColumnStub ell)) ∈ S.edges := by
    simpa [UnlabelledTypedSkeleton.cellEdges] using hp1
  have hEdge2 :
      ((Sigma.mk i2 p2.1, Sigma.mk j p2.2) :
        Prod (RowStub k) (ColumnStub ell)) ∈ S.edges := by
    simpa [UnlabelledTypedSkeleton.cellEdges] using hp2
  have hRight : (Sigma.mk j p1.2 : ColumnStub ell) = Sigma.mk j p2.2 := by
    exact Sigma.ext rfl (heq_of_eq (hSecond1.trans hSecond2.symm))
  have hEdges := S.rightUnique _ hEdge1 _ hEdge2 hRight
  exact hNe (congrArg (fun e => e.1.1) hEdges)

/-- Every row type in a physical unlabelled skeleton uses at most its available
row stubs. -/
theorem UnlabelledTypedSkeleton.sum_typeTable_row_le
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (i : I) :
    Finset.univ.sum (fun j => S.typeTable i j) <= k i := by
  calc
    Finset.univ.sum (fun j => S.typeTable i j)
        = Finset.univ.sum (fun j => (S.rowCell i j).card) := by
          apply Finset.sum_congr rfl
          intro j _
          exact (rowCell_card_aux S i j).symm
    _ = (Finset.biUnion Finset.univ (fun j => S.rowCell i j)).card := by
          rw [Finset.card_biUnion]
          intro j1 _ j2 _ hNe
          exact rowCell_disjoint_aux S i j1 j2 hNe
    _ <= (Finset.univ : Finset (Fin (k i))).card := by
          exact Finset.card_le_univ _
    _ = k i := by
          simp

/-- Every column type in a physical unlabelled skeleton uses at most its
available column stubs. -/
theorem UnlabelledTypedSkeleton.sum_typeTable_column_le
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {k : I -> Nat} {ell : J -> Nat}
    (S : UnlabelledTypedSkeleton k ell) (j : J) :
    Finset.univ.sum (fun i => S.typeTable i j) <= ell j := by
  calc
    Finset.univ.sum (fun i => S.typeTable i j)
        = Finset.univ.sum (fun i => (S.columnCell i j).card) := by
          apply Finset.sum_congr rfl
          intro i _
          exact (columnCell_card_aux S i j).symm
    _ = (Finset.biUnion Finset.univ (fun i => S.columnCell i j)).card := by
          rw [Finset.card_biUnion]
          intro i1 _ i2 _ hNe
          exact columnCell_disjoint_aux S j i1 i2 hNe
    _ <= (Finset.univ : Finset (Fin (ell j))).card := by
          exact Finset.card_le_univ _
    _ = ell j := by
          simp

#print axioms Erdos625.UnlabelledTypedSkeleton.sum_typeTable_row_le
#print axioms Erdos625.UnlabelledTypedSkeleton.sum_typeTable_column_le

end

end Erdos625
