import Erdos625.Section8CanonicalNearPrefix

/-!
# Section VIII canonical near-prefix uniqueness

This module records the deterministic no-further-near property of the
canonical prefix and its uniqueness among physical whole-cell near prefixes.
The reverse inclusion uses finite cell cardinalities explicitly; it does not
assume edgewise whole-cell closure as an extra premise.
-/

namespace Erdos625

noncomputable section

/-- A physical subset with the same cell cardinality as its ambient skeleton
contains exactly the same physical edges in that cell. -/
theorem UnlabelledTypedSkeleton.cellFilter_eq_of_edges_subset_of_typeTable_eq
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat}
    (S T : UnlabelledTypedSkeleton row col) (a : A) (b : B)
    (hSub : S.edges ⊆ T.edges)
    (hTable : S.typeTable a b = T.typeTable a b) :
    S.edges.filter (fun e ⇒ e.1.1 = a ∧ e.2.1 = b) =
      T.edges.filter (fun e ⇒ e.1.1 = a ∧ e.2.1 = b) := by
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨hSub he.1, he.2⟩
  · change T.typeTable a b ≤ S.typeTable a b
    rw [hTable]

/-- The canonical near prefix leaves no attained near cell unselected. -/
theorem CappedPhysicalHighFibre.canonicalNearPrefix_noFurtherNear
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    (endpoint : A → B → Nat)
    (H : CappedPhysicalHighFibre row col U) :
    NoFurtherNear endpoint H (H.canonicalNearPrefix endpoint) := by
  intro a b hDemand hNear
  change (H.canonicalNearSkeleton endpoint).typeTable a b ≠ 0
  rw [H.canonicalNearSkeleton_typeTable endpoint a b, if_pos hNear]
  exact hDemand

/-- Every physical whole-cell near prefix satisfying `NoFurtherNear` has the
canonical filtered edge set. -/
theorem NearPrefix.edges_eq_canonicalNearEdges_of_noFurtherNear
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    {endpoint : A → B → Nat}
    {H : CappedPhysicalHighFibre row col U}
    (P : NearPrefix endpoint H)
    (hNoFurther : NoFurtherNear endpoint H P) :
    P.physical.edges = H.canonicalNearEdges endpoint := by
  apply Finset.Subset.antisymm
  · intro e he
    apply (H.mem_canonicalNearEdges endpoint e).mpr
    refine ⟨P.edge_subset he, ?_⟩
    have hPresent : P.physical.typeTable e.1.1 e.2.1 ≠ 0 :=
      (P.physical.typeTable_ne_zero_iff_exists_physical_edge
        e.1.1 e.2.1).mpr ⟨e, he, rfl, rfl⟩
    exact P.near_of_present e.1.1 e.2.1 hPresent
  · intro e he
    have heCanonical := (H.mem_canonicalNearEdges endpoint e).mp he
    have hDemand : H.demand.1 e.1.1 e.2.1 ≠ 0 :=
      (H.demand_ne_zero_iff_exists_physical_edge
        e.1.1 e.2.1).mpr ⟨e, heCanonical.1, rfl, rfl⟩
    have hPresent : P.physical.typeTable e.1.1 e.2.1 ≠ 0 :=
      hNoFurther e.1.1 e.2.1 hDemand heCanonical.2
    have hTable :
        P.physical.typeTable e.1.1 e.2.1 =
          H.physical.1.typeTable e.1.1 e.2.1 :=
      P.whole_cell_of_present e.1.1 e.2.1 hPresent
    have hCellEq :=
      UnlabelledTypedSkeleton.cellFilter_eq_of_edges_subset_of_typeTable_eq
        P.physical H.physical.1 e.1.1 e.2.1 P.edge_subset hTable
    have heCell :
        e ∈ H.physical.1.edges.filter
          (fun f ⇒ f.1.1 = e.1.1 ∧ f.2.1 = e.2.1) := by
      exact Finset.mem_filter.mpr ⟨heCanonical.1, rfl, rfl⟩
    rw [← hCellEq] at heCell
    exact (Finset.mem_filter.mp heCell).1

/-- Every physical whole-cell near prefix satisfying `NoFurtherNear` is the
canonical filtered skeleton. -/
theorem NearPrefix.physical_eq_canonicalNearSkeleton_of_noFurtherNear
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    {endpoint : A → B → Nat}
    {H : CappedPhysicalHighFibre row col U}
    (P : NearPrefix endpoint H)
    (hNoFurther : NoFurtherNear endpoint H P) :
    P.physical = H.canonicalNearSkeleton endpoint := by
  apply UnlabelledTypedSkeleton.ext
  change P.physical.edges = H.canonicalNearEdges endpoint
  exact P.edges_eq_canonicalNearEdges_of_noFurtherNear hNoFurther

/-- For fixed `H`, the canonical physical whole-cell near prefix is the unique
near prefix satisfying `NoFurtherNear`. -/
theorem CappedPhysicalHighFibre.existsUnique_nearPrefix_noFurtherNear
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    (endpoint : A → B → Nat)
    (H : CappedPhysicalHighFibre row col U) :
    ∃! P : NearPrefix endpoint H, NoFurtherNear endpoint H P := by
  refine ⟨H.canonicalNearPrefix endpoint,
    H.canonicalNearPrefix_noFurtherNear endpoint, ?_⟩
  intro P hP
  apply NearPrefix.ext
  exact P.physical_eq_canonicalNearSkeleton_of_noFurtherNear hP

end

end Erdos625
