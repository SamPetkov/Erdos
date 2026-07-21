import Erdos625.Section8NearPrefixFoundation

/-!
# Section VIII canonical physical near prefix

This module specializes the deterministic canonical near-cell filter to an
attained physical high-skeleton fibre.  It records only the literal filtered
edge set, its exact type table, and the resulting `NearPrefix`.  In particular,
it contains no no-further-near assertion, weight identity, residual law, or
probability estimate.
-/

namespace Erdos625

noncomputable section

/-- The physical high edges whose attained type-table cell lies in the near
window.  The predicate is constant on each type cell, so this filter selects
whole physical cells. -/
def CappedPhysicalHighFibre.canonicalNearEdges
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    (endpoint : A → B → Nat)
    (H : CappedPhysicalHighFibre row col U) :
    Finset (RowStub row × ColumnStub col) := by
  classical
  exact H.physical.1.edges.filter fun e =>
    NearEntry (endpoint e.1.1 e.2.1) (H.demand.1 e.1.1 e.2.1)

/-- Literal membership in the canonical physical near-edge filter. -/
@[simp]
theorem CappedPhysicalHighFibre.mem_canonicalNearEdges
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    (endpoint : A → B → Nat)
    (H : CappedPhysicalHighFibre row col U)
    (e : RowStub row × ColumnStub col) :
    e ∈ H.canonicalNearEdges endpoint ↔
      e ∈ H.physical.1.edges ∧
        NearEntry (endpoint e.1.1 e.2.1) (H.demand.1 e.1.1 e.2.1) := by
  classical
  simp [CappedPhysicalHighFibre.canonicalNearEdges]

/-- The unlabelled physical skeleton carried by the canonical near edges.
Uniqueness of row and column stubs is inherited from the source high
skeleton. -/
def CappedPhysicalHighFibre.canonicalNearSkeleton
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    (endpoint : A → B → Nat)
    (H : CappedPhysicalHighFibre row col U) :
    UnlabelledTypedSkeleton row col where
  edges := H.canonicalNearEdges endpoint
  leftUnique := by
    intro e₁ he₁ e₂ he₂ hLeft
    exact H.physical.1.leftUnique e₁
      ((H.mem_canonicalNearEdges endpoint e₁).mp he₁).1 e₂
      ((H.mem_canonicalNearEdges endpoint e₂).mp he₂).1 hLeft
  rightUnique := by
    intro e₁ he₁ e₂ he₂ hRight
    exact H.physical.1.rightUnique e₁
      ((H.mem_canonicalNearEdges endpoint e₁).mp he₁).1 e₂
      ((H.mem_canonicalNearEdges endpoint e₂).mp he₂).1 hRight

/-- Exact cell table of the canonical physical near skeleton: an attained
cell is retained with its full multiplicity precisely when it lies in the
near window. -/
theorem CappedPhysicalHighFibre.canonicalNearSkeleton_typeTable
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    (endpoint : A → B → Nat)
    (H : CappedPhysicalHighFibre row col U)
    (a : A) (b : B) :
    (H.canonicalNearSkeleton endpoint).typeTable a b =
      if NearEntry (endpoint a b) (H.demand.1 a b)
      then H.demand.1 a b else 0 := by
  classical
  by_cases hNear : NearEntry (endpoint a b) (H.demand.1 a b)
  · have hFilter :
        (H.canonicalNearEdges endpoint).filter
            (fun e => e.1.1 = a ∧ e.2.1 = b) =
          H.physical.1.edges.filter
            (fun e => e.1.1 = a ∧ e.2.1 = b) := by
      ext e
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨he, ha, hb⟩
        exact ⟨((H.mem_canonicalNearEdges endpoint e).mp he).1, ha, hb⟩
      · rintro ⟨he, ha, hb⟩
        refine ⟨(H.mem_canonicalNearEdges endpoint e).mpr ⟨he, ?_⟩, ha, hb⟩
        simpa [ha, hb] using hNear
    rw [if_pos hNear]
    change
      ((H.canonicalNearEdges endpoint).filter
        (fun e => e.1.1 = a ∧ e.2.1 = b)).card = H.demand.1 a b
    rw [hFilter]
    exact congrFun (congrFun H.physical_typeTable a) b
  · have hFilter :
        (H.canonicalNearEdges endpoint).filter
            (fun e => e.1.1 = a ∧ e.2.1 = b) = ∅ := by
      ext e
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro he ha hb
      apply hNear
      have heNear := ((H.mem_canonicalNearEdges endpoint e).mp he).2
      simpa [ha, hb] using heNear
    rw [if_neg hNear]
    change
      ((H.canonicalNearEdges endpoint).filter
        (fun e => e.1.1 = a ∧ e.2.1 = b)).card = 0
    rw [hFilter, Finset.card_empty]

/-- The canonical whole-cell filter is a genuine physical `NearPrefix` of the
attained capped high fibre. -/
def CappedPhysicalHighFibre.canonicalNearPrefix
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    (endpoint : A → B → Nat)
    (H : CappedPhysicalHighFibre row col U) :
    NearPrefix endpoint H where
  physical := H.canonicalNearSkeleton endpoint
  edge_subset := by
    intro e he
    exact ((H.mem_canonicalNearEdges endpoint e).mp he).1
  whole_cell_of_present := by
    intro a b hPresent
    have hNear : NearEntry (endpoint a b) (H.demand.1 a b) := by
      by_contra hNotNear
      rw [H.canonicalNearSkeleton_typeTable endpoint a b,
        if_neg hNotNear] at hPresent
      exact hPresent rfl
    rw [H.canonicalNearSkeleton_typeTable endpoint a b, if_pos hNear]
    exact (congrFun (congrFun H.physical_typeTable a) b).symm
  near_of_present := by
    intro a b hPresent
    by_contra hNotNear
    rw [H.canonicalNearSkeleton_typeTable endpoint a b,
      if_neg hNotNear] at hPresent
    exact hPresent rfl

end

end Erdos625
