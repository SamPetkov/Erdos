import Erdos625.Section9PhysicalCycleCutting
import Erdos625.Section9ActualResidualENNRealPolymerBridge
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Section IX: residual-only simple-cycle enumeration

This module gives the physical cycle-to-walk injection for simple bipartite
cycles disjoint from the distinguished cell set.  A covering cycle walk is
rotated to begin at a row vertex, reified as an actual recursive kernel-path
code, and recovered from its decoded physical cells.  The resulting injection
has one row mark and an even walk length at least four.

The final theorem drops endpoint closure and simplicity only after this
injection, then applies the finite kernel row bound and the even geometric
tail.  It is a deterministic finite-kernel result; no residual probability
law or asymptotic assertion is made here.
-/

namespace Erdos625

open scoped BigOperators ENNReal

set_option autoImplicit false

noncomputable section

/-! ## Rooting a physical cycle at a row vertex -/

/-- The cell graph has its tautological two-coloring by the two bipartition
classes. -/
def cellGraphBicoloring
    {A B : Type*} (C : Finset (A × B)) :
    (cellGraph C).Coloring Bool := by
  refine ⟨fun v => Sum.elim (fun _ => false) (fun _ => true) v, ?_⟩
  intro u v huv
  rcases u with a | b <;> rcases v with a' | b' <;>
    simp [cellGraph] at huv ⊢

/-- Rotate a closed joined edge list so that a selected edge is first.  The
new start is the first endpoint of that edge. -/
theorem exists_closed_rotation_starting_at
    {V : Type*} {start : V} {edges : List (V × V)}
    (hclosed : OrientedEdgeList.Joins start edges start)
    {opening : V × V} (hopening : opening ∈ edges) :
    ∃ rotated : List (V × V),
      edges.Perm rotated ∧
        OrientedEdgeList.Joins opening.1 rotated opening.1 := by
  obtain ⟨before, after, hedges⟩ := List.mem_iff_append.mp hopening
  rcases opening with ⟨u, x⟩
  rw [hedges] at hclosed
  obtain ⟨middle, hbefore, hrest⟩ :=
    OrientedEdgeList.joins_append_iff.mp hclosed
  simp only [OrientedEdgeList.Joins] at hrest
  rcases hrest with ⟨rfl, hafter⟩
  refine ⟨(u, x) :: (after ++ before), ?_, ?_⟩
  · rw [hedges]
    simpa [List.append_assoc] using
      (List.perm_append_comm :
        List.Perm (before ++ ((u, x) :: after))
          (((u, x) :: after) ++ before))
  · exact ⟨rfl, OrientedEdgeList.joins_append hafter hbefore⟩

/-- Every selected physical edge of a closed bipartite traversal yields a
cyclic rotation rooted in the row class. -/
theorem exists_rowRooted_closed_rotation
    {A B : Type*} {start : A ⊕ B}
    {edges : List ((A ⊕ B) × (A ⊕ B))}
    (hclosed : OrientedEdgeList.Joins start edges start)
    {selected : (A ⊕ B) × (A ⊕ B)}
    (hselected : selected ∈ edges)
    {cell : A × B}
    (hdecode : orientedPairToCell selected = some cell) :
    ∃ (a : A) (rotated : List ((A ⊕ B) × (A ⊕ B))),
      edges.Perm rotated ∧
        OrientedEdgeList.Joins (Sum.inl a) rotated (Sum.inl a) := by
  rcases selected with ⟨u, v⟩
  rcases u with a | b <;> rcases v with a' | b' <;>
    simp [orientedPairToCell] at hdecode
  · obtain ⟨rotated, hperm, hjoins⟩ :=
      exists_closed_rotation_starting_at hclosed hselected
    exact ⟨a, rotated, hperm, hjoins⟩
  · obtain ⟨initial, hperm, hjoins, _⟩ :=
      exists_closed_rotation_ending_at hclosed hselected
    exact ⟨a', initial ++ [(Sum.inr b, Sum.inl a')], hperm, hjoins⟩

/-! ## The finite data-only target and its decoder -/

/-- A row-rooted closed recursive path of even length `4, 6, 8, ...` below
the ambient finite cutoff.  The predecessor `k` records length `2*k+4`. -/
abbrev ResidualCycleTraversalCode
    (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] :=
  Σ a : A, Σ k : Fin (Fintype.card (A ⊕ B)),
    KernelPathCode (A ⊕ B) (2 * k.1 + 4) (Sum.inl a) (Sum.inl a)

namespace ResidualCycleTraversalCode

def startRow
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (code : ResidualCycleTraversalCode A B) : A :=
  code.1

def lengthPredecessor
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (code : ResidualCycleTraversalCode A B) :
    Fin (Fintype.card (A ⊕ B)) :=
  code.2.1

def path
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (code : ResidualCycleTraversalCode A B) :
    KernelPathCode (A ⊕ B) (2 * code.lengthPredecessor.1 + 4)
      (Sum.inl code.startRow) (Sum.inl code.startRow) :=
  code.2.2

def orientedEdges
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (code : ResidualCycleTraversalCode A B) :
    List ((A ⊕ B) × (A ⊕ B)) :=
  kernelPathOrientedEdges code.path

def decodedCells
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (code : ResidualCycleTraversalCode A B) : Finset (A × B) :=
  decodeOrientedCells code.orientedEdges

def weight
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ENNReal)
    (code : ResidualCycleTraversalCode A B) : ENNReal :=
  code.path.weight (bipartiteCellKernel q)

end ResidualCycleTraversalCode

/-- Faithfulness records exactly the data needed for reconstruction and for
turning a list product into the physical edge-set product. -/
structure IsFaithfulResidualCycleTraversal
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (C : Finset (A × B)) (code : ResidualCycleTraversalCode A B) : Prop where
  decodedCells_eq : code.decodedCells = C
  decodedCellList_nodup :
    (code.orientedEdges.filterMap orientedPairToCell).Nodup
  orientedEdges_decode : ∀ edge ∈ code.orientedEdges,
    ∃ cell, orientedPairToCell edge = some cell

/-! ## Physical existence, choice, and reconstruction -/

/-- Every intrinsic simple bipartite cycle has a faithful row-rooted closed
path code of even length at least four. -/
theorem exists_faithfulResidualCycleTraversal
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (C : Finset (A × B)) (hC : IsSimpleBipartiteCycle C) :
    ∃ code : ResidualCycleTraversalCode A B,
      IsFaithfulResidualCycleTraversal C code := by
  obtain ⟨v, p, hp, hcover, _, hlengthBound⟩ :=
    exists_covering_cycleWalk_of_minimal_even C hC
  obtain ⟨cell, hcell⟩ := hC.2.1
  obtain ⟨selected, hselected, hselectedDecode⟩ :=
    exists_walkOrientedEdge_of_mem_of_cover p hcover hcell
  obtain ⟨a, rotated, hperm, hrotatedClosed⟩ :=
    exists_rowRooted_closed_rotation (walkOrientedEdges_joins p)
      hselected hselectedDecode
  have hpEven : Even p.length :=
    ((cellGraphBicoloring C).even_length_iff_congr p).mpr Iff.rfl
  obtain ⟨halfLength, hhalfLength⟩ := hpEven
  have hlengthFour : 4 ≤ p.length := by
    have hlengthThree := hp.three_le_length
    omega
  let kNat := halfLength - 2
  have hlengthFormula : p.length = 2 * kNat + 4 := by
    dsimp only [kNat]
    omega
  have hkBound : kNat < Fintype.card (A ⊕ B) := by
    omega
  let k : Fin (Fintype.card (A ⊕ B)) := ⟨kNat, hkBound⟩
  have hrotatedLength : rotated.length = 2 * k.1 + 4 := by
    calc
      rotated.length = (walkOrientedEdges p).length := hperm.length_eq.symm
      _ = p.length := walkOrientedEdges_length p
      _ = 2 * k.1 + 4 := hlengthFormula
  obtain ⟨rawCode, hrawCode⟩ :=
    exists_kernelPathCode_orientedEdges_eq rotated hrotatedClosed
  let pathCode : KernelPathCode (A ⊕ B) (2 * k.1 + 4)
      (Sum.inl a) (Sum.inl a) :=
    castKernelPathCode hrotatedLength rawCode
  let code : ResidualCycleTraversalCode A B := ⟨a, k, pathCode⟩
  have hcodeEdges : code.orientedEdges = rotated := by
    change kernelPathOrientedEdges pathCode = rotated
    dsimp only [pathCode]
    rw [kernelPathOrientedEdges_castKernelPathCode, hrawCode]
  refine ⟨code, {
    decodedCells_eq := ?_
    decodedCellList_nodup := ?_
    orientedEdges_decode := ?_
  }⟩
  · rw [ResidualCycleTraversalCode.decodedCells, hcodeEdges]
    calc
      decodeOrientedCells rotated =
          decodeOrientedCells (walkOrientedEdges p) :=
        (decodeOrientedCells_eq_of_perm hperm).symm
      _ = C :=
        decodeOrientedCells_walkOrientedEdges_eq_of_cover p hcover
  · rw [hcodeEdges]
    exact
      filterMap_orientedPairToCell_nodup_of_perm_walkOrientedEdges hp hperm
  · intro edge hedge
    rw [hcodeEdges] at hedge
    have hedgeWalk : edge ∈ walkOrientedEdges p := hperm.mem_iff.mpr hedge
    obtain ⟨sourceCell, _, hdecode⟩ :=
      walkOrientedEdge_decodes_mem p hedgeWalk
    exact ⟨sourceCell, hdecode⟩

/-- Residual-only simple cycles as an honest finite source type. -/
abbrev ResidualOnlySimpleCycle
    (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) :=
  {C : Finset (A × B) //
    C ∈ (simpleBipartiteCycles A B).filter (fun C => Disjoint C M)}

theorem residualOnlySimpleCycle_isSimple
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {M : Finset (A × B)} (C : ResidualOnlySimpleCycle A B M) :
    IsSimpleBipartiteCycle C.1 := by
  have hmem := (Finset.mem_filter.mp C.2).1
  unfold simpleBipartiteCycles at hmem
  simpa using hmem

theorem residualOnlySimpleCycle_disjoint
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {M : Finset (A × B)} (C : ResidualOnlySimpleCycle A B M) :
    Disjoint C.1 M :=
  (Finset.mem_filter.mp C.2).2

/-- Canonically choose the data-only faithful traversal supplied above. -/
noncomputable def chosenResidualOnlyCycleTraversal
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (C : ResidualOnlySimpleCycle A B M) :
    ResidualCycleTraversalCode A B :=
  Classical.choose
    (exists_faithfulResidualCycleTraversal C.1
      (residualOnlySimpleCycle_isSimple C))

theorem chosenResidualOnlyCycleTraversal_faithful
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (C : ResidualOnlySimpleCycle A B M) :
    IsFaithfulResidualCycleTraversal C.1
      (chosenResidualOnlyCycleTraversal M C) :=
  Classical.choose_spec
    (exists_faithfulResidualCycleTraversal C.1
      (residualOnlySimpleCycle_isSimple C))

theorem chosenResidualOnlyCycleTraversal_injective
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) :
    Function.Injective (chosenResidualOnlyCycleTraversal M) := by
  intro C D hcode
  apply Subtype.ext
  have hdecoded := congrArg ResidualCycleTraversalCode.decodedCells hcode
  exact
    (chosenResidualOnlyCycleTraversal_faithful M C).decodedCells_eq.symm.trans
      (hdecoded.trans
        (chosenResidualOnlyCycleTraversal_faithful M D).decodedCells_eq)

/-! ## Exact weight and finite enumeration -/

theorem chosenResidualOnlyCycleTraversal_weight_eq
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ENNReal) (M : Finset (A × B))
    (C : ResidualOnlySimpleCycle A B M) :
    (chosenResidualOnlyCycleTraversal M C).weight q =
      edgeWeightOutsideENN q M C.1 := by
  let code := chosenResidualOnlyCycleTraversal M C
  have hfaithful := chosenResidualOnlyCycleTraversal_faithful M C
  have hsdiff : C.1 \ M = C.1 := by
    apply Finset.Subset.antisymm Finset.sdiff_subset
    intro edge hedge
    exact Finset.mem_sdiff.mpr
      ⟨hedge, fun hedgeM =>
        Finset.disjoint_left.mp (residualOnlySimpleCycle_disjoint C)
          hedge hedgeM⟩
  calc
    code.weight q =
        orientedEdgeListWeight (bipartiteCellKernel q)
          code.orientedEdges :=
      kernelPathCode_weight_eq_orientedEdgeListWeight _ code.path
    _ = ((code.orientedEdges.filterMap orientedPairToCell).map
          fun cell => q cell.1 cell.2).prod :=
      orientedEdgeListWeight_bipartiteCellKernel_eq_cellListProd
        q code.orientedEdges hfaithful.orientedEdges_decode
    _ = (code.orientedEdges.filterMap orientedPairToCell).toFinset.prod
          (fun cell => q cell.1 cell.2) :=
      (List.prod_toFinset _ hfaithful.decodedCellList_nodup).symm
    _ = C.1.prod (fun cell => q cell.1 cell.2) := by
      change code.decodedCells.prod (fun cell => q cell.1 cell.2) = _
      rw [hfaithful.decodedCells_eq]
    _ = edgeWeightOutsideENN q M C.1 := by
      unfold edgeWeightOutsideENN
      rw [hsdiff]

theorem sum_residualOnlySimpleCycle_weight_le_traversalCode
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ENNReal) (M : Finset (A × B)) :
    (∑ C : ResidualOnlySimpleCycle A B M,
        edgeWeightOutsideENN q M C.1) ≤
      ∑ code : ResidualCycleTraversalCode A B, code.weight q := by
  calc
    (∑ C : ResidualOnlySimpleCycle A B M,
        edgeWeightOutsideENN q M C.1) =
        ∑ C : ResidualOnlySimpleCycle A B M,
          (chosenResidualOnlyCycleTraversal M C).weight q := by
      apply Finset.sum_congr rfl
      intro C hC
      exact (chosenResidualOnlyCycleTraversal_weight_eq q M C).symm
    _ ≤ ∑ code : ResidualCycleTraversalCode A B, code.weight q := by
      simpa only [tsum_fintype] using
        ENNReal.tsum_comp_le_tsum_of_injective
          (chosenResidualOnlyCycleTraversal_injective M)
          (fun code : ResidualCycleTraversalCode A B => code.weight q)

theorem sum_residualCycleTraversalCode_weight_eq_endpointMass
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ENNReal) :
    (∑ code : ResidualCycleTraversalCode A B, code.weight q) =
      ∑ a : A, ∑ k : Fin (Fintype.card (A ⊕ B)),
        finiteKernelEndpointMass (bipartiteCellKernel q)
          (2 * k.1 + 4) (Sum.inl a) (Sum.inl a) := by
  unfold ResidualCycleTraversalCode.weight ResidualCycleTraversalCode.path
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k hk
  exact sum_kernelPathCode_weight_eq_finiteKernelEndpointMass
    (bipartiteCellKernel q) (2 * k.1 + 4) (Sum.inl a) (Sum.inl a)

theorem sum_residualCycleTraversalCode_weight_le_walkMass
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ENNReal) :
    (∑ code : ResidualCycleTraversalCode A B, code.weight q) ≤
      ∑ a : A, ∑ k : Fin (Fintype.card (A ⊕ B)),
        finiteKernelWalkMass (bipartiteCellKernel q)
          (2 * k.1 + 4) (Sum.inl a) := by
  rw [sum_residualCycleTraversalCode_weight_eq_endpointMass]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro k hk
  calc
    finiteKernelEndpointMass (bipartiteCellKernel q)
        (2 * k.1 + 4) (Sum.inl a) (Sum.inl a) ≤
        ∑ w, finiteKernelEndpointMass (bipartiteCellKernel q)
          (2 * k.1 + 4) (Sum.inl a) w := by
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun w => finiteKernelEndpointMass (bipartiteCellKernel q)
          (2 * k.1 + 4) (Sum.inl a) w)
        (fun w _ => bot_le) (Finset.mem_univ (Sum.inl a))
    _ = finiteKernelWalkMass (bipartiteCellKernel q)
          (2 * k.1 + 4) (Sum.inl a) :=
      sum_finiteKernelEndpointMass_eq_finiteKernelWalkMass
        (bipartiteCellKernel q) (2 * k.1 + 4) (Sum.inl a)

theorem sum_rowRooted_evenWalkMass_le_geometric
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ENNReal) (tau : ENNReal)
    (hRow : ∀ a, ∑ b, q a b ≤ tau)
    (hColumn : ∀ b, ∑ a, q a b ≤ tau) :
    (∑ a : A, ∑ k : Fin (Fintype.card (A ⊕ B)),
        finiteKernelWalkMass (bipartiteCellKernel q)
          (2 * k.1 + 4) (Sum.inl a)) ≤
      (Fintype.card A : ENNReal) *
        (tau ^ 4 * (1 - tau ^ 2)⁻¹) := by
  let L := Fintype.card (A ⊕ B)
  have hKernelRow : ∀ v, ∑ w, bipartiteCellKernel q v w ≤ tau :=
    bipartiteCellKernel_rowSum_le q tau hRow hColumn
  calc
    (∑ a : A, ∑ k : Fin L,
        finiteKernelWalkMass (bipartiteCellKernel q)
          (2 * k.1 + 4) (Sum.inl a)) ≤
        ∑ a : A, ∑ k : Fin L, tau ^ (2 * k.1 + 4) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro k hk
      exact finiteKernelWalkMass_le_pow (bipartiteCellKernel q) tau
        hKernelRow (2 * k.1 + 4) (Sum.inl a)
    _ = (Fintype.card A : ENNReal) *
        (∑ k ∈ Finset.range L, tau ^ (2 * k + 4)) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun k => tau ^ (2 * k + 4)) L]
      simp
    _ ≤ (Fintype.card A : ENNReal) *
        (tau ^ 4 * (1 - tau ^ 2)⁻¹) :=
      mul_le_mul_right (sum_range_pow_even_add_four_le_geometric tau L)
        (Fintype.card A : ENNReal)

private theorem sum_filter_eq_sum_subtype
    {X : Type*} [DecidableEq X] (S : Finset X) (f : X → ENNReal) :
    (∑ x ∈ S, f x) = ∑ x : {x : X // x ∈ S}, f x.1 := by
  symm
  rw [show (Finset.univ : Finset {x : X // x ∈ S}) = S.attach by
    ext x
    simp]
  exact Finset.sum_attach S f

/-! ## Residual-only cycle bound -/

/-- Weighted enumeration of every simple bipartite cycle disjoint from `M`.
Each physical cycle is injected into a row-rooted alternating closed walk of
even length at least four before closure and simplicity are discarded. -/
theorem residualOnlySimpleCycle_weighted_walk_enumeration
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ENNReal) (M : Finset (A × B))
    (tau : ENNReal) (htau : tau < 1)
    (hRow : ∀ a, ∑ b, q a b ≤ tau)
    (hColumn : ∀ b, ∑ a, q a b ≤ tau) :
    (∑ C ∈ (simpleBipartiteCycles A B).filter (fun C => Disjoint C M),
        edgeWeightOutsideENN q M C) ≤
      (Fintype.card A : ENNReal) * (tau ^ 4 * (1 - tau ^ 2)⁻¹) := by
  by_cases h : tau < 1
  · calc
      (∑ C ∈ (simpleBipartiteCycles A B).filter
          (fun C => Disjoint C M), edgeWeightOutsideENN q M C) =
          ∑ C : ResidualOnlySimpleCycle A B M,
            edgeWeightOutsideENN q M C.1 :=
        sum_filter_eq_sum_subtype
          ((simpleBipartiteCycles A B).filter (fun C => Disjoint C M))
          (fun C => edgeWeightOutsideENN q M C)
      _ ≤ ∑ code : ResidualCycleTraversalCode A B, code.weight q :=
        sum_residualOnlySimpleCycle_weight_le_traversalCode q M
      _ ≤ ∑ a : A, ∑ k : Fin (Fintype.card (A ⊕ B)),
          finiteKernelWalkMass (bipartiteCellKernel q)
            (2 * k.1 + 4) (Sum.inl a) :=
        sum_residualCycleTraversalCode_weight_le_walkMass q
      _ ≤ (Fintype.card A : ENNReal) *
          (tau ^ 4 * (1 - tau ^ 2)⁻¹) :=
        sum_rowRooted_evenWalkMass_le_geometric q tau hRow hColumn
  · exact (h htau).elim

#print axioms exists_faithfulResidualCycleTraversal
#print axioms chosenResidualOnlyCycleTraversal_injective
#print axioms chosenResidualOnlyCycleTraversal_weight_eq
#print axioms sum_residualOnlySimpleCycle_weight_le_traversalCode
#print axioms sum_residualCycleTraversalCode_weight_eq_endpointMass
#print axioms sum_residualCycleTraversalCode_weight_le_walkMass
#print axioms sum_rowRooted_evenWalkMass_le_geometric
#print axioms residualOnlySimpleCycle_weighted_walk_enumeration

end

end Erdos625
