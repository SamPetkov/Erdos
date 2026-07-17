import Erdos625.Section9MinimalEvenCycleTour
import Erdos625.Section9BlockChainEnumeration

/-!
# Section 9: source-free decoding of a cycle cut at matching edges

This module isolates the data that a genuine cut of a simple cycle must
produce.  A `RelaxedBlockChainCode` contains only its successive positive
residual paths and matching transitions; in particular, it does not contain
the source cycle, an injectivity certificate, or a reconstruction proof.

The physical existence theorem which cuts the covering cycle walk at the
edges of `C ∩ M` is deliberately not postulated here.  The definitions and
lemmas below give its target interface: exact residual and transition lists,
separate path- and block-count cutoffs, endpoint closure, a source-free
decoder, and exact nonnegative kernel-weight preservation.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-! ## Oriented edges of the recursive path codes -/

/-- The successive oriented edges represented by a fixed-length kernel path
code.  No edge set or source object is stored in this list. -/
def kernelPathOrientedEdges {V : Type*} :
    {ell : ℕ} → {v w : V} →
      KernelPathCode V ell v w → List (V × V)
  | 0, _, _, _ => []
  | _ + 1, v, _, code =>
      (v, code.1) :: kernelPathOrientedEdges code.2

@[simp]
theorem kernelPathOrientedEdges_length
    {V : Type*} {ell : ℕ} {v w : V}
    (code : KernelPathCode V ell v w) :
    (kernelPathOrientedEdges code).length = ell := by
  induction ell generalizing v with
  | zero => rfl
  | succ ell ih =>
      simp [kernelPathOrientedEdges, ih code.2]

/-- A list of oriented edges joins its declared initial and terminal
vertices.  This small recursive predicate is independent of graph adjacency;
adjacency is supplied later by the kernels or by a covering walk. -/
def OrientedEdgeList.Joins {V : Type*} :
    V → List (V × V) → V → Prop
  | v, [], w => v = w
  | v, (x, y) :: edges, w => x = v ∧ Joins y edges w

namespace OrientedEdgeList

@[simp]
theorem joins_nil {V : Type*} {v w : V} :
    Joins v [] w ↔ v = w := Iff.rfl

@[simp]
theorem joins_cons {V : Type*} {v x y w : V}
    {edges : List (V × V)} :
    Joins v ((x, y) :: edges) w ↔ x = v ∧ Joins y edges w := Iff.rfl

theorem joins_append {V : Type*} {u v w : V}
    {left right : List (V × V)}
    (hleft : Joins u left v) (hright : Joins v right w) :
    Joins u (left ++ right) w := by
  induction left generalizing u with
  | nil =>
      simpa [Joins] using hleft ▸ hright
  | cons edge tail ih =>
      rcases edge with ⟨x, y⟩
      simp only [Joins] at hleft ⊢
      exact ⟨hleft.1, ih hleft.2⟩

end OrientedEdgeList

theorem kernelPathOrientedEdges_joins
    {V : Type*} {ell : ℕ} {v w : V}
    (code : KernelPathCode V ell v w) :
    OrientedEdgeList.Joins v (kernelPathOrientedEdges code) w := by
  induction ell generalizing v with
  | zero =>
      exact code.2.1.symm.trans code.2.2
  | succ ell ih =>
      exact ⟨rfl, ih code.2⟩

/-! ## Exact residual and transition projections -/

/-- The positive residual path in the first block of a chain. -/
def positivePathOrientedEdges {V : Type*} {L : ℕ} {v w : V}
    (code : PositiveKernelPathCode V L v w) : List (V × V) :=
  kernelPathOrientedEdges code.2

@[simp]
theorem positivePathOrientedEdges_length
    {V : Type*} {L : ℕ} {v w : V}
    (code : PositiveKernelPathCode V L v w) :
    (positivePathOrientedEdges code).length = code.length := by
  exact kernelPathOrientedEdges_length code.2

theorem positivePathOrientedEdges_length_pos
    {V : Type*} {L : ℕ} {v w : V}
    (code : PositiveKernelPathCode V L v w) :
    0 < (positivePathOrientedEdges code).length := by
  simp [positivePathOrientedEdges]

theorem positivePathOrientedEdges_length_le
    {V : Type*} {L : ℕ} {v w : V}
    (code : PositiveKernelPathCode V L v w) :
    (positivePathOrientedEdges code).length ≤ L := by
  rw [positivePathOrientedEdges_length]
  exact code.1.2

theorem positivePathOrientedEdges_joins
    {V : Type*} {L : ℕ} {v w : V}
    (code : PositiveKernelPathCode V L v w) :
    OrientedEdgeList.Joins v (positivePathOrientedEdges code) w :=
  kernelPathOrientedEdges_joins code.2

/-- All residual-path edges in a relaxed block chain, with block boundaries
forgotten but multiplicity and orientation retained. -/
def relaxedBlockResidualEdges {V : Type*} {L : ℕ} :
    {r : ℕ} → {v w : V} →
      RelaxedBlockChainCode V L r v w → List (V × V)
  | 0, _, _, _ => []
  | _ + 1, _, _, code =>
      positivePathOrientedEdges code.2.1.2 ++
        relaxedBlockResidualEdges code.2.2

/-- The transition edges in a relaxed block chain.  There is exactly one
such edge per block. -/
def relaxedBlockTransitionEdges {V : Type*} {L : ℕ} :
    {r : ℕ} → {v w : V} →
      RelaxedBlockChainCode V L r v w → List (V × V)
  | 0, _, _, _ => []
  | _ + 1, _, _, code =>
      (code.2.1.1, code.1) :: relaxedBlockTransitionEdges code.2.2

/-- The oriented edge list decoded from a relaxed block chain, retaining the
physical cyclic order: positive residual path, one transition, then the
remaining blocks. -/
def relaxedBlockOrientedEdges {V : Type*} {L : ℕ} :
    {r : ℕ} → {v w : V} →
      RelaxedBlockChainCode V L r v w → List (V × V)
  | 0, _, _, _ => []
  | _ + 1, _, _, code =>
      positivePathOrientedEdges code.2.1.2 ++
        (code.2.1.1, code.1) :: relaxedBlockOrientedEdges code.2.2

/-- The list of positive residual-path lengths.  Its length is the block
count, whereas its entries are the separate path lengths. -/
def relaxedBlockPathLengths {V : Type*} {L : ℕ} :
    {r : ℕ} → {v w : V} →
      RelaxedBlockChainCode V L r v w → List ℕ
  | 0, _, _, _ => []
  | _ + 1, _, _, code =>
      code.2.1.2.length :: relaxedBlockPathLengths code.2.2

@[simp]
theorem relaxedBlockTransitionEdges_length
    {V : Type*} {L r : ℕ} {v w : V}
    (code : RelaxedBlockChainCode V L r v w) :
    (relaxedBlockTransitionEdges code).length = r := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih =>
      simp [relaxedBlockTransitionEdges, ih code.2.2]

@[simp]
theorem relaxedBlockPathLengths_length
    {V : Type*} {L r : ℕ} {v w : V}
    (code : RelaxedBlockChainCode V L r v w) :
    (relaxedBlockPathLengths code).length = r := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih =>
      simp [relaxedBlockPathLengths, ih code.2.2]

/-- Each path cutoff is independent of the number of blocks. -/
theorem relaxedBlockPathLengths_mem_bounds
    {V : Type*} {L r : ℕ} {v w : V}
    (code : RelaxedBlockChainCode V L r v w) :
    ∀ ell ∈ relaxedBlockPathLengths code, 0 < ell ∧ ell ≤ L := by
  induction r generalizing v with
  | zero => simp [relaxedBlockPathLengths]
  | succ r ih =>
      intro ell hell
      simp only [relaxedBlockPathLengths, List.mem_cons] at hell
      rcases hell with rfl | hell
      · exact ⟨by simp [PositiveKernelPathCode.length], code.2.1.2.1.2⟩
      · exact ih code.2.2 ell hell

@[simp]
theorem relaxedBlockResidualEdges_length
    {V : Type*} {L r : ℕ} {v w : V}
    (code : RelaxedBlockChainCode V L r v w) :
    (relaxedBlockResidualEdges code).length =
      (relaxedBlockPathLengths code).sum := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih =>
      simp [relaxedBlockResidualEdges, relaxedBlockPathLengths,
        ih code.2.2]

theorem relaxedBlockResidualEdges_length_ge_blocks
    {V : Type*} {L r : ℕ} {v w : V}
    (code : RelaxedBlockChainCode V L r v w) :
    r ≤ (relaxedBlockResidualEdges code).length := by
  induction r generalizing v with
  | zero => exact Nat.zero_le _
  | succ r ih =>
      simp only [relaxedBlockResidualEdges, List.length_append,
        positivePathOrientedEdges_length]
      calc
        r + 1 = 1 + r := Nat.add_comm _ _
        _ ≤ code.2.1.2.length +
              (relaxedBlockResidualEdges code.2.2).length :=
          Nat.add_le_add
            (by simp [PositiveKernelPathCode.length])
            (ih code.2.2)

@[simp]
theorem relaxedBlockOrientedEdges_length
    {V : Type*} {L r : ℕ} {v w : V}
    (code : RelaxedBlockChainCode V L r v w) :
    (relaxedBlockOrientedEdges code).length =
      (relaxedBlockResidualEdges code).length + r := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih =>
      simp [relaxedBlockOrientedEdges, relaxedBlockResidualEdges,
        ih code.2.2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem relaxedBlockOrientedEdges_joins
    {V : Type*} {L r : ℕ} {v w : V}
    (code : RelaxedBlockChainCode V L r v w) :
    OrientedEdgeList.Joins v (relaxedBlockOrientedEdges code) w := by
  induction r generalizing v with
  | zero =>
      exact kernelPathOrientedEdges_joins code
  | succ r ih =>
      apply OrientedEdgeList.joins_append
        (positivePathOrientedEdges_joins code.2.1.2)
      exact ⟨rfl, ih code.2.2⟩

/-- Closing the endpoint fiber gives literal closure at the marked oriented
start; no `r - 1` endpoint convention is used.  A chain with `r` blocks has
`r` transitions, while the recursive tail after its first block has exactly
`r - 1` transitions. -/
theorem relaxedBlockOrientedEdges_closed
    {V : Type*} {L r : ℕ} {v : V}
    (code : RelaxedBlockChainCode V L r v v) :
    OrientedEdgeList.Joins v (relaxedBlockOrientedEdges code) v :=
  relaxedBlockOrientedEdges_joins code

theorem relaxedBlockTailTransitionEdges_length
    {V : Type*} {L r : ℕ} {v w : V}
    (code : RelaxedBlockChainCode V L (r + 1) v w) :
    (relaxedBlockTransitionEdges code.2.2).length = r :=
  relaxedBlockTransitionEdges_length code.2.2

/-! ## Source-free decoding to bipartite cells -/

/-- Forget the orientation of an alternating edge and recover its bipartite
cell.  Same-side pairs decode to no cell. -/
def orientedPairToCell {A B : Type*} :
    (A ⊕ B) × (A ⊕ B) → Option (A × B)
  | (Sum.inl a, Sum.inr b) => some (a, b)
  | (Sum.inr b, Sum.inl a) => some (a, b)
  | _ => none

/-- A `filterMap` which succeeds on every input preserves length.  This is
the generic no-drop lemma used by a faithful physical cut. -/
theorem filterMap_length_eq_length_of_forall_eq_some
    {α β : Type*} (f : α → Option β) (items : List α)
    (hdecode : ∀ item ∈ items, ∃ value, f item = some value) :
    (items.filterMap f).length = items.length := by
  induction items with
  | nil => rfl
  | cons item tail ih =>
      obtain ⟨value, hvalue⟩ := hdecode item (by simp)
      have htail : ∀ x ∈ tail, ∃ y, f x = some y := by
        intro x hx
        exact hdecode x (by simp [hx])
      simp [hvalue, ih htail]

/-- Decode an oriented edge list to its bipartite edge set. -/
def decodeOrientedCells {A B : Type*} [DecidableEq A] [DecidableEq B]
    (edges : List ((A ⊕ B) × (A ⊕ B))) : Finset (A × B) :=
  (edges.filterMap orientedPairToCell).toFinset

theorem decodeOrientedCells_append
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (left right : List ((A ⊕ B) × (A ⊕ B))) :
    decodeOrientedCells (left ++ right) =
      decodeOrientedCells left ∪ decodeOrientedCells right := by
  ext edge
  simp [decodeOrientedCells]

/-- Decode one oriented pair to either a singleton cell set or the empty
set. -/
def decodeOrientedCell {A B : Type*} [DecidableEq A] [DecidableEq B]
    (edge : (A ⊕ B) × (A ⊕ B)) : Finset (A × B) :=
  match orientedPairToCell edge with
  | some cell => {cell}
  | none => ∅

theorem decodeOrientedCells_cons_eq
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (edge : (A ⊕ B) × (A ⊕ B))
    (tail : List ((A ⊕ B) × (A ⊕ B))) :
    decodeOrientedCells (edge :: tail) =
      decodeOrientedCell edge ∪ decodeOrientedCells tail := by
  ext cell
  rcases edge with ⟨u, v⟩
  rcases u with a | b <;> rcases v with a' | b' <;>
    simp [decodeOrientedCells, decodeOrientedCell, orientedPairToCell]

/-- Residual-edge projection of a relaxed block code. -/
def decodeRelaxedResidualCells
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {L r : ℕ} {v w : A ⊕ B}
    (code : RelaxedBlockChainCode (A ⊕ B) L r v w) :
    Finset (A × B) :=
  decodeOrientedCells (relaxedBlockResidualEdges code)

/-- Transition-edge projection of a relaxed block code. -/
def decodeRelaxedTransitionCells
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {L r : ℕ} {v w : A ⊕ B}
    (code : RelaxedBlockChainCode (A ⊕ B) L r v w) :
    Finset (A × B) :=
  decodeOrientedCells (relaxedBlockTransitionEdges code)

/-- Full source-free decoder. -/
def decodeRelaxedBlockCells
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {L r : ℕ} {v w : A ⊕ B}
    (code : RelaxedBlockChainCode (A ⊕ B) L r v w) :
    Finset (A × B) :=
  decodeOrientedCells (relaxedBlockOrientedEdges code)

/-- The full decoder is exactly the union of its residual and transition
projections.  This identity is at the level of decoded cell sets, not merely
at the level of weights. -/
theorem decodeRelaxedBlockCells_eq_union
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {L r : ℕ} {v w : A ⊕ B}
    (code : RelaxedBlockChainCode (A ⊕ B) L r v w) :
    decodeRelaxedBlockCells code =
      decodeRelaxedResidualCells code ∪
        decodeRelaxedTransitionCells code := by
  induction r generalizing v with
  | zero =>
      simp [decodeRelaxedBlockCells, decodeRelaxedResidualCells,
        decodeRelaxedTransitionCells, relaxedBlockOrientedEdges,
        relaxedBlockResidualEdges, relaxedBlockTransitionEdges,
        decodeOrientedCells]
  | succ r ih =>
      have htail :
          decodeOrientedCells
              (relaxedBlockOrientedEdges code.2.2) =
            decodeOrientedCells
                (relaxedBlockResidualEdges code.2.2) ∪
              decodeOrientedCells
                (relaxedBlockTransitionEdges code.2.2) := by
        simpa only [decodeRelaxedBlockCells,
          decodeRelaxedResidualCells, decodeRelaxedTransitionCells] using
          ih code.2.2
      simp only [decodeRelaxedBlockCells, decodeRelaxedResidualCells,
        decodeRelaxedTransitionCells, relaxedBlockOrientedEdges,
        relaxedBlockResidualEdges, relaxedBlockTransitionEdges,
        decodeOrientedCells_append, decodeOrientedCells_cons_eq]
      rw [htail]
      ext cell
      simp only [Finset.mem_union]
      tauto

theorem relaxedBlockResidualEdges_sublist
    {V : Type*} {L r : ℕ} {v w : V}
    (code : RelaxedBlockChainCode V L r v w) :
    List.Sublist (relaxedBlockResidualEdges code)
      (relaxedBlockOrientedEdges code) := by
  induction r generalizing v with
  | zero => exact List.Sublist.refl []
  | succ r ih =>
      simp only [relaxedBlockResidualEdges, relaxedBlockOrientedEdges]
      exact (List.Sublist.refl _).append
        (List.Sublist.cons _ (ih code.2.2))

theorem relaxedBlockTransitionEdges_sublist
    {V : Type*} {L r : ℕ} {v w : V}
    (code : RelaxedBlockChainCode V L r v w) :
    List.Sublist (relaxedBlockTransitionEdges code)
      (relaxedBlockOrientedEdges code) := by
  induction r generalizing v with
  | zero => exact List.Sublist.refl []
  | succ r ih =>
      simp only [relaxedBlockTransitionEdges, relaxedBlockOrientedEdges]
      exact (List.Sublist.cons_cons _ (ih code.2.2)).trans
        (List.sublist_append_right _ _)

/-- Nodup of the full physical edge traversal implies nodup separately for
the residual and transition projections. -/
theorem relaxedBlock_projection_nodup
    {V : Type*} {L r : ℕ} {v w : V}
    (code : RelaxedBlockChainCode V L r v w)
    (hnodup : (relaxedBlockOrientedEdges code).Nodup) :
    (relaxedBlockResidualEdges code).Nodup ∧
      (relaxedBlockTransitionEdges code).Nodup :=
  ⟨hnodup.sublist (relaxedBlockResidualEdges_sublist code),
    hnodup.sublist (relaxedBlockTransitionEdges_sublist code)⟩

/-! ## Exact list-level nonnegative weight identity -/

/-- Product of a kernel along an oriented edge list. -/
def orientedEdgeListWeight {V : Type*}
    (K : V → V → ℝ≥0∞) (edges : List (V × V)) : ℝ≥0∞ :=
  (edges.map fun edge => K edge.1 edge.2).prod

theorem bipartiteCellKernel_eq_of_orientedPairToCell_eq_some
    {A B : Type*} (q : A → B → ℝ≥0∞)
    {edge : (A ⊕ B) × (A ⊕ B)} {cell : A × B}
    (hdecode : orientedPairToCell edge = some cell) :
    bipartiteCellKernel q edge.1 edge.2 = q cell.1 cell.2 := by
  rcases edge with ⟨u, v⟩
  rcases u with a | b <;> rcases v with a' | b' <;>
    simp [orientedPairToCell, bipartiteCellKernel] at hdecode ⊢
  all_goals subst cell
  all_goals rfl

theorem matchingTraversalKernel_eq_one_of_orientedPairToCell_eq_some
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B))
    {edge : (A ⊕ B) × (A ⊕ B)} {cell : A × B}
    (hdecode : orientedPairToCell edge = some cell) (hcell : cell ∈ M) :
    matchingTraversalKernel M edge.1 edge.2 = 1 := by
  rcases edge with ⟨u, v⟩
  rcases u with a | b <;> rcases v with a' | b' <;>
    simp [orientedPairToCell, matchingTraversalKernel] at hdecode ⊢
  all_goals subst cell
  all_goals simp [hcell]

/-- When every pair is genuinely bipartite, the kernel product is exactly
the list product of the decoded physical cell weights. -/
theorem orientedEdgeListWeight_bipartiteCellKernel_eq_cellListProd
    {A B : Type*} (q : A → B → ℝ≥0∞)
    (edges : List ((A ⊕ B) × (A ⊕ B)))
    (hdecode : ∀ edge ∈ edges,
      ∃ cell, orientedPairToCell edge = some cell) :
    orientedEdgeListWeight (bipartiteCellKernel q) edges =
      ((edges.filterMap orientedPairToCell).map
        fun cell => q cell.1 cell.2).prod := by
  induction edges with
  | nil => rfl
  | cons edge tail ih =>
      obtain ⟨cell, hcell⟩ := hdecode edge (by simp)
      have htail : ∀ e ∈ tail,
          ∃ c, orientedPairToCell e = some c := by
        intro e he
        exact hdecode e (by simp [he])
      simp only [orientedEdgeListWeight, List.map_cons, List.prod_cons]
      rw [bipartiteCellKernel_eq_of_orientedPairToCell_eq_some q hcell]
      have htailWeight := ih htail
      unfold orientedEdgeListWeight at htailWeight
      rw [htailWeight]
      simp [hcell]

/-- If every decoded transition cell belongs to `M`, its matching-kernel
weight is exactly one. -/
theorem orientedEdgeListWeight_matchingTraversalKernel_eq_one
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B))
    (edges : List ((A ⊕ B) × (A ⊕ B)))
    (hdecode : ∀ edge ∈ edges,
      ∃ cell, orientedPairToCell edge = some cell ∧ cell ∈ M) :
    orientedEdgeListWeight (matchingTraversalKernel M) edges = 1 := by
  induction edges with
  | nil => rfl
  | cons edge tail ih =>
      obtain ⟨cell, hcell, hmem⟩ := hdecode edge (by simp)
      have htail : ∀ e ∈ tail,
          ∃ c, orientedPairToCell e = some c ∧ c ∈ M := by
        intro e he
        exact hdecode e (by simp [he])
      simp only [orientedEdgeListWeight, List.map_cons, List.prod_cons]
      rw [matchingTraversalKernel_eq_one_of_orientedPairToCell_eq_some
        M hcell hmem]
      simpa [orientedEdgeListWeight] using ih htail

theorem kernelPathCode_weight_eq_orientedEdgeListWeight
    {V : Type*} (K : V → V → ℝ≥0∞)
    {ell : ℕ} {v w : V} (code : KernelPathCode V ell v w) :
    code.weight K = orientedEdgeListWeight K (kernelPathOrientedEdges code) := by
  induction ell generalizing v with
  | zero => rfl
  | succ ell ih =>
      simp [KernelPathCode.weight, kernelPathOrientedEdges,
        orientedEdgeListWeight, ih code.2]

theorem positiveKernelPathCode_weight_eq_orientedEdgeListWeight
    {V : Type*} (K : V → V → ℝ≥0∞)
    {L : ℕ} {v w : V} (code : PositiveKernelPathCode V L v w) :
    code.weight K = orientedEdgeListWeight K (positivePathOrientedEdges code) :=
  kernelPathCode_weight_eq_orientedEdgeListWeight K code.2

/-- Exact factorization of a relaxed block-chain weight into its residual and
transition oriented-edge lists.  This is valid for arbitrary nonnegative
kernels `K` and `P`; no probabilistic estimate or injectivity hypothesis is
used. -/
theorem relaxedBlockChainCode_weight_eq_projection_weights
    {V : Type*} (K P : V → V → ℝ≥0∞)
    {L r : ℕ} {v w : V}
    (code : RelaxedBlockChainCode V L r v w) :
    code.weight K P =
      orientedEdgeListWeight K (relaxedBlockResidualEdges code) *
        orientedEdgeListWeight P (relaxedBlockTransitionEdges code) := by
  induction r generalizing v with
  | zero =>
      simp [relaxedBlockResidualEdges, relaxedBlockTransitionEdges,
        orientedEdgeListWeight]
  | succ r ih =>
      rw [RelaxedBlockChainCode.weight_succ]
      rw [PositiveKernelThenTransitionCode.weight_mk]
      rw [positiveKernelPathCode_weight_eq_orientedEdgeListWeight]
      rw [ih code.2.2]
      simp only [relaxedBlockResidualEdges, relaxedBlockTransitionEdges,
        orientedEdgeListWeight, List.map_append, List.prod_append,
        List.map_cons, List.prod_cons]
      ac_rfl

/-- Specialization of the preceding identity to arbitrary nonnegative
bipartite cell weights and the matching traversal kernel. -/
theorem relaxedBlockChainCode_bipartite_weight_eq_projection_weights
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (q : A → B → ℝ≥0∞) (M : Finset (A × B))
    {L r : ℕ} {v w : A ⊕ B}
    (code : RelaxedBlockChainCode (A ⊕ B) L r v w) :
    code.weight (bipartiteCellKernel q) (matchingTraversalKernel M) =
      orientedEdgeListWeight (bipartiteCellKernel q)
          (relaxedBlockResidualEdges code) *
        orientedEdgeListWeight (matchingTraversalKernel M)
          (relaxedBlockTransitionEdges code) :=
  relaxedBlockChainCode_weight_eq_projection_weights _ _ code

/-! ## A block-count cutoff available before the physical cut -/

/-- A bipartite matching has at most as many edges as left vertices. -/
theorem bipartiteMatching_card_le_left
    {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M) :
    M.card ≤ Fintype.card A := by
  calc
    M.card = (M.image Prod.fst).card := by
      symm
      rw [Finset.card_image_iff.mpr]
      intro x hx y hy hxy
      exact Prod.ext hxy (hM.1 x.1 x.2 y.2 hx (by simpa [hxy] using hy))
    _ ≤ (Finset.univ : Finset A).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card A := Finset.card_univ

/-- Hence the number of matching edges met by any cycle is bounded by the
ambient vertex count.  This is the block-count cutoff; it is separate from
the per-residual-path cutoff carried by `PositiveKernelPathCode`. -/
theorem cycle_inter_matching_card_le_vertex_count
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (C M : Finset (A × B)) (hM : IsBipartiteMatching M) :
    (C ∩ M).card ≤ Fintype.card (A ⊕ B) := by
  calc
    (C ∩ M).card ≤ M.card :=
      Finset.card_le_card (Finset.inter_subset_right)
    _ ≤ Fintype.card A := bipartiteMatching_card_le_left M hM
    _ ≤ Fintype.card (A ⊕ B) := by
      simp only [Fintype.card_sum]
      exact Nat.le_add_right _ _

/-! ## The exact source-free target of the physical cutting lemma -/

/-- A closed relaxed block-chain code with a positive block count and the
manuscript path cutoff.  This type is source-free: it has no cycle field and
no reconstruction or injectivity certificate. -/
abbrev SourceFreeCycleCutCode
    (A B : Type*) [Fintype A] [Fintype B] :=
  Σ r : {r : ℕ // 0 < r},
    Σ v : A ⊕ B,
      RelaxedBlockChainCode (A ⊕ B)
        (Fintype.card (A ⊕ B)) r.1 v v

namespace SourceFreeCycleCutCode

/-- Number of positive residual blocks, hence also number of matching
transitions. -/
def blockCount
    {A B : Type*} [Fintype A] [Fintype B]
    (code : SourceFreeCycleCutCode A B) : ℕ :=
  code.1.1

/-- Marked oriented start vertex. -/
def start
    {A B : Type*} [Fintype A] [Fintype B]
    (code : SourceFreeCycleCutCode A B) : A ⊕ B :=
  code.2.1

/-- Underlying closed relaxed chain. -/
def chain
    {A B : Type*} [Fintype A] [Fintype B]
    (code : SourceFreeCycleCutCode A B) :
    RelaxedBlockChainCode (A ⊕ B)
      (Fintype.card (A ⊕ B)) code.blockCount code.start code.start :=
  code.2.2

theorem blockCount_pos
    {A B : Type*} [Fintype A] [Fintype B]
    (code : SourceFreeCycleCutCode A B) :
    0 < code.blockCount :=
  code.1.2

@[simp]
theorem transitionEdges_length
    {A B : Type*} [Fintype A] [Fintype B]
    (code : SourceFreeCycleCutCode A B) :
    (relaxedBlockTransitionEdges code.chain).length = code.blockCount :=
  relaxedBlockTransitionEdges_length code.chain

theorem pathLength_mem_bounds
    {A B : Type*} [Fintype A] [Fintype B]
    (code : SourceFreeCycleCutCode A B) :
    ∀ ell ∈ relaxedBlockPathLengths code.chain,
      0 < ell ∧ ell ≤ Fintype.card (A ⊕ B) :=
  relaxedBlockPathLengths_mem_bounds code.chain

theorem closed
    {A B : Type*} [Fintype A] [Fintype B]
    (code : SourceFreeCycleCutCode A B) :
    OrientedEdgeList.Joins code.start
      (relaxedBlockOrientedEdges code.chain) code.start :=
  relaxedBlockOrientedEdges_closed code.chain

end SourceFreeCycleCutCode

/-- The oriented marked matching edge that closes a cut traversal.  Its
second endpoint is exactly `orientedMatchingStartState z`: after the closing
transition the cyclic code is back at its marked start. -/
def orientedMatchingClosingEdge
    {A B : Type*} : ((A × B) × Bool) → (A ⊕ B) × (A ⊕ B)
  | ((a, b), true) => (Sum.inr b, Sum.inl a)
  | ((a, b), false) => (Sum.inl a, Sum.inr b)

@[simp]
theorem orientedMatchingClosingEdge_snd
    {A B : Type*} (z : (A × B) × Bool) :
    (orientedMatchingClosingEdge z).2 = orientedMatchingStartState z := by
  rcases z with ⟨⟨a, b⟩, orientation⟩
  cases orientation <;> rfl

/-- The faithful-cut relation is external to the source-free code type.
It states exactly what the still-missing construction from the covering cycle
walk must establish.  In particular, none of these equalities or nodup proofs
is stored in `SourceFreeCycleCutCode`. -/
structure IsFaithfulCycleCut
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (C M : Finset (A × B)) (code : SourceFreeCycleCutCode A B) : Prop where
  blockCount_eq : code.blockCount = (C ∩ M).card
  markedStart :
    ∃ z ∈ orientedMatchingStarts (C ∩ M),
      code.start = orientedMatchingStartState z ∧
        (relaxedBlockTransitionEdges code.chain).getLast? =
          some (orientedMatchingClosingEdge z)
  residualCells_eq : decodeRelaxedResidualCells code.chain = C \ M
  transitionCells_eq : decodeRelaxedTransitionCells code.chain = C ∩ M
  orientedEdges_nodup : (relaxedBlockOrientedEdges code.chain).Nodup
  residualEdges_decode :
    ∀ edge ∈ relaxedBlockResidualEdges code.chain,
      ∃ cell, orientedPairToCell edge = some cell
  transitionEdges_decode :
    ∀ edge ∈ relaxedBlockTransitionEdges code.chain,
      ∃ cell, orientedPairToCell edge = some cell
  residualCellList_nodup :
    ((relaxedBlockResidualEdges code.chain).filterMap
      orientedPairToCell).Nodup
  transitionCellList_nodup :
    ((relaxedBlockTransitionEdges code.chain).filterMap
      orientedPairToCell).Nodup

namespace IsFaithfulCycleCut

/-- Reconstruction is derived from the two projections; it is not a field of
the source-free target code. -/
theorem decode_eq
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {C M : Finset (A × B)} {code : SourceFreeCycleCutCode A B}
    (hcut : IsFaithfulCycleCut C M code) :
    decodeRelaxedBlockCells code.chain = C := by
  rw [decodeRelaxedBlockCells_eq_union,
    hcut.residualCells_eq, hcut.transitionCells_eq]
  ext edge
  simp
  tauto

/-- Exactly `|(C ∩ M)|` transitions are retained. -/
theorem transitionEdges_length_eq_inter_card
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {C M : Finset (A × B)} {code : SourceFreeCycleCutCode A B}
    (hcut : IsFaithfulCycleCut C M code) :
    (relaxedBlockTransitionEdges code.chain).length = (C ∩ M).card := by
  rw [SourceFreeCycleCutCode.transitionEdges_length, hcut.blockCount_eq]

/-- The decoded transition list also has exactly `|(C ∩ M)|` entries, so a
faithful cut neither drops a same-side transition nor merges two physical
matching edges. -/
theorem transitionCellList_length_eq_inter_card
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {C M : Finset (A × B)} {code : SourceFreeCycleCutCode A B}
    (hcut : IsFaithfulCycleCut C M code) :
    ((relaxedBlockTransitionEdges code.chain).filterMap
      orientedPairToCell).length = (C ∩ M).card := by
  calc
    ((relaxedBlockTransitionEdges code.chain).filterMap
        orientedPairToCell).length =
        (((relaxedBlockTransitionEdges code.chain).filterMap
          orientedPairToCell).toFinset).card :=
      (List.toFinset_card_of_nodup hcut.transitionCellList_nodup).symm
    _ = (decodeRelaxedTransitionCells code.chain).card := rfl
    _ = (C ∩ M).card := congrArg Finset.card hcut.transitionCells_eq

/-- No residual oriented edge is silently discarded by the cell decoder. -/
theorem residualCellList_length_eq_raw_length
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {C M : Finset (A × B)} {code : SourceFreeCycleCutCode A B}
    (hcut : IsFaithfulCycleCut C M code) :
    ((relaxedBlockResidualEdges code.chain).filterMap
      orientedPairToCell).length =
        (relaxedBlockResidualEdges code.chain).length :=
  filterMap_length_eq_length_of_forall_eq_some _ _
    hcut.residualEdges_decode

/-- The uniform transition decoder condition similarly rules out dropped
matching transitions. -/
theorem transitionCellList_length_eq_raw_length
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {C M : Finset (A × B)} {code : SourceFreeCycleCutCode A B}
    (hcut : IsFaithfulCycleCut C M code) :
    ((relaxedBlockTransitionEdges code.chain).filterMap
      orientedPairToCell).length =
        (relaxedBlockTransitionEdges code.chain).length :=
  filterMap_length_eq_length_of_forall_eq_some _ _
    hcut.transitionEdges_decode

/-- Consequently the raw residual list has exactly one oriented edge for
each physical cell of `C \ M`; no weight factor can disappear through
`filterMap`. -/
theorem residualEdges_length_eq_sdiff_card
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {C M : Finset (A × B)} {code : SourceFreeCycleCutCode A B}
    (hcut : IsFaithfulCycleCut C M code) :
    (relaxedBlockResidualEdges code.chain).length = (C \ M).card := by
  calc
    (relaxedBlockResidualEdges code.chain).length =
        ((relaxedBlockResidualEdges code.chain).filterMap
          orientedPairToCell).length :=
      hcut.residualCellList_length_eq_raw_length.symm
    _ = (((relaxedBlockResidualEdges code.chain).filterMap
          orientedPairToCell).toFinset).card :=
      (List.toFinset_card_of_nodup hcut.residualCellList_nodup).symm
    _ = (decodeRelaxedResidualCells code.chain).card := rfl
    _ = (C \ M).card := congrArg Finset.card hcut.residualCells_eq

/-- The residual kernel weight is exactly the product over the physical
decoded cells `C \ M`.  The no-drop and nodup fields are both essential:
the former prevents missing factors, while the latter prevents repeated
factors from being collapsed by `toFinset`. -/
theorem residualWeight_eq_sdiff_prod
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {C M : Finset (A × B)} {code : SourceFreeCycleCutCode A B}
    (hcut : IsFaithfulCycleCut C M code) (q : A → B → ℝ≥0∞) :
    orientedEdgeListWeight (bipartiteCellKernel q)
        (relaxedBlockResidualEdges code.chain) =
      (C \ M).prod (fun cell => q cell.1 cell.2) := by
  calc
    orientedEdgeListWeight (bipartiteCellKernel q)
        (relaxedBlockResidualEdges code.chain) =
        (((relaxedBlockResidualEdges code.chain).filterMap
          orientedPairToCell).map
            fun cell => q cell.1 cell.2).prod :=
      orientedEdgeListWeight_bipartiteCellKernel_eq_cellListProd
        q _ hcut.residualEdges_decode
    _ = (((relaxedBlockResidualEdges code.chain).filterMap
          orientedPairToCell).toFinset).prod
            (fun cell => q cell.1 cell.2) :=
      (List.prod_toFinset _ hcut.residualCellList_nodup).symm
    _ = (decodeRelaxedResidualCells code.chain).prod
          (fun cell => q cell.1 cell.2) := rfl
    _ = (C \ M).prod (fun cell => q cell.1 cell.2) := by
      rw [hcut.residualCells_eq]

/-- Every faithful transition is a decoded cell of `C ∩ M`, hence belongs
to `M` and has matching-traversal weight one. -/
theorem transitionWeight_eq_one
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {C M : Finset (A × B)} {code : SourceFreeCycleCutCode A B}
    (hcut : IsFaithfulCycleCut C M code) :
    orientedEdgeListWeight (matchingTraversalKernel M)
      (relaxedBlockTransitionEdges code.chain) = 1 := by
  apply orientedEdgeListWeight_matchingTraversalKernel_eq_one M
  intro edge hedge
  obtain ⟨cell, hdecode⟩ := hcut.transitionEdges_decode edge hedge
  refine ⟨cell, hdecode, ?_⟩
  have hcell : cell ∈ decodeRelaxedTransitionCells code.chain := by
    simp only [decodeRelaxedTransitionCells, decodeOrientedCells,
      List.mem_toFinset]
    exact List.mem_filterMap.mpr ⟨edge, hedge, hdecode⟩
  rw [hcut.transitionCells_eq] at hcell
  exact (Finset.mem_inter.mp hcell).2

/-- Exact physical-weight specialization for a faithful cut.  Since
`ℝ≥0∞` is nonnegative, this covers every generic nonnegative cell weight `q`.
The block-chain weight contains precisely the factors from `C \ M`; all
matching transitions contribute one. -/
theorem codeWeight_eq_sdiff_prod
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {C M : Finset (A × B)} {code : SourceFreeCycleCutCode A B}
    (hcut : IsFaithfulCycleCut C M code) (q : A → B → ℝ≥0∞) :
    code.chain.weight (bipartiteCellKernel q) (matchingTraversalKernel M) =
      (C \ M).prod (fun cell => q cell.1 cell.2) := by
  rw [relaxedBlockChainCode_weight_eq_projection_weights,
    hcut.residualWeight_eq_sdiff_prod q,
    hcut.transitionWeight_eq_one, mul_one]

/-- Raw residual and transition oriented-edge lists inherit nodup from the
full physical traversal. -/
theorem projection_orientedEdges_nodup
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {C M : Finset (A × B)} {code : SourceFreeCycleCutCode A B}
    (hcut : IsFaithfulCycleCut C M code) :
    (relaxedBlockResidualEdges code.chain).Nodup ∧
      (relaxedBlockTransitionEdges code.chain).Nodup :=
  relaxedBlock_projection_nodup code.chain hcut.orientedEdges_nodup

/-- The block-count cutoff is a consequence of faithfulness and the matching
property, whereas the path cutoff comes from the code type itself. -/
theorem blockCount_le_vertex_count
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {C M : Finset (A × B)} {code : SourceFreeCycleCutCode A B}
    (hM : IsBipartiteMatching M)
    (hcut : IsFaithfulCycleCut C M code) :
    code.blockCount ≤ Fintype.card (A ⊕ B) := by
  rw [hcut.blockCount_eq]
  exact cycle_inter_matching_card_le_vertex_count C M hM

end IsFaithfulCycleCut

/-- Existence of a faithful source-free code for one physical cycle. -/
def HasFaithfulCycleCut
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (C M : Finset (A × B)) : Prop :=
  ∃ code : SourceFreeCycleCutCode A B, IsFaithfulCycleCut C M code

/-- Exact remaining physical combinatorial obligation.  Proving this
proposition requires rotating the covering simple cycle walk to a marked edge
of `C ∩ M` and splitting its edge list at every matching edge.  It is a
definition, not an axiom or a theorem claimed by this module. -/
def PhysicalCycleCuttingStatement
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) : Prop :=
  IsBipartiteMatching M →
    ∀ C : Finset (A × B),
      IsSimpleBipartiteCycle C → (C ∩ M).Nonempty →
        HasFaithfulCycleCut C M

#print axioms relaxedBlockOrientedEdges_closed
#print axioms relaxedBlock_projection_nodup
#print axioms relaxedBlockChainCode_weight_eq_projection_weights
#print axioms cycle_inter_matching_card_le_vertex_count
#print axioms IsFaithfulCycleCut.decode_eq
#print axioms IsFaithfulCycleCut.blockCount_le_vertex_count
#print axioms IsFaithfulCycleCut.residualEdges_length_eq_sdiff_card
#print axioms IsFaithfulCycleCut.codeWeight_eq_sdiff_prod

end

end Erdos625
