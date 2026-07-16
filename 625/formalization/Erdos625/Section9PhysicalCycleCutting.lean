import Erdos625.Section9CycleWalkCutAtMatching
import Erdos625.Section9MinimalEvenCycleTour

/-!
# Section 9: constructing the physical cycle cut

This module begins the remaining physical construction behind
`PhysicalCycleCuttingStatement`.  Its first layer is fully constructive: an
oriented residual run is converted to the existing recursive kernel-path
code, and a joined list of positive residual runs separated by oriented
matching edges is assembled into the existing source-free relaxed block-chain
code.  No source cycle or reconstruction certificate is added to that code.

The subsequent obligation is to rotate the covering simple-cycle walk at a
chosen edge of `C ∩ M` and produce the joined block list consumed below.
-/

namespace Erdos625

noncomputable section

/-! ## The oriented edge traversal carried by a graph walk -/

/-- Forget adjacency proofs in the dart list while retaining the orientation
and order of every traversed edge. -/
def walkOrientedEdges
    {V : Type*} {G : SimpleGraph V} {v w : V}
    (p : G.Walk v w) : List (V × V) :=
  p.darts.map fun dart => (dart.fst, dart.snd)

@[simp]
theorem walkOrientedEdges_length
    {V : Type*} {G : SimpleGraph V} {v w : V}
    (p : G.Walk v w) :
    (walkOrientedEdges p).length = p.length := by
  simp [walkOrientedEdges, p.length_darts]

theorem walkOrientedEdges_joins
    {V : Type*} {G : SimpleGraph V} {v w : V}
    (p : G.Walk v w) :
    OrientedEdgeList.Joins v (walkOrientedEdges p) w := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      simp only [walkOrientedEdges, SimpleGraph.Walk.darts_cons,
        List.map_cons]
      exact ⟨rfl, ih⟩

/-- Forgetting orientation recovers Mathlib's edge list exactly. -/
theorem walkOrientedEdges_map_sym2
    {V : Type*} {G : SimpleGraph V} {v w : V}
    (p : G.Walk v w) :
    (walkOrientedEdges p).map (fun edge => s(edge.1, edge.2)) =
      p.edges := by
  simp [walkOrientedEdges, SimpleGraph.Walk.edges, List.map_map,
    SimpleGraph.Dart.edge]

/-- A cycle's oriented traversal has no repeated oriented edge. -/
theorem walkOrientedEdges_nodup_of_isCycle
    {V : Type*} {G : SimpleGraph V} {v : V}
    {p : G.Walk v v} (hp : p.IsCycle) :
    (walkOrientedEdges p).Nodup := by
  apply List.Nodup.of_map (fun edge => s(edge.1, edge.2))
  rw [walkOrientedEdges_map_sym2]
  exact hp.edges_nodup

/-- Every oriented edge of a `cellGraph C` walk decodes to a genuine cell of
`C`; same-side pairs cannot occur. -/
theorem walkOrientedEdge_decodes_mem
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {C : Finset (A × B)} {v w : A ⊕ B}
    (p : (cellGraph C).Walk v w)
    {edge : (A ⊕ B) × (A ⊕ B)}
    (hedge : edge ∈ walkOrientedEdges p) :
    ∃ cell ∈ C, orientedPairToCell edge = some cell := by
  unfold walkOrientedEdges at hedge
  obtain ⟨dart, hdart, rfl⟩ := List.mem_map.mp hedge
  rcases dart with ⟨⟨u, x⟩, hadj⟩
  rcases u with a | b <;> rcases x with a' | b' <;>
    simp [cellGraph, orientedPairToCell] at hadj ⊢
  all_goals exact hadj

theorem cellSym2_injective {A B : Type*} :
    Function.Injective (@cellSym2 A B) := by
  intro left right
  rcases left with ⟨a, b⟩
  rcases right with ⟨a', b'⟩
  simp [cellSym2]

theorem cellSym2_eq_sym2_of_orientedPairToCell_eq_some
    {A B : Type*} {edge : (A ⊕ B) × (A ⊕ B)} {cell : A × B}
    (hdecode : orientedPairToCell edge = some cell) :
    cellSym2 cell = s(edge.1, edge.2) := by
  rcases edge with ⟨u, x⟩
  rcases u with a | b <;> rcases x with a' | b' <;>
    simp [orientedPairToCell, cellSym2] at hdecode ⊢
  all_goals subst cell
  all_goals exact ⟨rfl, rfl⟩

/-- The decoded list of any `cellGraph C` walk is contained in `C`. -/
theorem decodeOrientedCells_walkOrientedEdges_subset
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {C : Finset (A × B)} {v w : A ⊕ B}
    (p : (cellGraph C).Walk v w) :
    decodeOrientedCells (walkOrientedEdges p) ⊆ C := by
  intro cell hcell
  simp only [decodeOrientedCells, List.mem_toFinset] at hcell
  obtain ⟨edge, hedge, hdecode⟩ := List.mem_filterMap.mp hcell
  obtain ⟨sourceCell, hsourceCell, hsourceDecode⟩ :=
    walkOrientedEdge_decodes_mem p hedge
  have : sourceCell = cell := by
    exact Option.some.inj (hsourceDecode.symm.trans hdecode)
  simpa [this] using hsourceCell

/-- When the walk covers exactly `C`, its source-free decoder recovers `C`.
-/
theorem decodeOrientedCells_walkOrientedEdges_eq_of_cover
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {C : Finset (A × B)} {v w : A ⊕ B}
    (p : (cellGraph C).Walk v w)
    (hcover : p.edges.toFinset = C.image cellSym2) :
    decodeOrientedCells (walkOrientedEdges p) = C := by
  apply Finset.Subset.antisymm
  · exact decodeOrientedCells_walkOrientedEdges_subset p
  · intro cell hcell
    have hedgeSym : cellSym2 cell ∈ p.edges := by
      rw [← List.mem_toFinset, hcover]
      exact Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
    rw [← walkOrientedEdges_map_sym2] at hedgeSym
    obtain ⟨edge, hedge, hsym⟩ := List.mem_map.mp hedgeSym
    obtain ⟨sourceCell, hsourceCell, hdecode⟩ :=
      walkOrientedEdge_decodes_mem p hedge
    have hsourceSym : cellSym2 sourceCell = cellSym2 cell := by
      rw [cellSym2_eq_sym2_of_orientedPairToCell_eq_some hdecode, hsym]
    have hsource : sourceCell = cell := cellSym2_injective hsourceSym
    subst sourceCell
    simp only [decodeOrientedCells, List.mem_toFinset]
    exact List.mem_filterMap.mpr ⟨edge, hedge, hdecode⟩

/-- Every covered physical cell has an oriented representative in the walk.
-/
theorem exists_walkOrientedEdge_of_mem_of_cover
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {C : Finset (A × B)} {v w : A ⊕ B}
    (p : (cellGraph C).Walk v w)
    (hcover : p.edges.toFinset = C.image cellSym2)
    {cell : A × B} (hcell : cell ∈ C) :
    ∃ edge ∈ walkOrientedEdges p,
      orientedPairToCell edge = some cell := by
  have hedgeSym : cellSym2 cell ∈ p.edges := by
    rw [← List.mem_toFinset, hcover]
    exact Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
  rw [← walkOrientedEdges_map_sym2] at hedgeSym
  obtain ⟨edge, hedge, hsym⟩ := List.mem_map.mp hedgeSym
  obtain ⟨sourceCell, _, hdecode⟩ :=
    walkOrientedEdge_decodes_mem p hedge
  have hsourceSym : cellSym2 sourceCell = cellSym2 cell := by
    rw [cellSym2_eq_sym2_of_orientedPairToCell_eq_some hdecode, hsym]
  have hsource : sourceCell = cell := cellSym2_injective hsourceSym
  subst sourceCell
  exact ⟨edge, hedge, hdecode⟩

/-- If every oriented pair decodes, mapping the decoded cells back to
undirected edges recovers the orientation-forgetting map exactly. -/
theorem map_cellSym2_filterMap_orientedPairToCell
    {A B : Type*} (edges : List ((A ⊕ B) × (A ⊕ B)))
    (hdecode : ∀ edge ∈ edges,
      ∃ cell, orientedPairToCell edge = some cell) :
    (edges.filterMap orientedPairToCell).map cellSym2 =
      edges.map (fun edge => s(edge.1, edge.2)) := by
  induction edges with
  | nil => rfl
  | cons edge tail ih =>
      obtain ⟨cell, hcell⟩ := hdecode edge (by simp)
      have htail : ∀ e ∈ tail,
          ∃ c, orientedPairToCell e = some c := by
        intro e he
        exact hdecode e (by simp [he])
      simp [hcell, ih htail,
        cellSym2_eq_sym2_of_orientedPairToCell_eq_some hcell]

/-- A covering simple-cycle walk decodes to a noduplicated physical cell
list. -/
theorem filterMap_orientedPairToCell_walkOrientedEdges_nodup
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {C : Finset (A × B)} {v : A ⊕ B}
    {p : (cellGraph C).Walk v v} (hp : p.IsCycle) :
    ((walkOrientedEdges p).filterMap orientedPairToCell).Nodup := by
  apply List.Nodup.of_map cellSym2
  rw [map_cellSym2_filterMap_orientedPairToCell]
  · rw [walkOrientedEdges_map_sym2]
    exact hp.edges_nodup
  · intro edge hedge
    obtain ⟨cell, _, hdecode⟩ := walkOrientedEdge_decodes_mem p hedge
    exact ⟨cell, hdecode⟩

theorem decodeOrientedCells_eq_of_perm
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {left right : List ((A ⊕ B) × (A ⊕ B))}
    (hperm : left.Perm right) :
    decodeOrientedCells left = decodeOrientedCells right := by
  unfold decodeOrientedCells
  apply List.toFinset_eq_of_perm
  rw [List.filterMap_eq_flatMap_toList, List.filterMap_eq_flatMap_toList]
  exact hperm.flatMap (fun _ _ => .refl _)

/-- Decoded-cell nodup is preserved by any permutation of a covering cycle's
oriented traversal. -/
theorem filterMap_orientedPairToCell_nodup_of_perm_walkOrientedEdges
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {C : Finset (A × B)} {v : A ⊕ B}
    {p : (cellGraph C).Walk v v} (hp : p.IsCycle)
    {edges : List ((A ⊕ B) × (A ⊕ B))}
    (hperm : (walkOrientedEdges p).Perm edges) :
    (edges.filterMap orientedPairToCell).Nodup := by
  apply List.Nodup.of_map cellSym2
  rw [map_cellSym2_filterMap_orientedPairToCell]
  · have hmapPerm := hperm.map (fun edge => s(edge.1, edge.2))
    apply hmapPerm.nodup_iff.mp
    rw [walkOrientedEdges_map_sym2]
    exact hp.edges_nodup
  · intro edge hedge
    have hedgeWalk : edge ∈ walkOrientedEdges p :=
      hperm.mem_iff.mpr hedge
    obtain ⟨cell, _, hdecode⟩ :=
      walkOrientedEdge_decodes_mem p hedgeWalk
    exact ⟨cell, hdecode⟩

/-- An oriented pair is a separator when it decodes to a cell of `M`. -/
def isMatchingTransition
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B))
    (edge : (A ⊕ B) × (A ⊕ B)) : Bool :=
  match orientedPairToCell edge with
  | some cell => decide (cell ∈ M)
  | none => false

theorem isMatchingTransition_eq_true_iff
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B))
    (edge : (A ⊕ B) × (A ⊕ B)) :
    isMatchingTransition M edge = true ↔
      ∃ cell ∈ M, orientedPairToCell edge = some cell := by
  rcases edge with ⟨u, x⟩
  rcases u with a | b <;> rcases x with a' | b' <;>
    simp [isMatchingTransition, orientedPairToCell]

/-- Filtering by matching transitions decodes exactly the intersection with
`M`. -/
theorem decodeOrientedCells_filter_isMatchingTransition
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B))
    (edges : List ((A ⊕ B) × (A ⊕ B))) :
    decodeOrientedCells
        (edges.filter (isMatchingTransition M)) =
      decodeOrientedCells edges ∩ M := by
  classical
  ext cell
  constructor
  · intro hcell
    simp only [decodeOrientedCells, List.mem_toFinset] at hcell
    obtain ⟨edge, hedgeFiltered, hdecode⟩ :=
      List.mem_filterMap.mp hcell
    have hedge : edge ∈ edges := List.mem_of_mem_filter hedgeFiltered
    obtain ⟨sourceCell, hsourceMem, hsourceDecode⟩ :=
      (isMatchingTransition_eq_true_iff M edge).mp
        (List.of_mem_filter hedgeFiltered)
    have hsource : sourceCell = cell :=
      Option.some.inj (hsourceDecode.symm.trans hdecode)
    subst sourceCell
    exact Finset.mem_inter.mpr
      ⟨by
        simp only [decodeOrientedCells, List.mem_toFinset]
        exact List.mem_filterMap.mpr ⟨edge, hedge, hdecode⟩,
       hsourceMem⟩
  · intro hcell
    obtain ⟨hdecoded, hmem⟩ := Finset.mem_inter.mp hcell
    simp only [decodeOrientedCells, List.mem_toFinset] at hdecoded ⊢
    obtain ⟨edge, hedge, hdecode⟩ := List.mem_filterMap.mp hdecoded
    refine List.mem_filterMap.mpr ⟨edge, ?_, hdecode⟩
    exact List.mem_filter_of_mem hedge
      ((isMatchingTransition_eq_true_iff M edge).mpr
        ⟨cell, hmem, hdecode⟩)

/-- Filtering by nontransitions decodes exactly the difference from `M`. -/
theorem decodeOrientedCells_filter_not_isMatchingTransition
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B))
    (edges : List ((A ⊕ B) × (A ⊕ B))) :
    decodeOrientedCells
        (edges.filter (fun edge => !(isMatchingTransition M edge))) =
      decodeOrientedCells edges \ M := by
  classical
  ext cell
  constructor
  · intro hcell
    simp only [decodeOrientedCells, List.mem_toFinset] at hcell
    obtain ⟨edge, hedgeFiltered, hdecode⟩ :=
      List.mem_filterMap.mp hcell
    have hedge : edge ∈ edges := List.mem_of_mem_filter hedgeFiltered
    have hnotSeparator : isMatchingTransition M edge = false := by
      simpa using List.of_mem_filter hedgeFiltered
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · simp only [decodeOrientedCells, List.mem_toFinset]
      exact List.mem_filterMap.mpr ⟨edge, hedge, hdecode⟩
    · intro hmem
      have htrue := (isMatchingTransition_eq_true_iff M edge).mpr
        ⟨cell, hmem, hdecode⟩
      exact Bool.false_ne_true (hnotSeparator.symm.trans htrue)
  · intro hcell
    obtain ⟨hdecoded, hnotMem⟩ := Finset.mem_sdiff.mp hcell
    simp only [decodeOrientedCells, List.mem_toFinset] at hdecoded ⊢
    obtain ⟨edge, hedge, hdecode⟩ := List.mem_filterMap.mp hdecoded
    refine List.mem_filterMap.mpr ⟨edge, ?_, hdecode⟩
    apply List.mem_filter_of_mem hedge
    have hfalse : isMatchingTransition M edge = false := by
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      obtain ⟨sourceCell, hsourceMem, hsourceDecode⟩ :=
        (isMatchingTransition_eq_true_iff M edge).mp htrue
      have hsource : sourceCell = cell :=
        Option.some.inj (hsourceDecode.symm.trans hdecode)
      exact hnotMem (hsource ▸ hsourceMem)
    simp [hfalse]

/-! ## Cutting and rotating a closed oriented edge list -/

namespace OrientedEdgeList

theorem joins_append_iff
    {V : Type*} {v w : V} {left right : List (V × V)} :
    Joins v (left ++ right) w ↔
      ∃ middle, Joins v left middle ∧ Joins middle right w := by
  constructor
  · intro hjoins
    induction left generalizing v with
    | nil =>
        exact ⟨v, rfl, hjoins⟩
    | cons edge tail ih =>
        rcases edge with ⟨x, y⟩
        simp only [List.cons_append, Joins] at hjoins
        obtain ⟨middle, htail, hright⟩ := ih hjoins.2
        exact ⟨middle, ⟨hjoins.1, htail⟩, hright⟩
  · rintro ⟨middle, hleft, hright⟩
    exact joins_append hleft hright

end OrientedEdgeList

/-- Rotate a closed oriented traversal immediately after any selected edge.
The selected oriented edge becomes the final closing edge, and the new start
is its second endpoint. -/
theorem exists_closed_rotation_ending_at
    {V : Type*} {start : V} {edges : List (V × V)}
    (hclosed : OrientedEdgeList.Joins start edges start)
    {closing : V × V} (hclosing : closing ∈ edges) :
    ∃ initial : List (V × V),
      edges.Perm (initial ++ [closing]) ∧
        OrientedEdgeList.Joins closing.2
          (initial ++ [closing]) closing.2 ∧
        (initial ++ [closing]).getLast? = some closing := by
  obtain ⟨before, after, hedges⟩ := List.mem_iff_append.mp hclosing
  rcases closing with ⟨u, x⟩
  rw [hedges] at hclosed
  obtain ⟨middle, hbefore, hrest⟩ :=
    OrientedEdgeList.joins_append_iff.mp hclosed
  simp only [OrientedEdgeList.Joins] at hrest
  rcases hrest with ⟨rfl, hafter⟩
  refine ⟨after ++ before, ?_, ?_, ?_⟩
  · rw [hedges]
    simpa [List.append_assoc] using
      (List.perm_append_comm :
        List.Perm ((before ++ [(u, x)]) ++ after)
          (after ++ (before ++ [(u, x)])))
  · rw [List.append_assoc]
    apply OrientedEdgeList.joins_append hafter
    apply OrientedEdgeList.joins_append hbefore
    exact ⟨rfl, rfl⟩
  · simp

/-! ## Reifying joined oriented edge lists as kernel path codes -/

/-- Every finite joined oriented edge list is represented by an actual
recursive `KernelPathCode`, with exactly the same oriented edges. -/
theorem exists_kernelPathCode_orientedEdges_eq
    {V : Type*} {v w : V} (edges : List (V × V))
    (hjoins : OrientedEdgeList.Joins v edges w) :
    ∃ code : KernelPathCode V edges.length v w,
      kernelPathOrientedEdges code = edges := by
  induction edges generalizing v with
  | nil =>
      simp only [OrientedEdgeList.Joins] at hjoins
      subst w
      exact ⟨⟨v, rfl, rfl⟩, rfl⟩
  | cons edge tail ih =>
      rcases edge with ⟨x, y⟩
      simp only [OrientedEdgeList.Joins] at hjoins
      rcases hjoins with ⟨rfl, hjoins⟩
      obtain ⟨tailCode, htailCode⟩ := ih hjoins
      refine ⟨⟨y, tailCode⟩, ?_⟩
      simp [kernelPathOrientedEdges, htailCode]

/-- Transport a path code across an equality of lengths. -/
def castKernelPathCode
    {V : Type*} {m n : ℕ} {v w : V} (h : m = n)
    (code : KernelPathCode V m v w) : KernelPathCode V n v w :=
  h ▸ code

@[simp]
theorem kernelPathOrientedEdges_castKernelPathCode
    {V : Type*} {m n : ℕ} {v w : V} (h : m = n)
    (code : KernelPathCode V m v w) :
    kernelPathOrientedEdges (castKernelPathCode h code) =
      kernelPathOrientedEdges code := by
  subst n
  rfl

/-- A nonempty joined run satisfying the independent path cutoff is
represented by an actual `PositiveKernelPathCode`. -/
theorem exists_positiveKernelPathCode_orientedEdges_eq
    {V : Type*} {L : ℕ} {v w : V} (edges : List (V × V))
    (hjoins : OrientedEdgeList.Joins v edges w)
    (hpositive : 0 < edges.length) (hcutoff : edges.length ≤ L) :
    ∃ code : PositiveKernelPathCode V L v w,
      positivePathOrientedEdges code = edges := by
  obtain ⟨fixedCode, hfixedCode⟩ :=
    exists_kernelPathCode_orientedEdges_eq edges hjoins
  obtain ⟨ell, hell⟩ := Nat.exists_eq_succ_of_ne_zero hpositive.ne'
  have hellL : ell < L := by omega
  let castCode : KernelPathCode V (ell + 1) v w :=
    castKernelPathCode hell fixedCode
  refine ⟨⟨⟨ell, hellL⟩, castCode⟩, ?_⟩
  change kernelPathOrientedEdges castCode = edges
  dsimp only [castCode]
  rw [kernelPathOrientedEdges_castKernelPathCode, hfixedCode]

/-! ## Joined lists of residual runs and transition edges -/

/-- One physical cut block consists of a residual run followed by its
oriented matching transition. -/
abbrev PhysicalCutBlock (V : Type*) := List (V × V) × (V × V)

namespace PhysicalCutBlockList

/-- The blocks join from `v` to `w`: each residual run reaches the first
endpoint of its transition, and the next block starts at the second endpoint.
-/
def Joins {V : Type*} :
    V → List (PhysicalCutBlock V) → V → Prop
  | v, [], w => v = w
  | v, (run, (u, x)) :: blocks, w =>
      OrientedEdgeList.Joins v run u ∧ Joins x blocks w

/-- Concatenation of all residual runs, retaining multiplicity and
orientation. -/
def residualEdges {V : Type*}
    (blocks : List (PhysicalCutBlock V)) : List (V × V) :=
  blocks.flatMap Prod.fst

/-- One transition edge per block. -/
def transitionEdges {V : Type*}
    (blocks : List (PhysicalCutBlock V)) : List (V × V) :=
  blocks.map Prod.snd

/-- Physical traversal order: each residual run followed by its transition.
-/
def orientedEdges {V : Type*}
    (blocks : List (PhysicalCutBlock V)) : List (V × V) :=
  blocks.flatMap fun block => block.1 ++ [block.2]

@[simp]
theorem transitionEdges_length {V : Type*}
    (blocks : List (PhysicalCutBlock V)) :
    (transitionEdges blocks).length = blocks.length := by
  simp [transitionEdges]

theorem joins_orientedEdges
    {V : Type*} {v w : V} {blocks : List (PhysicalCutBlock V)}
    (hjoins : Joins v blocks w) :
    OrientedEdgeList.Joins v (orientedEdges blocks) w := by
  induction blocks generalizing v with
  | nil =>
      simpa [Joins, orientedEdges] using hjoins
  | cons block blocks ih =>
      rcases block with ⟨run, ⟨u, x⟩⟩
      simp only [Joins] at hjoins
      simp only [orientedEdges, List.flatMap_cons]
      rw [List.append_assoc]
      apply OrientedEdgeList.joins_append hjoins.1
      exact ⟨rfl, ih hjoins.2⟩

theorem joins_of_orientedEdges
    {V : Type*} {v w : V} {blocks : List (PhysicalCutBlock V)}
    (hjoins : OrientedEdgeList.Joins v (orientedEdges blocks) w) :
    Joins v blocks w := by
  induction blocks generalizing v with
  | nil =>
      simpa [Joins, orientedEdges] using hjoins
  | cons block blocks ih =>
      rcases block with ⟨run, ⟨u, x⟩⟩
      simp only [orientedEdges, List.flatMap_cons] at hjoins
      obtain ⟨middle, hfirst, htail⟩ :=
        OrientedEdgeList.joins_append_iff.mp hjoins
      obtain ⟨preTransition, hrun, htransition⟩ :=
        OrientedEdgeList.joins_append_iff.mp hfirst
      simp only [OrientedEdgeList.Joins] at htransition
      rcases htransition with ⟨rfl, rfl⟩
      exact ⟨hrun, ih htail⟩

theorem decode_orientedEdges_eq_union
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (blocks : List (PhysicalCutBlock (A ⊕ B))) :
    decodeOrientedCells (orientedEdges blocks) =
      decodeOrientedCells (residualEdges blocks) ∪
        decodeOrientedCells (transitionEdges blocks) := by
  induction blocks with
  | nil =>
      simp [orientedEdges, residualEdges, transitionEdges,
        decodeOrientedCells]
  | cons block blocks ih =>
      rcases block with ⟨run, separator⟩
      have htail :
          decodeOrientedCells
              (List.flatMap (fun block => block.1 ++ [block.2]) blocks) =
            decodeOrientedCells (List.flatMap Prod.fst blocks) ∪
              decodeOrientedCells (List.map Prod.snd blocks) := by
        simpa only [orientedEdges, residualEdges, transitionEdges] using ih
      simp only [orientedEdges, residualEdges, transitionEdges,
        List.flatMap_cons, List.map_cons, decodeOrientedCells_append,
        decodeOrientedCells_cons_eq]
      rw [htail]
      ext cell
      simp only [Finset.mem_union]
      tauto

end PhysicalCutBlockList

/-! ## Deterministic linear splitting at separator edges -/

/-- Scan backward and attach every nonseparator edge to the next separator.
Any suffix after the final separator is intentionally omitted; the physical
application first rotates the cyclic traversal so that its marked separator
is the final edge, and the theorem below then proves that nothing is omitted.
-/
def cutAtSeparators {V : Type*} (isSeparator : V × V → Bool) :
    List (V × V) → List (PhysicalCutBlock V)
  | [] => []
  | edge :: tail =>
      if isSeparator edge = true then
        ([], edge) :: cutAtSeparators isSeparator tail
      else
        match cutAtSeparators isSeparator tail with
        | [] => []
        | (run, separator) :: blocks =>
            (edge :: run, separator) :: blocks

/-- The transition projection of the deterministic split is exactly the
separator subsequence, including multiplicity and order. -/
theorem transitionEdges_cutAtSeparators
    {V : Type*} (isSeparator : V × V → Bool)
    (edges : List (V × V)) :
    PhysicalCutBlockList.transitionEdges
        (cutAtSeparators isSeparator edges) =
      edges.filter isSeparator := by
  induction edges with
  | nil => rfl
  | cons edge tail ih =>
      rw [cutAtSeparators, List.filter_cons]
      by_cases hedge : isSeparator edge = true
      · simp only [hedge, ↓reduceIte,
          PhysicalCutBlockList.transitionEdges, List.map_cons]
        exact congrArg (List.cons edge) ih
      · simp only [hedge]
        generalize hblocks : cutAtSeparators isSeparator tail = blocks
        cases blocks with
        | nil =>
            have htail := ih
            rw [hblocks] at htail
            simpa [PhysicalCutBlockList.transitionEdges] using htail
        | cons block blocks =>
            rcases block with ⟨run, separator⟩
            have htail := ih
            rw [hblocks] at htail
            simpa [PhysicalCutBlockList.transitionEdges] using htail

@[simp]
theorem cutAtSeparators_length
    {V : Type*} (isSeparator : V × V → Bool)
    (edges : List (V × V)) :
    (cutAtSeparators isSeparator edges).length =
      (edges.filter isSeparator).length := by
  calc
    (cutAtSeparators isSeparator edges).length =
        (PhysicalCutBlockList.transitionEdges
          (cutAtSeparators isSeparator edges)).length :=
      (PhysicalCutBlockList.transitionEdges_length _).symm
    _ = (edges.filter isSeparator).length :=
      congrArg List.length
        (transitionEdges_cutAtSeparators isSeparator edges)

theorem separator_of_mem_cutAtSeparators
    {V : Type*} (isSeparator : V × V → Bool)
    {edges : List (V × V)}
    {block : PhysicalCutBlock V}
    (hblock : block ∈ cutAtSeparators isSeparator edges) :
    isSeparator block.2 = true := by
  have htransition :
      block.2 ∈ PhysicalCutBlockList.transitionEdges
        (cutAtSeparators isSeparator edges) := by
    simp only [PhysicalCutBlockList.transitionEdges, List.mem_map]
    exact ⟨block, hblock, rfl⟩
  rw [transitionEdges_cutAtSeparators] at htransition
  exact List.of_mem_filter htransition

/-- Every run edge lies outside the separator predicate. -/
theorem run_edge_not_separator_of_mem_cutAtSeparators
    {V : Type*} (isSeparator : V × V → Bool)
    (edges : List (V × V)) :
    ∀ block ∈ cutAtSeparators isSeparator edges,
      ∀ edge ∈ block.1, isSeparator edge ≠ true := by
  induction edges with
  | nil => simp [cutAtSeparators]
  | cons edge tail ih =>
      rw [cutAtSeparators]
      by_cases hedge : isSeparator edge = true
      · simpa [hedge] using ih
      · simp only [hedge]
        generalize hblocks : cutAtSeparators isSeparator tail = blocks
        have htail := ih
        rw [hblocks] at htail
        cases blocks with
        | nil => simp
        | cons first blocks =>
            rcases first with ⟨run, separator⟩
            intro block hblock runEdge hrunEdge
            rcases List.mem_cons.mp hblock with hblock | hblock
            · subst block
              simp only [List.mem_cons] at hrunEdge
              rcases hrunEdge with rfl | hrunEdge
              · exact hedge
              · exact htail (run, separator) (by simp) runEdge hrunEdge
            · exact htail block (by simp [hblock]) runEdge hrunEdge

theorem residual_edge_not_separator_cutAtSeparators
    {V : Type*} (isSeparator : V × V → Bool)
    {edges : List (V × V)}
    {edge : V × V}
    (hedge : edge ∈ PhysicalCutBlockList.residualEdges
      (cutAtSeparators isSeparator edges)) :
    isSeparator edge ≠ true := by
  unfold PhysicalCutBlockList.residualEdges at hedge
  obtain ⟨block, hblock, hedge⟩ := List.mem_flatMap.mp hedge
  exact run_edge_not_separator_of_mem_cutAtSeparators
    isSeparator edges block hblock edge hedge

/-- If a linearization ends at a separator, splitting loses no edge and
produces at least one block. -/
theorem cutAtSeparators_append_singleton
    {V : Type*} (isSeparator : V × V → Bool)
    (initial : List (V × V)) (closing : V × V)
    (hclosing : isSeparator closing = true) :
    cutAtSeparators isSeparator (initial ++ [closing]) ≠ [] ∧
      PhysicalCutBlockList.orientedEdges
          (cutAtSeparators isSeparator (initial ++ [closing])) =
        initial ++ [closing] := by
  induction initial with
  | nil =>
      simp [cutAtSeparators, hclosing,
        PhysicalCutBlockList.orientedEdges]
  | cons edge initial ih =>
      rw [List.cons_append, cutAtSeparators]
      by_cases hedge : isSeparator edge = true
      · simp only [hedge, ↓reduceIte,
          PhysicalCutBlockList.orientedEdges, List.flatMap_cons]
        exact ⟨by simp,
          congrArg (List.cons edge) ih.2⟩
      · simp only [hedge]
        generalize hblocks :
          cutAtSeparators isSeparator (initial ++ [closing]) = blocks at ih ⊢
        cases blocks with
        | nil => exact False.elim (ih.1 rfl)
        | cons block blocks =>
            rcases block with ⟨run, separator⟩
            constructor
            · simp
            · simp only [PhysicalCutBlockList.orientedEdges,
                List.flatMap_cons] at ih ⊢
              simpa [List.append_assoc] using congrArg (List.cons edge) ih.2

/-- When the closing edge is a separator, the residual projection is exactly
the nonseparator subsequence.  This list-level identity is stronger than the
decoded-set identity used below and will supply the no-drop and nodup fields of
the faithful cut. -/
theorem residualEdges_cutAtSeparators_append_singleton
    {V : Type*} (isSeparator : V × V → Bool)
    (initial : List (V × V)) (closing : V × V)
    (hclosing : isSeparator closing = true) :
    PhysicalCutBlockList.residualEdges
        (cutAtSeparators isSeparator (initial ++ [closing])) =
      (initial ++ [closing]).filter (fun edge => !(isSeparator edge)) := by
  induction initial with
  | nil =>
      simp [cutAtSeparators, hclosing,
        PhysicalCutBlockList.residualEdges]
  | cons edge initial ih =>
      rw [List.cons_append, cutAtSeparators, List.filter_cons]
      by_cases hedge : isSeparator edge = true
      · simp only [hedge, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          PhysicalCutBlockList.residualEdges, List.flatMap_cons,
          List.nil_append]
        simpa only [PhysicalCutBlockList.residualEdges,
          List.filter_append] using ih
      · simp only [hedge]
        generalize hblocks :
          cutAtSeparators isSeparator (initial ++ [closing]) = blocks at ih ⊢
        cases blocks with
        | nil =>
            have hnonempty :=
              (cutAtSeparators_append_singleton
                isSeparator initial closing hclosing).1
            exact False.elim (hnonempty hblocks)
        | cons block blocks =>
            rcases block with ⟨run, separator⟩
            simp only [PhysicalCutBlockList.residualEdges,
              List.flatMap_cons] at ih ⊢
            simpa [List.append_assoc] using congrArg (List.cons edge) ih

/-- The marked closing separator is the final transition of the split. -/
theorem transitionEdges_cutAtSeparators_append_singleton_getLast?
    {V : Type*} (isSeparator : V × V → Bool)
    (initial : List (V × V)) (closing : V × V)
    (hclosing : isSeparator closing = true) :
    (PhysicalCutBlockList.transitionEdges
      (cutAtSeparators isSeparator (initial ++ [closing]))).getLast? =
        some closing := by
  rw [transitionEdges_cutAtSeparators]
  simp [List.filter_append, hclosing]

/-- Every residual run produced by the splitter is a sublist of the input
traversal.  In particular its length is bounded by the traversal length. -/
theorem run_sublist_of_mem_cutAtSeparators
    {V : Type*} (isSeparator : V × V → Bool)
    (edges : List (V × V)) :
    ∀ block ∈ cutAtSeparators isSeparator edges,
      block.1.Sublist edges := by
  induction edges with
  | nil => simp [cutAtSeparators]
  | cons edge tail ih =>
      rw [cutAtSeparators]
      by_cases hedge : isSeparator edge = true
      · simp only [hedge, ↓reduceIte]
        intro block hblock
        rcases List.mem_cons.mp hblock with hblock | hblock
        · subst block
          exact List.nil_sublist (edge :: tail)
        · exact (ih block hblock).cons edge
      · simp only [hedge]
        generalize hblocks : cutAtSeparators isSeparator tail = blocks
        have htail := ih
        rw [hblocks] at htail
        cases blocks with
        | nil => simp
        | cons first blocks =>
            rcases first with ⟨run, separator⟩
            intro block hblock
            rcases List.mem_cons.mp hblock with hblock | hblock
            · subst block
              exact (htail (run, separator) (by simp)).cons_cons edge
            · exact (htail block (by simp [hblock])).cons edge

theorem run_length_le_of_mem_cutAtSeparators
    {V : Type*} (isSeparator : V × V → Bool)
    (edges : List (V × V))
    {block : PhysicalCutBlock V}
    (hblock : block ∈ cutAtSeparators isSeparator edges) :
    block.1.length ≤ edges.length :=
  (run_sublist_of_mem_cutAtSeparators isSeparator edges block hblock).length_le

/-- No two consecutive edges are separators.  This is deliberately an
adjacency condition, rather than `List.Pairwise`, because nonconsecutive
matching edges are allowed. -/
def SeparatorsSpaced {V : Type*} (isSeparator : V × V → Bool) :
    List (V × V) → Prop
  | [] => True
  | [_] => True
  | edge :: next :: tail =>
      ¬ (isSeparator edge = true ∧ isSeparator next = true) ∧
        SeparatorsSpaced isSeparator (next :: tail)

/-- Structural splitter invariant.  Every block except possibly the first has
a positive run; if the input begins with a nonseparator, the first run is
positive as well. -/
theorem cutAtSeparators_positive_invariants
    {V : Type*} (isSeparator : V × V → Bool)
    (edges : List (V × V)) (hspaced : SeparatorsSpaced isSeparator edges) :
    (∀ block ∈ (cutAtSeparators isSeparator edges).tail,
        0 < block.1.length) ∧
      (match edges with
       | [] => True
       | first :: _ => isSeparator first ≠ true →
           ∀ block ∈ cutAtSeparators isSeparator edges,
             0 < block.1.length) := by
  induction edges with
  | nil => simp [cutAtSeparators]
  | cons edge tail ih =>
      cases tail with
      | nil =>
          by_cases hedge : isSeparator edge = true <;>
            simp [cutAtSeparators, hedge]
      | cons next tail =>
          have hpair :
              ¬ (isSeparator edge = true ∧
                isSeparator next = true) := hspaced.1
          have htailSpaced :
              SeparatorsSpaced isSeparator (next :: tail) := hspaced.2
          have htailInv := ih htailSpaced
          rw [cutAtSeparators]
          by_cases hedge : isSeparator edge = true
          · simp only [hedge, ↓reduceIte, List.tail_cons]
            have hnext : isSeparator next ≠ true := by
              intro hnext
              exact hpair ⟨hedge, hnext⟩
            exact ⟨htailInv.2 hnext, fun h => False.elim (h rfl)⟩
          · simp only [hedge]
            generalize hblocks :
              cutAtSeparators isSeparator (next :: tail) = blocks
            have htailPositive := htailInv.1
            rw [hblocks] at htailPositive
            cases blocks with
            | nil => simp
            | cons first blocks =>
                rcases first with ⟨run, separator⟩
                constructor
                · exact htailPositive
                · intro _ block hblock
                  rcases List.mem_cons.mp hblock with hblock | hblock
                  · subst block
                    simp
                  · exact htailPositive block hblock

theorem cutAtSeparators_runs_positive_of_head_not_separator
    {V : Type*} (isSeparator : V × V → Bool)
    (first : V × V) (tail : List (V × V))
    (hspaced : SeparatorsSpaced isSeparator (first :: tail))
    (hfirst : isSeparator first ≠ true) :
    ∀ block ∈ cutAtSeparators isSeparator (first :: tail),
      0 < block.1.length :=
  (cutAtSeparators_positive_invariants isSeparator
    (first :: tail) hspaced).2 hfirst

/-- Two decoded matching cells carried by consecutive oriented edges must be
the same cell: their common intermediate vertex is either a common row or a
common column. -/
theorem decoded_matching_cells_eq_of_join
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {M : Finset (A × B)} (hM : IsBipartiteMatching M)
    {left right : (A ⊕ B) × (A ⊕ B)}
    {leftCell rightCell : A × B}
    (hjoin : left.2 = right.1)
    (hleftMem : leftCell ∈ M) (hrightMem : rightCell ∈ M)
    (hleftDecode : orientedPairToCell left = some leftCell)
    (hrightDecode : orientedPairToCell right = some rightCell) :
    leftCell = rightCell := by
  rcases left with ⟨leftStart, leftFinish⟩
  rcases right with ⟨rightStart, rightFinish⟩
  rcases leftStart with a | b <;> rcases leftFinish with a' | b' <;>
    rcases rightStart with c | d <;> rcases rightFinish with c' | d' <;>
    simp [orientedPairToCell] at hleftDecode hrightDecode
  all_goals subst leftCell
  all_goals subst rightCell
  all_goals simp at hjoin
  all_goals subst_vars
  · apply Prod.ext
    · exact hM.2 _ _ _ hleftMem hrightMem
    · rfl
  · apply Prod.ext
    · rfl
    · exact hM.1 _ _ _ hleftMem hrightMem

theorem matchingTransitions_not_both_of_join_sym2_ne
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (left right : (A ⊕ B) × (A ⊕ B))
    (hjoin : left.2 = right.1)
    (hsymNe : s(left.1, left.2) ≠ s(right.1, right.2)) :
    ¬ (isMatchingTransition M left = true ∧
      isMatchingTransition M right = true) := by
  rintro ⟨hleft, hright⟩
  obtain ⟨leftCell, hleftMem, hleftDecode⟩ :=
    (isMatchingTransition_eq_true_iff M left).mp hleft
  obtain ⟨rightCell, hrightMem, hrightDecode⟩ :=
    (isMatchingTransition_eq_true_iff M right).mp hright
  have hcells : leftCell = rightCell :=
    decoded_matching_cells_eq_of_join hM hjoin
      hleftMem hrightMem hleftDecode hrightDecode
  apply hsymNe
  rw [← cellSym2_eq_sym2_of_orientedPairToCell_eq_some hleftDecode,
    ← cellSym2_eq_sym2_of_orientedPairToCell_eq_some hrightDecode,
    hcells]

/-- Along a joined edge-simple oriented traversal, matching transitions are
spaced: two consecutive transitions would share a matching vertex and hence
be the same undirected edge, contradicting edge simplicity. -/
theorem separatorsSpaced_isMatchingTransition_of_joins_nodup
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    {start finish : A ⊕ B}
    (edges : List ((A ⊕ B) × (A ⊕ B)))
    (hjoins : OrientedEdgeList.Joins start edges finish)
    (hnodup :
      (edges.map (fun edge => s(edge.1, edge.2))).Nodup) :
    SeparatorsSpaced (isMatchingTransition M) edges := by
  induction edges generalizing start with
  | nil => trivial
  | cons edge tail ih =>
      cases tail with
      | nil => trivial
      | cons next tail =>
          have hjoin : edge.2 = next.1 := by
            rcases edge with ⟨u, x⟩
            rcases next with ⟨y, z⟩
            exact hjoins.2.1.symm
          have hsymNe :
              s(edge.1, edge.2) ≠ s(next.1, next.2) := by
            intro hsym
            exact (List.nodup_cons.mp hnodup).1 (by simp [hsym])
          constructor
          · exact matchingTransitions_not_both_of_join_sym2_ne
              M hM edge next hjoin hsymNe
          · exact ih hjoins.2 (List.nodup_cons.mp hnodup).2

/-- A closed traversal ending in a genuine bipartite edge cannot consist only
of that edge: a one-edge closed traversal would be a loop. -/
theorem initial_nonempty_of_closed_ending_decoded
    {A B : Type*}
    (initial : List ((A ⊕ B) × (A ⊕ B)))
    (closing : (A ⊕ B) × (A ⊕ B))
    (hclosed : OrientedEdgeList.Joins closing.2
      (initial ++ [closing]) closing.2)
    {cell : A × B}
    (hdecode : orientedPairToCell closing = some cell) :
    initial ≠ [] := by
  intro hinitial
  subst initial
  rcases closing with ⟨u, x⟩
  rcases u with a | b <;> rcases x with a' | b' <;>
    simp [OrientedEdgeList.Joins, orientedPairToCell] at hclosed hdecode

/-- In a closed edge-simple traversal whose last edge is a matching
transition, the first edge is not a matching transition. -/
theorem head_not_matching_of_closed_ending_matching
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (first : (A ⊕ B) × (A ⊕ B))
    (tail : List ((A ⊕ B) × (A ⊕ B)))
    (closing : (A ⊕ B) × (A ⊕ B))
    (hclosed : OrientedEdgeList.Joins closing.2
      ((first :: tail) ++ [closing]) closing.2)
    (hnodup :
      (((first :: tail) ++ [closing]).map
        (fun edge => s(edge.1, edge.2))).Nodup)
    (hclosing : isMatchingTransition M closing = true) :
    isMatchingTransition M first ≠ true := by
  have hjoin : closing.2 = first.1 := hclosed.1.symm
  have hsymNe : s(closing.1, closing.2) ≠ s(first.1, first.2) := by
    intro hsym
    have hnotMem := (List.nodup_cons.mp hnodup).1
    apply hnotMem
    simp [hsym]
  intro hfirst
  exact matchingTransitions_not_both_of_join_sym2_ne
    M hM closing first hjoin hsymNe ⟨hclosing, hfirst⟩

/-- A decoded oriented cell canonically determines the Boolean orientation
used by `orientedMatchingStarts`. -/
theorem exists_orientedMatchingStart_of_decode_mem
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset (A × B))
    (edge : (A ⊕ B) × (A ⊕ B))
    {cell : A × B} (hcell : cell ∈ S)
    (hdecode : orientedPairToCell edge = some cell) :
    ∃ z ∈ orientedMatchingStarts S,
      edge.2 = orientedMatchingStartState z ∧
        edge = orientedMatchingClosingEdge z := by
  rcases edge with ⟨u, x⟩
  rcases u with a | b <;> rcases x with a' | b' <;>
    simp [orientedPairToCell] at hdecode
  · subst cell
    exact ⟨((a, b'), false), by
      simp [orientedMatchingStarts, hcell], rfl, rfl⟩
  · subst cell
    exact ⟨((a', b), true), by
      simp [orientedMatchingStarts, hcell], rfl, rfl⟩

/-- Filtering before `filterMap` only removes decoded entries. -/
theorem filterMap_filter_sublist
    {X Y : Type*} (f : X → Option Y) (keep : X → Bool)
    (xs : List X) :
    (xs.filter keep).filterMap f |>.Sublist (xs.filterMap f) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases hkeep : keep x <;> cases hdecode : f x <;>
        simp [hkeep, hdecode, ih]

/-- On any permutation of a covering simple-cycle traversal, the number of
matching-transition edges is exactly the physical intersection cardinality.
-/
theorem matching_filter_length_eq_inter_card_of_perm_walk
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {C : Finset (A × B)} {v : A ⊕ B}
    {p : (cellGraph C).Walk v v} (hp : p.IsCycle)
    (hcover : p.edges.toFinset = C.image cellSym2)
    (M : Finset (A × B))
    (edges : List ((A ⊕ B) × (A ⊕ B)))
    (hperm : (walkOrientedEdges p).Perm edges) :
    (edges.filter (isMatchingTransition M)).length = (C ∩ M).card := by
  have hfullDecode : ∀ edge ∈ edges,
      ∃ cell, orientedPairToCell edge = some cell := by
    intro edge hedge
    have hedgeWalk : edge ∈ walkOrientedEdges p :=
      hperm.mem_iff.mpr hedge
    obtain ⟨cell, _, hdecode⟩ :=
      walkOrientedEdge_decodes_mem p hedgeWalk
    exact ⟨cell, hdecode⟩
  have hfilteredDecode : ∀ edge ∈ edges.filter (isMatchingTransition M),
      ∃ cell, orientedPairToCell edge = some cell := by
    intro edge hedge
    exact hfullDecode edge (List.mem_of_mem_filter hedge)
  have hfullNodup :
      (edges.filterMap orientedPairToCell).Nodup :=
    filterMap_orientedPairToCell_nodup_of_perm_walkOrientedEdges hp hperm
  have hfilteredNodup :
      ((edges.filter (isMatchingTransition M)).filterMap
        orientedPairToCell).Nodup :=
    hfullNodup.sublist
      (filterMap_filter_sublist orientedPairToCell
        (isMatchingTransition M) edges)
  have hdecodeFull : decodeOrientedCells edges = C := by
    rw [← decodeOrientedCells_eq_of_perm hperm]
    exact decodeOrientedCells_walkOrientedEdges_eq_of_cover p hcover
  have hdecodeFiltered :
      decodeOrientedCells (edges.filter (isMatchingTransition M)) =
        C ∩ M := by
    rw [decodeOrientedCells_filter_isMatchingTransition, hdecodeFull]
  calc
    (edges.filter (isMatchingTransition M)).length =
        ((edges.filter (isMatchingTransition M)).filterMap
          orientedPairToCell).length :=
      (filterMap_length_eq_length_of_forall_eq_some _ _
        hfilteredDecode).symm
    _ = (decodeOrientedCells
          (edges.filter (isMatchingTransition M))).card :=
      (List.toFinset_card_of_nodup hfilteredNodup).symm
    _ = (C ∩ M).card := congrArg Finset.card hdecodeFiltered

theorem decode_transitionEdges_cutAtSeparators_eq_inter
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B))
    (edges : List ((A ⊕ B) × (A ⊕ B))) :
    decodeOrientedCells
        (PhysicalCutBlockList.transitionEdges
          (cutAtSeparators (isMatchingTransition M) edges)) =
      decodeOrientedCells edges ∩ M := by
  classical
  rw [transitionEdges_cutAtSeparators,
    decodeOrientedCells_filter_isMatchingTransition]

/-- For the matching-transition predicate, the residual projection of a
no-loss split decodes exactly to the physical cells outside `M`. -/
theorem decode_residualEdges_cutAtSeparators_eq_sdiff
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B))
    (initial : List ((A ⊕ B) × (A ⊕ B)))
    (closing : (A ⊕ B) × (A ⊕ B))
    (hclosing : isMatchingTransition M closing = true) :
    decodeOrientedCells
        (PhysicalCutBlockList.residualEdges
          (cutAtSeparators (isMatchingTransition M)
            (initial ++ [closing]))) =
      decodeOrientedCells (initial ++ [closing]) \ M := by
  classical
  let blocks := cutAtSeparators (isMatchingTransition M)
    (initial ++ [closing])
  have hflatten : PhysicalCutBlockList.orientedEdges blocks =
      initial ++ [closing] :=
    (cutAtSeparators_append_singleton
      (isMatchingTransition M) initial closing hclosing).2
  apply Finset.Subset.antisymm
  · intro cell hresidual
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · have hunion :
          cell ∈ decodeOrientedCells
              (PhysicalCutBlockList.residualEdges blocks) ∪
            decodeOrientedCells
              (PhysicalCutBlockList.transitionEdges blocks) :=
        Finset.mem_union_left _ hresidual
      rw [← PhysicalCutBlockList.decode_orientedEdges_eq_union,
        hflatten] at hunion
      exact hunion
    · simp only [decodeOrientedCells, List.mem_toFinset] at hresidual
      obtain ⟨edge, hedge, hdecode⟩ :=
        List.mem_filterMap.mp hresidual
      have hnotSeparator : isMatchingTransition M edge ≠ true := by
        exact residual_edge_not_separator_cutAtSeparators
          (isMatchingTransition M) hedge
      intro hcellM
      exact hnotSeparator
        ((isMatchingTransition_eq_true_iff M edge).mpr
          ⟨cell, hcellM, hdecode⟩)
  · intro cell houtside
    obtain ⟨hfull, hnotM⟩ := Finset.mem_sdiff.mp houtside
    have hunion :
        cell ∈ decodeOrientedCells
            (PhysicalCutBlockList.residualEdges blocks) ∪
          decodeOrientedCells
            (PhysicalCutBlockList.transitionEdges blocks) := by
      rw [← PhysicalCutBlockList.decode_orientedEdges_eq_union,
        hflatten]
      exact hfull
    rcases Finset.mem_union.mp hunion with hresidual | htransition
    · exact hresidual
    · exfalso
      have htransitionEq :
          decodeOrientedCells
              (PhysicalCutBlockList.transitionEdges blocks) =
            decodeOrientedCells (initial ++ [closing]) ∩ M := by
        dsimp only [blocks]
        exact decode_transitionEdges_cutAtSeparators_eq_inter M _
      rw [htransitionEq] at htransition
      exact hnotM (Finset.mem_inter.mp htransition).2

/-! ## Assembly into the existing source-free dependent code -/

/-- A joined block list with positive, cutoff-bounded residual runs assembles
into an actual `RelaxedBlockChainCode`.  All three list projections are
definitionally reconstructed, so this theorem does not assume decoding or
injectivity. -/
theorem exists_relaxedBlockChainCode_of_physicalCutBlocks
    {V : Type*} {L : ℕ} {v w : V}
    (blocks : List (PhysicalCutBlock V))
    (hjoins : PhysicalCutBlockList.Joins v blocks w)
    (hpositive : ∀ block ∈ blocks, 0 < block.1.length)
    (hcutoff : ∀ block ∈ blocks, block.1.length ≤ L) :
    ∃ code : RelaxedBlockChainCode V L blocks.length v w,
      relaxedBlockResidualEdges code =
          PhysicalCutBlockList.residualEdges blocks ∧
        relaxedBlockTransitionEdges code =
          PhysicalCutBlockList.transitionEdges blocks ∧
        relaxedBlockOrientedEdges code =
          PhysicalCutBlockList.orientedEdges blocks := by
  induction blocks generalizing v with
  | nil =>
      simp only [PhysicalCutBlockList.Joins] at hjoins
      subst w
      let zeroCode : KernelPathCode V 0 v v := ⟨v, rfl, rfl⟩
      refine ⟨zeroCode, ?_⟩
      simp [relaxedBlockResidualEdges, relaxedBlockTransitionEdges,
        relaxedBlockOrientedEdges, PhysicalCutBlockList.residualEdges,
        PhysicalCutBlockList.transitionEdges,
        PhysicalCutBlockList.orientedEdges]
  | cons block blocks ih =>
      rcases block with ⟨run, ⟨u, x⟩⟩
      simp only [PhysicalCutBlockList.Joins] at hjoins
      have hrunPositive : 0 < run.length :=
        hpositive (run, (u, x)) (by simp)
      have hrunCutoff : run.length ≤ L :=
        hcutoff (run, (u, x)) (by simp)
      obtain ⟨runCode, hrunCode⟩ :=
        exists_positiveKernelPathCode_orientedEdges_eq run hjoins.1
          hrunPositive hrunCutoff
      have htailPositive : ∀ tailBlock ∈ blocks,
          0 < tailBlock.1.length := by
        intro tailBlock htailBlock
        exact hpositive tailBlock (by simp [htailBlock])
      have htailCutoff : ∀ tailBlock ∈ blocks,
          tailBlock.1.length ≤ L := by
        intro tailBlock htailBlock
        exact hcutoff tailBlock (by simp [htailBlock])
      obtain ⟨tailCode, hresidual, htransition, horiented⟩ :=
        ih hjoins.2 htailPositive htailCutoff
      let code : RelaxedBlockChainCode V L (blocks.length + 1) v w :=
        ⟨x, ⟨⟨u, runCode⟩, tailCode⟩⟩
      refine ⟨code, ?_, ?_, ?_⟩
      · simp [code, relaxedBlockResidualEdges,
          PhysicalCutBlockList.residualEdges, hrunCode, hresidual]
      · simp [code, relaxedBlockTransitionEdges,
          PhysicalCutBlockList.transitionEdges, htransition]
      · simp [code, relaxedBlockOrientedEdges,
          PhysicalCutBlockList.orientedEdges, hrunCode, horiented]

/-- Closed joined blocks therefore produce a closed relaxed code with one
transition per block and exactly the supplied physical traversal. -/
theorem exists_closed_relaxedBlockChainCode_of_physicalCutBlocks
    {V : Type*} {L : ℕ} {v : V}
    (blocks : List (PhysicalCutBlock V))
    (hjoins : PhysicalCutBlockList.Joins v blocks v)
    (hpositive : ∀ block ∈ blocks, 0 < block.1.length)
    (hcutoff : ∀ block ∈ blocks, block.1.length ≤ L) :
    ∃ code : RelaxedBlockChainCode V L blocks.length v v,
      relaxedBlockResidualEdges code =
          PhysicalCutBlockList.residualEdges blocks ∧
        relaxedBlockTransitionEdges code =
          PhysicalCutBlockList.transitionEdges blocks ∧
        relaxedBlockOrientedEdges code =
          PhysicalCutBlockList.orientedEdges blocks ∧
        OrientedEdgeList.Joins v (relaxedBlockOrientedEdges code) v := by
  obtain ⟨code, hresidual, htransition, horiented⟩ :=
    exists_relaxedBlockChainCode_of_physicalCutBlocks blocks hjoins
      hpositive hcutoff
  exact ⟨code, hresidual, htransition, horiented,
    relaxedBlockOrientedEdges_closed code⟩

/-! ## The physical cycle-cutting theorem -/

/-- The remaining physical construction is realizable: rotate a covering
simple-cycle walk after a marked matching edge, split at all matching edges,
and assemble the resulting positive residual runs into the existing
source-free code. -/
theorem physicalCycleCuttingStatement
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) : PhysicalCycleCuttingStatement M := by
  intro hM C hC hCM
  obtain ⟨v, p, hp, hcover, _, hlengthBound⟩ :=
    exists_covering_cycleWalk_of_minimal_even C hC
  obtain ⟨markedCell, hmarked⟩ := hCM
  have hmarkedC : markedCell ∈ C := (Finset.mem_inter.mp hmarked).1
  have hmarkedM : markedCell ∈ M := (Finset.mem_inter.mp hmarked).2
  obtain ⟨closing, hclosingWalk, hclosingDecode⟩ :=
    exists_walkOrientedEdge_of_mem_of_cover p hcover hmarkedC
  have hclosingMatching : isMatchingTransition M closing = true :=
    (isMatchingTransition_eq_true_iff M closing).mpr
      ⟨markedCell, hmarkedM, hclosingDecode⟩
  obtain ⟨initial, hrotationPerm, hrotationClosed, _⟩ :=
    exists_closed_rotation_ending_at (walkOrientedEdges_joins p)
      hclosingWalk
  have hinitial : initial ≠ [] :=
    initial_nonempty_of_closed_ending_decoded initial closing
      hrotationClosed hclosingDecode
  obtain ⟨first, tail, rfl⟩ := List.exists_cons_of_ne_nil hinitial
  let rotated : List ((A ⊕ B) × (A ⊕ B)) :=
    (first :: tail) ++ [closing]
  let blocks : List (PhysicalCutBlock (A ⊕ B)) :=
    cutAtSeparators (isMatchingTransition M) rotated
  have hperm : (walkOrientedEdges p).Perm rotated := by
    simpa only [rotated] using hrotationPerm
  have hclosed : OrientedEdgeList.Joins closing.2 rotated closing.2 := by
    simpa only [rotated] using hrotationClosed
  have hsymNodupWalk :
      ((walkOrientedEdges p).map
        (fun edge => s(edge.1, edge.2))).Nodup := by
    rw [walkOrientedEdges_map_sym2]
    exact hp.edges_nodup
  have hsymNodup :
      (rotated.map (fun edge => s(edge.1, edge.2))).Nodup :=
    (hperm.map (fun edge => s(edge.1, edge.2))).nodup_iff.mp
      hsymNodupWalk
  have horientedNodup : rotated.Nodup :=
    hperm.nodup_iff.mp (walkOrientedEdges_nodup_of_isCycle hp)
  have hcellListNodup :
      (rotated.filterMap orientedPairToCell).Nodup :=
    filterMap_orientedPairToCell_nodup_of_perm_walkOrientedEdges hp hperm
  have hdecodeAll : ∀ edge ∈ rotated,
      ∃ cell, orientedPairToCell edge = some cell := by
    intro edge hedge
    have hedgeWalk : edge ∈ walkOrientedEdges p := hperm.mem_iff.mpr hedge
    obtain ⟨cell, _, hdecode⟩ :=
      walkOrientedEdge_decodes_mem p hedgeWalk
    exact ⟨cell, hdecode⟩
  have hdecodeFull : decodeOrientedCells rotated = C := by
    rw [← decodeOrientedCells_eq_of_perm hperm]
    exact decodeOrientedCells_walkOrientedEdges_eq_of_cover p hcover
  have hspaced : SeparatorsSpaced (isMatchingTransition M) rotated :=
    separatorsSpaced_isMatchingTransition_of_joins_nodup
      M hM rotated hclosed hsymNodup
  have hfirst : isMatchingTransition M first ≠ true := by
    apply head_not_matching_of_closed_ending_matching
      M hM first tail closing
    · simpa only [rotated] using hclosed
    · simpa only [rotated] using hsymNodup
    · exact hclosingMatching
  have hpositive : ∀ block ∈ blocks, 0 < block.1.length := by
    have hspaced' : SeparatorsSpaced (isMatchingTransition M)
        (first :: (tail ++ [closing])) := by
      simpa only [rotated, List.cons_append] using hspaced
    have hpositive' :=
      cutAtSeparators_runs_positive_of_head_not_separator
        (isMatchingTransition M) first (tail ++ [closing])
        hspaced' hfirst
    simpa only [blocks, rotated, List.cons_append] using hpositive'
  have hsplit := cutAtSeparators_append_singleton
    (isMatchingTransition M) (first :: tail) closing hclosingMatching
  have hblocksNonempty : blocks ≠ [] := by
    simpa only [blocks, rotated] using hsplit.1
  have hflatten : PhysicalCutBlockList.orientedEdges blocks = rotated := by
    simpa only [blocks, rotated] using hsplit.2
  have hblockJoins :
      PhysicalCutBlockList.Joins closing.2 blocks closing.2 := by
    apply PhysicalCutBlockList.joins_of_orientedEdges
    rw [hflatten]
    exact hclosed
  have hrotatedLength : rotated.length = p.length := by
    calc
      rotated.length = (walkOrientedEdges p).length := hperm.length_eq.symm
      _ = p.length := walkOrientedEdges_length p
  have hcutoff : ∀ block ∈ blocks,
      block.1.length ≤ Fintype.card (A ⊕ B) := by
    intro block hblock
    have hblock' : block ∈
        cutAtSeparators (isMatchingTransition M) rotated := by
      simpa only [blocks] using hblock
    calc
      block.1.length ≤ rotated.length :=
        run_length_le_of_mem_cutAtSeparators
          (isMatchingTransition M) rotated hblock'
      _ = p.length := hrotatedLength
      _ ≤ Fintype.card (A ⊕ B) := hlengthBound
  obtain ⟨chain, hchainResidual, hchainTransition,
      hchainOriented, _⟩ :=
    exists_closed_relaxedBlockChainCode_of_physicalCutBlocks
      blocks hblockJoins hpositive hcutoff
  have hblocksLength : blocks.length = (C ∩ M).card := by
    calc
      blocks.length =
          (rotated.filter (isMatchingTransition M)).length := by
        simpa only [blocks] using
          cutAtSeparators_length (isMatchingTransition M) rotated
      _ = (C ∩ M).card :=
        matching_filter_length_eq_inter_card_of_perm_walk
          hp hcover M rotated hperm
  have hblocksPos : 0 < blocks.length :=
    List.length_pos_iff.mpr hblocksNonempty
  let code : SourceFreeCycleCutCode A B :=
    ⟨⟨blocks.length, hblocksPos⟩, ⟨closing.2, chain⟩⟩
  have hcodeBlockCount : code.blockCount = blocks.length := rfl
  have hcodeStart : code.start = closing.2 := rfl
  have hcodeResidual :
      relaxedBlockResidualEdges code.chain =
        PhysicalCutBlockList.residualEdges blocks := hchainResidual
  have hcodeTransition :
      relaxedBlockTransitionEdges code.chain =
        PhysicalCutBlockList.transitionEdges blocks := hchainTransition
  have hcodeOriented :
      relaxedBlockOrientedEdges code.chain =
        PhysicalCutBlockList.orientedEdges blocks := hchainOriented
  obtain ⟨z, hz, hzStart, hzClosing⟩ :=
    exists_orientedMatchingStart_of_decode_mem
      (C ∩ M) closing hmarked hclosingDecode
  have hblocksLast :
      (PhysicalCutBlockList.transitionEdges blocks).getLast? =
        some closing := by
    simpa only [blocks, rotated] using
      transitionEdges_cutAtSeparators_append_singleton_getLast?
        (isMatchingTransition M) (first :: tail) closing
        hclosingMatching
  have hresidualList :
      PhysicalCutBlockList.residualEdges blocks =
        rotated.filter (fun edge => !(isMatchingTransition M edge)) := by
    simpa only [blocks, rotated] using
      residualEdges_cutAtSeparators_append_singleton
        (isMatchingTransition M) (first :: tail) closing
        hclosingMatching
  have htransitionList :
      PhysicalCutBlockList.transitionEdges blocks =
        rotated.filter (isMatchingTransition M) := by
    simpa only [blocks] using
      transitionEdges_cutAtSeparators (isMatchingTransition M) rotated
  refine ⟨code, {
    blockCount_eq := ?_
    markedStart := ?_
    residualCells_eq := ?_
    transitionCells_eq := ?_
    orientedEdges_nodup := ?_
    residualEdges_decode := ?_
    transitionEdges_decode := ?_
    residualCellList_nodup := ?_
    transitionCellList_nodup := ?_
  }⟩
  · exact hcodeBlockCount.trans hblocksLength
  · refine ⟨z, hz, hcodeStart.trans hzStart, ?_⟩
    calc
      (relaxedBlockTransitionEdges code.chain).getLast? =
          (PhysicalCutBlockList.transitionEdges blocks).getLast? :=
        congrArg List.getLast? hcodeTransition
      _ = some closing := hblocksLast
      _ = some (orientedMatchingClosingEdge z) := congrArg some hzClosing
  · unfold decodeRelaxedResidualCells
    calc
      decodeOrientedCells (relaxedBlockResidualEdges code.chain) =
          decodeOrientedCells
             (PhysicalCutBlockList.residualEdges blocks) := by
        rw [hcodeResidual]
      _ = decodeOrientedCells rotated \ M := by
        simpa only [blocks, rotated] using
          decode_residualEdges_cutAtSeparators_eq_sdiff
            M (first :: tail) closing hclosingMatching
      _ = C \ M := by rw [hdecodeFull]
  · unfold decodeRelaxedTransitionCells
    calc
      decodeOrientedCells (relaxedBlockTransitionEdges code.chain) =
          decodeOrientedCells
             (PhysicalCutBlockList.transitionEdges blocks) := by
        rw [hcodeTransition]
      _ = decodeOrientedCells rotated ∩ M := by
        simpa only [blocks] using
          decode_transitionEdges_cutAtSeparators_eq_inter M rotated
      _ = C ∩ M := by rw [hdecodeFull]
  · rw [hcodeOriented, hflatten]
    exact horientedNodup
  · intro edge hedge
    have hedgeFiltered :
        edge ∈ rotated.filter
          (fun e => !(isMatchingTransition M e)) := by
      rw [hcodeResidual, hresidualList] at hedge
      exact hedge
    exact hdecodeAll edge (List.mem_of_mem_filter hedgeFiltered)
  · intro edge hedge
    have hedgeFiltered :
        edge ∈ rotated.filter (isMatchingTransition M) := by
      rw [hcodeTransition, htransitionList] at hedge
      exact hedge
    exact hdecodeAll edge (List.mem_of_mem_filter hedgeFiltered)
  · rw [hcodeResidual, hresidualList]
    exact hcellListNodup.sublist
      (filterMap_filter_sublist orientedPairToCell
        (fun edge => !(isMatchingTransition M edge)) rotated)
  · rw [hcodeTransition, htransitionList]
    exact hcellListNodup.sublist
      (filterMap_filter_sublist orientedPairToCell
        (isMatchingTransition M) rotated)

#print axioms exists_kernelPathCode_orientedEdges_eq
#print axioms exists_positiveKernelPathCode_orientedEdges_eq
#print axioms exists_relaxedBlockChainCode_of_physicalCutBlocks
#print axioms exists_closed_relaxedBlockChainCode_of_physicalCutBlocks
#print axioms physicalCycleCuttingStatement

end

end Erdos625
