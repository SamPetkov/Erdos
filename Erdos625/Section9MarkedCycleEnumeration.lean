import Erdos625.Section9PhysicalCycleEncoder

/-!
# Section IX: marking the chosen physical cycle encodings

The physical encoder lands in a dependent source-free code whose positive
block count and marked start vary with the cycle.  This module exposes exactly
those two finite indices: a marked orientation in `orientedMatchingStarts M`,
a predecessor in the finite block-count range, and the transported closed
relaxed block chain.  The target contains no physical cycle and no decoding,
faithfulness, reconstruction, or injectivity certificate.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-! ## The finite data-only target -/

/-- A marked, positive, bounded closed relaxed traversal.  The `Fin` index
`r` represents `r + 1` blocks, so every chain in the target has positive block
count at most the ambient vertex count. -/
abbrev MarkedCycleTraversalCode
    (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) :=
  Σ z : {z : (A × B) × Bool // z ∈ orientedMatchingStarts M},
    Σ r : Fin (Fintype.card (A ⊕ B)),
      RelaxedBlockChainCode (A ⊕ B) (Fintype.card (A ⊕ B))
        (r.1 + 1) (orientedMatchingStartState z.1)
          (orientedMatchingStartState z.1)

/-- The honest mixed-cycle source is finite because it is a subtype of the
finite type of bipartite edge sets. -/
noncomputable instance instFintypeMixedSimpleCycle
    (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) : Fintype (MixedSimpleCycle A B M) :=
  Fintype.ofFinite _

namespace MarkedCycleTraversalCode

/-- Marked orientation carried by a traversal code. -/
def mark
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {M : Finset (A × B)}
    (code : MarkedCycleTraversalCode A B M) : (A × B) × Bool :=
  code.1.1

/-- The positive block count is one more than this finite predecessor. -/
def blockPredecessor
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {M : Finset (A × B)}
    (code : MarkedCycleTraversalCode A B M) :
    Fin (Fintype.card (A ⊕ B)) :=
  code.2.1

/-- Underlying closed relaxed block chain. -/
def chain
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {M : Finset (A × B)}
    (code : MarkedCycleTraversalCode A B M) :
    RelaxedBlockChainCode (A ⊕ B) (Fintype.card (A ⊕ B))
      (code.blockPredecessor.1 + 1)
      (orientedMatchingStartState code.mark)
      (orientedMatchingStartState code.mark) :=
  code.2.2

/-- Exact chain weight of a marked traversal code. -/
def weight
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {M : Finset (A × B)}
    (q : A → B → ℝ≥0∞)
    (code : MarkedCycleTraversalCode A B M) : ℝ≥0∞ :=
  code.chain.weight (bipartiteCellKernel q) (matchingTraversalKernel M)

end MarkedCycleTraversalCode

/-! ## Honest dependent transport -/

/-- Transport a relaxed block chain across equal block counts and endpoints.
This helper contains no source object or certificate; it is only equality
elimination for the genuinely dependent target type. -/
def castRelaxedBlockChainCode
    {V : Type*} {L r r' : ℕ} {v v' w w' : V}
    (hr : r = r') (hv : v = v') (hw : w = w')
    (code : RelaxedBlockChainCode V L r v w) :
    RelaxedBlockChainCode V L r' v' w' := by
  subst r'
  subst v'
  subst w'
  exact code

@[simp]
theorem decodeRelaxedBlockCells_castRelaxedBlockChainCode
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {L r r' : ℕ} {v v' w w' : A ⊕ B}
    (hr : r = r') (hv : v = v') (hw : w = w')
    (code : RelaxedBlockChainCode (A ⊕ B) L r v w) :
    decodeRelaxedBlockCells
        (castRelaxedBlockChainCode hr hv hw code) =
      decodeRelaxedBlockCells code := by
  subst r'
  subst v'
  subst w'
  rfl

@[simp]
theorem relaxedBlockChainWeight_castRelaxedBlockChainCode
    {V : Type*} {L r r' : ℕ} {v v' w w' : V}
    (K P : V → V → ℝ≥0∞)
    (hr : r = r') (hv : v = v') (hw : w = w')
    (code : RelaxedBlockChainCode V L r v w) :
    (castRelaxedBlockChainCode hr hv hw code).weight K P =
      code.weight K P := by
  subst r'
  subst v'
  subst w'
  rfl

/-! ## Choosing and packaging the finite indices -/

/-- The marked oriented matching edge supplied by faithfulness of the chosen
physical cut. -/
noncomputable def chosenPhysicalCycleMark
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (C : MixedSimpleCycle A B M) : (A × B) × Bool :=
  Classical.choose (chosenPhysicalCycleCut_faithful M hM C).markedStart

theorem chosenPhysicalCycleMark_spec
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (C : MixedSimpleCycle A B M) :
    chosenPhysicalCycleMark M hM C ∈ orientedMatchingStarts (C.1 ∩ M) ∧
      (chosenPhysicalCycleCut M hM C).start =
        orientedMatchingStartState (chosenPhysicalCycleMark M hM C) ∧
      (relaxedBlockTransitionEdges
        (chosenPhysicalCycleCut M hM C).chain).getLast? =
          some (orientedMatchingClosingEdge
            (chosenPhysicalCycleMark M hM C)) :=
  Classical.choose_spec
    (chosenPhysicalCycleCut_faithful M hM C).markedStart

theorem orientedMatchingStarts_mono
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {S T : Finset (A × B)} (hST : S ⊆ T) :
    orientedMatchingStarts S ⊆ orientedMatchingStarts T := by
  intro z hz
  obtain ⟨hzS, hzOrientation⟩ := Finset.mem_product.mp hz
  exact Finset.mem_product.mpr ⟨hST hzS, hzOrientation⟩

theorem chosenPhysicalCycleMark_mem
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (C : MixedSimpleCycle A B M) :
    chosenPhysicalCycleMark M hM C ∈ orientedMatchingStarts M := by
  exact orientedMatchingStarts_mono Finset.inter_subset_right
    (chosenPhysicalCycleMark_spec M hM C).1

/-- The predecessor of the positive block count, with its strict ambient
vertex bound proved from faithfulness and the matching property. -/
noncomputable def chosenPhysicalCycleBlockPredecessor
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (C : MixedSimpleCycle A B M) :
    Fin (Fintype.card (A ⊕ B)) :=
  ⟨(chosenPhysicalCycleCut M hM C).blockCount - 1, by
    have hpos := (chosenPhysicalCycleCut M hM C).blockCount_pos
    have hle :=
      (chosenPhysicalCycleCut_faithful M hM C).blockCount_le_vertex_count hM
    omega⟩

theorem chosenPhysicalCycleBlockPredecessor_succ
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (C : MixedSimpleCycle A B M) :
    (chosenPhysicalCycleBlockPredecessor M hM C).1 + 1 =
      (chosenPhysicalCycleCut M hM C).blockCount := by
  change (chosenPhysicalCycleCut M hM C).blockCount - 1 + 1 =
    (chosenPhysicalCycleCut M hM C).blockCount
  have hpos := (chosenPhysicalCycleCut M hM C).blockCount_pos
  omega

/-- Transport the chosen source-free chain into the explicit finite marked
index. -/
noncomputable def chosenMarkedCycleChain
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (C : MixedSimpleCycle A B M) :
    RelaxedBlockChainCode (A ⊕ B) (Fintype.card (A ⊕ B))
      ((chosenPhysicalCycleBlockPredecessor M hM C).1 + 1)
      (orientedMatchingStartState (chosenPhysicalCycleMark M hM C))
      (orientedMatchingStartState (chosenPhysicalCycleMark M hM C)) :=
  castRelaxedBlockChainCode
    (chosenPhysicalCycleBlockPredecessor_succ M hM C).symm
    (chosenPhysicalCycleMark_spec M hM C).2.1
    (chosenPhysicalCycleMark_spec M hM C).2.1
    (chosenPhysicalCycleCut M hM C).chain

/-- Package the chosen physical encoder into the exact finite dependent
traversal family. -/
noncomputable def chosenMarkedCycleTraversal
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (C : MixedSimpleCycle A B M) :
    MarkedCycleTraversalCode A B M :=
  ⟨⟨chosenPhysicalCycleMark M hM C,
      chosenPhysicalCycleMark_mem M hM C⟩,
    ⟨chosenPhysicalCycleBlockPredecessor M hM C,
      chosenMarkedCycleChain M hM C⟩⟩

/-! ## Reconstruction, injectivity, and exact physical weight -/

theorem decode_chosenMarkedCycleTraversal
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (C : MixedSimpleCycle A B M) :
    decodeRelaxedBlockCells (chosenMarkedCycleTraversal M hM C).chain = C.1 := by
  change decodeRelaxedBlockCells (chosenMarkedCycleChain M hM C) = C.1
  unfold chosenMarkedCycleChain
  rw [decodeRelaxedBlockCells_castRelaxedBlockChainCode]
  exact decode_chosenPhysicalCycleCut M hM C

theorem chosenMarkedCycleTraversal_injective
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M) :
    Function.Injective (chosenMarkedCycleTraversal M hM) := by
  intro C D hcode
  apply Subtype.ext
  have hdecoded := congrArg
    (fun code : MarkedCycleTraversalCode A B M =>
      decodeRelaxedBlockCells code.chain) hcode
  exact (decode_chosenMarkedCycleTraversal M hM C).symm.trans
    (hdecoded.trans (decode_chosenMarkedCycleTraversal M hM D))

theorem chosenMarkedCycleTraversal_weight_eq
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ℝ≥0∞)
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (C : MixedSimpleCycle A B M) :
    (chosenMarkedCycleTraversal M hM C).weight q =
      edgeWeightOutsideENN q M C.1 := by
  change
    (chosenMarkedCycleChain M hM C).weight
      (bipartiteCellKernel q) (matchingTraversalKernel M) =
        edgeWeightOutsideENN q M C.1
  unfold chosenMarkedCycleChain
  rw [relaxedBlockChainWeight_castRelaxedBlockChainCode]
  exact chosenPhysicalCycleCut_weight_eq q M hM C

/-! ## Exact enumeration of the finite marked target -/

/-- Summing the data-only target first over its marked orientation and block
predecessor gives the endpoint-resolved mass of the composed block kernel.
-/
theorem sum_markedCycleTraversalCode_weight_eq_endpointMass
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ℝ≥0∞) (M : Finset (A × B)) :
    (∑ code : MarkedCycleTraversalCode A B M, code.weight q) =
      ∑ z : {z : (A × B) × Bool // z ∈ orientedMatchingStarts M},
        ∑ r : Fin (Fintype.card (A ⊕ B)),
          finiteKernelEndpointMass
            (finiteKernelComp
              (finitePositiveWalkKernel (bipartiteCellKernel q)
                (Fintype.card (A ⊕ B)))
              (matchingTraversalKernel M))
            (r.1 + 1) (orientedMatchingStartState z.1)
              (orientedMatchingStartState z.1) := by
  unfold MarkedCycleTraversalCode.weight MarkedCycleTraversalCode.chain
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  exact sum_relaxedBlockChainCode_weight_eq_finiteKernelEndpointMass
    (bipartiteCellKernel q) (matchingTraversalKernel M)
    (Fintype.card (A ⊕ B)) (r.1 + 1)
    (orientedMatchingStartState z.1) (orientedMatchingStartState z.1)

/-- Forgetting the terminal endpoint can only increase the marked traversal
mass.  The right-hand side is the same finite marked-start/block-count walk
mass used by the geometric traversal estimate, expressed on its intrinsic
subtype and `Fin` indices. -/
theorem sum_markedCycleTraversalCode_weight_le_walkMass
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ℝ≥0∞) (M : Finset (A × B)) :
    (∑ code : MarkedCycleTraversalCode A B M, code.weight q) ≤
      ∑ z : {z : (A × B) × Bool // z ∈ orientedMatchingStarts M},
        ∑ r : Fin (Fintype.card (A ⊕ B)),
          finiteKernelWalkMass
            (finiteKernelComp
              (finitePositiveWalkKernel (bipartiteCellKernel q)
                (Fintype.card (A ⊕ B)))
              (matchingTraversalKernel M))
            (r.1 + 1) (orientedMatchingStartState z.1) := by
  rw [sum_markedCycleTraversalCode_weight_eq_endpointMass]
  apply Finset.sum_le_sum
  intro z hz
  apply Finset.sum_le_sum
  intro r hr
  let K := finiteKernelComp
    (finitePositiveWalkKernel (bipartiteCellKernel q)
      (Fintype.card (A ⊕ B)))
    (matchingTraversalKernel M)
  let start := orientedMatchingStartState z.1
  calc
    finiteKernelEndpointMass K (r.1 + 1) start start ≤
        ∑ w, finiteKernelEndpointMass K (r.1 + 1) start w := by
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun w => finiteKernelEndpointMass K (r.1 + 1) start w)
        (fun w _ => bot_le) (Finset.mem_univ start)
    _ = finiteKernelWalkMass K (r.1 + 1) start :=
      sum_finiteKernelEndpointMass_eq_finiteKernelWalkMass
        K (r.1 + 1) start

/-- Convert the intrinsic subtype/`Fin` indexing into the literal nested
`Finset` sums used by the existing traversal bounds. -/
theorem sum_subtype_fin_eq_sum_finset_range
    {X : Type*} [DecidableEq X]
    (S : Finset X) (L : ℕ) (f : X → ℕ → ℝ≥0∞) :
    (∑ z : {z : X // z ∈ S}, ∑ r : Fin L, f z.1 r.1) =
      ∑ z ∈ S, ∑ r ∈ Finset.range L, f z r := by
  rw [show (Finset.univ : Finset {z : X // z ∈ S}) = S.attach by
    ext z
    simp]
  rw [Finset.sum_attach S (fun z => ∑ r : Fin L, f z r.1)]
  apply Finset.sum_congr rfl
  intro z hz
  exact Fin.sum_univ_eq_sum_range (f z) L

/-- Exact endpoint enumeration in the literal nested `Finset` syntax. -/
theorem sum_markedCycleTraversalCode_weight_eq_endpointMass_finset
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ℝ≥0∞) (M : Finset (A × B)) :
    (∑ code : MarkedCycleTraversalCode A B M, code.weight q) =
      ∑ z ∈ orientedMatchingStarts M,
        ∑ r ∈ Finset.range (Fintype.card (A ⊕ B)),
          finiteKernelEndpointMass
            (finiteKernelComp
              (finitePositiveWalkKernel (bipartiteCellKernel q)
                (Fintype.card (A ⊕ B)))
              (matchingTraversalKernel M))
            (r + 1) (orientedMatchingStartState z)
              (orientedMatchingStartState z) := by
  rw [sum_markedCycleTraversalCode_weight_eq_endpointMass]
  exact sum_subtype_fin_eq_sum_finset_range
    (orientedMatchingStarts M) (Fintype.card (A ⊕ B))
    (fun z r =>
      finiteKernelEndpointMass
        (finiteKernelComp
          (finitePositiveWalkKernel (bipartiteCellKernel q)
            (Fintype.card (A ⊕ B)))
          (matchingTraversalKernel M))
        (r + 1) (orientedMatchingStartState z)
          (orientedMatchingStartState z))

/-- Literal nested walk-mass bound matching the summation shape of the
existing marked traversal estimates. -/
theorem sum_markedCycleTraversalCode_weight_le_walkMass_finset
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ℝ≥0∞) (M : Finset (A × B)) :
    (∑ code : MarkedCycleTraversalCode A B M, code.weight q) ≤
      ∑ z ∈ orientedMatchingStarts M,
        ∑ r ∈ Finset.range (Fintype.card (A ⊕ B)),
          finiteKernelWalkMass
            (finiteKernelComp
              (finitePositiveWalkKernel (bipartiteCellKernel q)
                (Fintype.card (A ⊕ B)))
              (matchingTraversalKernel M))
            (r + 1) (orientedMatchingStartState z) := by
  calc
    (∑ code : MarkedCycleTraversalCode A B M, code.weight q) ≤
        ∑ z : {z : (A × B) × Bool // z ∈ orientedMatchingStarts M},
          ∑ r : Fin (Fintype.card (A ⊕ B)),
            finiteKernelWalkMass
              (finiteKernelComp
                (finitePositiveWalkKernel (bipartiteCellKernel q)
                  (Fintype.card (A ⊕ B)))
                (matchingTraversalKernel M))
              (r.1 + 1) (orientedMatchingStartState z.1) :=
      sum_markedCycleTraversalCode_weight_le_walkMass q M
    _ = ∑ z ∈ orientedMatchingStarts M,
          ∑ r ∈ Finset.range (Fintype.card (A ⊕ B)),
            finiteKernelWalkMass
              (finiteKernelComp
                (finitePositiveWalkKernel (bipartiteCellKernel q)
                  (Fintype.card (A ⊕ B)))
                (matchingTraversalKernel M))
              (r + 1) (orientedMatchingStartState z) :=
      sum_subtype_fin_eq_sum_finset_range
        (orientedMatchingStarts M) (Fintype.card (A ⊕ B))
        (fun z r =>
          finiteKernelWalkMass
            (finiteKernelComp
              (finitePositiveWalkKernel (bipartiteCellKernel q)
                (Fintype.card (A ⊕ B)))
              (matchingTraversalKernel M))
            (r + 1) (orientedMatchingStartState z))

/-- The injective physical encoder bounds the total mixed-cycle weight by the
total weight of the data-only marked traversal family. -/
theorem sum_mixedSimpleCycle_weight_le_markedTraversalCode
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ℝ≥0∞)
    (M : Finset (A × B)) (hM : IsBipartiteMatching M) :
    (∑ C : MixedSimpleCycle A B M, edgeWeightOutsideENN q M C.1) ≤
      ∑ code : MarkedCycleTraversalCode A B M, code.weight q := by
  calc
    (∑ C : MixedSimpleCycle A B M, edgeWeightOutsideENN q M C.1) =
        ∑ C : MixedSimpleCycle A B M,
          (chosenMarkedCycleTraversal M hM C).weight q := by
      apply Finset.sum_congr rfl
      intro C hC
      exact (chosenMarkedCycleTraversal_weight_eq q M hM C).symm
    _ ≤ ∑ code : MarkedCycleTraversalCode A B M, code.weight q := by
      simpa only [tsum_fintype] using
        ENNReal.tsum_comp_le_tsum_of_injective
          (chosenMarkedCycleTraversal_injective M hM)
          (fun code : MarkedCycleTraversalCode A B M => code.weight q)

/-- Combined physical-to-traversal inequality in the exact nested summation
shape consumed by the existing analytic bound. -/
theorem sum_mixedSimpleCycle_weight_le_nested_walkMass
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ℝ≥0∞)
    (M : Finset (A × B)) (hM : IsBipartiteMatching M) :
    (∑ C : MixedSimpleCycle A B M, edgeWeightOutsideENN q M C.1) ≤
      ∑ z ∈ orientedMatchingStarts M,
        ∑ r ∈ Finset.range (Fintype.card (A ⊕ B)),
          finiteKernelWalkMass
            (finiteKernelComp
              (finitePositiveWalkKernel (bipartiteCellKernel q)
                (Fintype.card (A ⊕ B)))
              (matchingTraversalKernel M))
            (r + 1) (orientedMatchingStartState z) :=
  (sum_mixedSimpleCycle_weight_le_markedTraversalCode q M hM).trans
    (sum_markedCycleTraversalCode_weight_le_walkMass_finset q M)

#print axioms decode_chosenMarkedCycleTraversal
#print axioms chosenMarkedCycleTraversal_injective
#print axioms chosenMarkedCycleTraversal_weight_eq
#print axioms sum_markedCycleTraversalCode_weight_eq_endpointMass
#print axioms sum_markedCycleTraversalCode_weight_le_walkMass
#print axioms sum_markedCycleTraversalCode_weight_eq_endpointMass_finset
#print axioms sum_markedCycleTraversalCode_weight_le_walkMass_finset
#print axioms sum_mixedSimpleCycle_weight_le_markedTraversalCode
#print axioms sum_mixedSimpleCycle_weight_le_nested_walkMass

end

end Erdos625
