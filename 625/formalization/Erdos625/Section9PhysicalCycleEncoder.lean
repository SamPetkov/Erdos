import Erdos625.Section9PhysicalCycleCutting
import Erdos625.Section9ActualResidualENNRealPolymerBridge

/-!
# Section IX: canonical faithful encoding of mixed physical cycles

The physical cutting theorem supplies at least one faithful source-free code
for every simple bipartite cycle meeting a fixed matching.  This module makes
one classical choice, proves that its source-free decoder recovers the
original cycle, and derives injectivity solely from that reconstruction.

The chosen target code still contains no source cycle or reconstruction
certificate.  This module also transports the exact physical residual weight
to the chosen code.  It does not yet package the dependent marked-start and
block-count indices or compare the resulting family sum with the complete
relaxed traversal enumeration.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- Simple bipartite cycles that meet the distinguished matching.  The source
object carries only the physical edge set and its two honest properties; it
does not carry a tour, cut, code, or reconstruction certificate. -/
abbrev MixedSimpleCycle
    (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) :=
  {C : Finset (A × B) //
    IsSimpleBipartiteCycle C ∧ (C ∩ M).Nonempty}

/-- Choose one faithful source-free cut code using the constructive physical
cycle-cutting theorem. -/
noncomputable def chosenPhysicalCycleCut
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (C : MixedSimpleCycle A B M) :
    SourceFreeCycleCutCode A B :=
  Classical.choose
    (physicalCycleCuttingStatement M hM C.1 C.2.1 C.2.2)

/-- The chosen code satisfies the full external faithfulness relation. -/
theorem chosenPhysicalCycleCut_faithful
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (C : MixedSimpleCycle A B M) :
    IsFaithfulCycleCut C.1 M (chosenPhysicalCycleCut M hM C) :=
  Classical.choose_spec
    (physicalCycleCuttingStatement M hM C.1 C.2.1 C.2.2)

/-- Decoding the chosen source-free code recovers the original physical
cycle exactly. -/
theorem decode_chosenPhysicalCycleCut
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (C : MixedSimpleCycle A B M) :
    decodeRelaxedBlockCells (chosenPhysicalCycleCut M hM C).chain = C.1 :=
  (chosenPhysicalCycleCut_faithful M hM C).decode_eq

/-- The canonical encoder is injective because its source-free decoder is a
left inverse.  No ordering of cycles and no code certificate in the source
type is used. -/
theorem chosenPhysicalCycleCut_injective
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M) :
    Function.Injective (chosenPhysicalCycleCut M hM) := by
  intro C D hcode
  apply Subtype.ext
  have hdecoded :=
    congrArg
      (fun code : SourceFreeCycleCutCode A B =>
        decodeRelaxedBlockCells code.chain)
      hcode
  exact (decode_chosenPhysicalCycleCut M hM C).symm.trans
    (hdecoded.trans (decode_chosenPhysicalCycleCut M hM D))

/-- Exact physical weight of the chosen code.  Every cell of `C \ M`
contributes once and every matching transition contributes one. -/
theorem chosenPhysicalCycleCut_weight_eq
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ℝ≥0∞)
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (C : MixedSimpleCycle A B M) :
    (chosenPhysicalCycleCut M hM C).chain.weight
        (bipartiteCellKernel q) (matchingTraversalKernel M) =
      edgeWeightOutsideENN q M C.1 := by
  simpa only [edgeWeightOutsideENN] using
    (chosenPhysicalCycleCut_faithful M hM C).codeWeight_eq_sdiff_prod q

#print axioms chosenPhysicalCycleCut_faithful
#print axioms decode_chosenPhysicalCycleCut
#print axioms chosenPhysicalCycleCut_injective
#print axioms chosenPhysicalCycleCut_weight_eq

end

end Erdos625
