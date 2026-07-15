import Erdos625.Section9CycleRankResidual
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# The finite binary cycle-space cardinality identity

For a finite simple graph `G`, the binary incidence map sends an edge
coefficient vector to its vector of vertex parities.  This file proves that
the kernel has dimension

`|E(G)| + number of connected components - |V(G)|`

and therefore has cardinality `2 ^ cycleRank G`.  It then identifies the
kernel with the literal finite edge subsets having even degree at every
vertex.  This is the finite identity used in manuscript equation (6.7).
-/

namespace Erdos625

open scoped BigOperators
open Matrix Module SimpleGraph

noncomputable section

/-- The vertex-by-edge incidence matrix of a finite simple graph over
`ZMod 2`.  Columns are indexed only by actual edges. -/
def graphIncidenceMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix V G.edgeSet (ZMod 2) :=
  fun v e => if v ∈ (e.1 : Sym2 V) then 1 else 0

/-- In characteristic two, the sum of two coefficients vanishes exactly when
the coefficients agree. -/
lemma zmodTwo_add_eq_zero_iff (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  have hself (x : ZMod 2) : x + x = 0 := by
    have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    rw [← two_mul, htwo, zero_mul]
  constructor
  · intro h
    apply add_right_cancel (b := b)
    exact h.trans (hself b).symm
  · intro h
    subst a
    exact hself _

/-- A transposed incidence column evaluates to the sum of the values at the
two endpoints of its edge. -/
lemma graphIncidenceMatrix_transpose_mulVec_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ZMod 2) {u v : V} (huv : G.Adj u v) :
    ((graphIncidenceMatrix G)ᵀ *ᵥ x)
        ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ = x u + x v := by
  simp only [graphIncidenceMatrix, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, ite_mul, one_mul, zero_mul, Sym2.mem_iff]
  have hsplit (w : V) :
      (if w = u ∨ w = v then x w else 0) =
        (if w = u then x u else 0) + (if w = v then x v else 0) := by
    by_cases hwu : w = u
    · subst w
      simp [huv.ne]
    · by_cases hwv : w = v
      · subst w
        simp [hwu]
      · simp [hwu, hwv]
  calc
    (∑ w, if w = u ∨ w = v then x w else 0) =
        ∑ w, ((if w = u then x u else 0) +
          (if w = v then x v else 0)) := by
      exact Finset.sum_congr rfl fun w _ => hsplit w
    _ = (∑ w, if w = u then x u else 0) +
        ∑ w, if w = v then x v else 0 := Finset.sum_add_distrib
    _ = x u + x v := by simp

/-- The cardinality of a finset depends only on its underlying set, expressed
with the instance-independent `Nat.card`. -/
lemma finset_card_eq_natCard_set_of_coe_eq
    {α : Type*} (F : Finset α) (S : Set α) (h : (F : Set α) = S) :
    F.card = Nat.card S := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.setCongr h)

/-- The kernel of the transposed incidence matrix consists exactly of vertex
functions that are constant across every edge. -/
lemma graphIncidenceMatrix_transpose_mulVec_eq_zero_iff_forall_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ZMod 2) :
    (graphIncidenceMatrix G)ᵀ *ᵥ x = 0 ↔
      ∀ u v : V, G.Adj u v → x u = x v := by
  constructor
  · intro hx u v huv
    have h := congrFun hx ⟨s(u, v), G.mem_edgeSet.mpr huv⟩
    rw [graphIncidenceMatrix_transpose_mulVec_apply G x huv] at h
    exact (zmodTwo_add_eq_zero_iff _ _).mp h
  · intro hx
    funext e
    rcases e with ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : G.Adj u v := G.mem_edgeSet.mp he
      rw [graphIncidenceMatrix_transpose_mulVec_apply G x huv]
      exact (zmodTwo_add_eq_zero_iff _ _).mpr (hx u v huv)

/-- Equivalently, a transposed-kernel vector is constant on every connected
component. -/
lemma graphIncidenceMatrix_transpose_mulVec_eq_zero_iff_forall_reachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ZMod 2) :
    (graphIncidenceMatrix G)ᵀ *ᵥ x = 0 ↔
      ∀ u v : V, G.Reachable u v → x u = x v := by
  rw [graphIncidenceMatrix_transpose_mulVec_eq_zero_iff_forall_adj]
  refine ⟨?_, fun h u v huv => h u v huv.reachable⟩
  intro h u v ⟨w⟩
  induction w with
  | nil => rfl
  | cons huv _ ih => exact (h _ _ huv).trans ih

/-- The indicator vector of a connected component, regarded as an element of
the transposed incidence kernel. -/
def incidenceTransposeKerBasisAux
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq G.ConnectedComponent]
    (c : G.ConnectedComponent) :
    LinearMap.ker (graphIncidenceMatrix G)ᵀ.mulVecLin := by
  refine ⟨fun v => if G.connectedComponentMk v = c then 1 else 0, ?_⟩
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply,
    graphIncidenceMatrix_transpose_mulVec_eq_zero_iff_forall_reachable]
  intro u v huv
  rw [ConnectedComponent.sound huv]

/-- Component indicator vectors are linearly independent. -/
lemma incidenceTransposeKerBasisAux_linearIndependent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq G.ConnectedComponent] :
    LinearIndependent (ZMod 2) (incidenceTransposeKerBasisAux G) := by
  rw [Fintype.linearIndependent_iff]
  intro coefficients hzero
  rw [Subtype.ext_iff] at hzero
  have hsum :
      ∑ c, coefficients c • incidenceTransposeKerBasisAux G c =
        fun v => coefficients (G.connectedComponentMk v) := by
    simp only [incidenceTransposeKerBasisAux, SetLike.mk_smul_mk]
    repeat rw [AddSubmonoid.coe_finsetSum]
    ext v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [hsum] at hzero
  intro c
  obtain ⟨v, hv⟩ : ∃ v : V, G.connectedComponentMk v = c := Quot.exists_rep c
  exact hv ▸ congrFun hzero v

/-- Component indicator vectors span the whole transposed incidence kernel. -/
lemma incidenceTransposeKerBasisAux_spans
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq G.ConnectedComponent] :
    ⊤ ≤ Submodule.span (ZMod 2)
      (Set.range (incidenceTransposeKerBasisAux G)) := by
  intro x _
  rw [Submodule.mem_span_range_iff_exists_fun]
  use Quot.lift x.val (by
    rw [← graphIncidenceMatrix_transpose_mulVec_eq_zero_iff_forall_reachable G,
      ← Matrix.mulVecLin_apply, LinearMap.map_coe_ker])
  ext v
  simp only [incidenceTransposeKerBasisAux]
  rw [AddSubmonoid.coe_finsetSum]
  simp only [SetLike.mk_smul_mk, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  rfl

/-- A basis of the transposed incidence kernel indexed by connected
components. -/
def incidenceTransposeKerBasis
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq G.ConnectedComponent] :
    Basis G.ConnectedComponent (ZMod 2)
      (LinearMap.ker (graphIncidenceMatrix G)ᵀ.mulVecLin) :=
  Basis.mk (incidenceTransposeKerBasisAux_linearIndependent G)
    (incidenceTransposeKerBasisAux_spans G)

/-- The nullity of the transposed incidence matrix is the number of connected
components. -/
lemma finrank_ker_graphIncidenceMatrix_transpose
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Module.finrank (ZMod 2)
        (LinearMap.ker (graphIncidenceMatrix G)ᵀ.mulVecLin) =
      Fintype.card G.ConnectedComponent := by
  classical
  rw [Module.finrank_eq_card_basis (incidenceTransposeKerBasis G)]

/-- The binary cycle space is the kernel of the vertex-edge incidence map. -/
abbrev graphCycleSpace
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  LinearMap.ker (graphIncidenceMatrix G).mulVecLin

/-- Rank-nullity and transpose-rank invariance give the usual cyclomatic
dimension formula for the binary cycle space. -/
theorem finrank_graphCycleSpace_eq_cycleRank
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Module.finrank (ZMod 2) (graphCycleSpace G) = cycleRank G := by
  classical
  let A := graphIncidenceMatrix G
  have hTranspose :
      A.rank + Fintype.card G.ConnectedComponent = Fintype.card V := by
    calc
      A.rank + Fintype.card G.ConnectedComponent =
          Aᵀ.rank + Module.finrank (ZMod 2) (LinearMap.ker Aᵀ.mulVecLin) := by
        rw [Matrix.rank_transpose, finrank_ker_graphIncidenceMatrix_transpose G]
      _ = Module.finrank (ZMod 2) (LinearMap.range Aᵀ.mulVecLin) +
          Module.finrank (ZMod 2) (LinearMap.ker Aᵀ.mulVecLin) := rfl
      _ = Module.finrank (ZMod 2) (V → ZMod 2) :=
        LinearMap.finrank_range_add_finrank_ker Aᵀ.mulVecLin
      _ = Fintype.card V := by simp
  have hOriginal :
      A.rank + Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) =
        Fintype.card G.edgeSet := by
    calc
      A.rank + Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) =
          Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) +
            Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) := rfl
      _ = Module.finrank (ZMod 2) (G.edgeSet → ZMod 2) :=
        LinearMap.finrank_range_add_finrank_ker A.mulVecLin
      _ = Fintype.card G.edgeSet := by simp
  have hTransposeNat :
      A.rank + Nat.card G.ConnectedComponent = Nat.card V := by
    simpa only [Nat.card_eq_fintype_card] using hTranspose
  have hOriginalNat :
      A.rank + Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) =
        Nat.card G.edgeSet := by
    simpa only [Nat.card_eq_fintype_card] using hOriginal
  have hDimension :
      Module.finrank (ZMod 2) (graphCycleSpace G) =
        Nat.card G.edgeSet + Nat.card G.ConnectedComponent - Nat.card V := by
    change Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) = _
    omega
  have hCycleRank :
      cycleRank G =
        Nat.card G.edgeSet + Nat.card G.ConnectedComponent - Nat.card V := by
    letI : DecidableEq V := Classical.decEq V
    letI : DecidableRel G.Adj := Classical.decRel _
    unfold cycleRank
    rw [G.edgeFinset_card]
    simp only [← Nat.card_eq_fintype_card]
  exact hDimension.trans hCycleRank.symm

/-- Consequently the binary cycle space has exactly `2 ^ cycleRank G`
elements. -/
theorem natCard_graphCycleSpace_eq_two_pow_cycleRank
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Nat.card (graphCycleSpace G) = 2 ^ cycleRank G := by
  calc
    Nat.card (graphCycleSpace G) =
        Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) (graphCycleSpace G) :=
      Module.natCard_eq_pow_finrank
    _ = 2 ^ cycleRank G := by
      rw [Nat.card_eq_fintype_card, ZMod.card,
        finrank_graphCycleSpace_eq_cycleRank]

/-- The edges of `F` incident with `v`. -/
def graphEdgeSubsetAtVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (F : Finset G.edgeSet) (v : V) : Finset G.edgeSet :=
  Finset.univ.filter fun e => e ∈ F ∧ v ∈ (e.1 : Sym2 V)

/-- Literal finite edge subsets having even degree at every vertex. -/
def EvenEdgeSubset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  {F : Finset G.edgeSet //
    ∀ v, Even (graphEdgeSubsetAtVertex F v).card}

/-- The zero-one coefficient vector of a finite edge subset. -/
def graphEdgeSubsetVector
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (F : Finset G.edgeSet) : G.edgeSet → ZMod 2 :=
  fun e => if e ∈ F then 1 else 0

/-- Applying the incidence matrix to an edge-subset indicator gives the
incident-edge cardinality modulo two at each vertex. -/
lemma graphIncidenceMatrix_mulVec_graphEdgeSubsetVector_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset G.edgeSet) (v : V) :
    (graphIncidenceMatrix G *ᵥ graphEdgeSubsetVector F) v =
      ((graphEdgeSubsetAtVertex F v).card : ZMod 2) := by
  simp only [graphIncidenceMatrix, graphEdgeSubsetVector,
    graphEdgeSubsetAtVertex, Matrix.mulVec, dotProduct, ite_mul,
    one_mul, zero_mul]
  change (∑ e, if v ∈ (e.1 : Sym2 V) then
      (if e ∈ F then (1 : ZMod 2) else 0) else 0) =
    ((Finset.univ.filter fun e => e ∈ F ∧ v ∈ (e.1 : Sym2 V)).card : ZMod 2)
  rw [← Finset.sum_filter]
  rw [Finset.sum_boole]
  have hfilter :
      ((Finset.univ.filter fun e : G.edgeSet => v ∈ (e.1 : Sym2 V)).filter
          fun e => e ∈ F) =
        Finset.univ.filter fun e => e ∈ F ∧ v ∈ (e.1 : Sym2 V) := by
    ext e
    simp [and_comm]
  rw [hfilter]

/-- The zero-one vector of `F` belongs to the binary cycle space exactly when
`F` has even degree at every vertex. -/
lemma graphEdgeSubsetVector_mem_graphCycleSpace_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset G.edgeSet) :
    graphEdgeSubsetVector F ∈ graphCycleSpace G ↔
      ∀ v, Even (graphEdgeSubsetAtVertex F v).card := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro h v
    apply ZMod.natCast_eq_zero_iff_even.mp
    rw [← graphIncidenceMatrix_mulVec_graphEdgeSubsetVector_apply G F v]
    exact congrFun h v
  · intro h
    funext v
    rw [graphIncidenceMatrix_mulVec_graphEdgeSubsetVector_apply]
    exact ZMod.natCast_eq_zero_iff_even.mpr (h v)

/-- Every nonzero coefficient in `ZMod 2` is one. -/
lemma zmodTwo_eq_one_of_ne_zero (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
  have hlt : x.val < 2 := ZMod.val_lt x
  have hval : x.val = 0 ∨ x.val = 1 := by omega
  rcases hval with hzero | hone
  · exfalso
    apply hx
    rw [← ZMod.natCast_zmod_val x, hzero]
    norm_num
  · rw [← ZMod.natCast_zmod_val x, hone]
    norm_num

/-- The support finset of a binary edge coefficient vector. -/
def graphEdgeVectorSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (x : G.edgeSet → ZMod 2) : Finset G.edgeSet :=
  Finset.univ.filter fun e => x e ≠ 0

@[simp] lemma graphEdgeVectorSupport_graphEdgeSubsetVector
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (F : Finset G.edgeSet) :
    graphEdgeVectorSupport (graphEdgeSubsetVector F) = F := by
  ext e
  simp [graphEdgeVectorSupport, graphEdgeSubsetVector]

lemma graphEdgeSubsetVector_graphEdgeVectorSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (x : G.edgeSet → ZMod 2) :
    graphEdgeSubsetVector (graphEdgeVectorSupport x) = x := by
  funext e
  by_cases he : x e = 0
  · simp [graphEdgeSubsetVector, graphEdgeVectorSupport, he]
  · have heOne : x e = 1 := zmodTwo_eq_one_of_ne_zero (x e) he
    simp [graphEdgeSubsetVector, graphEdgeVectorSupport, heOne]

/-- Literal even edge subsets are equivalent to vectors in the binary cycle
space. -/
def evenEdgeSubsetEquivGraphCycleSpace
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    EvenEdgeSubset G ≃ graphCycleSpace G where
  toFun F :=
    ⟨graphEdgeSubsetVector F.1,
      (graphEdgeSubsetVector_mem_graphCycleSpace_iff G F.1).mpr F.2⟩
  invFun x := by
    refine ⟨graphEdgeVectorSupport x.1, ?_⟩
    apply (graphEdgeSubsetVector_mem_graphCycleSpace_iff G _).mp
    rw [graphEdgeSubsetVector_graphEdgeVectorSupport]
    exact x.2
  left_inv F := by
    apply Subtype.ext
    exact graphEdgeVectorSupport_graphEdgeSubsetVector F.1
  right_inv x := by
    apply Subtype.ext
    exact graphEdgeSubsetVector_graphEdgeVectorSupport x.1

/-- Equation (6.7): the number of finite edge subsets having even degree at
every vertex is exactly `2 ^ cycleRank G`. -/
theorem natCard_evenEdgeSubset_eq_two_pow_cycleRank
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Nat.card (EvenEdgeSubset G) = 2 ^ cycleRank G := by
  rw [Nat.card_congr (evenEdgeSubsetEquivGraphCycleSpace G),
    natCard_graphCycleSpace_eq_two_pow_cycleRank]

#print axioms natCard_graphCycleSpace_eq_two_pow_cycleRank
#print axioms natCard_evenEdgeSubset_eq_two_pow_cycleRank

end

end Erdos625
