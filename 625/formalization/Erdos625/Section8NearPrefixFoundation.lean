import Erdos625.Section8NearArithmeticFoundation
import Erdos625.Section8PhysicalSkeletonFibreGrouping
import Erdos625.Section9CanonicalSupportMatching
import Mathlib.Data.ENNReal.BigOperators

/-!
# Section VIII physical near-prefix / middle-completion foundation

This is the lossless physical layer behind the near--middle split in Lemma
8.3. Its source is the repository's existing fibre

`{S : UnlabelledTypedSkeleton row col // S.typeTable = demand.1}`

over an *attained* canonical high-demand table, rather than an arbitrary pair
of a completion and a high skeleton. The row and column cap certificates are
explicit and are used to derive matchingness of the high support.

This module deliberately does **not** prove that every physical high-skeleton
fibre has an exhaustive near/middle presentation, that the resulting raw split
has the weighted no-extra-multiplicity formula of (8.25a), or that a raw middle
factor has a residual conditional law or conditional expectation. Those are
separate obligations. No field, definition, or theorem below asserts a tail
estimate or the desired final Section VIII bound.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- One existing physical high-skeleton fibre together with the explicit
ambient caps that make its attained canonical support a bipartite matching.
The `demand` field is in `canonicalDemandImage`, while `physical` is exactly
the existing physical unlabelled-skeleton fibre over that table. -/
structure CappedPhysicalHighFibre
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) (U : Nat) where
  rowCap : ∀ a, row a <= U
  colCap : ∀ b, col b <= U
  demand : canonicalDemandImage row col U
  physical :
    {S : UnlabelledTypedSkeleton row col // S.typeTable = demand.1}

/-- The positive type support of the attained high table. -/
def CappedPhysicalHighFibre.support
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    (H : CappedPhysicalHighFibre row col U) : Finset (A × B) :=
  positiveDemandSupport H.demand.1

/-- The physical fibre has exactly its attained demand table. -/
theorem CappedPhysicalHighFibre.physical_typeTable
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    (H : CappedPhysicalHighFibre row col U) :
    H.physical.1.typeTable = H.demand.1 :=
  H.physical.2

/-- The positive support read directly from the physical fibre. -/
def CappedPhysicalHighFibre.physicalSupport
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    (H : CappedPhysicalHighFibre row col U) : Finset (A × B) :=
  positiveDemandSupport H.physical.1.typeTable

/-- The explicit row and column caps derive the high-support matching fact;
it is not stored as an unverified premise on a near prefix. -/
theorem CappedPhysicalHighFibre.support_isBipartiteMatching
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    (H : CappedPhysicalHighFibre row col U) :
    IsBipartiteMatching H.support := by
  exact positiveDemandSupport_isBipartiteMatching_of_canonicalDemandImage
    U H.rowCap H.colCap H.demand

/-- The matching conclusion applies equally to the positive support of the
actual physical high-skeleton fibre, by its exact type-table equation. -/
theorem CappedPhysicalHighFibre.physicalSupport_isBipartiteMatching
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    (H : CappedPhysicalHighFibre row col U) :
    IsBipartiteMatching H.physicalSupport := by
  change IsBipartiteMatching (positiveDemandSupport H.physical.1.typeTable)
  rw [H.physical_typeTable]
  exact H.support_isBipartiteMatching

/-- A physical near prefix of one capped physical high-skeleton fibre. It
uses genuine physical edges of that fibre; whenever it enters a cell, it takes
the whole cell, and that cell is in the explicit near window. -/
structure NearPrefix
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    (endpoint : A -> B -> Nat)
    (H : CappedPhysicalHighFibre row col U) where
  physical : UnlabelledTypedSkeleton row col
  edge_subset : physical.edges ⊆ H.physical.1.edges
  whole_cell_of_present : ∀ a b,
    physical.typeTable a b ≠ 0 ->
      physical.typeTable a b = H.physical.1.typeTable a b
  near_of_present : ∀ a b,
    physical.typeTable a b ≠ 0 ->
      NearEntry (endpoint a b) (H.demand.1 a b)

/-- Restore each selected near cell to its endpoint multiplicity. This is a
raw table annotation, not an endpoint-table probability weight. -/
def NearPrefix.endpointTable
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    {endpoint : A -> B -> Nat}
    {H : CappedPhysicalHighFibre row col U}
    (P : NearPrefix endpoint H) : A -> B -> Nat :=
  fun a b => if P.physical.typeTable a b = 0 then 0 else endpoint a b

/-- The literal cellwise deficit of a near prefix. -/
def NearPrefix.deficit
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    {endpoint : A -> B -> Nat}
    {H : CappedPhysicalHighFibre row col U}
    (P : NearPrefix endpoint H) : A -> B -> Nat :=
  fun a b => P.endpointTable a b - P.physical.typeTable a b

/-- The total finite near deficit; this is only an integer statistic. -/
def NearPrefix.totalDeficit
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    {endpoint : A -> B -> Nat}
    {H : CappedPhysicalHighFibre row col U}
    (P : NearPrefix endpoint H) : Nat :=
  Finset.univ.sum fun a =>
    Finset.univ.sum fun b => P.deficit a b

/-- The literal remaining row-stub mass after exposing physical near edges.
It is not an asserted large- or small-residual regime. -/
def NearPrefix.residualMass
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    {endpoint : A -> B -> Nat}
    {H : CappedPhysicalHighFibre row col U}
    (P : NearPrefix endpoint H) : Nat :=
  Finset.univ.sum row - P.physical.edges.card

/-- Every near nonzero cell of the attained high table has already been put
in the physical prefix. This is the exact no-further-near condition before
one later constructs a residual configuration-model bridge. -/
def NoFurtherNear
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    (endpoint : A -> B -> Nat)
    (H : CappedPhysicalHighFibre row col U)
    (P : NearPrefix endpoint H) : Prop :=
  ∀ a b,
    H.demand.1 a b ≠ 0 ->
      NearEntry (endpoint a b) (H.demand.1 a b) ->
        P.physical.typeTable a b ≠ 0

/-- A completed raw near--middle split of a capped physical high-skeleton
fibre. The complement below is determined by the source high skeleton, so a
second freely chosen middle skeleton cannot introduce multiplicity. -/
structure NearCompletion
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) (U : Nat)
    (endpoint : A -> B -> Nat) where
  high : CappedPhysicalHighFibre row col U
  nearPrefix : NearPrefix endpoint high
  no_further_near : NoFurtherNear endpoint high nearPrefix

/-- The physical middle-high complement of a completed raw split. -/
def NearCompletion.middleHighEdges
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    {endpoint : A -> B -> Nat}
    (C : NearCompletion row col U endpoint) :
    Finset (RowStub row × ColumnStub col) :=
  C.high.physical.1.edges \ C.nearPrefix.physical.edges

/-- The middle multiplicity table, formed by removing the whole-cell near
prefix from the existing physical high-skeleton fibre. -/
def NearCompletion.middleTable
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    {endpoint : A -> B -> Nat}
    (C : NearCompletion row col U endpoint) : A -> B -> Nat :=
  fun a b => C.high.demand.1 a b - C.nearPrefix.physical.typeTable a b

/-- The raw finite indicator of the no-further-near condition. It is an
integrand component only: it is not a conditional probability. -/
noncomputable def noFurtherNearIndicator
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    {endpoint : A -> B -> Nat}
    (H : CappedPhysicalHighFibre row col U)
    (P : NearPrefix endpoint H) : ENNReal := by
  classical
  exact if NoFurtherNear endpoint H P then 1 else 0

/-- The raw product of supplied cell factors over actual middle cells of an
attained high table. This is deliberately neither named nor typed as a
conditional expectation. -/
noncomputable def rawMiddleCellProduct
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    {endpoint : A -> B -> Nat}
    (g : Nat -> ENNReal)
    (H : CappedPhysicalHighFibre row col U) : ENNReal := by
  classical
  exact Finset.univ.prod (fun a =>
    Finset.univ.prod (fun b =>
      if MiddleEntry (endpoint a b) (H.demand.1 a b)
      then g (H.demand.1 a b) else 1))

/-- The literal raw factor available before any residual probability law is
constructed. Later work may integrate this factor against a proved law, but
this definition itself performs no conditioning or expectation. -/
noncomputable def rawMiddleIntegrand
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    {endpoint : A -> B -> Nat}
    (g : Nat -> ENNReal)
    (H : CappedPhysicalHighFibre row col U)
    (P : NearPrefix endpoint H) : ENNReal :=
  noFurtherNearIndicator (endpoint := endpoint) H P *
    rawMiddleCellProduct (endpoint := endpoint) g H

/-- Raw lossless endpoint--near--middle data. The source high skeleton is
not copied: its physical edge set must be reconstructed from the disjoint
near/middle edge decomposition. -/
structure RawNearMiddleData
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) where
  endpointTable : A -> B -> Nat
  nearDeficit : A -> B -> Nat
  nearEdges : Finset (RowStub row × ColumnStub col)
  middleHighEdges : Finset (RowStub row × ColumnStub col)

/-- Encode a completed physical near split as raw endpoint, near, and middle
data. The intended injectivity proof reconstructs the physical high fibre by
`nearEdges ∪ middleHighEdges`; no weighted factor occurs here. -/
def encodeRawNearMiddle
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    (endpoint : A -> B -> Nat)
    (C : NearCompletion row col U endpoint) :
    RawNearMiddleData row col where
  endpointTable := C.nearPrefix.endpointTable
  nearDeficit := C.nearPrefix.deficit
  nearEdges := C.nearPrefix.physical.edges
  middleHighEdges := C.middleHighEdges

/-- Reconstruct the physical high edge set from a raw encoding. -/
def RawNearMiddleData.reconstructedHighEdges
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat}
    (D : RawNearMiddleData row col) :
    Finset (RowStub row × ColumnStub col) :=
  D.nearEdges ∪ D.middleHighEdges

/-- The finite image used only after the raw encoding has been established.
It has no weight or cardinality assertion built into it. -/
noncomputable def rawNearMiddleImage
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} {U : Nat}
    (endpoint : A -> B -> Nat)
    (s : Finset (NearCompletion row col U endpoint)) :
    Finset (RawNearMiddleData row col) := by
  classical
  exact s.image (encodeRawNearMiddle endpoint)

end

end Erdos625
