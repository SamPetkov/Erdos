import Erdos625.OrderedSignedProfileBridge
import Erdos625.Section8UnlabelledTypedSkeleton
import Erdos625.SignedFourSizeObjective
import Erdos625.LocalSignReward
import Erdos625.EndpointTransportBounds
import Mathlib.Tactic

/-!
# Section VIII: four-type endpoint foundation

This module keeps two incompatible notions of endpoint table apart:

* `FourEndpointStubTable` records sums of literal physical stub incidences;
* `FourEndpointFullTable` records counts of block-slot pairs whose physical
  cell has full-containment multiplicity `min u_i u_j`.

The manuscript table `ell_ij` in (8.5)--(8.6) is the second object. There is
no coercion between the newtypes and no equality between them is assumed.
The module defines finite data only; it does not assert the remaining
canonical-demand, transportation comparison, or asymptotic endpoint bounds.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- Raw endpoint-type incidences measured in *stub pairs*. -/
structure FourEndpointStubTable where
  toFun : Fin 4 -> Fin 4 -> Nat

namespace FourEndpointStubTable

/-- Equality of raw tables is extensional equality of their entries. -/
@[ext] theorem ext {table table' : FourEndpointStubTable}
    (h : table.toFun = table'.toFun) : table = table' := by
  cases table
  cases table'
  cases h
  rfl

end FourEndpointStubTable

/-- Manuscript endpoint table `ell_ij`, measured in full-containment
*block-slot pairs*. -/
structure FourEndpointFullTable where
  toFun : Fin 4 -> Fin 4 -> Nat

namespace FourEndpointFullTable

/-- Equality of full-cell tables is extensional equality of their entries. -/
@[ext] theorem ext {table table' : FourEndpointFullTable}
    (h : table.toFun = table'.toFun) : table = table' := by
  cases table
  cases table'
  cases h
  rfl

end FourEndpointFullTable

/-- The profile coordinate carrying deficit `2 + i`. -/
def fourEndpointCoordinate (alpha : Nat) (hAlpha : 5 < alpha) (i : Fin 4) :
    Fin (alpha + 1) :=
  fourDeficitCoordinate alpha hAlpha i

/-- Endpoint size `u_i`. -/
def fourEndpointSize (alpha : Nat) (hAlpha : 5 < alpha) (i : Fin 4) : Nat :=
  (fourEndpointCoordinate alpha hAlpha i).val + 1

/-- Endpoint multiplicity `k_i` at the actual four-size coordinate. -/
def fourEndpointMultiplicity (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (i : Fin 4) : Nat :=
  k (fourEndpointCoordinate alpha hAlpha i)

/-- The profile block slots whose block size is `u_i`. -/
noncomputable def fourEndpointBlockSlots (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (i : Fin 4) :
    Finset (ProfileBlockIndex k) := by
  classical
  exact Finset.univ.filter (fun q =>
    profileBlockMargin k q = fourEndpointSize alpha hAlpha i)

/-- Number of stub pairs in one full-containment endpoint cell. -/
def fourEndpointOverlapSize (alpha : Nat) (hAlpha : 5 < alpha)
    (i j : Fin 4) : Nat :=
  min (fourEndpointSize alpha hAlpha i) (fourEndpointSize alpha hAlpha j)

/-- Aggregate a literal block-slot table by endpoint type as raw stub totals. -/
noncomputable def fourEndpointStubTableOfBlockTypeTable
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (T : ProfileBlockIndex k -> ProfileBlockIndex k -> Nat) :
    FourEndpointStubTable where
  toFun i j :=
    (fourEndpointBlockSlots alpha hAlpha k i).sum fun a =>
      (fourEndpointBlockSlots alpha hAlpha k j).sum fun b => T a b

/-- Aggregate a literal block-slot table to the manuscript full-cell table. -/
noncomputable def fourEndpointFullTableOfBlockTypeTable
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (T : ProfileBlockIndex k -> ProfileBlockIndex k -> Nat) :
    FourEndpointFullTable where
  toFun i j :=
    (((fourEndpointBlockSlots alpha hAlpha k i).product
      (fourEndpointBlockSlots alpha hAlpha k j)).filter
        (fun ab => T ab.1 ab.2 = fourEndpointOverlapSize alpha hAlpha i j)).card

/-- Row margin `r_i` of a manuscript full-cell table. -/
def fourEndpointRowMargin (L : FourEndpointFullTable) (i : Fin 4) : Nat :=
  Finset.univ.sum fun j => L.toFun i j

/-- Column margin `c_j` of a manuscript full-cell table. -/
def fourEndpointColumnMargin (L : FourEndpointFullTable) (j : Fin 4) : Nat :=
  Finset.univ.sum fun i => L.toFun i j

/-- Feasibility for the endpoint transportation table. -/
def FourEndpointFeasible (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) : Prop :=
  (forall i, fourEndpointRowMargin L i <=
      fourEndpointMultiplicity alpha hAlpha k i) /\
    (forall j, fourEndpointColumnMargin L j <=
      fourEndpointMultiplicity alpha hAlpha k j)

/-- `J(L)` in (8.5). -/
def fourEndpointJ (alpha : Nat) (hAlpha : 5 < alpha)
    (L : FourEndpointFullTable) : Nat :=
  Finset.univ.sum fun i =>
    Finset.univ.sum fun j =>
      fourEndpointOverlapSize alpha hAlpha i j * L.toFun i j

/-- The exact `|i-j|` displacement in (8.11). -/
def fourEndpointDisplacement (L : FourEndpointFullTable) : Nat :=
  Finset.univ.sum fun i =>
    Finset.univ.sum fun j => Nat.dist i.val j.val * L.toFun i j

/-- Vertex/stub mass carried by a one-sided endpoint margin. -/
def fourEndpointMarginMass (alpha : Nat) (hAlpha : 5 < alpha)
    (r : Fin 4 -> Nat) : Nat :=
  Finset.univ.sum fun i => fourEndpointSize alpha hAlpha i * r i

def fourEndpointRowMass (alpha : Nat) (hAlpha : 5 < alpha)
    (L : FourEndpointFullTable) : Nat :=
  fourEndpointMarginMass alpha hAlpha (fun i => fourEndpointRowMargin L i)

def fourEndpointColumnMass (alpha : Nat) (hAlpha : 5 < alpha)
    (L : FourEndpointFullTable) : Nat :=
  fourEndpointMarginMass alpha hAlpha (fun j => fourEndpointColumnMargin L j)

/-- The arithmetic facts needed to turn (8.11) into global transport. -/
def FourEndpointMassFacts (alpha : Nat) (hAlpha : 5 < alpha)
    (L : FourEndpointFullTable) : Prop :=
  fourEndpointJ alpha hAlpha L <= fourEndpointRowMass alpha hAlpha L /\
    fourEndpointJ alpha hAlpha L <= fourEndpointColumnMass alpha hAlpha L /\
      fourEndpointRowMass alpha hAlpha L +
          fourEndpointColumnMass alpha hAlpha L =
        2 * fourEndpointJ alpha hAlpha L + fourEndpointDisplacement L

/-- The sole `prod ell_ij!` denominator in (8.6). -/
def fourEndpointCellFactorialProduct (L : FourEndpointFullTable) : Nat :=
  Finset.univ.prod fun i =>
    Finset.univ.prod fun j => (L.toFun i j).factorial

/-- `prod_i r_i!` in the manuscript `D(r)`. -/
def fourEndpointMarginFactorialProduct (r : Fin 4 -> Nat) : Nat :=
  Finset.univ.prod fun i => (r i).factorial

/-- `prod_i (k_i)_(r_i)`. -/
def fourEndpointMarginSelectionProduct (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (r : Fin 4 -> Nat) : Nat :=
  Finset.univ.prod fun i =>
    (fourEndpointMultiplicity alpha hAlpha k i).descFactorial (r i)

def fourEndpointRowSelectionProduct (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) : Nat :=
  fourEndpointMarginSelectionProduct alpha hAlpha k
    (fun i => fourEndpointRowMargin L i)

def fourEndpointColumnSelectionProduct (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) : Nat :=
  fourEndpointMarginSelectionProduct alpha hAlpha k
    (fun j => fourEndpointColumnMargin L j)

/-- The diagonal local term `u_i! g(u_i)` in (8.7). -/
noncomputable def fourEndpointDiagonalLocalFactor (alpha : Nat)
    (hAlpha : 5 < alpha) (i : Fin 4) : ENNReal :=
  ((fourEndpointSize alpha hAlpha i).factorial : ENNReal) *
    (localSignRewardNat (fourEndpointSize alpha hAlpha i) : ENNReal)

noncomputable def fourEndpointDiagonalLocalProduct (alpha : Nat)
    (hAlpha : 5 < alpha) (r : Fin 4 -> Nat) : ENNReal :=
  Finset.univ.prod fun i =>
    (fourEndpointDiagonalLocalFactor alpha hAlpha i) ^ r i

/-- The manuscript common-subprofile weight `D(r)` from (8.7). -/
noncomputable def fourEndpointD (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (r : Fin 4 -> Nat) : ENNReal :=
  ((((fourEndpointMarginSelectionProduct alpha hAlpha k r : Nat) : ENNReal) ^ 2 /
      (fourEndpointMarginFactorialProduct r : ENNReal)) *
    (fourEndpointDiagonalLocalProduct alpha hAlpha r /
      ((n.descFactorial (fourEndpointMarginMass alpha hAlpha r) : Nat) :
        ENNReal)))

/-- One local full-cell factor in `W(L)`. -/
noncomputable def fourEndpointLocalCellFactor (alpha : Nat)
    (hAlpha : 5 < alpha) (i j : Fin 4) : ENNReal :=
  let x := fourEndpointOverlapSize alpha hAlpha i j
  (((fourEndpointSize alpha hAlpha i).descFactorial x : ENNReal) *
      ((fourEndpointSize alpha hAlpha j).descFactorial x : ENNReal) /
        (x.factorial : ENNReal)) *
    (localSignRewardNat x : ENNReal)

noncomputable def fourEndpointLocalProduct (alpha : Nat) (hAlpha : 5 < alpha)
    (L : FourEndpointFullTable) : ENNReal :=
  Finset.univ.prod fun i => Finset.univ.prod fun j =>
    (fourEndpointLocalCellFactor alpha hAlpha i j) ^ L.toFun i j

/-- The exact endpoint weight `W(L)` from (8.6), excluding residual
attachments. Its ENNReal form is total; feasibility remains separate. -/
noncomputable def fourEndpointW (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) : ENNReal :=
  ((((fourEndpointRowSelectionProduct alpha hAlpha k L : Nat) : ENNReal) *
      ((fourEndpointColumnSelectionProduct alpha hAlpha k L : Nat) : ENNReal) /
        (fourEndpointCellFactorialProduct L : ENNReal) /
          ((n.descFactorial (fourEndpointJ alpha hAlpha L) : Nat) : ENNReal)) *
    fourEndpointLocalProduct alpha hAlpha L)

/-- Endpoint type distance `d = |i-j|`. -/
def fourEndpointDistance (i j : Fin 4) : Nat := Nat.dist i.val j.val

def fourEndpointLowerSize (alpha : Nat) (hAlpha : 5 < alpha)
    (i j : Fin 4) : Nat :=
  min (fourEndpointSize alpha hAlpha i) (fourEndpointSize alpha hAlpha j)

def fourEndpointUpperSize (alpha : Nat) (hAlpha : 5 < alpha)
    (i j : Fin 4) : Nat :=
  max (fourEndpointSize alpha hAlpha i) (fourEndpointSize alpha hAlpha j)

/-- The finite `Q_ij` expression in (8.9), defined before any inequality. -/
noncomputable def fourEndpointQ (n alpha : Nat) (hAlpha : 5 < alpha)
    (i j : Fin 4) : Real :=
  Real.rpow ((n + 1 : Nat) : Real) ((fourEndpointDistance i j : Real) / 2) *
    Real.sqrt ((fourEndpointUpperSize alpha hAlpha i j).descFactorial
      (fourEndpointDistance i j) : Real) /
      (fourEndpointDistance i j).factorial *
        Real.rpow 2
          (-((fourEndpointDistance i j * fourEndpointLowerSize alpha hAlpha i j +
            (fourEndpointDistance i j).choose 2 : Nat) : Real) / 2)

/-- Full endpoint block pairs in a literal physical skeleton. -/
noncomputable def fourEndpointFullPairs (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (S : UnlabelledTypedSkeleton (profileBlockMargin k) (profileBlockMargin k)) :
    Finset (Prod (ProfileBlockIndex k) (ProfileBlockIndex k)) := by
  classical
  exact (Finset.univ.product Finset.univ).filter fun ab =>
    exists i j, ab.1 ∈ fourEndpointBlockSlots alpha hAlpha k i /\
      ab.2 ∈ fourEndpointBlockSlots alpha hAlpha k j /\
        S.typeTable ab.1 ab.2 = fourEndpointOverlapSize alpha hAlpha i j

/-- Every physical edge is in a full endpoint cell. -/
def IsFourEndpointOnlyPhysicalSkeleton (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (S : UnlabelledTypedSkeleton (profileBlockMargin k) (profileBlockMargin k)) :
    Prop :=
  forall e, e ∈ S.edges ->
    exists i j, e.1.1 ∈ fourEndpointBlockSlots alpha hAlpha k i /\
      e.2.1 ∈ fourEndpointBlockSlots alpha hAlpha k j /\
        S.typeTable e.1.1 e.2.1 = fourEndpointOverlapSize alpha hAlpha i j

/-- The endpoint high-cell threshold `floor(u_max / 2)`. -/
def fourEndpointHighCutoff (alpha : Nat) (hAlpha : 5 < alpha) : Nat :=
  fourEndpointSize alpha hAlpha (0 : Fin 4) / 2

/-- Canonical-high form of an endpoint-only physical skeleton. -/
def IsCanonicalHighFourEndpointSkeleton (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (S : UnlabelledTypedSkeleton (profileBlockMargin k) (profileBlockMargin k)) :
    Prop :=
  IsFourEndpointOnlyPhysicalSkeleton alpha hAlpha k S /\
    (forall ab, ab ∈ fourEndpointFullPairs alpha hAlpha k S ->
      fourEndpointHighCutoff alpha hAlpha < S.typeTable ab.1 ab.2)

/-- Block-level matching for full endpoint pairs. -/
def FourEndpointFullPairsAreMatching (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (S : UnlabelledTypedSkeleton (profileBlockMargin k) (profileBlockMargin k)) :
    Prop :=
  (forall a b1 b2,
      (a, b1) ∈ fourEndpointFullPairs alpha hAlpha k S ->
      (a, b2) ∈ fourEndpointFullPairs alpha hAlpha k S -> b1 = b2) /\
    (forall a1 a2 b,
      (a1, b) ∈ fourEndpointFullPairs alpha hAlpha k S ->
      (a2, b) ∈ fourEndpointFullPairs alpha hAlpha k S -> a1 = a2)

/-- Endpoint-only and block-matching physical skeletons. -/
def IsFourEndpointPhysicalSkeleton (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (S : UnlabelledTypedSkeleton (profileBlockMargin k) (profileBlockMargin k)) :
    Prop :=
  IsFourEndpointOnlyPhysicalSkeleton alpha hAlpha k S /\
    FourEndpointFullPairsAreMatching alpha hAlpha k S

abbrev FourEndpointPhysicalSkeleton (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) :=
  {S : UnlabelledTypedSkeleton (profileBlockMargin k) (profileBlockMargin k) //
    IsFourEndpointPhysicalSkeleton alpha hAlpha k S}

/-- Fibre over a specified full-cell table; generic image/fibre partitioning is
intentionally not promoted to a theorem. -/
abbrev FourEndpointPhysicalFibre (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) :=
  {S : FourEndpointPhysicalSkeleton alpha hAlpha k //
    fourEndpointFullTableOfBlockTypeTable alpha hAlpha k S.1.typeTable = L}

noncomputable instance instFintypeFourEndpointPhysicalFibre
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable) :
    Fintype (FourEndpointPhysicalFibre alpha hAlpha k L) := by
  classical
  exact Fintype.ofFinite _

/-- Local reward read from literal full cells of a physical fibre member. -/
noncomputable def fourEndpointPhysicalLocalReward (alpha : Nat)
    (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (S : FourEndpointPhysicalFibre alpha hAlpha k L) : ENNReal :=
  (fourEndpointFullPairs alpha hAlpha k S.1.1).prod fun ab =>
    (localSignRewardNat (S.1.1.typeTable ab.1 ab.2) : ENNReal)

/-- Per-physical-skeleton contribution whose fibre sum is the exact (8.6)
target. -/
noncomputable def fourEndpointPhysicalWitnessWeight (n alpha : Nat)
    (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (S : FourEndpointPhysicalFibre alpha hAlpha k L) : ENNReal :=
  fourEndpointPhysicalLocalReward alpha hAlpha k L S /
    ((n.descFactorial (fourEndpointJ alpha hAlpha L) : Nat) : ENNReal)

end

end Erdos625
