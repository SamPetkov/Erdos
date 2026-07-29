import Erdos625.Section8DirectHalfDeficitAssembly
import Erdos625.Section8EndpointDecoratedReferenceIdentification
import Mathlib.Tactic

/-!
# Section VIII: direct grouping of full-support references

The zero-deficit reference of a block support should not be reconstructed by a
second cardinality argument.  Define it literally as the sum of the common
full-cell atom over every independent full stub matching in the selected block
cells.

The ambient type of all `Nat`-valued four-by-four tables is infinite.  The
correct finite index is therefore the image of the finite block-support space.
The total space of decorated supports is tautologically equivalent to the
dependent sum over these attained endpoint tables of the already defined
`FourEndpointDecoratedBlockPairing` fibres.

Consequently the total reference sum is exactly the finite attained-table sum
of `fourEndpointW`.  No endpoint transport inequality or asymptotic estimate is
asserted here.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

local instance : DecidableEq FourEndpointFullTable := Classical.decEq _

/-- The endpoint table carried by one abstract block support. -/
def fourEndpointSupportTable
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k) :
    FourEndpointFullTable where
  toFun := P.typeTable

/-- Regard an abstract support as a block pairing over its own endpoint table. -/
def fourEndpointBlockPairingOfSupport
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k) :
    FourEndpointBlockPairing alpha hAlpha k
      (fourEndpointSupportTable alpha hAlpha P) :=
  ⟨P, rfl⟩

/-- Independent full-cell physical stub matchings on one abstract support. -/
abbrev FourEndpointFullDecorationOfSupport
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k) :=
  ∀ e : ↥P.edges,
    SingleCellStubMatching
      (fourEndpointSize alpha hAlpha e.1.1.1)
      (fourEndpointSize alpha hAlpha e.1.2.1)
      (fourEndpointOverlapSize alpha hAlpha e.1.1.1 e.1.2.1)

/-- All block supports, decorated by literal full-cell physical matchings. -/
abbrev FourEndpointAllDecoratedSupport
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) :=
  Σ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
    FourEndpointFullDecorationOfSupport alpha hAlpha P

/-- The finite image of the block-support space in the endpoint-table space. -/
noncomputable def fourEndpointAttainedFullTables
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) : Finset FourEndpointFullTable :=
  Finset.univ.image
    (fun P : FourEndpointAbstractBlockSkeleton alpha hAlpha k =>
      fourEndpointSupportTable alpha hAlpha P)

/-- An endpoint table that is actually carried by at least one abstract block
support.  This is the finite table type relevant to the reference sum. -/
abbrev FourEndpointAttainedFullTable
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) :=
  ↥(fourEndpointAttainedFullTables alpha hAlpha k)

/-- The total decorated-support space is exactly the dependent sum of the
attained endpoint-table fibres. -/
def fourEndpointAllDecoratedSupportEquivSigmaTable
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) :
    FourEndpointAllDecoratedSupport alpha hAlpha k ≃
      Σ L : FourEndpointAttainedFullTable alpha hAlpha k,
        FourEndpointDecoratedBlockPairing alpha hAlpha k L.1 where
  toFun z :=
    let L : FourEndpointAttainedFullTable alpha hAlpha k :=
      ⟨fourEndpointSupportTable alpha hAlpha z.1,
        Finset.mem_image.mpr ⟨z.1, Finset.mem_univ z.1, rfl⟩⟩
    ⟨L, ⟨fourEndpointBlockPairingOfSupport alpha hAlpha z.1, z.2⟩⟩
  invFun z := ⟨z.2.1.1, z.2.2⟩
  left_inv z := rfl
  right_inv := by
    rintro ⟨⟨L, hL⟩, ⟨P, hP⟩, decoration⟩
    have htable : fourEndpointSupportTable alpha hAlpha P = L := by
      apply FourEndpointFullTable.ext
      exact hP
    subst L
    rfl

/-- The common atom attached to every full physical decoration of one support. -/
def fourEndpointFullSupportAtomWeight
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k) : ENNReal :=
  fourEndpointDecoratedReferenceAtomWeight n alpha hAlpha
    (fourEndpointSupportTable alpha hAlpha P)

/-- Aggregate zero-deficit reference weight of one block support. -/
def fourEndpointFullSupportReferenceWeight
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k) : ENNReal :=
  ∑ _ : FourEndpointFullDecorationOfSupport alpha hAlpha P,
    fourEndpointFullSupportAtomWeight n alpha hAlpha P

/-- Direct reference grouping: summing literal full-support reference weights
over all block supports gives exactly the finite attained endpoint-table sum. -/
theorem sum_fourEndpointFullSupportReferenceWeight_eq_sum_attained_W
    (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) :
    (∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
      fourEndpointFullSupportReferenceWeight n alpha hAlpha P) =
      ∑ L : FourEndpointAttainedFullTable alpha hAlpha k,
        fourEndpointW n alpha hAlpha k L.1 := by
  let equivalence :=
    fourEndpointAllDecoratedSupportEquivSigmaTable alpha hAlpha k
  let targetWeight :
      (Σ L : FourEndpointAttainedFullTable alpha hAlpha k,
        FourEndpointDecoratedBlockPairing alpha hAlpha k L.1) → ENNReal :=
    fun z => fourEndpointDecoratedReferenceAtomWeight n alpha hAlpha z.1.1
  calc
    (∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
        fourEndpointFullSupportReferenceWeight n alpha hAlpha P) =
      ∑ z : FourEndpointAllDecoratedSupport alpha hAlpha k,
        fourEndpointFullSupportAtomWeight n alpha hAlpha z.1 := by
          rw [Fintype.sum_sigma]
          rfl
    _ = ∑ z : FourEndpointAllDecoratedSupport alpha hAlpha k,
          targetWeight (equivalence z) := by
      apply Finset.sum_congr rfl
      intro z _
      rfl
    _ = ∑ z : Σ L : FourEndpointAttainedFullTable alpha hAlpha k,
          FourEndpointDecoratedBlockPairing alpha hAlpha k L.1,
        targetWeight z :=
      equivalence.sum_comp targetWeight
    _ = ∑ L : FourEndpointAttainedFullTable alpha hAlpha k,
          ∑ _ : FourEndpointDecoratedBlockPairing alpha hAlpha k L.1,
            fourEndpointDecoratedReferenceAtomWeight n alpha hAlpha L.1 := by
          rw [Fintype.sum_sigma]
          rfl
    _ = ∑ L : FourEndpointAttainedFullTable alpha hAlpha k,
          fourEndpointW n alpha hAlpha k L.1 := by
      apply Finset.sum_congr rfl
      intro L _
      exact sum_fourEndpointDecoratedReferenceAtomWeight_eq_fourEndpointW
        n alpha hAlpha k L.1

#print axioms fourEndpointAllDecoratedSupportEquivSigmaTable
#print axioms sum_fourEndpointFullSupportReferenceWeight_eq_sum_attained_W

end

end Erdos625
