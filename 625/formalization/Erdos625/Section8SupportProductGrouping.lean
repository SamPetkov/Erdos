import Erdos625.Section8DirectReferenceGrouping
import Erdos625.Section8SymmetricLocalDeficitRatio
import Mathlib.Tactic

/-!
# Section VIII: support products grouped by endpoint type

A block support is a finite matching whose edges carry one of sixteen endpoint
coordinate pairs.  Products and sums over selected physical block pairs can
therefore be regrouped by the support's `4 x 4` type table.

This module extracts that finite identity from the decorated-pairing count and
uses it to rewrite the zero-deficit reference of one support as the literal
product of full one-cell weighted counts times the single ambient reciprocal
falling factorial.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Product over support edges, grouped by their endpoint types. -/
theorem fourEndpointSupport_prod_by_type
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k)
    {R : Type*} [CommMonoid R]
    (f : Fin 4 → Fin 4 → R) :
    (∏ e : ↥P.edges, f e.1.1.1 e.1.2.1) =
      ∏ i : Fin 4, ∏ j : Fin 4, (f i j) ^ P.typeTable i j := by
  rw [← Finset.prod_subtype P.edges (fun _ => Iff.rfl)
    (fun e => f e.1.1 e.2.1)]
  rw [← Finset.prod_fiberwise' P.edges
    (fun e => (e.1.1, e.2.1))
    (fun ij : Fin 4 × Fin 4 => f ij.1 ij.2)]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  rw [Finset.prod_const]
  apply congrArg (fun count => (f i j) ^ count)
  calc
    (P.edges.filter fun e => (e.1.1, e.2.1) = (i, j)).card =
        (P.edges.filter fun e => e.1.1 = i ∧ e.2.1 = j).card := by
      congr 1
      ext e
      simp [Prod.ext_iff]
    _ = P.typeTable i j := rfl

/-- Sum over support edges, grouped by endpoint type. -/
theorem fourEndpointSupport_sum_by_type
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k)
    {R : Type*} [AddCommMonoid R]
    (f : Fin 4 → Fin 4 → R) :
    (∑ e : ↥P.edges, f e.1.1.1 e.1.2.1) =
      ∑ i : Fin 4, ∑ j : Fin 4, P.typeTable i j • f i j := by
  rw [← Finset.sum_subtype P.edges (fun _ => Iff.rfl)
    (fun e => f e.1.1 e.2.1)]
  rw [← Finset.sum_fiberwise' P.edges
    (fun e => (e.1.1, e.2.1))
    (fun ij : Fin 4 × Fin 4 => f ij.1 ij.2)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_const]
  congr 1
  calc
    (P.edges.filter fun e => (e.1.1, e.2.1) = (i, j)).card =
        (P.edges.filter fun e => e.1.1 = i ∧ e.2.1 = j).card := by
      congr 1
      ext e
      simp [Prod.ext_iff]
    _ = P.typeTable i j := rfl

/-- Full exposed multiplicity of one support. -/
def fourEndpointSupportFullTotalMultiplicity
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k) : Nat :=
  ∑ e : ↥P.edges,
    fourEndpointOverlapSize alpha hAlpha e.1.1.1 e.1.2.1

/-- The edgewise total equals `J` of the support's endpoint table. -/
theorem fourEndpointSupportFullTotalMultiplicity_eq_J
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k) :
    fourEndpointSupportFullTotalMultiplicity alpha hAlpha P =
      fourEndpointJ alpha hAlpha
        (fourEndpointSupportTable alpha hAlpha P) := by
  simpa [fourEndpointSupportFullTotalMultiplicity, fourEndpointJ,
    fourEndpointSupportTable, nsmul_eq_mul, Nat.cast_id, mul_comm] using
      (fourEndpointSupport_sum_by_type alpha hAlpha P
        (fun i j => fourEndpointOverlapSize alpha hAlpha i j))

/-- Product of full weighted one-cell counts on a support. -/
def fourEndpointSupportFullCellWeightProduct
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k) : ENNReal :=
  ∏ e : ↥P.edges,
    (endpointCellWeightedCount
      (fourEndpointSize alpha hAlpha e.1.1.1)
      (fourEndpointSize alpha hAlpha e.1.2.1)
      (fourEndpointOverlapSize alpha hAlpha e.1.1.1 e.1.2.1) : Nat)

/-- Cardinality of all full local stub decorations equals the product of the
one-cell cardinalities. -/
theorem card_fourEndpointFullDecorationOfSupport
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k) :
    Fintype.card (FourEndpointFullDecorationOfSupport alpha hAlpha P) =
      ∏ e : ↥P.edges,
        Fintype.card (SingleCellStubMatching
          (fourEndpointSize alpha hAlpha e.1.1.1)
          (fourEndpointSize alpha hAlpha e.1.2.1)
          (fourEndpointOverlapSize alpha hAlpha e.1.1.1 e.1.2.1)) := by
  rw [Fintype.card_pi]

/-- The table reward product is the edgewise product of local rewards. -/
theorem fourEndpointFullRewardProduct_supportTable
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k) :
    fourEndpointFullRewardProduct alpha hAlpha
        (fourEndpointSupportTable alpha hAlpha P) =
      ∏ e : ↥P.edges,
        (localSignRewardNat
          (fourEndpointOverlapSize alpha hAlpha e.1.1.1 e.1.2.1) : ENNReal) := by
  unfold fourEndpointFullRewardProduct fourEndpointSupportTable
  symm
  exact fourEndpointSupport_prod_by_type alpha hAlpha P
    (fun i j =>
      (localSignRewardNat
        (fourEndpointOverlapSize alpha hAlpha i j) : ENNReal))

/-- Exact algebraic form of the full-support reference weight. -/
theorem fourEndpointFullSupportReferenceWeight_eq_cellProduct
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k) :
    fourEndpointFullSupportReferenceWeight n alpha hAlpha P =
      fourEndpointSupportFullCellWeightProduct alpha hAlpha P *
        (((n.descFactorial
          (fourEndpointSupportFullTotalMultiplicity alpha hAlpha P) : Nat) :
            ENNReal)⁻¹) := by
  unfold fourEndpointFullSupportReferenceWeight
    fourEndpointFullSupportAtomWeight
    fourEndpointDecoratedReferenceAtomWeight
    fourEndpointSupportFullCellWeightProduct
    endpointCellWeightedCount
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_fourEndpointFullDecorationOfSupport]
  rw [fourEndpointFullRewardProduct_supportTable]
  rw [← fourEndpointSupportFullTotalMultiplicity_eq_J]
  simp only [div_eq_mul_inv, Nat.cast_prod, Nat.cast_mul]
  rw [Finset.prod_mul_distrib]
  ring

#print axioms fourEndpointSupport_prod_by_type
#print axioms fourEndpointSupport_sum_by_type
#print axioms fourEndpointSupportFullTotalMultiplicity_eq_J
#print axioms fourEndpointFullSupportReferenceWeight_eq_cellProduct

end

end Erdos625
