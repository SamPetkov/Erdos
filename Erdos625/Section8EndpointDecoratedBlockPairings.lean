import Erdos625.Section8EndpointProfileIndexing
import Erdos625.Section8EndpointBlockPairings
import Erdos625.Section8EndpointSingleCellStubs
import Mathlib.Tactic

/-!
# Decorated endpoint block-pairing cardinality

This module isolates the independent full-cell stub decorations of a selected
endpoint block pairing. It proves no equivalence with the manuscript's full
physical fibre, no reward constancy, and no probability or asymptotic bound.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- A canonical numbering of the endpoint blocks of each of the four sizes. -/
abbrev FourEndpointSlotIndexing (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) :=
  ∀ i : Fin 4, Fin (fourEndpointMultiplicity alpha hAlpha k i) ≃
    ↥(fourEndpointBlockSlots alpha hAlpha k i)

noncomputable def canonicalFourEndpointSlotIndexing (alpha : Nat)
    (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1)) :
    FourEndpointSlotIndexing alpha hAlpha k := fun i =>
  Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      ((fourEndpoint_profile_indexing_facts alpha hAlpha k).2.1 i).symm)

def fourEndpointActualBlockOfAtom (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (a : Σ i : Fin 4, Fin (fourEndpointMultiplicity alpha hAlpha k i)) :
    ProfileBlockIndex k :=
  (slotIndex a.1 a.2).1

/-- The stub decoration at one selected full endpoint cell. -/
abbrev FourEndpointSelectedCellStubMatching (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable)
    (P : FourEndpointBlockPairing alpha hAlpha k L) (e : ↥P.1.edges) :=
  SingleCellStubMatching
    (fourEndpointSize alpha hAlpha e.1.1.1)
    (fourEndpointSize alpha hAlpha e.1.2.1)
    (fourEndpointOverlapSize alpha hAlpha e.1.1.1 e.1.2.1)

/-- A selected endpoint block pairing together with an independent literal
stub matching in every selected cell. -/
abbrev FourEndpointDecoratedBlockPairing (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) :=
  Σ P : FourEndpointBlockPairing alpha hAlpha k L,
    ∀ e : ↥P.1.edges,
      FourEndpointSelectedCellStubMatching alpha hAlpha k L P e

def fourEndpointCellStubFactorialProduct (alpha : Nat) (hAlpha : 5 < alpha)
    (L : FourEndpointFullTable) : Nat :=
  ∏ i : Fin 4, ∏ j : Fin 4,
    (fourEndpointOverlapSize alpha hAlpha i j).factorial ^ L.toFun i j

def fourEndpointCellStubSelectionProduct (alpha : Nat) (hAlpha : 5 < alpha)
    (L : FourEndpointFullTable) : Nat :=
  ∏ i : Fin 4, ∏ j : Fin 4,
    (((fourEndpointSize alpha hAlpha i).descFactorial
        (fourEndpointOverlapSize alpha hAlpha i j)) *
      ((fourEndpointSize alpha hAlpha j).descFactorial
        (fourEndpointOverlapSize alpha hAlpha i j))) ^ L.toFun i j

theorem card_fourEndpointDecoratedBlockPairing_mul_cellStubFactorials
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) :
    Fintype.card (FourEndpointDecoratedBlockPairing alpha hAlpha k L) *
        fourEndpointCellStubFactorialProduct alpha hAlpha L =
      Fintype.card (FourEndpointBlockPairing alpha hAlpha k L) *
        fourEndpointCellStubSelectionProduct alpha hAlpha L := by
  let fac : Fin 4 → Fin 4 → Nat := fun i j =>
    (fourEndpointOverlapSize alpha hAlpha i j).factorial
  let sel : Fin 4 → Fin 4 → Nat := fun i j =>
    (fourEndpointSize alpha hAlpha i).descFactorial
        (fourEndpointOverlapSize alpha hAlpha i j) *
      (fourEndpointSize alpha hAlpha j).descFactorial
        (fourEndpointOverlapSize alpha hAlpha i j)
  have hgroup (P : FourEndpointBlockPairing alpha hAlpha k L)
      (f : Fin 4 → Fin 4 → Nat) :
      (∏ e ∈ P.1.edges, f e.1.1 e.2.1) =
        ∏ i : Fin 4, ∏ j : Fin 4, (f i j) ^ L.toFun i j := by
    rw [← Finset.prod_fiberwise' P.1.edges
      (fun e => (e.1.1, e.2.1))
      (fun ij : Fin 4 × Fin 4 => f ij.1 ij.2)]
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.prod_const]
    apply congrArg (fun n => (f i j) ^ n)
    calc
      _ = (P.1.edges.filter
          (fun e => e.1.1 = i ∧ e.2.1 = j)).card := by
        congr 1
        ext e
        simp [Prod.ext_iff]
      _ = P.1.typeTable i j := rfl
      _ = L.toFun i j := congrFun (congrFun P.2 i) j
  have hfiber (P : FourEndpointBlockPairing alpha hAlpha k L) :
      Fintype.card (∀ e : ↥P.1.edges,
          FourEndpointSelectedCellStubMatching alpha hAlpha k L P e) *
          fourEndpointCellStubFactorialProduct alpha hAlpha L =
        fourEndpointCellStubSelectionProduct alpha hAlpha L := by
    rw [Fintype.card_pi]
    rw [← Finset.prod_subtype P.1.edges (fun _ => Iff.rfl)
      (fun e => Fintype.card (SingleCellStubMatching
        (fourEndpointSize alpha hAlpha e.1.1)
        (fourEndpointSize alpha hAlpha e.2.1)
        (fourEndpointOverlapSize alpha hAlpha e.1.1 e.2.1)))]
    unfold fourEndpointCellStubFactorialProduct
      fourEndpointCellStubSelectionProduct
    rw [← hgroup P fac, ← hgroup P sel]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro e he
    exact card_singleCellStubMatching_mul_factorial _ _ _
  rw [Fintype.card_sigma]
  simp_rw [Finset.sum_mul, hfiber]
  simp

end

end Erdos625
