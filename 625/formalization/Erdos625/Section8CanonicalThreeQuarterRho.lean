import Erdos625.Section8CoarseHalfDeficitCharge
import Mathlib.Tactic

/-!
# Section VIII: canonical common three-quarter base

There are only sixteen endpoint types.  Instead of carrying a support-dependent
hypothesis saying that one common `rho` dominates every selected cell, define
`rho` canonically as the sum of the sixteen endpoint-type bases.  Every local
base is then bounded by `rho` by positivity.

This removes the final cellwise domination premise from the finite
bare-skeleton reduction.  The only analytic premise left is eventual smallness
of this explicit sixteen-term quantity.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Explicit common charge obtained by summing the sixteen endpoint-type bases. -/
def fourEndpointThreeQuarterRho
    (n alpha : Nat) (hAlpha : 5 < alpha) : ENNReal :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    threeQuarterCellBase n
      (fourEndpointOverlapSize alpha hAlpha i j)

/-- Each endpoint-type base is one nonnegative summand of the common charge. -/
theorem threeQuarterCellBase_le_fourEndpointThreeQuarterRho
    (n alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    threeQuarterCellBase n
        (fourEndpointOverlapSize alpha hAlpha i j) ≤
      fourEndpointThreeQuarterRho n alpha hAlpha := by
  have hrow :
      threeQuarterCellBase n
          (fourEndpointOverlapSize alpha hAlpha i j) ≤
        ∑ j' : Fin 4,
          threeQuarterCellBase n
            (fourEndpointOverlapSize alpha hAlpha i j') :=
    Finset.single_le_sum
      (s := Finset.univ)
      (f := fun j' : Fin 4 =>
        threeQuarterCellBase n
          (fourEndpointOverlapSize alpha hAlpha i j'))
      (fun _ _ => bot_le) (Finset.mem_univ j)
  have houter :
      (∑ j' : Fin 4,
          threeQuarterCellBase n
            (fourEndpointOverlapSize alpha hAlpha i j')) ≤
        ∑ i' : Fin 4, ∑ j' : Fin 4,
          threeQuarterCellBase n
            (fourEndpointOverlapSize alpha hAlpha i' j') :=
    Finset.single_le_sum
      (s := Finset.univ)
      (f := fun i' : Fin 4 => ∑ j' : Fin 4,
        threeQuarterCellBase n
          (fourEndpointOverlapSize alpha hAlpha i' j'))
      (fun _ _ => bot_le) (Finset.mem_univ i)
  exact hrow.trans houter

/-- The global support sum with the canonical common base.  No pairing-dependent
analytic premise remains. -/
theorem sum_profileCanonicalHighSkeleton_le_canonicalThreeQuarterRhoSupportSum
    (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (weightDemand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha) → ENNReal)
    (reference : FourEndpointAbstractBlockSkeleton alpha hAlpha k → ENNReal)
    (hrho : fourEndpointThreeQuarterRho n alpha hAlpha ≤ 1)
    (hweight : ∀ demand,
      weightDemand demand ≤
        fourEndpointSupportChoiceChargedWeight n alpha hAlpha reference
          (fourEndpointDemandSupportChoiceEncoding
            alpha hAlpha k hcover slotIndex demand)) :
    (∑ demand, weightDemand demand) ≤
      ∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
        reference P *
          (1 + ((alpha + 1 : Nat) : ENNReal) *
            fourEndpointThreeQuarterRho n alpha hAlpha) ^ P.edges.card := by
  apply sum_profileCanonicalHighSkeleton_le_uniformHalfDeficitSupportSum
    n alpha hAlpha k hcover slotIndex weightDemand reference
      (fourEndpointThreeQuarterRho n alpha hAlpha) hrho hweight
  intro P cell
  exact threeQuarterCellBase_le_fourEndpointThreeQuarterRho
    n alpha hAlpha cell.1.1.1 cell.1.2.1

#print axioms threeQuarterCellBase_le_fourEndpointThreeQuarterRho
#print axioms sum_profileCanonicalHighSkeleton_le_canonicalThreeQuarterRhoSupportSum

end

end Erdos625
