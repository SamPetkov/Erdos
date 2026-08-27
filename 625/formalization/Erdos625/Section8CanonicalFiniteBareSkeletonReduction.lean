import Erdos625.Section8CanonicalThreeQuarterRho
import Erdos625.Section8EncodedFullSupportCharge
import Erdos625.Section8FiniteBareSkeletonReduction
import Mathlib.Tactic

/-!
# Section VIII: canonical finite bare-skeleton reduction

This module specializes the proof-complete finite common-factor wrapper to the
actual profile high-skeleton weight and the canonical sum of all sixteen
three-quarter endpoint bases. It contains no endpoint transport or asymptotic
estimate.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- The actual profile high-skeleton weight is bounded by the realized-table
reference sum times the single canonical optional-deficit factor. -/
theorem sum_profileHighSkeletonWeight_le_canonicalDeficitFactor_mul_sum_W
    (alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (hrho : fourEndpointThreeQuarterRho
      (Finset.univ.sum (profileBlockMargin k)) alpha hAlpha ≤ 1) :
    (∑ demand : ProfileCanonicalHighSkeleton k
        (fourEndpointLargestSize alpha hAlpha),
      profileHighSkeletonWeight k
        (fourEndpointLargestSize alpha hAlpha) demand) ≤
      (∑ L : ↥(fourEndpointRealizedFullTables alpha hAlpha k),
        fourEndpointW
          (Finset.univ.sum (profileBlockMargin k))
          alpha hAlpha k L.1) *
      (1 + ((alpha + 1 : Nat) : ENNReal) *
        fourEndpointThreeQuarterRho
          (Finset.univ.sum (profileBlockMargin k)) alpha hAlpha) ^
        fourEndpointTotalBlockCount alpha hAlpha k := by
  exact sum_profileCanonicalHighSkeleton_le_commonDeficitFactor_mul_sum_W
    (Finset.univ.sum (profileBlockMargin k)) alpha hAlpha k hcover slotIndex
    (profileHighSkeletonWeight k (fourEndpointLargestSize alpha hAlpha))
    (fourEndpointThreeQuarterRho
      (Finset.univ.sum (profileBlockMargin k)) alpha hAlpha)
    hrho
    (fun demand =>
      profileHighSkeletonWeight_le_fourEndpointEncodedFullSupportCharge
        alpha hAlpha hHigh k hcover slotIndex demand)
    (fun P cell =>
      threeQuarterCellBase_le_fourEndpointThreeQuarterRho
        (Finset.univ.sum (profileBlockMargin k)) alpha hAlpha
        cell.1.1.1 cell.1.2.1)

#print axioms sum_profileHighSkeletonWeight_le_canonicalDeficitFactor_mul_sum_W

end

end Erdos625
