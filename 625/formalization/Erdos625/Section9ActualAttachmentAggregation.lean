import Erdos625.Section9CanonicalPolymerAggregation
import Mathlib.Tactic

/-!
# Section IX: literal attachment aggregation

This factors a uniform pointwise bound out of the exact attained-demand
attachment sum.  The left side remains the literal event-restricted
attachment sum, not the unrestricted polymer majorant.

The proof was returned by Aristotle project
`a4d1d2c3-582b-45bc-a5b6-14e3b2fb0040`, task
`cc53e112-8b47-4a3d-bda9-74d2950c2913`, and independently audited before
integration.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- A uniform pointwise bound on the literal residual attachment factors out
of the exact attained-demand attachment sum. -/
theorem midpointCanonicalAttachmentSum_le_bare_mul
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : ℕ) (K : ENNReal)
    (hK : ∀ demand : ProfileCanonicalHighSkeleton k U,
      profileHighSkeletonAttachment row₀ U demand ≤ K) :
    midpointCanonicalAttachmentSum row₀ U ≤
      canonicalBareSkeletonSum k U * K := by
  unfold midpointCanonicalAttachmentSum canonicalBareSkeletonSum
  simp only [profileHighSkeletonContribution, profileHighSkeletonWeight]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro demand _
  exact mul_le_mul_right (hK demand) _

end

end Erdos625
