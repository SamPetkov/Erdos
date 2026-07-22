import Erdos625.Section9ZeroResidualMatchingAttachment
import Erdos625.Section9CanonicalRawTwoRegimeSplit
import Mathlib.Tactic

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

theorem sum_zeroResidual_canonicalDemandRawAttachmentTerm_eq_bare
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : ℕ)
    (hcap : ∀ a : ProfileBlockIndex k, profileBlockMargin k a ≤ U) :
    (∑ demand ∈ (Finset.univ.filter fun demand :
        ProfileCanonicalHighSkeleton k U =>
          canonicalDemandResidualTotal (profileBlockMargin k)
            (profileBlockMargin k) U demand = 0),
      canonicalDemandRawAttachmentTerm (profileBlockMargin k)
        (profileBlockMargin k) U (profileBlockMargin_total_eq_self row₀) demand) =
    ∑ demand ∈ (Finset.univ.filter fun demand :
        ProfileCanonicalHighSkeleton k U =>
          canonicalDemandResidualTotal (profileBlockMargin k)
            (profileBlockMargin k) U demand = 0),
      (canonicalDemandLocalReward demand : ENNReal) *
        labelledWitnessIncidence demand.1 (profileBlockMargin k)
          (profileBlockMargin k) := by
  apply Finset.sum_congr rfl
  intro demand hdemand
  exact canonicalDemandRawAttachmentTerm_eq_bare_of_residualTotal_zero_of_matching
    (profileBlockMargin k) (profileBlockMargin k) U
    (profileBlockMargin_total_eq_self row₀) demand
    (Finset.mem_filter.mp hdemand).2
    (profileHighSkeleton_positiveSupport_isBipartiteMatching k U hcap demand)

end

end Erdos625
