import Erdos625.Section8ProfileSkeletonWeight
import Erdos625.ProfileBlockCardinalityBound
import Erdos625.Section9PositiveSupportMassBound
import Mathlib.Tactic

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

theorem profileHighSkeleton_cardinality_and_support_mass_bounds
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : ℕ)
    (demand : ProfileCanonicalHighSkeleton k U) :
    Fintype.card (ProfileBlockIndex k) ≤ n ∧
      (positiveDemandSupport demand.1).card * U ≤ 2 * n := by
  constructor
  · exact card_profileBlockIndex_le_vertex_count_of_orderedProfilePartition row₀
  · calc
      (positiveDemandSupport demand.1).card * U ≤ 2 * totalDemand demand.1 :=
        positiveDemandSupport_card_mul_cap_le_two_total demand.1 U
          (canonicalDemandImage_high (profileBlockMargin k) (profileBlockMargin k) U demand)
      _ ≤ 2 * n := by
        apply Nat.mul_le_mul_left 2
        calc
          totalDemand demand.1 ≤ ∑ q, profileBlockMargin k q :=
            profileHighSkeleton_totalDemand_le k U demand
          _ = ColoringProfile.vertexMass k := sum_profileBlockMargin_eq_vertexMass k
          _ = n := row₀.vertexMass_eq

end

end Erdos625
