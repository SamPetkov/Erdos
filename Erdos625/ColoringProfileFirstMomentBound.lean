import Erdos625.ColoringProfileAggregationBounds
import Erdos625.ColoringProfileLogBounds

/-!
# Finite uniform first-moment bound for bounded profiles

This module combines the per-profile exponential estimate with the exact
finite aggregation multiplicity.  It is the finite logical skeleton of
manuscript (4.3): the only remaining analytic input is a common real upper
bound for the explicit profile Stirling main term.
-/

namespace Erdos625

noncomputable section

/-- A common real upper bound on every admissible profile's explicit
Stirling expression yields the coordinate-box first-moment estimate. -/
theorem boundedProfileColoringExpectation_le_box_mul_exp
    (n b parts : ℕ) (L : ℝ)
    (hL : ∀ k ∈ boundedColoringProfiles n b parts,
      profileStirlingUpperMain n k + factorialLogErrorBound n ≤ L) :
    boundedProfileColoringExpectation n b parts ≤
      (((n + 1) ^ b : ℕ) : ENNReal) * ENNReal.ofReal (Real.exp L) := by
  apply boundedProfileColoringExpectation_le_box_mul
  intro k hk
  have hMass : ColoringProfile.vertexMass k = n :=
    (mem_boundedColoringProfiles k).1 hk |>.1
  exact profileColoringExpectation_le_of_stirlingUpperMain_add_error_le
    n k L hMass (hL k hk)

end

end Erdos625
