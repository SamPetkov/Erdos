import Erdos625.ColoringProfileAggregation

/-!
# Uniform bounds for finite coloring-profile aggregation

This module isolates the finite multiplicity step used in manuscript (4.3).
Once every admissible exact-profile expectation is bounded by the same
`ENNReal` value `C`, the aggregate expectation is at most the number of
profiles times `C`, and hence at most `(n + 1)^b * C`.

No logarithmic, Stirling, variational, or asymptotic estimate is asserted
here.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- A uniform per-profile bound transfers to the exact finite aggregate with
the actual number of admissible profiles as multiplicity. -/
theorem boundedProfileColoringExpectation_le_card_mul
    (n b parts : ℕ) (C : ENNReal)
    (h : ∀ k ∈ boundedColoringProfiles n b parts,
      profileColoringExpectation n k ≤ C) :
    boundedProfileColoringExpectation n b parts ≤
      ((boundedColoringProfiles n b parts).card : ENNReal) * C := by
  rw [boundedProfileColoringExpectation_eq_sum]
  calc
    (∑ k ∈ boundedColoringProfiles n b parts,
        profileColoringExpectation n k) ≤
        ∑ _k ∈ boundedColoringProfiles n b parts, C := by
      exact Finset.sum_le_sum fun k hk ↦ h k hk
    _ = ((boundedColoringProfiles n b parts).card : ENNReal) * C := by
      simp [nsmul_eq_mul]

/-- Replacing the actual profile count by the coordinate-box bound gives the
explicit multiplicity `(n + 1)^b`. -/
theorem boundedProfileColoringExpectation_le_box_mul
    (n b parts : ℕ) (C : ENNReal)
    (h : ∀ k ∈ boundedColoringProfiles n b parts,
      profileColoringExpectation n k ≤ C) :
    boundedProfileColoringExpectation n b parts ≤
      (((n + 1) ^ b : ℕ) : ENNReal) * C := by
  refine (boundedProfileColoringExpectation_le_card_mul n b parts C h).trans ?_
  gcongr
  exact_mod_cast card_boundedColoringProfiles_le n b parts

end

end Erdos625
