import Erdos625.ColoringProfileAggregation

/-!
# Positivity and partition extraction for bounded profile counts

This module develops the deterministic count interface needed in manuscript
(4.5).  The first layer identifies positivity of the exact-profile and
aggregated natural-valued counts with the existence of a proper unordered
partition.  The later layer will extract the bounded profile of a given
partition.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- A profile-partition indicator is positive exactly on its proper-colouring
event. -/
@[simp] theorem profilePartitionIndicator_pos_iff {b n : ℕ}
    (G : LabeledGraph n) {k : ColoringProfile b}
    (P : ProfilePartition n k) :
    0 < profilePartitionIndicator G P ↔
      G ∈ partitionColoringEvent P.1 := by
  classical
  by_cases h : G ∈ partitionColoringEvent P.1 <;>
    simp [profilePartitionIndicator, h]

/-- The exact-profile count is positive exactly when a proper unordered
partition of that profile exists. -/
theorem profileColoringCount_pos_iff {b n : ℕ}
    (G : LabeledGraph n) (k : ColoringProfile b) :
    0 < profileColoringCount G k ↔
      ∃ P : ProfilePartition n k,
        G ∈ partitionColoringEvent P.1 := by
  classical
  unfold profileColoringCount
  rw [show (∑ P : ProfilePartition n k,
      profilePartitionIndicator G P) =
      ∑ P ∈ (Finset.univ : Finset (ProfilePartition n k)),
        profilePartitionIndicator G P by simp,
    Finset.sum_pos_iff]
  simp only [Finset.mem_univ, true_and, profilePartitionIndicator_pos_iff]

/-- The bounded aggregate count is positive exactly when one admissible
profile has a proper partition. -/
theorem boundedProfileColoringCount_pos_iff {n : ℕ}
    (G : LabeledGraph n) (b parts : ℕ) :
    0 < boundedProfileColoringCount G b parts ↔
      ∃ k ∈ boundedColoringProfiles n b parts,
        ∃ P : ProfilePartition n k,
          G ∈ partitionColoringEvent P.1 := by
  classical
  unfold boundedProfileColoringCount
  rw [Finset.sum_pos_iff]
  simp only [profileColoringCount_pos_iff]

end

end Erdos625
