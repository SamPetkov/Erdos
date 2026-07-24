import Erdos625.LocalSignReward

/-!
# Capped local-reward telescoping for Section IX

This module records the exact finite telescoping identities in manuscript
(9.10)--(9.11), using the repository's existing local signed reward from
(6.5).  It contains no configuration-model probability estimate and no
attachment bound.
-/

namespace Erdos625

open scoped BigOperators

/-- The finite increment `Delta_x = g(x) - g(x-1)` from manuscript (9.5). -/
def rewardIncrement (x : ℕ) : ℕ :=
  localSignRewardNat x - localSignRewardNat (x - 1)

/-- Exact capped forms of manuscript (9.10) and (9.11).  The hypothesis
`r ≤ R` is essential because both displayed sums stop at the cap `R`. -/
theorem cappedReward_telescoping (r R : ℕ) (hr : r ≤ R) :
    localSignRewardNat r =
        1 + (∑ x ∈ Finset.Icc 3 R,
          if x ≤ r then rewardIncrement x else 0) ∧
      (if 2 ≤ r then localSignRewardNat r else 0) =
        (if 2 ≤ r then 1 else 0) +
          ∑ x ∈ Finset.Icc 3 R,
            if x ≤ r then rewardIncrement x else 0 := by
  have h_reward_step_mono : ∀ n,
      localSignRewardNat n ≤ localSignRewardNat (n + 1) := by
    intro n
    rcases n with (_ | _ | _ | n)
    · norm_num [localSignRewardNat]
    · norm_num [localSignRewardNat]
    · norm_num [localSignRewardNat]
    · simp only [localSignRewardNat]
      exact Nat.pow_le_pow_right (by decide)
        (Nat.sub_le_sub_right (Nat.choose_le_succ _ _) 1)
  have h_telescope : ∀ r,
      localSignRewardNat r =
        1 + ∑ x ∈ Finset.Icc 3 r, rewardIncrement x := by
    intro n
    induction n with
    | zero =>
        norm_num [localSignRewardNat]
    | succ n ih =>
        by_cases h3 : 3 ≤ n + 1
        · rw [Finset.sum_Icc_succ_top h3, ← add_assoc, ← ih]
          exact (Nat.add_sub_of_le (h_reward_step_mono n)).symm
        · have hn : n ≤ 1 := by omega
          interval_cases n <;>
            norm_num [localSignRewardNat, rewardIncrement]
  have h_filter :
      Finset.filter (fun x => x ≤ r) (Finset.Icc 3 R) =
        Finset.Icc 3 r := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hx
      exact ⟨hx.1.1, hx.2⟩
    · intro hx
      exact ⟨⟨hx.1, hx.2.trans hr⟩, hx.2⟩
  have h_capped_sum :
      (∑ x ∈ Finset.Icc 3 R,
        if x ≤ r then rewardIncrement x else 0) =
        ∑ x ∈ Finset.Icc 3 r, rewardIncrement x := by
    rw [← Finset.sum_filter, h_filter]
  have h_first :
      localSignRewardNat r =
        1 + ∑ x ∈ Finset.Icc 3 R,
          if x ≤ r then rewardIncrement x else 0 := by
    rw [h_capped_sum]
    exact h_telescope r
  refine ⟨h_first, ?_⟩
  by_cases h2 : 2 ≤ r
  · simp only [if_pos h2]
    exact h_first
  · have hIcc : Finset.Icc 3 r = ∅ :=
      Finset.Icc_eq_empty (by omega)
    have hzero :
        (∑ x ∈ Finset.Icc 3 R,
          if x ≤ r then rewardIncrement x else 0) = 0 := by
      rw [h_capped_sum, hIcc, Finset.sum_empty]
    simp only [if_neg h2, hzero, zero_add]

#print axioms cappedReward_telescoping

end Erdos625
