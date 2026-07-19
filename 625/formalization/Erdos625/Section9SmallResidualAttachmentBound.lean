import Erdos625.Section9AttachmentExpectationBound
import Erdos625.Section9ActualResidualCycleRankAssembly
import Erdos625.Section9CycleRankConfigurationAssembly
import Erdos625.Section9SmallResidualDeterministic
import Erdos625.Section9RewardCompatibility
import Mathlib.Tactic

/-!
# Section IX: faithful small-residual attachment bound

This module bounds the actual event-restricted attachment numerator, rather
than the larger unrestricted polymer majorant.  The row and column functions
are the residual degrees supplied to that numerator; their common total is
the residual mass `m`.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- The literal capped/no-return attachment numerator is bounded by the
deterministic small-residual exponent from manuscript (9.20)--(9.22). -/
theorem residualActualAttachmentNumerator_le_two_pow_of_small_mass
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R U m : ℕ)
    (row : A → ℕ) (col : B → ℕ)
    (htotal : (∑ a, row a) = ∑ b, col b)
    (hM : IsBipartiteMatching M)
    (hR : R = U / 2)
    (hm : (∑ a, row a) = m) :
    residualActualAttachmentNumerator M R row col htotal ≤
      ((2 : ENNReal) ^ (U * m / 2)) := by
  classical
  apply residualActualAttachmentNumerator_le_of_forall_event_integrand_le
  intro matching hevent
  let rank := cycleRank
    (bipartiteGraph fun a b =>
      (a, b) ∈ M ∨ 2 ≤ configurationCellCount matching a b)
  have hdet :
      2 ^ rank *
          (∏ a : A, ∏ b : B,
            localSignRewardNat (configurationCellCount matching a b)) ≤
        2 ^ (U * m / 2) := by
    apply smallResidualDeterministicBound
      (configurationCellCount matching) (fun _ _ => 0)
      (configurationCellCount matching) (fun _ _ => R)
      (fun a b => (a, b) ∈ M) U m rank
    · intro a b
      simp
    · intro a b
      constructor
      · exact hevent.1 a b
      · intro hab
        simpa using hevent.2 (a, b) hab
    · intro _ _
      rw [hR]
      omega
    · calc
        (∑ a, ∑ b, configurationCellCount matching a b) =
            ∑ p : A × B,
              configurationCellCount matching p.1 p.2 := by
          exact (Fintype.sum_prod_type fun p : A × B ↦
            configurationCellCount matching p.1 p.2).symm
        _ = ∑ a, row a := sum_configurationCellCount_all matching
        _ = m := hm
    · dsimp only [rank]
      exact
        cycleRank_matching_union_configurationResidualSupport_le_half_m₀
          matching (fun a b => (a, b) ∈ M) m hm hM.1 hM.2
  rw [coe_card_actualResidualEvenEdgeSets_eq_two_pow_cycleRank]
  simp_rw [residualReward_eq_localSignRewardNat]
  exact_mod_cast (show
    (∏ a : A, ∏ b : B,
      localSignRewardNat (configurationCellCount matching a b)) * 2 ^ rank ≤
        2 ^ (U * m / 2) by
      simpa only [mul_comm] using hdet)

#print axioms residualActualAttachmentNumerator_le_two_pow_of_small_mass

end

end Erdos625
