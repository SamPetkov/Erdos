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
  apply residualActualAttachmentNumerator_le_of_forall_event_integrand_le
  intro matching hevent
  rw [coe_card_actualResidualEvenEdgeSets_eq_two_pow_cycleRank]
  have hmass :
      (∑ a, ∑ b, configurationCellCount matching a b) = m := by
    calc
      (∑ a, ∑ b, configurationCellCount matching a b) = ∑ a, row a := by
        simpa only [Fintype.sum_prod_type] using
          sum_configurationCellCount_all matching
      _ = m := hm
  have hcycle :
      cycleRank (bipartiteGraph fun a b =>
        (a, b) ∈ M ∨ 2 ≤ configurationCellCount matching a b) ≤ m / 2 := by
    simpa only [configurationResidualSupportRelation] using
      cycleRank_matching_union_configurationResidualSupport_le_half_m₀
        matching (fun a b => (a, b) ∈ M) m hm hM.1 hM.2
  have hRle : R ≤ U := by
    rw [hR]
    exact Nat.div_le_self _ _
  have hdet := smallResidualDeterministicBound
    (full := fun a b => configurationCellCount matching a b)
    (demand := fun _ _ => 0)
    (residual := fun a b => configurationCellCount matching a b)
    (cap := fun _ _ => R)
    (support := fun a b => (a, b) ∈ M)
    (U := U) (m := m)
    (cycleRank := cycleRank (bipartiteGraph fun a b =>
      (a, b) ∈ M ∨ 2 ≤ configurationCellCount matching a b))
    (by simp)
    (by
      intro a b
      constructor
      · exact hevent.1 a b
      · intro hmem
        simpa using hevent.2 (a, b) hmem)
    (by intro _ _; exact hRle)
    hmass hcycle
  calc
    (∏ a : A, ∏ b : B,
        (residualReward (configurationCellCount matching a b) : ENNReal)) *
      (2 : ENNReal) ^ cycleRank (bipartiteGraph fun a b =>
        (a, b) ∈ M ∨ 2 ≤ configurationCellCount matching a b) =
        ((2 ^ cycleRank (bipartiteGraph fun a b =>
          (a, b) ∈ M ∨ 2 ≤ configurationCellCount matching a b) *
          (∏ a : A, ∏ b : B,
            localSignRewardNat (configurationCellCount matching a b)) : ℕ) :
              ENNReal) := by
          simp only [residualReward_eq_localSignRewardNat, Nat.cast_mul,
            Nat.cast_pow, Nat.cast_prod]
          rw [mul_comm]
          norm_num
    _ ≤ ((2 ^ (U * m / 2) : ℕ) : ENNReal) := by
      exact_mod_cast hdet
    _ = (2 : ENNReal) ^ (U * m / 2) := by norm_num

#print axioms residualActualAttachmentNumerator_le_two_pow_of_small_mass

end

end Erdos625
