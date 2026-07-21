import Erdos625.FullCornerWeights
import Mathlib.Tactic

/-!
# Finite full-corner local-ratio bound

This is the exact finite induction used at the full corner of Section VII.
It assumes the ratio bound only along coordinate prefixes of the particular
residual profile; it does not assume or prove the later midpoint asymptotics.

The proof was returned by Aristotle project
`48c50b13-4409-4141-8c8f-ecf2d88249b9`, task
`b2eec47e-ff64-4d64-bbb7-d94b558ba392`, and independently audited before
integration.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Finite full-corner induction.  It is enough to check the exact ratio
from (7.6) along the coordinate prefixes of the particular residual profile
`h`; a global ratio bound on every subprofile of `k` would be unnecessarily
strong and is not what the full-corner argument establishes. -/
theorem fullCornerWeight_le_one_of_local_ratio
    (u k h : I → ℕ)
    (hprofile : IsPartialSubprofile k h)
    (hlocal : ∀ g i, IsPartialSubprofile h g → g i < h i →
      fullCornerWeight u k (incrementProfile g i) /
          fullCornerWeight u k g ≤ 1) :
    fullCornerWeight u k h ≤ 1 := by
  induction' m : ∑ i, h i using Nat.strong_induction_on with m ih generalizing h
  by_cases h_zero : ∀ i, h i = 0
  · simp +decide [show h = fun _ ↦ 0 from funext h_zero,
      fullCornerWeight, residualMarkingCount, completeSignedFirstMoment,
      partialSignedFirstMoment, selectedVertexMass, selectedBlockCount,
      selectedInternalEdgeCount, partialProfileFactorialProduct]
    exact div_self_le_one _
  · obtain ⟨i, hi⟩ : ∃ i, h i > 0 := by
      push Not at h_zero
      exact h_zero.imp fun i hi ↦ Nat.pos_of_ne_zero hi
    obtain ⟨g, hg⟩ : ∃ g : I → ℕ,
        IsPartialSubprofile h g ∧ g i < h i ∧ incrementProfile g i = h := by
      refine ⟨fun j ↦ if j = i then h i - 1 else h j, ?_, ?_, ?_⟩ <;>
        simp +decide [IsPartialSubprofile, incrementProfile]
      · grind
      · exact hi
      · grind
    have h_ind : fullCornerWeight u k g ≤ 1 := by
      apply ih (∑ i, g i)
      · rw [← m]
        refine Finset.sum_lt_sum (fun i _ ↦ hg.1 i) ?_
        exact ⟨i, Finset.mem_univ _, hg.2.1⟩
      · exact fun j ↦ le_trans (hg.1 j) (hprofile j)
      · exact fun g' i hg' hg'' ↦
          hlocal g' i (fun j ↦ le_trans (hg' j) (hg.1 j))
            (lt_of_lt_of_le hg'' (hg.1 i))
      · rfl
    have h_pos : 0 < fullCornerWeight u k g := by
      apply fullCornerWeight_pos
      exact fun j ↦ le_trans (hg.1 j) (hprofile j)
    have hstep := hlocal g i hg.1 hg.2.1
    rw [hg.2.2, div_le_iff₀ h_pos] at hstep
    linarith

end

end Erdos625
