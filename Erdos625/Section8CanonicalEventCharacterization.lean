import Erdos625.Section8CanonicalEventResidual

/-!
# Section 8: canonical-event characterization

This names the event-level form of the existing exact support/cap
characterization for a full configuration matching.
-/

namespace Erdos625

/-- A matching has the prescribed canonical high-demand table exactly when it
equals that table on its nonzero support and is half-capped off the support. -/
theorem mem_canonicalDemandEvent_iff_exact_support_and_capped_off
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b)
    (matching : ConfigurationMatching row col) :
    matching ∈ canonicalDemandEvent demand row col U ↔
      (∀ a b, demand a b ≠ 0 →
        configurationCellCount matching a b = demand a b) ∧
      (∀ a b, demand a b = 0 →
        configurationCellCount matching a b ≤ U / 2) := by
  exact canonicalHighDemand_eq_iff_exact_support_and_capped_off
    (configurationCellCount matching) demand U hhigh

#print axioms mem_canonicalDemandEvent_iff_exact_support_and_capped_off

end Erdos625
