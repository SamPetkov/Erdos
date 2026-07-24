import Erdos625.Section8ResidualEventToSection9
import Erdos625.ConfigurationModelProbability
import Mathlib.Tactic

/-!
# Section IX: positive-support mass bound

This deterministic lemma converts the strict half-cap condition on every
positive demand cell into a support-cardinality bound. It keeps the literal
natural-number floor `U / 2`, including odd `U` and `U = 0`.

The proof was returned by Aristotle project
`87d795da-d6da-4927-8304-72b93c103dd7`, task
`ec2ec257-3c4a-42d6-a69d-790f13dcc42d`, and independently audited before
integration.
-/

namespace Erdos625

open scoped BigOperators

set_option autoImplicit false

/-- Strict half-cap support forces the support-cardinality/cap product below
twice the literal total demand. -/
theorem positiveDemandSupport_card_mul_cap_le_two_total
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (U : ℕ)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b) :
    (positiveDemandSupport demand).card * U ≤ 2 * totalDemand demand := by
  have h_sum : ∑ p ∈ positiveDemandSupport demand, U ≤
      ∑ p ∈ positiveDemandSupport demand, 2 * demand p.1 p.2 := by
    exact Finset.sum_le_sum fun p hp => by
      linarith [Nat.div_add_mod U 2, Nat.mod_lt U two_pos,
        hhigh p.1 p.2 (Finset.mem_filter.mp hp).2]
  calc
    (positiveDemandSupport demand).card * U =
        ∑ p ∈ positiveDemandSupport demand, U := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ p ∈ positiveDemandSupport demand, 2 * demand p.1 p.2 := h_sum
    _ ≤ 2 * totalDemand demand := by
      simp only [totalDemand, Finset.mul_sum]
      rw [← Finset.sum_product']
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end Erdos625
