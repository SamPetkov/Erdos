import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Mass carried by selected residual cells

The small-residual branch of Section IX uses the elementary fact that a
selected residual cell contains at least two paired stubs.  This module records
the exact finite counting consequence.  It contains no graph- or probability-
specific assertion.
-/

namespace Erdos625

open scoped BigOperators

/-- If every selected cell carries at least two units, twice the number of
selected cells is at most the ambient total mass. -/
theorem two_mul_card_selectedCells_le_total
    {E : Type*} [Fintype E] [DecidableEq E]
    (selected : Finset E) (mass : E → ℕ) (m : ℕ)
    (hselected : ∀ e ∈ selected, 2 ≤ mass e)
    (htotal : ∑ e, mass e = m) :
    2 * selected.card ≤ m := by
  calc
    2 * selected.card = ∑ _e ∈ selected, 2 := by simp [mul_comm]
    _ ≤ ∑ e ∈ selected, mass e := by
      exact Finset.sum_le_sum fun e he ↦ hselected e he
    _ ≤ ∑ e, mass e :=
      Finset.sum_le_univ_sum_of_nonneg fun e ↦ Nat.zero_le (mass e)
    _ = m := htotal

/-- Division form of `two_mul_card_selectedCells_le_total`. -/
theorem card_selectedCells_le_half_total
    {E : Type*} [Fintype E] [DecidableEq E]
    (selected : Finset E) (mass : E → ℕ) (m : ℕ)
    (hselected : ∀ e ∈ selected, 2 ≤ mass e)
    (htotal : ∑ e, mass e = m) :
    selected.card ≤ m / 2 := by
  have h := two_mul_card_selectedCells_le_total
    selected mass m hselected htotal
  omega

end Erdos625
