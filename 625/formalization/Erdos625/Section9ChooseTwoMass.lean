import Mathlib

/-!
# The finite choose-two mass estimate in Section IX

This is the division-free form of manuscript (9.21).  It is a finite arithmetic
bound only and assumes no cycle-rank or attachment estimate.
-/

namespace Erdos625

open scoped BigOperators

/-- If every residual multiplicity is at most `U` and their total is `m₀`,
then twice the total pair count is at most `(U - 1) * m₀`. -/
theorem twice_sum_choose_two_le_cap_mass
    {E : Type*} [Fintype E]
    (r : E → ℕ) (U m₀ : ℕ)
    (hCap : ∀ e, r e ≤ U)
    (hTotal : ∑ e, r e = m₀) :
    2 * (∑ e, (r e).choose 2) ≤ (U - 1) * m₀ := by
  have hPointwise : ∀ e, 2 * (r e).choose 2 ≤ (U - 1) * r e := by
    intro e
    have hTwiceChoose : 2 * (r e).choose 2 = r e * (r e - 1) := by
      rw [Nat.choose_two_right, mul_comm]
      exact Nat.div_mul_cancel
        (even_iff_two_dvd.mp (Nat.even_mul_pred_self _))
    rw [hTwiceChoose]
    calc
      r e * (r e - 1) = (r e - 1) * r e := Nat.mul_comm _ _
      _ ≤ (U - 1) * r e :=
        Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (hCap e) 1)
  calc
    2 * (∑ e, (r e).choose 2) = ∑ e, 2 * (r e).choose 2 := by
      rw [Finset.mul_sum]
    _ ≤ ∑ e, (U - 1) * r e :=
      Finset.sum_le_sum fun e _ => hPointwise e
    _ = (U - 1) * m₀ := by
      rw [← Finset.mul_sum, hTotal]

#print axioms twice_sum_choose_two_le_cap_mass

end Erdos625
