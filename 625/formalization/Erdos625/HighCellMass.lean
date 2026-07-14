import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Erdos625

open scoped BigOperators

/-!
# Total mass of high cells

This is the elementary counting inequality behind the bound on the number of
high cells in Section VIII.  It uses only the threshold definition; the
separate partial-matching property is not needed here.
-/

def highCellFinset {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (table : A → B → ℕ) (R : ℕ) : Finset (A × B) :=
  Finset.univ.filter (fun p => R < table p.1 p.2)

theorem highCellFinset_card_mul_succ_le_total
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (table : A → B → ℕ) (R : ℕ) :
    (highCellFinset table R).card * (R + 1) ≤
      ∑ a, ∑ b, table a b := by
  have htotal : ∑ a, ∑ b, table a b = ∑ p : A × B, table p.1 p.2 := by
    rw [Fintype.sum_prod_type]
  rw [htotal]
  calc
    (highCellFinset table R).card * (R + 1) =
        ∑ _p ∈ highCellFinset table R, (R + 1) := by
      rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ p ∈ highCellFinset table R, table p.1 p.2 := by
      apply Finset.sum_le_sum
      intro p hp
      have : R < table p.1 p.2 := by
        simpa [highCellFinset] using hp
      omega
    _ ≤ ∑ p : A × B, table p.1 p.2 := by
      apply Finset.sum_le_sum_of_subset
      exact Finset.subset_univ _

end Erdos625
