import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Erdos625

open scoped BigOperators

/-!
# Product of local sign rewards

This module isolates the finite exponent arithmetic in the local part of the
signed overlap reward.  It does not include the component-sign factor or the
global second-moment assembly.
-/

def localSignRewardNat (x : ℕ) : ℕ :=
  if 3 ≤ x then 2 ^ (x.choose 2 - 1) else 1

theorem prod_localSignRewardNat_eq_pow
    {E : Type*} [DecidableEq E]
    (S : Finset E) (r : E → ℕ)
    (hlarge : ∀ e ∈ S, 3 ≤ r e) :
    (∏ e ∈ S, localSignRewardNat (r e)) =
      2 ^ ((∑ e ∈ S, (r e).choose 2) - S.card) := by
  have hone : ∀ e ∈ S, 1 ≤ (r e).choose 2 := by
    intro e he
    have h3 : (3 : ℕ).choose 2 ≤ (r e).choose 2 :=
      Nat.choose_le_choose 2 (hlarge e he)
    have : (3 : ℕ).choose 2 = 3 := by decide
    omega
  have hprod :
      (∏ e ∈ S, localSignRewardNat (r e)) =
        ∏ e ∈ S, 2 ^ ((r e).choose 2 - 1) := by
    refine Finset.prod_congr rfl ?_
    intro e he
    simp only [localSignRewardNat, if_pos (hlarge e he)]
  rw [hprod, Finset.prod_pow_eq_pow_sum]
  congr 1
  have hsub := Finset.sum_tsub_distrib (s := S)
    (f := fun e => (r e).choose 2) (g := fun _ => 1) hone
  rw [hsub]
  simp

end Erdos625
