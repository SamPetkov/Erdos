import Erdos625.LocalSignReward
import Mathlib.Tactic

/-!
# Deterministic small-residual attachment bound

This module proves the finite arithmetic seam behind manuscript
(9.20)--(9.22).  It retains the literal full-table cap/no-return event and
keeps the residual-mass and cycle-rank inputs explicit.  It does not identify
the random residual table or prove the preceding probabilistic estimates.
-/

namespace Erdos625

open scoped BigOperators

/-- Literal full-table cap/no-return event.  On the exposed support the full
cell equals its exposed demand, and every cell obeys its cap. -/
def FullCapNoReturnEvent
    {A B : Type*}
    (full demand cap : A → B → ℕ) (support : A → B → Prop) : Prop :=
  ∀ a b,
    full a b ≤ cap a b ∧
      (support a b → full a b = demand a b)

/-- The exact deterministic small-residual integrand bound from
manuscript (9.20)--(9.22). -/
theorem smallResidualDeterministicBound
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (full demand residual cap : A → B → ℕ)
    (support : A → B → Prop)
    (U m cycleRank : ℕ)
    (hsplit : ∀ a b, full a b = demand a b + residual a b)
    (hEvent : FullCapNoReturnEvent full demand cap support)
    (hcap : ∀ a b, cap a b ≤ U)
    (hmass : ∑ a, ∑ b, residual a b = m)
    (hcycle : cycleRank ≤ m / 2) :
    2 ^ cycleRank *
        (∏ a, ∏ b, localSignRewardNat (residual a b)) ≤
      2 ^ (U * m / 2) := by
  have hres : ∀ a b, residual a b ≤ U := by
    exact fun a b => by
      linarith [hsplit a b, hEvent a b, hcap a b]
  have hprod :
      (∏ a, ∏ b, localSignRewardNat (residual a b)) ≤
        2 ^ (∑ a, ∑ b, ((U - 1) * residual a b) / 2) := by
    have hpoint : ∀ a b,
        localSignRewardNat (residual a b) ≤
          2 ^ ((U - 1) * residual a b / 2) := by
      intro a b
      unfold localSignRewardNat
      split_ifs <;> simp_all +decide [Nat.choose_two_right]
      · gcongr <;> try omega
        rw [Nat.le_div_iff_mul_le zero_lt_two]
        nlinarith only
          [ Nat.sub_add_cancel (by linarith : 1 ≤ residual a b),
            Nat.sub_add_cancel
              (show 1 ≤ U from
                Nat.one_le_iff_ne_zero.mpr <| by linarith [hres a b]),
            hres a b,
            Nat.div_mul_le_self (residual a b * (residual a b - 1)) 2,
            Nat.sub_add_cancel
              (show 1 ≤ residual a b * (residual a b - 1) / 2 from
                Nat.div_pos
                  (by
                    nlinarith only
                      [ ‹3 ≤ residual a b›,
                        Nat.sub_add_cancel (by linarith : 1 ≤ residual a b) ])
                  zero_lt_two) ]
      · exact Nat.one_le_pow _ _ (by decide)
    exact le_trans
      (Finset.prod_le_prod' fun a _ =>
        Finset.prod_le_prod' fun b _ => hpoint a b)
      (by simp +decide [Finset.prod_pow_eq_pow_sum])
  have hcombine :
      cycleRank + (∑ a, ∑ b, ((U - 1) * residual a b) / 2) ≤
        U * m / 2 := by
    have hlocal :
        (∑ a, ∑ b, ((U - 1) * residual a b) / 2) ≤
          (U - 1) * m / 2 := by
      rw [← hmass, Nat.le_div_iff_mul_le zero_lt_two]
      simp +decide only [Finset.mul_sum _ _ _]
      rw [Finset.sum_mul _ _ _]
      exact Finset.sum_le_sum fun a _ => by
        rw [Finset.sum_mul _ _ _]
        exact Finset.sum_le_sum fun b _ => Nat.div_mul_le_self _ _
    rcases U with (_ | _ | U) <;> simp_all +decide
    all_goals grind
  exact le_trans (Nat.mul_le_mul_left _ hprod) (by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by decide) hcombine)

#print axioms smallResidualDeterministicBound

end Erdos625
