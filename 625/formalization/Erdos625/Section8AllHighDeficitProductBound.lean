import Erdos625.Section8NearSkeletonExpansion
import Mathlib.Tactic

/-!
# Section VIII: uniform product bound for distinguishable high-cell deficits

Once the literal weight of every allowed nonzero deficit is bounded by one
common quantity `rho`, the optional-deficit expansion is controlled by a single
finite product. This module records that generic step independently of the
endpoint profile and its phase asymptotics.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- A power of an `ENNReal` number at most one is at most the number itself once
the exponent is positive. -/
theorem ennreal_pow_le_self_of_le_one
    (rho : ENNReal) (hrho : rho ≤ 1) (e : Nat) (he : 1 ≤ e) :
    rho ^ e ≤ rho := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
  have hk : rho ^ k ≤ 1 := pow_le_one₀ bot_le hrho
  rw [pow_add, pow_one]
  exact (mul_le_mul_right hk rho).trans_eq (mul_one rho)

/-- Uniform finite product estimate for optional distinguishable-cell choices.
Each cell has at most `U` allowed deficits, and every allowed weight is at most
`rho`. -/
theorem sum_nearSkeletonChoiceWeight_le_uniform_card_mul
    {Cell Deficit : Type*}
    [Fintype Cell] [Fintype Deficit] [DecidableEq Deficit]
    (allowed : Cell → Finset Deficit)
    (weight : Cell → Deficit → ENNReal)
    (U : Nat) (rho : ENNReal)
    (hcard : ∀ c, (allowed c).card ≤ U)
    (hweight : ∀ c e, e ∈ allowed c → weight c e ≤ rho) :
    (∑ choice : NearSkeletonChoice Cell Deficit allowed,
      nearSkeletonChoiceWeight allowed weight choice) ≤
        (1 + (U : ENNReal) * rho) ^ Fintype.card Cell := by
  rw [sum_nearSkeletonChoiceWeight_eq_product]
  calc
    (∏ c, (1 + ∑ e ∈ allowed c, weight c e)) ≤
        ∏ _c : Cell, (1 + (U : ENNReal) * rho) := by
      apply Finset.prod_le_prod'
      intro c _
      apply add_le_add_right
      calc
        (∑ e ∈ allowed c, weight c e) ≤
            ∑ _e ∈ allowed c, rho := by
          exact Finset.sum_le_sum fun e he => hweight c e he
        _ = ((allowed c).card : ENNReal) * rho := by
          simp
        _ ≤ (U : ENNReal) * rho := by
          have hcard' : ((allowed c).card : ENNReal) ≤ (U : ENNReal) := by
            exact_mod_cast hcard c
          exact mul_le_mul_right' hcard' rho
    _ = (1 + (U : ENNReal) * rho) ^ Fintype.card Cell := by
      simp

/-- If each allowed deficit has a positive natural exponent and its literal
weight is bounded by `rho^e`, the same uniform product bound follows whenever
`rho ≤ 1`. -/
theorem sum_nearSkeletonChoiceWeight_le_uniform_pow
    {Cell Deficit : Type*}
    [Fintype Cell] [Fintype Deficit] [DecidableEq Deficit]
    (allowed : Cell → Finset Deficit)
    (weight : Cell → Deficit → ENNReal)
    (exponent : Deficit → Nat)
    (U : Nat) (rho : ENNReal)
    (hrho : rho ≤ 1)
    (hcard : ∀ c, (allowed c).card ≤ U)
    (hpositive : ∀ c e, e ∈ allowed c → 1 ≤ exponent e)
    (hweight : ∀ c e, e ∈ allowed c → weight c e ≤ rho ^ exponent e) :
    (∑ choice : NearSkeletonChoice Cell Deficit allowed,
      nearSkeletonChoiceWeight allowed weight choice) ≤
        (1 + (U : ENNReal) * rho) ^ Fintype.card Cell := by
  apply sum_nearSkeletonChoiceWeight_le_uniform_card_mul
    allowed weight U rho hcard
  intro c e he
  exact (hweight c e he).trans
    (ennreal_pow_le_self_of_le_one rho hrho (exponent e) (hpositive c e he))

#print axioms ennreal_pow_le_self_of_le_one
#print axioms sum_nearSkeletonChoiceWeight_le_uniform_card_mul
#print axioms sum_nearSkeletonChoiceWeight_le_uniform_pow

end

end Erdos625
