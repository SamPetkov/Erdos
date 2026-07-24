import Erdos625.Phase
import Mathlib.Tactic

/-!
# Finite falling-factorial ratio for the empty corner

The proof was returned by Aristotle project
`3d5fd715-841c-45b3-a097-94c185287192`, task
`953bd883-0ad0-4c48-9c08-00f8bc575106`, and independently audited before
integration.
-/

namespace Erdos625

/-- Finite falling-factorial comparison behind the empty-corner estimate
(7.10). The sole hypothesis makes the denominator's binomial coefficient
positive; it also keeps the explicit lower factor positive, including the
edge case `s = 0`. -/
theorem mu_div_mu_sub_le_pow {v s m : Nat}
    (hsm : s + m <= v) :
    mu v s / mu (v - m) s <=
      ((v : Real) / ((v - m - s + 1 : Nat) : Real)) ^ s := by
  by_cases hs : s = 0 <;> simp_all +decide [mu]
  rw [mul_div_mul_right _ _ (by positivity)]
  have h_binom :
      (Nat.choose v s : ℝ) / (Nat.choose (v - m) s : ℝ) =
        (∏ i ∈ Finset.range s, (v - i : ℝ)) /
          (∏ i ∈ Finset.range s, (v - m - i : ℝ)) := by
    have h_prod :
        (∏ i ∈ Finset.range s, (v - i : ℝ)) =
            (Nat.descFactorial v s : ℝ) ∧
          (∏ i ∈ Finset.range s, (v - m - i : ℝ)) =
            (Nat.descFactorial (v - m) s : ℝ) := by
      constructor <;> rw [Nat.descFactorial_eq_prod_range] <;> norm_num
      · exact Finset.prod_congr rfl fun x hx => by
          rw [Nat.cast_sub (by linarith [Finset.mem_range.mp hx])]
      · exact Finset.prod_congr rfl fun x hx => by
          rw [Nat.cast_sub <| Nat.le_sub_of_add_le <| by
            linarith [Finset.mem_range.mp hx]]
          rw [Nat.cast_sub <| by linarith [Finset.mem_range.mp hx]]
    rw [h_prod.1, h_prod.2, Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_factorial_mul_choose]
    ring_nf
    simp +decide [mul_comm, mul_left_comm, Nat.factorial_ne_zero]
  have hden : ((v - m - s + 1 : ℕ) : ℝ) = (v : ℝ) - m - s + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : s ≤ v - m),
      Nat.cast_sub (by omega : m ≤ v)]
  have h_term_le :
      ∀ i ∈ Finset.range s, (v - i : ℝ) / (v - m - i : ℝ) ≤
        v / (((v - m - s : ℕ) : ℝ) + 1) := by
    have hden' :
        ((v - m - s : ℕ) : ℝ) + 1 = ((v - m - s + 1 : ℕ) : ℝ) := by
      norm_num
    rw [hden', hden]
    intro i hi
    rw [div_le_div_iff₀] <;>
      nlinarith only [
        show (i : ℝ) + 1 ≤ s by
          norm_cast
          linarith [Finset.mem_range.mp hi],
        show (s : ℝ) + m ≤ v by norm_cast]
  have h_nonneg :
      ∀ i ∈ Finset.range s, 0 ≤ (v - i : ℝ) / (v - m - i : ℝ) := by
    intro i hi
    have hiNat := Finset.mem_range.mp hi
    exact div_nonneg
      (sub_nonneg.2 <| Nat.cast_le.2 <| by omega)
      (sub_nonneg.2 <| by
        have hi' : (i : ℝ) + 1 ≤ s := by norm_cast
        have hsm' : (s : ℝ) + m ≤ v := by norm_cast
        linarith)
  rw [h_binom, ← Finset.prod_div_distrib]
  calc
    ∏ i ∈ Finset.range s, (v - i : ℝ) / (v - m - i : ℝ) ≤
        ∏ _i ∈ Finset.range s,
          (v : ℝ) / (((v - m - s : ℕ) : ℝ) + 1) :=
      Finset.prod_le_prod h_nonneg h_term_le
    _ = ((v : ℝ) / (((v - m - s : ℕ) : ℝ) + 1)) ^ s := by
      rw [Finset.prod_const, Finset.card_range]

end Erdos625
