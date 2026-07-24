import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

/-!
# Section 9: row and column norm of the residual `q` kernel

The endpoint estimate supplies a pointwise quadratic bound for each residual
cell.  Degree caps and the exact row/column totals turn that estimate into the
uniform row and column norms required by the positive traversal kernel.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- A pointwise degree-square estimate gives both row and column kernel-norm
bounds `kappa * U^3 / m`. -/
theorem q_row_column_le_of_pointwise_degree_square
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (q : A → B → ℝ≥0∞)
    (U m : ℕ) (kappa : ℝ≥0∞)
    (hm : 0 < m)
    (hrowTotal : ∑ a, row a = m)
    (hcolTotal : ∑ b, col b = m)
    (hrowCap : ∀ a, row a ≤ U)
    (hcolCap : ∀ b, col b ≤ U)
    (hq : ∀ a b,
      q a b ≤
        kappa * (row a : ℝ≥0∞) ^ 2 * (col b : ℝ≥0∞) ^ 2 /
          (m : ℝ≥0∞) ^ 2) :
    (∀ a, ∑ b, q a b ≤ kappa * (U : ℝ≥0∞) ^ 3 / (m : ℝ≥0∞)) ∧
    (∀ b, ∑ a, q a b ≤ kappa * (U : ℝ≥0∞) ^ 3 / (m : ℝ≥0∞)) := by
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hm.ne'
  have hmt : (m : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top m
  have hcancel (x : ℝ≥0∞) :
      x / (m : ℝ≥0∞) =
        (x * (m : ℝ≥0∞)) / (m : ℝ≥0∞) ^ 2 := by
    apply (ENNReal.eq_div_iff (pow_ne_zero 2 hm0) (by finiteness)).2
    have hdiv : (m : ℝ≥0∞) * (x / (m : ℝ≥0∞)) = x :=
      (ENNReal.eq_div_iff hm0 hmt).1 rfl
    calc
      (m : ℝ≥0∞) ^ 2 * (x / (m : ℝ≥0∞)) =
          (m : ℝ≥0∞) * ((m : ℝ≥0∞) * (x / (m : ℝ≥0∞))) := by ring
      _ = (m : ℝ≥0∞) * x := by rw [hdiv]
      _ = x * (m : ℝ≥0∞) := mul_comm _ _
  refine' ⟨fun a => le_trans (Finset.sum_le_sum fun b _ => hq a b) _,
    fun b => le_trans (Finset.sum_le_sum fun a _ => hq a b) _⟩
  · simp +decide only [div_eq_mul_inv, mul_right_comm]
    simp +decide [← Finset.mul_sum _ _ _, ← Finset.sum_mul]
    have h_simp : (row a : ℝ≥0∞) ^ 2 *
        (∑ b, (col b : ℝ≥0∞) ^ 2) ≤ U ^ 3 * m := by
      have h_simp : (row a : ℝ≥0∞) ^ 2 *
          (∑ b, (col b : ℝ≥0∞) ^ 2) ≤
          (U : ℝ≥0∞) ^ 2 * (∑ b, (col b : ℝ≥0∞) * U) := by
        gcongr <;> norm_cast
        · exact hrowCap a
        · nlinarith only [hcolCap ‹_›]
      convert h_simp using 1
      all_goals norm_cast
      all_goals simp +decide [← Finset.sum_mul _ _ _, hcolTotal]
      all_goals ring
    convert mul_le_mul_right h_simp
      (kappa * (m ^ 2 : ℝ≥0∞)⁻¹) using 1
    · rfl
    · ring
    · calc
        kappa * (m : ℝ≥0∞)⁻¹ * (U : ℝ≥0∞) ^ 3 =
            (kappa * (U : ℝ≥0∞) ^ 3) / (m : ℝ≥0∞) := by
          rw [div_eq_mul_inv]
          ring
        _ = ((kappa * (U : ℝ≥0∞) ^ 3) * (m : ℝ≥0∞)) /
            (m : ℝ≥0∞) ^ 2 := hcancel _
        _ = kappa * ((m : ℝ≥0∞) ^ 2)⁻¹ *
            ((U : ℝ≥0∞) ^ 3 * (m : ℝ≥0∞)) := by
          rw [div_eq_mul_inv]
          ring
  · simp +decide only [mul_assoc, div_eq_mul_inv]
    simp +decide [← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul]
    have h_simp : (∑ i, (row i : ℝ≥0∞) ^ 2) *
        (col b : ℝ≥0∞) ^ 2 ≤
        (U : ℝ≥0∞) ^ 3 * (m : ℝ≥0∞) := by
      have h_simp : (∑ i, (row i : ℝ≥0∞) ^ 2) ≤
          (U : ℝ≥0∞) * (m : ℝ≥0∞) := by
        norm_cast
        exact le_trans
          (Finset.sum_le_sum fun _ _ => Nat.mul_le_mul_left _ (hrowCap _))
          (by simp +decide [← hrowTotal, mul_comm, Finset.mul_sum _ _ _])
      refine' le_trans (mul_le_mul_left h_simp _) _
      norm_cast
      nlinarith only
        [show U * m * col b ^ 2 ≤ U * m * U ^ 2 by
            exact Nat.mul_le_mul_left _
              (Nat.pow_le_pow_left (hcolCap b) 2),
          show U ^ 3 * m ≥ U * m * U ^ 2 by
            nlinarith only
              [show U ^ 3 ≥ U ^ 2 * U by
                  nlinarith only [show U ^ 2 ≥ 0 by positivity],
                show U * m ≥ 0 by positivity]]
    convert mul_le_mul_right h_simp kappa |>
      mul_le_mul_left <| (m ^ 2 : ℝ≥0∞)⁻¹ using 1
    · rfl
    · ring
    · calc
        kappa * (U : ℝ≥0∞) ^ 3 * (m : ℝ≥0∞)⁻¹ =
            (kappa * (U : ℝ≥0∞) ^ 3) / (m : ℝ≥0∞) := by
          rw [div_eq_mul_inv]
        _ = ((kappa * (U : ℝ≥0∞) ^ 3) * (m : ℝ≥0∞)) /
            (m : ℝ≥0∞) ^ 2 := hcancel _
        _ = kappa * ((U : ℝ≥0∞) ^ 3 * (m : ℝ≥0∞)) *
            ((m : ℝ≥0∞) ^ 2)⁻¹ := by
          rw [div_eq_mul_inv]
          ring

#print axioms q_row_column_le_of_pointwise_degree_square

end

end Erdos625
