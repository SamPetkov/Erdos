import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Erdos625

open scoped BigOperators

/-!
# Weighted finite Cauchy--Schwarz

The square-root form below is the analytic bridge used when the Section VIII
margin-pair sum is reduced to two one-margin sums.  It is an isolated finite
inequality, not the table enumeration or skeleton assembly.
-/

theorem sum_sqrt_mul_weight_le
    {ι : Type*} [Fintype ι]
    (A C Q : ι → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hC : ∀ i, 0 ≤ C i)
    (hQ : ∀ i, 0 ≤ Q i) :
    (∑ i, Real.sqrt (A i * C i) * Q i) ≤
      Real.sqrt (∑ i, A i * Q i) *
        Real.sqrt (∑ i, C i * Q i) := by
  have key : ∀ i, Real.sqrt (A i * C i) * Q i =
      Real.sqrt (A i * Q i) * Real.sqrt (C i * Q i) := by
    intro i
    rw [← Real.sqrt_mul (mul_nonneg (hA i) (hQ i))]
    rw [show A i * Q i * (C i * Q i) = A i * C i * (Q i) ^ 2 by ring]
    rw [Real.sqrt_mul (mul_nonneg (hA i) (hC i)), Real.sqrt_sq (hQ i)]
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => mul_nonneg (hA i) (hQ i))]
  refine Real.le_sqrt_of_sq_le ?_
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (A i * Q i)) (fun i => Real.sqrt (C i * Q i))
  calc
    (∑ i, Real.sqrt (A i * C i) * Q i) ^ 2 =
        (∑ i, Real.sqrt (A i * Q i) * Real.sqrt (C i * Q i)) ^ 2 := by
      simp_rw [key]
    _ ≤ (∑ i, Real.sqrt (A i * Q i) ^ 2) *
        (∑ i, Real.sqrt (C i * Q i) ^ 2) := hcs
    _ = (∑ i, A i * Q i) * (∑ i, C i * Q i) := by
      simp_rw [Real.sq_sqrt (mul_nonneg (hA _) (hQ _)),
        Real.sq_sqrt (mul_nonneg (hC _) (hQ _))]

end Erdos625
