import Erdos625.ProfileOptimizerS4

/-!
# Stability of the optimized four-point profile value

This module proves the finite-support value-stability part of manuscript
display (3.9).  At a fixed target `T ∈ (2,5)`, changing every score coordinate
by at most `ε` changes the optimized value by at most `ε`.  The proof compares
each optimizer against the other score via the zero-safe Gibbs variational
inequality, so no positivity assumption is imposed on competitor coordinates.

The final corollary gives sequential convergence for a fixed target under
uniform convergence of the four score coordinates.  It does not assert
uniformity over a set of target values `T`.
-/

open Finset Filter

namespace Erdos625.ProfileEntropyS4

noncomputable section

/-- The dual (equivalently, optimized entropy-plus-score) value at target
`T`.  The definition is total, although its optimizer interpretation is used
only for `T ∈ (2,5)`. -/
noncomputable def optimizedValue (h : Fin 4 → ℝ) (T : ℝ) : ℝ :=
  Real.log (partition h (tilt h T)) - tilt h T * T

/-- A probability-weighted score difference is bounded by a coordinatewise
upper bound. -/
theorem sum_mul_sub_sum_mul_le
    (p h g : Fin 4 → ℝ) {ε : ℝ}
    (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i : Fin 4, p i = 1)
    (hcoord : ∀ i, h i - g i ≤ ε) :
    (∑ i : Fin 4, p i * h i) - ∑ i : Fin 4, p i * g i ≤ ε := by
  calc
    (∑ i : Fin 4, p i * h i) - ∑ i : Fin 4, p i * g i =
        ∑ i : Fin 4, p i * (h i - g i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ ∑ i : Fin 4, p i * ε := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_left (hcoord i) (hp i)
    _ = ε := by
      rw [← Finset.sum_mul, hpSum, one_mul]

/-- **Finite-support value stability (the value part of (3.9)).**
For a fixed interior target, the optimized value is 1-Lipschitz in the
coordinatewise sup norm. -/
theorem abs_optimizedValue_sub_optimizedValue_le
    (h g : Fin 4 → ℝ) {T ε : ℝ}
    (hT : T ∈ Set.Ioo (2 : ℝ) 5)
    (hε : 0 ≤ ε)
    (hclose : ∀ i, |h i - g i| ≤ ε) :
    |optimizedValue h T - optimizedValue g T| ≤ ε := by
  have hhEq :=
    optimizer_entropy_score_eq_log_partition_sub_tilt_mul_target h hT
  have hgLe := entropy_score_le_log_partition_sub_tilt_mul_target
    g (optimizer h T) hT (optimizer_nonneg h T) (sum_optimizer h T)
      (sum_optimizer_mul_support h hT)
  have ggEq :=
    optimizer_entropy_score_eq_log_partition_sub_tilt_mul_target g hT
  have ghLe := entropy_score_le_log_partition_sub_tilt_mul_target
    h (optimizer g T) hT (optimizer_nonneg g T) (sum_optimizer g T)
      (sum_optimizer_mul_support g hT)
  have hhg :
      optimizedValue h T - optimizedValue g T ≤
        (∑ i : Fin 4, optimizer h T i * h i) -
          ∑ i : Fin 4, optimizer h T i * g i := by
    simp only [optimizedValue]
    linarith
  have hgh :
      optimizedValue g T - optimizedValue h T ≤
        (∑ i : Fin 4, optimizer g T i * g i) -
          ∑ i : Fin 4, optimizer g T i * h i := by
    simp only [optimizedValue]
    linarith
  have hhgBound :
      (∑ i : Fin 4, optimizer h T i * h i) -
          ∑ i : Fin 4, optimizer h T i * g i ≤ ε :=
    sum_mul_sub_sum_mul_le (optimizer h T) h g
      (optimizer_nonneg h T) (sum_optimizer h T)
      (fun i ↦ (le_abs_self (h i - g i)).trans (hclose i))
  have hghBound :
      (∑ i : Fin 4, optimizer g T i * g i) -
          ∑ i : Fin 4, optimizer g T i * h i ≤ ε :=
    sum_mul_sub_sum_mul_le (optimizer g T) g h
      (optimizer_nonneg g T) (sum_optimizer g T)
      (fun i ↦ (le_abs_self (g i - h i)).trans (by
        simpa [abs_sub_comm] using hclose i))
  have hbound : |optimizedValue h T - optimizedValue g T| ≤ ε := by
    rw [abs_le]
    constructor
    · linarith
    · exact hhg.trans hhgBound
  calc
    |optimizedValue h T - optimizedValue g T| ≤ |ε| := by
      simpa [abs_of_nonneg hε] using hbound
    _ = ε := abs_of_nonneg hε

/-- At a fixed interior target, uniform convergence of the four score
coordinates implies convergence of the optimized values.  This is a
sequential, fixed-`T` statement and makes no compact-uniform claim in `T`. -/
theorem tendsto_optimizedValue_of_uniform_scores
    (h : ℕ → Fin 4 → ℝ) (g : Fin 4 → ℝ) {T : ℝ}
    (hT : T ∈ Set.Ioo (2 : ℝ) 5)
    (huniform : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ i, |h n i - g i| < ε) :
    Tendsto (fun n ↦ optimizedValue (h n) T) atTop
      (nhds (optimizedValue g T)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := huniform (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq]
  exact lt_of_le_of_lt
    (abs_optimizedValue_sub_optimizedValue_le (h n) g hT
      (half_pos hε).le (fun i ↦ (hN n hn i).le))
    (half_lt_self hε)

end

end Erdos625.ProfileEntropyS4
