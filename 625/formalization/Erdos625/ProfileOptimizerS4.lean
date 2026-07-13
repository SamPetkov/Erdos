import Erdos625.ProfileEntropyS4

/-!
# The entropy optimizer on `S₄ = {2,3,4,5}`

For an arbitrary score `h : Fin 4 → ℝ` and target mean `T ∈ (2,5)`, this
module selects the unique exponential tilt with mean `T` and proves the
finite Gibbs variational inequality.  Competitor coordinates are allowed to
vanish; the scalar entropy estimate treats that case separately.
-/

open Finset

namespace Erdos625.ProfileEntropyS4

noncomputable section

/-! ## The unique tilt and its probability vector -/

/-- The unique exponential-family parameter whose mean is `T` when
`T ∈ (2,5)`.  Outside that interval it is assigned the harmless value zero,
so the definition itself is total. -/
noncomputable def tilt (h : Fin 4 → ℝ) (T : ℝ) : ℝ :=
  if hT : T ∈ Set.Ioo (2 : ℝ) 5 then
    Classical.choose (existsUnique_mean_eq_of_mem_Ioo h hT).exists
  else 0

theorem mean_tilt_eq (h : Fin 4 → ℝ) {T : ℝ}
    (hT : T ∈ Set.Ioo (2 : ℝ) 5) :
    mean h (tilt h T) = T := by
  rw [tilt, dif_pos hT]
  exact Classical.choose_spec (existsUnique_mean_eq_of_mem_Ioo h hT).exists

theorem eq_tilt_of_mean_eq (h : Fin 4 → ℝ) {T t : ℝ}
    (hT : T ∈ Set.Ioo (2 : ℝ) 5) (ht : mean h t = T) :
    t = tilt h T := by
  exact mean_injective h (ht.trans (mean_tilt_eq h hT).symm)

theorem mean_eq_iff_eq_tilt (h : Fin 4 → ℝ) {T t : ℝ}
    (hT : T ∈ Set.Ioo (2 : ℝ) 5) :
    mean h t = T ↔ t = tilt h T := by
  constructor
  · exact eq_tilt_of_mean_eq h hT
  · rintro rfl
    exact mean_tilt_eq h hT

/-- The maximizing probability vector at target mean `T`. -/
noncomputable def optimizer (h : Fin 4 → ℝ) (T : ℝ) (i : Fin 4) : ℝ :=
  weight h (tilt h T) i

theorem optimizer_pos (h : Fin 4 → ℝ) (T : ℝ) (i : Fin 4) :
    0 < optimizer h T i :=
  weight_pos h (tilt h T) i

theorem optimizer_nonneg (h : Fin 4 → ℝ) (T : ℝ) (i : Fin 4) :
    0 ≤ optimizer h T i :=
  (optimizer_pos h T i).le

theorem sum_optimizer (h : Fin 4 → ℝ) (T : ℝ) :
    ∑ i : Fin 4, optimizer h T i = 1 :=
  sum_weight h (tilt h T)

theorem sum_optimizer_mul_support (h : Fin 4 → ℝ) {T : ℝ}
    (hT : T ∈ Set.Ioo (2 : ℝ) 5) :
    ∑ i : Fin 4, optimizer h T i * support i = T := by
  change ∑ i : Fin 4, weight h (tilt h T) i * support i = T
  rw [← mean_eq_sum_weight_support]
  exact mean_tilt_eq h hT

/-- Feasibility for the four-point entropy problem.  Zero coordinates are
explicitly permitted. -/
def IsFeasible (p : Fin 4 → ℝ) (T : ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧
    (∑ i : Fin 4, p i = 1) ∧
      (∑ i : Fin 4, p i * support i = T)

theorem optimizer_isFeasible (h : Fin 4 → ℝ) {T : ℝ}
    (hT : T ∈ Set.Ioo (2 : ℝ) 5) :
    IsFeasible (optimizer h T) T :=
  ⟨optimizer_nonneg h T, sum_optimizer h T,
    sum_optimizer_mul_support h hT⟩

/-! ## Zero-safe relative-entropy inequality -/

/-- The scalar log-sum inequality, including the boundary case `x = 0`.
This is the only place where a zero competitor mass needs special handling. -/
theorem neg_mul_log_add_mul_log_le_sub {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 < y) :
    -x * Real.log x + x * Real.log y ≤ y - x := by
  rcases eq_or_lt_of_le hx with rfl | hxPos
  · simpa using hy.le
  · have hLog := Real.log_le_sub_one_of_pos (div_pos hy hxPos)
    have hScaled := mul_le_mul_of_nonneg_left hLog hx
    rw [Real.log_div hy.ne' hxPos.ne'] at hScaled
    field_simp [hxPos.ne'] at hScaled
    linarith

/-- The logarithm of a normalized exponential weight. -/
theorem log_weight (h : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) :
    Real.log (weight h t i) =
      h i + t * support i - Real.log (partition h t) := by
  rw [weight, Real.log_div (unnormalized_pos h t i).ne'
    (partition_pos h t).ne', unnormalized, Real.log_exp]

/-- Summed zero-safe relative-entropy inequality for two probability
vectors, with strict positivity required only of the reference vector. -/
theorem sum_neg_mul_log_add_mul_log_le_zero
    (p q' : Fin 4 → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q' i)
    (hpSum : ∑ i : Fin 4, p i = 1)
    (hqSum : ∑ i : Fin 4, q' i = 1) :
    ∑ i : Fin 4,
      (-p i * Real.log (p i) + p i * Real.log (q' i)) ≤ 0 := by
  calc
    ∑ i : Fin 4,
        (-p i * Real.log (p i) + p i * Real.log (q' i)) ≤
        ∑ i : Fin 4, (q' i - p i) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact neg_mul_log_add_mul_log_le_sub (hp i) (hq i)
    _ = 0 := by
      rw [Finset.sum_sub_distrib, hqSum, hpSum, sub_self]

/-- The log-weight average under any feasible competitor, before choosing
the target-matching tilt. -/
theorem sum_mul_log_weight (h p : Fin 4 → ℝ) (t T : ℝ)
    (hpSum : ∑ i : Fin 4, p i = 1)
    (hpMean : ∑ i : Fin 4, p i * support i = T) :
    ∑ i : Fin 4, p i * Real.log (weight h t i) =
      (∑ i : Fin 4, p i * h i) + t * T - Real.log (partition h t) := by
  calc
    ∑ i : Fin 4, p i * Real.log (weight h t i) =
        ∑ i : Fin 4,
          (p i * h i + t * (p i * support i) -
            Real.log (partition h t) * p i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [log_weight]
      ring
    _ = (∑ i : Fin 4, p i * h i) +
          t * (∑ i : Fin 4, p i * support i) -
            Real.log (partition h t) * (∑ i : Fin 4, p i) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.mul_sum]
    _ = (∑ i : Fin 4, p i * h i) + t * T -
          Real.log (partition h t) := by
      rw [hpMean, hpSum, mul_one]

/-! ## The finite Gibbs variational principle -/

/-- Every feasible four-point probability vector has entropy-plus-score at
most the dual value at the unique target-matching tilt.  The hypothesis
allows arbitrary zero coordinates. -/
theorem entropy_score_le_log_partition_sub_tilt_mul_target
    (h p : Fin 4 → ℝ) {T : ℝ}
    (hT : T ∈ Set.Ioo (2 : ℝ) 5)
    (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i : Fin 4, p i = 1)
    (hpMean : ∑ i : Fin 4, p i * support i = T) :
    -(∑ i : Fin 4, p i * Real.log (p i)) +
        ∑ i : Fin 4, p i * h i ≤
      Real.log (partition h (tilt h T)) - tilt h T * T := by
  have hOptimizerFeasible := optimizer_isFeasible h hT
  have hRelative := sum_neg_mul_log_add_mul_log_le_zero
    p (optimizer h T) hp (optimizer_pos h T) hpSum hOptimizerFeasible.2.1
  simp only [optimizer] at hRelative
  have hSumForm :
      (∑ i : Fin 4,
          (-p i * Real.log (p i) +
            p i * Real.log (weight h (tilt h T) i))) =
        -(∑ i : Fin 4, p i * Real.log (p i)) +
          ∑ i : Fin 4, p i * Real.log (weight h (tilt h T) i) := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hSumForm] at hRelative
  have hLogAverage := sum_mul_log_weight h p (tilt h T) T hpSum hpMean
  linarith

/-- The optimizer attains the dual value exactly. -/
theorem optimizer_entropy_score_eq_log_partition_sub_tilt_mul_target
    (h : Fin 4 → ℝ) {T : ℝ}
    (hT : T ∈ Set.Ioo (2 : ℝ) 5) :
    -(∑ i : Fin 4, optimizer h T i * Real.log (optimizer h T i)) +
        ∑ i : Fin 4, optimizer h T i * h i =
      Real.log (partition h (tilt h T)) - tilt h T * T := by
  have hLogAverage := sum_mul_log_weight h (optimizer h T)
    (tilt h T) T (sum_optimizer h T) (sum_optimizer_mul_support h hT)
  simp only [optimizer] at hLogAverage ⊢
  linarith

end

end Erdos625.ProfileEntropyS4
