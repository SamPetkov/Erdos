import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# A four-point exponential family on `S₄ = {2,3,4,5}`

This file develops only finite-dimensional analytic infrastructure.  For an arbitrary
log-weight (or "score") `h : Fin 4 → ℝ`, it studies the one-parameter family with
unnormalized mass

`exp (h i + λ * support i)`.

No assertion from the Erdős 625 manuscript is formalized in this file.
-/

open Filter Finset
open scoped Topology

namespace Erdos625.ProfileEntropyS4

noncomputable section

/-- The ordered support `S₄ = {2,3,4,5}`. -/
def support (i : Fin 4) : ℝ := (i.val : ℝ) + 2

@[simp] theorem support_zero : support 0 = 2 := by norm_num [support]
@[simp] theorem support_one : support 1 = 3 := by norm_num [support]
@[simp] theorem support_two : support 2 = 4 := by norm_num [support]
@[simp] theorem support_three : support 3 = 5 := by norm_num [support]

/-- The unnormalized exponential-family mass at a support point. -/
def unnormalized (h : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) : ℝ :=
  Real.exp (h i + t * support i)

/-- The exact four-term partition function. -/
def partition (h : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin 4, unnormalized h t i

/-- The normalized mass at a support point.  The denominator is never zero. -/
def weight (h : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) : ℝ :=
  unnormalized h t i / partition h t

/-- The numerator of the first moment. -/
def firstNumerator (h : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin 4, support i * unnormalized h t i

/-- The numerator of the second moment. -/
def secondNumerator (h : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin 4, support i ^ 2 * unnormalized h t i

/-- The mean of the normalized four-point family. -/
def mean (h : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  firstNumerator h t / partition h t

/-- The weighted centered second moment. -/
def variance (h : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin 4, weight h t i * (support i - mean h t) ^ 2

theorem unnormalized_pos (h : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) :
    0 < unnormalized h t i := by
  exact Real.exp_pos _

theorem partition_pos (h : Fin 4 → ℝ) (t : ℝ) : 0 < partition h t := by
  rw [partition, Fin.sum_univ_four]
  exact add_pos (add_pos (add_pos (unnormalized_pos h t 0) (unnormalized_pos h t 1))
    (unnormalized_pos h t 2)) (unnormalized_pos h t 3)

theorem weight_pos (h : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) :
    0 < weight h t i := by
  exact div_pos (unnormalized_pos h t i) (partition_pos h t)

theorem sum_weight (h : Fin 4 → ℝ) (t : ℝ) :
    ∑ i : Fin 4, weight h t i = 1 := by
  simp only [weight]
  rw [← Finset.sum_div, partition]
  exact div_self (ne_of_gt (partition_pos h t))

theorem mean_eq_sum_weight_support (h : Fin 4 → ℝ) (t : ℝ) :
    mean h t = ∑ i : Fin 4, weight h t i * support i := by
  rw [mean, firstNumerator]
  simp only [weight]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem two_lt_mean (h : Fin 4 → ℝ) (t : ℝ) : 2 < mean h t := by
  rw [mean_eq_sum_weight_support, Fin.sum_univ_four]
  have hs := sum_weight h t
  rw [Fin.sum_univ_four] at hs
  have h0 := weight_pos h t 0
  have h1 := weight_pos h t 1
  have h2 := weight_pos h t 2
  have h3 := weight_pos h t 3
  simp only [support_zero, support_one, support_two, support_three]
  nlinarith

theorem mean_lt_five (h : Fin 4 → ℝ) (t : ℝ) : mean h t < 5 := by
  rw [mean_eq_sum_weight_support, Fin.sum_univ_four]
  have hs := sum_weight h t
  rw [Fin.sum_univ_four] at hs
  have h0 := weight_pos h t 0
  have h1 := weight_pos h t 1
  have h2 := weight_pos h t 2
  have h3 := weight_pos h t 3
  simp only [support_zero, support_one, support_two, support_three]
  nlinarith

theorem mean_mem_Ioo (h : Fin 4 → ℝ) (t : ℝ) : mean h t ∈ Set.Ioo 2 5 :=
  ⟨two_lt_mean h t, mean_lt_five h t⟩

theorem hasDerivAt_unnormalized (h : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) :
    HasDerivAt (fun x ↦ unnormalized h x i)
      (support i * unnormalized h t i) t := by
  simpa only [unnormalized, Function.const_apply, Pi.add_apply, id_eq, zero_add, one_mul,
    mul_comm] using
    ((hasDerivAt_const t (h i)).add ((hasDerivAt_id t).mul_const (support i))).exp

theorem hasDerivAt_partition (h : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (partition h) (firstNumerator h t) t := by
  change HasDerivAt (fun x ↦ ∑ i : Fin 4, unnormalized h x i)
    (∑ i : Fin 4, support i * unnormalized h t i) t
  exact HasDerivAt.fun_sum fun i _ ↦ hasDerivAt_unnormalized h t i

theorem hasDerivAt_firstNumerator (h : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (firstNumerator h) (secondNumerator h t) t := by
  change HasDerivAt (fun x ↦ ∑ i : Fin 4, support i * unnormalized h x i)
    (∑ i : Fin 4, support i ^ 2 * unnormalized h t i) t
  apply HasDerivAt.fun_sum
  intro i hi
  simpa only [pow_two, mul_assoc] using
    (hasDerivAt_unnormalized h t i).const_mul (support i)

theorem sum_weight_support_sq (h : Fin 4 → ℝ) (t : ℝ) :
    ∑ i : Fin 4, weight h t i * support i ^ 2 = secondNumerator h t / partition h t := by
  rw [secondNumerator]
  simp only [weight]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem variance_eq_raw (h : Fin 4 → ℝ) (t : ℝ) :
    variance h t = secondNumerator h t / partition h t - mean h t ^ 2 := by
  calc
    variance h t = ∑ i : Fin 4,
        (weight h t i * support i ^ 2 -
          2 * mean h t * (weight h t i * support i) +
          mean h t ^ 2 * weight h t i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i : Fin 4, weight h t i * support i ^ 2) -
          2 * mean h t * (∑ i : Fin 4, weight h t i * support i) +
          mean h t ^ 2 * (∑ i : Fin 4, weight h t i) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = secondNumerator h t / partition h t - mean h t ^ 2 := by
      rw [sum_weight_support_sq, ← mean_eq_sum_weight_support, sum_weight]
      ring

theorem hasDerivAt_mean (h : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (mean h) (variance h t) t := by
  have hd := (hasDerivAt_firstNumerator h t).div (hasDerivAt_partition h t)
    (ne_of_gt (partition_pos h t))
  have halg : variance h t =
      (secondNumerator h t * partition h t -
        firstNumerator h t * firstNumerator h t) / partition h t ^ 2 := by
    rw [variance_eq_raw, mean]
    field_simp [ne_of_gt (partition_pos h t)]
  rw [halg]
  exact hd

theorem differentiableAt_mean (h : Fin 4 → ℝ) (t : ℝ) :
    DifferentiableAt ℝ (mean h) t :=
  (hasDerivAt_mean h t).differentiableAt

theorem differentiable_mean (h : Fin 4 → ℝ) : Differentiable ℝ (mean h) :=
  fun t ↦ differentiableAt_mean h t

theorem continuous_mean (h : Fin 4 → ℝ) : Continuous (mean h) :=
  (differentiable_mean h).continuous

theorem deriv_mean (h : Fin 4 → ℝ) (t : ℝ) :
    deriv (mean h) t = variance h t :=
  (hasDerivAt_mean h t).deriv

theorem variance_pos (h : Fin 4 → ℝ) (t : ℝ) : 0 < variance h t := by
  rw [variance, Fin.sum_univ_four]
  have hmean : 2 < mean h t := two_lt_mean h t
  have hsq0 : 0 < (support 0 - mean h t) ^ 2 := by
    apply sq_pos_of_ne_zero
    simp only [support_zero]
    linarith
  have hterm0 : 0 < weight h t 0 * (support 0 - mean h t) ^ 2 :=
    mul_pos (weight_pos h t 0) hsq0
  have hterm1 : 0 ≤ weight h t 1 * (support 1 - mean h t) ^ 2 :=
    mul_nonneg (weight_pos h t 1).le (sq_nonneg _)
  have hterm2 : 0 ≤ weight h t 2 * (support 2 - mean h t) ^ 2 :=
    mul_nonneg (weight_pos h t 2).le (sq_nonneg _)
  have hterm3 : 0 ≤ weight h t 3 * (support 3 - mean h t) ^ 2 :=
    mul_nonneg (weight_pos h t 3).le (sq_nonneg _)
  positivity

theorem strictMono_mean (h : Fin 4 → ℝ) : StrictMono (mean h) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [deriv_mean]
  exact variance_pos h t

/-! ## Endpoint limits -/

theorem tendsto_exp_const_sub_pos_mul_atTop (a c : ℝ) (hc : 0 < c) :
    Tendsto (fun t : ℝ ↦ Real.exp (a - c * t)) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  have hlin : Tendsto (fun t : ℝ ↦ (-c) * t + a) atTop atBot :=
    tendsto_atBot_add_const_right atTop a
      (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hc))
  convert hlin using 1
  ring_nf

theorem tendsto_exp_const_add_pos_mul_atBot (a c : ℝ) (hc : 0 < c) :
    Tendsto (fun t : ℝ ↦ Real.exp (a + c * t)) atBot (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  have hlin : Tendsto (fun t : ℝ ↦ c * t + a) atBot atBot :=
    tendsto_atBot_add_const_right atBot a (tendsto_id.const_mul_atBot hc)
  convert hlin using 1
  ring_nf

/-- The partition function after dividing by the mass at support point `5`. -/
def topDenominator (h : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  Real.exp ((h 0 - h 3) - 3 * t) +
    Real.exp ((h 1 - h 3) - 2 * t) +
    Real.exp ((h 2 - h 3) - t) + 1

/-- The first-moment numerator after dividing by the mass at support point `5`. -/
def topNumerator (h : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  2 * Real.exp ((h 0 - h 3) - 3 * t) +
    3 * Real.exp ((h 1 - h 3) - 2 * t) +
    4 * Real.exp ((h 2 - h 3) - t) + 5

theorem mean_eq_top_scaled (h : Fin 4 → ℝ) (t : ℝ) :
    mean h t = topNumerator h t / topDenominator h t := by
  have hA : Real.exp (h 3 + t * 5) ≠ 0 := Real.exp_ne_zero _
  have h0 : Real.exp (h 0 + t * 2) =
      Real.exp (h 3 + t * 5) * Real.exp ((h 0 - h 3) - 3 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 : Real.exp (h 1 + t * 3) =
      Real.exp (h 3 + t * 5) * Real.exp ((h 1 - h 3) - 2 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (h 2 + t * 4) =
      Real.exp (h 3 + t * 5) * Real.exp ((h 2 - h 3) - t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mean, firstNumerator, partition, Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [unnormalized, support_zero, support_one, support_two, support_three]
  rw [h0, h1, h2]
  unfold topNumerator topDenominator
  field_simp [hA]

theorem tendsto_topDenominator_atTop (h : Fin 4 → ℝ) :
    Tendsto (topDenominator h) atTop (𝓝 1) := by
  change Tendsto (fun t : ℝ ↦
    Real.exp ((h 0 - h 3) - 3 * t) +
      Real.exp ((h 1 - h 3) - 2 * t) +
      Real.exp ((h 2 - h 3) - t) + 1) atTop (𝓝 1)
  have h0 := tendsto_exp_const_sub_pos_mul_atTop (h 0 - h 3) 3 (by norm_num)
  have h1 := tendsto_exp_const_sub_pos_mul_atTop (h 1 - h 3) 2 (by norm_num)
  have h2 := tendsto_exp_const_sub_pos_mul_atTop (h 2 - h 3) 1 (by norm_num)
  simpa only [topDenominator, one_mul, add_zero, zero_add] using
    (((h0.add h1).add h2).add tendsto_const_nhds)

theorem tendsto_topNumerator_atTop (h : Fin 4 → ℝ) :
    Tendsto (topNumerator h) atTop (𝓝 5) := by
  change Tendsto (fun t : ℝ ↦
    2 * Real.exp ((h 0 - h 3) - 3 * t) +
      3 * Real.exp ((h 1 - h 3) - 2 * t) +
      4 * Real.exp ((h 2 - h 3) - t) + 5) atTop (𝓝 5)
  have h0 := tendsto_exp_const_sub_pos_mul_atTop (h 0 - h 3) 3 (by norm_num)
  have h1 := tendsto_exp_const_sub_pos_mul_atTop (h 1 - h 3) 2 (by norm_num)
  have h2 := tendsto_exp_const_sub_pos_mul_atTop (h 2 - h 3) 1 (by norm_num)
  simpa only [topNumerator, one_mul, mul_zero, add_zero, zero_add] using
    ((((h0.const_mul 2).add (h1.const_mul 3)).add (h2.const_mul 4)).add
      tendsto_const_nhds)

theorem tendsto_mean_atTop (h : Fin 4 → ℝ) :
    Tendsto (mean h) atTop (𝓝 5) := by
  rw [show mean h = topNumerator h / topDenominator h from by
    ext t
    exact mean_eq_top_scaled h t]
  simpa only [div_one] using
    (tendsto_topNumerator_atTop h).div (tendsto_topDenominator_atTop h)
      (by norm_num : (1 : ℝ) ≠ 0)

/-- The partition function after dividing by the mass at support point `2`. -/
def bottomDenominator (h : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  1 + Real.exp ((h 1 - h 0) + t) +
    Real.exp ((h 2 - h 0) + 2 * t) +
    Real.exp ((h 3 - h 0) + 3 * t)

/-- The first-moment numerator after dividing by the mass at support point `2`. -/
def bottomNumerator (h : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  2 + 3 * Real.exp ((h 1 - h 0) + t) +
    4 * Real.exp ((h 2 - h 0) + 2 * t) +
    5 * Real.exp ((h 3 - h 0) + 3 * t)

theorem mean_eq_bottom_scaled (h : Fin 4 → ℝ) (t : ℝ) :
    mean h t = bottomNumerator h t / bottomDenominator h t := by
  have hA : Real.exp (h 0 + t * 2) ≠ 0 := Real.exp_ne_zero _
  have h1 : Real.exp (h 1 + t * 3) =
      Real.exp (h 0 + t * 2) * Real.exp ((h 1 - h 0) + t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (h 2 + t * 4) =
      Real.exp (h 0 + t * 2) * Real.exp ((h 2 - h 0) + 2 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (h 3 + t * 5) =
      Real.exp (h 0 + t * 2) * Real.exp ((h 3 - h 0) + 3 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mean, firstNumerator, partition, Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [unnormalized, support_zero, support_one, support_two, support_three]
  rw [h1, h2, h3]
  unfold bottomNumerator bottomDenominator
  field_simp [hA]

theorem tendsto_bottomDenominator_atBot (h : Fin 4 → ℝ) :
    Tendsto (bottomDenominator h) atBot (𝓝 1) := by
  change Tendsto (fun t : ℝ ↦
    1 + Real.exp ((h 1 - h 0) + t) +
      Real.exp ((h 2 - h 0) + 2 * t) +
      Real.exp ((h 3 - h 0) + 3 * t)) atBot (𝓝 1)
  have h1 := tendsto_exp_const_add_pos_mul_atBot (h 1 - h 0) 1 (by norm_num)
  have h2 := tendsto_exp_const_add_pos_mul_atBot (h 2 - h 0) 2 (by norm_num)
  have h3 := tendsto_exp_const_add_pos_mul_atBot (h 3 - h 0) 3 (by norm_num)
  simpa only [bottomDenominator, one_mul, add_zero, zero_add] using
    (((tendsto_const_nhds.add h1).add h2).add h3)

theorem tendsto_bottomNumerator_atBot (h : Fin 4 → ℝ) :
    Tendsto (bottomNumerator h) atBot (𝓝 2) := by
  change Tendsto (fun t : ℝ ↦
    2 + 3 * Real.exp ((h 1 - h 0) + t) +
      4 * Real.exp ((h 2 - h 0) + 2 * t) +
      5 * Real.exp ((h 3 - h 0) + 3 * t)) atBot (𝓝 2)
  have h1 := tendsto_exp_const_add_pos_mul_atBot (h 1 - h 0) 1 (by norm_num)
  have h2 := tendsto_exp_const_add_pos_mul_atBot (h 2 - h 0) 2 (by norm_num)
  have h3 := tendsto_exp_const_add_pos_mul_atBot (h 3 - h 0) 3 (by norm_num)
  simpa only [bottomNumerator, one_mul, mul_zero, add_zero, zero_add] using
    (((tendsto_const_nhds.add (h1.const_mul 3)).add (h2.const_mul 4)).add
      (h3.const_mul 5))

theorem tendsto_mean_atBot (h : Fin 4 → ℝ) :
    Tendsto (mean h) atBot (𝓝 2) := by
  rw [show mean h = bottomNumerator h / bottomDenominator h from by
    ext t
    exact mean_eq_bottom_scaled h t]
  simpa only [div_one] using
    (tendsto_bottomNumerator_atBot h).div (tendsto_bottomDenominator_atBot h)
      (by norm_num : (1 : ℝ) ≠ 0)

/-! ## Exact inversion on the open support interval -/

theorem exists_mean_eq_of_mem_Ioo (h : Fin 4 → ℝ) {T : ℝ}
    (hT : T ∈ Set.Ioo 2 5) : ∃ t : ℝ, mean h t = T := by
  have haEventually : ∀ᶠ t : ℝ in atBot, mean h t < T :=
    (tendsto_mean_atBot h).eventually (Iio_mem_nhds hT.1)
  have hbEventually : ∀ᶠ t : ℝ in atTop, T < mean h t :=
    (tendsto_mean_atTop h).eventually (Ioi_mem_nhds hT.2)
  obtain ⟨a, ha⟩ := haEventually.exists
  obtain ⟨b, hb⟩ := hbEventually.exists
  exact Set.mem_range.mp <|
    mem_range_of_exists_le_of_exists_ge (continuous_mean h) ⟨a, ha.le⟩ ⟨b, hb.le⟩

theorem mean_injective (h : Fin 4 → ℝ) : Function.Injective (mean h) :=
  (strictMono_mean h).injective

theorem existsUnique_mean_eq_of_mem_Ioo (h : Fin 4 → ℝ) {T : ℝ}
    (hT : T ∈ Set.Ioo 2 5) : ∃! t : ℝ, mean h t = T := by
  obtain ⟨t, ht⟩ := exists_mean_eq_of_mem_Ioo h hT
  refine ⟨t, ht, ?_⟩
  intro u hu
  exact mean_injective h (hu.trans ht.symm)

end

end Erdos625.ProfileEntropyS4
