import Erdos625.ConfigurationModelProbability

/-!
# Degree moments and configuration-cell parameters

This module isolates the finite arithmetic used in manuscript (9.13)--(9.14).
For a nonnegative integer degree family of total mass m, bounded pointwise
by U, its second and third moments are at most U m and U squared times m.

The second half applies those inequalities to the configuration-cell
parameter. Exact finite factorization identities are stated for every m.
Bounds that cancel a denominator explicitly assume positive m; the zero-total
case is recorded separately. No asymptotic estimate is asserted here.
-/

namespace Erdos625

open scoped BigOperators ENNReal

/-! ## Capped moments of a finite degree family -/

/-- A capped natural-valued family of total m has second moment at most U m. -/
theorem degreeSquareSum_le_cap_mul_total
    {I : Type*} [Fintype I] (d : I → ℕ) (U m : ℕ)
    (hcap : ∀ i, d i ≤ U) (htotal : ∑ i, d i = m) :
    ∑ i, d i ^ 2 ≤ U * m := by
  calc
    ∑ i, d i ^ 2 ≤ ∑ i, U * d i := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [pow_two, mul_comm] using
        Nat.mul_le_mul_right (d i) (hcap i)
    _ = U * m := by rw [← Finset.mul_sum, htotal]

/-- A capped natural-valued family of total m has third moment at most
U squared times m. -/
theorem degreeCubeSum_le_cap_sq_mul_total
    {I : Type*} [Fintype I] (d : I → ℕ) (U m : ℕ)
    (hcap : ∀ i, d i ≤ U) (htotal : ∑ i, d i = m) :
    ∑ i, d i ^ 3 ≤ U ^ 2 * m := by
  calc
    ∑ i, d i ^ 3 ≤ ∑ i, U ^ 2 * d i := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        d i ^ 3 = d i ^ 2 * d i := by ring
        _ ≤ U ^ 2 * d i :=
          Nat.mul_le_mul_right (d i) (Nat.pow_le_pow_left (hcap i) 2)
    _ = U ^ 2 * m := by rw [← Finset.mul_sum, htotal]

/-- Real-cast form of the capped second-moment inequality. -/
theorem degreeSquareSum_real_le_cap_mul_total
    {I : Type*} [Fintype I] (d : I → ℕ) (U m : ℕ)
    (hcap : ∀ i, d i ≤ U) (htotal : ∑ i, d i = m) :
    ∑ i, (d i : ℝ) ^ 2 ≤ (U : ℝ) * (m : ℝ) := by
  exact_mod_cast degreeSquareSum_le_cap_mul_total d U m hcap htotal

/-- Real-cast form of the capped third-moment inequality. -/
theorem degreeCubeSum_real_le_cap_sq_mul_total
    {I : Type*} [Fintype I] (d : I → ℕ) (U m : ℕ)
    (hcap : ∀ i, d i ≤ U) (htotal : ∑ i, d i = m) :
    ∑ i, (d i : ℝ) ^ 3 ≤ (U : ℝ) ^ 2 * (m : ℝ) := by
  exact_mod_cast degreeCubeSum_le_cap_sq_mul_total d U m hcap htotal

/-- Extended-nonnegative-real form of the capped second-moment inequality. -/
theorem degreeSquareSum_ennreal_le_cap_mul_total
    {I : Type*} [Fintype I] (d : I → ℕ) (U m : ℕ)
    (hcap : ∀ i, d i ≤ U) (htotal : ∑ i, d i = m) :
    ∑ i, (d i : ℝ≥0∞) ^ 2 ≤ (U : ℝ≥0∞) * (m : ℝ≥0∞) := by
  exact_mod_cast degreeSquareSum_le_cap_mul_total d U m hcap htotal

/-- Extended-nonnegative-real form of the capped third-moment inequality. -/
theorem degreeCubeSum_ennreal_le_cap_sq_mul_total
    {I : Type*} [Fintype I] (d : I → ℕ) (U m : ℕ)
    (hcap : ∀ i, d i ≤ U) (htotal : ∑ i, d i = m) :
    ∑ i, (d i : ℝ≥0∞) ^ 3 ≤
      (U : ℝ≥0∞) ^ 2 * (m : ℝ≥0∞) := by
  exact_mod_cast degreeCubeSum_le_cap_sq_mul_total d U m hcap htotal

/-! ## Exact finite theta factorizations -/

/-- Exact row factorization of the squared cell parameters, valid for all m. -/
theorem sum_configurationCellTheta_sq_row
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (m : ℕ) (a : A) :
    ∑ b, configurationCellTheta row col m a b ^ 2 =
      (eulerENNReal / (m : ℝ≥0∞)) ^ 2 *
        (row a : ℝ≥0∞) ^ 2 *
        ∑ b, (col b : ℝ≥0∞) ^ 2 := by
  have hpoint : ∀ b : B,
      configurationCellTheta row col m a b ^ 2 =
        ((eulerENNReal / (m : ℝ≥0∞)) ^ 2 *
          (row a : ℝ≥0∞) ^ 2) *
          (col b : ℝ≥0∞) ^ 2 := by
    intro b
    simp only [configurationCellTheta, div_eq_mul_inv]
    ring
  simp_rw [hpoint]
  rw [Finset.mul_sum]

/-- Exact column factorization of the squared cell parameters, valid for all m. -/
theorem sum_configurationCellTheta_sq_column
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (m : ℕ) (b : B) :
    ∑ a, configurationCellTheta row col m a b ^ 2 =
      (eulerENNReal / (m : ℝ≥0∞)) ^ 2 *
        (col b : ℝ≥0∞) ^ 2 *
        ∑ a, (row a : ℝ≥0∞) ^ 2 := by
  have hpoint : ∀ a : A,
      configurationCellTheta row col m a b ^ 2 =
        ((eulerENNReal / (m : ℝ≥0∞)) ^ 2 *
          (col b : ℝ≥0∞) ^ 2) *
          (row a : ℝ≥0∞) ^ 2 := by
    intro a
    simp only [configurationCellTheta, div_eq_mul_inv]
    ring
  simp_rw [hpoint]
  rw [Finset.mul_sum]

/-- Exact factorization of the global cubic theta sum, valid for all m. -/
theorem sum_configurationCellTheta_cube
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (m : ℕ) :
    (∑ a, ∑ b, configurationCellTheta row col m a b ^ 3) =
      (eulerENNReal / (m : ℝ≥0∞)) ^ 3 *
        (∑ a, (row a : ℝ≥0∞) ^ 3) *
        (∑ b, (col b : ℝ≥0∞) ^ 3) := by
  have hpoint : ∀ a : A, ∀ b : B,
      configurationCellTheta row col m a b ^ 3 =
        (eulerENNReal / (m : ℝ≥0∞)) ^ 3 *
          (row a : ℝ≥0∞) ^ 3 * (col b : ℝ≥0∞) ^ 3 := by
    intro a b
    simp only [configurationCellTheta, div_eq_mul_inv]
    ring
  simp_rw [hpoint]
  calc
    (∑ a, ∑ b,
        (eulerENNReal / (m : ℝ≥0∞)) ^ 3 *
          (row a : ℝ≥0∞) ^ 3 * (col b : ℝ≥0∞) ^ 3) =
        ∑ a,
          ((eulerENNReal / (m : ℝ≥0∞)) ^ 3 *
            (row a : ℝ≥0∞) ^ 3) *
            (∑ b, (col b : ℝ≥0∞) ^ 3) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
    _ = (∑ a,
          (eulerENNReal / (m : ℝ≥0∞)) ^ 3 *
            (row a : ℝ≥0∞) ^ 3) *
          (∑ b, (col b : ℝ≥0∞) ^ 3) := by
      rw [Finset.sum_mul]
    _ = (eulerENNReal / (m : ℝ≥0∞)) ^ 3 *
          (∑ a, (row a : ℝ≥0∞) ^ 3) *
          (∑ b, (col b : ℝ≥0∞) ^ 3) := by
      congr 1
      rw [Finset.mul_sum]

/-! ## Bounds before and after positive-mass cancellation -/

/-- Row-square theta bound before cancelling m. -/
theorem sum_configurationCellTheta_sq_row_le_raw
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (m U : ℕ) (a : A)
    (hcolCap : ∀ b, col b ≤ U) (hcolTotal : ∑ b, col b = m) :
    ∑ b, configurationCellTheta row col m a b ^ 2 ≤
      (eulerENNReal / (m : ℝ≥0∞)) ^ 2 *
        (row a : ℝ≥0∞) ^ 2 *
        ((U : ℝ≥0∞) * (m : ℝ≥0∞)) := by
  rw [sum_configurationCellTheta_sq_row]
  exact mul_le_mul_right
    (degreeSquareSum_ennreal_le_cap_mul_total col U m hcolCap hcolTotal)
    ((eulerENNReal / (m : ℝ≥0∞)) ^ 2 * (row a : ℝ≥0∞) ^ 2)

/-- Column-square theta bound before cancelling m. -/
theorem sum_configurationCellTheta_sq_column_le_raw
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (m U : ℕ) (b : B)
    (hrowCap : ∀ a, row a ≤ U) (hrowTotal : ∑ a, row a = m) :
    ∑ a, configurationCellTheta row col m a b ^ 2 ≤
      (eulerENNReal / (m : ℝ≥0∞)) ^ 2 *
        (col b : ℝ≥0∞) ^ 2 *
        ((U : ℝ≥0∞) * (m : ℝ≥0∞)) := by
  rw [sum_configurationCellTheta_sq_column]
  exact mul_le_mul_right
    (degreeSquareSum_ennreal_le_cap_mul_total row U m hrowCap hrowTotal)
    ((eulerENNReal / (m : ℝ≥0∞)) ^ 2 * (col b : ℝ≥0∞) ^ 2)

/-- Cancellation identity used in the positive-total square bounds. -/
private theorem normalizeThetaSquareBound
    (e r U : ℝ≥0∞) (m : ℕ) (hm : 0 < m) :
    (e / (m : ℝ≥0∞)) ^ 2 * r ^ 2 *
        (U * (m : ℝ≥0∞)) =
      e ^ 2 * r ^ 2 * U / (m : ℝ≥0∞) := by
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hmt : (m : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top m
  apply (ENNReal.eq_div_iff hm0 hmt).2
  rw [div_eq_mul_inv]
  calc
    (m : ℝ≥0∞) *
        ((e * (m : ℝ≥0∞)⁻¹) ^ 2 * r ^ 2 *
          (U * (m : ℝ≥0∞))) =
        e ^ 2 * r ^ 2 * U *
          ((m : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹) ^ 2 := by ring
    _ = e ^ 2 * r ^ 2 * U := by
      rw [ENNReal.mul_inv_cancel hm0 hmt, one_pow, mul_one]

/-- Positive-total row-square bound in cancelled form. -/
theorem sum_configurationCellTheta_sq_row_le
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (m U : ℕ) (a : A)
    (hm : 0 < m)
    (hcolCap : ∀ b, col b ≤ U) (hcolTotal : ∑ b, col b = m) :
    ∑ b, configurationCellTheta row col m a b ^ 2 ≤
      eulerENNReal ^ 2 * (row a : ℝ≥0∞) ^ 2 *
        (U : ℝ≥0∞) / (m : ℝ≥0∞) := by
  calc
    ∑ b, configurationCellTheta row col m a b ^ 2 ≤
        (eulerENNReal / (m : ℝ≥0∞)) ^ 2 *
          (row a : ℝ≥0∞) ^ 2 *
          ((U : ℝ≥0∞) * (m : ℝ≥0∞)) :=
      sum_configurationCellTheta_sq_row_le_raw
        row col m U a hcolCap hcolTotal
    _ = eulerENNReal ^ 2 * (row a : ℝ≥0∞) ^ 2 *
        (U : ℝ≥0∞) / (m : ℝ≥0∞) :=
      normalizeThetaSquareBound eulerENNReal (row a : ℝ≥0∞)
        (U : ℝ≥0∞) m hm

/-- Positive-total column-square bound in cancelled form. -/
theorem sum_configurationCellTheta_sq_column_le
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (m U : ℕ) (b : B)
    (hm : 0 < m)
    (hrowCap : ∀ a, row a ≤ U) (hrowTotal : ∑ a, row a = m) :
    ∑ a, configurationCellTheta row col m a b ^ 2 ≤
      eulerENNReal ^ 2 * (col b : ℝ≥0∞) ^ 2 *
        (U : ℝ≥0∞) / (m : ℝ≥0∞) := by
  calc
    ∑ a, configurationCellTheta row col m a b ^ 2 ≤
        (eulerENNReal / (m : ℝ≥0∞)) ^ 2 *
          (col b : ℝ≥0∞) ^ 2 *
          ((U : ℝ≥0∞) * (m : ℝ≥0∞)) :=
      sum_configurationCellTheta_sq_column_le_raw
        row col m U b hrowCap hrowTotal
    _ = eulerENNReal ^ 2 * (col b : ℝ≥0∞) ^ 2 *
        (U : ℝ≥0∞) / (m : ℝ≥0∞) :=
      normalizeThetaSquareBound eulerENNReal (col b : ℝ≥0∞)
        (U : ℝ≥0∞) m hm

/-- Uniform row-square bound after also using the row cap. -/
theorem sum_configurationCellTheta_sq_row_le_uniform
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (m U : ℕ) (a : A)
    (hm : 0 < m) (hrowCap : ∀ a, row a ≤ U)
    (hcolCap : ∀ b, col b ≤ U) (hcolTotal : ∑ b, col b = m) :
    ∑ b, configurationCellTheta row col m a b ^ 2 ≤
      eulerENNReal ^ 2 * (U : ℝ≥0∞) ^ 3 / (m : ℝ≥0∞) := by
  calc
    ∑ b, configurationCellTheta row col m a b ^ 2 ≤
        eulerENNReal ^ 2 * (row a : ℝ≥0∞) ^ 2 *
          (U : ℝ≥0∞) / (m : ℝ≥0∞) :=
      sum_configurationCellTheta_sq_row_le
        row col m U a hm hcolCap hcolTotal
    _ ≤ eulerENNReal ^ 2 * (U : ℝ≥0∞) ^ 3 /
        (m : ℝ≥0∞) := by
      apply ENNReal.div_le_div
      · have hr : (row a : ℝ≥0∞) ^ 2 ≤ (U : ℝ≥0∞) ^ 2 := by
          exact pow_le_pow_left' (by exact_mod_cast hrowCap a) 2
        calc
          eulerENNReal ^ 2 * (row a : ℝ≥0∞) ^ 2 * (U : ℝ≥0∞) ≤
              eulerENNReal ^ 2 * (U : ℝ≥0∞) ^ 2 * (U : ℝ≥0∞) :=
            mul_le_mul_left (mul_le_mul_right hr (eulerENNReal ^ 2))
              (U : ℝ≥0∞)
          _ = eulerENNReal ^ 2 * (U : ℝ≥0∞) ^ 3 := by ring
      · rfl

/-- Uniform column-square bound after also using the column cap. -/
theorem sum_configurationCellTheta_sq_column_le_uniform
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (m U : ℕ) (b : B)
    (hm : 0 < m) (hrowCap : ∀ a, row a ≤ U)
    (hcolCap : ∀ b, col b ≤ U) (hrowTotal : ∑ a, row a = m) :
    ∑ a, configurationCellTheta row col m a b ^ 2 ≤
      eulerENNReal ^ 2 * (U : ℝ≥0∞) ^ 3 / (m : ℝ≥0∞) := by
  calc
    ∑ a, configurationCellTheta row col m a b ^ 2 ≤
        eulerENNReal ^ 2 * (col b : ℝ≥0∞) ^ 2 *
          (U : ℝ≥0∞) / (m : ℝ≥0∞) :=
      sum_configurationCellTheta_sq_column_le
        row col m U b hm hrowCap hrowTotal
    _ ≤ eulerENNReal ^ 2 * (U : ℝ≥0∞) ^ 3 /
        (m : ℝ≥0∞) := by
      apply ENNReal.div_le_div
      · have hc : (col b : ℝ≥0∞) ^ 2 ≤ (U : ℝ≥0∞) ^ 2 := by
          exact pow_le_pow_left' (by exact_mod_cast hcolCap b) 2
        calc
          eulerENNReal ^ 2 * (col b : ℝ≥0∞) ^ 2 * (U : ℝ≥0∞) ≤
              eulerENNReal ^ 2 * (U : ℝ≥0∞) ^ 2 * (U : ℝ≥0∞) :=
            mul_le_mul_left (mul_le_mul_right hc (eulerENNReal ^ 2))
              (U : ℝ≥0∞)
          _ = eulerENNReal ^ 2 * (U : ℝ≥0∞) ^ 3 := by ring
      · rfl

/-! ## The global cubic bound -/

/-- Global cubic theta bound before cancelling m. -/
theorem sum_configurationCellTheta_cube_le_raw
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (m U : ℕ)
    (hrowCap : ∀ a, row a ≤ U) (hcolCap : ∀ b, col b ≤ U)
    (hrowTotal : ∑ a, row a = m) (hcolTotal : ∑ b, col b = m) :
    (∑ a, ∑ b, configurationCellTheta row col m a b ^ 3) ≤
      (eulerENNReal / (m : ℝ≥0∞)) ^ 3 *
        ((U : ℝ≥0∞) ^ 2 * (m : ℝ≥0∞)) *
        ((U : ℝ≥0∞) ^ 2 * (m : ℝ≥0∞)) := by
  rw [sum_configurationCellTheta_cube]
  have hrow :=
    degreeCubeSum_ennreal_le_cap_sq_mul_total row U m hrowCap hrowTotal
  have hcol :=
    degreeCubeSum_ennreal_le_cap_sq_mul_total col U m hcolCap hcolTotal
  calc
    (eulerENNReal / (m : ℝ≥0∞)) ^ 3 *
        (∑ a, (row a : ℝ≥0∞) ^ 3) *
        (∑ b, (col b : ℝ≥0∞) ^ 3) ≤
      (eulerENNReal / (m : ℝ≥0∞)) ^ 3 *
        ((U : ℝ≥0∞) ^ 2 * (m : ℝ≥0∞)) *
        (∑ b, (col b : ℝ≥0∞) ^ 3) :=
      mul_le_mul_left
        (mul_le_mul_right hrow
          ((eulerENNReal / (m : ℝ≥0∞)) ^ 3))
        (∑ b, (col b : ℝ≥0∞) ^ 3)
    _ ≤ (eulerENNReal / (m : ℝ≥0∞)) ^ 3 *
        ((U : ℝ≥0∞) ^ 2 * (m : ℝ≥0∞)) *
        ((U : ℝ≥0∞) ^ 2 * (m : ℝ≥0∞)) :=
      mul_le_mul_right hcol
        ((eulerENNReal / (m : ℝ≥0∞)) ^ 3 *
          ((U : ℝ≥0∞) ^ 2 * (m : ℝ≥0∞)))

/-- Cancellation identity used in the positive-total cubic bound. -/
private theorem normalizeThetaCubeBound
    (e U : ℝ≥0∞) (m : ℕ) (hm : 0 < m) :
    (e / (m : ℝ≥0∞)) ^ 3 *
        (U ^ 2 * (m : ℝ≥0∞)) * (U ^ 2 * (m : ℝ≥0∞)) =
      e ^ 3 * U ^ 4 / (m : ℝ≥0∞) := by
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hmt : (m : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top m
  apply (ENNReal.eq_div_iff hm0 hmt).2
  rw [div_eq_mul_inv]
  calc
    (m : ℝ≥0∞) *
        ((e * (m : ℝ≥0∞)⁻¹) ^ 3 *
          (U ^ 2 * (m : ℝ≥0∞)) * (U ^ 2 * (m : ℝ≥0∞))) =
        e ^ 3 * U ^ 4 *
          ((m : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹) ^ 3 := by ring
    _ = e ^ 3 * U ^ 4 := by
      rw [ENNReal.mul_inv_cancel hm0 hmt, one_pow, mul_one]

/-- Positive-total global cubic theta bound in cancelled form. -/
theorem sum_configurationCellTheta_cube_le
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (m U : ℕ) (hm : 0 < m)
    (hrowCap : ∀ a, row a ≤ U) (hcolCap : ∀ b, col b ≤ U)
    (hrowTotal : ∑ a, row a = m) (hcolTotal : ∑ b, col b = m) :
    (∑ a, ∑ b, configurationCellTheta row col m a b ^ 3) ≤
      eulerENNReal ^ 3 * (U : ℝ≥0∞) ^ 4 / (m : ℝ≥0∞) := by
  calc
    (∑ a, ∑ b, configurationCellTheta row col m a b ^ 3) ≤
        (eulerENNReal / (m : ℝ≥0∞)) ^ 3 *
          ((U : ℝ≥0∞) ^ 2 * (m : ℝ≥0∞)) *
          ((U : ℝ≥0∞) ^ 2 * (m : ℝ≥0∞)) :=
      sum_configurationCellTheta_cube_le_raw
        row col m U hrowCap hcolCap hrowTotal hcolTotal
    _ = eulerENNReal ^ 3 * (U : ℝ≥0∞) ^ 4 /
        (m : ℝ≥0∞) :=
      normalizeThetaCubeBound eulerENNReal (U : ℝ≥0∞) m hm

/-! ## The zero-total branch -/

/-- Zero row total forces every cell parameter with denominator zero to zero. -/
theorem configurationCellTheta_eq_zero_of_rowTotal_zero
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (hrowTotal : ∑ a, row a = 0)
    (a : A) (b : B) :
    configurationCellTheta row col 0 a b = 0 := by
  have hrowa : row a = 0 :=
    (Finset.sum_eq_zero_iff.mp hrowTotal) a (Finset.mem_univ a)
  simp [configurationCellTheta, hrowa]

/-- Zero column total gives the symmetric vanishing statement. -/
theorem configurationCellTheta_eq_zero_of_colTotal_zero
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (hcolTotal : ∑ b, col b = 0)
    (a : A) (b : B) :
    configurationCellTheta row col 0 a b = 0 := by
  have hcolb : col b = 0 :=
    (Finset.sum_eq_zero_iff.mp hcolTotal) b (Finset.mem_univ b)
  simp [configurationCellTheta, hcolb]

/-- The global cubic theta sum vanishes in the zero-total branch. -/
theorem sum_configurationCellTheta_cube_eq_zero_of_total_zero
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (hrowTotal : ∑ a, row a = 0) :
    (∑ a, ∑ b, configurationCellTheta row col 0 a b ^ 3) = 0 := by
  simp_rw [configurationCellTheta_eq_zero_of_rowTotal_zero
    row col hrowTotal]
  simp

end Erdos625
