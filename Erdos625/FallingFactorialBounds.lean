import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Lower bounds for descending factorials

This module proves the effective lower bound used in manuscript (6.10):
`(m / exp 1)^x ≤ m.descFactorial x` for `0 < m` and `x ≤ m`.

The finite core compares geometric means.  The top `x` factors in
`m.descFactorial x` have geometric mean at least that of all factors in `m!`,
which is encoded without roots as `(m!)^x ≤ ((m)_x)^m`.  Mathlib's effective
Stirling lower bound then supplies the constant `exp 1`.
-/

namespace Erdos625

open scoped ENNReal

/-- Every factor in `(m)_x` is at least `m-x+1`. -/
theorem pow_sub_add_one_le_descFactorial
    {m x : ℕ} (hx : x ≤ m) :
    (m - x + 1) ^ x ≤ m.descFactorial x := by
  induction x with
  | zero => simp
  | succ k ih =>
      have hk : k ≤ m := k.le_succ.trans hx
      have hbase : (m - k) ^ k ≤ (m - k + 1) ^ k :=
        Nat.pow_le_pow_left (Nat.le_succ _) _
      have hpow : (m - k) ^ k ≤ m.descFactorial k :=
        hbase.trans (ih hk)
      have hsub : m - (k + 1) + 1 = m - k := by omega
      simpa [Nat.descFactorial_succ, pow_succ', hsub] using
        Nat.mul_le_mul_left (m - k) hpow

/-- The geometric mean of the top `x` factors is at least the geometric mean
of all `m` factors, written without roots. -/
theorem factorial_pow_le_descFactorial_pow
    {m x : ℕ} (hx : x ≤ m) :
    m.factorial ^ x ≤ (m.descFactorial x) ^ m := by
  let r := m - x
  have hrx : r + x = m := Nat.sub_add_cancel hx
  have hbottom : r.factorial ^ x ≤ (m.descFactorial x) ^ r := by
    calc
      r.factorial ^ x ≤ (r ^ r) ^ x :=
        Nat.pow_le_pow_left r.factorial_le_pow _
      _ = r ^ (r * x) := by rw [pow_mul]
      _ ≤ (r + 1) ^ (x * r) := by
        rw [Nat.mul_comm r x]
        exact Nat.pow_le_pow_left (Nat.le_succ _) _
      _ = ((r + 1) ^ x) ^ r := by rw [pow_mul]
      _ ≤ (m.descFactorial x) ^ r := by
        apply Nat.pow_le_pow_left
        simpa [r] using pow_sub_add_one_le_descFactorial hx
  calc
    m.factorial ^ x = (r.factorial * m.descFactorial x) ^ x := by
      rw [Nat.factorial_mul_descFactorial hx]
    _ = r.factorial ^ x * (m.descFactorial x) ^ x := by rw [mul_pow]
    _ ≤ (m.descFactorial x) ^ r * (m.descFactorial x) ^ x :=
      Nat.mul_le_mul_right _ hbottom
    _ = (m.descFactorial x) ^ (r + x) := (pow_add _ _ _).symm
    _ = (m.descFactorial x) ^ m := by rw [hrx]

/-- Effective global falling-factorial lower bound, equation (6.10). -/
theorem real_div_exp_one_pow_le_descFactorial
    {m x : ℕ} (hm : 0 < m) (hx : x ≤ m) :
    ((m : ℝ) / Real.exp 1) ^ x ≤ (m.descFactorial x : ℝ) := by
  have hm_one : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (m : ℝ)) := by
    rw [Real.one_le_sqrt]
    have hpi := Real.pi_gt_three
    nlinarith
  have hbaseNonneg : 0 ≤ ((m : ℝ) / Real.exp 1) ^ m := by positivity
  have hbase : ((m : ℝ) / Real.exp 1) ^ m ≤ (m.factorial : ℝ) := by
    calc
      ((m : ℝ) / Real.exp 1) ^ m =
          1 * ((m : ℝ) / Real.exp 1) ^ m := by rw [one_mul]
      _ ≤ Real.sqrt (2 * Real.pi * (m : ℝ)) *
          ((m : ℝ) / Real.exp 1) ^ m :=
        mul_le_mul_of_nonneg_right hsqrt hbaseNonneg
      _ ≤ (m.factorial : ℝ) := Stirling.le_factorial_stirling m
  have hNat := factorial_pow_le_descFactorial_pow hx
  have hpow :
      (((m : ℝ) / Real.exp 1) ^ x) ^ m ≤
        ((m.descFactorial x : ℝ)) ^ m := by
    calc
      (((m : ℝ) / Real.exp 1) ^ x) ^ m =
          (((m : ℝ) / Real.exp 1) ^ m) ^ x := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm x m]
      _ ≤ ((m.factorial : ℝ)) ^ x :=
        pow_le_pow_left₀ hbaseNonneg hbase _
      _ ≤ ((m.descFactorial x : ℝ)) ^ m := by
        exact_mod_cast hNat
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) hm.ne').mp hpow

/-- Euler's number, embedded in `ℝ≥0∞`.  Naming this constant keeps the
configuration-model bound legible while retaining its exact value. -/
noncomputable def eulerENNReal : ℝ≥0∞ := ENNReal.ofReal (Real.exp 1)

/-- `ℝ≥0∞` form of the effective falling-factorial lower bound (6.10). -/
theorem ennreal_div_euler_pow_le_descFactorial
    {m x : ℕ} (hm : 0 < m) (hx : x ≤ m) :
    ((m : ℝ≥0∞) / eulerENNReal) ^ x ≤
      (m.descFactorial x : ℝ≥0∞) := by
  have h := ENNReal.ofReal_le_ofReal
    (real_div_exp_one_pow_le_descFactorial hm hx)
  have hbase : 0 ≤ (m : ℝ) / Real.exp 1 :=
    div_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  rw [ENNReal.ofReal_pow hbase,
    ENNReal.ofReal_div_of_pos (Real.exp_pos 1),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast] at h
  exact h

end Erdos625
