import Erdos625.PhaseEstimates
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Zero-safe uniform factorial bounds for coloring profiles

This module packages the Robbins bounds from `PhaseEstimates` in a form suited
to the profile sum in manuscript equation (4.3).  The entropy main term is
defined by a branch at zero, so the zero-coordinate case never requires a
logarithm of zero.  All estimates are finite and explicit.
-/

namespace Erdos625

open scoped BigOperators

/-! ## One-coordinate bounds -/

/-- The zero-safe entropy main term for `log (m!)`.

At `m = 0` this is defined to be zero directly.  At positive `m` it is the
usual expression `m * log m - m`. -/
noncomputable def factorialEntropyMain (m : ℕ) : ℝ :=
  if m = 0 then 0 else (m : ℝ) * Real.log (m : ℝ) - m

/-- A coarse explicit error that is uniform at zero and grows only
logarithmically. -/
noncomputable def factorialLogErrorBound (m : ℕ) : ℝ :=
  Real.log ((m + 1 : ℕ) : ℝ) + 4

@[simp] theorem factorialEntropyMain_zero : factorialEntropyMain 0 = 0 := by
  simp [factorialEntropyMain]

theorem factorialEntropyMain_of_pos {m : ℕ} (hm : 0 < m) :
    factorialEntropyMain m = (m : ℝ) * Real.log (m : ℝ) - m := by
  simp [factorialEntropyMain, hm.ne']

theorem factorialLogErrorBound_nonneg (m : ℕ) :
    0 ≤ factorialLogErrorBound m := by
  have hlog : 0 ≤ Real.log ((m + 1 : ℕ) : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega : m + 1 ≠ 0))
  simp only [factorialLogErrorBound]
  linarith

/-- The entropy main term is a lower bound for `log (m!)`, including `m = 0`.
-/
theorem factorialEntropyMain_le_log_factorial (m : ℕ) :
    factorialEntropyMain m ≤ Real.log (m.factorial : ℝ) := by
  rcases m with _ | m
  · simp [factorialEntropyMain]
  · have hm : 0 < m + 1 := Nat.succ_pos m
    have hR := stirlingLogRemainder_nonneg hm
    have hLogM : 0 ≤ Real.log ((m + 1 : ℕ) : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast hm)
    have hLogTwoPi : 0 < Real.log (2 * Real.pi) := by
      apply Real.log_pos
      have hpi := Real.pi_gt_three
      nlinarith
    rw [factorialEntropyMain_of_pos hm]
    simp only [stirlingLogRemainder] at hR
    linarith

/-- Robbins' formula, weakened to a zero-safe `log (m+1) + 4` error. -/
theorem log_factorial_le_factorialEntropyMain_add_error (m : ℕ) :
    Real.log (m.factorial : ℝ) ≤
      factorialEntropyMain m + factorialLogErrorBound m := by
  rcases m with _ | m
  · norm_num [factorialEntropyMain, factorialLogErrorBound]
  · have hm : 0 < m + 1 := Nat.succ_pos m
    have hR := stirlingLogRemainder_le hm
    have hLogMono :
        Real.log ((m + 1 : ℕ) : ℝ) ≤
          Real.log (((m + 1 : ℕ) + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast hm
      · exact_mod_cast (Nat.le_succ (m + 1))
    have hLogNonneg : 0 ≤ Real.log ((m + 1 : ℕ) : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast hm)
    have hLogTwoPi : Real.log (2 * Real.pi) ≤ 7 := by
      have hpos : 0 < 2 * Real.pi := by positivity
      have hlog := Real.log_le_sub_one_of_pos hpos
      have hpi := Real.pi_lt_four
      linarith
    have hInv : 1 / (12 * ((m + 1 : ℕ) : ℝ)) ≤ 1 / 12 := by
      have hmReal : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast hm
      rw [div_le_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 1)
        (by positivity : (0 : ℝ) < 12 * (m + 1 : ℕ))
        (by norm_num : (0 : ℝ) < 12)]
      nlinarith
    rw [factorialEntropyMain_of_pos hm]
    simp only [factorialLogErrorBound, stirlingLogRemainder] at hR ⊢
    linarith

/-- Absolute-error form of the zero-safe one-coordinate bound. -/
theorem abs_log_factorial_sub_factorialEntropyMain_le (m : ℕ) :
    |Real.log (m.factorial : ℝ) - factorialEntropyMain m| ≤
      factorialLogErrorBound m := by
  rw [abs_of_nonneg (sub_nonneg.mpr (factorialEntropyMain_le_log_factorial m))]
  linarith [log_factorial_le_factorialEntropyMain_add_error m]

/-! ## Finite profile sums -/

/-- Sum of the logarithms of the coordinate factorials. -/
noncomputable def profileLogFactorialSum {b : ℕ} (k : Fin b → ℕ) : ℝ :=
  ∑ i, Real.log ((k i).factorial : ℝ)

/-- Sum of the zero-safe entropy main terms. -/
noncomputable def profileFactorialEntropyMain {b : ℕ} (k : Fin b → ℕ) : ℝ :=
  ∑ i, factorialEntropyMain (k i)

/-- Sum of the coordinatewise explicit errors. -/
noncomputable def profileFactorialLogError {b : ℕ} (k : Fin b → ℕ) : ℝ :=
  ∑ i, factorialLogErrorBound (k i)

theorem profileFactorialEntropyMain_le_logFactorialSum {b : ℕ}
    (k : Fin b → ℕ) :
    profileFactorialEntropyMain k ≤ profileLogFactorialSum k := by
  classical
  simp only [profileFactorialEntropyMain, profileLogFactorialSum]
  exact Finset.sum_le_sum fun i _ ↦ factorialEntropyMain_le_log_factorial (k i)

theorem profileLogFactorialSum_le_main_add_error {b : ℕ}
    (k : Fin b → ℕ) :
    profileLogFactorialSum k ≤
      profileFactorialEntropyMain k + profileFactorialLogError k := by
  classical
  simp only [profileLogFactorialSum, profileFactorialEntropyMain,
    profileFactorialLogError, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ ↦
    log_factorial_le_factorialEntropyMain_add_error (k i)

/-- If every coordinate is at most `n`, the total Stirling error is bounded by
`b * (log (n+1) + 4)`.  This is valid for the empty profile `b = 0`. -/
theorem abs_profileLogFactorialSum_sub_main_le {b n : ℕ}
    (k : Fin b → ℕ) (hk : ∀ i, k i ≤ n) :
    |profileLogFactorialSum k - profileFactorialEntropyMain k| ≤
      (b : ℝ) * (Real.log ((n + 1 : ℕ) : ℝ) + 4) := by
  classical
  have hNonneg :
      0 ≤ profileLogFactorialSum k - profileFactorialEntropyMain k :=
    sub_nonneg.mpr (profileFactorialEntropyMain_le_logFactorialSum k)
  rw [abs_of_nonneg hNonneg]
  have hToError :
      profileLogFactorialSum k - profileFactorialEntropyMain k ≤
        profileFactorialLogError k := by
    linarith [profileLogFactorialSum_le_main_add_error k]
  calc
    profileLogFactorialSum k - profileFactorialEntropyMain k ≤
        profileFactorialLogError k := hToError
    _ ≤ ∑ _i : Fin b, (Real.log ((n + 1 : ℕ) : ℝ) + 4) := by
      simp only [profileFactorialLogError]
      apply Finset.sum_le_sum
      intro i _hi
      have hcast : (((k i + 1 : ℕ) : ℝ)) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (hk i)
      have hlog := Real.log_le_log (by positivity) hcast
      simp only [factorialLogErrorBound]
      linarith
    _ = (b : ℝ) * (Real.log ((n + 1 : ℕ) : ℝ) + 4) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]

@[simp] theorem profileLogFactorialSum_empty (k : Fin 0 → ℕ) :
    profileLogFactorialSum k = 0 := by
  simp [profileLogFactorialSum]

@[simp] theorem profileFactorialEntropyMain_empty (k : Fin 0 → ℕ) :
    profileFactorialEntropyMain k = 0 := by
  simp [profileFactorialEntropyMain]

end Erdos625
