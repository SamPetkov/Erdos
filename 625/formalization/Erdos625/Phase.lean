import Erdos625.Foundation
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Choose.Basic

/-!
# The elementary phase arithmetic

This module formalizes the exact definitions and identities from Sections 1--2
of the manuscript that do not require asymptotic analysis.  In particular, it
does **not** assert the phase expansion (2.2).

The integer phase is defined for every `n`.  Its natural-number version agrees
with that integer exactly on `PhaseDomain`, which records both the logarithmic
domain condition and the nonnegativity needed to pass through `Int.toNat`.
-/

namespace Erdos625

/-- The manuscript constant `q = log 2`. -/
noncomputable def q : ℝ := Real.log 2

theorem q_pos : 0 < q := by
  exact Real.log_pos (by norm_num : (1 : ℝ) < 2)

theorem q_ne_zero : q ≠ 0 := ne_of_gt q_pos

/-- Natural logarithm of the graph order, denoted `N` in the manuscript. -/
noncomputable def logOrder (n : ℕ) : ℝ := Real.log (n : ℝ)

/-- `log N`, denoted `w` in the manuscript. -/
noncomputable def logLogOrder (n : ℕ) : ℝ := Real.log (logOrder n)

/-- Base-two logarithm, expressed through the natural logarithm. -/
noncomputable def logBaseTwo (x : ℝ) : ℝ := Real.log x / q

/-- The real-valued independence-number phase `alpha_0` from (2.1). -/
noncomputable def alphaZero (n : ℕ) : ℝ :=
  2 * logBaseTwo (n : ℝ) -
    2 * logBaseTwo (logBaseTwo (n : ℝ)) +
    2 * logBaseTwo (Real.exp 1 / 2) + 1

/-- The floor phase as an integer.  This is total, even at small `n`. -/
noncomputable def phaseInt (n : ℕ) : ℤ := ⌊alphaZero n⌋

/-- The natural phase.  On `PhaseDomain` it is exactly the integer floor. -/
noncomputable def phaseNat (n : ℕ) : ℕ := (phaseInt n).toNat

/-- The fractional phase `delta = alpha_0 - floor(alpha_0)`. -/
noncomputable def phaseDelta (n : ℕ) : ℝ :=
  alphaZero n - (phaseInt n : ℝ)

/-- Safe domain for interpreting the floor phase as a natural class size.

The first conjunct makes the nested logarithm in `alphaZero` a logarithm of a
positive base-two logarithm.  The second is exactly what is needed for
`phaseNat` to retain, rather than truncate, the integer floor.
-/
def PhaseDomain (n : ℕ) : Prop := 1 < n ∧ 0 ≤ alphaZero n

theorem phaseDomain_logBaseTwo_pos {n : ℕ} (hn : PhaseDomain n) :
    0 < logBaseTwo (n : ℝ) := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn.1
  exact div_pos (Real.log_pos hn') q_pos

theorem phaseInt_le_alphaZero (n : ℕ) :
    (phaseInt n : ℝ) ≤ alphaZero n := by
  exact Int.floor_le (alphaZero n)

theorem alphaZero_lt_phaseInt_add_one (n : ℕ) :
    alphaZero n < (phaseInt n : ℝ) + 1 := by
  exact Int.lt_floor_add_one (alphaZero n)

theorem phaseDelta_nonneg (n : ℕ) : 0 ≤ phaseDelta n := by
  exact sub_nonneg.mpr (phaseInt_le_alphaZero n)

theorem phaseDelta_lt_one (n : ℕ) : phaseDelta n < 1 := by
  dsimp [phaseDelta]
  linarith [alphaZero_lt_phaseInt_add_one n]

theorem phaseDelta_mem_Ico (n : ℕ) : phaseDelta n ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨phaseDelta_nonneg n, phaseDelta_lt_one n⟩

theorem alphaZero_eq_phaseInt_add_delta (n : ℕ) :
    alphaZero n = (phaseInt n : ℝ) + phaseDelta n := by
  simp [phaseDelta]

theorem phaseInt_nonneg {n : ℕ} (hn : PhaseDomain n) : 0 ≤ phaseInt n := by
  exact Int.floor_nonneg.mpr hn.2

theorem phaseNat_cast_int {n : ℕ} (hn : PhaseDomain n) :
    (phaseNat n : ℤ) = phaseInt n := by
  simp [phaseNat, Int.toNat_of_nonneg (phaseInt_nonneg hn)]

theorem phaseNat_cast_real {n : ℕ} (hn : PhaseDomain n) :
    (phaseNat n : ℝ) = (phaseInt n : ℝ) := by
  exact_mod_cast phaseNat_cast_int hn

theorem alphaZero_eq_phaseNat_add_delta {n : ℕ} (hn : PhaseDomain n) :
    alphaZero n = (phaseNat n : ℝ) + phaseDelta n := by
  rw [phaseNat_cast_real hn]
  exact alphaZero_eq_phaseInt_add_delta n

/-- The first moment for independent `s`-sets in a graph on `v` vertices:
`choose v s * 2^(-choose s 2)`.  The reciprocal-power spelling avoids an
integer exponent while remaining exactly the displayed real number. -/
noncomputable def mu (v s : ℕ) : ℝ :=
  (v.choose s : ℝ) * ((2 : ℝ) ^ (s.choose 2))⁻¹

theorem mu_nonneg (v s : ℕ) : 0 ≤ mu v s := by
  unfold mu
  positivity

theorem mu_pos {v s : ℕ} (hsv : s ≤ v) : 0 < mu v s := by
  unfold mu
  exact mul_pos (by exact_mod_cast Nat.choose_pos hsv) (by positivity)

theorem mu_ne_zero {v s : ℕ} (hsv : s ≤ v) : mu v s ≠ 0 :=
  ne_of_gt (mu_pos hsv)

@[simp] theorem chooseTwo_succ (s : ℕ) :
    (s + 1).choose 2 = s.choose 2 + s := by
  rw [Nat.choose_succ_succ']
  simp [Nat.add_comm]

private theorem inv_two_pow_add_mul_pow (a b : ℕ) :
    ((2 : ℝ) ^ (a + b))⁻¹ * (2 : ℝ) ^ b = ((2 : ℝ) ^ a)⁻¹ := by
  calc
    ((2 : ℝ) ^ (a + b))⁻¹ * (2 : ℝ) ^ b =
        ((2 : ℝ) ^ a)⁻¹ * (((2 : ℝ) ^ b)⁻¹ * (2 : ℝ) ^ b) := by
          rw [pow_add, mul_inv_rev]
          ring
    _ = ((2 : ℝ) ^ a)⁻¹ := by
      rw [inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ b ≠ 0), mul_one]

/-- Denominator-free form of the first adjacent-size identity in (2.8).
It is valid without side conditions, including beyond `s = v`. -/
theorem mu_succ_mul_identity (v s : ℕ) :
    mu v (s + 1) * ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s =
      mu v s * ((v - s : ℕ) : ℝ) := by
  have hchoose := congrArg (fun x : ℕ ↦ (x : ℝ))
    (Nat.choose_succ_right_eq v s)
  norm_num only [Nat.cast_mul] at hchoose
  rw [mu, mu, chooseTwo_succ]
  calc
    (v.choose (s + 1) : ℝ) * ((2 : ℝ) ^ (s.choose 2 + s))⁻¹ *
          ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s =
        ((v.choose (s + 1) : ℝ) * ((s + 1 : ℕ) : ℝ)) *
          (((2 : ℝ) ^ (s.choose 2 + s))⁻¹ * (2 : ℝ) ^ s) := by ring
    _ = ((v.choose s : ℝ) * ((v - s : ℕ) : ℝ)) *
          ((2 : ℝ) ^ (s.choose 2))⁻¹ := by
      rw [hchoose, inv_two_pow_add_mul_pow]
    _ = (v.choose s : ℝ) * ((2 : ℝ) ^ (s.choose 2))⁻¹ *
          ((v - s : ℕ) : ℝ) := by ring

/-- The first ratio in (2.8), with the exact hypothesis ensuring that its
denominator `mu v s` is nonzero. -/
theorem mu_succ_div_identity {v s : ℕ} (hsv : s ≤ v) :
    mu v (s + 1) / mu v s =
      (((v - s : ℕ) : ℝ) / ((s + 1 : ℕ) : ℝ)) /
        (2 : ℝ) ^ s := by
  have hmu : mu v s ≠ 0 := mu_ne_zero hsv
  have hs : ((s + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hp : (2 : ℝ) ^ s ≠ 0 := by positivity
  field_simp
  simpa [mul_assoc, mul_left_comm, mul_comm] using mu_succ_mul_identity v s

/-- Denominator-free form of the second adjacent-size identity in (2.8). -/
theorem mu_pred_mul_identity {v s : ℕ} (hs : 0 < s) (hsv : s ≤ v) :
    mu v (s - 1) * (((v - s : ℕ) + 1 : ℕ) : ℝ) =
      mu v s * (s : ℝ) * (2 : ℝ) ^ (s - 1) := by
  have h := mu_succ_mul_identity v (s - 1)
  have hs' : s - 1 + 1 = s := by omega
  have hv : v - (s - 1) = v - s + 1 := by omega
  simpa only [hs', hv] using h.symm

/-- The second ratio in (2.8), with hypotheses making both displayed
denominators nonzero and making `s - 1` the intended predecessor. -/
theorem mu_pred_div_identity {v s : ℕ} (hs : 0 < s) (hsv : s ≤ v) :
    mu v (s - 1) / mu v s =
      ((s : ℝ) / (((v - s : ℕ) + 1 : ℕ) : ℝ)) *
        (2 : ℝ) ^ (s - 1) := by
  have hmu : mu v s ≠ 0 := mu_ne_zero hsv
  have hv : (((v - s : ℕ) + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  simpa [mul_assoc, mul_left_comm, mul_comm] using mu_pred_mul_identity hs hsv

end Erdos625
