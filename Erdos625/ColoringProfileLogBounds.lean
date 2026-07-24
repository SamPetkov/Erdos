import Erdos625.ColoringProfileLogWeight
import Erdos625.ColoringProfileFactorialBounds

/-!
# Zero-safe upper bounds for exact profile log-weights

This module combines the exact logarithmic first-moment identity with the
zero-safe factorial estimates.  It isolates the discrete upper expression
that precedes the variational maximization in manuscript (4.3).

The result is finite and explicit.  It does not yet identify the constrained
maximum with `L_+(n,k)` or make an asymptotic claim.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- The entropy-form upper main term for one exact coloring profile. -/
def profileStirlingUpperMain {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) : ℝ :=
  factorialEntropyMain n -
    ∑ i : Fin b,
      (k i : ℝ) * Real.log (Nat.factorial (i.1 + 1) : ℝ) -
    profileFactorialEntropyMain k -
    (ColoringProfile.forbiddenEdges k : ℝ) * Real.log 2

/-- The exact log-weight is at most its zero-safe entropy main term plus the
single numerator-factorial error. -/
theorem profileLogWeight_le_stirlingUpperMain_add_error {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) :
    profileLogWeight n k ≤
      profileStirlingUpperMain n k + factorialLogErrorBound n := by
  have hn := log_factorial_le_factorialEntropyMain_add_error n
  have hk := profileFactorialEntropyMain_le_logFactorialSum k
  simp only [profileLogFactorialSum] at hk
  unfold profileLogWeight profileStirlingUpperMain
  linarith

/-- Under the mass constraint, the logarithm of the actual exact-profile
expectation satisfies the same explicit upper bound. -/
theorem log_profileColoringExpectation_toReal_le_stirlingUpperMain_add_error
    {b : ℕ} (n : ℕ) (k : ColoringProfile b)
    (hMass : ColoringProfile.vertexMass k = n) :
    Real.log (profileColoringExpectation n k).toReal ≤
      profileStirlingUpperMain n k + factorialLogErrorBound n := by
  rw [log_profileColoringExpectation_toReal_eq_profileLogWeight n k hMass]
  exact profileLogWeight_le_stirlingUpperMain_add_error n k

/-- Any common real upper bound for the explicit Stirling expression gives
an `ENNReal` exponential upper bound for the actual exact-profile
expectation. -/
theorem profileColoringExpectation_le_of_stirlingUpperMain_add_error_le
    {b : ℕ} (n : ℕ) (k : ColoringProfile b) (L : ℝ)
    (hMass : ColoringProfile.vertexMass k = n)
    (hL : profileStirlingUpperMain n k + factorialLogErrorBound n ≤ L) :
    profileColoringExpectation n k ≤ ENNReal.ofReal (Real.exp L) := by
  have hpos : 0 < profileColoringExpectation n k :=
    profileColoringExpectation_pos n k hMass
  have htop : profileColoringExpectation n k ≠ ⊤ := by
    rw [profileColoringExpectation_eq_enumerativeCoefficient_mul_of n k
      (profileEnumerationStatement n k hMass)]
    finiteness
  have hlog :
      Real.log (profileColoringExpectation n k).toReal ≤ L :=
    (log_profileColoringExpectation_toReal_le_stirlingUpperMain_add_error
      n k hMass).trans hL
  have hreal : (profileColoringExpectation n k).toReal ≤ Real.exp L :=
    (Real.log_le_iff_le_exp (ENNReal.toReal_pos hpos.ne' htop)).mp hlog
  apply (ENNReal.toReal_le_toReal htop (by finiteness)).mp
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg L)]
  exact hreal

end

end Erdos625
