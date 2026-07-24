import Erdos625.ColoringProfileEnumerationInjective

/-!
# Exact logarithmic weight of a finite coloring profile

This module takes the multiplication-form enumeration theorem for an
unordered coloring profile and derives the exact logarithmic form of the
finite first moment.  In particular, none of the proofs takes the logarithm
of a natural-number quotient: positivity is obtained first from the
multiplication identity, and every logarithm below has a positive argument.

The statements include the empty profile (`b = 0`, `n = 0`) and coordinates
equal to zero.  Empty products and sums, `0! = 1`, and zeroth powers therefore
need no exceptional convention.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

namespace ColoringProfile

/-- The arithmetic coefficient of every finite profile is strictly positive.
This is derived from the multiplication identity, not from the quotient
presentation of `Multiset.bell`. -/
theorem enumerativeCoefficient_pos {b : ℕ} (k : ColoringProfile b) :
    0 < enumerativeCoefficient k := by
  by_contra h
  have hzero : enumerativeCoefficient k = 0 := Nat.eq_zero_of_not_pos h
  have hfactorialZero : Nat.factorial (vertexMass k) = 0 := by
    rw [← enumerativeCoefficient_mul_coordinateDenominator_eq k, hzero]
    simp
  exact (Nat.factorial_ne_zero _) hfactorialZero

/-- Logarithm of the class-size factorial product, expanded coordinatewise. -/
private theorem log_classSizeFactorialProduct {b : ℕ}
    (k : ColoringProfile b) :
    Real.log
        ((∏ i : Fin b, (Nat.factorial (i.1 + 1)) ^ k i : ℕ) : ℝ) =
      ∑ i : Fin b,
        (k i : ℝ) * Real.log (Nat.factorial (i.1 + 1) : ℝ) := by
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_pow, Real.log_pow]
  · intro i _
    positivity

/-- Logarithm of the equal-size multiplicity factorial product, expanded
coordinatewise.  In particular, a zero coordinate contributes `log (0!) = 0`.
-/
private theorem log_coordinateFactorialProduct {b : ℕ}
    (k : ColoringProfile b) :
    Real.log ((∏ i : Fin b, Nat.factorial (k i) : ℕ) : ℝ) =
      ∑ i : Fin b, Real.log (Nat.factorial (k i) : ℝ) := by
  rw [Nat.cast_prod, Real.log_prod]
  intro i _
  positivity

/-- Exact logarithm of the arithmetic unordered-profile coefficient. -/
theorem log_enumerativeCoefficient_eq {b : ℕ} (k : ColoringProfile b) :
    Real.log (enumerativeCoefficient k : ℝ) =
      Real.log (Nat.factorial (vertexMass k) : ℝ) -
        ∑ i : Fin b,
          (k i : ℝ) * Real.log (Nat.factorial (i.1 + 1) : ℝ) -
        ∑ i : Fin b, Real.log (Nat.factorial (k i) : ℝ) := by
  let A : ℕ := enumerativeCoefficient k
  let B : ℕ := ∏ i : Fin b, (Nat.factorial (i.1 + 1)) ^ k i
  let C : ℕ := ∏ i : Fin b, Nat.factorial (k i)
  have hA : (A : ℝ) ≠ 0 := by
    exact_mod_cast (enumerativeCoefficient_pos k).ne'
  have hB : (B : ℝ) ≠ 0 := by
    dsimp only [B]
    positivity
  have hC : (C : ℝ) ≠ 0 := by
    dsimp only [C]
    positivity
  have hmulNat : A * B * C = Nat.factorial (vertexMass k) := by
    simpa only [A, B, C] using
      enumerativeCoefficient_mul_coordinateDenominator_eq k
  have hmulReal : (A : ℝ) * (B : ℝ) * (C : ℝ) =
      (Nat.factorial (vertexMass k) : ℝ) := by
    exact_mod_cast hmulNat
  have hlog : Real.log (A : ℝ) + Real.log (B : ℝ) +
      Real.log (C : ℝ) =
        Real.log (Nat.factorial (vertexMass k) : ℝ) := by
    calc
      Real.log (A : ℝ) + Real.log (B : ℝ) + Real.log (C : ℝ) =
          Real.log ((A : ℝ) * (B : ℝ)) + Real.log (C : ℝ) := by
            rw [Real.log_mul hA hB]
      _ = Real.log (((A : ℝ) * (B : ℝ)) * (C : ℝ)) := by
            rw [Real.log_mul (mul_ne_zero hA hB) hC]
      _ = Real.log (Nat.factorial (vertexMass k) : ℝ) := by
            rw [hmulReal]
  rw [show A = enumerativeCoefficient k by rfl,
    show B = ∏ i : Fin b, (Nat.factorial (i.1 + 1)) ^ k i by rfl,
    show C = ∏ i : Fin b, Nat.factorial (k i) by rfl,
    log_classSizeFactorialProduct, log_coordinateFactorialProduct] at hlog
  linarith

end ColoringProfile

/-- The exact finite real log-weight in equation (4.2). -/
noncomputable def profileLogWeight {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) : ℝ :=
  Real.log (Nat.factorial n : ℝ) -
    ∑ i : Fin b,
      (k i : ℝ) * Real.log (Nat.factorial (i.1 + 1) : ℝ) -
    ∑ i : Fin b, Real.log (Nat.factorial (k i) : ℝ) -
    (ColoringProfile.forbiddenEdges k : ℝ) * Real.log 2

/-- Under the necessary mass constraint, the exact-profile first moment is
strictly positive, including for the empty profile on the empty graph. -/
theorem profileColoringExpectation_pos {b : ℕ}
    (n : ℕ) (k : ColoringProfile b)
    (hMass : ColoringProfile.vertexMass k = n) :
    0 < profileColoringExpectation n k := by
  rw [profileColoringExpectation_eq_enumerativeCoefficient_mul_of n k
    (profileEnumerationStatement n k hMass)]
  apply ENNReal.mul_pos
  · exact_mod_cast (ColoringProfile.enumerativeCoefficient_pos k).ne'
  · exact pow_ne_zero _ (by norm_num)

/-- Exact real-log form of the finite profile first moment.  This is the
logarithm of the actual `ENNReal` expectation, after `toReal`, rather than the
logarithm of a quotient proxy. -/
theorem log_profileColoringExpectation_toReal_eq_profileLogWeight
    {b : ℕ} (n : ℕ) (k : ColoringProfile b)
    (hMass : ColoringProfile.vertexMass k = n) :
    Real.log (profileColoringExpectation n k).toReal =
      profileLogWeight n k := by
  have hExpectation :=
    profileColoringExpectation_eq_enumerativeCoefficient_mul_of n k
      (profileEnumerationStatement n k hMass)
  have hToReal :
      (profileColoringExpectation n k).toReal =
        (ColoringProfile.enumerativeCoefficient k : ℝ) *
          (1 / 2 : ℝ) ^ ColoringProfile.forbiddenEdges k := by
    rw [hExpectation, ENNReal.toReal_mul, ENNReal.toReal_pow]
    norm_num
  rw [hToReal, Real.log_mul]
  · rw [Real.log_pow, ColoringProfile.log_enumerativeCoefficient_eq,
      hMass, Real.log_div]
    · simp only [Real.log_one, zero_sub]
      unfold profileLogWeight
      ring
    · norm_num
    · norm_num
  · exact_mod_cast (ColoringProfile.enumerativeCoefficient_pos k).ne'
  · positivity

end

end Erdos625
