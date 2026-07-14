import Erdos625.ProfileAsymptoticTools
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Finite variance and derivative stability tools

These lemmas isolate the algebra needed to express a finite weighted variance,
transport a derivative through the centered tilt reflection, and compare two
normalized raw variances under explicit numerator and denominator errors.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- The finite weighted centered second moment equals the raw second moment
minus the square of the mean. -/
theorem weighted_variance_eq_raw
    {ι : Type*} [Fintype ι] (w x : ι → ℝ) (mu : ℝ)
    (hsum : ∑ i, w i = 1)
    (hmean : ∑ i, w i * x i = mu) :
    (∑ i, w i * (x i - mu) ^ 2) =
      (∑ i, w i * x i ^ 2) - mu ^ 2 := by
  have hexpand : ∀ i,
      w i * (x i - mu) ^ 2 =
        w i * x i ^ 2 - 2 * mu * (w i * x i) + mu ^ 2 * w i := by
    intro i
    ring
  simp only [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hmean, hsum]
  ring

/-- If `m (B-u) = A-d u`, then reflection reverses both derivative signs, so
the centered function has the same derivative value as the original one. -/
theorem hasDerivAt_of_reflected_centering
    {m d : ℝ → ℝ} {A B lambda V : ℝ}
    (hm : HasDerivAt m V (B - lambda))
    (hidentity : ∀ u : ℝ, m (B - u) = A - d u) :
    HasDerivAt d V lambda := by
  have hfun : d = fun u ↦ A - m (B - u) := by
    funext u
    have hu := hidentity u
    linarith
  rw [hfun]
  have hcomp : HasDerivAt (fun u ↦ m (B - u)) (-V) lambda := by
    simpa using hm.comp_const_sub B lambda
  simpa using hcomp.const_sub A

/-- Explicit stability of `second/Z - (first/Z)^2` when both partitions are
at least one and all three unnormalized quantities are uniformly close. -/
theorem normalized_raw_variance_stability
    {Z z A a B b K ε : ℝ}
    (hZ : 1 ≤ Z) (hz : 1 ≤ z)
    (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hZerr : |Z - z| ≤ ε)
    (hAerr : |A - a| ≤ ε)
    (hBerr : |B - b| ≤ ε)
    (hA : |A| ≤ K) (ha : |a| ≤ K) (hb : |b| ≤ K) :
    |(B / Z - (A / Z) ^ 2) - (b / z - (a / z) ^ 2)| ≤
      (1 + K) * (1 + 2 * K) * ε := by
  have hFirst : |A / Z - a / z| ≤ ε + K * ε := by
    have h := abs_div_sub_div_le_of_denominator_ge
      (z := 1) (epsA := ε) (epsB := ε) (M := K)
      zero_lt_one hε hε hK hZ hz hAerr hZerr ha
    simpa using h
  have hSecond : |B / Z - b / z| ≤ ε + K * ε := by
    have h := abs_div_sub_div_le_of_denominator_ge
      (z := 1) (epsA := ε) (epsB := ε) (M := K)
      zero_lt_one hε hε hK hZ hz hBerr hZerr hb
    simpa using h
  have hANorm : |A / Z| ≤ K := by
    rw [abs_div, abs_of_nonneg (by linarith : 0 ≤ Z)]
    exact (div_le_self (abs_nonneg A) hZ).trans hA
  have haNorm : |a / z| ≤ K := by
    rw [abs_div, abs_of_nonneg (by linarith : 0 ≤ z)]
    exact (div_le_self (abs_nonneg a) hz).trans ha
  have hSquare : |(A / Z) ^ 2 - (a / z) ^ 2| ≤
      (ε + K * ε) * (2 * K) := by
    rw [show (A / Z) ^ 2 - (a / z) ^ 2 =
      (A / Z - a / z) * (A / Z + a / z) by ring, abs_mul]
    have hsum : |A / Z + a / z| ≤ 2 * K := by
      calc
        |A / Z + a / z| ≤ |A / Z| + |a / z| := abs_add_le _ _
        _ ≤ 2 * K := by linarith
    exact mul_le_mul hFirst hsum (abs_nonneg _)
      (add_nonneg hε (mul_nonneg hK hε))
  calc
    |(B / Z - (A / Z) ^ 2) - (b / z - (a / z) ^ 2)| =
        |(B / Z - b / z) - ((A / Z) ^ 2 - (a / z) ^ 2)| := by
      congr 1
      ring
    _ ≤ |B / Z - b / z| + |(A / Z) ^ 2 - (a / z) ^ 2| := abs_sub _ _
    _ ≤ (ε + K * ε) + (ε + K * ε) * (2 * K) :=
      add_le_add hSecond hSquare
    _ = (1 + K) * (1 + 2 * K) * ε := by ring

end

end Erdos625
