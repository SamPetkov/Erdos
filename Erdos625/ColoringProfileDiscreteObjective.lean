import Erdos625.ColoringProfileLogBounds

/-!
# The discrete profile objective behind the variational bound

This module repackages the explicit Stirling upper main term as a sum of
zero-safe coordinate entropy terms plus the exact class-size energy
`log (s!) + choose(s,2) * log 2`.  This is the finite discrete objective that
will next be compared with the continuous maximum `L_+(n,k)`.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- Logarithmic cost of one independent color class of positive size `s`. -/
def coloringClassLogCost (s : ℕ) : ℝ :=
  Real.log (Nat.factorial s : ℝ) + (s.choose 2 : ℝ) * Real.log 2

/-- Zero-safe discrete objective for an exact bounded coloring profile. -/
def profileDiscreteObjective {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) : ℝ :=
  factorialEntropyMain n -
    ∑ i : Fin b,
      (factorialEntropyMain (k i) +
        (k i : ℝ) * coloringClassLogCost (i.1 + 1))

/-- Lean's totalized logarithm makes the usual entropy formula valid at zero
as well: the apparent `0 * log 0` term is exactly zero. -/
theorem factorialEntropyMain_eq_mul_log_sub (m : ℕ) :
    factorialEntropyMain m = (m : ℝ) * Real.log (m : ℝ) - m := by
  rcases m with _ | m
  · simp [factorialEntropyMain]
  · exact factorialEntropyMain_of_pos (Nat.succ_pos m)

/-- The discrete objective in the exact algebraic form of manuscript (3.2):
`n log n - n + number_of_parts`, minus the zero-safe coordinate costs. -/
def profileManuscriptObjective {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) : ℝ :=
  (n : ℝ) * Real.log (n : ℝ) - n +
    (ColoringProfile.partCount k : ℝ) -
    ∑ i : Fin b,
      (k i : ℝ) *
        (Real.log (k i : ℝ) + coloringClassLogCost (i.1 + 1))

/-- The zero-safe discrete objective and the manuscript algebraic expression
are exactly equal, including zero coordinates and the empty profile. -/
theorem profileDiscreteObjective_eq_profileManuscriptObjective {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) :
    profileDiscreteObjective n k = profileManuscriptObjective n k := by
  have hsum :
      (∑ i : Fin b,
        (factorialEntropyMain (k i) +
          (k i : ℝ) * coloringClassLogCost (i.1 + 1))) =
        (∑ i : Fin b,
          ((k i : ℝ) * Real.log (k i : ℝ) +
            (k i : ℝ) * coloringClassLogCost (i.1 + 1))) -
          ∑ i : Fin b, (k i : ℝ) := by
    calc
      _ = ∑ i : Fin b,
          (((k i : ℝ) * Real.log (k i : ℝ) +
              (k i : ℝ) * coloringClassLogCost (i.1 + 1)) -
            (k i : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [factorialEntropyMain_eq_mul_log_sub]
        ring
      _ = _ := by
        simp
  rw [profileDiscreteObjective, profileManuscriptObjective,
    factorialEntropyMain_eq_mul_log_sub,
    ColoringProfile.partCount_eq_sum, Nat.cast_sum, hsum]
  ring

/-- The Stirling upper main term is exactly the discrete coordinate
objective; in particular the forbidden-edge energy has no approximation. -/
theorem profileStirlingUpperMain_eq_profileDiscreteObjective {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) :
    profileStirlingUpperMain n k = profileDiscreteObjective n k := by
  have hsum :
      (∑ i : Fin b,
        (factorialEntropyMain (k i) +
          (k i : ℝ) * coloringClassLogCost (i.1 + 1))) =
        (∑ i : Fin b, factorialEntropyMain (k i)) +
          (∑ i : Fin b,
            (k i : ℝ) * Real.log (Nat.factorial (i.1 + 1) : ℝ)) +
          (∑ i : Fin b,
            (k i : ℝ) * ((i.1 + 1).choose 2 : ℝ) * Real.log 2) := by
    calc
      _ = ∑ i : Fin b,
          ((factorialEntropyMain (k i) +
              (k i : ℝ) * Real.log (Nat.factorial (i.1 + 1) : ℝ)) +
            (k i : ℝ) * ((i.1 + 1).choose 2 : ℝ) * Real.log 2) := by
        apply Finset.sum_congr rfl
        intro i _
        unfold coloringClassLogCost
        ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [profileStirlingUpperMain, profileDiscreteObjective,
    ColoringProfile.forbiddenEdges_eq_sum, hsum]
  simp only [profileFactorialEntropyMain, Nat.cast_sum, Nat.cast_mul,
    Finset.sum_mul]
  ring

/-- The exact profile log-weight is therefore bounded by the discrete
objective plus the numerator-factorial error. -/
theorem profileLogWeight_le_discreteObjective_add_error {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) :
    profileLogWeight n k ≤
      profileDiscreteObjective n k + factorialLogErrorBound n := by
  rw [← profileStirlingUpperMain_eq_profileDiscreteObjective]
  exact profileLogWeight_le_stirlingUpperMain_add_error n k

end

end Erdos625
