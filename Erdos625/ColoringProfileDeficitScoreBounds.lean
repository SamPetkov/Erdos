import Erdos625.ColoringProfileDeficitDual

/-!
# Pointwise bounds for the deficit-coordinate score

This module isolates the exact endpoint value and the elementary Gaussian
upper bound for the centered residual score.  The only estimate is the
finite-product inequality

`alpha.descFactorial d ≤ alpha ^ d`.
-/

namespace Erdos625

noncomputable section

/-- The top support coordinate has class size `alpha + 1` and deficit `-1`. -/
theorem profileDeficit_last (alpha : ℕ) :
    profileDeficit alpha (Fin.last alpha) = -1 := by
  simp [profileDeficit, profileClassSize]

/-- Exact residual score of the unique top coordinate. -/
theorem profileDeficitResidualScore_last (alpha : ℕ) (halpha : 0 < alpha) :
    profileDeficitResidualScore alpha (Fin.last alpha) =
      -q / 2 + Real.log ((alpha : ℝ) / ((alpha : ℝ) + 1)) := by
  have halphaReal : (0 : ℝ) < alpha := by exact_mod_cast halpha
  have halphaFactorial : (alpha.factorial : ℝ) ≠ 0 := by positivity
  have halphaSuccReal : (0 : ℝ) < (alpha : ℝ) + 1 := by positivity
  have hfactorial :
      Real.log (((alpha + 1).factorial : ℕ) : ℝ) =
        Real.log ((alpha : ℝ) + 1) +
          Real.log ((alpha.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul]
    · norm_num [Nat.cast_add]
    · exact_mod_cast (Nat.succ_ne_zero alpha)
    · exact halphaFactorial
  have hchoose : (((alpha + 1).choose 2 : ℕ) : ℝ) =
      (alpha.choose 2 : ℝ) + alpha := by
    exact_mod_cast chooseTwo_succ alpha
  rw [profileDeficitResidualScore, profileDualScore,
    profileDeficitAffineA, profileDeficitAffineB,
    coloringClassLogCost, profileDeficit_last]
  simp only [Fin.val_last]
  rw [hfactorial, hchoose,
    Real.log_div halphaReal.ne' halphaSuccReal.ne']
  unfold coloringClassLogCost q
  ring

/-- On a coordinate of size at most `alpha`, the real deficit is the cast of
the corresponding natural-number subtraction. -/
theorem profileDeficit_eq_cast_sub (alpha : ℕ) (i : Fin (alpha + 1))
    (hsize : i.1 + 1 ≤ alpha) :
    profileDeficit alpha i = ((alpha - (i.1 + 1) : ℕ) : ℝ) := by
  unfold profileDeficit profileClassSize
  rw [Nat.cast_sub hsize]

/-- Exact finite-product decomposition of an interior residual score. -/
theorem profileDeficitResidualScore_eq_descFactorial
    (alpha : ℕ) (i : Fin (alpha + 1)) (hsize : i.1 + 1 ≤ alpha) :
    profileDeficitResidualScore alpha i =
      Real.log
          ((alpha.descFactorial (alpha - (i.1 + 1)) : ℕ) : ℝ) -
        ((alpha - (i.1 + 1) : ℕ) : ℝ) * Real.log (alpha : ℝ) -
        q / 2 * (((alpha - (i.1 + 1) : ℕ) : ℝ) ^ 2) := by
  let s : ℕ := i.1 + 1
  let d : ℕ := alpha - s
  have hsPos : 0 < s := by simp [s]
  have hdle : d ≤ alpha := by simp [d]
  have hsub : alpha - d = s := by
    dsimp [d]
    omega
  have hfactorialNat : s.factorial * alpha.descFactorial d = alpha.factorial := by
    simpa only [hsub] using (Nat.factorial_mul_descFactorial hdle)
  have hsFactorial : (s.factorial : ℝ) ≠ 0 := by positivity
  have hdesc : (alpha.descFactorial d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ((Nat.descFactorial_pos).2 hdle))
  have hfactorialLog :
      Real.log (alpha.factorial : ℝ) - Real.log (s.factorial : ℝ) =
        Real.log (alpha.descFactorial d : ℝ) := by
    have hcast := congrArg (fun m : ℕ ↦ (m : ℝ)) hfactorialNat
    norm_num only [Nat.cast_mul] at hcast
    calc
      Real.log (alpha.factorial : ℝ) - Real.log (s.factorial : ℝ) =
          Real.log ((s.factorial : ℝ) * (alpha.descFactorial d : ℝ)) -
            Real.log (s.factorial : ℝ) := by rw [hcast]
      _ = Real.log (alpha.descFactorial d : ℝ) := by
        rw [Real.log_mul hsFactorial hdesc]
        ring
  have hdcast : (d : ℝ) = (alpha : ℝ) - (s : ℝ) := by
    dsimp [d]
    exact Nat.cast_sub hsize
  have hchoose :
      (alpha.choose 2 : ℝ) - (s.choose 2 : ℝ) =
        (d : ℝ) * (alpha : ℝ) - ((d : ℝ) ^ 2 + d) / 2 := by
    rw [Nat.cast_choose_two, Nat.cast_choose_two, hdcast]
    ring
  have hdeficit : profileDeficit alpha i = (d : ℝ) := by
    simpa only [s, d] using profileDeficit_eq_cast_sub alpha i hsize
  change
    -coloringClassLogCost s - -coloringClassLogCost alpha -
        profileDeficitAffineB alpha * profileDeficit alpha i = _
  rw [hdeficit]
  unfold coloringClassLogCost profileDeficitAffineB
  change
    -(Real.log (s.factorial : ℝ) + (s.choose 2 : ℝ) * Real.log 2) -
          -(Real.log (alpha.factorial : ℝ) +
            (alpha.choose 2 : ℝ) * Real.log 2) -
        (q * (alpha : ℝ) - q / 2 + Real.log (alpha : ℝ)) * (d : ℝ) =
      Real.log (alpha.descFactorial d : ℝ) -
        (d : ℝ) * Real.log (alpha : ℝ) - q / 2 * (d : ℝ) ^ 2
  unfold q
  linear_combination hfactorialLog + Real.log 2 * hchoose

/-- The factorial ratio contributes a nonpositive correction to the centered
quadratic energy. -/
theorem log_descFactorial_le_mul_log (alpha d : ℕ) (hd : d ≤ alpha)
    (halpha : 0 < alpha) :
    Real.log (alpha.descFactorial d : ℝ) ≤
      (d : ℝ) * Real.log (alpha : ℝ) := by
  have hdescPos : (0 : ℝ) < alpha.descFactorial d := by
    exact_mod_cast ((Nat.descFactorial_pos).2 hd)
  have hpowPos : (0 : ℝ) < (alpha : ℝ) ^ d := by positivity
  have hcastBound : (alpha.descFactorial d : ℝ) ≤ (alpha : ℝ) ^ d := by
    exact_mod_cast (Nat.descFactorial_le_pow alpha d)
  have hlog := Real.log_le_log hdescPos hcastBound
  rwa [Real.log_pow] at hlog

/-- Every coordinate of size at most `alpha` obeys the Gaussian residual
upper bound. -/
theorem profileDeficitResidualScore_le_gaussian_of_size_le
    (alpha : ℕ) (halpha : 0 < alpha) (i : Fin (alpha + 1))
    (hsize : i.1 + 1 ≤ alpha) :
    profileDeficitResidualScore alpha i ≤
      -q / 2 * (profileDeficit alpha i) ^ 2 := by
  let d : ℕ := alpha - (i.1 + 1)
  have hdle : d ≤ alpha := by simp [d]
  have hlog := log_descFactorial_le_mul_log alpha d hdle halpha
  rw [profileDeficitResidualScore_eq_descFactorial alpha i hsize,
    profileDeficit_eq_cast_sub alpha i hsize]
  dsimp [d] at hlog
  linarith

/-- The same Gaussian upper bound holds on the entire support.  The only
coordinate not covered by the factorial-ratio argument is the unique class
of size `alpha + 1`; its extra term is `log (alpha / (alpha + 1)) ≤ 0`. -/
theorem profileDeficitResidualScore_le_gaussian
    (alpha : ℕ) (halpha : 0 < alpha) (i : Fin (alpha + 1)) :
    profileDeficitResidualScore alpha i ≤
      -q / 2 * (profileDeficit alpha i) ^ 2 := by
  by_cases hsize : i.1 + 1 ≤ alpha
  · exact profileDeficitResidualScore_le_gaussian_of_size_le
      alpha halpha i hsize
  · have hiVal : i.1 = alpha := by
      have hiLt := i.2
      omega
    have hi : i = Fin.last alpha := by
      apply Fin.ext
      simpa only [Fin.val_last] using hiVal
    rw [hi, profileDeficitResidualScore_last alpha halpha,
      profileDeficit_last]
    have halphaReal : (0 : ℝ) < alpha := by exact_mod_cast halpha
    have halphaSuccReal : (0 : ℝ) < (alpha : ℝ) + 1 := by positivity
    have hratioNonneg :
        (0 : ℝ) ≤ (alpha : ℝ) / ((alpha : ℝ) + 1) := by positivity
    have hratioLeOne :
        (alpha : ℝ) / ((alpha : ℝ) + 1) ≤ 1 := by
      exact (div_le_one halphaSuccReal).2 (by linarith)
    have hlog :
        Real.log ((alpha : ℝ) / ((alpha : ℝ) + 1)) ≤ 0 :=
      Real.log_nonpos hratioNonneg hratioLeOne
    norm_num
    linarith

end

end Erdos625
