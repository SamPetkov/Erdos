import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Formalization foundation

This module establishes the namespace and records the manuscript constant and
target scale used throughout the formal proof.
-/

namespace Erdos625

/-- The explicit constant in the Erdős 625 lower bound. -/
noncomputable def gapConstant : ℝ :=
  (Real.log 2) ^ 2 / 4 * Real.log (200 / 153 : ℝ)

/-- The explicit lower-bound constant is strictly positive. -/
theorem gapConstant_pos : 0 < gapConstant := by
  unfold gapConstant
  positivity

/-- The manuscript's asserted gap scale at `n`.  Its values at small `n` are
irrelevant to the eventual statement. -/
noncomputable def gapScale (n : ℕ) : ℝ :=
  gapConstant * (n : ℝ) / (Real.log (n : ℝ)) ^ 3

end Erdos625
