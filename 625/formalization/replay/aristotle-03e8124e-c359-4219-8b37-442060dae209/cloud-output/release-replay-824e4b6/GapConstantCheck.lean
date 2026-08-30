import Erdos625

open Real in
example : Erdos625.gapConstant = (Real.log 2) ^ 2 / 4 * Real.log (200 / 153 : ℝ) := rfl

/-- The gap constant is exactly the one-quarter constant, i.e. four times it is
`(log 2)^2 * log (200/153)`. -/
example : 4 * Erdos625.gapConstant = (Real.log 2) ^ 2 * Real.log (200 / 153 : ℝ) := by
  unfold Erdos625.gapConstant; ring

#print Erdos625.gapConstant
#print axioms Erdos625.erdos625
#print Erdos625.Erdos625Statement
