import Mathlib

/-!
# Exact midpoint rounding for the root corridor

The real root separation is an upstream analytic task. This file formalizes
only the deterministic loss from the manuscript choices
`floor rPlus - ceil N` and `ceil ((rCo + rPlus) / 2)`.
-/

namespace Erdos625

open scoped Topology

noncomputable section

/-- The integer chromatic lower-location selected from the unrestricted real
root. -/
def rootChromaticIndex (rPlus N : ℝ) : ℤ :=
  ⌊rPlus⌋ - ⌈N⌉

/-- The integer cocolouring witness location selected from the midpoint of
the two real roots. -/
def rootCochromaticIndex (rCo rPlus : ℝ) : ℤ :=
  ⌈(rCo + rPlus) / 2⌉

/-- A real root gap of `c * base` and a deterministic rounding budget
`N + 3 ≤ rho * base` imply the exact Section XI-style integer threshold gap.
The three units are the floor loss and the two ceiling losses. -/
theorem root_midpoint_rounding_gap
    (rPlus rCo N c base rho : ℝ)
    (hGap : c * base ≤ rPlus - rCo)
    (hRounding : N + 3 ≤ rho * base) :
    (c / 2 - rho) * base ≤
      ((rootChromaticIndex rPlus N : ℤ) : ℝ) -
        ((rootCochromaticIndex rCo rPlus : ℤ) : ℝ) := by
  unfold rootChromaticIndex rootCochromaticIndex
  norm_num [sub_mul] at *
  linarith [Int.lt_floor_add_one rPlus, Int.ceil_lt_add_one N,
    Int.ceil_lt_add_one ((rCo + rPlus) / 2)]

end

end Erdos625
